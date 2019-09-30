/******************************************************************************
 *
 * Project:  Viewshed Generation
 * Purpose:  Core algorithm implementation for viewshed generation.
 * Author:   Tamas Szekeres, szekerest@gmail.com
 *
 ******************************************************************************
 *
 * Permission is hereby granted, free of charge, to any person obtaining a
 * copy of this software and associated documentation files (the "Software"),
 * to deal in the Software without restriction, including without limitation
 * the rights to use, copy, modify, merge, publish, distribute, sublicense,
 * and/or sell copies of the Software, and to permit persons to whom the
 * Software is furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included
 * in all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
 * OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
 * THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
 * FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
 * DEALINGS IN THE SOFTWARE.
 ****************************************************************************/

#include "cpl_port.h"
#include "gdal_alg.h"

#include <cmath>
#include <cstring>

#include <algorithm>

#include "cpl_conv.h"
#include "cpl_error.h"
#include "cpl_progress.h"
#include "cpl_vsi.h"
#include "gdal.h"
#include "gdal_priv.h"
#include "gdal_priv_templates.hpp"
#include "ogr_api.h"
#include "ogr_core.h"
#include "commonutils.h"

CPL_CVSID("$Id$")

/************************************************************************/
/*                        GDALViewShedGenerate()                         */
/************************************************************************/

/**
 * Create viewshed raster from raster DEM.
 *
 * This algorithm will generate a viewshed raster from an input DEM raster
 * by using a modified algorithm of "Generating Viewsheds without Using Sightlines" 
 * published at https://www.asprs.org/wp-content/uploads/pers/2000journal/january/2000_jan_87-90.pdf
 * This appoach provides a relatively fast calculation, since the output raster is
 * generated in a single scan.
 * The gdal/apps/gdal_viewshed.cpp mainline can be used as an example of
 * how to use this function.
 *
 * ALGORITHM RULES
 *
 * @param hBand The band to read the DEM data from. Only the part of the raster
 * within the specified maxdistance around the observer point is processed.
 *
 * @param pszTargetRasterName The name of the target raster to be generated.
 *
 * @param dfObserverX The X position of the observer in the SRS of the DEM.
 *
 * @param dfObserverY The Y position of the observer in the SRS of the DEM.
 *
 * @param dfObserverHeight The height of the observer above the DEM surface.
 *
 * @param dfTargetHeight The height of the target above the DEM surface.
 *
 * @param dfVisibleVal The value to be set for the visible cells.
 *
 * @param dfInVisibleVal The value to be set for the invisible cells.
 *
 * @param dfNoDataVal The value to be set for the cells that has no data.
 *
 * @param dfCurvCoeff Coefficient to consider the effect of the refraction.
 * The height of the DEM is corrected according to the following formula:
 * [Height] -= dfCurvCoeff * [Target Distance]^2 / [Earth Diameter]
 * For atmospheric refraction we can use 0.85714‬.
 *
 * @param eMode The mode of the viewshed calculation.
 * Possible values GVM_Diagonal = 1, GVM_Edge = 2 (default), GVM_Max = 3, GVM_Min = 4.
 * 
 * @param dfMaxDistance Specifies the maximum distance of the analysis.
 *
 * @param pfnProgress A GDALProgressFunc that may be used to report progress
 * to the user, or to interrupt the algorithm.  May be NULL if not required.
 *
 * @param pProgressArg The callback data for the pfnProgress function.
 *
 * @return CE_None on success or CE_Failure if an error occurs.
 */

#define EARTH_DIAMETER 12741994.0;

#ifndef round
inline double round( double d )
{
    return floor( d + 0.5 );
}
#endif

void SetVisibility(int iPixel, double dfZ, double dfZTarget, double* padfZVal,
    GByte* pabyResult, GByte byVisibleVal, GByte byInvisibleVal)
{
    if (padfZVal[iPixel] + dfZTarget < dfZ)
    {
        padfZVal[iPixel] = dfZ;
        pabyResult[iPixel] = byInvisibleVal;
    }
    else
        pabyResult[iPixel] = byVisibleVal;
}

int AdjustHeightInRange(double* adfGeoTransform, int iPixel, int iLine, double& dfHeight, double dfDistance2, double dfCurvCoeff)
{  
    if (dfDistance2 <= 0 && dfCurvCoeff == 0)
        return TRUE;

    double dfX = adfGeoTransform[1] * iPixel + adfGeoTransform[2] * iLine;
    double dfY = adfGeoTransform[4] * iPixel + adfGeoTransform[5] * iLine;
    double dfR2 = dfX * dfX + dfY * dfY;

    /* calc adjustment */
    if (dfCurvCoeff != 0)
        dfHeight -= dfCurvCoeff * dfR2 / EARTH_DIAMETER;
    
    if (dfDistance2 > 0 && dfR2 > dfDistance2)
        return FALSE;

    return TRUE;
}

static double CalcHeightLine(int i, double Za, double Zo)
{
    if (i == 1)
        return Za;
    else
        return (Za - Zo) / (i - 1) + Za;
}

static double CalcHeightDiagonal(int i, int j, double Za, double Zb, double Zo)
{
    return ((Za - Zo) * i + (Zb - Zo) * j) / (i + j - 1) + Zo;
}

static double CalcHeightEdge(int i, int j, double Za, double Zb, double Zo)
{
    if (i == j)
        return CalcHeightLine(i, Za, Zo);
    else
        return ((Za - Zo) * i + (Zb - Zo) * (j - i)) / (j - 1) + Zo;
}

static double CalcHeight(double dfZ, double dfZ2, GDALViewshedMode eMode)
{
    if (eMode == GVM_Edge)
        return dfZ2;
    else if (eMode == GVM_Max)
        return std::max(dfZ, dfZ2);
    else if (eMode == GVM_Min)
        return std::min(dfZ, dfZ2);
    else
        return dfZ;
}

CPLErr GDALViewshedGenerate(GDALRasterBandH hBand, const char* pszTargetRasterName,
                    double dfObserverX, double dfObserverY, double dfObserverHeight,
                    double dfTargetHeight, double dfVisibleVal, double dfInvisibleVal,
                    double dfOutOfRangeVal, double dfNoDataVal, double dfCurvCoeff,
                    GDALViewshedMode eMode, double dfMaxDistance,
                    GDALProgressFunc pfnProgress, void *pProgressArg)

{
    VALIDATE_POINTER1( hBand, "GDALViewshedGenerate", CE_Failure );

    if( pfnProgress == nullptr )
        pfnProgress = GDALDummyProgress;

    if( !pfnProgress( 0.0, "", pProgressArg ) )
    {
        CPLError( CE_Failure, CPLE_UserInterrupt, "User terminated" );
        return CE_Failure;
    }

    GByte byNoDataVal = dfNoDataVal >= 0 ? static_cast<GByte>(dfNoDataVal) : 0;
    GByte byVisibleVal = dfVisibleVal >= 0 ? static_cast<GByte>(dfVisibleVal) : 255;
    GByte byInvisibleVal = dfInvisibleVal >= 0 ? static_cast<GByte>(dfInvisibleVal) : 0;
    GByte byOutOfRangeVal = dfOutOfRangeVal >= 0 ? static_cast<GByte>(dfOutOfRangeVal) : 0;

    /* set up geotransformation */
    double adfGeoTransform[6];
    adfGeoTransform[0] = 0.0;
    adfGeoTransform[1] = 1.0;
    adfGeoTransform[2] = 0.0;
    adfGeoTransform[3] = 0.0;
    adfGeoTransform[4] = 0.0;
    adfGeoTransform[5] = 1.0;
    GDALDatasetH hSrcDS = GDALGetBandDataset( hBand );
    if( hSrcDS != nullptr )
        GDALGetGeoTransform( hSrcDS, adfGeoTransform );

    double adfInvGeoTransform[6];
    if (!GDALInvGeoTransform(adfGeoTransform, adfInvGeoTransform))
    {
        CPLError(CE_Failure, CPLE_AppDefined, "Cannot invert geotransform");
        return CE_Failure;
    }

    /* calculate observer position */
    double dfX, dfY;
    GDALApplyGeoTransform(adfInvGeoTransform, dfObserverX, dfObserverY, &dfX, &dfY);
    int nX = static_cast<int>(round(dfX));
    int nY = static_cast<int>(round(dfY));

    int nXSize = GDALGetRasterBandXSize( hBand );
    int nYSize = GDALGetRasterBandYSize( hBand );

    if (nX < 0 || nX > nXSize || nY < 0 || nY > nYSize)
    {
        CPLError(CE_Failure, CPLE_AppDefined, "The observer location falls outside of the DEM area");
        return CE_Failure;
    } 

    CPLErr eErr = CE_None;
    /* calculate the area of interest */
    int nXStart = dfMaxDistance > 0? std::max(0, static_cast<int>(floor(nX - adfInvGeoTransform[1] * dfMaxDistance))) : 0;
    int nXStop = dfMaxDistance > 0? std::min(nXSize, static_cast<int>(ceil(nX + adfInvGeoTransform[1] * dfMaxDistance) + 1)) : nXSize;
    int nYStart = dfMaxDistance > 0? std::max(0, static_cast<int>(floor(nY + adfInvGeoTransform[5] * dfMaxDistance))) : 0;
    int nYStop = dfMaxDistance > 0 ? std::min(nYSize, static_cast<int>(ceil(nY - adfInvGeoTransform[5] * dfMaxDistance) + 1)) : nYSize;

    /* normalize horizontal index (0 - nXSize) */
    nXSize = nXStop - nXStart;
    nX -= nXStart;

    GDALRasterBandH hTargetBand = nullptr;
    GDALDatasetH hDstDS = nullptr;
    if (pszTargetRasterName != nullptr)
    {
		GDALDriverH hDriver = GDALGetDriverByName("GTiff");
		if (hDriver == nullptr)
		{
			CPLError(CE_Failure, CPLE_AppDefined,
				"Cannot get driver for GTiff");
			return CE_Failure;
		}
		/* create output raster */
		hDstDS = GDALCreate(hDriver, pszTargetRasterName, nXSize, nYStop - nYStart, 1,
				GDT_Byte, nullptr);
		if (hDstDS == nullptr)
		{
			CPLError(CE_Failure, CPLE_AppDefined,
				"Cannot create dataset for %s", pszTargetRasterName);
			return CE_Failure;
		}

		const char *pszProjection = GDALGetProjectionRef(hSrcDS);
		if (pszProjection != nullptr && strlen(pszProjection) > 0)
			GDALSetProjection(hDstDS, pszProjection);

		double adfDstGeoTransform[6];
		adfDstGeoTransform[0] = adfGeoTransform[0] + adfGeoTransform[1] * nXStart;
		adfDstGeoTransform[1] = adfGeoTransform[1];
		adfDstGeoTransform[2] = adfGeoTransform[2];
		adfDstGeoTransform[3] = adfGeoTransform[3] + adfGeoTransform[5] * nYStart;
		adfDstGeoTransform[4] = adfGeoTransform[4];
		adfDstGeoTransform[5] = adfGeoTransform[5];
		GDALSetGeoTransform(hDstDS, adfDstGeoTransform);

		hTargetBand = GDALGetRasterBand(hDstDS, 1);
		if (hTargetBand == nullptr)
		{
			CPLError(CE_Failure, CPLE_AppDefined,
				"Cannot get band for %s", pszTargetRasterName);
			return CE_Failure;
		}

		if (dfNoDataVal >= 0)
			GDALSetRasterNoDataValue(hTargetBand, byNoDataVal);
    }
    else
    {
        CPLError(CE_Failure, CPLE_AppDefined,
            "Invalid target raster name");
        return CE_Failure;
    }

    /* create scanlines */
    double *padfFirstLineVal = static_cast<double *>(
        VSI_MALLOC2_VERBOSE(sizeof(double), nXSize));
    double *padfLastLineVal = static_cast<double *>(
        VSI_MALLOC2_VERBOSE(sizeof(double), nXSize));
    double *padfThisLineVal = static_cast<double *>(
        VSI_MALLOC2_VERBOSE(sizeof(double), nXSize));
    GByte *pabyResult = static_cast<GByte *>(
        VSI_MALLOC2_VERBOSE(sizeof(GByte), nXSize));

    if (padfFirstLineVal == nullptr || padfLastLineVal == nullptr ||
        padfThisLineVal == nullptr || pabyResult == nullptr)
    {
        CPLError(CE_Failure, CPLE_AppDefined,
            "Failed to allocate scanlines");

        CPLFree(padfFirstLineVal);
        CPLFree(padfLastLineVal);
        CPLFree(padfThisLineVal);
        CPLFree(pabyResult);

        if (hDstDS != nullptr)
            GDALClose(hDstDS);

        return CE_Failure;
    }

    /* process first line */
    if (GDALRasterIO(hBand, GF_Read, nXStart, nY, nXSize, 1,
        padfFirstLineVal, nXSize, 1, GDT_Float64, 0, 0) != CE_None)
    {
        CPLError(CE_Failure, CPLE_AppDefined,
            "RasterIO error when reading DEM at position (%d,%d), size (%d,%d)", nXStart, nY, nXSize, 1);

        CPLFree(padfFirstLineVal);
        CPLFree(padfLastLineVal);
        CPLFree(padfThisLineVal);
        CPLFree(pabyResult);

        if (hDstDS != nullptr)
            GDALClose(hDstDS);

        return CE_Failure;
    }

    double dfZObserver = dfObserverHeight + padfFirstLineVal[nX];
    double dfZ = 0.0;
    int iPixel, iLine;
    double dfDistance2 = dfMaxDistance * dfMaxDistance;

    /* mark the observer point as visible */
    pabyResult[nX] = byVisibleVal;
    if (nX > 0)
    {
        AdjustHeightInRange(adfGeoTransform, 1, 0, padfFirstLineVal[nX - 1], dfDistance2, dfCurvCoeff);
        pabyResult[nX - 1] = byVisibleVal;
    }
    if (nX < nXSize - 1)
    {
        AdjustHeightInRange(adfGeoTransform, 1, 0, padfFirstLineVal[nX + 1], dfDistance2, dfCurvCoeff);
        pabyResult[nX + 1] = byVisibleVal;
    }

    /* process left direction */
    for (iPixel = nX - 2; iPixel >= 0; iPixel--)
    {
        if (AdjustHeightInRange(adfGeoTransform, nX - iPixel, 0, padfFirstLineVal[iPixel], dfDistance2, dfCurvCoeff))
        {
            dfZ = CalcHeightLine(nX - iPixel, padfFirstLineVal[iPixel + 1], dfZObserver);
            SetVisibility(iPixel, dfZ, dfTargetHeight, padfFirstLineVal, pabyResult, byVisibleVal, byInvisibleVal);
        }
        else
        {
            for (; iPixel >= 0; iPixel--)
                pabyResult[iPixel] = byOutOfRangeVal;
        }
    }
    /* process right direction */
    for (iPixel = nX + 2; iPixel < nXSize; iPixel++)
    {
        if (AdjustHeightInRange(adfGeoTransform, iPixel - nX, 0, padfFirstLineVal[iPixel], dfDistance2, dfCurvCoeff))
        {
            dfZ = CalcHeightLine(iPixel - nX, padfFirstLineVal[iPixel - 1], dfZObserver);
            SetVisibility(iPixel, dfZ, dfTargetHeight, padfFirstLineVal, pabyResult, byVisibleVal, byInvisibleVal);
        }
        else
        {
            for (; iPixel < nXSize; iPixel++)
                pabyResult[iPixel] = byOutOfRangeVal;
        }
    }
    /* write result line */
    if (hTargetBand != nullptr)
    {
        if (GDALRasterIO(hTargetBand, GF_Write, 0, nY - nYStart, nXSize, 1,
            pabyResult, nXSize, 1, GDT_Byte, 0, 0) != CE_None)
        {
            CPLError(CE_Failure, CPLE_AppDefined,
                "RasterIO error when writing target raster at position (%d,%d), size (%d,%d)", 0, nY - nYStart, nXSize, 1);

            CPLFree(padfFirstLineVal);
            CPLFree(padfLastLineVal);
            CPLFree(padfThisLineVal);
            CPLFree(pabyResult);

            if (hDstDS != nullptr)
                GDALClose(hDstDS);

            return CE_Failure;
        }
    }

    /* scan upwards */
    memcpy(padfLastLineVal, padfFirstLineVal, nXSize * sizeof(double));
    for (iLine = nY - 1; iLine >= nYStart && eErr == CE_None; iLine--)
    {
        if (GDALRasterIO(hBand, GF_Read, nXStart, iLine, nXSize, 1,
            padfThisLineVal, nXSize, 1, GDT_Float64, 0, 0) != CE_None)
        {
            CPLError(CE_Failure, CPLE_AppDefined,
                "RasterIO error when reading DEM at position (%d,%d), size (%d,%d)", nXStart, iLine, nXSize, 1);
            eErr = CE_Failure;
            continue;
        }

        /* set up initial point on the scanline */
        if (AdjustHeightInRange(adfGeoTransform, 0, nY - iLine, padfThisLineVal[nX], dfDistance2, dfCurvCoeff))
        {
            dfZ = CalcHeightLine(nY - iLine, padfLastLineVal[nX], dfZObserver);
            SetVisibility(nX, dfZ, dfTargetHeight, padfThisLineVal, pabyResult, byVisibleVal, byInvisibleVal);
        }
        else
        {
            pabyResult[nX] = byOutOfRangeVal;
        }

        /* process left direction */
        for (iPixel = nX - 1; iPixel >= 0; iPixel--)
        {
            if (AdjustHeightInRange(adfGeoTransform, nX - iPixel, nY - iLine, padfThisLineVal[iPixel], dfDistance2, dfCurvCoeff))
            {
                if (eMode != GVM_Edge)
                    dfZ = CalcHeightDiagonal(nX - iPixel, nY - iLine,
                        padfThisLineVal[iPixel + 1], padfLastLineVal[iPixel], dfZObserver);

                if (eMode != GVM_Diagonal)
                {
                    double dfZ2 = nX - iPixel >= nY - iLine ?
                        CalcHeightEdge(nY - iLine, nX - iPixel,
                            padfLastLineVal[iPixel + 1], padfThisLineVal[iPixel + 1], dfZObserver) :
                        CalcHeightEdge(nX - iPixel, nY - iLine,
                            padfLastLineVal[iPixel + 1], padfLastLineVal[iPixel], dfZObserver);
                    dfZ = CalcHeight(dfZ, dfZ2, eMode);
                }

                SetVisibility(iPixel, dfZ, dfTargetHeight, padfThisLineVal, pabyResult, byVisibleVal, byInvisibleVal);
            }
            else
            {
                for (; iPixel >= 0; iPixel--)
                    pabyResult[iPixel] = byOutOfRangeVal;
            }
        }
        /* process right direction */
        for (iPixel = nX + 1; iPixel < nXSize; iPixel++)
        {
            if (AdjustHeightInRange(adfGeoTransform, iPixel - nX, nY - iLine, padfThisLineVal[iPixel], dfDistance2, dfCurvCoeff))
            {
                if (eMode != GVM_Edge)
                    dfZ = CalcHeightDiagonal(iPixel - nX, nY - iLine,
                        padfThisLineVal[iPixel - 1], padfLastLineVal[iPixel], dfZObserver);

                if (eMode != GVM_Diagonal)
                {
                    double dfZ2 = iPixel - nX >= nY - iLine ?
                        CalcHeightEdge(nY - iLine, iPixel - nX,
                            padfLastLineVal[iPixel - 1], padfThisLineVal[iPixel - 1], dfZObserver) :
                        CalcHeightEdge(iPixel - nX, nY - iLine,
                            padfLastLineVal[iPixel - 1], padfLastLineVal[iPixel], dfZObserver);
                    dfZ = CalcHeight(dfZ, dfZ2, eMode);
                }

                SetVisibility(iPixel, dfZ, dfTargetHeight, padfThisLineVal, pabyResult, byVisibleVal, byInvisibleVal);
            }
            else
            {
                for (; iPixel < nXSize; iPixel++)
                    pabyResult[iPixel] = byOutOfRangeVal;
            }
        }

        /* write result line */
        if (hTargetBand != nullptr)
        {
            if (GDALRasterIO(hTargetBand, GF_Write, 0, iLine - nYStart, nXSize, 1,
                pabyResult, nXSize, 1, GDT_Byte, 0, 0) != CE_None)
            {
                CPLError(CE_Failure, CPLE_AppDefined,
                    "RasterIO error when writing target raster at position (%d,%d), size (%d,%d)", 0, iLine - nYStart, nXSize, 1);
                eErr = CE_Failure;
                continue;
            }
        }

        std::swap(padfLastLineVal, padfThisLineVal);

        if (!pfnProgress((nYStart - iLine + 1) / static_cast<double>(nYStop),
                "", pProgressArg))
        {
            CPLError(CE_Failure, CPLE_UserInterrupt, "User terminated");
            eErr = CE_Failure;
            continue;
        }
    }
    /* scan downwards */
    memcpy(padfLastLineVal, padfFirstLineVal, nXSize * sizeof(double));
    for(iLine = nY + 1; iLine < nYStop && eErr == CE_None; iLine++ )
    {
        if (GDALRasterIO( hBand, GF_Read, nXStart, iLine, nXStop - nXStart, 1,
            padfThisLineVal, nXStop - nXStart, 1, GDT_Float64, 0, 0 ) != CE_None)
        {
            CPLError(CE_Failure, CPLE_AppDefined,
                "RasterIO error when reading DEM at position (%d,%d), size (%d,%d)", nXStart, iLine, nXStop - nXStart, 1);
            eErr = CE_Failure;
            continue;
        }

        /* set up initial point on the scanline */
        if (AdjustHeightInRange(adfGeoTransform, 0, iLine - nY, padfThisLineVal[nX], dfDistance2, dfCurvCoeff))
        {
            dfZ = CalcHeightLine(iLine - nY, padfLastLineVal[nX], dfZObserver);
            SetVisibility(nX, dfZ, dfTargetHeight, padfThisLineVal, pabyResult, byVisibleVal, byInvisibleVal);
        }
        else
        {
            pabyResult[nX] = byOutOfRangeVal;
        }

        /* process left direction */
        for (iPixel = nX - 1; iPixel >= 0; iPixel--)
        {
            if (AdjustHeightInRange(adfGeoTransform, nX - iPixel, iLine - nY, padfThisLineVal[iPixel], dfDistance2, dfCurvCoeff))
            {
                if (eMode != GVM_Edge)
                    dfZ = CalcHeightDiagonal(nX - iPixel, iLine - nY,
                        padfThisLineVal[iPixel + 1], padfLastLineVal[iPixel], dfZObserver);

                if (eMode != GVM_Diagonal)
                {
                    double dfZ2 = nX - iPixel >= iLine - nY ?
                        CalcHeightEdge(iLine - nY, nX - iPixel,
                            padfLastLineVal[iPixel + 1], padfThisLineVal[iPixel + 1], dfZObserver) :
                        CalcHeightEdge(nX - iPixel, iLine - nY,
                            padfLastLineVal[iPixel + 1], padfLastLineVal[iPixel], dfZObserver);
                    dfZ = CalcHeight(dfZ, dfZ2, eMode);
                }

                SetVisibility(iPixel, dfZ, dfTargetHeight, padfThisLineVal, pabyResult, byVisibleVal, byInvisibleVal);
            }
            else
            {
                for (; iPixel >= 0; iPixel--)
                    pabyResult[iPixel] = byOutOfRangeVal;
            }
        }
        /* process right direction */
        for (iPixel = nX + 1; iPixel < nXSize; iPixel++)
        {
            if (AdjustHeightInRange(adfGeoTransform, iPixel - nX, iLine - nY, padfThisLineVal[iPixel], dfDistance2, dfCurvCoeff))
            {
                if (eMode != GVM_Edge)
                    dfZ = CalcHeightDiagonal(iPixel - nX, iLine - nY,
                        padfThisLineVal[iPixel - 1], padfLastLineVal[iPixel], dfZObserver);

                if (eMode != GVM_Diagonal)
                {
                    double dfZ2 = iPixel - nX >= iLine - nY ?
                        CalcHeightEdge(iLine - nY, iPixel - nX,
                            padfLastLineVal[iPixel - 1], padfThisLineVal[iPixel - 1], dfZObserver) :
                        CalcHeightEdge(iPixel - nX, iLine - nY,
                            padfLastLineVal[iPixel - 1], padfLastLineVal[iPixel], dfZObserver);
                    dfZ = CalcHeight(dfZ, dfZ2, eMode);
                }

                SetVisibility(iPixel, dfZ, dfTargetHeight, padfThisLineVal, pabyResult, byVisibleVal, byInvisibleVal);
            }
            else
            {
                for (; iPixel < nXSize; iPixel++)
                    pabyResult[iPixel] = byOutOfRangeVal;
            }
        }

        /* write result line */
        if (hTargetBand != nullptr)
        {
            if (GDALRasterIO(hTargetBand, GF_Write, 0, iLine - nYStart, nXSize, 1,
                pabyResult, nXSize, 1, GDT_Byte, 0, 0) != CE_None)
            {
                CPLError(CE_Failure, CPLE_AppDefined,
                    "RasterIO error when writing target raster at position (%d,%d), size (%d,%d)", 0, iLine - nYStart, nXSize, 1);
                eErr = CE_Failure;
                continue;
            }
        }

        std::swap(padfLastLineVal, padfThisLineVal);

        if(!pfnProgress((iLine + 1) / static_cast<double>(nYStop),
                         "", pProgressArg) )
        {
            CPLError( CE_Failure, CPLE_UserInterrupt, "User terminated" );
            eErr = CE_Failure;
            continue;
        }
    }

    if (hDstDS != nullptr)
        GDALClose(hDstDS);

    CPLFree(padfFirstLineVal);
    CPLFree(padfLastLineVal);
    CPLFree(padfThisLineVal);
    CPLFree(pabyResult);

    return eErr;
}
