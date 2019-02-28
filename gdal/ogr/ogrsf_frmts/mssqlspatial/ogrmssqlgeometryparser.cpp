/******************************************************************************
 *
 * Project:  MSSQL Spatial driver
 * Purpose:  Implements OGRMSSQLGeometryParser class to parse native SqlGeometries.
 * Author:   Tamas Szekeres, szekerest at gmail.com
 *
 ******************************************************************************
 * Copyright (c) 2010, Tamas Szekeres
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

#include "cpl_conv.h"
#include "ogr_mssqlspatial.h"

CPL_CVSID("$Id$")

/*   SqlGeometry/SqlGeography serialization format

Simple Point (SerializationProps & IsSinglePoint)
  [SRID][0x01][SerializationProps][Point][z][m]

Simple Line Segment (SerializationProps & IsSingleLineSegment)
  [SRID][0x01][SerializationProps][Point1][Point2][z1][z2][m1][m2]

Complex Geometries
  [SRID][VersionAttribute][SerializationProps][NumPoints][Point1]..[PointN][z1]..[zN][m1]..[mN]
  [NumFigures][Figure]..[Figure][NumShapes][Shape]..[Shape]

Complex Geometries (FigureAttribute == Curve)
  [SRID][VersionAttribute][SerializationProps][NumPoints][Point1]..[PointN][z1]..[zN][m1]..[mN]
  [NumFigures][Figure]..[Figure][NumShapes][Shape]..[Shape][NumSegments][SegmentType]..[SegmentType]

VersionAttribute (1 byte)
  0x01 = Katmai (MSSQL2008+)
  0x02 = Denali (MSSQL2012+)

SRID
  Spatial Reference Id (4 bytes)

SerializationProps (bitmask) 1 byte
  0x01 = HasZValues
  0x02 = HasMValues
  0x04 = IsValid
  0x08 = IsSinglePoint
  0x10 = IsSingleLineSegment
  0x20 = IsLargerThanAHemisphere

Point (2-4)x8 bytes, size depends on SerializationProps & HasZValues & HasMValues
  [x][y]                  - SqlGeometry
  [latitude][longitude]   - SqlGeography

Figure
  [FigureAttribute][PointOffset]

FigureAttribute - Katmai (1 byte)
  0x00 = Interior Ring
  0x01 = Stroke
  0x02 = Exterior Ring

FigureAttribute - Denali (1 byte)
  0x00 = None
  0x01 = Line
  0x02 = Arc
  0x03 = Curve

Shape
  [ParentFigureOffset][FigureOffset][ShapeType]

ShapeType (1 byte)
  0x00 = Unknown
  0x01 = Point
  0x02 = LineString
  0x03 = Polygon
  0x04 = MultiPoint
  0x05 = MultiLineString
  0x06 = MultiPolygon
  0x07 = GeometryCollection
  -- Denali
  0x08 = CircularString
  0x09 = CompoundCurve
  0x0A = CurvePolygon
  0x0B = FullGlobe

SegmentType (1 byte)
  0x00 = Line
  0x01 = Arc
  0x02 = FirstLine
  0x03 = FirstArc

*/

/************************************************************************/
/*                         Geometry parser macros                       */
/************************************************************************/

#define ReadInt32(nPos) (*((unsigned int*)(pszData + (nPos))))

#define ReadByte(nPos) (pszData[nPos])

#define ReadDouble(nPos) (*((double*)(pszData + (nPos))))

#define ParentOffset(iShape) (ReadInt32(nShapePos + (iShape) * 9 ))
#define FigureOffset(iShape) (ReadInt32(nShapePos + (iShape) * 9 + 4))
#define ShapeType(iShape) (ReadByte(nShapePos + (iShape) * 9 + 8))
#define SegmentType(iSegment) (ReadByte(nSegmentPos + (iSegment)))

#define NextFigureOffset(iShape) (iShape + 1 < nNumShapes? FigureOffset((iShape) +1) : nNumFigures)

#define FigureAttribute(iFigure) (ReadByte(nFigurePos + (iFigure) * 5))
#define PointOffset(iFigure) (ReadInt32(nFigurePos + (iFigure) * 5 + 1))
#define NextPointOffset(iFigure) (iFigure + 1 < nNumFigures? PointOffset((iFigure) +1) : nNumPoints)

#define ReadX(iPoint) (ReadDouble(nPointPos + 16 * (iPoint)))
#define ReadY(iPoint) (ReadDouble(nPointPos + 16 * (iPoint) + 8))
#define ReadZ(iPoint) (ReadDouble(nPointPos + 16 * nNumPoints + 8 * (iPoint)))
#define ReadM(iPoint) (ReadDouble(nPointPos + 24 * nNumPoints + 8 * (iPoint)))

/************************************************************************/
/*                   OGRMSSQLGeometryParser()                           */
/************************************************************************/

OGRMSSQLGeometryParser::OGRMSSQLGeometryParser(int nGeomColumnType)
{
    nColType = nGeomColumnType;
    pszData = nullptr;
    chProps = 0;
    nPointSize = 0;
    nPointPos = 0;
    nNumPoints = 0;
    nFigurePos = 0;
    nNumFigures = 0;
    nShapePos = 0;
    nNumShapes = 0;
    nSegmentPos = 0;
    nNumSegments = 0;
    nSRSId = 0;
}

/************************************************************************/
/*                         ReadPoint()                                  */
/************************************************************************/

OGRPoint* OGRMSSQLGeometryParser::ReadPoint(int iShape)
{
    int iFigure = FigureOffset(iShape);
    if ( iFigure < nNumFigures )
    {
        int iPoint = PointOffset(iFigure);
        if ( iPoint < nNumPoints )
        {
            if (nColType == MSSQLCOLTYPE_GEOGRAPHY)
            {
                if ( (chProps & SP_HASZVALUES) && (chProps & SP_HASMVALUES) )
                    return new OGRPoint(ReadY(iPoint), ReadX(iPoint), ReadZ(iPoint), ReadM(iPoint) );
                else if ( chProps & SP_HASZVALUES )
                    return new OGRPoint( ReadY(iPoint), ReadX(iPoint), ReadZ(iPoint) );
                else if ( chProps & SP_HASMVALUES )
                {
                    OGRPoint* poPoint = new OGRPoint( ReadY(iPoint), ReadX(iPoint) );
                    poPoint->setM( ReadZ(iPoint) );
                    return poPoint;
                }
                else
                    return new OGRPoint( ReadY(iPoint), ReadX(iPoint) );
            }
            else
            {
                if ( (chProps & SP_HASZVALUES) && (chProps & SP_HASMVALUES) )
                    return new OGRPoint( ReadX(iPoint), ReadY(iPoint), ReadZ(iPoint), ReadM(iPoint) );
                else if ( chProps & SP_HASZVALUES )
                    return new OGRPoint( ReadX(iPoint), ReadY(iPoint), ReadZ(iPoint) );
                else if ( chProps & SP_HASMVALUES )
                {
                    OGRPoint* poPoint = new OGRPoint( ReadX(iPoint), ReadY(iPoint) );
                    poPoint->setM( ReadZ(iPoint) );
                    return poPoint;
                }
                else
                    return new OGRPoint( ReadX(iPoint), ReadY(iPoint) );
            }
        }
    }
    return nullptr;
}

/************************************************************************/
/*                         ReadMultiPoint()                             */
/************************************************************************/

OGRMultiPoint* OGRMSSQLGeometryParser::ReadMultiPoint(int iShape)
{
    int i;
    OGRMultiPoint* poMultiPoint = new OGRMultiPoint();
    OGRGeometry* poGeom;

    for (i = iShape + 1; i < nNumShapes; i++)
    {
        poGeom = nullptr;
        if (ParentOffset(i) == (unsigned int)iShape)
        {
            if  ( ShapeType(i) == ST_POINT )
                poGeom = ReadPoint(i);
        }
        if ( poGeom )
            poMultiPoint->addGeometryDirectly( poGeom );
    }

    return poMultiPoint;
}

/************************************************************************/
/*                         ReadSimpleCurve()                            */
/************************************************************************/

OGRErr OGRMSSQLGeometryParser::ReadSimpleCurve(OGRSimpleCurve* poCurve, int iPoint, int iNextPoint)
{
    if (iPoint >= iNextPoint)
        return OGRERR_NOT_ENOUGH_DATA;

    poCurve->setNumPoints(iNextPoint - iPoint);
    int i = 0;
    while (iPoint < iNextPoint)
    {
        if (nColType == MSSQLCOLTYPE_GEOGRAPHY)
        {
            if ((chProps & SP_HASZVALUES) && (chProps & SP_HASMVALUES))
                poCurve->setPoint(i, ReadY(iPoint), ReadX(iPoint), ReadZ(iPoint), ReadM(iPoint));
            else if (chProps & SP_HASZVALUES)
                poCurve->setPoint(i, ReadY(iPoint), ReadX(iPoint), ReadZ(iPoint));
            else if (chProps & SP_HASMVALUES)
                poCurve->setPointM(i, ReadY(iPoint), ReadX(iPoint), ReadZ(iPoint));
            else
                poCurve->setPoint(i, ReadY(iPoint), ReadX(iPoint));
        }
        else
        {
            if ((chProps & SP_HASZVALUES) && (chProps & SP_HASMVALUES))
                poCurve->setPoint(i, ReadX(iPoint), ReadY(iPoint), ReadZ(iPoint), ReadM(iPoint));
            else if (chProps & SP_HASZVALUES)
                poCurve->setPoint(i, ReadX(iPoint), ReadY(iPoint), ReadZ(iPoint));
            else if (chProps & SP_HASMVALUES)
                poCurve->setPointM(i, ReadX(iPoint), ReadY(iPoint), ReadZ(iPoint));
            else
                poCurve->setPoint(i, ReadX(iPoint), ReadY(iPoint));
        }

        ++iPoint;
        ++i;
    }

    return OGRERR_NONE;
}

/************************************************************************/
/*                         ReadLineString()                             */
/************************************************************************/

OGRLineString* OGRMSSQLGeometryParser::ReadLineString(int iShape)
{
    int iFigure = FigureOffset(iShape);
    OGRLineString* poLineString = new OGRLineString();
    ReadSimpleCurve(poLineString, PointOffset(iFigure), NextPointOffset(iFigure));
    return poLineString;
}

/************************************************************************/
/*                         ReadLinearRing()                             */
/************************************************************************/

OGRLinearRing* OGRMSSQLGeometryParser::ReadLinearRing(int iShape)
{
    int iFigure = FigureOffset(iShape);
    OGRLinearRing* poLinearRing = new OGRLinearRing();
    ReadSimpleCurve(poLinearRing, PointOffset(iFigure), NextPointOffset(iFigure));
    return poLinearRing;
}

/************************************************************************/
/*                         ReadCircularString()                         */
/************************************************************************/

OGRCircularString* OGRMSSQLGeometryParser::ReadCircularString(int iShape)
{
    int iFigure = FigureOffset(iShape);
    OGRCircularString* poCircularString = new OGRCircularString();
    ReadSimpleCurve(poCircularString, PointOffset(iFigure), NextPointOffset(iFigure));
    return poCircularString;
}

/************************************************************************/
/*                         ReadMultiLineString()                        */
/************************************************************************/

OGRMultiLineString* OGRMSSQLGeometryParser::ReadMultiLineString(int iShape)
{
    int i;
    OGRMultiLineString* poMultiLineString = new OGRMultiLineString();
    OGRGeometry* poGeom;

    for (i = iShape + 1; i < nNumShapes; i++)
    {
        poGeom = nullptr;
        if (ParentOffset(i) == (unsigned int)iShape)
        {
            if  ( ShapeType(i) == ST_LINESTRING )
                poGeom = ReadLineString(i);
        }
        if ( poGeom )
            poMultiLineString->addGeometryDirectly( poGeom );
    }

    return poMultiLineString;
}

/************************************************************************/
/*                         ReadPolygon()                                */
/************************************************************************/

OGRPolygon* OGRMSSQLGeometryParser::ReadPolygon(int iShape)
{
    int iFigure;
    int iNextFigure = NextFigureOffset(iShape);

    OGRPolygon* poPoly = new OGRPolygon();
    for (iFigure = FigureOffset(iShape); iFigure < iNextFigure; iFigure++)
        poPoly->addRingDirectly(ReadLinearRing(iFigure));

    poPoly->closeRings();
    return poPoly;
}

/************************************************************************/
/*                         ReadMultiPolygon()                           */
/************************************************************************/

OGRMultiPolygon* OGRMSSQLGeometryParser::ReadMultiPolygon(int iShape)
{
    int i;
    OGRMultiPolygon* poMultiPolygon = new OGRMultiPolygon();
    OGRGeometry* poGeom;

    for (i = iShape + 1; i < nNumShapes; i++)
    {
        poGeom = nullptr;
        if (ParentOffset(i) == (unsigned int)iShape)
        {
            if ( ShapeType(i) == ST_POLYGON )
                poGeom = ReadPolygon(i);
        }
        if ( poGeom )
            poMultiPolygon->addGeometryDirectly( poGeom );
    }

    return poMultiPolygon;
}

/************************************************************************/
/*                         AddCurveSegment()                            */
/************************************************************************/

void OGRMSSQLGeometryParser::AddCurveSegment(OGRCompoundCurve* poCompoundCurve,
    OGRSimpleCurve* poCurve, int iPoint, int iNextPoint)
{
    if (poCurve != nullptr)
    {
        if (iPoint < iNextPoint)
        {
            ReadSimpleCurve(poCurve, iPoint, iNextPoint);
            poCompoundCurve->addCurveDirectly(poCurve);
        }
        else
            delete poCurve;
    }
}

/************************************************************************/
/*                         ReadCompoundCurve()                          */
/************************************************************************/

OGRCompoundCurve* OGRMSSQLGeometryParser::ReadCompoundCurve(int iFigure)
{
    int iPoint, iNextPoint, nPointsPrepared;
    char chSegmentType;
    OGRCompoundCurve* poCompoundCurve = new OGRCompoundCurve();
    iPoint = PointOffset(iFigure);
    iNextPoint = NextPointOffset(iFigure) - 1;

    OGRSimpleCurve* poCurve = nullptr;

    nPointsPrepared = 0;
    while (iPoint < iNextPoint && iSegment < nNumSegments)
    {
        switch (SegmentType(iSegment))
        {
        case SMT_FIRSTLINE:
            AddCurveSegment(poCompoundCurve, poCurve, iPoint - nPointsPrepared, iPoint + 1);
            poCurve = new OGRLineString();
            nPointsPrepared = 0;
        case SMT_LINE:
            ++nPointsPrepared;
            ++iPoint;
            break;
        case SMT_FIRSTARC:
            AddCurveSegment(poCompoundCurve, poCurve, iPoint - nPointsPrepared, iPoint + 1);
            poCurve = new OGRCircularString();
            nPointsPrepared = 0;    
        case SMT_ARC:           
            nPointsPrepared += 2;
            iPoint += 2;
            break;
        }
        ++iSegment;
    }

    // adding the last curve
    if (iPoint == iNextPoint)
        AddCurveSegment(poCompoundCurve, poCurve, iPoint - nPointsPrepared, iPoint + 1);

    return poCompoundCurve;
}

/************************************************************************/
/*                         ReadCurvePolygon()                         */
/************************************************************************/

OGRCurvePolygon* OGRMSSQLGeometryParser::ReadCurvePolygon(int iShape)
{
    int iFigure;
    int iNextFigure = NextFigureOffset(iShape);

    OGRCurvePolygon* poPoly = new OGRCurvePolygon();
    for (iFigure = FigureOffset(iShape); iFigure < iNextFigure; iFigure++)
    {
        switch (FigureAttribute(iFigure))
        {
        case 0x01:
            poPoly->addRingDirectly(ReadLinearRing(iFigure));
            break;
        case 0x02:
            poPoly->addRingDirectly(ReadCircularString(iFigure));
            break;
        case 0x03:
            poPoly->addRingDirectly(ReadCompoundCurve(iFigure));
            break;
        }      
    }
    poPoly->closeRings();
    return poPoly;
}

/************************************************************************/
/*                         ReadGeometryCollection()                     */
/************************************************************************/

OGRGeometryCollection* OGRMSSQLGeometryParser::ReadGeometryCollection(int iShape)
{
    int i;
    OGRGeometryCollection* poGeomColl = new OGRGeometryCollection();
    OGRGeometry* poGeom;

    for (i = iShape + 1; i < nNumShapes; i++)
    {
        poGeom = nullptr;
        if (ParentOffset(i) == (unsigned int)iShape)
        {
            switch (ShapeType(i))
            {
            case ST_POINT:
                poGeom = ReadPoint(i);
                break;
            case ST_LINESTRING:
                poGeom = ReadLineString(i);
                break;
            case ST_POLYGON:
                poGeom = ReadPolygon(i);
                break;
            case ST_MULTIPOINT:
                poGeom = ReadMultiPoint(i);
                break;
            case ST_MULTILINESTRING:
                poGeom = ReadMultiLineString(i);
                break;
            case ST_MULTIPOLYGON:
                poGeom = ReadMultiPolygon(i);
                break;
            case ST_GEOMETRYCOLLECTION:
                poGeom = ReadGeometryCollection(i);
                break;
            case ST_CIRCULARSTRING:
                poGeom = ReadCircularString(i);
                break;
            case ST_COMPOUNDCURVE:
                poGeom = ReadCompoundCurve(i);
                break;
            case ST_CURVEPOLYGON:
                poGeom = ReadCurvePolygon(i);
                break;
            }
        }
        if ( poGeom )
            poGeomColl->addGeometryDirectly( poGeom );
    }

    return poGeomColl;
}

/************************************************************************/
/*                         ParseSqlGeometry()                           */
/************************************************************************/

OGRErr OGRMSSQLGeometryParser::ParseSqlGeometry(unsigned char* pszInput,
                                int nLen, OGRGeometry **poGeom)
{
    if (nLen < 10)
        return OGRERR_NOT_ENOUGH_DATA;

    pszData = pszInput;

    /* store the SRS id for further use */
    nSRSId = ReadInt32(0);

    chVersion = ReadByte(4);

    if (chVersion == 0 || chVersion > 2)
    {
        return OGRERR_CORRUPT_DATA;
    }

    chProps = ReadByte(5);

    nPointSize = 16;

    if (chProps & SP_HASZVALUES)
        nPointSize += 8;

    if (chProps & SP_HASMVALUES)
        nPointSize += 8;

    if ( chProps & SP_ISSINGLEPOINT )
    {
        // single point geometry
        nNumPoints = 1;
        nPointPos = 6;

        if (nLen < 6 + nPointSize)
        {
            return OGRERR_NOT_ENOUGH_DATA;
        }

        if (nColType == MSSQLCOLTYPE_GEOGRAPHY)
        {
            if ((chProps & SP_HASZVALUES) && (chProps & SP_HASMVALUES))
                *poGeom = new OGRPoint(ReadY(0), ReadX(0), ReadZ(0), ReadM(0));
            else if (chProps & SP_HASZVALUES)
                *poGeom = new OGRPoint(ReadY(0), ReadX(0), ReadZ(0));
            else if (chProps & SP_HASMVALUES)
            {
                *poGeom = new OGRPoint(ReadY(0), ReadX(0));
                ((OGRPoint*)(*poGeom))->setM(ReadZ(0));
            }
            else
                *poGeom = new OGRPoint(ReadY(0), ReadX(0));
        }
        else
        {
            if ((chProps & SP_HASZVALUES) && (chProps & SP_HASMVALUES))
                *poGeom = new OGRPoint(ReadX(0), ReadY(0), ReadZ(0), ReadM(0));
            else if (chProps & SP_HASZVALUES)
                *poGeom = new OGRPoint(ReadX(0), ReadY(0), ReadZ(0));
            else if (chProps & SP_HASMVALUES)
            {
                *poGeom = new OGRPoint(ReadX(0), ReadY(0));
                ((OGRPoint*)(*poGeom))->setM(ReadZ(0));
            }
            else
                *poGeom = new OGRPoint(ReadX(0), ReadY(0));
        }
    }
    else if ( chProps & SP_ISSINGLELINESEGMENT )
    {
        // single line segment with 2 points
        nNumPoints = 2;
        nPointPos = 6;

        if (nLen < 6 + 2 * nPointSize)
        {
            return OGRERR_NOT_ENOUGH_DATA;
        }

        OGRLineString* line = new OGRLineString();
        line->setNumPoints(2);

        if (nColType == MSSQLCOLTYPE_GEOGRAPHY)
        {
            if ( (chProps & SP_HASZVALUES) && (chProps & SP_HASMVALUES) )
            {
                line->setPoint(0, ReadY(0), ReadX(0), ReadZ(0), ReadM(0));
                line->setPoint(1, ReadY(1), ReadX(1), ReadZ(1), ReadM(1));
            }
            else if ( chProps & SP_HASZVALUES )
            {
                line->setPoint(0, ReadY(0), ReadX(0), ReadZ(0));
                line->setPoint(1, ReadY(1), ReadX(1), ReadZ(1));
            }
            else if ( chProps & SP_HASMVALUES )
            {
                line->setPointM(0, ReadY(0), ReadX(0), ReadZ(0));
                line->setPointM(1, ReadY(1), ReadX(1), ReadZ(1));
            }
            else
            {
                line->setPoint(0, ReadY(0), ReadX(0));
                line->setPoint(1, ReadY(1), ReadX(1));
            }
        }
        else
        {
            if ( (chProps & SP_HASZVALUES) && (chProps & SP_HASMVALUES) )
            {
                line->setPoint(0, ReadX(0), ReadY(0), ReadZ(0), ReadM(0));
                line->setPoint(1, ReadX(1), ReadY(1), ReadZ(1), ReadM(1));
            }
            else if ( chProps & SP_HASZVALUES )
            {
                line->setPoint(0, ReadX(0), ReadY(0), ReadZ(0));
                line->setPoint(1, ReadX(1), ReadY(1), ReadZ(1));
            }
            else if ( chProps & SP_HASMVALUES )
            {
                line->setPointM(0, ReadX(0), ReadY(0), ReadZ(0));
                line->setPointM(1, ReadX(1), ReadY(1), ReadZ(1));
            }
            else
            {
                line->setPoint(0, ReadX(0), ReadY(0));
                line->setPoint(1, ReadX(1), ReadY(1));
            }
        }

        *poGeom = line;
    }
    else
    {
        // complex geometries
        nNumPoints = ReadInt32(6);

        if ( nNumPoints <= 0 )
        {
            return OGRERR_NONE;
        }

        // position of the point array
        nPointPos = 10;

        // position of the figures
        nFigurePos = nPointPos + nPointSize * nNumPoints + 4;

        if (nLen < nFigurePos)
        {
            return OGRERR_NOT_ENOUGH_DATA;
        }

        nNumFigures = ReadInt32(nFigurePos - 4);

        if ( nNumFigures <= 0 )
        {
            return OGRERR_NONE;
        }

        // position of the shapes
        nShapePos = nFigurePos + 5 * nNumFigures + 4;

        if (nLen < nShapePos)
        {
            return OGRERR_NOT_ENOUGH_DATA;
        }

        nNumShapes = ReadInt32(nShapePos - 4);

        if (nLen < nShapePos + 9 * nNumShapes)
        {
            return OGRERR_NOT_ENOUGH_DATA;
        }

        if ( nNumShapes <= 0 )
        {
            return OGRERR_NONE;
        }

        // position of the segments (for complex curve figures)
        if (chVersion == 0x02)
        {
            iSegment = 0;
            nSegmentPos = nShapePos + 9 * nNumShapes + 4;
            if (nLen > nShapePos)
            {
                // segment array is present
                nNumSegments = ReadInt32(nSegmentPos - 4);
                if (nLen < nSegmentPos + nNumSegments)
                {
                    return OGRERR_NOT_ENOUGH_DATA;
                }
            }
        }

        // pick up the root shape
        if ( ParentOffset(0) != 0xFFFFFFFF)
        {
            return OGRERR_CORRUPT_DATA;
        }

        // determine the shape type
        switch (ShapeType(0))
        {
        case ST_POINT:
            *poGeom = ReadPoint(0);
            break;
        case ST_LINESTRING:
            *poGeom = ReadLineString(0);
            break;
        case ST_POLYGON:
            *poGeom = ReadPolygon(0);
            break;
        case ST_MULTIPOINT:
            *poGeom = ReadMultiPoint(0);
            break;
        case ST_MULTILINESTRING:
            *poGeom = ReadMultiLineString(0);
            break;
        case ST_MULTIPOLYGON:
            *poGeom = ReadMultiPolygon(0);
            break;
        case ST_GEOMETRYCOLLECTION:
            *poGeom = ReadGeometryCollection(0);
            break;
        case ST_CIRCULARSTRING:
            *poGeom = ReadCircularString(0);
            break;
        case ST_COMPOUNDCURVE:
            *poGeom = ReadCompoundCurve(0);
            break;
        case ST_CURVEPOLYGON:
            *poGeom = ReadCurvePolygon(0);
            break;
        default:
            return OGRERR_UNSUPPORTED_GEOMETRY_TYPE;
        }
    }

    return OGRERR_NONE;
}
