module

public import Purelib.Geometry
public import formalisations.DivineProportions.Chapters

-- Preserve the numbered theorem surface through its migrated subject owners.
public import Purelib.Geometry.Circles.Conic.Tangent
public import Purelib.Geometry.Circles.Diameter.Right
public import Purelib.Geometry.Circles.Power
public import Purelib.Geometry.Circles.Projective.Parametrization
public import Purelib.Geometry.Conics.Parabola.Reflection
public import Purelib.Geometry.Conics.Parabola.Uniqueness
public import Purelib.Geometry.Plane.Isometry.Incidence
public import Purelib.Geometry.Plane.Isometry.Specification
public import Purelib.Geometry.Plane.Line.Cross.Quadruple
public import Purelib.Geometry.Plane.Line.Cross.Triple
public import Purelib.Geometry.Plane.Line.Spread.Consecutive
public import Purelib.Geometry.Plane.Line.Spread.Orthogonality
public import Purelib.Geometry.Plane.Line.Spread.Quadruple
public import Purelib.Geometry.Plane.Line.Spread.Realization
public import Purelib.Geometry.Plane.Line.Spread.Triple
public import Purelib.Geometry.Plane.Line.Trigonometry.Conversion
public import Purelib.Geometry.Plane.Line.Turn.Triple
public import Purelib.Geometry.Plane.Line.Twist.Triple
public import Purelib.Geometry.Plane.Line.VertexBisector.Classification
public import Purelib.Geometry.Plane.Point.Affine.Quadrance
public import Purelib.Geometry.Plane.Point.Quadrance.Collinear
public import Purelib.Geometry.Plane.Reflection.Spread
public import Purelib.Geometry.Polygons.Regular.CornerTriangle
public import Purelib.Geometry.Polygons.SignedArea.Fan
public import Purelib.Geometry.Quadrilaterals.Bretschneider
public import Purelib.Geometry.Quadrilaterals.Cyclic.Determinant
public import Purelib.Geometry.Quadrilaterals.Cyclic.SignedArea
public import Purelib.Geometry.Quadrilaterals.Cyclic.Spread
public import Purelib.Geometry.Quadrilaterals.Parallelogram.Quadrance
public import Purelib.Geometry.Stars.Regular.OrderFive.Classification
public import Purelib.Geometry.Stars.Regular.OrderSeven.Classification
public import Purelib.Geometry.Stars.Regular.OrderThree.Classification
public import Purelib.Geometry.Triangles.Centers.Euler
public import Purelib.Geometry.Triangles.Ceva.Proportions
public import Purelib.Geometry.Triangles.Circumcenter.ExtendedSpread
public import Purelib.Geometry.Triangles.Equilateral.Numeric
public import Purelib.Geometry.Triangles.Incenter.Quadrance
public import Purelib.Geometry.Triangles.Incenter.Spread
public import Purelib.Geometry.Triangles.Isosceles.Median
public import Purelib.Geometry.Triangles.Isosceles.Null
public import Purelib.Geometry.Triangles.Isosceles.Numeric
public import Purelib.Geometry.Triangles.Medial.Quadrance
public import Purelib.Geometry.Triangles.Medial.Similarity
public import Purelib.Geometry.Triangles.Median.Quadrance
public import Purelib.Geometry.Triangles.Median.Spread
public import Purelib.Geometry.Triangles.Menelaus.Proportions
public import Purelib.Geometry.Triangles.NinePointCircle
public import Purelib.Geometry.Triangles.Proportions
public import Purelib.Geometry.Triangles.Right.Midpoint
public import Purelib.Geometry.Triangles.Right.Quadrance
public import Purelib.Geometry.Triangles.Right.Trigonometry
public import Purelib.Geometry.Triangles.Trigonometry.Cross
public import Purelib.Geometry.Triangles.Trigonometry.Spread
public import Purelib.Geometry.Trigonometry.Spread.Cyclic.Diagonals
public import Purelib.Geometry.Trigonometry.Spread.Cyclic.Ptolemy
public import Purelib.Geometry.Trigonometry.Spread.Triple.Ratio
public import Purelib.Polynomial.Recurrence.Spread.Composition
public import Purelib.Polynomial.Recurrence.Spread.Formula
public import Purelib.Polynomial.Recurrence.Spread.Triple

/-!
# Divine Proportions

A constructive, finite-algebra formalization of N. J. Wildberger's
*Divine Proportions*.  The chapter modules follow the source's numbering.  The
coverage ledger in `formalisations/DivineProportions/coverage.md` records every named theorem,
worked example, exercise, and solved problem.
-/
