module
public import Purelib.Geometry.Triangles.NonNull.Basic
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Triangles

section
@[expose] public section

/-!
# Divine Proportions, Chapter 10 further exercises

This module contains the equilateral centroid calculations, the unit-
quadrance existence criterion, and the corrected right-altitude formulas.
-/

namespace Purelib.Geometry.Triangles.Altitude.Foot.NonNullTriangle

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The explicit foot from the third vertex to the opposite side. -/
def thirdAltitudeFoot [DecidableEq K]
    (triangle : NonNull.Basic.NonNullTriangle K) : Purelib.Geometry.Plane.Point K :=
  Altitude.altitudeFoot triangle.third
    (Incidence.lineThrough triangle.first triangle.second
      triangle.firstSecondDistinct)
    triangle.firstSecondNonNull
end Purelib.Geometry.Triangles.Altitude.Foot.NonNullTriangle

end
