module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Basic

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 3 finite examples

This module records the literal coordinate data in Examples 3.2, 3.6, and
3.7, together with an explicit quadrilateral for Exercise 3.14.  The
characteristic-thirteen calculations are generic polynomial certificates;
they do not enumerate a finite-field carrier or install another global field
model.
-/

namespace Purelib.Geometry.Plane.Point.Laws

section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
omit [Purelib.Algebra.Field.ExplicitField K] in
/-- Different first coordinates imply that two Cartesian points are distinct. -/
public theorem points_ne_of_x_ne
    {left right : Point K} (xDifferent : left.x ≠ right.x) : left ≠ right := by
  intro equal
  exact xDifferent (congrArg x equal)

omit [Purelib.Algebra.Field.ExplicitField K] in
/-- Different second coordinates imply that two Cartesian points are distinct. -/
public theorem points_ne_of_y_ne
    {left right : Point K} (yDifferent : left.y ≠ right.y) : left ≠ right := by
  intro equal
  exact yDifferent (congrArg y equal)

end

end

end Purelib.Geometry.Plane.Point.Laws

end

end
