module

public import Purelib.Geometry.Plane.Point.Basic

import Purelib.Algebra.Field.ExplicitField
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry

/-!
# Divine Proportions, §19.3: higher-order curves and tangents

A cubic remains a finite ten-coefficient record.  Its Taylor coefficients are
explicit polynomials in the displayed base point.  First- and second-order
non-singularity are constructive disjunctions, used directly to build the
tangent line and tangent conic.
-/

@[expose] public section

namespace Purelib.Curves.Plane.Cubic.Basic

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- A displayed cubic `⟨g:h:i:j:d:e:f:a:b:c⟩`, with a genuinely nonzero cubic part. -/
structure CubicCurve (K : Type*) [Zero K] where
  /-- The coefficient of x cubed. -/ g : K
  /-- The coefficient of x squared times y. -/ h : K
  /-- The coefficient of x times y squared. -/ i : K
  /-- The coefficient of y cubed. -/ j : K
  /-- The coefficient of x squared. -/ d : K
  /-- The coefficient of x times y. -/ e : K
  /-- The coefficient of y squared. -/ f : K
  /-- The coefficient of x. -/ a : K
  /-- The coefficient of y. -/ b : K
  /-- The constant coefficient. -/ c : K
  /-- At least one displayed degree-three coefficient is nonzero. -/ cubic_nonzero : g ≠ 0 ∨ h ≠ 0 ∨ i ≠ 0 ∨ j ≠ 0

constructive_injectivity Purelib.Curves.Plane.Cubic.Basic.CubicCurve

namespace CubicCurve

/-- Evaluation of the displayed cubic polynomial. -/
def evaluate (curve : Curves.Plane.Cubic.Basic.CubicCurve K) (point :
  Plane.Point K) : K :=
  curve.g * point.x ^ 3 + curve.h * point.x ^ 2 * point.y +
    curve.i * point.x * point.y ^ 2 + curve.j * point.y ^ 3 +
    curve.d * point.x ^ 2 + curve.e * point.x * point.y +
    curve.f * point.y ^ 2 + curve.a * point.x +
    curve.b * point.y + curve.c

/-- Incidence with a cubic is one finite polynomial equation. -/
def Contains (curve : Curves.Plane.Cubic.Basic.CubicCurve K) (point :
  Plane.Point K) : Prop :=
  curve.evaluate point = 0
end CubicCurve

end Purelib.Curves.Plane.Cubic.Basic

end
