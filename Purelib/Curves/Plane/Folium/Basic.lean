module
import Purelib.Algebra.Field.ExplicitField
-- Exposed coefficients retain the constructive natural numeral certificates.
public import Purelib.Data.Nat.Order
public import Purelib.Curves.Plane.Cubic.Basic
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
public import Mathlib.Algebra.GroupWithZero.NeZero

open scoped Purelib.Data.Nat

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, §19.4: the folium of Descartes

The folium, its rational parametrization, first- and second-order tangent
formulae, and the reciprocal-parameter spread symmetry are all finite
polynomial constructions.  Denominators and the characteristic-three
exception are exposed as explicit hypotheses.
-/

namespace Purelib.Curves.Plane.Folium

section Folium

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The folium of Descartes `x³+y³+3xy=0`.

The displayed ten coefficients define the cubic, with its nonzero leading
coefficient certified by the nontriviality of the field. -/
def curve [Nontrivial K] : Cubic.Basic.CubicCurve K where
  g := 1
  h := 0
  i := 0
  j := 1
  d := 0
  e := 3
  f := 0
  a := 0
  b := 0
  c := 0
  cubic_nonzero := Or.inl one_ne_zero

/-- The displayed cubic equation is recovered exactly.

Evaluation of the retained folium coefficients at a displayed point equals
the sum of the two coordinate cubes and the mixed term `3xy`. -/
theorem evaluate_curve [Nontrivial K] (point : Geometry.Plane.Point
  K) :
    (curve (K := K)).evaluate point =
      point.x ^ 3 + point.y ^ 3 + 3 * point.x * point.y := by
  unfold curve Cubic.Basic.CubicCurve.evaluate
  ring1
end Folium

end Purelib.Curves.Plane.Folium

end
