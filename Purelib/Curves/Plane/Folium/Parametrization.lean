module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Nat.Order
-- The exposed parameter point retains this original negation parent.
public import Purelib.Algebra.Group.Negation
import Purelib.Curves.Plane.Cubic.Basic
public import Purelib.Curves.Plane.Folium.Basic
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

open Purelib

open Purelib.Curves.Plane.Folium

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

namespace Purelib.Curves.Plane.Folium.Parametrization

section Folium

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The denominator `1+t³` in equation (19.3). -/
def parameterDenominator (parameter : K) : K :=
  1 + parameter ^ 3

/-- The rational parameter point with coordinates `-3t/(1+t³)` and `-3t²/(1+t³)`.

Both coordinates retain the same displayed denominator and the field's
existing division operation; the point is defined for every parameter. -/
def parameterPoint (parameter : K) : Geometry.Plane.Point K
  :=
  ⟨(-3 * parameter) / parameterDenominator parameter,
    (-3 * parameter ^ 2) / parameterDenominator parameter⟩

/-- Every parameter with nonzero displayed denominator produces a point of the folium.

Substitution of the two coordinates into the retained cubic equation gives
zero using the supplied cancellation certificate for `1+t³`. -/
theorem parameterPoint_contains [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : parameterDenominator parameter ≠ 0) :
    (Folium.curve (K := K)).Contains (parameterPoint parameter) := by
  let denominator := parameterDenominator parameter
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold Curves.Plane.Cubic.Basic.CubicCurve.Contains parameterPoint
  rw [Folium.evaluate_curve]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  change
    ((-3 * parameter) * denominator⁻¹) ^ 3 +
        ((-3 * parameter ^ 2) * denominator⁻¹) ^ 3 +
        3 * ((-3 * parameter) * denominator⁻¹) *
          ((-3 * parameter ^ 2) * denominator⁻¹) = 0
  calc
    ((-3 * parameter) * denominator⁻¹) ^ 3 +
          ((-3 * parameter ^ 2) * denominator⁻¹) ^ 3 +
          3 * ((-3 * parameter) * denominator⁻¹) *
            ((-3 * parameter ^ 2) * denominator⁻¹) =
        27 * parameter ^ 3 * denominator⁻¹ ^ 2 *
          (1 - denominator * denominator⁻¹) := by
      unfold denominator parameterDenominator
      ring1
    _ = 0 := by rw [cancel]; ring1
end Folium

end Purelib.Curves.Plane.Folium.Parametrization

end
