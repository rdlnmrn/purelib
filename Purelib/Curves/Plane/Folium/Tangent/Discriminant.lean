module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Folium.Parametrization
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane.Folium.Parametrization

section
@[expose] public section

/-!
# Divine Proportions, §19.4: the folium of Descartes

The folium, its rational parametrization, first- and second-order tangent
formulae, and the reciprocal-parameter spread symmetry are all finite
polynomial constructions.  Denominators and the characteristic-three
exception are exposed as explicit hypotheses.
-/

namespace Purelib.Curves.Plane.Folium.Tangent.Discriminant

section Folium

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The polynomial controlling the determinant in Example 19.8. -/
def determinantPolynomial (parameter : K) : K :=
  parameter ^ 6 - 34 * parameter ^ 3 + 1

/-- Example 19.8's matrix determinant, with the factor `1/4` cleared: `4 det M = -(t⁶-34t³+1)`. -/
theorem four_mul_associatedMatrixDeterminant (parameter :
  K) :
    4 * (3 * parameter * (3 * parameter ^ 2)) -
        (-(Parametrization.parameterDenominator parameter)) ^ 2 =
      -(determinantPolynomial parameter) := by
  unfold Parametrization.parameterDenominator determinantPolynomial
  ring1

/-- The two displayed quadratic roots in Example 19.8 are roots whenever an explicit square root of `2` is supplied. -/
theorem determinant_quadratic_roots
    (rootTwo : K) (rootTwoSquared : rootTwo ^ 2 = 2) :
    let lower := 17 - 12 * rootTwo
    let upper := 17 + 12 * rootTwo
    lower ^ 2 - 34 * lower + 1 = 0 ∧
      upper ^ 2 - 34 * upper + 1 = 0 ∧ lower * upper = 1 := by
  dsimp only
  constructor
  · rw [show (17 - 12 * rootTwo) ^ 2 - 34 * (17 - 12 * rootTwo) + 1 =
        144 * (rootTwo ^ 2 - 2) by ring1,
      rootTwoSquared]
    ring1
  · constructor
    · rw [show (17 + 12 * rootTwo) ^ 2 - 34 * (17 + 12 * rootTwo) + 1 =
          144 * (rootTwo ^ 2 - 2) by ring1,
        rootTwoSquared]
      ring1
    · rw [show (17 - 12 * rootTwo) * (17 + 12 * rootTwo) =
          289 - 144 * rootTwo ^ 2 by ring1,
        rootTwoSquared]
      ring1

/-- A cube root of either displayed quadratic root makes the determinant polynomial vanish. No completed real-number or
order structure is used. -/
theorem determinantPolynomial_eq_zero_of_cube_root
    (parameter root : K)
    (rootEquation : root ^ 2 - 34 * root + 1 = 0)
    (cubeRoot : parameter ^ 3 = root) :
    determinantPolynomial parameter = 0 := by
  unfold determinantPolynomial
  rw [show parameter ^ 6 = (parameter ^ 3) ^ 2 by ring1, cubeRoot]
  exact rootEquation
end Folium

end Purelib.Curves.Plane.Folium.Tangent.Discriminant

end
