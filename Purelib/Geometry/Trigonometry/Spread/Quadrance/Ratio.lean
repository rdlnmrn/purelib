module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Ratio
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

/-!
# Divine Proportions, Exercises 6.3--6.6

The common spread ratio and the two null-triangle formulas are finite
consequences of the Quadrea-spread identity.  The rational triangle inequality
is the statement that the coordinate-determinant square is nonnegative; no
absolute value, square root, compactness, or extremum is introduced.
-/

@[expose] public section

namespace Purelib.Geometry.Trigonometry.Spread.Quadrance.Ratio

variable {K : Type*} [ExplicitField K]

/-- The three spread-to-quadrance ratios agree under the cyclic quadrea equations.

For nonzero quadrances and nonzero two, their common value is the quadrea divided by four times the product of the three
quadrances (Exercise 6.3). -/
theorem spread_quadrance_ratios
    (q₁ q₂ q₃ s₁ s₂ s₃ area : K)
    (twoNonzero : (2 : K) ≠ 0)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (q₃Nonzero : q₃ ≠ 0)
    (areaAtFirst : area = 4 * q₂ * q₃ * s₁)
    (areaAtSecond : area = 4 * q₁ * q₃ * s₂)
    (areaAtThird : area = 4 * q₁ * q₂ * s₃) :
    s₁ / q₁ = s₂ / q₂ ∧
      s₂ / q₂ = s₃ / q₃ ∧
      s₃ / q₃ = area / (4 * q₁ * q₂ * q₃) := by
  have fourNonzero := Characteristic.Nonzero.four_ne_zero twoNonzero
  have denominatorNonzero : 4 * q₁ * q₂ * q₃ ≠ 0 :=
    ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (ExplicitField.mul_ne_zero fourNonzero q₁Nonzero)
        q₂Nonzero)
      q₃Nonzero
  have firstCommon :
      s₁ / q₁ = area / (4 * q₁ * q₂ * q₃) := by
    apply Ratio.ratio_eq_of_cross_product q₁Nonzero denominatorNonzero
    rw [areaAtFirst]
    ring1
  have secondCommon :
      s₂ / q₂ = area / (4 * q₁ * q₂ * q₃) := by
    apply Ratio.ratio_eq_of_cross_product q₂Nonzero denominatorNonzero
    rw [areaAtSecond]
    ring1
  have thirdCommon :
      s₃ / q₃ = area / (4 * q₁ * q₂ * q₃) := by
    apply Ratio.ratio_eq_of_cross_product q₃Nonzero denominatorNonzero
    rw [areaAtThird]
    ring1
  exact ⟨firstCommon.trans secondCommon.symm,
    secondCommon.trans thirdCommon.symm, thirdCommon⟩

end Purelib.Geometry.Trigonometry.Spread.Quadrance.Ratio

end
