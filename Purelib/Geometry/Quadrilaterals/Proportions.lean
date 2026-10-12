module
import Purelib.Algebra.Field.Ratio

public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

@[expose] public section

/-!
# Divine Proportions, Chapter 11: quadrilateral proportions

As for triangle proportions, the cross-product identity is primary and the
book's quotient is recovered from explicit nonzero denominator certificates.
-/

namespace Purelib.Geometry.Quadrilaterals.Proportions

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Two cleared spread laws sharing a diagonal imply the quadrilateral cross-product relation. -/
theorem quadrilateral_proportions_cleared
    (r₁ r₂ s₁ s₂ R₁ R₂ R : K)
    (firstTriangle : r₁ * R = s₁ * R₁)
    (secondTriangle : r₂ * R = s₂ * R₂) :
    r₁ * (s₂ * R₂) = (s₁ * R₁) * r₂ := by
  calc
    r₁ * (s₂ * R₂) = r₁ * (r₂ * R) := by rw [← secondTriangle]
    _ = (r₁ * R) * r₂ := by ring1
    _ = (s₁ * R₁) * r₂ := by rw [firstTriangle]

/-- Quadrilateral proportions obtained from two cleared spread laws.

The displayed denominator factors are nonzero, so cancellation gives the ratio of the two side quantities. -/
theorem quadrilateral_proportions
    (r₁ r₂ s₁ s₂ R₁ R₂ R : K)
    (r₂Nonzero : r₂ ≠ 0) (s₂Nonzero : s₂ ≠ 0)
    (R₂Nonzero : R₂ ≠ 0)
    (firstTriangle : r₁ * R = s₁ * R₁)
    (secondTriangle : r₂ * R = s₂ * R₂) :
    r₁ / r₂ = (s₁ * R₁) / (s₂ * R₂) := by
  have denominatorNonzero : s₂ * R₂ ≠ 0 :=
    Algebra.Field.ExplicitField.mul_ne_zero s₂Nonzero R₂Nonzero
  exact Ratio.ratio_eq_of_cross_product r₂Nonzero denominatorNonzero
    (Geometry.Quadrilaterals.Proportions.quadrilateral_proportions_cleared r₁ r₂ s₁ s₂ R₁ R₂ R
      firstTriangle secondTriangle)

/-- Two quotient spread laws imply the quadrilateral proportion.

The shared diagonal and each displayed denominator have explicit nonzero certificates. -/
theorem quadrilateral_proportions_of_spread_laws
    (r₁ r₂ s₁ s₂ R₁ R₂ R : K)
    (r₂Nonzero : r₂ ≠ 0) (s₂Nonzero : s₂ ≠ 0)
    (R₁Nonzero : R₁ ≠ 0) (R₂Nonzero : R₂ ≠ 0)
    (RNonzero : R ≠ 0)
    (firstTriangle : r₁ / R₁ = s₁ / R)
    (secondTriangle : r₂ / R₂ = s₂ / R) :
    r₁ / r₂ = (s₁ * R₁) / (s₂ * R₂) := by
  have firstCleared : r₁ * R = s₁ * R₁ :=
    Ratio.cross_product_of_ratio_eq R₁Nonzero RNonzero firstTriangle
  have secondCleared : r₂ * R = s₂ * R₂ :=
    Ratio.cross_product_of_ratio_eq R₂Nonzero RNonzero secondTriangle
  exact Geometry.Quadrilaterals.Proportions.quadrilateral_proportions r₁ r₂ s₁ s₂ R₁ R₂ R
    r₂Nonzero s₂Nonzero R₂Nonzero firstCleared secondCleared

end Purelib.Geometry.Quadrilaterals.Proportions

end
