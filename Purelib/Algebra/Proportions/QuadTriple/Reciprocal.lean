module
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Operations
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 21: two-dimensional problems

The applications are separated into their finite metric identities and the
geometric incidence arguments that supply those identities.  Denominators are
always accompanied by explicit nonzero certificates.
-/

namespace Purelib.Algebra.Proportions.QuadTriple.Reciprocal

section TwoDimensionalProblems

variable {K : Type*} [ExplicitField K]

/-- Cleared twist ratios carry a quad triple to reciprocal quadrances.

The supplied nonzero denominator and three nonzero quadrances justify two normalizations of the base quad triple. -/
theorem problem_4_from_twist_relations [DecidableEq K]
    (p₁ p₂ p₃ q₁ q₂ q₃ : K)
    (p₂Nonzero : p₂ ≠ 0)
    (q₁Nonzero : q₁ ≠ 0) (q₂Nonzero : q₂ ≠ 0)
    (q₃Nonzero : q₃ ≠ 0)
    (baseQuadTriple : Geometry.Trigonometry.QuadTriple p₁ p₂ p₃)
    (firstTwistRelation : p₁ * q₁ = p₂ * q₂)
    (secondTwistRelation : p₃ * q₃ = p₂ * q₂) :
    Geometry.Trigonometry.QuadTriple (1 / q₁) (1 / q₂) (1 / q₃) := by
  have firstRatio : p₁ / p₂ = q₂ / q₁ :=
    Algebra.Field.Ratio.ratio_eq_of_cross_product p₂Nonzero q₁Nonzero (by
      calc
        p₁ * q₁ = p₂ * q₂ := firstTwistRelation
        _ = q₂ * p₂ := by ring1)
  have thirdRatio : p₃ / p₂ = q₂ / q₃ :=
    Algebra.Field.Ratio.ratio_eq_of_cross_product p₂Nonzero q₃Nonzero (by
      calc
        p₃ * q₃ = p₂ * q₂ := secondTwistRelation
        _ = q₂ * p₂ := by ring1)
  have middleRatio : p₂ / p₂ = (1 : K) := by
    calc
      p₂ / p₂ = (1 / p₂) * p₂ := by
        simp only [ExplicitField.div_eq_mul_inv]
        ring1
      _ = 1 := ExplicitField.div_mul_cancel 1 p₂Nonzero
  have normalized := QuadTriple.Operations.quadTriple_normalize p₁ p₂ p₃ p₂ baseQuadTriple
  rw [firstRatio, middleRatio, thirdRatio] at normalized
  have reciprocalTriple :=
    QuadTriple.Operations.quadTriple_normalize (q₂ / q₁) 1 (q₂ / q₃) q₂ normalized
  have q₂Cancel : q₂ * q₂⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel q₂ q₂Nonzero
  have firstCoordinate : (q₂ / q₁) / q₂ = 1 / q₁ := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      q₂ * q₁⁻¹ * q₂⁻¹ = (q₂ * q₂⁻¹) * q₁⁻¹ := by ring1
      _ = q₁⁻¹ := by rw [q₂Cancel, one_mul]
      _ = 1 * q₁⁻¹ := by rw [one_mul]
  have thirdCoordinate : (q₂ / q₃) / q₂ = 1 / q₃ := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      q₂ * q₃⁻¹ * q₂⁻¹ = (q₂ * q₂⁻¹) * q₃⁻¹ := by ring1
      _ = q₃⁻¹ := by rw [q₂Cancel, one_mul]
      _ = 1 * q₃⁻¹ := by rw [one_mul]
  rw [firstCoordinate, thirdCoordinate] at reciprocalTriple
  exact reciprocalTriple
end TwoDimensionalProblems
end Purelib.Algebra.Proportions.QuadTriple.Reciprocal

end
