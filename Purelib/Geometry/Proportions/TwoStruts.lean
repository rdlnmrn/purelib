module
import Purelib.Algebra.Field.Ratio
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Trigonometry.QuadTriple.Operations
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Trigonometry

open Purelib.Geometry.Trigonometry.QuadTriple

@[expose] public section

/-!
# Divine Proportions, Chapter 11: the two struts theorem

Triangle proportions reduces the geometric configuration to the two
normalized quad triples used below.  Homogeneity then removes every quotient
with explicit cancellation of `p` and `r`.
-/

namespace Purelib.Geometry.Proportions.TwoStruts

variable {K : Type*} [ExplicitField K]

/-- Theorem 74 (Two struts). These are exactly the two normalized quad triples obtained in the book after applying
Triangle proportions and dividing the original Triple-quad identities by `P₁²` and `R₁²`. -/
theorem two_struts
    (p r m n : K) (pNonzero : p ≠ 0) (rNonzero : r ≠ 0)
    (firstNormalized : Geometry.Trigonometry.QuadTriple (m / r) 1 (1 / p))
    (secondNormalized : Geometry.Trigonometry.QuadTriple (n / p) 1 (1 / r)) :
    Geometry.Trigonometry.QuadTriple r (r * p) (m * p) ∧
      Geometry.Trigonometry.QuadTriple p (r * p) (n * r) := by
  have firstScaled := Operations.quadTriple_scale (m / r) 1 (1 / p) (r * p)
    firstNormalized
  have firstCoordinate : (r * p) * (m / r) = m * p := by
    calc
      (r * p) * (m / r) = (m / r) * r * p := by ring1
      _ = m * p := by
        rw [ExplicitField.div_mul_cancel m rNonzero]
  have firstMiddle : (r * p) * 1 = r * p := by ring1
  have firstLast : (r * p) * (1 / p) = r := by
    calc
      (r * p) * (1 / p) = r * ((1 / p) * p) := by ring1
      _ = r := by
        rw [ExplicitField.div_mul_cancel 1 pNonzero]
        ring1
  rw [firstCoordinate, firstMiddle, firstLast] at firstScaled
  have secondScaled := Operations.quadTriple_scale (n / p) 1 (1 / r) (p * r)
    secondNormalized
  have secondCoordinate : (p * r) * (n / p) = n * r := by
    calc
      (p * r) * (n / p) = (n / p) * p * r := by ring1
      _ = n * r := by
        rw [ExplicitField.div_mul_cancel n pNonzero]
  have secondMiddle : (p * r) * 1 = r * p := by ring1
  have secondLast : (p * r) * (1 / r) = p := by
    calc
      (p * r) * (1 / r) = p * ((1 / r) * r) := by ring1
      _ = p := by
        rw [ExplicitField.div_mul_cancel 1 rNonzero]
        ring1
  rw [secondCoordinate, secondMiddle, secondLast] at secondScaled
  exact ⟨Operations.quadTriple_reverse (m * p) (r * p) r firstScaled,
    Operations.quadTriple_reverse (n * r) (r * p) p secondScaled⟩

/-- The algebraic interface produced directly by the geometric proof. The two input quad triples come from the collinear
triples in Figure 11.3; the two displayed proportions are equation (11.1) and its symmetric counterpart. -/
theorem two_struts_of_proportions
    (p r m n Q₁ Q₂ P₁ P₂ R₁ R₂ : K)
    (pNonzero : p ≠ 0) (rNonzero : r ≠ 0)
    (P₁Nonzero : P₁ ≠ 0) (R₁Nonzero : R₁ ≠ 0)
    (pDefinition : p * P₂ = P₁)
    (rDefinition : r * R₂ = R₁)
    (firstProportion : Q₂ / P₁ = m / r)
    (secondProportion : Q₁ / R₁ = n / p)
    (firstCollinearTriple : Geometry.Trigonometry.QuadTriple Q₂ P₁ P₂)
    (secondCollinearTriple : Geometry.Trigonometry.QuadTriple Q₁ R₁ R₂) :
    Geometry.Trigonometry.QuadTriple r (r * p) (m * p) ∧
      Geometry.Trigonometry.QuadTriple p (r * p) (n * r) := by
  have firstNormalizedRaw := Operations.quadTriple_normalize Q₂ P₁ P₂ P₁
    firstCollinearTriple
  have secondNormalizedRaw := Operations.quadTriple_normalize Q₁ R₁ R₂ R₁
    secondCollinearTriple
  have P₂Ratio : P₂ / P₁ = 1 / p := by
    apply Ratio.ratio_eq_of_cross_product P₁Nonzero pNonzero
    calc
      P₂ * p = p * P₂ := by ring1
      _ = P₁ := pDefinition
      _ = 1 * P₁ := by ring1
  have R₂Ratio : R₂ / R₁ = 1 / r := by
    apply Ratio.ratio_eq_of_cross_product R₁Nonzero rNonzero
    calc
      R₂ * r = r * R₂ := by ring1
      _ = R₁ := rDefinition
      _ = 1 * R₁ := by ring1
  have P₁Ratio : P₁ / P₁ = 1 := by
    rw [ExplicitField.div_eq_mul_inv]
    exact ExplicitField.mul_inv_cancel P₁ P₁Nonzero
  have R₁Ratio : R₁ / R₁ = 1 := by
    rw [ExplicitField.div_eq_mul_inv]
    exact ExplicitField.mul_inv_cancel R₁ R₁Nonzero
  rw [firstProportion, P₁Ratio, P₂Ratio] at firstNormalizedRaw
  rw [secondProportion, R₁Ratio, R₂Ratio] at secondNormalizedRaw
  exact two_struts p r m n pNonzero rNonzero firstNormalizedRaw
    secondNormalizedRaw

end Purelib.Geometry.Proportions.TwoStruts

end
