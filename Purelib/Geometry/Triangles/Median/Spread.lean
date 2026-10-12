module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Chapter 11: median quadrance

The denominator-cleared identity already proved for right midpoints gives the
median formula directly.  The source's extra `Q₁ ≠ 0` hypothesis is not needed;
only characteristic two is excluded so that the displayed midpoint and `/4`
normalization have their intended meaning.
-/

namespace Purelib.Geometry.Triangles.Median.Spread

variable {K : Type*} [ExplicitField K]

/-- The three median-spread equations with their common denominator retained.

The median quadrance identity and five cleared spread laws imply the result when the cancelled median and side
quadrances, and two, are nonzero. -/
theorem median_spreads_cleared
    (Q₁ Q₂ Q₃ P s₁ s₂ s₃ r u v : K)
    (PNonzero : P ≠ 0) (Q₁Nonzero : Q₁ ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (medianValue : P * 4 = 2 * (Q₂ + Q₃) - Q₁)
    (triangleLaw₂ : s₁ * Q₂ = s₂ * Q₁)
    (triangleLaw₃ : s₁ * Q₃ = s₃ * Q₁)
    (halfLawR : r * P = s₂ * Q₃)
    (halfLawU : 4 * u * P = s₂ * Q₁)
    (halfLawV : 4 * v * P = s₃ * Q₁) :
    r * (2 * (s₂ + s₃) - s₁) = 4 * s₂ * s₃ ∧
      u * (2 * (s₂ + s₃) - s₁) = s₁ * s₂ ∧
      v * (2 * (s₂ + s₃) - s₁) = s₁ * s₃ := by
  let denominator := 2 * (s₂ + s₃) - s₁
  have weightedMedian : denominator * Q₁ = s₁ * (P * 4) := by
    calc
      denominator * Q₁ =
          2 * (s₂ * Q₁ + s₃ * Q₁) - s₁ * Q₁ := by
        unfold denominator
        ring1
      _ = 2 * (s₁ * Q₂ + s₁ * Q₃) - s₁ * Q₁ := by
        rw [← triangleLaw₂, ← triangleLaw₃]
      _ = s₁ * (2 * (Q₂ + Q₃) - Q₁) := by ring1
      _ = s₁ * (P * 4) := by rw [medianValue]
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have PQ₁Nonzero : P * Q₁ ≠ 0 :=
    ExplicitField.mul_ne_zero PNonzero Q₁Nonzero
  have fourPNonzero : (4 : K) * P ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero PNonzero
  have rFormula : r * denominator = 4 * s₂ * s₃ := by
    apply ExplicitField.eq_of_mul_eq_mul_right PQ₁Nonzero
    calc
      (r * denominator) * (P * Q₁) =
          (denominator * Q₁) * (r * P) := by ring1
      _ = (s₁ * (P * 4)) * (s₂ * Q₃) := by
        rw [weightedMedian, halfLawR]
      _ = 4 * s₂ * P * (s₁ * Q₃) := by ring1
      _ = 4 * s₂ * P * (s₃ * Q₁) := by rw [triangleLaw₃]
      _ = (4 * s₂ * s₃) * (P * Q₁) := by ring1
  have uFormula : u * denominator = s₁ * s₂ := by
    apply ExplicitField.eq_of_mul_eq_mul_right fourPNonzero
    calc
      (u * denominator) * (4 * P) =
          denominator * (4 * u * P) := by ring1
      _ = denominator * (s₂ * Q₁) := by rw [halfLawU]
      _ = s₂ * (denominator * Q₁) := by ring1
      _ = s₂ * (s₁ * (P * 4)) := by rw [weightedMedian]
      _ = (s₁ * s₂) * (4 * P) := by ring1
  have vFormula : v * denominator = s₁ * s₃ := by
    apply ExplicitField.eq_of_mul_eq_mul_right fourPNonzero
    calc
      (v * denominator) * (4 * P) =
          denominator * (4 * v * P) := by ring1
      _ = denominator * (s₃ * Q₁) := by rw [halfLawV]
      _ = s₃ * (denominator * Q₁) := by ring1
      _ = s₃ * (s₁ * (P * 4)) := by rw [weightedMedian]
      _ = (s₁ * s₃) * (4 * P) := by ring1
  exact ⟨by simpa only [denominator] using rFormula,
    by simpa only [denominator] using uFormula,
    by simpa only [denominator] using vFormula⟩

/-- The three spreads determined by a median as quotients of the original triangle spreads.

The common spread denominator, the cancelled median and side quadrances, and two are all nonzero. -/
theorem median_spreads
    (Q₁ Q₂ Q₃ P s₁ s₂ s₃ r u v : K)
    (PNonzero : P ≠ 0) (Q₁Nonzero : Q₁ ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (denominatorNonzero : 2 * (s₂ + s₃) - s₁ ≠ 0)
    (medianValue : P * 4 = 2 * (Q₂ + Q₃) - Q₁)
    (triangleLaw₂ : s₁ * Q₂ = s₂ * Q₁)
    (triangleLaw₃ : s₁ * Q₃ = s₃ * Q₁)
    (halfLawR : r * P = s₂ * Q₃)
    (halfLawU : 4 * u * P = s₂ * Q₁)
    (halfLawV : 4 * v * P = s₃ * Q₁) :
    r = (4 * s₂ * s₃) / (2 * (s₂ + s₃) - s₁) ∧
      u = (s₁ * s₂) / (2 * (s₂ + s₃) - s₁) ∧
      v = (s₁ * s₃) / (2 * (s₂ + s₃) - s₁) := by
  rcases median_spreads_cleared Q₁ Q₂ Q₃ P s₁ s₂ s₃ r u v
    PNonzero Q₁Nonzero twoNonzero medianValue triangleLaw₂ triangleLaw₃
    halfLawR halfLawU halfLawV with ⟨rCleared, uCleared, vCleared⟩
  constructor
  · apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
    calc
      r * (2 * (s₂ + s₃) - s₁) = 4 * s₂ * s₃ := rCleared
      _ = ((4 * s₂ * s₃) / (2 * (s₂ + s₃) - s₁)) *
          (2 * (s₂ + s₃) - s₁) :=
        (ExplicitField.div_mul_cancel _ denominatorNonzero).symm
  constructor
  · apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
    calc
      u * (2 * (s₂ + s₃) - s₁) = s₁ * s₂ := uCleared
      _ = ((s₁ * s₂) / (2 * (s₂ + s₃) - s₁)) *
          (2 * (s₂ + s₃) - s₁) :=
        (ExplicitField.div_mul_cancel _ denominatorNonzero).symm
  · apply ExplicitField.eq_of_mul_eq_mul_right denominatorNonzero
    calc
      v * (2 * (s₂ + s₃) - s₁) = s₁ * s₃ := vCleared
      _ = ((s₁ * s₃) / (2 * (s₂ + s₃) - s₁)) *
          (2 * (s₂ + s₃) - s₁) :=
        (ExplicitField.div_mul_cancel _ denominatorNonzero).symm

end Purelib.Geometry.Triangles.Median.Spread

end
