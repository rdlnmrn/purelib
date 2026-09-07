import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Proportions.Stewart
import DivineProportions.Triangles.Median

/-!
# Divine Proportions, Chapter 11: median quadrance

The denominator-cleared identity already proved for right midpoints gives the
median formula directly.  The source's extra `Q₁ ≠ 0` hypothesis is not needed;
only characteristic two is excluded so that the displayed midpoint and `/4`
normalization have their intended meaning.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

/-- Theorem 76 (Median quadrance), with `A₁` as the vertex and `M₁` the
midpoint of `A₂A₃`. -/
theorem median_quadrance
    (first second third : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrance first (midpoint second third) =
      (2 * (quadrance first third + quadrance first second) -
        quadrance second third) / 4 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  apply eq_of_mul_eq_mul_right fourNonzero
  calc
    quadrance first (midpoint second third) * 4 =
        quadrance (midpoint second third) first * 4 := by
      rw [quadrance_symm first (midpoint second third)]
    _ = 2 * quadrance second first + 2 * quadrance third first -
        quadrance second third :=
      median_quadrance_cleared second third first twoNonzero
    _ = 2 * (quadrance first third + quadrance first second) -
        quadrance second third := by
      rw [quadrance_symm second first, quadrance_symm third first]
      ring1
    _ = ((2 * (quadrance first third + quadrance first second) -
        quadrance second third) / 4) * 4 :=
      (RFAP.ExplicitField.div_mul_cancel _ fourNonzero).symm

/-- Denominator-free form of Exercise 11.7: the sum of the three median
quadrances is three quarters of the sum of the side quadrances. -/
theorem exercise_11_7_cleared
    (first second third : Point K) (twoNonzero : (2 : K) ≠ 0) :
    (quadrance first (midpoint second third) +
        quadrance second (midpoint first third) +
        quadrance third (midpoint first second)) * 4 =
      3 * (quadrance second third + quadrance first third +
        quadrance first second) := by
  rw [quadrance_symm first (midpoint second third),
    quadrance_symm second (midpoint first third),
    quadrance_symm third (midpoint first second)]
  calc
    (quadrance (midpoint second third) first +
          quadrance (midpoint first third) second +
          quadrance (midpoint first second) third) * 4 =
        quadrance (midpoint second third) first * 4 +
          quadrance (midpoint first third) second * 4 +
          quadrance (midpoint first second) third * 4 := by ring1
    _ = (2 * quadrance second first + 2 * quadrance third first -
          quadrance second third) +
        (2 * quadrance first second + 2 * quadrance third second -
          quadrance first third) +
        (2 * quadrance first third + 2 * quadrance second third -
          quadrance first second) := by
      rw [median_quadrance_cleared second third first twoNonzero,
        median_quadrance_cleared first third second twoNonzero,
        median_quadrance_cleared first second third twoNonzero]
    _ = 3 * (quadrance second third + quadrance first third +
        quadrance first second) := by
      rw [quadrance_symm second first, quadrance_symm third first,
        quadrance_symm third second]
      ring1

/-- Exercise 11.7 in its printed quotient form. -/
theorem exercise_11_7
    (first second third : Point K) (twoNonzero : (2 : K) ≠ 0) :
    quadrance first (midpoint second third) +
        quadrance second (midpoint first third) +
        quadrance third (midpoint first second) =
      (3 * (quadrance second third + quadrance first third +
        quadrance first second)) / 4 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  apply eq_of_mul_eq_mul_right fourNonzero
  calc
    (quadrance first (midpoint second third) +
          quadrance second (midpoint first third) +
          quadrance third (midpoint first second)) * 4 =
        3 * (quadrance second third + quadrance first third +
          quadrance first second) :=
      exercise_11_7_cleared first second third twoNonzero
    _ = ((3 * (quadrance second third + quadrance first third +
        quadrance first second)) / 4) * 4 :=
      (RFAP.ExplicitField.div_mul_cancel _ fourNonzero).symm

/-- Denominator-free core of Theorem 77.  The five displayed equalities are
the Median quadrance theorem, the two original-triangle Spread laws, and the
three needed cleared Spread laws in the two half-triangles. -/
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
    have squareNonzero := RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have PQ₁Nonzero : P * Q₁ ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero PNonzero Q₁Nonzero
  have fourPNonzero : (4 : K) * P ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero PNonzero
  have rFormula : r * denominator = 4 * s₂ * s₃ := by
    apply eq_of_mul_eq_mul_right PQ₁Nonzero
    calc
      (r * denominator) * (P * Q₁) =
          (denominator * Q₁) * (r * P) := by ring1
      _ = (s₁ * (P * 4)) * (s₂ * Q₃) := by
        rw [weightedMedian, halfLawR]
      _ = 4 * s₂ * P * (s₁ * Q₃) := by ring1
      _ = 4 * s₂ * P * (s₃ * Q₁) := by rw [triangleLaw₃]
      _ = (4 * s₂ * s₃) * (P * Q₁) := by ring1
  have uFormula : u * denominator = s₁ * s₂ := by
    apply eq_of_mul_eq_mul_right fourPNonzero
    calc
      (u * denominator) * (4 * P) =
          denominator * (4 * u * P) := by ring1
      _ = denominator * (s₂ * Q₁) := by rw [halfLawU]
      _ = s₂ * (denominator * Q₁) := by ring1
      _ = s₂ * (s₁ * (P * 4)) := by rw [weightedMedian]
      _ = (s₁ * s₂) * (4 * P) := by ring1
  have vFormula : v * denominator = s₁ * s₃ := by
    apply eq_of_mul_eq_mul_right fourPNonzero
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

/-- Theorem 77 (Median spreads), in the three printed quotient forms. -/
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
  · apply eq_of_mul_eq_mul_right denominatorNonzero
    calc
      r * (2 * (s₂ + s₃) - s₁) = 4 * s₂ * s₃ := rCleared
      _ = ((4 * s₂ * s₃) / (2 * (s₂ + s₃) - s₁)) *
          (2 * (s₂ + s₃) - s₁) :=
        (RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero).symm
  constructor
  · apply eq_of_mul_eq_mul_right denominatorNonzero
    calc
      u * (2 * (s₂ + s₃) - s₁) = s₁ * s₂ := uCleared
      _ = ((s₁ * s₂) / (2 * (s₂ + s₃) - s₁)) *
          (2 * (s₂ + s₃) - s₁) :=
        (RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero).symm
  · apply eq_of_mul_eq_mul_right denominatorNonzero
    calc
      v * (2 * (s₂ + s₃) - s₁) = s₁ * s₃ := vCleared
      _ = ((s₁ * s₃) / (2 * (s₂ + s₃) - s₁)) *
          (2 * (s₂ + s₃) - s₁) :=
        (RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero).symm

end DivineProportions
