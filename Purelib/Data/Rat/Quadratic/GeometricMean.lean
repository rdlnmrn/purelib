module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 24: surveying

Every construction is expressed by its finite quadrance/spread equations.
Decimal readings are retained as exact integer coefficient pairs, with
integer interval certificates for the source's numerical approximations.
-/

namespace Purelib.Data.Rat.Quadratic.GeometricMean

section SurveyingApplications

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

open Purelib.Algebra
open Purelib.Data.Rat
/-- Twice any rational mean is at most a positive rational plus the mean square divided by that rational. -/
theorem regiomontanus_denominator_bound
    (P mean : Fraction.Rational) (PPositive : 0 < P) :
    2 * mean ≤ P + mean ^ 2 / P := by
  have PNonzero : P ≠ 0 := by
    intro PZero
    rw [PZero] at PPositive
    exact (lt_irrefl 0 PPositive).elim
  have squareNonnegative : (0 : Fraction.Rational) ≤ (P - mean) ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct (P - mean)
  have quotientNonnegative : (0 : Fraction.Rational) ≤ (P - mean) ^ 2 / P :=
    Fraction.Order.Field.div_nonneg_direct squareNonnegative
      (Fraction.Order.Arithmetic.le_of_lt_direct PPositive)
  have differenceIdentity :
      P + mean ^ 2 / P - 2 * mean = (P - mean) ^ 2 / P := by
    apply Field.ExplicitField.eq_of_mul_eq_mul_right PNonzero
    calc
      (P + mean ^ 2 / P - 2 * mean) * P =
          P ^ 2 + (mean ^ 2 / P) * P - 2 * mean * P := by ring1
      _ = P ^ 2 + mean ^ 2 - 2 * mean * P := by
        rw [Field.ExplicitField.div_mul_cancel (mean ^ 2) PNonzero]
      _ = (P - mean) ^ 2 := by ring1
      _ = ((P - mean) ^ 2 / P) * P :=
        (Field.ExplicitField.div_mul_cancel ((P - mean) ^ 2) PNonzero).symm
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  rw [differenceIdentity]
  exact quotientNonnegative

/-- A retained product equal to the mean square yields the quadratic denominator bound and the exact doubled-mean
identity.

The denominator-bound conclusion uses the supplied positive denominator. The doubled-mean identity also handles zero
mean through the canonical total division operation, so no extra nonzero-mean premise is required. -/
theorem problem_20 (P mean Q₁ Q₂ : Fraction.Rational)
    (PPositive : 0 < P) (meanSquare : mean ^ 2 = Q₁ * Q₂) :
    2 * mean ≤ P + Q₁ * Q₂ / P ∧
      mean + Q₁ * Q₂ / mean = 2 * mean := by
  constructor
  · rw [← meanSquare]
    exact regiomontanus_denominator_bound P mean PPositive
  · rw [← meanSquare]
    by_cases meanZero : mean = 0
    · rw [meanZero, pow_two, zero_mul,
          Field.ExplicitField.zero_div]
      ring1
    ·
      have quotientValue : mean ^ 2 / mean = mean := by
        apply Field.ExplicitField.eq_of_mul_eq_mul_right meanZero
        calc
          (mean ^ 2 / mean) * mean = mean ^ 2 :=
            Field.ExplicitField.div_mul_cancel (mean ^ 2) meanZero
          _ = mean * mean := by ring1
      rw [quotientValue]
      ring1
end SurveyingApplications
end Purelib.Data.Rat.Quadratic.GeometricMean

end
