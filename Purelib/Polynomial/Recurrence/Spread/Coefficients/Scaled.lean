module
public import Purelib.Polynomial.Recurrence.Spread.Basic
public import Purelib.Polynomial.Recurrence.Spread.Coefficients.Array
import Purelib.Polynomial.Recurrence.Spread.Coefficients.Formula

import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Semiring.Normalization
public import Purelib.Algebra.Group.Negation
public import Purelib.Algebra.FiniteSum.Prefix
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: scaled cross coefficients

Exercise 8.20 asks how the coefficients of `Cₙ*(r)=4Cₙ(r/4)` are read
from the spread array.  Odd rows are copied with alternating signs.  Even rows
are subtracted from the constant `4`.  The scaling calculation is first proved
without division for an arbitrary commutative ring.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Coefficients.Scaled

open Purelib.Algebra

/-- The alternating polynomial read directly from row `row` of the spread
array. -/
def scaledSpreadCoefficientExpansion
    {R : Type*} [CommRing R] (row : Nat) (value : R) : R :=
  FiniteSum.Prefix.prefixSum row (fun index =>
    (Recurrence.Spread.Coefficients.Array.spreadArrayCoefficient row (index + 1) : R) *
      (-1) ^ index * value ^ (index + 1))

/-- Division-free scaling law for the spread-array coefficients. -/
theorem scaledSpreadCoefficientExpansion_cleared
    {R : Type*} [CommRing R] (row : Nat) (quarter : R) :
    4 * Recurrence.Spread.Basic.spreadPolynomial row quarter =
      scaledSpreadCoefficientExpansion row (4 * quarter) := by
  rw [Recurrence.Spread.Coefficients.Formula.exercise_8_9_integer_coefficients]
  unfold Recurrence.Spread.Coefficients.Formula.spreadCoefficientExpansion
    scaledSpreadCoefficientExpansion
  rw [← FiniteSum.Prefix.prefixSum_mul_left]
  apply FiniteSum.Prefix.prefixSum_congr
  intro index indexBound
  rw [show -4 * quarter = (-1) * (4 * quarter) by ring1,
    Semiring.Normalization.product_pow, pow_succ]
  generalize (-1 : R) ^ index = signPower
  generalize (4 * quarter) ^ index = scaledPower
  ring1

/-- Scaling the spread argument by one quarter gives the alternating coefficient expansion.

Four must be nonzero in the supplied explicit field; multiplying the resulting spread value by four removes the scale.
-/
theorem scaledSpreadCoefficientExpansion_source
    {K : Type*} [ExplicitField K]
    (row : Nat) (value : K) (fourNonzero : (4 : K) ≠ 0) :
    4 * Recurrence.Spread.Basic.spreadPolynomial row (value / 4) =
      scaledSpreadCoefficientExpansion row value := by
  let quarter := value / 4
  have recoverValue : value = 4 * quarter := by
    unfold quarter
    calc
      value = value / 4 * 4 :=
        (ExplicitField.div_mul_cancel value fourNonzero).symm
      _ = 4 * (value / 4) := by ring1
  change 4 * Recurrence.Spread.Basic.spreadPolynomial row quarter =
    scaledSpreadCoefficientExpansion row value
  rw [recoverValue]
  exact scaledSpreadCoefficientExpansion_cleared row quarter
end Purelib.Polynomial.Recurrence.Spread.Coefficients.Scaled

end
