module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Explicit finite repeated sampling

An `iidSamples` table contains lists of exactly a supplied natural number of
draws from one displayed rational distribution.  The construction uses only
finite products and pushforwards.  Sample sums and means then have exact
rational expectation and variance formulas, giving a one-shot finite
Chebyshev estimate with the familiar reciprocal sample-count factor.

No infinite product, sequence of random variables, or asymptotic law is
constructed.
-/

namespace Purelib.Measure
namespace Distribution

open Purelib.Data.Rat
/-- A positive natural rational cast is nonzero. -/
theorem positiveSampleCount_ne_zero (count : Nat)
    (positive : 0 < (count : Fraction.Rational)) :
    (count : Fraction.Rational) ≠ 0 :=
  positive.ne'

/-- A positive natural rational cast multiplied by its reciprocal is one. -/
theorem positiveSampleCount_mul_inv (count : Nat)
    (positive : 0 < (count : Fraction.Rational)) :
    (count : Fraction.Rational) * (count : Fraction.Rational)⁻¹ = 1 :=
  Fraction.Field.mul_inv_cancel _
    (positiveSampleCount_ne_zero count positive)

/-- The reciprocal of a positive natural cast cancels that cast when scaling a rational value. -/
theorem positiveSampleCount_inv_mul_value (count : Nat)
    (positive : 0 < (count : Fraction.Rational)) (value : Fraction.Rational) :
    (count : Fraction.Rational)⁻¹ * ((count : Fraction.Rational) * value) = value := by
  calc
    (count : Fraction.Rational)⁻¹ * ((count : Fraction.Rational) * value) =
        ((count : Fraction.Rational)⁻¹ * (count : Fraction.Rational)) * value :=
      Fraction.Field.mul_assoc _ _ _ |>.symm
    _ = ((count : Fraction.Rational) * (count : Fraction.Rational)⁻¹) * value := by
      rw [Fraction.Field.mul_comm
        (count : Fraction.Rational)⁻¹ (count : Fraction.Rational)]
    _ = 1 * value := by rw [positiveSampleCount_mul_inv count positive]
    _ = value := _root_.one_mul value

/-- The squared reciprocal of a positive natural cast times the cast-scaled value equals division by that cast. -/
theorem positiveSampleCount_inv_sq_mul_value (count : Nat)
    (positive : 0 < (count : Fraction.Rational)) (value : Fraction.Rational) :
    (count : Fraction.Rational)⁻¹ ^ 2 * ((count : Fraction.Rational) * value) =
      value / (count : Fraction.Rational) := by
  rw [pow_two, Fraction.Field.mul_pair_swap]
  have inverseTimesCount :
      (count : Fraction.Rational)⁻¹ * (count : Fraction.Rational) = 1 := by
    rw [Fraction.Field.mul_comm
      (count : Fraction.Rational)⁻¹ (count : Fraction.Rational),
      positiveSampleCount_mul_inv count positive]
  rw [inverseTimesCount, _root_.one_mul,
    Fraction.Field.mul_comm (count : Fraction.Rational)⁻¹ value,
    Fraction.Field.div_eq_mul_inv_direct]
end Distribution

end Purelib.Measure

end
