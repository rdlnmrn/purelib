module

public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Rational products and finite sign comparisons

Strict product bounds determine the relative signs of canonical rationals.
Square comparisons are resolved by direct sign splits and scalar identities.
-/

namespace Purelib.Data.Rat.Sign.Products

open Purelib.Data.Rat

/-- Opposite and equal signs relative to a common reference force a negative product between the two values.

The reference is nonzero because its product with the second factor is positive. Multiplication by its positive square
transports the negative product bound to the two factors. -/
public theorem product_neg_of_opposite_and_same
    {left right reference : Fraction.Rational}
    (leftOpposite : left * reference < 0)
    (rightSame : 0 < right * reference) : left * right < 0 := by
  have referenceNonzero : reference ≠ 0 := by
    intro referenceZero
    rw [referenceZero, Fraction.Field.mul_zero_direct] at rightSame
    exact (lt_irrefl 0 rightSame).elim
  have referenceSquarePositive : 0 < reference * reference :=
    by simpa only [pow_two] using
      Fraction.Order.Arithmetic.exact_rational_sq_pos referenceNonzero
  have combinedNegative :
      (left * right) * (reference * reference) < 0 := by
    calc
      (left * right) * (reference * reference) =
          (left * reference) * (right * reference) := by ring1
      _ < 0 := Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct
        leftOpposite rightSame
  rcases lt_trichotomy (left * right) 0 with
      productNegative | productZero | productPositive
  · exact productNegative
  · rw [productZero, Fraction.Field.zero_mul_direct]
      at combinedNegative
    exact (lt_irrefl 0 combinedNegative).elim
  · have combinedPositive := Fraction.Order.Arithmetic.mul_pos_direct
      productPositive referenceSquarePositive
    exact (lt_asymm combinedPositive combinedNegative).elim

/-- Two positive products against the same reference force a positive product between the two values.

The positive reference square transports the two aligned product bounds to positivity of the product of the original
factors. -/
public theorem product_pos_of_two_same
    {left right reference : Fraction.Rational}
    (leftSame : 0 < left * reference)
    (rightSame : 0 < right * reference) : 0 < left * right := by
  have referenceNonzero : reference ≠ 0 := by
    intro referenceZero
    rw [referenceZero, Fraction.Field.mul_zero_direct] at rightSame
    exact (lt_irrefl 0 rightSame).elim
  have referenceSquarePositive : 0 < reference * reference :=
    by simpa only [pow_two] using
      Fraction.Order.Arithmetic.exact_rational_sq_pos referenceNonzero
  have combinedPositive :
      0 < (left * right) * (reference * reference) := by
    calc
      0 < (left * reference) * (right * reference) :=
        Fraction.Order.Arithmetic.mul_pos_direct leftSame rightSame
      _ = (left * right) * (reference * reference) := by ring1
  exact Fraction.Order.Arithmetic.pos_of_mul_pos_right_direct
    (left := reference * reference)
    (by simpa only [Fraction.Field.mul_comm] using combinedPositive)
    referenceSquarePositive.le

/-- A positive rational product forces equal Boolean decisions for nonnegativity of its factors.

Positive multiplication excludes opposite weak sign decisions. The remaining decisions are equal by direct certificates
for their Boolean readbacks. -/
public theorem nonnegative_sign_eq_of_mul_pos {x y : Fraction.Rational} (positive : 0 < x * y) :
    decide (0 ≤ x) = decide (0 ≤ y) := by
  by_cases hx : 0 ≤ x
  · by_cases hy : 0 ≤ y
    · exact (decide_eq_true hx).trans (decide_eq_true hy).symm
    · exact (not_lt_of_ge ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (le_of_not_ge hy) hx).trans_eq
        (mul_zero x)) positive).elim
  · by_cases hy : 0 ≤ y
    · exact (not_lt_of_ge ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_of_not_ge hx) hy).trans_eq
        (zero_mul y)) positive).elim
    · exact (decide_eq_false hx).trans (decide_eq_false hy).symm

/-- A strict square bound against a negative right value makes the difference times that value negative.

The negative right factor and strict square comparison force the difference to be positive; their product is therefore
negative. -/
public theorem sub_mul_neg_of_sq_lt_sq_of_right_neg {a b : Fraction.Rational}
    (bNegative : b < 0) (squares : a ^ 2 < b ^ 2) :
    (a - b) * b < 0 := by
  have bLessA : b < a := by
    rcases lt_trichotomy a 0 with aNegative | rfl | aPositive
    · rcases lt_trichotomy b a with less | equal | reverse
      · exact less
      · subst a
        exact (lt_irrefl _ squares).elim
      · have differenceNegative : a - b < 0 := by
          have reverseDifferencePositive :=
            Fraction.Order.Arithmetic.sub_pos_direct reverse
          calc
            a - b = -(b - a) := by ring1
            _ < 0 := by
              have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct reverseDifferencePositive
              have zeroIdentity : -(0 : Fraction.Rational) = 0 := by ring1
              rewrite [zeroIdentity] at reversed
              exact reversed
        have sumNegative : a + b < 0 := by
          calc
            a + b < 0 + b :=
              Fraction.Order.Arithmetic.add_lt_add_right_direct aNegative b
            _ = b := by ring1
            _ < 0 := bNegative
        have productPositive : 0 < (a - b) * (a + b) :=
          Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
            differenceNegative sumNegative
        have reverseSquares : b ^ 2 < a ^ 2 := by
          have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
            productPositive (b ^ 2)
          calc
            b ^ 2 = 0 + b ^ 2 := by ring1
            _ < (a - b) * (a + b) + b ^ 2 := shifted
            _ = a ^ 2 := by ring1
        exact (lt_asymm squares reverseSquares).elim
    · exact bNegative
    · exact bNegative.trans aPositive
  have differencePositive := Fraction.Order.Arithmetic.sub_pos_direct bLessA
  exact Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
    differencePositive bNegative

/-- A strict square bound against a positive right value makes the difference times that value negative.

The positive right factor and strict square comparison force the difference to be negative; their product is therefore
negative. -/
public theorem sub_mul_neg_of_sq_lt_sq_of_right_pos {a b : Fraction.Rational}
    (bPositive : 0 < b) (squares : a ^ 2 < b ^ 2) :
    (a - b) * b < 0 := by
  have aLessB : a < b := by
    rcases lt_trichotomy a 0 with aNegative | rfl | aPositive
    · exact aNegative.trans bPositive
    · exact bPositive
    · exact Bounds.Square.lt_of_sq_lt_sq_of_nonneg bPositive.le squares
  have reverseDifferencePositive :=
    Fraction.Order.Arithmetic.sub_pos_direct aLessB
  have differenceNegative : a - b < 0 := by
    calc
      a - b = -(b - a) := by ring1
      _ < 0 := by
              have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct reverseDifferencePositive
              have zeroIdentity : -(0 : Fraction.Rational) = 0 := by ring1
              rewrite [zeroIdentity] at reversed
              exact reversed
  exact Fraction.Order.Arithmetic.mul_neg_of_neg_of_pos_direct
    differenceNegative bPositive

/-- A strict rational square comparison makes the difference times the right value negative.

Split the sign of the right factor. Its zero case contradicts square nonnegativity, and each strict case retains a
negative product. -/
public theorem sub_mul_neg_of_sq_lt_sq {a b : Fraction.Rational}
    (squares : a ^ 2 < b ^ 2) : (a - b) * b < 0 := by
  rcases lt_trichotomy b 0 with bNegative | rfl | bPositive
  · exact Sign.Products.sub_mul_neg_of_sq_lt_sq_of_right_neg bNegative squares
  · exact ((not_lt_of_ge
      (Fraction.Order.Arithmetic.sq_nonneg_direct a)) squares).elim
  · exact Sign.Products.sub_mul_neg_of_sq_lt_sq_of_right_pos bPositive squares

/-- A squared displacement smaller than the sample square forces the value and sample to have positive product.

The strict displacement bound excludes a zero sample and opposite signs. Direct scalar factorization supplies the
contradiction in each remaining opposite-sign case. -/
public theorem mul_pos_of_sub_sq_lt_sq {x sample : Fraction.Rational}
    (close : (x - sample) ^ 2 < sample ^ 2) : 0 < x * sample := by
  rcases lt_trichotomy x 0 with xNegative | rfl | xPositive <;>
    rcases lt_trichotomy sample 0 with sampleNegative | rfl | samplePositive
  · exact Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
      xNegative sampleNegative
  · have subtraction : x - (0 : Fraction.Rational) = x := by ring1
    rewrite [subtraction] at close
    exact ((not_lt_of_ge
      (Fraction.Order.Arithmetic.sq_nonneg_direct x)) close).elim
  · have twiceSamplePositive : 0 < 2 * sample := by
      calc
        0 = 0 + 0 := by ring1
        _ < sample + 0 :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct samplePositive 0
        _ < sample + sample :=
          Fraction.Order.Arithmetic.add_lt_add_left_direct samplePositive sample
        _ = 2 * sample := by ring1
    have reverseDifferencePositive : 0 < 2 * sample - x :=
      Fraction.Order.Arithmetic.sub_pos_direct
        (xNegative.trans twiceSamplePositive)
    have differenceNegative : x - 2 * sample < 0 := by
      calc
        x - 2 * sample = -(2 * sample - x) := by ring1
        _ < 0 := by
              have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct reverseDifferencePositive
              have zeroIdentity : -(0 : Fraction.Rational) = 0 := by ring1
              rewrite [zeroIdentity] at reversed
              exact reversed
    have factorPositive :=
      Fraction.Order.Arithmetic.mul_pos_of_neg_of_neg_direct
        xNegative differenceNegative
    have reverse : sample ^ 2 < (x - sample) ^ 2 := by
      have positiveDifference :
          0 < (x - sample) ^ 2 - sample ^ 2 := by
        calc
          0 < x * (x - 2 * sample) := factorPositive
          _ = (x - sample) ^ 2 - sample ^ 2 := by ring1
      have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
        positiveDifference (sample ^ 2)
      calc
        sample ^ 2 = 0 + sample ^ 2 := by ring1
        _ < ((x - sample) ^ 2 - sample ^ 2) + sample ^ 2 := shifted
        _ = (x - sample) ^ 2 := by ring1
    exact (lt_asymm close reverse).elim
  · have squareIdentity : ((0 : Fraction.Rational) - sample) ^ 2 = sample ^ 2 := by ring1
    rewrite [squareIdentity] at close
    exact (lt_irrefl _ close).elim
  · have subtraction : (0 : Fraction.Rational) - 0 = 0 := by ring1
    rewrite [subtraction] at close
    exact (lt_irrefl _ close).elim
  · have squareIdentity : ((0 : Fraction.Rational) - sample) ^ 2 = sample ^ 2 := by ring1
    rewrite [squareIdentity] at close
    exact (lt_irrefl _ close).elim
  · have twiceSampleNegative : 2 * sample < 0 := by
      calc
        2 * sample = sample + sample := by ring1
        _ < 0 + sample :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct
            sampleNegative sample
        _ < 0 + 0 :=
          Fraction.Order.Arithmetic.add_lt_add_left_direct sampleNegative 0
        _ = 0 := by ring1
    have differencePositive : 0 < x - 2 * sample :=
      Fraction.Order.Arithmetic.sub_pos_direct
        (twiceSampleNegative.trans xPositive)
    have factorPositive := Fraction.Order.Arithmetic.mul_pos_direct
      xPositive differencePositive
    have reverse : sample ^ 2 < (x - sample) ^ 2 := by
      have positiveDifference :
          0 < (x - sample) ^ 2 - sample ^ 2 := by
        calc
          0 < x * (x - 2 * sample) := factorPositive
          _ = (x - sample) ^ 2 - sample ^ 2 := by ring1
      have shifted := Fraction.Order.Arithmetic.add_lt_add_right_direct
        positiveDifference (sample ^ 2)
      calc
        sample ^ 2 = 0 + sample ^ 2 := by ring1
        _ < ((x - sample) ^ 2 - sample ^ 2) + sample ^ 2 := shifted
        _ = (x - sample) ^ 2 := by ring1
    exact (lt_asymm close reverse).elim
  · have subtraction : x - (0 : Fraction.Rational) = x := by ring1
    rewrite [subtraction] at close
    exact ((not_lt_of_ge
      (Fraction.Order.Arithmetic.sq_nonneg_direct x)) close).elim
  · exact Fraction.Order.Arithmetic.mul_pos_direct xPositive samplePositive

end Purelib.Data.Rat.Sign.Products
