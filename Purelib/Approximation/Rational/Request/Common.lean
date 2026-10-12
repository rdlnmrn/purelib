module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction.Order

/-!
# Common positive rational requests

Dividing the product of two positive requests by their sum gives a positive
request strictly below each input. The original common target and common
coherence request retain their named computations and endpoint certificates.
-/

namespace Purelib.Approximation.Rational.Request.Common

/-- A small common target below each of two positive rational targets.

The product of the two targets is divided by their sum. For positive inputs
this exact rational lies strictly below each input; the same total division
operation remains defined for every rational pair. -/
@[expose] public def commonTarget (left right : Fraction.Rational) : Fraction.Rational :=
  (left * right) / (left + right)

/-- The common target of two positive rational targets is positive.

Both targets are strictly positive, so their product and their sum are
positive. Division by that exact sum preserves the strict sign. -/
public theorem commonTarget_pos {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    0 < commonTarget left right :=
  Fraction.Order.Field.div_pos_direct
    (Arithmetic.mul_pos_direct leftPositive rightPositive)
    (Arithmetic.add_pos_of_pos_of_nonneg_direct leftPositive
      (Arithmetic.le_of_lt_direct rightPositive))

/-- The common target is strictly below its positive left input when both inputs
are positive.

Positivity of both targets makes the denominator positive and its right
summand strictly smaller than the full sum. Multiplication by the positive
left target yields the stated strict quotient bound. -/
public theorem commonTarget_lt_left {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    commonTarget left right < left := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Arithmetic.add_pos_of_pos_of_nonneg_direct leftPositive
      (Arithmetic.le_of_lt_direct rightPositive))).2
  have rightLt : right < left + right := by
    calc
      right = 0 + right := (_root_.zero_add right).symm
      _ < left + right :=
        Arithmetic.add_lt_add_right_direct leftPositive right
  exact Arithmetic.mul_lt_mul_of_pos_left_direct
    leftPositive rightLt

/-- The common target is strictly below its positive right input when both inputs
are positive.

Positivity of both targets makes the denominator positive and its left summand
strictly smaller than the full sum. Multiplication by the positive right
target yields the stated strict quotient bound. -/
public theorem commonTarget_lt_right {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    commonTarget left right < right := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Arithmetic.add_pos_of_pos_of_nonneg_direct leftPositive
      (Arithmetic.le_of_lt_direct rightPositive))).2
  have leftLt : left < left + right := by
    calc
      left = 0 + left := (_root_.zero_add left).symm
      _ < right + left :=
        Arithmetic.add_lt_add_right_direct
          rightPositive left
      _ = left + right := _root_.add_comm _ _
  have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct
    rightPositive leftLt
  calc
    left * right = right * left :=
      Fraction.Field.mul_comm _ _
    _ < right * (left + right) := scaled

end Purelib.Approximation.Rational.Request.Common

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent

/-- A positive rational request strictly below each of two positive requests. This
is finite arithmetic data, not an infimum operation.

The two positive requests use the exact product divided by their sum. This
finite rational expression is strictly below both inputs and retains the
original request computation. -/
@[expose] public def commonRequest (left right : Fraction.Rational) : Fraction.Rational :=
  (left * right) / (left + right)

/-- The common request of two positive rational requests is positive.

Both original requests are strictly positive. Their positive product and
positive sum give a strictly positive rational quotient. -/
public theorem commonRequest_pos {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    0 < commonRequest left right :=
  Fraction.Order.Field.div_pos_direct
    (Arithmetic.mul_pos_direct leftPositive rightPositive)
    (Arithmetic.add_pos_of_pos_of_nonneg_direct leftPositive
      (Arithmetic.le_of_lt_direct rightPositive))

/-- The common request is strictly below its left input when both inputs are
positive.

Both requests are positive, so the denominator is positive and exceeds its
right summand. Scaling by the positive left request gives the strict left
bound. -/
public theorem commonRequest_lt_left {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    commonRequest left right < left := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Arithmetic.add_pos_of_pos_of_nonneg_direct leftPositive
      (Arithmetic.le_of_lt_direct rightPositive))).2
  have rightLt : right < left + right := by
    calc
      right = 0 + right := (_root_.zero_add right).symm
      _ < left + right :=
        Arithmetic.add_lt_add_right_direct leftPositive right
  exact Arithmetic.mul_lt_mul_of_pos_left_direct
    leftPositive rightLt

/-- The common request is strictly below its right input when both inputs are
positive.

Both requests are positive, so the denominator is positive and exceeds its
left summand. Scaling by the positive right request gives the strict right
bound. -/
public theorem commonRequest_lt_right {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    commonRequest left right < right := by
  apply (Fraction.Order.Field.div_lt_iff_pos
    (Arithmetic.add_pos_of_pos_of_nonneg_direct leftPositive
      (Arithmetic.le_of_lt_direct rightPositive))).2
  have leftLt : left < left + right := by
    calc
      left = 0 + left := (_root_.zero_add left).symm
      _ < right + left :=
        Arithmetic.add_lt_add_right_direct rightPositive left
      _ = left + right := _root_.add_comm _ _
  have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct
    rightPositive leftLt
  calc
    left * right = right * left := Fraction.Field.mul_comm _ _
    _ < right * (left + right) := scaled

end Purelib.Approximation.Gaussian.Process.Coherence.Basic.Coherent
