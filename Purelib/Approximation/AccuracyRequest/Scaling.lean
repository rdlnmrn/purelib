module

public import Purelib.Approximation.AccuracyRequest
-- Public rescaling bodies retain the original rational field's numeral and division instances.
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Nat.Order

/-! # Positive rescaling of retained finite accuracy requests -/

public section

namespace Purelib.Approximation.AccuracyRequest

open Purelib.Data.Rat
open scoped Purelib.Data.Nat

/-- Dividing a positive retained tolerance by a positive factor keeps the tolerance strictly positive. -/
theorem divided_positive (request : AccuracyRequest) (factor : Fraction.Rational) (positive : 0 < factor) :
    0 < request.tolerance / factor :=
  Fraction.Order.Field.div_pos_direct request.positive positive

/-- Construct the same retained accuracy request rescaled by a supplied positive divisor. -/
@[expose] def divide (request : AccuracyRequest) (factor : Fraction.Rational) (positive : 0 < factor) :
    AccuracyRequest :=
  { tolerance := request.tolerance / factor
    positive := divided_positive request factor positive }

/-- The rescaled request has exactly the original tolerance divided by its supplied factor. -/
theorem divide_tolerance (request : AccuracyRequest) (factor : Fraction.Rational) (positive : 0 < factor) :
    (request.divide factor positive).tolerance = request.tolerance / factor := rfl

/-- A divisor at least one makes the rescaled positive request no larger than the original. -/
theorem divide_le (request : AccuracyRequest) (factor : Fraction.Rational) (positive : 0 < factor)
    (lower : 1 ≤ factor) : (request.divide factor positive).tolerance ≤ request.tolerance := by
  change request.tolerance / factor ≤ request.tolerance
  apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct (c := factor) _ positive
  rewrite [Fraction.Field.div_mul_cancel_of_ne _ factor positive.ne.symm]
  exact (Fraction.Field.mul_one_direct request.tolerance).symm.le.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lower request.positive.le)

/-- Construct the retained quarter tolerance used when squared numerical allowances are bisected. -/
@[expose] def quarter (request : AccuracyRequest) : AccuracyRequest :=
  request.divide 4 (by decide +kernel)

/-- The quarter request retains exactly one fourth of the original tolerance. -/
theorem quarter_tolerance (request : AccuracyRequest) : request.quarter.tolerance = request.tolerance / 4 := rfl

/-- The positive quarter request is no larger than the original request. -/
theorem quarter_le (request : AccuracyRequest) : request.quarter.tolerance ≤ request.tolerance :=
  request.divide_le 4 (by decide +kernel) (by decide +kernel)

end Purelib.Approximation.AccuracyRequest
