module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Expectation
public import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Moments.Basic
public import Purelib.Measure.Distribution.Moments.Covariance
import Purelib.Measure.Distribution.Product.Expectation
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Moments of explicit finite product distributions

The product distribution is a displayed finite atom list.  Coordinate
expectations and variances therefore factor by exact rational arithmetic,
giving the usual zero covariance and variance-addition laws without any
abstract product measure.
-/

namespace Purelib.Measure

namespace Distribution

open Purelib.Data.Rat
/-- A left-coordinate observable retains its original variance under the product law. -/
theorem product_variance_left {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : α → Fraction.Rational) :
    (left.product right).variance (fun pair => value pair.1) =
      left.variance value := by
  rw [(left.product right).variance_eq_secondMoment_sub_sq,
    left.variance_eq_secondMoment_sub_sq,
    left.product_expectation_left right]
  have secondMoment :
      (left.product right).expectation (fun pair => value pair.1 ^ 2) =
        left.expectation (fun item => value item ^ 2) := by
    simpa only [] using
      left.product_expectation_left right (fun item => value item ^ 2)
  rw [secondMoment]

/-- A right-coordinate observable retains its original variance under the product law. -/
theorem product_variance_right {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : β → Fraction.Rational) :
    (left.product right).variance (fun pair => value pair.2) =
      right.variance value := by
  rw [(left.product right).variance_eq_secondMoment_sub_sq,
    right.variance_eq_secondMoment_sub_sq,
    left.product_expectation_right right]
  have secondMoment :
      (left.product right).expectation (fun pair => value pair.2 ^ 2) =
        right.expectation (fun item => value item ^ 2) := by
    simpa only [] using
      left.product_expectation_right right (fun item => value item ^ 2)
  rw [secondMoment]

/-- Observables on separate product coordinates have covariance zero. -/
theorem product_covariance_coordinates_zero {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    (left.product right).covariance
        (fun pair => leftValue pair.1)
        (fun pair => rightValue pair.2) = 0 := by
  rw [(left.product right).covariance_eq_productMoment_sub_means,
    left.product_expectation_mul right leftValue rightValue,
    left.product_expectation_left right,
    left.product_expectation_right right]
  ring1

/-- The variance of a sum of separate-coordinate observables is the sum of their original marginal variances. -/
theorem product_variance_add_coordinates {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    (left.product right).variance
        (fun pair => leftValue pair.1 + rightValue pair.2) =
      left.variance leftValue + right.variance rightValue := by
  rw [(left.product right).variance_add,
    left.product_variance_left right,
    left.product_variance_right right,
    left.product_covariance_coordinates_zero right]
  ring1

end Distribution

end Purelib.Measure

end
