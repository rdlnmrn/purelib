module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Distribution.Kernel.Basic
import Purelib.Data.List.Event
public import Purelib.Measure.Distribution.Lp.Natural
import Purelib.Measure.Distribution.Lp.L2
import Purelib.Measure.Distribution.Lp.L1
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Powered Lp laws on explicit finite products

Finite Fubini evaluation gives exact factorization of natural-powered
magnitudes for separable products.  Observables pulled back from either
coordinate retain their powered Lp quantities and distances exactly.  All
statements are finite rational identities; no roots or product sigma algebra
are constructed.
-/

namespace Purelib.Measure

namespace Content
end Content

namespace Distribution

section
open Purelib
open Purelib.Data.Rat
/-- A separated product observable's natural-powered magnitude expectation factors into the two original marginal
powered expectations. -/
theorem product_poweredLp_mul {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (exponent : Nat) (leftValue : α → Fraction.Rational)
    (rightValue : β → Fraction.Rational) :
    (left.product right).poweredLp exponent
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredLp exponent leftValue *
        right.poweredLp exponent rightValue := by
  change (left.product right).expectation (fun pair =>
      Distance.rationalSeparation (leftValue pair.1 * rightValue pair.2) 0 ^
        exponent) =
    left.expectation (fun item =>
        Distance.rationalSeparation (leftValue item) 0 ^ exponent) *
      right.expectation (fun item =>
        Distance.rationalSeparation (rightValue item) 0 ^ exponent)
  calc
    (left.product right).expectation (fun pair =>
        Distance.rationalSeparation (leftValue pair.1 * rightValue pair.2) 0 ^
          exponent) =
        (left.product right).expectation (fun pair =>
          Distance.rationalSeparation (leftValue pair.1) 0 ^ exponent *
            Distance.rationalSeparation (rightValue pair.2) 0 ^ exponent) :=
      (left.product right).expectation_congr _ _ (fun pair => by
        rw [Distance.rationalSeparation_mul_zero, Fraction.Field.mul_pow_direct])
    _ = left.expectation (fun item =>
          Distance.rationalSeparation (leftValue item) 0 ^ exponent) *
        right.expectation (fun item =>
          Distance.rationalSeparation (rightValue item) 0 ^ exponent) :=
      left.product_expectation_mul right
        (fun item => Distance.rationalSeparation (leftValue item) 0 ^ exponent)
        (fun item => Distance.rationalSeparation (rightValue item) 0 ^ exponent)

/-- The magnitude expectation of a separated product factors into its two marginal magnitude expectations. -/
theorem product_poweredL1_mul {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    (left.product right).poweredL1
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredL1 leftValue * right.poweredL1 rightValue := by
  have factorization := left.product_poweredLp_mul right 1
    leftValue rightValue
  rw [(left.product right).poweredLp_one, left.poweredLp_one,
    right.poweredLp_one] at factorization
  exact factorization

/-- The squared expectation of a separated product factors into its two marginal squared expectations. -/
theorem product_poweredL2_mul {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    (left.product right).poweredL2
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredL2 leftValue * right.poweredL2 rightValue := by
  have factorization := left.product_poweredLp_mul right 2
    leftValue rightValue
  rw [(left.product right).poweredLp_two, left.poweredLp_two,
    right.poweredLp_two] at factorization
  exact factorization

/-- A left-coordinate observable retains its original natural-powered magnitude expectation under the product law. -/
theorem product_poweredLp_left {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (exponent : Nat) (value : α → Fraction.Rational) :
    (left.product right).poweredLp exponent (fun pair => value pair.1) =
      left.poweredLp exponent value := by
  change (left.product right).expectation (fun pair =>
      Distance.rationalSeparation (value pair.1) 0 ^ exponent) =
    left.expectation (fun item => Distance.rationalSeparation (value item) 0 ^ exponent)
  rw [left.product_expectation_iterated]
  exact left.expectation_congr _ _ (fun item =>
    right.expectation_constant
      (Distance.rationalSeparation (value item) 0 ^ exponent))

/-- A right-coordinate observable retains its original natural-powered magnitude expectation under the product law. -/
theorem product_poweredLp_right {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (exponent : Nat) (value : β → Fraction.Rational) :
    (left.product right).poweredLp exponent (fun pair => value pair.2) =
      right.poweredLp exponent value := by
  change (left.product right).expectation (fun pair =>
      Distance.rationalSeparation (value pair.2) 0 ^ exponent) =
    right.expectation (fun item => Distance.rationalSeparation (value item) 0 ^ exponent)
  rw [left.product_expectation_iterated]
  exact left.expectation_constant
    (right.expectation (fun item =>
      Distance.rationalSeparation (value item) 0 ^ exponent))

/-- A left-coordinate observable retains its original magnitude expectation under the product law. -/
theorem product_poweredL1_left {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (value : α → Fraction.Rational) :
    (left.product right).poweredL1 (fun pair => value pair.1) =
      left.poweredL1 value := by
  have preserved := left.product_poweredLp_left right 1 value
  rw [(left.product right).poweredLp_one, left.poweredLp_one] at preserved
  exact preserved

/-- A right-coordinate observable retains its original magnitude expectation under the product law. -/
theorem product_poweredL1_right {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (value : β → Fraction.Rational) :
    (left.product right).poweredL1 (fun pair => value pair.2) =
      right.poweredL1 value := by
  have preserved := left.product_poweredLp_right right 1 value
  rw [(left.product right).poweredLp_one, right.poweredLp_one] at preserved
  exact preserved

/-- A left-coordinate observable retains its original squared expectation under the product law. -/
theorem product_poweredL2_left {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (value : α → Fraction.Rational) :
    (left.product right).poweredL2 (fun pair => value pair.1) =
      left.poweredL2 value := by
  have preserved := left.product_poweredLp_left right 2 value
  rw [(left.product right).poweredLp_two, left.poweredLp_two] at preserved
  exact preserved

/-- A right-coordinate observable retains its original squared expectation under the product law. -/
theorem product_poweredL2_right {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (value : β → Fraction.Rational) :
    (left.product right).poweredL2 (fun pair => value pair.2) =
      right.poweredL2 value := by
  have preserved := left.product_poweredLp_right right 2 value
  rw [(left.product right).poweredLp_two, right.poweredLp_two] at preserved
  exact preserved

/-- Left-coordinate observables retain their original natural-powered distance expectation under the product law. -/
theorem product_poweredLpDistance_left {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (exponent : Nat) (first second : α → Fraction.Rational) :
    (left.product right).poweredLpDistance exponent
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.poweredLpDistance exponent first second := by
  change (left.product right).expectation (fun pair =>
      Distance.rationalSeparation (first pair.1) (second pair.1) ^ exponent) =
    left.expectation (fun item =>
      Distance.rationalSeparation (first item) (second item) ^ exponent)
  rw [left.product_expectation_iterated]
  exact left.expectation_congr _ _ (fun item =>
    right.expectation_constant
      (Distance.rationalSeparation (first item) (second item) ^ exponent))

/-- Right-coordinate observables retain their original natural-powered distance expectation under the product law. -/
theorem product_poweredLpDistance_right {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (exponent : Nat) (first second : β → Fraction.Rational) :
    (left.product right).poweredLpDistance exponent
        (fun pair => first pair.2) (fun pair => second pair.2) =
      right.poweredLpDistance exponent first second := by
  change (left.product right).expectation (fun pair =>
      Distance.rationalSeparation (first pair.2) (second pair.2) ^ exponent) =
    right.expectation (fun item =>
      Distance.rationalSeparation (first item) (second item) ^ exponent)
  rw [left.product_expectation_iterated]
  exact left.expectation_constant
    (right.expectation (fun item =>
      Distance.rationalSeparation (first item) (second item) ^ exponent))

/-- Left-coordinate observables retain their original integrated distance under the product law. -/
theorem product_l1Distance_left {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (first second : α → Fraction.Rational) :
    (left.product right).l1Distance
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.l1Distance first second := by
  have preserved := left.product_poweredLpDistance_left right 1 first second
  rw [(left.product right).poweredLpDistance_one,
    left.poweredLpDistance_one] at preserved
  exact preserved

/-- Right-coordinate observables retain their original integrated distance under the product law. -/
theorem product_l1Distance_right {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (first second : β → Fraction.Rational) :
    (left.product right).l1Distance
        (fun pair => first pair.2) (fun pair => second pair.2) =
      right.l1Distance first second := by
  have preserved := left.product_poweredLpDistance_right right 1 first second
  rw [(left.product right).poweredLpDistance_one,
    right.poweredLpDistance_one] at preserved
  exact preserved

/-- Left-coordinate observables retain their original squared-distance expectation under the product law. -/
theorem product_poweredL2Distance_left {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (first second : α → Fraction.Rational) :
    (left.product right).poweredL2Distance
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.poweredL2Distance first second := by
  have preserved := left.product_poweredLpDistance_left right 2 first second
  rw [(left.product right).poweredLpDistance_two,
    left.poweredLpDistance_two] at preserved
  exact preserved

/-- Right-coordinate observables retain their original squared-distance expectation under the product law. -/
theorem product_poweredL2Distance_right {α β : Type}
    (left : Measure.Distribution α) (right : Measure.Distribution β)
    (first second : β → Fraction.Rational) :
    (left.product right).poweredL2Distance
        (fun pair => first pair.2) (fun pair => second pair.2) =
      right.poweredL2Distance first second := by
  have preserved := left.product_poweredLpDistance_right right 2 first second
  rw [(left.product right).poweredLpDistance_two,
    right.poweredLpDistance_two] at preserved
  exact preserved

end

end Distribution

end Purelib.Measure

end
