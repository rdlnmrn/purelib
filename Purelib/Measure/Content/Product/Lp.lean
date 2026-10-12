module
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations
import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
public import Purelib.Measure.Content.Lp.Natural
import Purelib.Measure.Content.Lp.L2
import Purelib.Measure.Content.Lp.L1
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

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

section
open Purelib
open Purelib.Data.Rat
/-- Every natural-powered integral of a separated product observable factors into the original two powered integrals. -/
theorem product_poweredLp_mul {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (exponent : Nat) (leftValue : α → Fraction.Rational)
    (rightValue : β → Fraction.Rational) :
    (left.product right).poweredLp exponent
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredLp exponent leftValue *
        right.poweredLp exponent rightValue := by
  change (left.product right).integral (fun pair =>
      Distance.rationalSeparation (leftValue pair.1 * rightValue pair.2) 0 ^
        exponent) =
    left.integral (fun item =>
        Distance.rationalSeparation (leftValue item) 0 ^ exponent) *
      right.integral (fun item =>
        Distance.rationalSeparation (rightValue item) 0 ^ exponent)
  calc
    (left.product right).integral (fun pair =>
        Distance.rationalSeparation (leftValue pair.1 * rightValue pair.2) 0 ^
          exponent) =
        (left.product right).integral (fun pair =>
          Distance.rationalSeparation (leftValue pair.1) 0 ^ exponent *
            Distance.rationalSeparation (rightValue pair.2) 0 ^ exponent) :=
      (left.product right).integral_congr _ _ (fun pair => by
        rw [Distance.rationalSeparation_mul_zero, Fraction.Field.mul_pow_direct])
    _ = left.integral (fun item =>
          Distance.rationalSeparation (leftValue item) 0 ^ exponent) *
        right.integral (fun item =>
          Distance.rationalSeparation (rightValue item) 0 ^ exponent) :=
      left.product_integral_mul right
        (fun item => Distance.rationalSeparation (leftValue item) 0 ^ exponent)
        (fun item => Distance.rationalSeparation (rightValue item) 0 ^ exponent)

/-- The magnitude integral of a separated product observable factors into the two original magnitude integrals. -/
theorem product_poweredL1_mul {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    (left.product right).poweredL1
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredL1 leftValue * right.poweredL1 rightValue := by
  have factorization := left.product_poweredLp_mul right 1
    leftValue rightValue
  rw [(left.product right).poweredLp_one, left.poweredLp_one,
    right.poweredLp_one] at factorization
  exact factorization

/-- The square integral of a separated product observable factors into the two original square integrals. -/
theorem product_poweredL2_mul {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    (left.product right).poweredL2
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredL2 leftValue * right.poweredL2 rightValue := by
  have factorization := left.product_poweredLp_mul right 2
    leftValue rightValue
  rw [(left.product right).poweredLp_two, left.poweredLp_two,
    right.poweredLp_two] at factorization
  exact factorization

/-- A left-coordinate observable's powered integral over product content is its original powered integral times right
total mass. -/
theorem product_poweredLp_left {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (exponent : Nat) (value : α → Fraction.Rational) :
    (left.product right).poweredLp exponent (fun pair => value pair.1) =
      left.poweredLp exponent value * right.total := by
  change (left.product right).integral (fun pair =>
      Distance.rationalSeparation (value pair.1) 0 ^ exponent) =
    left.integral (fun item => Distance.rationalSeparation (value item) 0 ^ exponent) *
      right.total
  calc
    (left.product right).integral (fun pair =>
          Distance.rationalSeparation (value pair.1) 0 ^ exponent) =
        (left.product right).integral (fun pair =>
          Distance.rationalSeparation (value pair.1) 0 ^ exponent * 1) := by
      exact (left.product right).integral_congr _ _ (fun pair => by ring1)
    _ = left.integral (fun item =>
          Distance.rationalSeparation (value item) 0 ^ exponent) *
        right.integral (fun _ => 1) :=
      left.product_integral_mul right
        (fun item => Distance.rationalSeparation (value item) 0 ^ exponent)
        (fun _ => 1)
    _ = left.integral (fun item =>
          Distance.rationalSeparation (value item) 0 ^ exponent) * right.total := by
      rw [right.integral_constant]
      ring1

/-- A right-coordinate observable's powered integral over product content is left total mass times its original powered
integral. -/
theorem product_poweredLp_right {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (exponent : Nat) (value : β → Fraction.Rational) :
    (left.product right).poweredLp exponent (fun pair => value pair.2) =
      left.total * right.poweredLp exponent value := by
  change (left.product right).integral (fun pair =>
      Distance.rationalSeparation (value pair.2) 0 ^ exponent) =
    left.total *
      right.integral (fun item => Distance.rationalSeparation (value item) 0 ^ exponent)
  calc
    (left.product right).integral (fun pair =>
          Distance.rationalSeparation (value pair.2) 0 ^ exponent) =
        (left.product right).integral (fun pair =>
          1 * Distance.rationalSeparation (value pair.2) 0 ^ exponent) := by
      exact (left.product right).integral_congr _ _ (fun pair => by ring1)
    _ = left.integral (fun _ => 1) *
        right.integral (fun item =>
          Distance.rationalSeparation (value item) 0 ^ exponent) :=
      left.product_integral_mul right (fun _ => 1)
        (fun item => Distance.rationalSeparation (value item) 0 ^ exponent)
    _ = left.total * right.integral (fun item =>
          Distance.rationalSeparation (value item) 0 ^ exponent) := by
      rw [left.integral_constant]
      ring1

/-- Powered distance of left-coordinate observables over product content is their original powered distance times right
total mass. -/
theorem product_poweredLpDistance_left {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (exponent : Nat) (first second : α → Fraction.Rational) :
    (left.product right).poweredLpDistance exponent
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.poweredLpDistance exponent first second * right.total := by
  change (left.product right).integral (fun pair =>
      Distance.rationalSeparation (first pair.1) (second pair.1) ^ exponent) =
    left.integral (fun item =>
      Distance.rationalSeparation (first item) (second item) ^ exponent) * right.total
  calc
    (left.product right).integral (fun pair =>
          Distance.rationalSeparation (first pair.1) (second pair.1) ^ exponent) =
        (left.product right).integral (fun pair =>
          Distance.rationalSeparation (first pair.1) (second pair.1) ^ exponent * 1) := by
      exact (left.product right).integral_congr _ _ (fun pair => by ring1)
    _ = left.integral (fun item =>
          Distance.rationalSeparation (first item) (second item) ^ exponent) *
        right.integral (fun _ => 1) :=
      left.product_integral_mul right
        (fun item =>
          Distance.rationalSeparation (first item) (second item) ^ exponent)
        (fun _ => 1)
    _ = left.integral (fun item =>
          Distance.rationalSeparation (first item) (second item) ^ exponent) *
        right.total := by
      rw [right.integral_constant]
      ring1

/-- Powered distance of right-coordinate observables over product content is left total mass times their original
powered distance. -/
theorem product_poweredLpDistance_right {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (exponent : Nat) (first second : β → Fraction.Rational) :
    (left.product right).poweredLpDistance exponent
        (fun pair => first pair.2) (fun pair => second pair.2) =
      left.total * right.poweredLpDistance exponent first second := by
  change (left.product right).integral (fun pair =>
      Distance.rationalSeparation (first pair.2) (second pair.2) ^ exponent) =
    left.total * right.integral (fun item =>
      Distance.rationalSeparation (first item) (second item) ^ exponent)
  calc
    (left.product right).integral (fun pair =>
          Distance.rationalSeparation (first pair.2) (second pair.2) ^ exponent) =
        (left.product right).integral (fun pair =>
          1 * Distance.rationalSeparation (first pair.2) (second pair.2) ^ exponent) := by
      exact (left.product right).integral_congr _ _ (fun pair => by ring1)
    _ = left.integral (fun _ => 1) *
        right.integral (fun item =>
          Distance.rationalSeparation (first item) (second item) ^ exponent) :=
      left.product_integral_mul right (fun _ => 1)
        (fun item =>
          Distance.rationalSeparation (first item) (second item) ^ exponent)
    _ = left.total * right.integral (fun item =>
          Distance.rationalSeparation (first item) (second item) ^ exponent) := by
      rw [left.integral_constant]
      ring1

/-- A left-coordinate observable's product magnitude integral is its original magnitude integral times right total mass.
-/
theorem product_poweredL1_left {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (value : α → Fraction.Rational) :
    (left.product right).poweredL1 (fun pair => value pair.1) =
      left.poweredL1 value * right.total := by
  have preserved := left.product_poweredLp_left right 1 value
  rw [(left.product right).poweredLp_one, left.poweredLp_one] at preserved
  exact preserved

/-- A right-coordinate observable's product magnitude integral is left total mass times its original magnitude integral.
-/
theorem product_poweredL1_right {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (value : β → Fraction.Rational) :
    (left.product right).poweredL1 (fun pair => value pair.2) =
      left.total * right.poweredL1 value := by
  have preserved := left.product_poweredLp_right right 1 value
  rw [(left.product right).poweredLp_one, right.poweredLp_one] at preserved
  exact preserved

/-- A left-coordinate observable's product square integral is its original square integral times right total mass. -/
theorem product_poweredL2_left {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (value : α → Fraction.Rational) :
    (left.product right).poweredL2 (fun pair => value pair.1) =
      left.poweredL2 value * right.total := by
  have preserved := left.product_poweredLp_left right 2 value
  rw [(left.product right).poweredLp_two, left.poweredLp_two] at preserved
  exact preserved

/-- A right-coordinate observable's product square integral is left total mass times its original square integral. -/
theorem product_poweredL2_right {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (value : β → Fraction.Rational) :
    (left.product right).poweredL2 (fun pair => value pair.2) =
      left.total * right.poweredL2 value := by
  have preserved := left.product_poweredLp_right right 2 value
  rw [(left.product right).poweredLp_two, right.poweredLp_two] at preserved
  exact preserved

/-- Integrated separation of left-coordinate observables is their original separation integral times right total mass.
-/
theorem product_l1Distance_left {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (first second : α → Fraction.Rational) :
    (left.product right).l1Distance
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.l1Distance first second * right.total := by
  have preserved := left.product_poweredLpDistance_left right 1 first second
  rw [(left.product right).poweredLpDistance_one,
    left.poweredLpDistance_one] at preserved
  exact preserved

/-- Integrated separation of right-coordinate observables is left total mass times their original separation integral.
-/
theorem product_l1Distance_right {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (first second : β → Fraction.Rational) :
    (left.product right).l1Distance
        (fun pair => first pair.2) (fun pair => second pair.2) =
      left.total * right.l1Distance first second := by
  have preserved := left.product_poweredLpDistance_right right 1 first second
  rw [(left.product right).poweredLpDistance_one,
    right.poweredLpDistance_one] at preserved
  exact preserved

/-- Squared integrated distance of left-coordinate observables is their original squared distance times right total
mass. -/
theorem product_poweredL2Distance_left {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (first second : α → Fraction.Rational) :
    (left.product right).poweredL2Distance
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.poweredL2Distance first second * right.total := by
  have preserved := left.product_poweredLpDistance_left right 2 first second
  rw [(left.product right).poweredLpDistance_two,
    left.poweredLpDistance_two] at preserved
  exact preserved

/-- Squared integrated distance of right-coordinate observables is left total mass times their original squared
distance. -/
theorem product_poweredL2Distance_right {α β : Type}
    (left : Measure.Content α) (right : Measure.Content β)
    (first second : β → Fraction.Rational) :
    (left.product right).poweredL2Distance
        (fun pair => first pair.2) (fun pair => second pair.2) =
      left.total * right.poweredL2Distance first second := by
  have preserved := left.product_poweredLpDistance_right right 2 first second
  rw [(left.product right).poweredLpDistance_two,
    right.poweredLpDistance_two] at preserved
  exact preserved

end

end Content

namespace Distribution
end Distribution

end Purelib.Measure

end
