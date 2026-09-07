import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.NaturalLp
import FiniteMeasure.ContentIntegral
import FiniteMeasure.Stochastic

/-!
# Powered Lp laws on explicit finite products

Finite Fubini evaluation gives exact factorization of natural-powered
magnitudes for separable products.  Observables pulled back from either
coordinate retain their powered Lp quantities and distances exactly.  All
statements are finite rational identities; no roots or product sigma algebra
are constructed.
-/

namespace FiniteMeasure

namespace FiniteContent

/-- Natural-powered magnitude of a separable product factors for arbitrary
finite contents, including their unnormalized total masses. -/
theorem product_poweredLp_mul {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (exponent : Nat) (leftValue : α → Coordinate)
    (rightValue : β → Coordinate) :
    (left.product right).poweredLp exponent
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredLp exponent leftValue *
        right.poweredLp exponent rightValue := by
  change (left.product right).integral (fun pair =>
      rationalSeparation (leftValue pair.1 * rightValue pair.2) 0 ^
        exponent) =
    left.integral (fun item =>
        rationalSeparation (leftValue item) 0 ^ exponent) *
      right.integral (fun item =>
        rationalSeparation (rightValue item) 0 ^ exponent)
  calc
    (left.product right).integral (fun pair =>
        rationalSeparation (leftValue pair.1 * rightValue pair.2) 0 ^
          exponent) =
        (left.product right).integral (fun pair =>
          rationalSeparation (leftValue pair.1) 0 ^ exponent *
            rationalSeparation (rightValue pair.2) 0 ^ exponent) :=
      (left.product right).integral_congr _ _ (fun pair => by
        rw [rationalSeparation_mul_zero, mul_pow])
    _ = left.integral (fun item =>
          rationalSeparation (leftValue item) 0 ^ exponent) *
        right.integral (fun item =>
          rationalSeparation (rightValue item) 0 ^ exponent) :=
      left.product_integral_mul right
        (fun item => rationalSeparation (leftValue item) 0 ^ exponent)
        (fun item => rationalSeparation (rightValue item) 0 ^ exponent)

theorem product_poweredL1_mul {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate) :
    (left.product right).poweredL1
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredL1 leftValue * right.poweredL1 rightValue := by
  have factorization := left.product_poweredLp_mul right 1
    leftValue rightValue
  rw [(left.product right).poweredLp_one, left.poweredLp_one,
    right.poweredLp_one] at factorization
  exact factorization

theorem product_poweredL2_mul {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate) :
    (left.product right).poweredL2
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredL2 leftValue * right.poweredL2 rightValue := by
  have factorization := left.product_poweredLp_mul right 2
    leftValue rightValue
  rw [(left.product right).poweredLp_two, left.poweredLp_two,
    right.poweredLp_two] at factorization
  exact factorization

/-- Pullback from the left coordinate retains its powered quantity, scaled
by the total mass of the right content. -/
theorem product_poweredLp_left {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (exponent : Nat) (value : α → Coordinate) :
    (left.product right).poweredLp exponent (fun pair => value pair.1) =
      left.poweredLp exponent value * right.total := by
  change (left.product right).integral (fun pair =>
      rationalSeparation (value pair.1) 0 ^ exponent) =
    left.integral (fun item => rationalSeparation (value item) 0 ^ exponent) *
      right.total
  calc
    (left.product right).integral (fun pair =>
          rationalSeparation (value pair.1) 0 ^ exponent) =
        (left.product right).integral (fun pair =>
          rationalSeparation (value pair.1) 0 ^ exponent * 1) := by
      exact (left.product right).integral_congr _ _ (fun pair => by ring1)
    _ = left.integral (fun item =>
          rationalSeparation (value item) 0 ^ exponent) *
        right.integral (fun _ => 1) :=
      left.product_integral_mul right
        (fun item => rationalSeparation (value item) 0 ^ exponent)
        (fun _ => 1)
    _ = left.integral (fun item =>
          rationalSeparation (value item) 0 ^ exponent) * right.total := by
      rw [right.integral_constant]
      ring1

/-- The symmetric coordinate-pullback law for arbitrary finite contents. -/
theorem product_poweredLp_right {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (exponent : Nat) (value : β → Coordinate) :
    (left.product right).poweredLp exponent (fun pair => value pair.2) =
      left.total * right.poweredLp exponent value := by
  change (left.product right).integral (fun pair =>
      rationalSeparation (value pair.2) 0 ^ exponent) =
    left.total *
      right.integral (fun item => rationalSeparation (value item) 0 ^ exponent)
  calc
    (left.product right).integral (fun pair =>
          rationalSeparation (value pair.2) 0 ^ exponent) =
        (left.product right).integral (fun pair =>
          1 * rationalSeparation (value pair.2) 0 ^ exponent) := by
      exact (left.product right).integral_congr _ _ (fun pair => by ring1)
    _ = left.integral (fun _ => 1) *
        right.integral (fun item =>
          rationalSeparation (value item) 0 ^ exponent) :=
      left.product_integral_mul right (fun _ => 1)
        (fun item => rationalSeparation (value item) 0 ^ exponent)
    _ = left.total * right.integral (fun item =>
          rationalSeparation (value item) 0 ^ exponent) := by
      rw [left.integral_constant]
      ring1

theorem product_poweredLpDistance_left {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (exponent : Nat) (first second : α → Coordinate) :
    (left.product right).poweredLpDistance exponent
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.poweredLpDistance exponent first second * right.total := by
  change (left.product right).integral (fun pair =>
      rationalSeparation (first pair.1) (second pair.1) ^ exponent) =
    left.integral (fun item =>
      rationalSeparation (first item) (second item) ^ exponent) * right.total
  calc
    (left.product right).integral (fun pair =>
          rationalSeparation (first pair.1) (second pair.1) ^ exponent) =
        (left.product right).integral (fun pair =>
          rationalSeparation (first pair.1) (second pair.1) ^ exponent * 1) := by
      exact (left.product right).integral_congr _ _ (fun pair => by ring1)
    _ = left.integral (fun item =>
          rationalSeparation (first item) (second item) ^ exponent) *
        right.integral (fun _ => 1) :=
      left.product_integral_mul right
        (fun item =>
          rationalSeparation (first item) (second item) ^ exponent)
        (fun _ => 1)
    _ = left.integral (fun item =>
          rationalSeparation (first item) (second item) ^ exponent) *
        right.total := by
      rw [right.integral_constant]
      ring1

theorem product_poweredLpDistance_right {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (exponent : Nat) (first second : β → Coordinate) :
    (left.product right).poweredLpDistance exponent
        (fun pair => first pair.2) (fun pair => second pair.2) =
      left.total * right.poweredLpDistance exponent first second := by
  change (left.product right).integral (fun pair =>
      rationalSeparation (first pair.2) (second pair.2) ^ exponent) =
    left.total * right.integral (fun item =>
      rationalSeparation (first item) (second item) ^ exponent)
  calc
    (left.product right).integral (fun pair =>
          rationalSeparation (first pair.2) (second pair.2) ^ exponent) =
        (left.product right).integral (fun pair =>
          1 * rationalSeparation (first pair.2) (second pair.2) ^ exponent) := by
      exact (left.product right).integral_congr _ _ (fun pair => by ring1)
    _ = left.integral (fun _ => 1) *
        right.integral (fun item =>
          rationalSeparation (first item) (second item) ^ exponent) :=
      left.product_integral_mul right (fun _ => 1)
        (fun item =>
          rationalSeparation (first item) (second item) ^ exponent)
    _ = left.total * right.integral (fun item =>
          rationalSeparation (first item) (second item) ^ exponent) := by
      rw [left.integral_constant]
      ring1

theorem product_poweredL1_left {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (value : α → Coordinate) :
    (left.product right).poweredL1 (fun pair => value pair.1) =
      left.poweredL1 value * right.total := by
  have preserved := left.product_poweredLp_left right 1 value
  rw [(left.product right).poweredLp_one, left.poweredLp_one] at preserved
  exact preserved

theorem product_poweredL1_right {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (value : β → Coordinate) :
    (left.product right).poweredL1 (fun pair => value pair.2) =
      left.total * right.poweredL1 value := by
  have preserved := left.product_poweredLp_right right 1 value
  rw [(left.product right).poweredLp_one, right.poweredLp_one] at preserved
  exact preserved

theorem product_poweredL2_left {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (value : α → Coordinate) :
    (left.product right).poweredL2 (fun pair => value pair.1) =
      left.poweredL2 value * right.total := by
  have preserved := left.product_poweredLp_left right 2 value
  rw [(left.product right).poweredLp_two, left.poweredLp_two] at preserved
  exact preserved

theorem product_poweredL2_right {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (value : β → Coordinate) :
    (left.product right).poweredL2 (fun pair => value pair.2) =
      left.total * right.poweredL2 value := by
  have preserved := left.product_poweredLp_right right 2 value
  rw [(left.product right).poweredLp_two, right.poweredLp_two] at preserved
  exact preserved

theorem product_l1Distance_left {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (first second : α → Coordinate) :
    (left.product right).l1Distance
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.l1Distance first second * right.total := by
  have preserved := left.product_poweredLpDistance_left right 1 first second
  rw [(left.product right).poweredLpDistance_one,
    left.poweredLpDistance_one] at preserved
  exact preserved

theorem product_l1Distance_right {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (first second : β → Coordinate) :
    (left.product right).l1Distance
        (fun pair => first pair.2) (fun pair => second pair.2) =
      left.total * right.l1Distance first second := by
  have preserved := left.product_poweredLpDistance_right right 1 first second
  rw [(left.product right).poweredLpDistance_one,
    right.poweredLpDistance_one] at preserved
  exact preserved

theorem product_poweredL2Distance_left {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (first second : α → Coordinate) :
    (left.product right).poweredL2Distance
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.poweredL2Distance first second * right.total := by
  have preserved := left.product_poweredLpDistance_left right 2 first second
  rw [(left.product right).poweredLpDistance_two,
    left.poweredLpDistance_two] at preserved
  exact preserved

theorem product_poweredL2Distance_right {α β : Type}
    (left : FiniteContent α) (right : FiniteContent β)
    (first second : β → Coordinate) :
    (left.product right).poweredL2Distance
        (fun pair => first pair.2) (fun pair => second pair.2) =
      left.total * right.poweredL2Distance first second := by
  have preserved := left.product_poweredLpDistance_right right 2 first second
  rw [(left.product right).poweredLpDistance_two,
    right.poweredLpDistance_two] at preserved
  exact preserved

end FiniteContent

namespace Distribution

/-- Natural-powered magnitude of a separable product factors exactly. -/
theorem product_poweredLp_mul {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (exponent : Nat) (leftValue : α → Coordinate)
    (rightValue : β → Coordinate) :
    (left.product right).poweredLp exponent
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredLp exponent leftValue *
        right.poweredLp exponent rightValue := by
  change (left.product right).expectation (fun pair =>
      rationalSeparation (leftValue pair.1 * rightValue pair.2) 0 ^
        exponent) =
    left.expectation (fun item =>
        rationalSeparation (leftValue item) 0 ^ exponent) *
      right.expectation (fun item =>
        rationalSeparation (rightValue item) 0 ^ exponent)
  calc
    (left.product right).expectation (fun pair =>
        rationalSeparation (leftValue pair.1 * rightValue pair.2) 0 ^
          exponent) =
        (left.product right).expectation (fun pair =>
          rationalSeparation (leftValue pair.1) 0 ^ exponent *
            rationalSeparation (rightValue pair.2) 0 ^ exponent) :=
      (left.product right).expectation_congr _ _ (fun pair => by
        rw [rationalSeparation_mul_zero, mul_pow])
    _ = left.expectation (fun item =>
          rationalSeparation (leftValue item) 0 ^ exponent) *
        right.expectation (fun item =>
          rationalSeparation (rightValue item) 0 ^ exponent) :=
      left.product_expectation_mul right
        (fun item => rationalSeparation (leftValue item) 0 ^ exponent)
        (fun item => rationalSeparation (rightValue item) 0 ^ exponent)

theorem product_poweredL1_mul {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate) :
    (left.product right).poweredL1
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredL1 leftValue * right.poweredL1 rightValue := by
  have factorization := left.product_poweredLp_mul right 1
    leftValue rightValue
  rw [(left.product right).poweredLp_one, left.poweredLp_one,
    right.poweredLp_one] at factorization
  exact factorization

theorem product_poweredL2_mul {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate) :
    (left.product right).poweredL2
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.poweredL2 leftValue * right.poweredL2 rightValue := by
  have factorization := left.product_poweredLp_mul right 2
    leftValue rightValue
  rw [(left.product right).poweredLp_two, left.poweredLp_two,
    right.poweredLp_two] at factorization
  exact factorization

/-- Pullback from the left coordinate preserves every natural-powered Lp
quantity on the normalized finite product. -/
theorem product_poweredLp_left {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (exponent : Nat) (value : α → Coordinate) :
    (left.product right).poweredLp exponent (fun pair => value pair.1) =
      left.poweredLp exponent value := by
  change (left.product right).expectation (fun pair =>
      rationalSeparation (value pair.1) 0 ^ exponent) =
    left.expectation (fun item => rationalSeparation (value item) 0 ^ exponent)
  rw [left.product_expectation_iterated]
  exact left.expectation_congr _ _ (fun item =>
    right.expectation_constant
      (rationalSeparation (value item) 0 ^ exponent))

theorem product_poweredLp_right {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (exponent : Nat) (value : β → Coordinate) :
    (left.product right).poweredLp exponent (fun pair => value pair.2) =
      right.poweredLp exponent value := by
  change (left.product right).expectation (fun pair =>
      rationalSeparation (value pair.2) 0 ^ exponent) =
    right.expectation (fun item => rationalSeparation (value item) 0 ^ exponent)
  rw [left.product_expectation_iterated]
  exact left.expectation_constant
    (right.expectation (fun item =>
      rationalSeparation (value item) 0 ^ exponent))

theorem product_poweredL1_left {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : α → Coordinate) :
    (left.product right).poweredL1 (fun pair => value pair.1) =
      left.poweredL1 value := by
  have preserved := left.product_poweredLp_left right 1 value
  rw [(left.product right).poweredLp_one, left.poweredLp_one] at preserved
  exact preserved

theorem product_poweredL1_right {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : β → Coordinate) :
    (left.product right).poweredL1 (fun pair => value pair.2) =
      right.poweredL1 value := by
  have preserved := left.product_poweredLp_right right 1 value
  rw [(left.product right).poweredLp_one, right.poweredLp_one] at preserved
  exact preserved

theorem product_poweredL2_left {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : α → Coordinate) :
    (left.product right).poweredL2 (fun pair => value pair.1) =
      left.poweredL2 value := by
  have preserved := left.product_poweredLp_left right 2 value
  rw [(left.product right).poweredLp_two, left.poweredLp_two] at preserved
  exact preserved

theorem product_poweredL2_right {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : β → Coordinate) :
    (left.product right).poweredL2 (fun pair => value pair.2) =
      right.poweredL2 value := by
  have preserved := left.product_poweredLp_right right 2 value
  rw [(left.product right).poweredLp_two, right.poweredLp_two] at preserved
  exact preserved

/-- Pullback from the left coordinate preserves powered distance exactly. -/
theorem product_poweredLpDistance_left {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (exponent : Nat) (first second : α → Coordinate) :
    (left.product right).poweredLpDistance exponent
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.poweredLpDistance exponent first second := by
  change (left.product right).expectation (fun pair =>
      rationalSeparation (first pair.1) (second pair.1) ^ exponent) =
    left.expectation (fun item =>
      rationalSeparation (first item) (second item) ^ exponent)
  rw [left.product_expectation_iterated]
  exact left.expectation_congr _ _ (fun item =>
    right.expectation_constant
      (rationalSeparation (first item) (second item) ^ exponent))

theorem product_poweredLpDistance_right {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (exponent : Nat) (first second : β → Coordinate) :
    (left.product right).poweredLpDistance exponent
        (fun pair => first pair.2) (fun pair => second pair.2) =
      right.poweredLpDistance exponent first second := by
  change (left.product right).expectation (fun pair =>
      rationalSeparation (first pair.2) (second pair.2) ^ exponent) =
    right.expectation (fun item =>
      rationalSeparation (first item) (second item) ^ exponent)
  rw [left.product_expectation_iterated]
  exact left.expectation_constant
    (right.expectation (fun item =>
      rationalSeparation (first item) (second item) ^ exponent))

theorem product_l1Distance_left {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (first second : α → Coordinate) :
    (left.product right).l1Distance
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.l1Distance first second := by
  have preserved := left.product_poweredLpDistance_left right 1 first second
  rw [(left.product right).poweredLpDistance_one,
    left.poweredLpDistance_one] at preserved
  exact preserved

theorem product_l1Distance_right {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (first second : β → Coordinate) :
    (left.product right).l1Distance
        (fun pair => first pair.2) (fun pair => second pair.2) =
      right.l1Distance first second := by
  have preserved := left.product_poweredLpDistance_right right 1 first second
  rw [(left.product right).poweredLpDistance_one,
    right.poweredLpDistance_one] at preserved
  exact preserved

theorem product_poweredL2Distance_left {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (first second : α → Coordinate) :
    (left.product right).poweredL2Distance
        (fun pair => first pair.1) (fun pair => second pair.1) =
      left.poweredL2Distance first second := by
  have preserved := left.product_poweredLpDistance_left right 2 first second
  rw [(left.product right).poweredLpDistance_two,
    left.poweredLpDistance_two] at preserved
  exact preserved

theorem product_poweredL2Distance_right {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (first second : β → Coordinate) :
    (left.product right).poweredL2Distance
        (fun pair => first pair.2) (fun pair => second pair.2) =
      right.poweredL2Distance first second := by
  have preserved := left.product_poweredLpDistance_right right 2 first second
  rw [(left.product right).poweredLpDistance_two,
    right.poweredLpDistance_two] at preserved
  exact preserved

end Distribution

end FiniteMeasure
