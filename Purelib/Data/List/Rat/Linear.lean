module
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! Exact finite sums of rational-valued terms. -/

public section

namespace Purelib.Data.List.Rat.Linear

open Purelib.Data.Rat

/-- Pointwise equal finite rational terms have equal sums over the same original occurrences. -/
theorem sum_congr {α : Type} (first second : α → Fraction.Rational) :
    ∀ items : List α, (∀ item ∈ items, first item = second item) →
      (items.map first).sum = (items.map second).sum
  | [], _ => rfl
  | head :: tail, equal => by
      have firstEqual := equal head List.mem_cons_self
      have remaining := sum_congr first second tail (fun item member => equal item (List.mem_cons_of_mem head member))
      change first head + (tail.map first).sum = second head + (tail.map second).sum
      rw [firstEqual, remaining]

/-- A finite rational sum distributes over pointwise addition. -/
theorem sum_add {α : Type} (first second : α → Fraction.Rational) : ∀ items : List α,
    (items.map (fun item => first item + second item)).sum = (items.map first).sum + (items.map second).sum
  | [] => by
      change (0 : Fraction.Rational) = 0 + 0
      ring1
  | head :: tail => by
      change (first head + second head) + (tail.map (fun item => first item + second item)).sum =
        (first head + (tail.map first).sum) + (second head + (tail.map second).sum)
      rw [sum_add first second tail]
      ring1

/-- A finite rational sum of zero terms is zero. -/
theorem sum_zero {α : Type} : ∀ items : List α,
    (items.map (fun _ => (0 : Fraction.Rational))).sum = 0
  | [] => rfl
  | _ :: tail => by
      change (0 : Fraction.Rational) + (tail.map (fun _ => (0 : Fraction.Rational))).sum = 0
      rw [sum_zero tail]
      decide

/-- A finite sum of nonnegative rational terms is nonnegative. -/
theorem sum_nonnegative {α : Type} (term : α → Fraction.Rational) :
    ∀ items : List α, (∀ item ∈ items, 0 ≤ term item) → 0 ≤ (items.map term).sum
  | [], _ => Fraction.Order.Basic.le_refl _
  | head :: tail, nonnegative => by
      have first := nonnegative head List.mem_cons_self
      have rest := sum_nonnegative term tail (fun item member => nonnegative item (List.mem_cons_of_mem head member))
      have sum := Fraction.Order.Arithmetic.add_le_add_direct first rest
      change (0 : Fraction.Rational) ≤ term head + (tail.map term).sum at sum
      exact sum

/-- Interchange two finite rational sums without changing their retained entries. -/
theorem sum_swap {α β : Type} (term : α → β → Fraction.Rational) :
    ∀ (parents : List α) (children : List β),
      (children.map (fun child => (parents.map (fun parent => term parent child)).sum)).sum =
        (parents.map (fun parent => (children.map (term parent)).sum)).sum
  | [], children => by
      change (children.map (fun _ => (0 : Fraction.Rational))).sum = 0
      exact sum_zero children
  | parent :: remaining, children => by
      change (children.map (fun child => term parent child +
        (remaining.map (fun other => term other child)).sum)).sum =
          (children.map (term parent)).sum +
            (remaining.map (fun other => (children.map (term other)).sum)).sum
      rw [sum_add, sum_swap term remaining children]

/-- A fixed right factor distributes over a finite rational sum. -/
theorem sum_mul_right {α : Type} (term : α → Fraction.Rational) (factor : Fraction.Rational) :
    ∀ items : List α, (items.map (fun item => term item * factor)).sum = (items.map term).sum * factor
  | [] => by
      change (0 : Fraction.Rational) = 0 * factor
      ring1
  | head :: tail => by
      change term head * factor + (tail.map (fun item => term item * factor)).sum =
        (term head + (tail.map term).sum) * factor
      rw [sum_mul_right term factor tail]
      ring1

/-- Pointwise rational bounds remain bounds after summing the same finite occurrences. -/
theorem sum_le {α : Type} (first second : α → Fraction.Rational) :
    ∀ items : List α, (∀ item ∈ items, first item ≤ second item) → (items.map first).sum ≤ (items.map second).sum
  | [], _ => Fraction.Order.Basic.le_refl _
  | head :: tail, bounds => by
      have headBound := bounds head List.mem_cons_self
      have tailBound := sum_le first second tail (fun item member => bounds item (List.mem_cons_of_mem head member))
      change first head + (tail.map first).sum ≤ second head + (tail.map second).sum
      exact Fraction.Order.Arithmetic.add_le_add_direct headBound tailBound

/-- A nonnegative marked contribution is bounded by the sum of its actual point contributions. -/
theorem any_indicator_le {α : Type} (items : List α) (predicate : α → Bool)
    (weight : Fraction.Rational) (nonnegative : 0 ≤ weight) :
    (if items.any predicate then weight else 0) ≤
      (items.map (fun item => if predicate item then weight else 0)).sum := by
  induction items with
  | nil => exact Fraction.Order.Basic.le_refl _
  | cons head tail inductionHypothesis =>
      change (if predicate head || tail.any predicate then weight else 0) ≤
        (if predicate head then weight else 0) + (tail.map (fun item => if predicate item then weight else 0)).sum
      cases accepted : predicate head with
      | false =>
          change (if tail.any predicate then weight else 0) ≤
            0 + (tail.map (fun item => if predicate item then weight else 0)).sum
          rewrite [Fraction.Field.zero_add]
          exact inductionHypothesis
      | true =>
          change weight ≤ weight + (tail.map (fun item => if predicate item then weight else 0)).sum
          have tailNonnegative := sum_nonnegative (fun item => if predicate item then weight else 0) tail (by
            intro item _
            cases predicate item with
            | false => exact Fraction.Order.Basic.le_refl _
            | true => exact nonnegative)
          have total := Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl weight)
            tailNonnegative
          have identity : weight + 0 = weight := by ring1
          rw [identity] at total
          exact total

end Purelib.Data.List.Rat.Linear

end
