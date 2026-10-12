module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Bound.Process
import Purelib.Approximation.OneSided.Basic
public import Purelib.Approximation.OneSided.Located
public import Purelib.Approximation.Rational.Budget.Geometric
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Worked one-sided rational process examples

All four examples are finite and executable.  They cover algebraic bisection,
staged rational classification, fuel-bounded inspection of finite routes, and
factorial-position radix prefixes associated with a Liouville-style target.

None of the constructions defines a limit, a completed real, or a hidden endpoint.
The conversion to `BoundProcess` occurs only because each example supplies a
separate finite gap request.
-/

namespace Purelib.Examples.Approximation.Rational.Radix.FactorialPosition.WorkedExamples

open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Examples
open Purelib.Data.Rat
open Purelib.Algebra
open Purelib.Data.Nat
open Purelib

/-! ## Example 1: algebraic bisection around square three -/

/-! ## Example 2: staged finite probability for `x² < 2` -/

/-! ## Example 3: short-circuit inspection of finite graph routes -/

/-! ## Example 4: finite prefixes of the base-four Liouville constant

Classically, the nested radix cylinders below approach
`L₄ = ∑ k ≥ 1, 4⁻ᵏ!`, a Liouville and hence transcendental number.  The Lean
construction never forms that infinite series or a completed endpoint: every
state contains only a finite digit prefix and an explicit rational cylinder.
-/

/-- The recursively computed natural-number factorial used by the digit rule. -/
def factorial : Nat → Nat
  | 0 => 1
  | index + 1 => factorial index * (index
    + 1)

/-- Check the displayed position against a finite list of computed factorials.

Searches indices from zero through the supplied position and retains a Boolean membership result. -/
def isFactorialPosition (position
  : Nat) : Bool :=
  (List.range (position + 1)).any fun index =>
    decide (factorial index = position)

/-- The radix-four digit one exactly at positive factorial positions, otherwise zero. -/
def digit (index : Nat) :
  Rational :=
  if isFactorialPosition (index + 1) then 1 else 0

/-- Every retained factorial-position digit is nonnegative. -/
theorem digit_nonnegative (index :
  Nat) : 0 ≤ digit index := by
  unfold digit
  split <;> decide

/-- Every retained factorial-position digit is at most one. -/
theorem digit_le_one (index : Nat)
  : digit index ≤ 1 := by
  unfold digit
  split <;> decide

/-- The radix-four place bound at the given finite index. -/
def place (index : Nat) :
  Rational :=
  (1 / 4 : Rational) ^ index

/-- Every radix-four place bound is nonnegative. -/
theorem place_nonnegative (index :
  Nat) : 0 ≤ place index :=
  Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) index

/-- Every finite radix-four place bound is strictly positive. -/
theorem place_positive (index :
  Nat) : 0 < place index :=
  Fraction.Order.Arithmetic.pow_pos_direct (by decide) index

/-- The next place bound is one quarter of the current bound. -/
theorem place_succ (index : Nat) :
    place (index + 1) =
      place index / 4 := by
  unfold place
  rw [pow_succ, Field.ExplicitField.div_eq_mul_inv,
    Field.ExplicitField.div_eq_mul_inv,
    Fraction.Field.one_mul]

/-- The original finite radix-four prefix with factorial-position digits.

Accumulates each retained digit at its corresponding quarter-power place without changing the recursive index order. -/
def prefixValue : Nat →
  Rational
  | 0 => 0
  | index + 1 => prefixValue index +
    digit index *
    (place index / 4)

/-- The finite prefix value plus its retained radix-four tail bound. -/
def prefixUpper (index : Nat) :
  Rational :=
  prefixValue index +
    place index

/-- Appending the next nonnegative digit cannot decrease the prefix value. -/
theorem prefix_step_mono (index :
  Nat) :
    prefixValue index ≤
      prefixValue (index + 1) := by
  rw [prefixValue]
  exact le_add_of_nonneg_right
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (digit_nonnegative index)
      (Fraction.Order.Field.div_nonneg_direct
        (place_nonnegative index) (by decide)))

/-- Appending the next digit refines the retained upper prefix bound.

Uses the original zero-or-one digit branch and quarter-place identity to retain the explicit rational upper estimate. -/
theorem prefixUpper_step_antitone
  (index : Nat) :
    prefixUpper (index + 1) ≤
      prefixUpper index := by
  unfold prefixUpper
  rw [prefixValue,
    place_succ]
  have placeNonnegative := place_nonnegative index
  have placeQuarter : place index / 4 =
      (1 / 4 : Rational) * place index := by
    change place index * (4 : Rational)⁻¹ =
      (1 * (4 : Rational)⁻¹) * place index
    rw [Fraction.Field.one_mul]
    ring1
  rw [placeQuarter]
  unfold digit
  split
  · calc
      prefixValue index + 1 * ((1 / 4 : Rational)
        * place index) +
            (1 / 4 : Rational) * place index =
          prefixValue index +
            ((1 / 4 : Rational) + 1 / 4) * place
              index := by ring1
      _ = prefixValue index + (1 / 2 : Rational)
        * place index := by
        rw [show (1 / 4 : Rational) + 1 / 4 = 1 / 2 by decide]
      _ ≤ prefixValue index + 1 *
        place index :=
        add_le_add le_rfl
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by decide) placeNonnegative)
      _ = prefixValue index +
        place index := by
        ring1
  · calc
      prefixValue index + 0 * ((1 / 4 : Rational)
        * place index) +
            (1 / 4 : Rational) * place index =
          prefixValue index + (1 / 4 : Rational)
            * place index := by ring1
      _ ≤ prefixValue index + 1 *
        place index :=
        add_le_add le_rfl
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by decide) placeNonnegative)
      _ = prefixValue index +
        place index := by
        ring1

/-- Every finite prefix value is nonnegative. -/
theorem prefix_nonnegative : ∀
  index : Nat, 0 ≤ prefixValue index
  | 0 => le_rfl
  | index + 1 =>
      (prefix_nonnegative index).trans
        (prefix_step_mono index)

/-- Every retained upper prefix bound is at most one. -/
theorem prefixUpper_le_one : ∀
  index : Nat, prefixUpper index ≤ 1
  | 0 => by
      unfold prefixUpper
        prefixValue
        place
      decide
  | index + 1 =>
      (prefixUpper_step_antitone index).trans
        (prefixUpper_le_one index)

/-- Larger finite indices have no smaller retained prefix values. -/
theorem prefix_mono_index {earlier
  later : Nat} (order : earlier ≤ later) :
    prefixValue earlier ≤
      prefixValue later := by
  obtain ⟨extra, rfl⟩ :=
    (show ∃ extra : Nat, later = earlier + extra from
      ⟨later - earlier, (Subtraction.add_sub_of_le order).symm⟩)
  clear order
  induction extra with
  | zero => exact le_rfl
  | succ extra inductionHypothesis =>
      exact inductionHypothesis.trans
        (by
            simpa only [Nat.add_succ]
              using prefix_step_mono (earlier + extra))

/-- Larger finite indices have no larger retained upper bounds. -/
theorem prefixUpper_antitone_index
  {earlier later : Nat}
    (order : earlier ≤ later) : prefixUpper later ≤
      prefixUpper earlier := by
  obtain ⟨extra, rfl⟩ :=
    (show ∃ extra : Nat, later = earlier + extra from
      ⟨later - earlier, (Subtraction.add_sub_of_le order).symm⟩)
  clear order
  induction extra with
  | zero => exact le_rfl
  | succ extra inductionHypothesis =>
      have step : prefixUpper (earlier + (extra + 1)) ≤
          prefixUpper (earlier + extra) := by
        simpa only [Nat.add_succ] using
          prefixUpper_step_antitone (earlier + extra)
      exact step.trans inductionHypothesis

/-- The lower approximation process formed by the original finite prefixes. -/
def lower :
  Approximation.LowerProcess where
  State := Nat
  bound := prefixValue
  initial := 0
  refine index := index + 1
  monotone := prefix_step_mono
  refinesInitial := prefix_nonnegative

/-- The upper approximation process formed by the retained prefix-plus-tail bounds. -/
def upper :
  Approximation.UpperProcess where
  State := Nat
  bound := prefixUpper
  initial := 0
  refine index := index + 1
  antitone := prefixUpper_step_antitone
  refinesInitial state := by
    change prefixUpper state ≤ 1
    exact prefixUpper_le_one state

/-- Pair the lower and upper readings at the same original prefix index. -/
def observation (index : Nat) :
  Approximation.PairedObservation lower
  upper where
  lowerState := index
  upperState := index
  ordered := by
    change prefixValue index ≤
      prefixValue index +
      place index
    exact le_add_of_nonneg_right (place_nonnegative index)

/-- The paired observation gap is exactly the retained place bound. -/
@[simp] theorem observation_gap
  (index : Nat) :
    (observation index).gap =
      place index := by
  change prefixUpper index -
    prefixValue index =
    place index
  unfold prefixUpper
  ring1

/-- The located pair of factorial-position prefix processes.

Accuracy requests retain the current index and use the original finite quarter-geometric search to choose a later index
with a sufficiently small gap. -/
def located :
  Approximation.LocatedPair lower
  upper where
  State := Nat
  observation := observation
  initial := 0
  request index epsilon _ :=
    Approximation.Geometric.firstQuarterBelow 1 index epsilon
  request_refines index epsilon positive := by
    have order := Approximation.Geometric.firstQuarterBelow_ge 1 index epsilon
    exact ⟨prefix_mono_index order,
      prefixUpper_antitone_index order⟩
  accurate index epsilon positive := by
    rw [observation_gap,
      place]
    have accurate := Approximation.Geometric.firstQuarterBelow_accurate
      1 (by decide) index epsilon positive
    rw [Approximation.Geometric.quarterAllowance_eq_mul_pow] at accurate
    simpa only [Fraction.Field.one_mul] using accurate
  refinesInitial index :=
    ⟨prefix_nonnegative index,
      prefixUpper_le_one index⟩

/-- The first six retained digits are one, one, zero, zero, zero, one. -/
theorem first_digits :
    digit 0 = 1 ∧
      digit 1 = 1 ∧
      digit 2 = 0 ∧
      digit 3 = 0 ∧
        digit 4 = 0 ∧
        digit 5 = 1 := by
  decide

/-- The six-digit prefix is five sixteenths plus its final retained place contribution. -/
theorem prefix_six :
    prefixValue 6 = 5 / 16 +
      place 5 / 4 := by
  rcases first_digits with ⟨_, _, digitTwo, digitThree,
    digitFour, digitFive⟩
  rw [prefixValue,
    prefixValue,
    prefixValue,
    prefixValue,
    digitTwo, digitThree, digitFour, digitFive]
  rw [show prefixValue 2 = 5 / 16 by decide]
  ring1

/-- The original prefix and upper readings at indices zero, two and six.

Keeps the exact rational values and the separate retained place contributions at the sixth digit. -/
theorem displayed_prefixes :
    prefixValue 0 = 0 ∧
      prefixUpper 0 = 1 ∧
      prefixValue 2 = 5 / 16 ∧
        prefixUpper 2 = 3 / 8 ∧
      prefixValue 6 = 5 / 16 +
        place 5 / 4 ∧
      prefixUpper 6 = 5 / 16 +
        place 5 / 4 +
        place 6 := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · exact (by decide)
  constructor
  · decide
  constructor
  · exact prefix_six
  · unfold prefixUpper
    rw [prefix_six]

/-- The original one-tenth gap request selects index two. -/
theorem tenth_request_index :
    Approximation.Geometric.firstQuarterBelow 1 0 (1 / 10) = 2 := by
  decide

/-- A one-tenth bound-process request has width below one tenth. -/
theorem tenth_request_width :
    let process := located.toBoundProcess
    (process.bound
      (process.request process.initial (1 / 10) (by decide))).width <
        1 / 10 :=
  located.toBoundProcess.accurate _ _ (by decide)

end Purelib.Examples.Approximation.Rational.Radix.FactorialPosition.WorkedExamples

end
