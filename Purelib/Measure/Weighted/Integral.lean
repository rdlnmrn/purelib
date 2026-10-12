module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic

section
public section

/-!
# Exact integrals on finite weighted occurrence lists

The integral sums each original weight times its rational observation.
Linearity, monotonicity, and constant integration concern the same retained
occurrences and do not require normalization of their total weight.
-/

namespace Purelib.Measure
namespace Distribution

section
open Purelib.Data.Rat
/-- Sum each retained rational weight times the observable at its original payload.

This is the unnormalized finite integral over the exact occurrence list. Repeated payloads remain separate summands, and
no normalization or support replacement is performed. -/
@[expose] def expectationWeight {α : Type} :
    List (Weighted α) → (α → Fraction.Rational) → Fraction.Rational
  | [], _ => 0
  | atom :: remaining, value =>
      atom.weight * value atom.item + expectationWeight remaining value

/-- Pointwise equal observables have equal weighted integrals over the same occurrence list.

Equality at the original head identifies its weighted scalar contribution.
Scalar congruence transports that contribution and the unchanged recursive
tail without identifying the observable functions themselves. -/
theorem expectationWeight_congr {α : Type}
    (atoms : List (Weighted α)) (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    expectationWeight atoms left = expectationWeight atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom remaining ih =>
      change atom.weight * left atom.item + expectationWeight remaining left =
        atom.weight * right atom.item + expectationWeight remaining right
      exact (congrArg (fun value => atom.weight * value +
        expectationWeight remaining left) (pointwise atom.item)).trans
          (congrArg (fun tail => atom.weight * right atom.item + tail) ih)

/-- The finite weighted integral preserves pointwise addition of rational observables.

Each retained head weight distributes over the two original observations.
Scalar transport of the recursive tail and regrouping of those same
summands identify the two integrals without changing either observation. -/
theorem expectationWeight_add {α : Type}
    (atoms : List (Weighted α)) (left right : α → Fraction.Rational) :
    expectationWeight atoms (fun item => left item + right item) =
      expectationWeight atoms left + expectationWeight atoms right := by
  induction atoms with
  | nil => exact (Fraction.Field.zero_add 0).symm
  | cons atom remaining ih =>
      change atom.weight * (left atom.item + right atom.item) +
          expectationWeight remaining (fun item => left item + right item) =
        (atom.weight * left atom.item + expectationWeight remaining left) +
          (atom.weight * right atom.item + expectationWeight remaining right)
      calc
        _ = atom.weight * (left atom.item + right atom.item) +
            (expectationWeight remaining left + expectationWeight remaining right) :=
          congrArg (fun tail =>
            atom.weight * (left atom.item + right atom.item) + tail) ih
        _ = _ := by ring1

/-- A rational scalar factors out of the exact finite weighted integral.

The same retained weights multiply each scaled observation. Scalar tail
transport, associativity, and distributivity identify this sum with the
factor times the original integral. -/
theorem expectationWeight_scale {α : Type}
    (atoms : List (Weighted α)) (factor : Fraction.Rational)
    (value : α → Fraction.Rational) :
    expectationWeight atoms (fun item => factor * value item) =
      factor * expectationWeight atoms value := by
  induction atoms with
  | nil => exact (Fraction.Field.mul_zero_direct factor).symm
  | cons atom remaining ih =>
      change atom.weight * (factor * value atom.item) +
          expectationWeight remaining (fun item => factor * value item) =
        factor * (atom.weight * value atom.item + expectationWeight remaining value)
      calc
        _ = atom.weight * (factor * value atom.item) +
            factor * expectationWeight remaining value :=
          congrArg (fun tail => atom.weight * (factor * value atom.item) + tail) ih
        _ = _ := by ring1

/-- An observable nonnegative at every retained occurrence has nonnegative weighted integral. -/
theorem expectationWeight_nonneg {α : Type}
    (atoms : List (Weighted α)) (value : α → Fraction.Rational)
    (nonnegative : ∀ atom, atom ∈ atoms → 0 ≤ value atom.item) :
    0 ≤ expectationWeight atoms value := by
  induction atoms with
  | nil => exact le_rfl
  | cons atom remaining inductionHypothesis =>
      have head := nonnegative atom List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          0 ≤ value candidate.item :=
        fun candidate member =>
          nonnegative candidate (List.mem_cons_of_mem atom member)
      exact add_nonneg
        (Fraction.Order.Arithmetic.mul_nonneg_direct atom.nonnegative head)
        (inductionHypothesis tail)

/-- Pointwise comparison on the retained occurrences bounds their weighted integrals. -/
theorem expectationWeight_mono {α : Type}
    (atoms : List (Weighted α)) (lower upper : α → Fraction.Rational)
    (pointwise : ∀ atom, atom ∈ atoms →
      lower atom.item ≤ upper atom.item) :
    expectationWeight atoms lower ≤ expectationWeight atoms upper := by
  induction atoms with
  | nil => exact le_rfl
  | cons atom remaining inductionHypothesis =>
      have head := pointwise atom List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          lower candidate.item ≤ upper candidate.item :=
        fun candidate member =>
          pointwise candidate (List.mem_cons_of_mem atom member)
      exact add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          head atom.nonnegative)
        (inductionHypothesis tail)

/-- A lower threshold on selected occurrences bounds threshold times event weight by the nonnegative observable's
weighted integral.

The observable is nonnegative on every retained occurrence and at least the threshold wherever the event holds. The same
weighted list supplies both the event weight and integral. -/
theorem threshold_mul_eventWeight_le_expectationWeight {α : Type}
    (atoms : List (Weighted α)) (event : α → Bool)
    (value : α → Fraction.Rational) (threshold : Fraction.Rational)
    (nonnegative : ∀ atom, atom ∈ atoms → 0 ≤ value atom.item)
    (selectedLower : ∀ atom, atom ∈ atoms → event atom.item = true →
      threshold ≤ value atom.item) :
    threshold * eventWeight atoms event ≤
      expectationWeight atoms value := by
  induction atoms with
  | nil =>
      simp only [eventWeight, expectationWeight, mul_zero]
      exact le_rfl
  | cons atom remaining inductionHypothesis =>
      have headNonnegative := nonnegative atom List.mem_cons_self
      have tailNonnegative : ∀ candidate, candidate ∈ remaining →
          0 ≤ value candidate.item :=
        fun candidate member =>
          nonnegative candidate (List.mem_cons_of_mem atom member)
      have tailLower : ∀ candidate, candidate ∈ remaining →
          event candidate.item = true → threshold ≤ value candidate.item :=
        fun candidate member =>
          selectedLower candidate (List.mem_cons_of_mem atom member)
      have tailBound := inductionHypothesis tailNonnegative tailLower
      cases selected : event atom.item
      · simp only [eventWeight, selected, zero_add, expectationWeight]
        exact tailBound.trans
          (le_add_of_nonneg_left
            (Fraction.Order.Arithmetic.mul_nonneg_direct
              atom.nonnegative headNonnegative))
      · have headLower :=
          selectedLower atom List.mem_cons_self selected
        have scaled :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            headLower atom.nonnegative
        simp only [eventWeight, selected, expectationWeight]
        calc
          threshold * (atom.weight + eventWeight remaining event) =
              atom.weight * threshold +
                threshold * eventWeight remaining event := by ring1
          _ ≤ atom.weight * value atom.item +
                expectationWeight remaining value :=
            add_le_add scaled tailBound

/-- Return one or zero according to the supplied Boolean event at the payload. -/
@[expose] def indicator {α : Type} (event : α → Bool) (item : α) : Fraction.Rational :=
  match event item with
  | true => 1
  | false => 0

/-- The weighted integral of a constant equals the exact total weight times that constant.

Every original occurrence contributes its retained weight times the same
constant. Scalar tail transport and distributivity identify the recursive
sum with the original total; normalization is not required. -/
theorem weighted_constant {α : Type}
    (atoms : List (Weighted α)) (constant : Fraction.Rational) :
    expectationWeight atoms (fun _ => constant) =
      totalWeight atoms * constant := by
  induction atoms with
  | nil => exact (Fraction.Field.zero_mul_direct constant).symm
  | cons atom remaining ih =>
      change atom.weight * constant + expectationWeight remaining (fun _ => constant) =
        (atom.weight + totalWeight remaining) * constant
      calc
        _ = atom.weight * constant + totalWeight remaining * constant :=
          congrArg (fun tail => atom.weight * constant + tail) ih
        _ = _ := by ring1

/-- Integrating a Boolean indicator over retained occurrences gives their event weight.

Each selected head contributes its original weight, and an unselected head
contributes scalar zero. Scalar transport of the same tail identifies the
integral and event scans without requiring total-weight normalization. -/
theorem expectationWeight_indicator {α : Type}
    (atoms : List (Weighted α)) (event : α → Bool) :
    expectationWeight atoms (indicator event) = eventWeight atoms event := by
  induction atoms with
  | nil => rfl
  | cons atom remaining ih =>
      let contribution : Fraction.Rational :=
        match event atom.item with | true => atom.weight | false => 0
      have head : atom.weight * indicator event atom.item = contribution := by
        change atom.weight * (match event atom.item with | true => 1 | false => 0) =
          (match event atom.item with | true => atom.weight | false => 0)
        cases event atom.item with
        | false => exact Fraction.Field.mul_zero_direct atom.weight
        | true =>
            exact (Fraction.Field.mul_comm atom.weight 1).trans
              (Fraction.Field.one_mul atom.weight)
      change atom.weight * indicator event atom.item +
          expectationWeight remaining (indicator event) =
        contribution + eventWeight remaining event
      exact (congrArg (fun scalar => scalar +
        expectationWeight remaining (indicator event)) head).trans
          (congrArg (fun tail => contribution + tail) ih)

end

end Distribution

end Purelib.Measure

end
