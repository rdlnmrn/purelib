module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

public section

/-!
# Shared finite weighted-list operations

These scaling and append identities are the list-algebra layer shared by
finite contents and normalized finite distributions.
-/

namespace Purelib.Measure

open Distribution

section
open Purelib.Data.Rat
/-- Multiply every retained occurrence weight by the supplied nonnegative rational factor.

Keep the same payload order and multiplicities. Each product retains its direct nonnegativity proof, including a zero
factor or zero original weight. -/
@[expose] def scaleAtoms {α : Type} (factor : Fraction.Rational) (nonnegative : 0 ≤ factor) :
    List (Weighted α) → List (Weighted α)
  | [] => []
  | atom :: remaining =>
      { item := atom.item
        weight := factor * atom.weight
        nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
          nonnegative atom.nonnegative } ::
        scaleAtoms factor nonnegative remaining

/-- Scaling weights preserves the exact occurrence count.

Each original head produces one scaled head with the same payload. The
recursive tail count therefore supplies the count for the retained output. -/
theorem scaleAtoms_length {α : Type}
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (atoms : List (Weighted α)) :
    (scaleAtoms factor nonnegative atoms).length = atoms.length := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      exact congrArg Nat.succ inductionHypothesis

end

open Purelib.Data.Rat in
open Fraction.Order in
/-- Every scaled occurrence retains a payload from an exact original-list occurrence.

Structural membership identifies the scaled head or a recursively scaled
tail occurrence. The source witness belongs to that original list and retains
the original payload equality. -/
theorem mem_scaleAtoms_source {α : Type}
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (candidate : Weighted α) :
    ∀ {atoms : List (Weighted α)},
      candidate ∈ scaleAtoms factor nonnegative atoms →
        ∃ source, source ∈ atoms ∧ source.item = candidate.item
  | [], member => by nomatch member
  | atom :: remaining, member => by
      change candidate ∈ (⟨atom.item, factor * atom.weight,
          Arithmetic.mul_nonneg_direct nonnegative atom.nonnegative⟩ : Weighted α) ::
        scaleAtoms factor nonnegative remaining at member
      cases member with
      | head => exact ⟨atom, List.Mem.head remaining, rfl⟩
      | tail _ tailMember =>
          rcases mem_scaleAtoms_source factor nonnegative candidate tailMember with
            ⟨source, sourceMember, itemEqual⟩
          exact ⟨source, List.Mem.tail atom sourceMember, itemEqual⟩

open Purelib.Data.Rat
/-- Scaling every weight scales the exact total by the same factor.

The original factor and its nonnegativity witness scale each retained weight
in order. The recursive tail certificate and scalar distributivity identify
the total of those exact products. -/
theorem totalWeight_scaleAtoms {α : Type}
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (atoms : List (Weighted α)) :
    totalWeight (scaleAtoms factor nonnegative atoms) =
      factor * totalWeight atoms := by
  induction atoms with
  | nil => exact (Fraction.Field.mul_zero_direct factor).symm
  | cons atom remaining ih =>
      change factor * atom.weight + totalWeight (scaleAtoms factor nonnegative remaining) =
        factor * (atom.weight + totalWeight remaining)
      calc
        factor * atom.weight + totalWeight (scaleAtoms factor nonnegative remaining) =
            factor * atom.weight + factor * totalWeight remaining :=
          congrArg (fun tail => factor * atom.weight + tail) ih
        _ = factor * (atom.weight + totalWeight remaining) := by ring1

/-- Appending retained occurrence lists adds their exact event weights.

The Boolean test contributes the same original head weight in both scans.
Scalar associativity joins the retained recursive left total to the right total. -/
theorem eventWeight_append {α : Type} (left right : List (Weighted α))
    (event : α → Bool) :
    eventWeight (left ++ right) event =
      eventWeight left event + eventWeight right event := by
  induction left with
  | nil => exact (Fraction.Field.zero_add _).symm
  | cons atom remaining ih =>
      let contribution := match event atom.item with | true => atom.weight | false => 0
      change contribution + eventWeight (remaining ++ right) event =
        (contribution + eventWeight remaining event) + eventWeight right event
      exact (congrArg (fun tail => contribution + tail) ih).trans
        (Fraction.Field.add_assoc _ _ _).symm

/-- Appending retained occurrence lists adds their exact weighted integrals.

Both scans use the same observable at the original head payload. Scalar
associativity transports the retained recursive tail sum to the appended total. -/
theorem expectationWeight_append {α : Type}
    (left right : List (Weighted α)) (value : α → Fraction.Rational) :
    expectationWeight (left ++ right) value =
      expectationWeight left value + expectationWeight right value := by
  induction left with
  | nil => exact (Fraction.Field.zero_add _).symm
  | cons atom remaining ih =>
      change atom.weight * value atom.item + expectationWeight (remaining ++ right) value =
        (atom.weight * value atom.item + expectationWeight remaining value) +
          expectationWeight right value
      exact (congrArg (fun tail => atom.weight * value atom.item + tail) ih).trans
        (Fraction.Field.add_assoc _ _ _).symm

/-- Scaling every occurrence weight scales every event weight by the same factor.

The Boolean event reads each original payload, so a selected head contributes
the same scaled weight. Its scalar certificate and the unchanged recursive
tail establish the original factor times the original event weight. -/
theorem eventWeight_scaleAtoms {α : Type}
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (atoms : List (Weighted α)) (event : α → Bool) :
    eventWeight (scaleAtoms factor nonnegative atoms) event =
      factor * eventWeight atoms event := by
  induction atoms with
  | nil => exact (Fraction.Field.mul_zero_direct factor).symm
  | cons atom remaining ih =>
      let contribution := match event atom.item with | true => atom.weight | false => 0
      have headScale : (match event atom.item with
          | true => factor * atom.weight | false => 0) = factor * contribution := by
        dsimp only [contribution]
        cases event atom.item with
        | false => exact (Fraction.Field.mul_zero_direct factor).symm
        | true => rfl
      change (match event atom.item with | true => factor * atom.weight | false => 0) +
          eventWeight (scaleAtoms factor nonnegative remaining) event =
        factor * (contribution + eventWeight remaining event)
      calc
        (match event atom.item with | true => factor * atom.weight | false => 0) +
            eventWeight (scaleAtoms factor nonnegative remaining) event =
            factor * contribution + factor * eventWeight remaining event :=
          (congrArg (fun head => head + eventWeight (scaleAtoms factor nonnegative remaining) event)
            headScale).trans (congrArg (fun tail => factor * contribution + tail) ih)
        _ = factor * (contribution + eventWeight remaining event) := by ring1

/-- Scaling every occurrence weight scales the weighted integral by the same factor.

The scaled head and original head read the same observable payload. Scalar
associativity and distributivity transport that contribution and the retained
tail integral without changing the factor or its supplied witness. -/
theorem expectationWeight_scaleAtoms {α : Type}
    (factor : Fraction.Rational) (nonnegative : 0 ≤ factor)
    (atoms : List (Weighted α)) (value : α → Fraction.Rational) :
    expectationWeight (scaleAtoms factor nonnegative atoms) value =
      factor * expectationWeight atoms value := by
  induction atoms with
  | nil => exact (Fraction.Field.mul_zero_direct factor).symm
  | cons atom remaining ih =>
      change (factor * atom.weight) * value atom.item +
          expectationWeight (scaleAtoms factor nonnegative remaining) value =
        factor * (atom.weight * value atom.item + expectationWeight remaining value)
      calc
        (factor * atom.weight) * value atom.item +
            expectationWeight (scaleAtoms factor nonnegative remaining) value =
            (factor * atom.weight) * value atom.item + factor * expectationWeight remaining value :=
          congrArg (fun tail => (factor * atom.weight) * value atom.item + tail) ih
        _ = factor * (atom.weight * value atom.item + expectationWeight remaining value) := by ring1

end Purelib.Measure
