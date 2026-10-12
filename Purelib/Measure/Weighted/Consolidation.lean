module
meta import Lean.Elab.Command
meta import Lean.Meta.CongrTheorems
meta import Lean.Meta.Basic
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
public import Purelib.Measure.Weighted.Integral
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic

section
public section

/-!
# Constructive consolidation of finite atom tables

When equality of payloads is explicitly decidable, repeated payloads can be
merged by finite recursion and rational weight addition.  This is an
executable histogram operation; no quotient or choice of representatives is
used.
-/

namespace Purelib.Measure

/-- Decide whether the candidate payload equals the exact supplied target. -/
@[expose] def atomEvent {α : Type} [DecidableEq α] (target candidate : α) : Bool :=
  decide (candidate = target)

/-- Insert one weighted occurrence, merging its weight with the first equal payload if present.

Keep that matching payload and the remaining list unchanged. If no match occurs, append the supplied occurrence after
all original entries; every constructed weight keeps its nonnegativity proof. -/
@[expose] def insertWeighted {α : Type} [DecidableEq α]
    (atom : Weighted α) : List (Weighted α) → List (Weighted α)
  | [] => [atom]
  | current :: remaining =>
      if _ : atom.item = current.item then
        { item := current.item
          weight := atom.weight + current.weight
          nonnegative := add_nonneg atom.nonnegative current.nonnegative } ::
            remaining
      else
        current :: insertWeighted atom remaining

/-- Equality decisions agree pointwise under either supplied procedure. -/
theorem atomEvent_eq_of_decidableEq {α : Type} (first second : DecidableEq α)
    (target candidate : α) :
    @atomEvent α first target candidate = @atomEvent α second target candidate := by
  unfold atomEvent
  cases first candidate target with
  | isTrue equality =>
      exact (@decide_eq_true (candidate = target) (second candidate target) equality).symm
  | isFalse inequality =>
      exact (@decide_eq_false (candidate = target) (second candidate target) inequality).symm

/-- Equal singleton inputs retain their Boolean event under either equality procedure. -/
private theorem atomEvent_agreement {α : Type} {first : DecidableEq α}
    [second : DecidableEq α] (target target' : α) (e_target : target = target')
    (candidate candidate' : α) (e_candidate : candidate = candidate') :
    @atomEvent α first target candidate = @atomEvent α second target' candidate' := by
  cases e_target
  cases e_candidate
  exact atomEvent_eq_of_decidableEq first second target candidate

open Lean Elab Command in
run_elab do
  let name := Name.str ``atomEvent "congr_simp"
  let kinds : Array Meta.CongrArgKind := #[.fixed, .subsingletonInst, .eq, .eq]
  let .thmInfo info ← getConstInfo ``atomEvent_agreement
    | throwError "pointwise certificate is not a safe theorem"
  let operationInfo ← getConstInfo ``atomEvent
  let .forallE alpha _ operationType _ := operationInfo.type
    | throwError "equality procedure owner has no type binder"
  let .forallE procedure _ operationType _ := operationType
    | throwError "equality procedure owner has no procedure binder"
  let .forallE left _ operationType _ := operationType
    | throwError "equality procedure owner has no first input"
  let .forallE right _ _ _ := operationType
    | throwError "equality procedure owner has no second input"
  let names := #[alpha, procedure, procedure, left, left,
    Name.str .anonymous ("e_" ++ left.toString), right, right,
    Name.str .anonymous ("e_" ++ right.toString)]
  let rec retainNames (type : Expr) (index : Nat) : Expr :=
    match type with
    | .forallE original domain body mode =>
        .forallE (names[index]?.getD original) domain (retainNames body (index + 1)) mode
    | other => other
  Meta.realizeConst ``atomEvent name do
    addDecl (.thmDecl {
      name, type := retainNames info.type 0, levelParams := info.levelParams
      value := info.value
    }) (forceExpose := true)
    modifyEnv fun environment => Meta.congrKindsExt.insert environment name kinds
  let some congrThm ← Meta.mkCongrSimpForConst? ``atomEvent []
    | throwError "registered original congruence lookup failed"
  unless congrThm.proof.isConstOf name && congrThm.argKinds == kinds do
    throwError "automatic lookup changed the original public certificate"

/-- Insertion preserves every ordered weighted occurrence under either equality procedure. -/
theorem insertWeighted_eq_of_decidableEq {α : Type} (first second : DecidableEq α)
    (atom : Weighted α) (atoms : List (Weighted α)) :
    @insertWeighted α first atom atoms = @insertWeighted α second atom atoms := by
  induction atoms with
  | nil => rfl
  | cons current remaining ih =>
      cases first atom.item current.item with
      | isTrue equality =>
          simp only [-eq_self, -iff_self, insertWeighted, dif_pos equality]
          rfl
      | isFalse inequality =>
          simp only [-eq_self, -iff_self, insertWeighted, dif_neg inequality]
          exact congrArg (List.cons current) ih

/-- Insertion adds the inserted occurrence's weight to the exact original total. -/
theorem totalWeight_insertWeighted {α : Type} [DecidableEq α]
    (atom : Weighted α) : ∀ atoms : List (Weighted α),
    totalWeight (insertWeighted atom atoms) =
      atom.weight + totalWeight atoms
  | [] => by
      simp only [-eq_self, -iff_self, insertWeighted, totalWeight, add_zero]
      rfl
  | current :: remaining => by
      by_cases equal : atom.item = current.item
      · rw [insertWeighted, dif_pos equal]
        simp only [-eq_self, -iff_self,  totalWeight]
        ring1
      · rw [insertWeighted, dif_neg equal]
        simp only [-eq_self, -iff_self,  totalWeight,
          totalWeight_insertWeighted atom remaining]
        ring1

/-- Insertion adds the inserted occurrence's selected contribution to the original event weight. -/
theorem eventWeight_insertWeighted {α : Type} [DecidableEq α]
    (atom : Weighted α) (event : α → Bool) :
    ∀ atoms : List (Weighted α),
    eventWeight (insertWeighted atom atoms) event =
      (match event atom.item with
        | true => atom.weight
        | false => 0) + eventWeight atoms event
  | [] => by
      rfl
  | current :: remaining => by
      by_cases equal : atom.item = current.item
      · rw [insertWeighted, dif_pos equal]
        dsimp only [eventWeight]
        rw [equal]
        cases event current.item <;> dsimp only <;> ring1
      · rw [insertWeighted, dif_neg equal]
        dsimp only [eventWeight]
        rw [eventWeight_insertWeighted atom event remaining]
        ring1

open Purelib.Data.Rat in
/-- Insertion adds the inserted occurrence's weighted observable value to the original integral. -/
theorem expectationWeight_insertWeighted {α : Type} [DecidableEq α]
    (atom : Weighted α) (value : α → Fraction.Rational) :
    ∀ atoms : List (Weighted α),
    Distribution.expectationWeight (insertWeighted atom atoms) value =
      atom.weight * value atom.item +
        Distribution.expectationWeight atoms value
  | [] => by
      simp only [-eq_self, -iff_self, insertWeighted, Distribution.expectationWeight, add_zero]
      rfl
  | current :: remaining => by
      by_cases equal : atom.item = current.item
      · rw [insertWeighted, dif_pos equal]
        simp only [-eq_self, -iff_self,
          Distribution.expectationWeight]
        rw [equal]
        ring1
      · rw [insertWeighted, dif_neg equal]
        simp only [-eq_self, -iff_self,
          Distribution.expectationWeight,
          expectationWeight_insertWeighted atom value remaining]
        ring1

/-- Inserting one weighted occurrence increases list length by at most one. -/
theorem insertWeighted_length_le {α : Type} [DecidableEq α]
    (atom : Weighted α) : ∀ atoms : List (Weighted α),
    (insertWeighted atom atoms).length ≤ atoms.length + 1
  | [] => le_rfl
  | current :: remaining => by
      by_cases equal : atom.item = current.item
      · rw [insertWeighted, dif_pos equal]
        simp only [-eq_self, -iff_self,  List.length_cons]
        exact Nat.le_add_right _ 1
      · rw [insertWeighted, dif_neg equal]
        simp only [-eq_self, -iff_self,  List.length_cons]
        exact Nat.succ_le_succ (insertWeighted_length_le atom remaining)

/-- Require the supplied payload to differ from every payload in the retained weighted list. -/
@[expose] def PayloadAbsent {α : Type} (item : α) : List (Weighted α) → Prop
  | [] => True
  | atom :: remaining =>
      item ≠ atom.item ∧ PayloadAbsent item remaining

/-- Require every retained head payload to be absent from its exact tail recursively. -/
@[expose] def NoRepeatedPayloads {α : Type} : List (Weighted α) → Prop
  | [] => True
  | atom :: remaining =>
      PayloadAbsent atom.item remaining ∧ NoRepeatedPayloads remaining

/-- A payload remains absent after inserting a different weighted payload. -/
theorem payloadAbsent_insertWeighted {α : Type} [DecidableEq α]
    (item : α) (atom : Weighted α) (different : item ≠ atom.item) :
    ∀ atoms : List (Weighted α), PayloadAbsent item atoms →
      PayloadAbsent item (insertWeighted atom atoms)
  | [], absent => by
      simp only [-eq_self, -iff_self, insertWeighted, PayloadAbsent]
      exact ⟨different, trivial⟩
  | current :: remaining, absent => by
      rcases absent with ⟨currentDifferent, remainingAbsent⟩
      by_cases equal : atom.item = current.item
      · rw [insertWeighted, dif_pos equal]
        simp only [-eq_self, -iff_self,  PayloadAbsent]
        exact ⟨currentDifferent, remainingAbsent⟩
      · rw [insertWeighted, dif_neg equal]
        simp only [-eq_self, -iff_self,  PayloadAbsent]
        exact ⟨currentDifferent,
          payloadAbsent_insertWeighted item atom different remaining
            remainingAbsent⟩

/-- Insertion preserves absence of repeated payloads in the retained weighted list. -/
theorem insertWeighted_noRepeatedPayloads {α : Type} [DecidableEq α]
    (atom : Weighted α) : ∀ atoms : List (Weighted α),
    NoRepeatedPayloads atoms →
      NoRepeatedPayloads (insertWeighted atom atoms)
  | [], noRepeated => by
      simp only [-eq_self, -iff_self, insertWeighted, NoRepeatedPayloads, PayloadAbsent]
      trivial
  | current :: remaining, noRepeated => by
      rcases noRepeated with ⟨currentAbsent, remainingNoRepeated⟩
      by_cases equal : atom.item = current.item
      · rw [insertWeighted, dif_pos equal]
        simp only [-eq_self, -iff_self,  NoRepeatedPayloads]
        exact ⟨currentAbsent, remainingNoRepeated⟩
      · rw [insertWeighted, dif_neg equal]
        simp only [-eq_self, -iff_self,  NoRepeatedPayloads]
        constructor
        · exact payloadAbsent_insertWeighted current.item atom
            (fun reverse => equal reverse.symm) remaining currentAbsent
        · exact insertWeighted_noRepeatedPayloads atom remaining
            remainingNoRepeated

/-- Merge equal payload weights by recursively consolidating the tail and inserting the original head.

The exact recursive order determines the retained representative occurrence. Total, event and integral readbacks are
preserved without constructing a new carrier enumeration. -/
@[expose] def consolidateAtoms {α : Type} [DecidableEq α] :
    List (Weighted α) → List (Weighted α)
  | [] => []
  | atom :: remaining => insertWeighted atom (consolidateAtoms remaining)

/-- Consolidation retains the same ordered representatives under either equality procedure. -/
theorem consolidateAtoms_eq_of_decidableEq {α : Type} (first second : DecidableEq α)
    (atoms : List (Weighted α)) :
    @consolidateAtoms α first atoms = @consolidateAtoms α second atoms := by
  induction atoms with
  | nil => rfl
  | cons atom remaining ih =>
      change @insertWeighted α first atom (@consolidateAtoms α first remaining) =
        @insertWeighted α second atom (@consolidateAtoms α second remaining)
      exact (congrArg (@insertWeighted α first atom) ih).trans
        (insertWeighted_eq_of_decidableEq first second atom _)

/-- Consolidation preserves the exact total weight. -/
theorem totalWeight_consolidateAtoms {α : Type} [DecidableEq α] :
    ∀ atoms : List (Weighted α),
      totalWeight (consolidateAtoms atoms) = totalWeight atoms
  | [] => rfl
  | atom :: remaining => by
      rw [consolidateAtoms, totalWeight_insertWeighted,
        totalWeight_consolidateAtoms remaining]
      rfl

/-- Consolidation preserves every Boolean event's exact weight. -/
theorem eventWeight_consolidateAtoms {α : Type} [DecidableEq α]
    (event : α → Bool) : ∀ atoms : List (Weighted α),
    eventWeight (consolidateAtoms atoms) event = eventWeight atoms event
  | [] => rfl
  | atom :: remaining => by
      rw [consolidateAtoms, eventWeight_insertWeighted,
        eventWeight_consolidateAtoms event remaining]
      rfl

open Purelib.Data.Rat in
/-- Consolidation preserves every rational observable's exact weighted integral. -/
theorem expectationWeight_consolidateAtoms {α : Type} [DecidableEq α]
    (value : α → Fraction.Rational) : ∀ atoms : List (Weighted α),
    Distribution.expectationWeight (consolidateAtoms atoms) value =
      Distribution.expectationWeight atoms value
  | [] => rfl
  | atom :: remaining => by
      rw [consolidateAtoms, expectationWeight_insertWeighted,
        expectationWeight_consolidateAtoms value remaining]
      rfl

/-- The consolidated list has at most the original number of retained occurrences. -/
theorem consolidateAtoms_length_le {α : Type} [DecidableEq α] :
    ∀ atoms : List (Weighted α),
      (consolidateAtoms atoms).length ≤ atoms.length
  | [] => le_rfl
  | atom :: remaining => by
      rw [consolidateAtoms]
      exact (insertWeighted_length_le atom
        (consolidateAtoms remaining)).trans (by
          simpa only [-eq_self, -iff_self, List.length_cons, Nat.succ_eq_add_one] using
            Nat.add_le_add_right
              (consolidateAtoms_length_le remaining) 1)

/-- Consolidation produces a weighted list with no repeated payloads. -/
theorem consolidateAtoms_noRepeatedPayloads
    {α : Type} [DecidableEq α] :
    ∀ atoms : List (Weighted α),
      NoRepeatedPayloads (consolidateAtoms atoms)
  | [] => trivial
  | atom :: remaining => by
      rw [consolidateAtoms]
      exact insertWeighted_noRepeatedPayloads atom
        (consolidateAtoms remaining)
        (consolidateAtoms_noRepeatedPayloads remaining)

namespace Distribution
end Distribution

end Purelib.Measure

end
