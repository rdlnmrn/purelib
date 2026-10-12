module
meta import Lean.Elab.Command
meta import Lean.Meta.CongrTheorems
meta import Lean.Meta.Basic
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Density.Witness
public import Purelib.Measure.Content.Equivalence
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Operations
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Consolidation
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Integral
public import Purelib.Measure.Weighted.Payload
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
/-!
# Finite Radon--Nikodym existence

For arbitrary displayed finite contents with decidable payload equality, the
union of their payload tables can be consolidated into a duplicate-free key
list.  Assigning each key its exact singleton mass gives aligned source and
target rows.  Absolute continuity supplies the rowwise zero implication, so
the quotient-density algorithm yields a Radon--Nikodym witness.

The proof below includes the finite histogram reconstruction lemma: summing
singleton masses over any duplicate-free key list covering a displayed atom
table recovers every rational integral.
-/

public section

namespace Purelib.Measure
namespace Content

/-- Require every content occurrence's payload to have a representative in the exact retained key list. -/
@[expose] def PayloadsCovered {α : Type} (content : Content α)
    (keys : List (Weighted α)) : Prop :=
  ∀ atom, atom ∈ content.atoms → PayloadPresent atom.item keys

section
open Purelib.Data.Rat
/-- Sum each retained key's singleton content mass times the observable at that key's exact payload.

The key list determines the finite order and multiplicity. Its stored weights are not used; each coefficient is measured
from the original content at that same payload. -/
@[expose] def atomMassSum {α : Type} [DecidableEq α]
    (content : Content α) :
    List (Weighted α) → (α → Fraction.Rational) → Fraction.Rational
  | [], _ => 0
  | key :: remaining, value =>
      content.measure (atomEvent key.item) * value key.item +
        content.atomMassSum remaining value

/-- The same retained key list has the same singleton-mass sum under either equality procedure. -/
theorem atomMassSum_eq_of_decidableEq {α : Type} (first second : DecidableEq α)
    (content : Content α) (keys : List (Weighted α)) (value : α → Fraction.Rational) :
    @atomMassSum α first content keys value = @atomMassSum α second content keys value := by
  induction keys with
  | nil => rfl
  | cons key remaining ih =>
      change content.measure (@atomEvent α first key.item) * value key.item +
          @atomMassSum α first content remaining value =
        content.measure (@atomEvent α second key.item) * value key.item +
          @atomMassSum α second content remaining value
      have mass := content.measure_congr (@atomEvent α first key.item)
        (@atomEvent α second key.item)
        (fun candidate => atomEvent_eq_of_decidableEq first second key.item candidate)
      exact congrArg₂ (fun current tail => current + tail)
        (congrArg (fun current => current * value key.item) mass) ih

/-- Equal original content, keys and observable retain the singleton-mass sum under either equality procedure. -/
private theorem atomMassSum_agreement {α : Type} {first : DecidableEq α}
    [second : DecidableEq α] (content content' : Content α) (e_content : content = content')
    (keys keys' : List (Weighted α)) (e_keys : keys = keys')
    (value value' : α → Fraction.Rational) (e_value : value = value') :
    @atomMassSum α first content keys value = @atomMassSum α second content' keys' value' := by
  cases e_content
  cases e_keys
  cases e_value
  exact atomMassSum_eq_of_decidableEq first second content keys value

end

open Lean Elab Command in
run_elab do
  let name := Name.str ``atomMassSum "congr_simp"
  let kinds : Array Meta.CongrArgKind := #[.fixed, .subsingletonInst, .eq, .eq, .eq]
  let .thmInfo info ← getConstInfo ``atomMassSum_agreement
    | throwError "pointwise certificate is not a safe theorem"
  let .thmInfo invariant ← getConstInfo ``atomMassSum_eq_of_decidableEq
    | throwError "equality-procedure invariance is not a safe theorem"
  unless invariant.levelParams.isEmpty do
    throwError "mass sum invariance unexpectedly has universe parameters"
  let proofValue := info.value.replace fun expression =>
    if expression.isConstOf ``atomMassSum_eq_of_decidableEq then some invariant.value else none
  let operationInfo ← getConstInfo ``atomMassSum
  let .forallE alpha _ operationType _ := operationInfo.type
    | throwError "mass sum owner has no type binder"
  let .forallE procedure _ operationType _ := operationType
    | throwError "mass sum owner has no equality procedure"
  let .forallE content _ operationType _ := operationType
    | throwError "mass sum owner has no content binder"
  let .forallE keys _ operationType _ := operationType
    | throwError "mass sum owner has no retained key list"
  let .forallE value _ _ _ := operationType
    | throwError "mass sum owner has no observable binder"
  let names := #[alpha, procedure, procedure, content, content, content.appendBefore "e_",
    keys, keys, keys.appendBefore "e_", value, value, value.appendBefore "e_"]
  let rec retainNames (type : Expr) (index : Nat) : Expr :=
    match type with
    | .forallE original domain body mode =>
        .forallE (names[index]?.getD original) domain (retainNames body (index + 1)) mode
    | other => other
  Meta.realizeConst ``atomMassSum name do
    addDecl (.thmDecl {
      name, type := retainNames info.type 0, levelParams := info.levelParams
      value := proofValue
    }) (forceExpose := true)
    modifyEnv fun environment => Meta.congrKindsExt.insert environment name kinds
  let some congrThm ← Meta.mkCongrSimpForConst? ``atomMassSum []
    | throwError "registered original mass sum congruence lookup failed"
  unless congrThm.proof.isConstOf name && congrThm.argKinds == kinds do
    throwError "automatic lookup changed the original public mass sum certificate"

section
open Purelib.Data.Rat
/-- Equal singleton masses on the retained keys give equal key-indexed weighted sums. -/
theorem atomMassSum_congr {α : Type} [DecidableEq α]
    (left right : Content α) (value : α → Fraction.Rational) :
    ∀ keys : List (Weighted α),
      (∀ key, key ∈ keys →
        left.measure (atomEvent key.item) =
          right.measure (atomEvent key.item)) →
      left.atomMassSum keys value = right.atomMassSum keys value
  | [], equal => rfl
  | key :: remaining, equal => by
      simp only [-eq_self, -iff_self, atomMassSum]
      rw [equal key List.mem_cons_self,
        atomMassSum_congr left right value remaining
          (fun candidate member =>
            equal candidate (List.mem_cons_of_mem key member))]

/-- Restricting content to one payload makes every integral its singleton mass times the value there. -/
private theorem restrict_singleton_integral {α : Type} [DecidableEq α]
    (content : Content α) (item : α)
    (value : α → Fraction.Rational) :
    (content.restrict (atomEvent item)).integral value =
      content.measure (atomEvent item) * value item := by
  rw [content.restrict_integral]
  calc
    content.integral (fun candidate =>
          Distribution.indicator (atomEvent item) candidate *
            value candidate) =
        content.integral (fun candidate =>
          value item * Distribution.indicator (atomEvent item) candidate) :=
      content.integral_congr _ _ (fun candidate => by
        cases selected : atomEvent item candidate
        · simp only [-eq_self, -iff_self, Distribution.indicator, selected, mul_zero, zero_mul]
          rfl
        · have same : candidate = item := by
            unfold atomEvent at selected
            exact of_decide_eq_true selected
          rw [same]
          ring1)
    _ = value item *
          content.integral (Distribution.indicator (atomEvent item)) :=
      content.integral_scale _ _
    _ = value item * content.measure (atomEvent item) :=
      congrArg (fun mass => value item * mass)
        (content.integral_indicator (atomEvent item))
    _ = content.measure (atomEvent item) * value item := by ring1

/-- Restriction by an event and its complement partitions every original content integral. -/
private theorem restrict_add_complement_integral {α : Type}
    (content : Content α) (event : α → Bool)
    (value : α → Fraction.Rational) :
    (content.restrict event).integral value +
        (content.restrict (complementEvent event)).integral value =
      content.integral value := by
  rw [content.restrict_integral, content.restrict_integral]
  calc
    content.integral (fun item =>
          Distribution.indicator event item * value item) +
        content.integral (fun item =>
          Distribution.indicator (complementEvent event) item * value item) =
      content.integral (fun item =>
        Distribution.indicator event item * value item +
          Distribution.indicator (complementEvent event) item * value item) :=
      (content.integral_add _ _).symm
    _ = content.integral value :=
      content.integral_congr _ _ (fun item => by
        cases selected : event item <;>
          simp only [-eq_self, -iff_self, Distribution.indicator, complementEvent, selected,
            Bool.not_false, Bool.not_true, zero_mul, one_mul,
            add_zero, zero_add]
        all_goals rfl)

end

/-- Removing a different payload leaves the retained payload's singleton content mass unchanged. -/
private theorem restrict_complement_singleton_mass {α : Type}
    [DecidableEq α] (content : Content α)
    (removed kept : α) (different : kept ≠ removed) :
    (content.restrict (complementEvent (atomEvent removed))).measure
        (atomEvent kept) = content.measure (atomEvent kept) := by
  rw [content.restrict_measure]
  exact content.measure_congr _ _ (fun candidate => by
    cases selected : atomEvent kept candidate
    · simp only [-eq_self, -iff_self, intersectionEvent, selected, Bool.false_and]
      rfl
    · have same : candidate = kept := by
        unfold atomEvent at selected
        exact of_decide_eq_true selected
      have notRemoved : atomEvent removed candidate = false := by
        unfold atomEvent
        rw [same]
        exact decide_eq_false different
      simp only [-eq_self, -iff_self, intersectionEvent, complementEvent, selected, notRemoved,
        Bool.not_false, Bool.and_true]
      rfl)

open Purelib in
open Purelib.Data.Rat in
/-- Distinct retained keys covering the original content payloads compute its exact integral from singleton masses.

The finite proof removes the current key's singleton event and continues over the same remaining keys. Coverage and
no-repetition ensure that every original occurrence contributes exactly once. -/
theorem atomMassSum_eq_integral {α : Type} [DecidableEq α]
    (value : α → Fraction.Rational) :
    ∀ (keys : List (Weighted α)) (content : Content α),
      NoRepeatedPayloads keys → content.PayloadsCovered keys →
        content.atomMassSum keys value = content.integral value
  | [], content, noRepeated, covered => by
      cases atomsSame : content.atoms with
      | nil =>
          simp only [-eq_self, -iff_self, atomMassSum, Content.integral, atomsSame,
            Distribution.expectationWeight]
          rfl
      | cons atom remaining =>
          have present := covered atom (atomsSame ▸ List.mem_cons_self)
          rcases present with ⟨candidate, member, equal⟩
          cases member
  | key :: remaining, content, noRepeated, covered => by
      rcases noRepeated with ⟨keyAbsent, tailNoRepeated⟩
      let residual :=
        content.restrict (complementEvent (atomEvent key.item))
      have residualCovered : residual.PayloadsCovered remaining := by
        intro atom member
        have originalMember : atom ∈ content.atoms :=
          Measure.mem_restrictAtoms_original
            (complementEvent (atomEvent key.item)) member
        have complementSelected :
            complementEvent (atomEvent key.item) atom.item = true :=
          Measure.mem_restrictAtoms_selected
            (complementEvent (atomEvent key.item)) member
        have different : atom.item ≠ key.item := by
          intro same
          have selectedSelf : atomEvent key.item atom.item = true := by
            unfold atomEvent
            exact decide_eq_true same
          unfold complementEvent at complementSelected
          rw [selectedSelf] at complementSelected
          exact Bool.noConfusion complementSelected
        exact Measure.payloadPresent_tail_of_cons_of_ne atom.item key remaining
          different (covered atom originalMember)
      have tailMassEqual : content.atomMassSum remaining value =
          residual.atomMassSum remaining value := by
        apply atomMassSum_congr content residual value remaining
        intro candidate member
        have different : candidate.item ≠ key.item := by
          intro same
          exact (Measure.payloadAbsent_ne_of_mem key.item keyAbsent member) same.symm
        exact (restrict_complement_singleton_mass content key.item
          candidate.item different).symm
      calc
        content.atomMassSum (key :: remaining) value =
            content.measure (atomEvent key.item) * value key.item +
              content.atomMassSum remaining value := rfl
        _ = (content.restrict (atomEvent key.item)).integral value +
              residual.atomMassSum remaining value := by
          rw [restrict_singleton_integral, tailMassEqual]
        _ = (content.restrict (atomEvent key.item)).integral value +
              residual.integral value := by
          rw [atomMassSum_eq_integral value remaining residual
            tailNoRepeated residualCovered]
        _ = content.integral value :=
          restrict_add_complement_integral content (atomEvent key.item) value

/-- Build content on the exact retained keys using original singleton masses as their nonnegative weights. -/
@[expose] def atomMassContent {α : Type} [DecidableEq α]
    (content : Content α) (keys : List (Weighted α)) :
    Content α where
  atoms := keys.map fun key =>
    { item := key.item
      weight := content.measure (atomEvent key.item)
      nonnegative := content.measure_nonneg (atomEvent key.item) }

open Purelib.Data.Rat in
/-- Integrating the key-based singleton-mass content equals its exact key-indexed mass sum. -/
theorem atomMassContent_integral {α : Type} [DecidableEq α]
    (content : Content α) (keys : List (Weighted α))
    (value : α → Fraction.Rational) :
    (content.atomMassContent keys).integral value =
      content.atomMassSum keys value := by
  unfold atomMassContent Content.integral
  induction keys with
  | nil => rfl
  | cons key remaining inductionHypothesis =>
      simp only [-eq_self, -iff_self, List.map_cons, Distribution.expectationWeight, atomMassSum,
        inductionHypothesis]
      rfl

/-- Distinct retained keys covering all original payloads give singleton-mass content evaluation equivalent to the
original. -/
theorem atomMassContent_evaluationEquivalent {α : Type} [DecidableEq α]
    (content : Content α) (keys : List (Weighted α))
    (noRepeated : NoRepeatedPayloads keys)
    (covered : content.PayloadsCovered keys) :
    EvaluationEquivalent (content.atomMassContent keys) content := by
  apply EvaluationEquivalent.of_integral_eq
  intro value
  rw [content.atomMassContent_integral keys value]
  exact content.atomMassSum_eq_integral value keys noRepeated covered

/-- Consolidate the exact source list followed by the target list into shared finite payload keys. -/
@[expose] def radonNikodymKeys {α : Type} [DecidableEq α]
    (source target : Content α) : List (Weighted α) :=
  consolidateAtoms (source.atoms ++ target.atoms)

/-- The shared source-target key list has no repeated payloads. -/
theorem radonNikodymKeys_noRepeated {α : Type} [DecidableEq α]
    (source target : Content α) :
    NoRepeatedPayloads (source.radonNikodymKeys target) :=
  consolidateAtoms_noRepeatedPayloads _

section
open Purelib
/-- The shared key list covers every exact source occurrence's payload. -/
theorem payloadsCovered_radonNikodymKeys_left {α : Type}
    [DecidableEq α] (source target : Content α) :
    source.PayloadsCovered (source.radonNikodymKeys target) := by
  intro atom member
  exact Measure.payloadPresent_consolidateAtoms_of_mem
    (source.atoms ++ target.atoms) atom
    (List.mem_append_left target.atoms member)

/-- The shared key list covers every exact target occurrence's payload. -/
theorem payloadsCovered_radonNikodymKeys_right {α : Type}
    [DecidableEq α] (source target : Content α) :
    target.PayloadsCovered (source.radonNikodymKeys target) := by
  intro atom member
  exact Measure.payloadPresent_consolidateAtoms_of_mem
    (source.atoms ++ target.atoms) atom
    (List.mem_append_right source.atoms member)

end

namespace EvaluationEquivalent

/-- Equality of all singleton masses gives evaluation equivalence of the original finite contents. -/
theorem of_atom_measure_eq {α : Type} [DecidableEq α]
    {left right : Content α}
    (atomEqual : ∀ item : α,
      left.measure (atomEvent item) = right.measure (atomEvent item)) :
    EvaluationEquivalent left right := by
  apply EvaluationEquivalent.of_integral_eq
  intro value
  let keys := left.radonNikodymKeys right
  calc
    left.integral value = left.atomMassSum keys value :=
      (left.atomMassSum_eq_integral value keys
        (left.radonNikodymKeys_noRepeated right)
        (left.payloadsCovered_radonNikodymKeys_left right)).symm
    _ = right.atomMassSum keys value := by
      apply atomMassSum_congr left right value keys
      intro key member
      exact atomEqual key.item
    _ = right.integral value :=
      right.atomMassSum_eq_integral value keys
        (left.radonNikodymKeys_noRepeated right)
        (left.payloadsCovered_radonNikodymKeys_right right)

/-- Evaluation-equivalent contents have equal mass at every singleton payload. -/
theorem atom_measure_eq {α : Type} [DecidableEq α]
    {left right : Content α}
    (equivalent : EvaluationEquivalent left right) (item : α) :
    left.measure (atomEvent item) = right.measure (atomEvent item) :=
  equivalent.measure_eq (atomEvent item)

end EvaluationEquivalent

/-- Two finite contents are evaluation equivalent exactly when all singleton payload masses agree. -/
theorem evaluationEquivalent_iff_atom_measure_eq {α : Type}
    [DecidableEq α] (left right : Content α) :
    EvaluationEquivalent left right ↔
      ∀ item : α,
        left.measure (atomEvent item) = right.measure (atomEvent item) :=
  ⟨fun equivalent item => equivalent.atom_measure_eq item,
    EvaluationEquivalent.of_atom_measure_eq⟩

end Content

end Purelib.Measure

end
