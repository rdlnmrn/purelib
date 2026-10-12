module
meta import Lean.Elab.Command
meta import Lean.Meta.CongrTheorems
meta import Lean.Meta.Basic
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Content.Singularity
import Purelib.Measure.Weighted.Event
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Content.AbsoluteContinuity.Basic
import Purelib.Measure.Content.Basic
import Purelib.Measure.Content.Operations
import Purelib.Measure.Weighted.AlmostEverywhere
public import Purelib.Measure.Weighted.Consolidation
import Purelib.Data.Rat.Fraction.Arithmetic

/-!
# Finite constructive Lebesgue decomposition

Exact rational equality decides whether a payload has positive source mass.
That executable support event splits any target content into a part absolutely
continuous with respect to the source and a mutually singular remainder.
The decomposition is a finite partition of the displayed target table.
-/

@[expose] public section

namespace Purelib.Measure

namespace Content

/-- Select payloads with nonzero singleton mass in the exact retained finite content. -/
def supportEvent {α : Type} [DecidableEq α]
    (content : Content α) : α → Bool :=
  fun item => if content.measure (atomEvent item) = 0 then false else true

/-- Source support agrees at each item under either supplied equality procedure. -/
theorem supportEvent_eq_of_decidableEq {α : Type}
    (first second : DecidableEq α) (content : Content α) (item : α) :
    @supportEvent α first content item = @supportEvent α second content item := by
  have singletonEqual :
      content.measure (@atomEvent α first item) =
        content.measure (@atomEvent α second item) := by
    apply content.measure_congr
    intro candidate
    exact atomEvent_eq_of_decidableEq first second item candidate
  unfold supportEvent
  rewrite [singletonEqual]
  rfl

/-- Equal source contents and items retain the same support decision. -/
private theorem supportEvent_agreement {α : Type} {first : DecidableEq α}
    [second : DecidableEq α] (content content' : Content α)
    (e_content : content = content') (item item' : α) (e_item : item = item') :
    @supportEvent α first content item = @supportEvent α second content' item' := by
  cases e_content
  cases e_item
  exact supportEvent_eq_of_decidableEq first second content item

open Lean Elab Command in
run_elab do
  let name := Name.str ``supportEvent "congr_simp"
  let kinds : Array Meta.CongrArgKind := #[.fixed, .subsingletonInst, .eq, .eq]
  let .thmInfo info ← getConstInfo ``supportEvent_agreement
    | throwError "pointwise source-support certificate is not a safe theorem"
  let operationInfo ← getConstInfo ``supportEvent
  let .forallE alpha _ operationType _ := operationInfo.type
    | throwError "source-support owner has no type binder"
  let .forallE procedure _ operationType _ := operationType
    | throwError "source-support owner has no equality procedure"
  let .forallE content _ operationType _ := operationType
    | throwError "source-support owner has no content binder"
  let .forallE item _ _ _ := operationType
    | throwError "source-support owner has no item binder"
  let names := #[alpha, procedure, procedure, content, content,
    Name.str .anonymous ("e_" ++ content.toString), item, item,
    item.replacePrefix (`a) (`e_a)]
  let rec retainNames (type : Expr) (index : Nat) : Expr :=
    match type with
    | .forallE original domain body mode =>
        .forallE (names[index]?.getD original) domain (retainNames body (index + 1)) mode
    | other => other
  Meta.realizeConst ``supportEvent name do
    addDecl (.thmDecl {
      name, type := retainNames info.type 0, levelParams := info.levelParams
      value := info.value
    }) (forceExpose := true)
    modifyEnv fun environment => Meta.congrKindsExt.insert environment name kinds
  let some congrThm ← Meta.mkCongrSimpForConst? ``supportEvent []
    | throwError "registered original source-support congruence lookup failed"
  unless congrThm.proof.isConstOf name && congrThm.argKinds == kinds do
    throwError "automatic lookup changed the source-support certificate"

/-- The support event rejects a payload exactly when its original singleton mass is zero. -/
theorem supportEvent_eq_false_iff {α : Type} [DecidableEq α]
    (content : Content α) (item : α) :
    content.supportEvent item = false ↔
      content.measure (atomEvent item) = 0 := by
  unfold supportEvent
  by_cases zero : content.measure (atomEvent item) = 0
  · rw [if_pos zero]
    exact ⟨fun _ => zero, fun _ => rfl⟩
  · rw [if_neg zero]
    constructor
    · intro impossible
      nomatch impossible
    · intro equality
      exact (zero equality).elim

/-- The support event selects a payload exactly when its original singleton mass is nonzero. -/
theorem supportEvent_eq_true_iff {α : Type} [DecidableEq α]
    (content : Content α) (item : α) :
    content.supportEvent item = true ↔
      content.measure (atomEvent item) ≠ 0 := by
  unfold supportEvent
  by_cases zero : content.measure (atomEvent item) = 0
  · rw [if_pos zero]
    constructor
    · intro impossible
      nomatch impossible
    · intro nonzero
      exact (nonzero zero).elim
  · rw [if_neg zero]
    exact ⟨fun _ => zero, fun _ => rfl⟩

section
open Purelib.Data.Rat
/-- The complement of the exact singleton-mass support has zero content mass. -/
theorem measure_complement_supportEvent_eq_zero {α : Type}
    [DecidableEq α] (content : Content α) :
    content.measure (complementEvent content.supportEvent) = 0 := by
  have equal : EqualOffZeroWeightOn content.atoms
      (complementEvent content.supportEvent) (fun _ => false) := by
    intro atom member
    by_cases singletonZero :
        content.measure (atomEvent atom.item) = 0
    · apply Or.inl
      have selected : atomEvent atom.item atom.item = true := by
        change decide (atom.item = atom.item) = true
        exact decide_eq_true rfl
      have bounded := atom_weight_le_eventWeight_of_mem member selected
      change atom.weight ≤ content.measure (atomEvent atom.item) at bounded
      rw [singletonZero] at bounded
      exact Fraction.Order.Basic.Compatibility.le_antisymm
        atom.weight 0 bounded atom.nonnegative
    · apply Or.inr
      unfold complementEvent supportEvent
      rw [if_neg singletonZero]
      rfl
  calc
    content.measure (complementEvent content.supportEvent) =
        content.measure (fun _ => false) :=
      eventWeight_congr_off_zero content.atoms
        (complementEvent content.supportEvent) (fun _ => false) equal
    _ = 0 := content.measure_empty

/-- Splitting an event by another event and its complement preserves its original total measurement. -/
theorem measure_intersection_add_complement {α : Type}
    (content : Content α) (event split : α → Bool) :
    content.measure (intersectionEvent event split) +
        content.measure
          (intersectionEvent event (complementEvent split)) =
      content.measure event := by
  unfold measure
  induction content.atoms with
  | nil =>
      change (0 : Fraction.Rational) + 0 = 0
      ring1
  | cons atom remaining inductionHypothesis =>
      cases eventSelected : event atom.item <;>
        cases splitSelected : split atom.item <;>
        simp only [eventWeight, intersectionEvent, complementEvent,
          eventSelected, splitSelected, Bool.false_and, Bool.true_and,
          Bool.not_false, Bool.not_true, zero_add] <;>
        rw [← inductionHypothesis] <;>
        ring1

end

/-- Restrict the exact target content to payloads with nonzero singleton mass in the original source. -/
def lebesgueRegularPart {α : Type} [DecidableEq α]
    (target source : Content α) : Content α :=
  target.restrict source.supportEvent

/-- Restrict the exact target content to payloads with zero singleton mass in the original source. -/
def lebesgueSingularPart {α : Type} [DecidableEq α]
    (target source : Content α) : Content α :=
  target.restrict (complementEvent source.supportEvent)

open Purelib.Data.Rat in
/-- The retained target restriction to source support is absolutely continuous with respect to that original source. -/
theorem lebesgueRegularPart_absolutelyContinuous {α : Type}
    [DecidableEq α] (target source : Content α) :
    (target.lebesgueRegularPart source).AbsolutelyContinuous source := by
  intro event eventZero
  rw [lebesgueRegularPart, target.restrict_measure]
  calc
    target.measure (intersectionEvent event source.supportEvent) =
        target.measure (fun _ => false) := by
      apply target.measure_congr
      intro item
      cases selected : event item
      · simp only [intersectionEvent, selected, Bool.false_and,
          -eq_self, -iff_self]
        rfl
      · have singletonLe : source.measure (atomEvent item) ≤
            source.measure event := by
          apply source.mono
          intro atom member atomSelected
          have same : atom.item = item := by
            unfold atomEvent at atomSelected
            exact of_decide_eq_true atomSelected
          exact same.symm ▸ selected
        have singletonZero : source.measure (atomEvent item) = 0 :=
          Fraction.Order.Basic.Compatibility.le_antisymm _ _
            (eventZero ▸ singletonLe) (source.measure_nonneg _)
        unfold intersectionEvent supportEvent
        rw [selected, if_pos singletonZero]
        rfl
    _ = 0 := target.measure_empty

/-- The original source is singular to the retained target restriction outside source support. -/
def lebesgueSingularPart_mutuallySingular {α : Type}
    [DecidableEq α] (target source : Content α) :
    MutuallySingular source (target.lebesgueSingularPart source) where
  separator := source.supportEvent
  left_outside_zero := source.measure_complement_supportEvent_eq_zero
  right_inside_zero := by
    rw [lebesgueSingularPart, target.restrict_measure]
    calc
      target.measure (intersectionEvent source.supportEvent
            (complementEvent source.supportEvent)) =
          target.measure (fun _ => false) := by
        apply target.measure_congr
        intro item
        cases selected : source.supportEvent item <;>
          unfold intersectionEvent complementEvent <;>
          rw [selected] <;> rfl
      _ = 0 := target.measure_empty

/-- Every target event measurement splits into its exact source-support and source-null restriction measurements. -/
theorem measure_eq_lebesgueRegularPart_add_lebesgueSingularPart
    {α : Type} [DecidableEq α] (target source : Content α)
    (event : α → Bool) :
    target.measure event =
        (target.lebesgueRegularPart source).measure event +
      (target.lebesgueSingularPart source).measure event := by
  rw [lebesgueRegularPart, lebesgueSingularPart,
    target.restrict_measure, target.restrict_measure]
  exact (target.measure_intersection_add_complement
    event source.supportEvent).symm

set_option genInjectivity false in
/-- Retain regular and singular contents decomposing all measurements of the exact target relative to the original
source.

The regular part is absolutely continuous with respect to the source; a retained separator certifies singularity of the
other part to that same source. -/
structure LebesgueDecomposition {α : Type}
    (target source : Content α) where
  /-- The retained part absolutely continuous with respect to the original source. -/ regular : Content α
  /-- The retained part separated from the original source by a certified Boolean event. -/ singular : Content α
  /-- Every original target event mass is the sum of its two retained part measurements. -/ measure_eq : ∀ event : α →
    Bool,
    target.measure event = regular.measure event + singular.measure event
  /-- The retained regular part gives zero mass to every original source-null event. -/ regular_absolutelyContinuous :
    regular.AbsolutelyContinuous source
  /-- A retained separator certifies singularity of the original source and exact singular part. -/
    source_mutuallySingular_singular : MutuallySingular source singular

constructive_injectivity LebesgueDecomposition

/-- Construct the finite decomposition by restricting the exact target to source singleton support and its complement.

Both parts retain original target occurrences and their weights. The source support supplies the original regularity and
separator certificates. -/
def lebesgueDecomposition {α : Type} [DecidableEq α]
    (target source : Content α) :
    LebesgueDecomposition target source where
  regular := target.lebesgueRegularPart source
  singular := target.lebesgueSingularPart source
  measure_eq := target.measure_eq_lebesgueRegularPart_add_lebesgueSingularPart
    source
  regular_absolutelyContinuous :=
    target.lebesgueRegularPart_absolutelyContinuous source
  source_mutuallySingular_singular :=
    target.lebesgueSingularPart_mutuallySingular source

end Content

end Purelib.Measure
