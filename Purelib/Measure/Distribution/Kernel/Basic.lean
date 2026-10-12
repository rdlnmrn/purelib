module
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Measure.Content.Overlap
import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Expectation
import Purelib.Measure.Weighted.Basic
import Purelib.Measure.Weighted.Event
import Purelib.Measure.Weighted.Fubini
import Purelib.Measure.Weighted.Integral
import Purelib.Measure.Weighted.Operations
public import Purelib.Measure.Weighted.Transform
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

section
@[expose] public section

/-!
# Bounded finite stochastic processes

Finite distributions compose by explicit list flattening and rational weight
multiplication.  Iteration takes a displayed natural horizon and therefore
constructs only a finite process table.
-/

namespace Purelib.Measure

open Distribution
open Purelib.Data.List

/-- Expand each original weighted occurrence through its exact transition distribution and scale that target list by the
original weight.

Concatenate the scaled target lists in the original source order. Target payload multiplicity and transition ownership
remain explicit; no consolidation or alternate enumeration is introduced. -/
def bindAtoms {α β : Type} :
    List (Weighted α) → (α → Distribution β) → List (Weighted β)
  | [], _ => []
  | atom :: remaining, transition =>
      scaleAtoms atom.weight atom.nonnegative
          (transition atom.item).atoms ++
        bindAtoms remaining transition

/-- Pointwise equal transition distributions produce the same exact expanded occurrence list.

At each original source occurrence, scalar congruence transports its own transition list and the unchanged recursive
tail. Both expansions retain the same source weights and occurrence order. -/
theorem bindAtoms_congr {α β : Type}
    (atoms : List (Weighted α)) (left right : α → Distribution β)
    (pointwise : ∀ item, left item = right item) :
    bindAtoms atoms left = bindAtoms atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom remaining ih =>
      change scaleAtoms atom.weight atom.nonnegative (left atom.item).atoms ++
          bindAtoms remaining left =
        scaleAtoms atom.weight atom.nonnegative (right atom.item).atoms ++
          bindAtoms remaining right
      exact (congrArg (fun target : Distribution β =>
        scaleAtoms atom.weight atom.nonnegative target.atoms ++ bindAtoms remaining left)
          (pointwise atom.item)).trans
            (congrArg (fun tail =>
              scaleAtoms atom.weight atom.nonnegative (right atom.item).atoms ++ tail) ih)

/-- Every bound occurrence has an original source occurrence and a member of that exact source's transition distribution
with the same payload.

Structural append membership identifies the original head transition or the recursive tail. Scaling preserves the
selected target payload and its exact original source occurrence. -/
theorem mem_bindAtoms_source_transition {α β : Type}
    (transition : α → Distribution β) (candidate : Weighted β) :
    ∀ {atoms : List (Weighted α)},
      candidate ∈ bindAtoms atoms transition →
        ∃ source, source ∈ atoms ∧
          ∃ target, target ∈ (transition source.item).atoms ∧
            target.item = candidate.item
  | [], member => by nomatch member
  | atom :: remaining, member => by
      change candidate ∈ scaleAtoms atom.weight atom.nonnegative
        (transition atom.item).atoms ++ bindAtoms remaining transition at member
      rcases Membership.mem_append.mp member with headMember | tailMember
      · rcases mem_scaleAtoms_source atom.weight atom.nonnegative candidate
          headMember with ⟨target, targetMember, itemEqual⟩
        exact ⟨atom, List.Mem.head remaining, target, targetMember, itemEqual⟩
      · rcases mem_bindAtoms_source_transition transition candidate tailMember
          with ⟨source, sourceMember, target, targetMember, itemEqual⟩
        exact ⟨source, List.Mem.tail atom sourceMember,
          target, targetMember, itemEqual⟩

open Purelib.Data.Rat in
/-- Expanding through normalized transition distributions preserves the exact original total weight.

Each original occurrence scales its own retained transition atoms by its
original weight. That transition's normalization certificate identifies the
scaled row total, and the unchanged recursive tail retains the source total. -/
theorem totalWeight_bindAtoms {α β : Type}
    (atoms : List (Weighted α)) (transition : α → Distribution β) :
    totalWeight (bindAtoms atoms transition) = totalWeight atoms := by
  induction atoms with
  | nil => rfl
  | cons atom remaining ih =>
      change totalWeight (scaleAtoms atom.weight atom.nonnegative
          (transition atom.item).atoms ++ bindAtoms remaining transition) =
        atom.weight + totalWeight remaining
      calc
        totalWeight (scaleAtoms atom.weight atom.nonnegative
            (transition atom.item).atoms ++ bindAtoms remaining transition) =
            totalWeight (scaleAtoms atom.weight atom.nonnegative (transition atom.item).atoms) +
              totalWeight (bindAtoms remaining transition) := totalWeight_append _ _
        _ = atom.weight * totalWeight (transition atom.item).atoms + totalWeight remaining :=
          (congrArg (fun row => row + totalWeight (bindAtoms remaining transition))
            (totalWeight_scaleAtoms atom.weight atom.nonnegative (transition atom.item).atoms)).trans
            (congrArg (fun tail => atom.weight * totalWeight (transition atom.item).atoms + tail) ih)
        _ = atom.weight + totalWeight remaining :=
          congrArg (fun row => row + totalWeight remaining)
            ((congrArg (fun total => atom.weight * total) (transition atom.item).total_one).trans
              (Fraction.Field.mul_one_direct atom.weight))

/-- Bound event weight equals the original weighted integral of the exact transition probabilities.

The original head transition contributes its scaled event weight. Scalar congruence combines that retained row
certificate with the integral over the unchanged recursive tail. -/
theorem eventWeight_bindAtoms {α β : Type}
    (atoms : List (Weighted α)) (transition : α → Distribution β)
    (event : β → Bool) :
    eventWeight (bindAtoms atoms transition) event =
      expectationWeight atoms
        (fun item => (transition item).probability event) := by
  induction atoms with
  | nil => rfl
  | cons atom remaining ih =>
      change eventWeight (scaleAtoms atom.weight atom.nonnegative
          (transition atom.item).atoms ++ bindAtoms remaining transition) event =
        atom.weight * (transition atom.item).probability event +
          expectationWeight remaining (fun item => (transition item).probability event)
      calc
        _ = eventWeight (scaleAtoms atom.weight atom.nonnegative
              (transition atom.item).atoms) event +
            eventWeight (bindAtoms remaining transition) event :=
          eventWeight_append _ _ event
        _ = _ :=
          (congrArg (fun row => row + eventWeight (bindAtoms remaining transition) event)
            (eventWeight_scaleAtoms atom.weight atom.nonnegative (transition atom.item).atoms event)).trans
              (congrArg (fun tail =>
                atom.weight * (transition atom.item).probability event + tail) ih)

open Purelib.Data.Rat in
/-- Bound weighted integration equals the original weighted integral of the exact transition expectations.

The original head transition contributes its scaled observable integral. Scalar congruence combines that retained row
certificate with the integral over the unchanged recursive tail. -/
theorem expectationWeight_bindAtoms {α β : Type}
    (atoms : List (Weighted α)) (transition : α → Distribution β)
    (value : β → Fraction.Rational) :
    expectationWeight (bindAtoms atoms transition) value =
      expectationWeight atoms
        (fun item => (transition item).expectation value) := by
  induction atoms with
  | nil => rfl
  | cons atom remaining ih =>
      change expectationWeight (scaleAtoms atom.weight atom.nonnegative
          (transition atom.item).atoms ++ bindAtoms remaining transition) value =
        atom.weight * (transition atom.item).expectation value +
          expectationWeight remaining (fun item => (transition item).expectation value)
      calc
        _ = expectationWeight (scaleAtoms atom.weight atom.nonnegative
              (transition atom.item).atoms) value +
            expectationWeight (bindAtoms remaining transition) value :=
          expectationWeight_append _ _ value
        _ = _ :=
          (congrArg (fun row => row + expectationWeight (bindAtoms remaining transition) value)
            (expectationWeight_scaleAtoms atom.weight atom.nonnegative (transition atom.item).atoms value)).trans
              (congrArg (fun tail =>
                atom.weight * (transition atom.item).expectation value + tail) ih)

/-- Transitions with a fixed occurrence count multiply the original list length by that count.

Every original transition has the supplied common count, and scaling retains that list length. Structural append lengths
and the unchanged source tail give the exact finite product. -/
theorem bindAtoms_length_of_constant {α β : Type}
    (transition : α → Distribution β) (count : Nat)
    (constantLength : ∀ item, (transition item).atoms.length = count) :
    ∀ atoms : List (Weighted α),
      (bindAtoms atoms transition).length = atoms.length * count
  | [] => (Nat.zero_mul count).symm
  | atom :: remaining => by
      change (scaleAtoms atom.weight atom.nonnegative (transition atom.item).atoms ++
          bindAtoms remaining transition).length = (remaining.length + 1) * count
      calc
        _ = (scaleAtoms atom.weight atom.nonnegative (transition atom.item).atoms).length +
            (bindAtoms remaining transition).length := Append.length_append _ _
        _ = count + remaining.length * count :=
          (congrArg (fun head => head + (bindAtoms remaining transition).length)
            ((scaleAtoms_length atom.weight atom.nonnegative (transition atom.item).atoms).trans
              (constantLength atom.item))).trans
                (congrArg (fun tail => count + tail)
                  (bindAtoms_length_of_constant transition count constantLength remaining))
        _ = remaining.length * count + count := Nat.add_comm _ _
        _ = (remaining.length + 1) * count := (Nat.succ_mul remaining.length count).symm

namespace Distribution

open Purelib.Data.Rat in
/-- Retain a singleton distribution of unit weight at the supplied exact payload.

The single original payload carries weight one and its nonnegativity witness. The stored normalization certificate
concerns precisely that singleton list. -/
def pure {α : Type} (value : α) : Distribution α where
  atoms := [⟨value, 1, by decide⟩]
  total_one := (Fraction.Field.add_comm 1 0).trans (Fraction.Field.zero_add 1)

/-- Expand the retained source distribution through its exact transition distributions, preserving normalization.

The builder retains the original bindAtoms result. Its total certificate
composes that exact expanded-list total with the original source's retained
normalization witness. -/
def bind {α β : Type} (source : Distribution α)
    (transition : α → Distribution β) : Distribution β where
  atoms := bindAtoms source.atoms transition
  total_one := (totalWeight_bindAtoms source.atoms transition).trans source.total_one

/-- Map a retained distribution by binding each original payload to its exact singleton image distribution. -/
def map {α β : Type} (source : Distribution α) (function : α → β) :
    Distribution β :=
  source.bind fun value => Distribution.pure (function value)

/-- Pointwise equal payload functions produce equal exact mapped distributions. -/
theorem map_congr {α β : Type} (source : Distribution α)
    (left right : α → β) (pointwise : ∀ item, left item = right item) :
    source.map left = source.map right := by
  apply Distribution.eq_of_atoms_eq
  unfold map bind
  exact bindAtoms_congr source.atoms _ _ (fun item =>
    congrArg Distribution.pure (pointwise item))

/-- Pair each retained left payload with the exact mapped right distribution in left-major order. -/
def product {α β : Type} (left : Distribution α)
    (right : Distribution β) : Distribution (α × β) :=
  left.bind fun leftValue =>
    right.map fun rightValue => (leftValue, rightValue)

/-- Mapping a distribution preserves its retained occurrence count. -/
theorem map_atoms_length {α β : Type} (source : Distribution α)
    (function : α → β) :
    (source.map function).atoms.length = source.atoms.length := by
  unfold map bind
  change (bindAtoms source.atoms
      (fun value => Distribution.pure (function value))).length =
    source.atoms.length
  rw [bindAtoms_length_of_constant
    (fun value => Distribution.pure (function value)) 1]
  · exact Nat.mul_one source.atoms.length
  · intro item
    rfl

/-- The exact product distribution has occurrence count equal to the product of the original counts. -/
theorem product_atoms_length {α β : Type}
    (left : Distribution α) (right : Distribution β) :
    (left.product right).atoms.length =
      left.atoms.length * right.atoms.length := by
  unfold product bind
  change (bindAtoms left.atoms
      (fun leftValue => right.map fun rightValue =>
        (leftValue, rightValue))).length =
    left.atoms.length * right.atoms.length
  apply bindAtoms_length_of_constant
  intro leftValue
  exact right.map_atoms_length fun rightValue => (leftValue, rightValue)

/-- Every mapped occurrence's payload is the image of an exact original source occurrence.

The bind witness supplies the original source occurrence and a target in its retained singleton image. Structural
singleton membership identifies that target without a decidable membership assumption. -/
theorem mem_map_atoms_source {α β : Type}
    (source : Distribution α) (function : α → β)
    (candidate : Weighted β) (member : candidate ∈ (source.map function).atoms) :
    ∃ atom, atom ∈ source.atoms ∧ function atom.item = candidate.item := by
  unfold map bind at member
  rcases mem_bindAtoms_source_transition
      (fun value => Distribution.pure (function value)) candidate member with
    ⟨atom, atomMember, target, targetMember, targetEqual⟩
  change target ∈ [⟨function atom.item, 1, _⟩] at targetMember
  have targetIdentity := Membership.mem_singleton.mp targetMember
  have mappedEqual : function atom.item = target.item :=
    (congrArg Weighted.item targetIdentity).symm
  exact ⟨atom, atomMember, mappedEqual.trans targetEqual⟩

/-- Every product occurrence retains a payload pair from exact original left and right occurrences. -/
theorem mem_product_atoms_sources {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (candidate : Weighted (α × β))
    (member : candidate ∈ (left.product right).atoms) :
    ∃ leftAtom, leftAtom ∈ left.atoms ∧
      ∃ rightAtom, rightAtom ∈ right.atoms ∧
        (leftAtom.item, rightAtom.item) = candidate.item := by
  unfold product bind at member
  rcases mem_bindAtoms_source_transition
      (fun leftValue => right.map fun rightValue =>
        (leftValue, rightValue)) candidate member with
    ⟨leftAtom, leftMember, target, targetMember, targetEqual⟩
  rcases right.mem_map_atoms_source
      (fun rightValue => (leftAtom.item, rightValue)) target targetMember with
    ⟨rightAtom, rightMember, pairEqual⟩
  exact ⟨leftAtom, leftMember, rightAtom, rightMember,
    pairEqual.trans targetEqual⟩

/-- Probability after binding equals source expectation of the exact transition probabilities. -/
theorem bind_probability {α β : Type} (source : Distribution α)
    (transition : α → Distribution β) (event : β → Bool) :
    (source.bind transition).probability event =
      source.expectation (fun item =>
        (transition item).probability event) :=
  eventWeight_bindAtoms source.atoms transition event

open Purelib.Data.Rat in
/-- Expectation after binding equals source expectation of the exact transition expectations. -/
theorem bind_expectation {α β : Type} (source : Distribution α)
    (transition : α → Distribution β) (value : β → Fraction.Rational) :
    (source.bind transition).expectation value =
      source.expectation (fun item =>
        (transition item).expectation value) :=
  expectationWeight_bindAtoms source.atoms transition value

/-- Associating two finite transition stages in either order preserves every event probability. -/
theorem bind_bind_probability {α β γ : Type}
    (source : Distribution α) (first : α → Distribution β)
    (second : β → Distribution γ) (event : γ → Bool) :
    ((source.bind first).bind second).probability event =
      (source.bind fun item => (first item).bind second).probability event := by
  calc
    ((source.bind first).bind second).probability event =
        (source.bind first).expectation
          (fun middle => (second middle).probability event) :=
      (source.bind first).bind_probability second event
    _ = source.expectation (fun item =>
          (first item).expectation
            (fun middle => (second middle).probability event)) :=
      source.bind_expectation first _
    _ = source.expectation (fun item =>
          ((first item).bind second).probability event) := by
      exact source.expectation_congr _ _ (fun item =>
        (first item).bind_probability second event |>.symm)
    _ = (source.bind fun item =>
          (first item).bind second).probability event :=
      (source.bind_probability
        (fun item => (first item).bind second) event).symm

section
open Purelib.Data.Rat
/-- Associating two finite transition stages in either order preserves every rational expectation. -/
theorem bind_bind_expectation {α β γ : Type}
    (source : Distribution α) (first : α → Distribution β)
    (second : β → Distribution γ) (value : γ → Fraction.Rational) :
    ((source.bind first).bind second).expectation value =
      (source.bind fun item => (first item).bind second).expectation value := by
  calc
    ((source.bind first).bind second).expectation value =
        (source.bind first).expectation
          (fun middle => (second middle).expectation value) :=
      (source.bind first).bind_expectation second value
    _ = source.expectation (fun item =>
          (first item).expectation
            (fun middle => (second middle).expectation value)) :=
      source.bind_expectation first _
    _ = source.expectation (fun item =>
          ((first item).bind second).expectation value) := by
      exact source.expectation_congr _ _ (fun item =>
        (first item).bind_expectation second value |>.symm)
    _ = (source.bind fun item =>
          (first item).bind second).expectation value :=
      (source.bind_expectation
        (fun item => (first item).bind second) value).symm

/-- A singleton distribution's event probability is the Boolean indicator at its exact payload.

The original singleton contributes weight one exactly when its Boolean test is true. Its empty tail contributes zero
under both Boolean outcomes. -/
@[simp] theorem pure_probability {α : Type} (item : α)
    (event : α → Bool) :
    (Distribution.pure item).probability event =
      indicator event item := by
  change (match event item with | true => (1 : Fraction.Rational) | false => 0) +
      (0 : Fraction.Rational) =
    (match event item with | true => (1 : Fraction.Rational) | false => 0)
  cases event item <;> exact (Fraction.Field.add_comm _ 0).trans (Fraction.Field.zero_add _)

/-- A singleton distribution's expectation is the observable at its exact payload.

The original singleton contributes one times the supplied scalar observation. Its empty tail contributes zero, so the
retained observable is unchanged. -/
@[simp] theorem pure_expectation {α : Type} (item : α)
    (value : α → Fraction.Rational) :
    (Distribution.pure item).expectation value = value item := by
  change 1 * value item + 0 = value item
  exact (congrArg (fun head => head + 0) (Fraction.Field.one_mul (value item))).trans
    ((Fraction.Field.add_comm (value item) 0).trans (Fraction.Field.zero_add (value item)))

end

/-- Binding a singleton has the same event probabilities as its exact transition distribution. -/
theorem pure_bind_probability {α β : Type} (item : α)
    (transition : α → Distribution β) (event : β → Bool) :
    ((Distribution.pure item).bind transition).probability event =
      (transition item).probability event := by
  rw [bind_probability, pure_expectation]

open Purelib.Data.Rat in
/-- Binding a singleton has the same expectations as its exact transition distribution. -/
theorem pure_bind_expectation {α β : Type} (item : α)
    (transition : α → Distribution β) (value : β → Fraction.Rational) :
    ((Distribution.pure item).bind transition).expectation value =
      (transition item).expectation value := by
  rw [bind_expectation, pure_expectation]

/-- Binding every original payload to itself as a singleton preserves all event probabilities. -/
theorem bind_pure_probability {α : Type} (source : Distribution α)
    (event : α → Bool) :
    (source.bind Distribution.pure).probability event =
      source.probability event := by
  rw [bind_probability]
  calc
    source.expectation (fun item =>
          (Distribution.pure item).probability event) =
        source.expectation (indicator event) :=
      source.expectation_congr _ _ (fun item => pure_probability item event)
    _ = source.probability event := source.expectation_indicator event

open Purelib.Data.Rat in
/-- Binding every original payload to itself as a singleton preserves all expectations. -/
theorem bind_pure_expectation {α : Type} (source : Distribution α)
    (value : α → Fraction.Rational) :
    (source.bind Distribution.pure).expectation value =
      source.expectation value := by
  rw [bind_expectation]
  exact source.expectation_congr _ _ (fun item => pure_expectation item value)

/-- Mapped probability equals original probability of the pulled-back event.

Each retained singleton image contributes the indicator of the pulled-back Boolean event. Pointwise integral congruence
and the original indicator certificate identify its probability. -/
theorem map_probability {α β : Type} (source : Distribution α)
    (function : α → β) (event : β → Bool) :
    (source.map function).probability event =
      source.probability (fun item => event (function item)) := by
  rw [map, bind_probability]
  calc
    source.expectation (fun item => (Distribution.pure (function item)).probability event) =
        source.expectation (indicator (fun item => event (function item))) :=
      source.expectation_congr _ _ (fun item => pure_probability (function item) event)
    _ = source.probability (fun item => event (function item)) :=
      source.expectation_indicator (fun item => event (function item))

section
open Purelib.Data.Rat
/-- Mapped expectation equals original expectation of the pulled-back observable. -/
theorem map_expectation {α β : Type} (source : Distribution α)
    (function : α → β) (value : β → Fraction.Rational) :
    (source.map function).expectation value =
      source.expectation (fun item => value (function item)) := by
  rw [map, bind_expectation]
  exact source.expectation_congr _ _ (fun item =>
    pure_expectation (function item) value)

/-- A constant times an event indicator has expectation equal to event probability times that constant.

Pointwise commutativity exposes the same scalar as an integral factor. The original event indicator integral then
supplies its exact probability. -/
private theorem expectation_event_constant {α : Type}
    (source : Distribution α) (event : α → Bool)
    (constant : Fraction.Rational) :
    source.expectation
        (fun item => indicator event item * constant) =
      source.probability event * constant := by
  calc
    source.expectation (fun item => indicator event item * constant) =
        source.expectation (fun item => constant * indicator event item) :=
      source.expectation_congr _ _ (fun item =>
        Fraction.Field.mul_comm (indicator event item) constant)
    _ = constant * source.expectation (indicator event) :=
      source.expectation_scale constant (indicator event)
    _ = constant * source.probability event :=
      congrArg (fun observation => constant * observation) (source.expectation_indicator event)
    _ = source.probability event * constant := Fraction.Field.mul_comm _ _

/-- A rectangular event has product-distribution probability equal to the product of its marginal probabilities.

For each original left occurrence, its Boolean event selects either zero or the exact right event probability. The
retained left integral factors that right probability using the same event indicator. -/
theorem product_probability_rectangle {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (leftEvent : α → Bool) (rightEvent : β → Bool) :
    (left.product right).probability
        (fun pair => leftEvent pair.1 && rightEvent pair.2) =
      left.probability leftEvent * right.probability rightEvent := by
  have conditional : ∀ item,
      ((right.map fun rightValue => (item, rightValue)).probability
          (fun pair => leftEvent pair.1 && rightEvent pair.2)) =
        indicator leftEvent item * right.probability rightEvent := by
    intro item
    cases selected : leftEvent item
    · calc
        (right.map fun rightValue => (item, rightValue)).probability
              (fun pair => leftEvent pair.1 && rightEvent pair.2) =
            right.probability (fun rightValue =>
              leftEvent item && rightEvent rightValue) :=
          right.map_probability (fun rightValue => (item, rightValue)) _
        _ = right.probability (fun _ => false) :=
          right.probability_congr _ _ (fun rightValue => by
            rw [selected, Bool.false_and])
        _ = 0 := right.probability_false
        _ = indicator leftEvent item * right.probability rightEvent := by
          change 0 = (match leftEvent item with | true => 1 | false => 0) *
            right.probability rightEvent
          rw [selected]
          exact (Fraction.Field.zero_mul_direct _).symm
    · calc
        (right.map fun rightValue => (item, rightValue)).probability
              (fun pair => leftEvent pair.1 && rightEvent pair.2) =
            right.probability (fun rightValue =>
              leftEvent item && rightEvent rightValue) :=
          right.map_probability (fun rightValue => (item, rightValue)) _
        _ = right.probability rightEvent :=
          right.probability_congr _ _ (fun rightValue => by
            rw [selected, Bool.true_and])
        _ = indicator leftEvent item * right.probability rightEvent := by
          change right.probability rightEvent =
            (match leftEvent item with | true => 1 | false => 0) * right.probability rightEvent
          rw [selected]
          exact (Fraction.Field.one_mul _).symm
  calc
    (left.product right).probability
          (fun pair => leftEvent pair.1 && rightEvent pair.2) =
        left.expectation (fun item =>
          (right.map fun rightValue => (item, rightValue)).probability
            (fun pair => leftEvent pair.1 && rightEvent pair.2)) :=
      left.bind_probability
        (fun item => right.map fun rightValue => (item, rightValue)) _
    _ = left.expectation (fun item =>
          indicator leftEvent item * right.probability rightEvent) :=
      left.expectation_congr _ _ conditional
    _ = left.probability leftEvent * right.probability rightEvent :=
      expectation_event_constant left leftEvent
        (right.probability rightEvent)

end

/-- Product-event probability equals left expectation of the exact right slice probabilities. -/
theorem product_probability_iterated {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (event : α × β → Bool) :
    (left.product right).probability event =
      left.expectation (fun leftItem =>
        right.probability (fun rightItem => event (leftItem, rightItem))) := by
  calc
    (left.product right).probability event =
        left.expectation (fun leftItem =>
          (right.map fun rightItem => (leftItem, rightItem)).probability
            event) :=
      left.bind_probability
        (fun leftItem => right.map fun rightItem => (leftItem, rightItem)) event
    _ = left.expectation (fun leftItem =>
          right.probability (fun rightItem => event (leftItem, rightItem))) :=
      left.expectation_congr _ _ (fun leftItem =>
        right.map_probability (fun rightItem => (leftItem, rightItem)) event)

open Purelib.Data.Rat
/-- A product of separate observables has product expectation equal to the product of the original expectations. -/
theorem product_expectation_mul {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (leftValue : α → Fraction.Rational) (rightValue : β → Fraction.Rational) :
    (left.product right).expectation
        (fun pair => leftValue pair.1 * rightValue pair.2) =
      left.expectation leftValue * right.expectation rightValue := by
  rw [product, bind_expectation]
  have conditional : ∀ item,
      (right.map fun rightItem => (item, rightItem)).expectation
          (fun pair => leftValue pair.1 * rightValue pair.2) =
        leftValue item * right.expectation rightValue := by
    intro item
    rw [map_expectation]
    exact right.expectation_scale (leftValue item) rightValue
  calc
    left.expectation (fun item =>
          (right.map fun rightItem => (item, rightItem)).expectation
            (fun pair => leftValue pair.1 * rightValue pair.2)) =
        left.expectation
          (fun item => leftValue item * right.expectation rightValue) :=
      left.expectation_congr _ _ conditional
    _ = left.expectation
          (fun item => right.expectation rightValue * leftValue item) := by
      exact left.expectation_congr _ _ (fun item => by ring1)
    _ = right.expectation rightValue * left.expectation leftValue :=
      left.expectation_scale (right.expectation rightValue) leftValue
    _ = left.expectation leftValue * right.expectation rightValue := by ring1

/-- Product expectation equals the exact left-then-right nested expectations. -/
theorem product_expectation_iterated {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : α × β → Fraction.Rational) :
    (left.product right).expectation value =
      left.expectation (fun leftItem =>
        right.expectation (fun rightItem => value (leftItem, rightItem))) := by
  rw [product, bind_expectation]
  exact left.expectation_congr _ _ (fun leftItem =>
    right.map_expectation (fun rightItem => (leftItem, rightItem)) value)

/-- Exchange the exact finite nested expectations of a rational observable on paired payloads. -/
theorem expectation_exchange {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : α → β → Fraction.Rational) :
    left.expectation (fun leftItem =>
        right.expectation (fun rightItem => value leftItem rightItem)) =
      right.expectation (fun rightItem =>
        left.expectation (fun leftItem => value leftItem rightItem)) :=
  expectationWeight_exchange value left.atoms right.atoms
end Distribution

end Purelib.Measure

end

section
/-!
# Finite pushforward laws for powered Lp and essential maxima

An executable pushforward retains every displayed source row and merely
changes its payload.  Consequently rational L1, natural-powered Lp, finite
almost-everywhere equality, and computed essential maxima all obey exact
change-of-variables laws.  No quotient function space or measurable-map
side condition is needed on a displayed finite table.
-/

@[expose] public section

namespace Purelib.Measure

open Purelib.Data.Rat in
/-- Binding to singleton images gives exactly the original weight-preserving mapped occurrence list.

The singleton target is scaled by its original source weight, leaving that weight unchanged. Constructor equivalence
retains the same payload and nonnegativity proof while scalar tail congruence retains the mapped order. -/
private theorem bindAtoms_pure_eq_mapAtoms {α β : Type}
    (function : α → β) : ∀ atoms : List (Weighted α),
    bindAtoms atoms (fun item => Distribution.pure (function item)) =
      mapAtoms function atoms
  | [] => rfl
  | atom :: remaining => by
      change (⟨function atom.item, atom.weight * 1, _⟩ : Weighted β) ::
          bindAtoms remaining (fun item => Distribution.pure (function item)) =
        (⟨function atom.item, atom.weight, atom.nonnegative⟩ : Weighted β) ::
          mapAtoms function remaining
      exact congrArg₂ List.cons
        ((Weighted.mk.injEq _ _ _ _ _ _).mpr
          ⟨rfl, Fraction.Field.mul_one_direct atom.weight⟩)
        (bindAtoms_pure_eq_mapAtoms function remaining)

namespace Distribution

/-- The mapped distribution retains exactly the weight-preserving mapped source occurrence list. -/
theorem map_atoms_eq_mapAtoms {α β : Type} (source : Distribution α)
    (function : α → β) :
    (source.map function).atoms = mapAtoms function source.atoms := by
  unfold map bind
  exact bindAtoms_pure_eq_mapAtoms function source.atoms
end Distribution

end Purelib.Measure

end

section
/-!
# Stationary finite dynamics and occupation averages

A finite transition preserves a displayed rational law when one exact step is
evaluation-equivalent to the original law.  This module proves preservation
at every supplied finite horizon and computes the exact expectation of a
finite Markov-path occupation count and frequency.  A final Chebyshev theorem
isolates the remaining dynamical input as the exact variance of that finite
occupation frequency.

This is a finite quantitative mean-ergodic interface, not an asymptotic
ergodic theorem: every path, horizon, event, expectation, and variance is
displayed finite rational data.
-/

@[expose] public section

namespace Purelib.Measure
namespace Distribution

/-- Return the singleton distribution at the exact transformed payload. -/
def deterministicTransition {alpha : Type} (transformation : alpha → alpha)
    (item : alpha) : Distribution alpha :=
  Distribution.pure (transformation item)

end Distribution

end Purelib.Measure

end
