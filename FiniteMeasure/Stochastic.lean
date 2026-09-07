import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.AtomOperations

/-!
# Bounded finite stochastic processes

Finite distributions compose by explicit list flattening and rational weight
multiplication.  Iteration takes a displayed natural horizon and therefore
constructs only a finite process table.
-/

namespace FiniteMeasure

open Distribution

/-- Explicit finite flattening of one distribution through a finite
transition kernel. -/
def bindAtoms {α β : Type} :
    List (Weighted α) → (α → Distribution β) → List (Weighted β)
  | [], _ => []
  | atom :: remaining, transition =>
      scaleAtoms atom.weight atom.nonnegative
          (transition atom.item).atoms ++
        bindAtoms remaining transition

/-- Pointwise-equal transition tables produce the same explicit flattened
list.  The proof compares only the finitely displayed source rows. -/
theorem bindAtoms_congr {α β : Type}
    (atoms : List (Weighted α)) (left right : α → Distribution β)
    (pointwise : ∀ item, left item = right item) :
    bindAtoms atoms left = bindAtoms atoms right := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [bindAtoms, pointwise atom.item, inductionHypothesis]

/-- Every row emitted by finite bind comes with an explicit source row and
an explicit row of that source payload's transition table. -/
theorem mem_bindAtoms_source_transition {α β : Type}
    (transition : α → Distribution β) (candidate : Weighted β) :
    ∀ {atoms : List (Weighted α)},
      candidate ∈ bindAtoms atoms transition →
        ∃ source, source ∈ atoms ∧
          ∃ target, target ∈ (transition source.item).atoms ∧
            target.item = candidate.item
  | [], member => (List.not_mem_nil member).elim
  | atom :: remaining, member => by
      simp only [bindAtoms, List.mem_append] at member
      rcases member with headMember | tailMember
      · rcases mem_scaleAtoms_source atom.weight atom.nonnegative candidate
          headMember with ⟨target, targetMember, itemEqual⟩
        exact ⟨atom, List.mem_cons_self, target, targetMember, itemEqual⟩
      · rcases mem_bindAtoms_source_transition transition candidate tailMember
          with ⟨source, sourceMember, target, targetMember, itemEqual⟩
        exact ⟨source, List.mem_cons_of_mem atom sourceMember,
          target, targetMember, itemEqual⟩

theorem totalWeight_bindAtoms {α β : Type}
    (atoms : List (Weighted α)) (transition : α → Distribution β) :
    totalWeight (bindAtoms atoms transition) = totalWeight atoms := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [bindAtoms, totalWeight_append,
        totalWeight_scaleAtoms, (transition atom.item).total_one,
        mul_one, totalWeight, inductionHypothesis]

/-- Finite law of total probability for explicit list flattening. -/
theorem eventWeight_bindAtoms {α β : Type}
    (atoms : List (Weighted α)) (transition : α → Distribution β)
    (event : β → Bool) :
    eventWeight (bindAtoms atoms transition) event =
      expectationWeight atoms
        (fun item => (transition item).probability event) := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [bindAtoms, eventWeight_append,
        eventWeight_scaleAtoms, Distribution.probability,
        expectationWeight, inductionHypothesis]

/-- Finite iterated-evaluation identity for explicit list flattening. -/
theorem expectationWeight_bindAtoms {α β : Type}
    (atoms : List (Weighted α)) (transition : α → Distribution β)
    (value : β → Coordinate) :
    expectationWeight (bindAtoms atoms transition) value =
      expectationWeight atoms
        (fun item => (transition item).expectation value) := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [bindAtoms, expectationWeight_append,
        expectationWeight_scaleAtoms, Distribution.expectation,
        expectationWeight, inductionHypothesis]

private theorem expectationWeight_zero {α : Type}
    (atoms : List (Weighted α)) :
    expectationWeight atoms (fun _ => 0) = 0 := by
  induction atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [expectationWeight, mul_zero, inductionHypothesis, zero_add]

/-- Finite double sums may be exchanged exactly.  This is the arithmetic
core of symmetric finite Fubini, proved by recursion on displayed rows. -/
theorem expectationWeight_exchange {α β : Type}
    (value : α → β → Coordinate) :
    ∀ (left : List (Weighted α)) (right : List (Weighted β)),
      expectationWeight left (fun leftItem =>
        expectationWeight right (fun rightItem =>
          value leftItem rightItem)) =
      expectationWeight right (fun rightItem =>
        expectationWeight left (fun leftItem =>
          value leftItem rightItem))
  | [], right => by
      change 0 = expectationWeight right (fun _ => 0)
      exact (expectationWeight_zero right).symm
  | atom :: remaining, right => by
      simp only [expectationWeight]
      rw [expectationWeight_add, expectationWeight_scale,
        expectationWeight_exchange value remaining right]

/-- If every transition table has the same displayed size, finite bind has
the source size times that transition size. -/
theorem bindAtoms_length_of_constant {α β : Type}
    (transition : α → Distribution β) (count : Nat)
    (constantLength : ∀ item, (transition item).atoms.length = count) :
    ∀ atoms : List (Weighted α),
      (bindAtoms atoms transition).length = atoms.length * count
  | [] => by simp only [bindAtoms, List.length_nil, zero_mul]
  | atom :: remaining => by
      simp only [bindAtoms, List.length_append, scaleAtoms_length,
        constantLength, List.length_cons,
        bindAtoms_length_of_constant transition count constantLength
          remaining]
      rw [Nat.succ_mul, Nat.add_comm]

namespace Distribution

/-- Deterministic one-atom rational distribution. -/
def pure {α : Type} (value : α) : Distribution α where
  atoms := [⟨value, 1, by decide⟩]
  total_one := by
    simp only [totalWeight, add_zero]

/-- Finite rational distribution bind. -/
def bind {α β : Type} (source : Distribution α)
    (transition : α → Distribution β) : Distribution β where
  atoms := bindAtoms source.atoms transition
  total_one := by
    rw [totalWeight_bindAtoms, source.total_one]

/-- Exact finite pushforward of a displayed distribution. -/
def map {α β : Type} (source : Distribution α) (function : α → β) :
    Distribution β :=
  source.bind fun value => Distribution.pure (function value)

/-- Pointwise-equal maps give structurally equal finite pushforward tables.
No equality between the map functions is required. -/
theorem map_congr {α β : Type} (source : Distribution α)
    (left right : α → β) (pointwise : ∀ item, left item = right item) :
    source.map left = source.map right := by
  apply Distribution.eq_of_atoms_eq
  unfold map bind
  exact bindAtoms_congr source.atoms _ _ (fun item =>
    congrArg Distribution.pure (pointwise item))

/-- Exact finite product distribution. -/
def product {α β : Type} (left : Distribution α)
    (right : Distribution β) : Distribution (α × β) :=
  left.bind fun leftValue =>
    right.map fun rightValue => (leftValue, rightValue)

/-- One bounded finite stochastic step. -/
def step {α : Type} (transition : α → Distribution α)
    (source : Distribution α) : Distribution α :=
  source.bind transition

/-- Execute exactly the displayed finite number of stochastic steps. -/
def iterate {α : Type} (transition : α → Distribution α) :
    Nat → Distribution α → Distribution α
  | 0, source => source
  | count + 1, source => iterate transition count (source.step transition)

/-- Finite pushforward preserves the number of displayed atoms, including
duplicates. -/
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

/-- The explicit finite product table has the product of the two displayed
atom counts. -/
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

/-- Every displayed pushforward row comes from an explicitly displayed
source row and carries exactly its mapped payload. -/
theorem mem_map_atoms_source {α β : Type}
    (source : Distribution α) (function : α → β)
    (candidate : Weighted β) (member : candidate ∈ (source.map function).atoms) :
    ∃ atom, atom ∈ source.atoms ∧ function atom.item = candidate.item := by
  unfold map bind at member
  rcases mem_bindAtoms_source_transition
      (fun value => Distribution.pure (function value)) candidate member with
    ⟨atom, atomMember, target, targetMember, targetEqual⟩
  simp only [pure, List.mem_cons, List.not_mem_nil, or_false] at targetMember
  have mappedEqual : function atom.item = target.item := by
    rw [targetMember]
  exact ⟨atom, atomMember, mappedEqual.trans targetEqual⟩

/-- Every displayed product row has explicitly displayed left and right
source rows whose payload pair is the product payload. -/
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

/-- Exact finite law of total probability. -/
theorem bind_probability {α β : Type} (source : Distribution α)
    (transition : α → Distribution β) (event : β → Bool) :
    (source.bind transition).probability event =
      source.expectation (fun item =>
        (transition item).probability event) :=
  eventWeight_bindAtoms source.atoms transition event

/-- Exact finite iterated-expectation, or finite Fubini, identity. -/
theorem bind_expectation {α β : Type} (source : Distribution α)
    (transition : α → Distribution β) (value : β → Coordinate) :
    (source.bind transition).expectation value =
      source.expectation (fun item =>
        (transition item).expectation value) :=
  expectationWeight_bindAtoms source.atoms transition value

/-- Finite bind is associative under every executable event evaluation. -/
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

/-- Finite bind is associative under every rational observable evaluation. -/
theorem bind_bind_expectation {α β γ : Type}
    (source : Distribution α) (first : α → Distribution β)
    (second : β → Distribution γ) (value : γ → Coordinate) :
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

@[simp] theorem pure_probability {α : Type} (item : α)
    (event : α → Bool) :
    (Distribution.pure item).probability event =
      indicator event item := by
  cases selected : event item <;>
    simp only [probability, pure, eventWeight, indicator, selected,
      add_zero]

@[simp] theorem pure_expectation {α : Type} (item : α)
    (value : α → Coordinate) :
    (Distribution.pure item).expectation value = value item := by
  simp only [expectation, pure, expectationWeight, one_mul, add_zero]

/-- Evaluating a bind from a deterministic source is exactly evaluation of
the displayed transition at that source value. -/
theorem pure_bind_probability {α β : Type} (item : α)
    (transition : α → Distribution β) (event : β → Bool) :
    ((Distribution.pure item).bind transition).probability event =
      (transition item).probability event := by
  rw [bind_probability, pure_expectation]

theorem pure_bind_expectation {α β : Type} (item : α)
    (transition : α → Distribution β) (value : β → Coordinate) :
    ((Distribution.pure item).bind transition).expectation value =
      (transition item).expectation value := by
  rw [bind_expectation, pure_expectation]

/-- Binding to deterministic copies preserves every executable event
probability. -/
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

/-- Binding to deterministic copies preserves every rational expectation. -/
theorem bind_pure_expectation {α : Type} (source : Distribution α)
    (value : α → Coordinate) :
    (source.bind Distribution.pure).expectation value =
      source.expectation value := by
  rw [bind_expectation]
  exact source.expectation_congr _ _ (fun item => pure_expectation item value)

/-- Pushforward evaluates an event by its executable preimage. -/
theorem map_probability {α β : Type} (source : Distribution α)
    (function : α → β) (event : β → Bool) :
    (source.map function).probability event =
      source.probability (fun item => event (function item)) := by
  rw [map, bind_probability]
  change expectationWeight source.atoms
      (fun item => (Distribution.pure (function item)).probability event) =
    eventWeight source.atoms (fun item => event (function item))
  induction source.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      cases selected : event (function atom.item)
      · have head :
            (Distribution.pure (function atom.item)).probability event = 0 := by
          rw [pure_probability]
          simp only [indicator, selected]
        simp only [expectationWeight, eventWeight, selected, head, mul_zero,
          zero_add, inductionHypothesis]
      · have head :
            (Distribution.pure (function atom.item)).probability event = 1 := by
          rw [pure_probability]
          simp only [indicator, selected]
        simp only [expectationWeight, eventWeight, selected, head, mul_one,
          inductionHypothesis]

/-- Pushforward evaluates a rational observable by composition. -/
theorem map_expectation {α β : Type} (source : Distribution α)
    (function : α → β) (value : β → Coordinate) :
    (source.map function).expectation value =
      source.expectation (fun item => value (function item)) := by
  rw [map, bind_expectation]
  exact source.expectation_congr _ _ (fun item =>
    pure_expectation (function item) value)

private theorem expectation_event_constant {α : Type}
    (source : Distribution α) (event : α → Bool)
    (constant : Coordinate) :
    source.expectation
        (fun item => indicator event item * constant) =
      source.probability event * constant := by
  unfold expectation probability
  induction source.atoms with
  | nil =>
      simp only [expectationWeight, eventWeight, zero_mul]
  | cons atom remaining inductionHypothesis =>
      cases selected : event atom.item
      · have head : indicator event atom.item = 0 := by
          simp only [indicator, selected]
        simp only [expectationWeight, eventWeight, selected, head, zero_mul,
          mul_zero, zero_add, inductionHypothesis]
      · have head : indicator event atom.item = 1 := by
          simp only [indicator, selected]
        simp only [expectationWeight, eventWeight, selected, head, one_mul,
          inductionHypothesis]
        ring1

/-- Rectangular events in an explicit product distribution factor exactly.
This is finite independence, with no product sigma-algebra. -/
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
          simp only [indicator, selected, zero_mul]
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
          simp only [indicator, selected, one_mul]
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

/-- Full finite Fubini identity for an arbitrary Boolean event on the
explicit product distribution. -/
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

/-- Separable rational observables on an explicit product factor exactly. -/
theorem product_expectation_mul {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (leftValue : α → Coordinate) (rightValue : β → Coordinate) :
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

/-- Full finite Fubini identity for an arbitrary rational observable on the
explicit product distribution. -/
theorem product_expectation_iterated {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : α × β → Coordinate) :
    (left.product right).expectation value =
      left.expectation (fun leftItem =>
        right.expectation (fun rightItem => value (leftItem, rightItem))) := by
  rw [product, bind_expectation]
  exact left.expectation_congr _ _ (fun leftItem =>
    right.map_expectation (fun rightItem => (leftItem, rightItem)) value)

/-- Symmetric finite Fubini: the two exact nested rational expectations may
be exchanged. -/
theorem expectation_exchange {α β : Type}
    (left : Distribution α) (right : Distribution β)
    (value : α → β → Coordinate) :
    left.expectation (fun leftItem =>
        right.expectation (fun rightItem => value leftItem rightItem)) =
      right.expectation (fun rightItem =>
        left.expectation (fun leftItem => value leftItem rightItem)) :=
  expectationWeight_exchange value left.atoms right.atoms

@[simp] theorem iterate_zero {α : Type}
    (transition : α → Distribution α) (source : Distribution α) :
    iterate transition 0 source = source := rfl

@[simp] theorem iterate_succ {α : Type}
    (transition : α → Distribution α) (count : Nat)
    (source : Distribution α) :
    iterate transition (count + 1) source =
      iterate transition count (source.step transition) := rfl

theorem step_probability {α : Type}
    (transition : α → Distribution α) (source : Distribution α)
    (event : α → Bool) :
    (source.step transition).probability event =
      source.expectation (fun item =>
        (transition item).probability event) :=
  source.bind_probability transition event

theorem step_expectation {α : Type}
    (transition : α → Distribution α) (source : Distribution α)
    (value : α → Coordinate) :
    (source.step transition).expectation value =
      source.expectation (fun item =>
        (transition item).expectation value) :=
  source.bind_expectation transition value

/-- A pointwise harmonic observable has exactly preserved expectation at
every displayed finite horizon. -/
theorem iterate_expectation_of_harmonic {α : Type}
    (transition : α → Distribution α)
    (value : α → Coordinate)
    (harmonic : ∀ item, (transition item).expectation value = value item) :
    ∀ (count : Nat) (source : Distribution α),
      (iterate transition count source).expectation value =
        source.expectation value
  | 0, source => rfl
  | count + 1, source => by
      rw [iterate_succ,
        iterate_expectation_of_harmonic transition value harmonic count
          (source.step transition),
        source.step_expectation transition]
      exact source.expectation_congr _ _ harmonic

/-- A globally superharmonic observable has nonincreasing expectation over
every displayed finite horizon. -/
theorem iterate_expectation_le_of_superharmonic {α : Type}
    (transition : α → Distribution α)
    (value : α → Coordinate)
    (superharmonic : ∀ item,
      (transition item).expectation value ≤ value item) :
    ∀ (count : Nat) (source : Distribution α),
      (iterate transition count source).expectation value ≤
        source.expectation value
  | 0, source => le_rfl
  | count + 1, source => by
      calc
        (iterate transition (count + 1) source).expectation value =
            (iterate transition count
              (source.step transition)).expectation value := rfl
        _ ≤ (source.step transition).expectation value :=
          iterate_expectation_le_of_superharmonic transition value
            superharmonic count (source.step transition)
        _ = source.expectation (fun item =>
              (transition item).expectation value) :=
          source.step_expectation transition value
        _ ≤ source.expectation value := by
          apply source.expectation_mono
          intro atom member
          exact superharmonic atom.item

/-- A globally subharmonic observable has nondecreasing expectation over
every displayed finite horizon. -/
theorem iterate_expectation_mono_of_subharmonic {α : Type}
    (transition : α → Distribution α)
    (value : α → Coordinate)
    (subharmonic : ∀ item,
      value item ≤ (transition item).expectation value) :
    ∀ (count : Nat) (source : Distribution α),
      source.expectation value ≤
        (iterate transition count source).expectation value
  | 0, source => le_rfl
  | count + 1, source => by
      calc
        source.expectation value ≤
            source.expectation (fun item =>
              (transition item).expectation value) := by
          apply source.expectation_mono
          intro atom member
          exact subharmonic atom.item
        _ = (source.step transition).expectation value :=
          (source.step_expectation transition value).symm
        _ ≤ (iterate transition count
              (source.step transition)).expectation value :=
          iterate_expectation_mono_of_subharmonic transition value
            subharmonic count (source.step transition)
        _ = (iterate transition (count + 1) source).expectation value := rfl

/-- An executable event with harmonic one-step probabilities has invariant
probability at every displayed finite horizon. -/
theorem iterate_probability_of_harmonic_event {α : Type}
    (transition : α → Distribution α) (event : α → Bool)
    (harmonic : ∀ item,
      (transition item).probability event = indicator event item)
    (count : Nat) (source : Distribution α) :
    (iterate transition count source).probability event =
      source.probability event := by
  rw [← (iterate transition count source).expectation_indicator event,
    ← source.expectation_indicator event]
  exact iterate_expectation_of_harmonic transition (indicator event)
    (fun item => by
      rw [(transition item).expectation_indicator]
      exact harmonic item) count source

end Distribution

end FiniteMeasure
