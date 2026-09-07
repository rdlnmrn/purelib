import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Bounds

/-!
# Finite rational contents and event bounds

Weights are attached only to a displayed finite list.  Event measurement is
a three-way finite classification: inside, outside, or unresolved.  The
unresolved weight is exactly the width of the returned rational enclosure.
-/

namespace FiniteMeasure

/-- One displayed atom or cell with a certified nonnegative rational weight. -/
structure Weighted (α : Type) where
  item : α
  weight : Coordinate
  nonnegative : 0 ≤ weight

namespace Weighted

/-- Forget the payload while retaining its certified rational weight. -/
def amount {α : Type} (entry : Weighted α) : Coordinate :=
  entry.weight

end Weighted

/-- Total weight of a finite displayed list. -/
def totalWeight {α : Type} : List (Weighted α) → Coordinate
  | [] => 0
  | entry :: remaining => entry.weight + totalWeight remaining

@[simp] theorem totalWeight_nil {α : Type} :
    totalWeight ([] : List (Weighted α)) = 0 := rfl

@[simp] theorem totalWeight_cons {α : Type} (entry : Weighted α)
    (remaining : List (Weighted α)) :
    totalWeight (entry :: remaining) =
      entry.weight + totalWeight remaining := rfl

theorem totalWeight_nonneg {α : Type} :
    ∀ entries : List (Weighted α), 0 ≤ totalWeight entries
  | [] => le_rfl
  | entry :: remaining =>
      add_nonneg entry.nonnegative (totalWeight_nonneg remaining)

theorem totalWeight_append {α : Type}
    (left right : List (Weighted α)) :
    totalWeight (left ++ right) = totalWeight left + totalWeight right := by
  induction left with
  | nil =>
      simp only [List.nil_append, totalWeight_nil, zero_add]
  | cons entry remaining inductionHypothesis =>
      simp only [List.cons_append, totalWeight_cons, inductionHypothesis]
      ring1

/-- Finite classification of a weighted cell relative to an event. -/
inductive Status where
  | inside
  | outside
  | unresolved
deriving DecidableEq, Repr

/-- A displayed weighted cell together with its current finite event status. -/
structure Classified (α : Type) where
  atom : Weighted α
  status : Status

/-- Total weight, ignoring classifications. -/
def classifiedWeight {α : Type} : List (Classified α) → Coordinate
  | [] => 0
  | entry :: remaining => entry.atom.weight + classifiedWeight remaining

/-- Weight already certified to lie inside the event. -/
def lowerWeight {α : Type} : List (Classified α) → Coordinate
  | [] => 0
  | entry :: remaining =>
      (match entry.status with
        | .inside => entry.atom.weight
        | .outside | .unresolved => 0) + lowerWeight remaining

/-- Weight not yet certified to lie outside the event. -/
def upperWeight {α : Type} : List (Classified α) → Coordinate
  | [] => 0
  | entry :: remaining =>
      (match entry.status with
        | .outside => 0
        | .inside | .unresolved => entry.atom.weight) + upperWeight remaining

/-- The entire current rational error budget. -/
def unresolvedWeight {α : Type} : List (Classified α) → Coordinate
  | [] => 0
  | entry :: remaining =>
      (match entry.status with
        | .unresolved => entry.atom.weight
        | .inside | .outside => 0) + unresolvedWeight remaining

@[simp] theorem classifiedWeight_nil {α : Type} :
    classifiedWeight ([] : List (Classified α)) = 0 := rfl

@[simp] theorem classifiedWeight_cons {α : Type} (entry : Classified α)
    (remaining : List (Classified α)) :
    classifiedWeight (entry :: remaining) =
      entry.atom.weight + classifiedWeight remaining := rfl

@[simp] theorem lowerWeight_nil {α : Type} :
    lowerWeight ([] : List (Classified α)) = 0 := rfl

@[simp] theorem upperWeight_nil {α : Type} :
    upperWeight ([] : List (Classified α)) = 0 := rfl

@[simp] theorem unresolvedWeight_nil {α : Type} :
    unresolvedWeight ([] : List (Classified α)) = 0 := rfl

theorem classifiedWeight_nonneg {α : Type} :
    ∀ entries : List (Classified α), 0 ≤ classifiedWeight entries
  | [] => le_rfl
  | entry :: remaining =>
      add_nonneg entry.atom.nonnegative
        (classifiedWeight_nonneg remaining)

theorem lowerWeight_nonneg {α : Type} :
    ∀ entries : List (Classified α), 0 ≤ lowerWeight entries
  | [] => le_rfl
  | entry :: remaining => by
      rcases entry with ⟨atom, status⟩
      cases status
      · exact add_nonneg atom.nonnegative
          (lowerWeight_nonneg remaining)
      · simpa only [lowerWeight, zero_add] using
          lowerWeight_nonneg remaining
      · simpa only [lowerWeight, zero_add] using
          lowerWeight_nonneg remaining

theorem unresolvedWeight_nonneg {α : Type} :
    ∀ entries : List (Classified α), 0 ≤ unresolvedWeight entries
  | [] => le_rfl
  | entry :: remaining => by
      rcases entry with ⟨atom, status⟩
      cases status
      · simpa only [unresolvedWeight, zero_add] using
          unresolvedWeight_nonneg remaining
      · simpa only [unresolvedWeight, zero_add] using
          unresolvedWeight_nonneg remaining
      · exact add_nonneg atom.nonnegative
          (unresolvedWeight_nonneg remaining)

theorem upperWeight_le_classifiedWeight {α : Type} :
    ∀ entries : List (Classified α),
      upperWeight entries ≤ classifiedWeight entries
  | [] => le_rfl
  | entry :: remaining => by
      rcases entry with ⟨atom, status⟩
      cases status
      · exact add_le_add le_rfl
          (upperWeight_le_classifiedWeight remaining)
      · simpa only [upperWeight, classifiedWeight, zero_add] using
          (upperWeight_le_classifiedWeight remaining).trans
            (le_add_of_nonneg_left atom.nonnegative)
      · exact add_le_add le_rfl
          (upperWeight_le_classifiedWeight remaining)

theorem upperWeight_eq_lower_add_unresolved {α : Type} :
    ∀ entries : List (Classified α),
      upperWeight entries = lowerWeight entries + unresolvedWeight entries
  | [] => by
      simp only [upperWeight_nil, lowerWeight_nil, unresolvedWeight_nil,
        add_zero]
  | entry :: remaining => by
      have inductionHypothesis :=
        upperWeight_eq_lower_add_unresolved remaining
      rcases entry with ⟨atom, status⟩
      cases status
      · dsimp only [upperWeight, lowerWeight, unresolvedWeight]
        rw [inductionHypothesis]
        ring1
      · dsimp only [upperWeight, lowerWeight, unresolvedWeight]
        rw [inductionHypothesis]
        ring1
      · dsimp only [upperWeight, lowerWeight, unresolvedWeight]
        rw [inductionHypothesis]
        ring1

theorem lowerWeight_le_upperWeight {α : Type}
    (entries : List (Classified α)) :
    lowerWeight entries ≤ upperWeight entries := by
  rw [upperWeight_eq_lower_add_unresolved]
  exact le_add_of_nonneg_right (unresolvedWeight_nonneg entries)

/-- Rational lower and upper event weights at one finite frontier. -/
def eventBound {α : Type} (entries : List (Classified α)) : Bound where
  lower := lowerWeight entries
  upper := upperWeight entries
  valid := lowerWeight_le_upperWeight entries

theorem eventBound_width {α : Type} (entries : List (Classified α)) :
    (eventBound entries).width = unresolvedWeight entries := by
  dsimp only [Bound.width, eventBound]
  rw [upperWeight_eq_lower_add_unresolved]
  ring1

theorem lowerWeight_append {α : Type}
    (left right : List (Classified α)) :
    lowerWeight (left ++ right) = lowerWeight left + lowerWeight right := by
  induction left with
  | nil =>
      simp only [List.nil_append, lowerWeight_nil, zero_add]
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨atom, status⟩
      cases status <;>
        simp only [List.cons_append, lowerWeight, inductionHypothesis] <;>
        ring1

theorem upperWeight_append {α : Type}
    (left right : List (Classified α)) :
    upperWeight (left ++ right) = upperWeight left + upperWeight right := by
  induction left with
  | nil =>
      simp only [List.nil_append, upperWeight_nil, zero_add]
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨atom, status⟩
      cases status <;>
        simp only [List.cons_append, upperWeight, inductionHypothesis] <;>
        ring1

theorem unresolvedWeight_append {α : Type}
    (left right : List (Classified α)) :
    unresolvedWeight (left ++ right) =
      unresolvedWeight left + unresolvedWeight right := by
  induction left with
  | nil =>
      simp only [List.nil_append, unresolvedWeight_nil, zero_add]
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨atom, status⟩
      cases status <;>
        simp only [List.cons_append, unresolvedWeight, inductionHypothesis] <;>
        ring1

theorem classifiedWeight_append {α : Type}
    (left right : List (Classified α)) :
    classifiedWeight (left ++ right) =
      classifiedWeight left + classifiedWeight right := by
  induction left with
  | nil =>
      simp only [List.nil_append, classifiedWeight_nil, zero_add]
  | cons entry remaining inductionHypothesis =>
      simp only [List.cons_append, classifiedWeight_cons, inductionHypothesis]
      ring1

theorem eventBound_append {α : Type}
    (left right : List (Classified α)) :
    eventBound (left ++ right) = (eventBound left).add (eventBound right) := by
  apply Bound.ext
  · exact lowerWeight_append left right
  · exact upperWeight_append left right

/-- A finite event request is resolved to the displayed tolerance exactly
when its unresolved rational mass meets that tolerance. -/
def Resolves {α : Type} (entries : List (Classified α))
    (epsilon : Coordinate) : Prop :=
  unresolvedWeight entries < epsilon

theorem eventBound_width_lt {α : Type} {entries : List (Classified α)}
    {epsilon : Coordinate} (resolves : Resolves entries epsilon) :
    (eventBound entries).width < epsilon := by
  rw [eventBound_width]
  exact resolves

/-! ## Certified finite refinement -/

/-- A child status is compatible with its parent status.  Once a cell is
known inside or outside, refinement may not retract that positive fact;
an unresolved parent permits any finite child classification. -/
def Status.Refines (child parent : Status) : Prop :=
  match parent with
  | .inside => child = .inside
  | .outside => child = .outside
  | .unresolved => True

/-- Replacement of one classified parent by finitely many children whose
weights are exactly conserved and whose positive classifications persist. -/
structure Split {α β : Type} (parent : Classified α) where
  children : List (Classified β)
  conserved : classifiedWeight children = parent.atom.weight
  statuses : ∀ child, child ∈ children → child.status.Refines parent.status

private theorem lowerWeight_eq_classifiedWeight_of_inside {α : Type} :
    ∀ {entries : List (Classified α)},
      (∀ entry, entry ∈ entries → entry.status = .inside) →
      lowerWeight entries = classifiedWeight entries
  | [], _ => rfl
  | entry :: remaining, all => by
      have head := all entry List.mem_cons_self
      have tail : ∀ child, child ∈ remaining → child.status = .inside :=
        fun child member => all child (List.mem_cons_of_mem entry member)
      rcases entry with ⟨atom, status⟩
      cases status <;> try contradiction
      dsimp only [lowerWeight, classifiedWeight]
      rw [lowerWeight_eq_classifiedWeight_of_inside tail]

private theorem upperWeight_eq_classifiedWeight_of_inside {α : Type} :
    ∀ {entries : List (Classified α)},
      (∀ entry, entry ∈ entries → entry.status = .inside) →
      upperWeight entries = classifiedWeight entries
  | [], _ => rfl
  | entry :: remaining, all => by
      have head := all entry List.mem_cons_self
      have tail : ∀ child, child ∈ remaining → child.status = .inside :=
        fun child member => all child (List.mem_cons_of_mem entry member)
      rcases entry with ⟨atom, status⟩
      cases status <;> try contradiction
      dsimp only [upperWeight, classifiedWeight]
      rw [upperWeight_eq_classifiedWeight_of_inside tail]

private theorem lowerWeight_eq_zero_of_outside {α : Type} :
    ∀ {entries : List (Classified α)},
      (∀ entry, entry ∈ entries → entry.status = .outside) →
      lowerWeight entries = 0
  | [], _ => rfl
  | entry :: remaining, all => by
      have head := all entry List.mem_cons_self
      have tail : ∀ child, child ∈ remaining → child.status = .outside :=
        fun child member => all child (List.mem_cons_of_mem entry member)
      rcases entry with ⟨atom, status⟩
      cases status <;> try contradiction
      dsimp only [lowerWeight]
      simpa only [zero_add] using lowerWeight_eq_zero_of_outside tail

private theorem upperWeight_eq_zero_of_outside {α : Type} :
    ∀ {entries : List (Classified α)},
      (∀ entry, entry ∈ entries → entry.status = .outside) →
      upperWeight entries = 0
  | [], _ => rfl
  | entry :: remaining, all => by
      have head := all entry List.mem_cons_self
      have tail : ∀ child, child ∈ remaining → child.status = .outside :=
        fun child member => all child (List.mem_cons_of_mem entry member)
      rcases entry with ⟨atom, status⟩
      cases status <;> try contradiction
      dsimp only [upperWeight]
      simpa only [zero_add] using upperWeight_eq_zero_of_outside tail

/-- Replacing one cell by a certified finite split narrows its event bound. -/
theorem Split.eventBound_refines {α β : Type} {parent : Classified α}
    (split : Split (β := β) parent) :
    Bound.Refines (eventBound split.children) (eventBound [parent]) := by
  rcases parent with ⟨atom, parentStatus⟩
  cases parentStatus with
  | inside =>
      have allInside : ∀ child, child ∈ split.children →
          child.status = .inside := by
        intro child member
        exact split.statuses child member
      have lower := lowerWeight_eq_classifiedWeight_of_inside allInside
      have upper := upperWeight_eq_classifiedWeight_of_inside allInside
      constructor
      · simpa only [eventBound, lowerWeight, split.conserved, add_zero] using
          le_of_eq lower.symm
      · simpa only [eventBound, upperWeight, split.conserved, add_zero] using
          le_of_eq upper
  | outside =>
      have allOutside : ∀ child, child ∈ split.children →
          child.status = .outside := by
        intro child member
        exact split.statuses child member
      have lower := lowerWeight_eq_zero_of_outside allOutside
      have upper := upperWeight_eq_zero_of_outside allOutside
      constructor
      · simpa only [eventBound, lowerWeight, lower, add_zero] using
          (le_rfl : (0 : Coordinate) ≤ 0)
      · simpa only [eventBound, upperWeight, upper, add_zero] using
          (le_rfl : (0 : Coordinate) ≤ 0)
  | unresolved =>
      constructor
      · simpa only [eventBound, lowerWeight, add_zero] using
          lowerWeight_nonneg split.children
      · simpa only [eventBound, upperWeight, split.conserved, add_zero] using
          upperWeight_le_classifiedWeight split.children

/-- Replacing one parent inside an arbitrary finite frontier by a certified
same-type split narrows the complete event enclosure. -/
theorem Split.frontier_eventBound_refines
    {α : Type} {parent : Classified α}
    (split : Split (β := α) parent)
    (before after : List (Classified α)) :
    Bound.Refines
      (eventBound (before ++ split.children ++ after))
      (eventBound (before ++ [parent] ++ after)) := by
  have middle := split.eventBound_refines
  have withAfter := Bound.Refines.add middle
    (Bound.Refines.refl (eventBound after))
  have complete := Bound.Refines.add
    (Bound.Refines.refl (eventBound before)) withAfter
  rw [List.append_assoc, List.append_assoc]
  rw [eventBound_append before (split.children ++ after),
    eventBound_append split.children after,
    eventBound_append before ([parent] ++ after),
    eventBound_append [parent] after]
  exact complete

end FiniteMeasure
