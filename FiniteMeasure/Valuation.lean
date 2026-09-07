import FiniteMeasure.Probability

/-!
# Exact finite rational valuations

`FiniteContent` is the normalized-independent core measure object: a displayed
finite weighted list evaluated only against executable Boolean events.
-/

namespace FiniteMeasure

/-- A displayed finite rational content, with no normalization requirement. -/
structure FiniteContent (α : Type) where
  atoms : List (Weighted α)

namespace FiniteContent

/-- Total displayed rational mass. -/
def total {α : Type} (content : FiniteContent α) : Coordinate :=
  totalWeight content.atoms

/-- Exact content of an executable finite event. -/
def measure {α : Type} (content : FiniteContent α)
    (event : α → Bool) : Coordinate :=
  eventWeight content.atoms event

/-- Pointwise-equal executable events have the same finite content. -/
theorem measure_congr {α : Type} (content : FiniteContent α)
    (left right : α → Bool) (pointwise : ∀ item, left item = right item) :
    content.measure left = content.measure right :=
  eventWeight_congr content.atoms left right pointwise

theorem measure_nonneg {α : Type} (content : FiniteContent α)
    (event : α → Bool) : 0 ≤ content.measure event :=
  eventWeight_nonneg content.atoms event

theorem measure_le_total {α : Type} (content : FiniteContent α)
    (event : α → Bool) : content.measure event ≤ content.total :=
  eventWeight_le_totalWeight content.atoms event

@[simp] theorem measure_empty {α : Type} (content : FiniteContent α) :
    content.measure (fun _ => false) = 0 := by
  unfold measure
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [eventWeight, zero_add, inductionHypothesis]

@[simp] theorem measure_univ {α : Type} (content : FiniteContent α) :
    content.measure (fun _ => true) = content.total := by
  unfold measure total
  induction content.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      simp only [eventWeight, totalWeight, inductionHypothesis]

/-- The exact finite valuation law. -/
theorem valuation {α : Type} (content : FiniteContent α)
    (first second : α → Bool) :
    content.measure first + content.measure second =
      content.measure (unionEvent first second) +
        content.measure (intersectionEvent first second) :=
  eventWeight_valuation content.atoms first second

/-- Complement consumes exactly the remaining displayed mass. -/
theorem add_complement {α : Type} (content : FiniteContent α)
    (event : α → Bool) :
    content.measure event + content.measure (complementEvent event) =
      content.total :=
  eventWeight_add_complement content.atoms event

/-- Exact finite additivity for events disjoint on the displayed atoms. -/
theorem union_of_disjoint {α : Type} (content : FiniteContent α)
    {first second : α → Bool}
    (disjoint : DisjointOn content.atoms first second) :
    content.measure (unionEvent first second) =
      content.measure first + content.measure second :=
  eventWeight_union_of_disjoint disjoint

/-- Monotonicity from an explicit implication checked only on the displayed
finite atoms. -/
theorem mono {α : Type} (content : FiniteContent α)
    {first second : α → Bool}
    (implication : EventImpliesOn content.atoms first second) :
    content.measure first ≤ content.measure second :=
  eventWeight_mono implication

end FiniteContent

namespace Distribution

/-- Forget normalization while retaining the same displayed finite content. -/
def toFiniteContent {α : Type} (distribution : Distribution α) :
    FiniteContent α :=
  ⟨distribution.atoms⟩

@[simp] theorem toFiniteContent_total {α : Type}
    (distribution : Distribution α) :
    distribution.toFiniteContent.total = 1 :=
  distribution.total_one

end Distribution

end FiniteMeasure
