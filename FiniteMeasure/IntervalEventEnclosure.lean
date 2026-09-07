import FiniteMeasure.ClassifiedProbability
import FiniteMeasure.EnclosedExpectation

/-!
# Finite probability of rational-interval membership

A rational enclosure for each displayed atom can certify that its value is
inside a target rational interval, outside it, or still unresolved.  The
resulting finite lower/upper sums enclose the exact probability for every
explicit rational observable admitted by those enclosures.  Narrower source
enclosures can only narrow the probability enclosure.
-/

namespace FiniteMeasure

/-- Executable event that a rational observable lies in one displayed
rational target enclosure. -/
def withinBoundEvent {α : Type} (target : Bound)
    (value : α → Coordinate) : α → Bool :=
  fun item => decide (target.Contains (value item))

/-- Classify a source enclosure relative to membership in a target rational
enclosure.  Containment of the whole source proves `inside`; strict
separation proves `outside`; overlap without containment stays unresolved. -/
def withinBoundStatus (range target : Bound) : Status :=
  if target.lower ≤ range.lower ∧ range.upper ≤ target.upper then .inside
  else if range.upper < target.lower ∨ target.upper < range.lower then .outside
  else .unresolved

/-- Classify every displayed row of a finite distribution using only its
current rational source enclosure. -/
def Distribution.withinBoundFrontier {α : Type}
    (distribution : Distribution α) (ranges : α → Bound)
    (target : Bound) : List (Classified α) :=
  distribution.classifiedEventFrontier fun item =>
    withinBoundStatus (ranges item) target

/-- Executable event selecting exactly those payloads whose current source
enclosure neither lies wholly inside nor strictly outside the target. -/
def withinBoundUnresolvedEvent {α : Type} (ranges : α → Bound)
    (target : Bound) : α → Bool :=
  unresolvedStatusEvent fun item => withinBoundStatus (ranges item) target

/-- The uncertainty of an interval-membership probability enclosure is
exactly the probability mass of its currently unresolved displayed rows. -/
theorem Distribution.withinBoundFrontier_width {α : Type}
    (distribution : Distribution α) (ranges : α → Bound)
    (target : Bound) :
    (eventBound (distribution.withinBoundFrontier ranges target)).width =
      distribution.probability (withinBoundUnresolvedEvent ranges target) :=
  distribution.classifiedEventFrontier_width _

theorem Distribution.withinBoundClassification_sound
    {α : Type} (distribution : Distribution α) (ranges : α → Bound)
    (target : Bound) (value : α → Coordinate)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).Contains (value atom.item)) :
    ClassificationSoundOn distribution.atoms
      (fun item => withinBoundStatus (ranges item) target)
      (withinBoundEvent target value) := by
  intro atom member
  have admitted := inside atom member
  by_cases whollyInside :
      target.lower ≤ (ranges atom.item).lower ∧
        (ranges atom.item).upper ≤ target.upper
  · simp only [withinBoundStatus, whollyInside,
      Status.AdmitsSelection, withinBoundEvent]
    apply decide_eq_true_eq.mpr
    exact ⟨whollyInside.1.trans admitted.1,
      admitted.2.trans whollyInside.2⟩
  · by_cases separated :
        (ranges atom.item).upper < target.lower ∨
          target.upper < (ranges atom.item).lower
    · simp only [withinBoundStatus, whollyInside, separated, ↓reduceIte,
        Status.AdmitsSelection, withinBoundEvent]
      apply decide_eq_false_iff_not.mpr
      intro selected
      rcases separated with left | right
      · exact left.2 (selected.1.trans admitted.2)
      · exact right.2 (admitted.1.trans selected.2)
    · simp only [withinBoundStatus, whollyInside, separated, ↓reduceIte,
        Status.AdmitsSelection]

/-- Every explicitly admitted rational observable has its exact finite
interval-membership probability inside the computed event enclosure. -/
theorem Distribution.probability_mem_withinBoundFrontier
    {α : Type} (distribution : Distribution α) (ranges : α → Bound)
    (target : Bound) (value : α → Coordinate)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).Contains (value atom.item)) :
    (eventBound (distribution.withinBoundFrontier ranges target)).Contains
      (distribution.probability (withinBoundEvent target value)) :=
  distribution.probability_mem_classifiedEventFrontier
    (fun item => withinBoundStatus (ranges item) target)
    (withinBoundEvent target value)
    (distribution.withinBoundClassification_sound ranges target value inside)

theorem withinBoundStatus_refines {inner outer target : Bound}
    (refines : Bound.Refines inner outer) :
    (withinBoundStatus inner target).Refines
      (withinBoundStatus outer target) := by
  by_cases outerInside :
      target.lower ≤ outer.lower ∧ outer.upper ≤ target.upper
  · have innerInside :
        target.lower ≤ inner.lower ∧ inner.upper ≤ target.upper :=
      ⟨outerInside.1.trans refines.lower,
        refines.upper.trans outerInside.2⟩
    simp [withinBoundStatus, outerInside, innerInside, Status.Refines]
  · by_cases outerOutside :
        outer.upper < target.lower ∨ target.upper < outer.lower
    · have innerOutside :
          inner.upper < target.lower ∨ target.upper < inner.lower := by
        rcases outerOutside with left | right
        · exact Or.inl (refines.upper.trans_lt left)
        · exact Or.inr (right.trans_le refines.lower)
      have innerNotInside :
          ¬(target.lower ≤ inner.lower ∧ inner.upper ≤ target.upper) := by
        intro selected
        rcases innerOutside with left | right
        · exact left.2 (selected.1.trans inner.valid)
        · exact right.2 (inner.valid.trans selected.2)
      simp [withinBoundStatus, outerInside, outerOutside,
        innerNotInside, innerOutside, Status.Refines]
    · simp [withinBoundStatus, outerInside, outerOutside, Status.Refines]

/-- Pointwise finite refinement of source enclosures narrows the computed
interval-membership probability enclosure. -/
theorem Distribution.withinBoundFrontier_eventBound_refines
    {α : Type} (distribution : Distribution α)
    (inner outer : α → Bound) (target : Bound)
    (refines : ∀ atom, atom ∈ distribution.atoms →
      Bound.Refines (inner atom.item) (outer atom.item)) :
    Bound.Refines
      (eventBound (distribution.withinBoundFrontier inner target))
      (eventBound (distribution.withinBoundFrontier outer target)) := by
  unfold withinBoundFrontier
  exact distribution.classifiedEventFrontier_refines
    (fun item => withinBoundStatus (inner item) target)
    (fun item => withinBoundStatus (outer item) target)
    (fun atom member => withinBoundStatus_refines (refines atom member))

/-- A target-membership query is decided throughout one source enclosure. -/
def WithinBoundResolved (range target : Bound) : Prop :=
  (target.lower ≤ range.lower ∧ range.upper ≤ target.upper) ∨
    range.upper < target.lower ∨ target.upper < range.lower

private theorem unresolvedWeight_withinBoundFrontier_eq_zero
    {α : Type} (ranges : α → Bound) (target : Bound) :
    ∀ atoms : List (Weighted α),
      (∀ atom, atom ∈ atoms →
        WithinBoundResolved (ranges atom.item) target) →
      unresolvedWeight (atoms.map fun atom =>
        ⟨atom, withinBoundStatus (ranges atom.item) target⟩) = 0
  | [], _ => rfl
  | atom :: remaining, resolved => by
      have head := resolved atom List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          WithinBoundResolved (ranges candidate.item) target :=
        fun candidate member =>
          resolved candidate (List.mem_cons_of_mem atom member)
      simp only [List.map_cons, unresolvedWeight]
      rw [unresolvedWeight_withinBoundFrontier_eq_zero
        ranges target remaining tail]
      rcases head with whollyInside | separated
      · simp [withinBoundStatus, whollyInside]
      · have notInside :
            ¬(target.lower ≤ (ranges atom.item).lower ∧
              (ranges atom.item).upper ≤ target.upper) := by
          intro selected
          rcases separated with left | right
          · exact left.2 (selected.1.trans (ranges atom.item).valid)
          · exact right.2 ((ranges atom.item).valid.trans selected.2)
        simp [withinBoundStatus, notInside, separated]

/-- If every displayed source enclosure is already wholly inside or strictly
outside the target, the interval-membership probability bound is exact. -/
theorem Distribution.withinBoundFrontier_width_eq_zero_of_resolved
    {α : Type} (distribution : Distribution α)
    (ranges : α → Bound) (target : Bound)
    (resolved : ∀ atom, atom ∈ distribution.atoms →
      WithinBoundResolved (ranges atom.item) target) :
    (eventBound
      (distribution.withinBoundFrontier ranges target)).width = 0 := by
  rw [eventBound_width]
  unfold withinBoundFrontier classifiedEventFrontier classifiedAtomsWith
  exact unresolvedWeight_withinBoundFrontier_eq_zero
    ranges target distribution.atoms resolved

/-- An explicit rational budget on unresolved interval-membership rows is
an accuracy certificate for the complete probability enclosure. -/
theorem Distribution.withinBoundFrontier_width_lt_of_unresolved_budget
    {α : Type} (distribution : Distribution α)
    (ranges : α → Bound) (target : Bound) (epsilon : Coordinate)
    (budget : distribution.probability
      (withinBoundUnresolvedEvent ranges target) < epsilon) :
    (eventBound
      (distribution.withinBoundFrontier ranges target)).width < epsilon := by
  rw [distribution.withinBoundFrontier_width]
  exact budget

namespace PointwiseEnclosureProcess

/-- A pointwise enclosure controller plus one fixed admitted rational
observable gives a sound finite classification process for membership in a
displayed rational target.  Accuracy is charged only to unresolved
probability mass. -/
def toWithinBoundClassificationProcess {α : Type}
    {distribution : Distribution α}
    (process : PointwiseEnclosureProcess distribution)
    (target : Bound) (value : α → Coordinate)
    (admitted : ∀ state atom, atom ∈ distribution.atoms →
      (process.ranges state atom.item).Contains (value atom.item))
    (unresolvedAccurate : ∀ state epsilon positive,
      distribution.probability
        (withinBoundUnresolvedEvent
          (process.ranges (process.request state epsilon positive)) target) <
        epsilon) :
    ClassificationProcess distribution (withinBoundEvent target value) where
  State := process.State
  status state item := withinBoundStatus (process.ranges state item) target
  initial := process.initial
  request := process.request
  sound state := distribution.withinBoundClassification_sound
    (process.ranges state) target value (admitted state)
  request_refines state epsilon positive atom member :=
    withinBoundStatus_refines
      (process.request_refines state epsilon positive atom member)
  accurate := unresolvedAccurate
  refinesInitial state atom member :=
    withinBoundStatus_refines (process.refinesInitial state atom member)

end PointwiseEnclosureProcess

end FiniteMeasure
