import FiniteMeasure.EnclosedExpectation
import FiniteMeasure.ClassifiedProbability

/-!
# Threshold events from finite rational enclosures

Pointwise rational enclosures can decide some threshold comparisons and leave
the rest explicitly unresolved.  The resulting lower and upper probability
sums contain the exact threshold probability of every rational observable
admitted by the displayed enclosures.  Refining the enclosures narrows the
probability bound.
-/

namespace FiniteMeasure

/-- Classify a rational enclosure relative to a displayed lower-threshold
event. -/
def thresholdStatus (range : Bound) (threshold : Coordinate) : Status :=
  if threshold ≤ range.lower then .inside
  else if range.upper < threshold then .outside
  else .unresolved

/-- Executable event that a displayed rational observable meets a lower
threshold. -/
def atLeastEvent {α : Type} (threshold : Coordinate)
    (value : α → Coordinate) : α → Bool :=
  fun item => decide (threshold ≤ value item)

/-- Classify every atom of a finite distribution using only its current
rational enclosure. -/
def Distribution.thresholdFrontier {α : Type}
    (distribution : Distribution α) (ranges : α → Bound)
    (threshold : Coordinate) : List (Classified α) :=
  distribution.classifiedEventFrontier fun item =>
    thresholdStatus (ranges item) threshold

theorem Distribution.thresholdClassification_sound
    {α : Type} (distribution : Distribution α) (ranges : α → Bound)
    (threshold : Coordinate) (value : α → Coordinate)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).Contains (value atom.item)) :
    ClassificationSoundOn distribution.atoms
      (fun item => thresholdStatus (ranges item) threshold)
      (atLeastEvent threshold value) := by
  intro atom member
  have admitted := inside atom member
  by_cases definitelyInside : threshold ≤ (ranges atom.item).lower
  · simp only [thresholdStatus, definitelyInside, ↓reduceIte,
      Status.AdmitsSelection]
    exact decide_eq_true_eq.mpr (definitelyInside.trans admitted.1)
  · by_cases definitelyOutside : (ranges atom.item).upper < threshold
    · simp only [thresholdStatus, definitelyInside, definitelyOutside,
        ↓reduceIte, Status.AdmitsSelection]
      apply decide_eq_false_iff_not.mpr
      intro selected
      exact definitelyOutside.2 (selected.trans admitted.2)
    · simp only [thresholdStatus, definitelyInside, definitelyOutside,
        ↓reduceIte, Status.AdmitsSelection]

/-- Every rational observable admitted pointwise by the current enclosures
has its exact threshold probability inside the computed event bound. -/
theorem Distribution.probability_mem_thresholdFrontier
    {α : Type} (distribution : Distribution α) (ranges : α → Bound)
    (threshold : Coordinate) (value : α → Coordinate)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (ranges atom.item).Contains (value atom.item)) :
    (eventBound (distribution.thresholdFrontier ranges threshold)).Contains
      (distribution.probability (atLeastEvent threshold value)) := by
  exact distribution.probability_mem_classifiedEventFrontier
    (fun item => thresholdStatus (ranges item) threshold)
    (atLeastEvent threshold value)
    (distribution.thresholdClassification_sound
      ranges threshold value inside)

theorem thresholdStatus_refines {inner outer : Bound}
    {threshold : Coordinate} (refines : Bound.Refines inner outer) :
    (thresholdStatus inner threshold).Refines
      (thresholdStatus outer threshold) := by
  by_cases outerInside : threshold ≤ outer.lower
  · have innerInside : threshold ≤ inner.lower :=
      outerInside.trans refines.lower
    simp [thresholdStatus, outerInside, innerInside, Status.Refines]
  · by_cases outerOutside : outer.upper < threshold
    · have innerOutside : inner.upper < threshold :=
        refines.upper.trans_lt outerOutside
      have innerNotInside : ¬threshold ≤ inner.lower := by
        intro selected
        exact innerOutside.2 (selected.trans inner.valid)
      simp [thresholdStatus, outerInside, outerOutside,
        innerNotInside, innerOutside, Status.Refines]
    · simp [thresholdStatus, outerInside, outerOutside, Status.Refines]

/-- Pointwise refinement of rational enclosures narrows their computed
threshold-probability enclosure. -/
theorem Distribution.thresholdFrontier_eventBound_refines
    {α : Type} (distribution : Distribution α)
    (inner outer : α → Bound) (threshold : Coordinate)
    (refines : ∀ atom, atom ∈ distribution.atoms →
      Bound.Refines (inner atom.item) (outer atom.item)) :
    Bound.Refines
      (eventBound (distribution.thresholdFrontier inner threshold))
      (eventBound (distribution.thresholdFrontier outer threshold)) := by
  unfold thresholdFrontier
  exact distribution.classifiedEventFrontier_refines
    (fun item => thresholdStatus (inner item) threshold)
    (fun item => thresholdStatus (outer item) threshold)
    (fun atom member =>
      thresholdStatus_refines (refines atom member))

/-- The lower endpoint of a threshold frontier is exactly the mass of rows
whose displayed lower enclosure endpoint meets the threshold. -/
theorem Distribution.thresholdFrontier_lower_eq_probability_lower
    {α : Type} (distribution : Distribution α) (ranges : α → Bound)
    (threshold : Coordinate) :
    (eventBound (distribution.thresholdFrontier ranges threshold)).lower =
      distribution.probability
        (fun item => decide (threshold ≤ (ranges item).lower)) := by
  unfold thresholdFrontier classifiedEventFrontier classifiedAtomsWith
    probability
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have tailIH :
          lowerWeight (List.map (fun candidate =>
            (⟨candidate, thresholdStatus (ranges candidate.item) threshold⟩ :
              Classified α)) remaining) =
            eventWeight remaining
              (fun item => decide (threshold ≤ (ranges item).lower)) := by
        simpa only [eventBound] using inductionHypothesis
      by_cases inside : threshold ≤ (ranges atom.item).lower
      · have headStatus :
            (fun item => thresholdStatus (ranges item) threshold) atom.item =
              .inside := by
          simp only [thresholdStatus, inside, ↓reduceIte]
        rw [List.map_cons, headStatus]
        simp only [eventBound, lowerWeight, eventWeight, inside, decide_true,
          tailIH]
      · by_cases outside : (ranges atom.item).upper < threshold
        · have headStatus :
              (fun item => thresholdStatus (ranges item) threshold) atom.item =
                .outside := by
            simp only [thresholdStatus, inside, outside, ↓reduceIte]
          rw [List.map_cons, headStatus]
          simp only [eventBound, lowerWeight, eventWeight, inside,
            decide_false, zero_add, tailIH]
        · have headStatus :
              (fun item => thresholdStatus (ranges item) threshold) atom.item =
                .unresolved := by
            simp only [thresholdStatus, inside, outside, ↓reduceIte]
          rw [List.map_cons, headStatus]
          simp only [eventBound, lowerWeight, eventWeight, inside,
            decide_false, zero_add, tailIH]

/-- The upper endpoint of a threshold frontier is exactly the mass of rows
whose displayed upper enclosure endpoint meets the threshold. -/
theorem Distribution.thresholdFrontier_upper_eq_probability_upper
    {α : Type} (distribution : Distribution α) (ranges : α → Bound)
    (threshold : Coordinate) :
    (eventBound (distribution.thresholdFrontier ranges threshold)).upper =
      distribution.probability
        (fun item => decide (threshold ≤ (ranges item).upper)) := by
  unfold thresholdFrontier classifiedEventFrontier classifiedAtomsWith
    probability
  induction distribution.atoms with
  | nil => rfl
  | cons atom remaining inductionHypothesis =>
      have tailIH :
          upperWeight (List.map (fun candidate =>
            (⟨candidate, thresholdStatus (ranges candidate.item) threshold⟩ :
              Classified α)) remaining) =
            eventWeight remaining
              (fun item => decide (threshold ≤ (ranges item).upper)) := by
        simpa only [eventBound] using inductionHypothesis
      by_cases inside : threshold ≤ (ranges atom.item).lower
      · have upper : threshold ≤ (ranges atom.item).upper :=
          inside.trans (ranges atom.item).valid
        have headStatus :
            (fun item => thresholdStatus (ranges item) threshold) atom.item =
              .inside := by
          simp only [thresholdStatus, inside, ↓reduceIte]
        rw [List.map_cons, headStatus]
        simp only [eventBound, upperWeight, eventWeight, upper, decide_true,
          tailIH]
      · by_cases outside : (ranges atom.item).upper < threshold
        · have notUpper : ¬threshold ≤ (ranges atom.item).upper := outside.2
          have headStatus :
              (fun item => thresholdStatus (ranges item) threshold) atom.item =
                .outside := by
            simp only [thresholdStatus, inside, outside, ↓reduceIte]
          rw [List.map_cons, headStatus]
          simp only [eventBound, upperWeight, eventWeight, notUpper,
            decide_false, zero_add, tailIH]
        · have upper : threshold ≤ (ranges atom.item).upper :=
            RFAP.ConstructiveFraction.le_of_not_gt_direct outside
          have headStatus :
              (fun item => thresholdStatus (ranges item) threshold) atom.item =
                .unresolved := by
            simp only [thresholdStatus, inside, outside, ↓reduceIte]
          rw [List.map_cons, headStatus]
          simp only [eventBound, upperWeight, eventWeight, upper, decide_true,
            tailIH]

/-- Raising a lower threshold can only decrease the lower endpoint of its
finite probability enclosure. -/
theorem Distribution.thresholdFrontier_lower_anti
    {α : Type} (distribution : Distribution α) (ranges : α → Bound)
    {lower upper : Coordinate} (order : lower ≤ upper) :
    (eventBound (distribution.thresholdFrontier ranges upper)).lower ≤
      (eventBound (distribution.thresholdFrontier ranges lower)).lower := by
  rw [distribution.thresholdFrontier_lower_eq_probability_lower,
    distribution.thresholdFrontier_lower_eq_probability_lower]
  apply eventWeight_mono
  intro atom member selected
  have upperLe : upper ≤ (ranges atom.item).lower :=
    of_decide_eq_true selected
  exact decide_eq_true_eq.mpr (order.trans upperLe)

/-- Raising a lower threshold can only decrease the upper endpoint of its
finite probability enclosure. -/
theorem Distribution.thresholdFrontier_upper_anti
    {α : Type} (distribution : Distribution α) (ranges : α → Bound)
    {lower upper : Coordinate} (order : lower ≤ upper) :
    (eventBound (distribution.thresholdFrontier ranges upper)).upper ≤
      (eventBound (distribution.thresholdFrontier ranges lower)).upper := by
  rw [distribution.thresholdFrontier_upper_eq_probability_upper,
    distribution.thresholdFrontier_upper_eq_probability_upper]
  apply eventWeight_mono
  intro atom member selected
  have upperLe : upper ≤ (ranges atom.item).upper :=
    of_decide_eq_true selected
  exact decide_eq_true_eq.mpr (order.trans upperLe)

/-- A threshold is already decided throughout one displayed enclosure. -/
def ThresholdResolved (range : Bound) (threshold : Coordinate) : Prop :=
  threshold ≤ range.lower ∨ range.upper < threshold

private theorem unresolvedWeight_thresholdFrontier_eq_zero
    {α : Type} (ranges : α → Bound) (threshold : Coordinate) :
    ∀ atoms : List (Weighted α),
      (∀ atom, atom ∈ atoms →
        ThresholdResolved (ranges atom.item) threshold) →
      unresolvedWeight (atoms.map fun atom =>
        ⟨atom, thresholdStatus (ranges atom.item) threshold⟩) = 0
  | [], _ => rfl
  | atom :: remaining, resolved => by
      have head := resolved atom List.mem_cons_self
      have tail : ∀ candidate, candidate ∈ remaining →
          ThresholdResolved (ranges candidate.item) threshold :=
        fun candidate member =>
          resolved candidate (List.mem_cons_of_mem atom member)
      simp only [List.map_cons, unresolvedWeight]
      rw [unresolvedWeight_thresholdFrontier_eq_zero
        ranges threshold remaining tail]
      rcases head with definitelyInside | definitelyOutside
      · simp [thresholdStatus, definitelyInside]
      · have notInside : ¬threshold ≤ (ranges atom.item).lower := by
          intro selected
          exact definitelyOutside.2
            (selected.trans (ranges atom.item).valid)
        simp [thresholdStatus, notInside, definitelyOutside]

theorem Distribution.thresholdFrontier_unresolvedWeight_eq_zero
    {α : Type} (distribution : Distribution α)
    (ranges : α → Bound) (threshold : Coordinate)
    (resolved : ∀ atom, atom ∈ distribution.atoms →
      ThresholdResolved (ranges atom.item) threshold) :
    unresolvedWeight (distribution.thresholdFrontier ranges threshold) = 0 := by
  unfold thresholdFrontier
  exact unresolvedWeight_thresholdFrontier_eq_zero
    ranges threshold distribution.atoms resolved

theorem Distribution.thresholdFrontier_width_eq_zero_of_resolved
    {α : Type} (distribution : Distribution α)
    (ranges : α → Bound) (threshold : Coordinate)
    (resolved : ∀ atom, atom ∈ distribution.atoms →
      ThresholdResolved (ranges atom.item) threshold) :
    (eventBound (distribution.thresholdFrontier ranges threshold)).width = 0 := by
  rw [eventBound_width,
    distribution.thresholdFrontier_unresolvedWeight_eq_zero
      ranges threshold resolved]

namespace PointwiseEnclosureProcess

/-- A pointwise enclosure controller plus a fixed admitted rational
observable gives a sound finite classification process for one threshold.
The supplied accuracy condition concerns only the probability mass still
unresolved, so low-weight ambiguous rows need not all be decided. -/
def toThresholdClassificationProcess {α : Type}
    {distribution : Distribution α}
    (process : PointwiseEnclosureProcess distribution)
    (threshold : Coordinate) (value : α → Coordinate)
    (admitted : ∀ state atom, atom ∈ distribution.atoms →
      (process.ranges state atom.item).Contains (value atom.item))
    (unresolvedAccurate : ∀ state epsilon positive,
      distribution.probability
        (unresolvedStatusEvent fun item =>
          thresholdStatus
            (process.ranges (process.request state epsilon positive) item)
            threshold) < epsilon) :
    ClassificationProcess distribution (atLeastEvent threshold value) where
  State := process.State
  status state item := thresholdStatus (process.ranges state item) threshold
  initial := process.initial
  request := process.request
  sound state := distribution.thresholdClassification_sound
    (process.ranges state) threshold value (admitted state)
  request_refines state epsilon positive atom member :=
    thresholdStatus_refines
      (process.request_refines state epsilon positive atom member)
  accurate := unresolvedAccurate
  refinesInitial state atom member :=
    thresholdStatus_refines (process.refinesInitial state atom member)

/-- If every pointwise request resolves a displayed threshold on every
displayed atom, the same finite requests form a rational bound process for
that threshold probability. -/
def toThresholdBoundProcess {α : Type}
    {distribution : Distribution α}
    (process : PointwiseEnclosureProcess distribution)
    (threshold : Coordinate)
    (requestResolved : ∀ state epsilon positive atom,
      atom ∈ distribution.atoms →
        ThresholdResolved
          (process.ranges (process.request state epsilon positive) atom.item)
          threshold) : BoundProcess where
  State := process.State
  bound state := eventBound
    (distribution.thresholdFrontier (process.ranges state) threshold)
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    distribution.thresholdFrontier_eventBound_refines
      (process.ranges (process.request state epsilon positive))
      (process.ranges state) threshold
      (process.request_refines state epsilon positive)
  accurate state epsilon positive := by
    rw [distribution.thresholdFrontier_width_eq_zero_of_resolved]
    · exact positive
    · exact requestResolved state epsilon positive
  refinesInitial state :=
    distribution.thresholdFrontier_eventBound_refines
      (process.ranges state) (process.ranges process.initial) threshold
      (process.refinesInitial state)

/-- An admitted rational observable supplies an admitted exact probability
at every finite state of the threshold process. -/
theorem probability_mem_thresholdBound {α : Type}
    {distribution : Distribution α}
    (process : PointwiseEnclosureProcess distribution)
    (threshold : Coordinate)
    (requestResolved : ∀ state epsilon positive atom,
      atom ∈ distribution.atoms →
        ThresholdResolved
          (process.ranges (process.request state epsilon positive) atom.item)
          threshold)
    (state : process.State) (value : α → Coordinate)
    (inside : ∀ atom, atom ∈ distribution.atoms →
      (process.ranges state atom.item).Contains (value atom.item)) :
    ((process.toThresholdBoundProcess threshold requestResolved).bound state).Contains
      (distribution.probability (atLeastEvent threshold value)) :=
  distribution.probability_mem_thresholdFrontier
    (process.ranges state) threshold value inside

end PointwiseEnclosureProcess

end FiniteMeasure
