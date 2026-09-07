import FiniteMeasure.Probability
import FiniteMeasure.Schedule

/-!
# Sound finite event classifications

A three-way status table becomes a probability enclosure once its inside and
outside claims are certified against one executable event.  Unresolved rows
need no claim; their exact rational weight is the complete error budget.
-/

namespace FiniteMeasure

namespace Status

/-- A status is compatible with the actual Boolean selection of its row. -/
def AdmitsSelection (status : Status) (selected : Bool) : Prop :=
  match status with
  | .inside => selected = true
  | .outside => selected = false
  | .unresolved => True

end Status

/-- Attach one supplied status function to every row of a weighted table. -/
def classifiedAtomsWith {α : Type} (atoms : List (Weighted α))
    (status : α → Status) : List (Classified α) :=
  atoms.map fun atom => ⟨atom, status atom.item⟩

/-- Soundness of a status function for an executable event, required only on
the displayed finite atom table. -/
def ClassificationSoundOn {α : Type} (atoms : List (Weighted α))
    (status : α → Status) (event : α → Bool) : Prop :=
  ∀ atom, atom ∈ atoms →
    (status atom.item).AdmitsSelection (event atom.item)

/-- Executable event selecting exactly those payloads whose current status
is unresolved. -/
def unresolvedStatusEvent {α : Type} (status : α → Status) : α → Bool :=
  fun item => decide (status item = .unresolved)

/-- The unresolved rational weight of a classified table is exactly the
selected weight of its executable unresolved-status event. -/
theorem unresolvedWeight_classifiedAtomsWith {α : Type}
    (status : α → Status) : ∀ atoms : List (Weighted α),
    unresolvedWeight (classifiedAtomsWith atoms status) =
      eventWeight atoms (unresolvedStatusEvent status)
  | [] => rfl
  | atom :: remaining => by
      have tail := unresolvedWeight_classifiedAtomsWith status remaining
      have mappedTail :
          unresolvedWeight
              (remaining.map fun candidate =>
                (⟨candidate, status candidate.item⟩ : Classified α)) =
            eventWeight remaining (unresolvedStatusEvent status) := by
        simpa only [classifiedAtomsWith] using tail
      cases current : status atom.item <;>
        simp [classifiedAtomsWith, unresolvedWeight, eventWeight,
          unresolvedStatusEvent, current] <;>
        exact mappedTail

/-- A sound finite classification encloses the exact selected weight between
its lower and upper rational sums. -/
theorem eventWeight_mem_eventBound_of_classification
    {α : Type} (status : α → Status) (event : α → Bool) :
    ∀ atoms : List (Weighted α),
      ClassificationSoundOn atoms status event →
      (eventBound (classifiedAtomsWith atoms status)).Contains
        (eventWeight atoms event)
  | [], _ => ⟨le_rfl, le_rfl⟩
  | atom :: remaining, sound => by
      change lowerWeight (classifiedAtomsWith (atom :: remaining) status) ≤
          eventWeight (atom :: remaining) event ∧
        eventWeight (atom :: remaining) event ≤
          upperWeight (classifiedAtomsWith (atom :: remaining) status)
      have head := sound atom List.mem_cons_self
      have tailSound : ClassificationSoundOn remaining status event :=
        fun candidate member =>
          sound candidate (List.mem_cons_of_mem atom member)
      have tail := eventWeight_mem_eventBound_of_classification
        status event remaining tailSound
      cases current : status atom.item with
      | inside =>
          have selected : event atom.item = true := by
            simpa only [Status.AdmitsSelection, current] using head
          simp only [classifiedAtomsWith, List.map_cons, lowerWeight,
            upperWeight, eventWeight, current, selected]
          exact ⟨add_le_add le_rfl tail.1, add_le_add le_rfl tail.2⟩
      | outside =>
          have selected : event atom.item = false := by
            simpa only [Status.AdmitsSelection, current] using head
          simp only [classifiedAtomsWith, List.map_cons, lowerWeight,
            upperWeight, eventWeight, current, selected, zero_add]
          exact tail
      | unresolved =>
          cases selected : event atom.item
          · simp only [classifiedAtomsWith, List.map_cons, lowerWeight,
              upperWeight, eventWeight, current, selected, zero_add]
            exact ⟨tail.1,
              tail.2.trans (le_add_of_nonneg_left atom.nonnegative)⟩
          · simp only [classifiedAtomsWith, List.map_cons, lowerWeight,
              upperWeight, eventWeight, current, selected, zero_add]
            exact ⟨tail.1.trans
                (le_add_of_nonneg_left atom.nonnegative),
              add_le_add le_rfl tail.2⟩

private theorem singleton_classified_eventBound_refines {α : Type}
    (atom : Weighted α) (inner outer : Status)
    (refines : inner.Refines outer) :
    Bound.Refines (eventBound [⟨atom, inner⟩])
      (eventBound [⟨atom, outer⟩]) := by
  let replacement : Split (⟨atom, outer⟩ : Classified α) :=
    { children := [⟨atom, inner⟩]
      conserved := by
        simp only [classifiedWeight, add_zero]
      statuses := by
        intro child member
        simp only [List.mem_singleton] at member
        rw [member]
        exact refines }
  exact replacement.eventBound_refines

/-- Pointwise status refinement narrows the lower/upper bound of a
classification on the same displayed finite atom table. -/
theorem eventBound_classifiedAtomsWith_refines {α : Type}
    (inner outer : α → Status) :
    ∀ atoms : List (Weighted α),
      (∀ atom, atom ∈ atoms →
        (inner atom.item).Refines (outer atom.item)) →
      Bound.Refines
        (eventBound (classifiedAtomsWith atoms inner))
        (eventBound (classifiedAtomsWith atoms outer))
  | [], _ => Bound.Refines.refl _
  | atom :: remaining, refines => by
      have head := singleton_classified_eventBound_refines atom
        (inner atom.item) (outer atom.item)
        (refines atom List.mem_cons_self)
      have tail := eventBound_classifiedAtomsWith_refines
        inner outer remaining (fun candidate member =>
          refines candidate (List.mem_cons_of_mem atom member))
      have combined := Bound.Refines.add head tail
      rw [← eventBound_append [⟨atom, inner atom.item⟩]
          (classifiedAtomsWith remaining inner),
        ← eventBound_append [⟨atom, outer atom.item⟩]
          (classifiedAtomsWith remaining outer)] at combined
      simpa only [classifiedAtomsWith, List.map_cons,
        List.singleton_append] using combined

namespace Distribution

/-- Classify each displayed row of a finite distribution. -/
def classifiedEventFrontier {α : Type} (distribution : Distribution α)
    (status : α → Status) : List (Classified α) :=
  classifiedAtomsWith distribution.atoms status

theorem classifiedEventFrontier_refines {α : Type}
    (distribution : Distribution α) (inner outer : α → Status)
    (refines : ∀ atom, atom ∈ distribution.atoms →
      (inner atom.item).Refines (outer atom.item)) :
    Bound.Refines
      (eventBound (distribution.classifiedEventFrontier inner))
      (eventBound (distribution.classifiedEventFrontier outer)) :=
  eventBound_classifiedAtomsWith_refines
    inner outer distribution.atoms refines

/-- The width of a finite classification bound is exactly the probability
mass of its currently unresolved displayed rows. -/
theorem classifiedEventFrontier_width {α : Type}
    (distribution : Distribution α) (status : α → Status) :
    (eventBound (distribution.classifiedEventFrontier status)).width =
      distribution.probability (unresolvedStatusEvent status) := by
  rw [eventBound_width]
  exact unresolvedWeight_classifiedAtomsWith status distribution.atoms

/-- A sound classifier's lower/upper event bound contains the exact rational
probability of its executable event. -/
theorem probability_mem_classifiedEventFrontier
    {α : Type} (distribution : Distribution α)
    (status : α → Status) (event : α → Bool)
    (sound : ClassificationSoundOn distribution.atoms status event) :
    (eventBound (distribution.classifiedEventFrontier status)).Contains
      (distribution.probability event) :=
  eventWeight_mem_eventBound_of_classification
    status event distribution.atoms sound

end Distribution

/-! ## Arbitrarily accurate finite classifications -/

/-- An executable controller for repeatedly classifying the fixed rows of one
finite distribution against one fixed Boolean event.  Every state is sound;
a request must reduce the exact rational mass of unresolved rows below the
supplied positive rational tolerance.  No sequence or limiting event is part
of the data. -/
structure ClassificationProcess {α : Type}
    (distribution : Distribution α) (event : α → Bool) where
  State : Type
  status : State → α → Status
  initial : State
  request : (state : State) → (epsilon : Coordinate) → 0 < epsilon → State
  sound : ∀ state,
    ClassificationSoundOn distribution.atoms (status state) event
  request_refines : ∀ state epsilon positive atom,
    atom ∈ distribution.atoms →
      (status (request state epsilon positive) atom.item).Refines
        (status state atom.item)
  accurate : ∀ state epsilon positive,
    distribution.probability
      (unresolvedStatusEvent (status (request state epsilon positive))) <
        epsilon
  refinesInitial : ∀ state atom, atom ∈ distribution.atoms →
    (status state atom.item).Refines (status initial atom.item)

namespace ClassificationProcess

/-- Forget the row statuses only after retaining their certified rational
probability enclosure. -/
def toBoundProcess {α : Type} {distribution : Distribution α}
    {event : α → Bool}
    (process : ClassificationProcess distribution event) : BoundProcess where
  State := process.State
  bound state := eventBound
    (distribution.classifiedEventFrontier (process.status state))
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    distribution.classifiedEventFrontier_refines
      (process.status (process.request state epsilon positive))
      (process.status state)
      (process.request_refines state epsilon positive)
  accurate state epsilon positive := by
    rw [distribution.classifiedEventFrontier_width]
    exact process.accurate state epsilon positive
  refinesInitial state :=
    distribution.classifiedEventFrontier_refines
      (process.status state) (process.status process.initial)
      (process.refinesInitial state)

/-- At every displayed finite state, the computed lower and upper rational
weights contain the exact probability of the fixed executable event. -/
theorem probability_mem_bound {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : ClassificationProcess distribution event)
    (state : process.State) :
    (process.toBoundProcess.bound state).Contains
      (distribution.probability event) :=
  distribution.probability_mem_classifiedEventFrontier
    (process.status state) event (process.sound state)

/-- One finite accuracy request returns an entirely rational representative
within the requested tolerance of the exact finite event probability. -/
theorem probability_close_to_approximation {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : ClassificationProcess distribution event)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    distribution.probability event -
          process.toBoundProcess.approximate state epsilon positive < epsilon ∧
      process.toBoundProcess.approximate state epsilon positive -
          distribution.probability event < epsilon :=
  process.toBoundProcess.candidate_close_to_approximate
    state epsilon positive
    (process.probability_mem_bound
      (process.request state epsilon positive))

/-- The complete uncertainty after a request is not merely bounded by, but
is exactly, the rational probability mass still labelled unresolved. -/
theorem requested_width_eq_unresolved_probability {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : ClassificationProcess distribution event)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    (process.toBoundProcess.bound
      (process.request state epsilon positive)).width =
        distribution.probability
          (unresolvedStatusEvent
            (process.status (process.request state epsilon positive))) :=
  distribution.classifiedEventFrontier_width _

/-- Execute a displayed finite list of classification-accuracy requests. -/
def runRequests {α : Type} {distribution : Distribution α}
    {event : α → Bool}
    (process : ClassificationProcess distribution event)
    (state : process.State) (requests : List AccuracyRequest) : process.State :=
  process.toBoundProcess.runRequests state requests

/-- The canonical rational representative computed from the final status
table of a displayed finite request batch. -/
def runRequestsApproximation {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : ClassificationProcess distribution event)
    (state : process.State) (requests : List AccuracyRequest) : Coordinate :=
  process.toBoundProcess.runRequestsApproximation state requests

/-- One final finite status table has unresolved probability below every
tolerance explicitly present in the finite request batch. -/
theorem runRequests_unresolved_probability_lt_of_mem {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : ClassificationProcess distribution event)
    (state : process.State) (requests : List AccuracyRequest)
    (request : AccuracyRequest) (member : request ∈ requests) :
    distribution.probability
        (unresolvedStatusEvent
          (process.status (process.runRequests state requests))) <
      request.tolerance := by
  have accurate := process.toBoundProcess.runRequests_width_lt_of_mem
    state requests request member
  change (eventBound (distribution.classifiedEventFrontier
    (process.status (process.runRequests state requests)))).width <
      request.tolerance at accurate
  rw [distribution.classifiedEventFrontier_width] at accurate
  exact accurate

/-- The one rational representative from a finite request batch is close to
the exact event probability at every tolerance appearing in that batch. -/
theorem runRequests_probability_close_to_approximation_of_mem {α : Type}
    {distribution : Distribution α} {event : α → Bool}
    (process : ClassificationProcess distribution event)
    (state : process.State) (requests : List AccuracyRequest)
    (request : AccuracyRequest) (member : request ∈ requests) :
    distribution.probability event -
          process.runRequestsApproximation state requests <
        request.tolerance ∧
      process.runRequestsApproximation state requests -
          distribution.probability event < request.tolerance := by
  exact process.toBoundProcess
    |>.runRequests_candidate_close_to_approximation_of_mem
      state requests request member
      (process.probability_mem_bound
        (process.runRequests state requests))

end ClassificationProcess

end FiniteMeasure
