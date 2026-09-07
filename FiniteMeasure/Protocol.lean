import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Bounds

/-!
# Finite-request refinement protocols

The structures here retain only finite observations.  They express arbitrary
accuracy, finite satisfiability, monotone refinement, and pairwise shrinking
without constructing a stream, an intersection, or a completed value.
-/

namespace FiniteMeasure

/-- One finitely satisfiable observation with a displayed pairwise spread. -/
structure Observation (α : Type) (distance : α → α → Coordinate) where
  Possible : α → Prop
  witness : α
  witness_possible : Possible witness
  spread : Coordinate
  spread_nonnegative : 0 ≤ spread
  pairwise : ∀ {left right : α}, Possible left → Possible right →
    distance left right ≤ spread

namespace Observation

/-- Transport a finite observation through a displayed sensitivity bound. -/
def map
    {α β : Type} {sourceDistance : α → α → Coordinate}
    {targetDistance : β → β → Coordinate}
    (observation : Observation α sourceDistance)
    (function : α → β) (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      targetDistance (function left) (function right) ≤
        factor * sourceDistance left right) :
    Observation β targetDistance where
  Possible value := ∃ source, observation.Possible source ∧
    value = function source
  witness := function observation.witness
  witness_possible :=
    ⟨observation.witness, observation.witness_possible, rfl⟩
  spread := factor * observation.spread
  spread_nonnegative := RFAP.ConstructiveFraction.mul_nonneg_direct
    nonnegative observation.spread_nonnegative
  pairwise := by
    intro left right leftPossible rightPossible
    rcases leftPossible with ⟨leftSource, leftSourcePossible, rfl⟩
    rcases rightPossible with ⟨rightSource, rightSourcePossible, rfl⟩
    exact (sensitive leftSource rightSource).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (observation.pairwise leftSourcePossible rightSourcePossible)
        nonnegative)

/-- The later finite predicate contains no candidates rejected by the older
predicate. -/
structure Refines {α : Type} {distance : α → α → Coordinate}
    (inner outer : Observation α distance) : Prop where
  possible : ∀ {value : α}, inner.Possible value → outer.Possible value

namespace Refines

theorem refl {α : Type} {distance : α → α → Coordinate}
    (observation : Observation α distance) : Refines observation observation :=
  ⟨fun possible => possible⟩

theorem trans {α : Type} {distance : α → α → Coordinate}
    {inner middle outer : Observation α distance}
    (innerMiddle : Refines inner middle)
    (middleOuter : Refines middle outer) : Refines inner outer :=
  ⟨fun possible => middleOuter.possible (innerMiddle.possible possible)⟩

theorem witness_possible {α : Type} {distance : α → α → Coordinate}
    {inner outer : Observation α distance} (refines : Refines inner outer) :
    outer.Possible inner.witness :=
  refines.possible inner.witness_possible

theorem map
    {α β : Type} {sourceDistance : α → α → Coordinate}
    {targetDistance : β → β → Coordinate}
    {inner outer : Observation α sourceDistance}
    (refines : Refines inner outer)
    (function : α → β) (factor : Coordinate) (nonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      targetDistance (function left) (function right) ≤
        factor * sourceDistance left right) :
    Refines (inner.map function factor nonnegative sensitive)
      (outer.map function factor nonnegative sensitive) := by
  constructor
  rintro value ⟨source, possible, equal⟩
  exact ⟨source, refines.possible possible, equal⟩

end Refines

/-- A chronological finite refinement history, indexed by its latest
observation.  There is no constructor for an infinite history. -/
inductive History {α : Type} {distance : α → α → Coordinate}
    (initial : Observation α distance) : Observation α distance → Type where
  | start : History initial initial
  | step {older newer : Observation α distance} :
      History initial older → Refines newer older → History initial newer

namespace History

/-- The end of a finite history refines its beginning. -/
theorem refines_initial
    {α : Type} {distance : α → α → Coordinate}
    {initial latest : Observation α distance}
    (history : History initial latest) : Refines latest initial := by
  induction history with
  | start => exact Refines.refl initial
  | @step older newer history refines inductionHypothesis =>
      exact refines.trans inductionHypothesis

/-- The latest witness of any finite history satisfies the initial finite
predicate.  This is the inhabited-finite-intersection argument. -/
theorem latest_witness_possible_initial
    {α : Type} {distance : α → α → Coordinate}
    {initial latest : Observation α distance}
    (history : History initial latest) :
    initial.Possible latest.witness := by
  exact history.refines_initial.possible latest.witness_possible

/-- Every candidate admitted at the end of a finite history was admitted at
the beginning. -/
theorem latest_possible_initial
    {α : Type} {distance : α → α → Coordinate}
    {initial latest : Observation α distance}
    (history : History initial latest) {value : α}
    (possible : latest.Possible value) : initial.Possible value := by
  exact history.refines_initial.possible possible

end History

end Observation

/-- An executable arbitrary-accuracy name whose results remain finite
observations. -/
structure ProgressiveObservation (α : Type)
    (distance : α → α → Coordinate) where
  State : Type
  observation : State → Observation α distance
  initial : State
  request : (state : State) → (epsilon : Coordinate) → 0 < epsilon → State
  request_refines : ∀ state epsilon positive,
    Observation.Refines
      (observation (request state epsilon positive)) (observation state)
  accurate : ∀ state epsilon positive,
    (observation (request state epsilon positive)).spread < epsilon
  refinesInitial : ∀ state,
    Observation.Refines (observation state) (observation initial)

namespace ProgressiveObservation

/-- Every two candidates at a requested finite precision meet the displayed
distance request. -/
theorem request_pairwise
    {α : Type} {distance : α → α → Coordinate}
    (name : ProgressiveObservation α distance)
    (state : name.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    {left right : α}
    (leftPossible :
      (name.observation (name.request state epsilon positive)).Possible left)
    (rightPossible :
      (name.observation (name.request state epsilon positive)).Possible right) :
    distance left right < epsilon :=
  (name.observation (name.request state epsilon positive)).pairwise
    leftPossible rightPossible |>.trans_lt
      (name.accurate state epsilon positive)

/-- One request extends any already displayed finite history. -/
def requestHistory
    {α : Type} {distance : α → α → Coordinate}
    (name : ProgressiveObservation α distance)
    {latest : name.State}
    (history : Observation.History
      (name.observation name.initial) (name.observation latest))
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    Observation.History (name.observation name.initial)
      (name.observation (name.request latest epsilon positive)) :=
  .step history (name.request_refines latest epsilon positive)

/-- The witness produced after a finite request remains a candidate at the
displayed initial observation. -/
theorem request_witness_possible_initial
    {α : Type} {distance : α → α → Coordinate}
    (name : ProgressiveObservation α distance)
    (state : name.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    (name.observation name.initial).Possible
      (name.observation (name.request state epsilon positive)).witness :=
  (name.request_refines state epsilon positive).trans
    (name.refinesInitial state) |>.witness_possible

end ProgressiveObservation

/-! ## Rational enclosure processes -/

/-- Finite-request rational bounds, useful for measures, integrals, and tail
budgets.  Coherence is expressed by endpoint refinement, not by a completed
rational or real value. -/
structure BoundProcess where
  State : Type
  bound : State → Bound
  initial : State
  request : (state : State) → (epsilon : Coordinate) → 0 < epsilon → State
  request_refines : ∀ state epsilon positive,
    Bound.Refines (bound (request state epsilon positive)) (bound state)
  accurate : ∀ state epsilon positive,
    (bound (request state epsilon positive)).width < epsilon
  refinesInitial : ∀ state, Bound.Refines (bound state) (bound initial)

namespace BoundProcess

/-- Constant exact rational process, useful as a terminal finite name. -/
def exact (value : Coordinate) : BoundProcess where
  State := Unit
  bound _ := Bound.exact value
  initial := ()
  request state epsilon positive := state
  request_refines state epsilon positive := Bound.Refines.refl _
  accurate state epsilon positive := by
    simpa only [Bound.exact_width] using positive
  refinesInitial state := Bound.Refines.refl _

/-- Additive inverse of a finite rational enclosure process. -/
def neg (process : BoundProcess) : BoundProcess where
  State := process.State
  bound state := (process.bound state).neg
  initial := process.initial
  request := process.request
  request_refines state epsilon positive :=
    (process.request_refines state epsilon positive).neg
  accurate state epsilon positive := by
    rw [Bound.neg_width]
    exact process.accurate state epsilon positive
  refinesInitial state := (process.refinesInitial state).neg

/-- Sum of two finite rational enclosure processes.  Each request allocates
half of its tolerance to each operand. -/
def add (left right : BoundProcess) : BoundProcess where
  State := left.State × right.State
  bound state := (left.bound state.1).add (right.bound state.2)
  initial := ⟨left.initial, right.initial⟩
  request state epsilon positive :=
    let half := epsilon / 2
    let halfPositive := RFAP.ConstructiveFraction.div_pos_direct positive
      (by decide : (0 : Coordinate) < 2)
    ⟨left.request state.1 half halfPositive,
      right.request state.2 half halfPositive⟩
  request_refines state epsilon positive :=
    Bound.Refines.add
      (left.request_refines state.1 (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide)))
      (right.request_refines state.2 (epsilon / 2)
        (RFAP.ConstructiveFraction.div_pos_direct positive (by decide)))
  accurate state epsilon positive := by
    rw [Bound.add_width]
    have halfPositive : (0 : Coordinate) < epsilon / 2 :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    have leftSmall := left.accurate state.1 (epsilon / 2) halfPositive
    have rightSmall := right.accurate state.2 (epsilon / 2) halfPositive
    calc
      (left.bound (left.request state.1 (epsilon / 2) halfPositive)).width +
          (right.bound
            (right.request state.2 (epsilon / 2) halfPositive)).width <
          epsilon / 2 + epsilon / 2 :=
        RFAP.ConstructiveFraction.add_lt_add_direct leftSmall rightSmall
      _ = epsilon := by
        calc
          epsilon / 2 + epsilon / 2 = (epsilon / 2) * 2 := by ring1
          _ = epsilon :=
            RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon 2
              (by decide)
  refinesInitial state :=
    Bound.Refines.add (left.refinesInitial state.1)
      (right.refinesInitial state.2)

/-- Difference of two finite rational enclosure processes. -/
def sub (left right : BoundProcess) : BoundProcess :=
  left.add right.neg

/-- Positive rational scaling of a finite enclosure process. -/
def scalePositive (process : BoundProcess) (factor : Coordinate)
    (positive : 0 < factor) : BoundProcess where
  State := process.State
  bound state := (process.bound state).scale factor positive.le
  initial := process.initial
  request state epsilon epsilonPositive :=
    process.request state (epsilon / factor)
      (RFAP.ConstructiveFraction.div_pos_direct epsilonPositive positive)
  request_refines state epsilon epsilonPositive :=
    Bound.Refines.scale factor positive.le
      (process.request_refines state (epsilon / factor)
        (RFAP.ConstructiveFraction.div_pos_direct epsilonPositive positive))
  accurate state epsilon epsilonPositive := by
    rw [Bound.scale_width]
    have requestPositive : (0 : Coordinate) < epsilon / factor :=
      RFAP.ConstructiveFraction.div_pos_direct epsilonPositive positive
    have small := process.accurate state (epsilon / factor) requestPositive
    have scaled :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct positive small
    calc
      factor *
          (process.bound
            (process.request state (epsilon / factor) requestPositive)).width <
          factor * (epsilon / factor) := scaled
      _ = epsilon := by
        calc
          factor * (epsilon / factor) = (epsilon / factor) * factor := by ring1
          _ = epsilon :=
            RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon factor
              positive.ne'
  refinesInitial state :=
    Bound.Refines.scale factor positive.le (process.refinesInitial state)

theorem request_refines_initial (process : BoundProcess)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    Bound.Refines
      (process.bound (process.request state epsilon positive))
      (process.bound process.initial) :=
  (process.request_refines state epsilon positive).trans
    (process.refinesInitial state)

/-- Any two explicitly supplied rational values admitted by the same finite
request differ by less than the requested tolerance in both directions. -/
theorem request_pairwise_difference_lt (process : BoundProcess)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    {left right : Coordinate}
    (leftInside :
      (process.bound (process.request state epsilon positive)).Contains left)
    (rightInside :
      (process.bound (process.request state epsilon positive)).Contains right) :
    left - right < epsilon ∧ right - left < epsilon := by
  have pairwise := Bound.pairwise_difference_le leftInside rightInside
  exact ⟨pairwise.1.trans_lt (process.accurate state epsilon positive),
    pairwise.2.trans_lt (process.accurate state epsilon positive)⟩

/-- Execute one finite request and return its canonical rational endpoint
representative. -/
def approximate (process : BoundProcess) (state : process.State)
    (epsilon : Coordinate) (positive : 0 < epsilon) : Coordinate :=
  (process.bound (process.request state epsilon positive)).sample

theorem approximate_inside (process : BoundProcess)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    (process.bound (process.request state epsilon positive)).Contains
      (process.approximate state epsilon positive) :=
  (process.bound (process.request state epsilon positive)).sample_contains

/-- Every rational still admitted by the requested finite enclosure is
within the request tolerance of the computed rational representative. -/
theorem candidate_close_to_approximate (process : BoundProcess)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    {candidate : Coordinate}
    (inside :
      (process.bound (process.request state epsilon positive)).Contains
        candidate) :
    candidate - process.approximate state epsilon positive < epsilon ∧
      process.approximate state epsilon positive - candidate < epsilon :=
  process.request_pairwise_difference_lt state epsilon positive inside
    (process.approximate_inside state epsilon positive)

end BoundProcess

end FiniteMeasure
