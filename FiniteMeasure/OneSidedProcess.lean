import FiniteMeasure.Protocol

/-!
# One-sided rational refinement processes

These processes expose improving rational evidence without postulating a
hidden endpoint.  A lower process only promises increasing lower bounds, and
an upper process only promises decreasing upper bounds.  In particular,
neither structure contains an accuracy request or a convergence claim.

A `LocatedPair` is deliberately stronger: it supplies a finite request which
puts one lower observation and one upper observation within an explicitly
requested positive rational gap.  Only at that boundary do the observations
become an ordinary two-sided `BoundProcess`.
-/

namespace FiniteMeasure

/-- Executable increasing rational lower evidence.  Every state supplied by
the process is compatible with its displayed initial lower bound, but no rate
of increase and no limiting value are part of the data. -/
structure LowerProcess where
  State : Type
  bound : State → Coordinate
  initial : State
  refine : State → State
  monotone : ∀ state, bound state ≤ bound (refine state)
  refinesInitial : ∀ state, bound initial ≤ bound state

/-- Executable decreasing rational upper evidence.  Every state supplied by
the process is compatible with its displayed initial upper bound, but no rate
of decrease and no limiting value are part of the data. -/
structure UpperProcess where
  State : Type
  bound : State → Coordinate
  initial : State
  refine : State → State
  antitone : ∀ state, bound (refine state) ≤ bound state
  refinesInitial : ∀ state, bound state ≤ bound initial

namespace LowerProcess

/-- The newer lower observation contains at least the evidence in the older
one. -/
def Refines (process : LowerProcess)
    (newer older : process.State) : Prop :=
  process.bound older ≤ process.bound newer

namespace Refines

theorem refl (process : LowerProcess) (state : process.State) :
    process.Refines state state :=
  le_rfl

theorem trans {process : LowerProcess} {newest newer older : process.State}
    (newestNewer : process.Refines newest newer)
    (newerOlder : process.Refines newer older) :
    process.Refines newest older := by
  change process.bound older ≤ process.bound newest
  exact le_trans newerOlder newestNewer

end Refines

/-- Perform exactly the displayed finite number of lower refinements. -/
def advance (process : LowerProcess) : Nat → process.State → process.State
  | 0, state => state
  | count + 1, state => process.refine (advance process count state)

@[simp] theorem advance_zero (process : LowerProcess) (state : process.State) :
    process.advance 0 state = state :=
  rfl

theorem advance_succ (process : LowerProcess) (count : Nat)
    (state : process.State) :
    process.advance (count + 1) state =
      process.refine (process.advance count state) :=
  rfl

theorem bound_le_advance (process : LowerProcess) :
    ∀ (count : Nat) (state : process.State),
      process.bound state ≤ process.bound (process.advance count state)
  | 0, _ => le_rfl
  | count + 1, state =>
      (process.bound_le_advance count state).trans
        (process.monotone (process.advance count state))

theorem advance_add (process : LowerProcess) (left right : Nat)
    (state : process.State) :
    process.advance (left + right) state =
      process.advance right (process.advance left state) := by
  induction right with
  | zero => rfl
  | succ right inductionHypothesis =>
      rw [Nat.add_succ, advance_succ, advance_succ,
        inductionHypothesis]

/-- Later finite schedules return at least as strong a lower bound. -/
theorem advance_mono (process : LowerProcess) {earlier later : Nat}
    (order : earlier ≤ later) (state : process.State) :
    process.bound (process.advance earlier state) ≤
      process.bound (process.advance later state) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [process.advance_add earlier extra state]
  exact process.bound_le_advance extra (process.advance earlier state)

/-- A direct common finite refinement for two lower-bound schedules. -/
def commonAdvance (process : LowerProcess) (left right : Nat)
    (state : process.State) : process.State :=
  process.advance (max left right) state

theorem left_le_commonAdvance (process : LowerProcess) (left right : Nat)
    (state : process.State) :
    process.bound (process.advance left state) ≤
      process.bound (process.commonAdvance left right state) :=
  process.advance_mono (Nat.le_max_left left right) state

theorem right_le_commonAdvance (process : LowerProcess) (left right : Nat)
    (state : process.State) :
    process.bound (process.advance right state) ≤
      process.bound (process.commonAdvance left right state) :=
  process.advance_mono (Nat.le_max_right left right) state

/-- Constant exact lower evidence. -/
def exact (value : Coordinate) : LowerProcess where
  State := Unit
  bound _ := value
  initial := ()
  refine state := state
  monotone _ := le_rfl
  refinesInitial _ := le_rfl

/-- Pointwise addition of independently refinable lower evidence. -/
def add (left right : LowerProcess) : LowerProcess where
  State := left.State × right.State
  bound state := left.bound state.1 + right.bound state.2
  initial := ⟨left.initial, right.initial⟩
  refine state := ⟨left.refine state.1, right.refine state.2⟩
  monotone state := add_le_add (left.monotone state.1)
    (right.monotone state.2)
  refinesInitial state := add_le_add (left.refinesInitial state.1)
    (right.refinesInitial state.2)

/-- Scaling lower evidence by an explicitly nonnegative rational preserves
its direction. -/
def scale (process : LowerProcess) (factor : Coordinate)
    (nonnegative : 0 ≤ factor) : LowerProcess where
  State := process.State
  bound state := factor * process.bound state
  initial := process.initial
  refine := process.refine
  monotone state :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (process.monotone state) nonnegative
  refinesInitial state :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (process.refinesInitial state) nonnegative

/-- Negation turns lower evidence into upper evidence. -/
def neg (process : LowerProcess) : UpperProcess where
  State := process.State
  bound state := -process.bound state
  initial := process.initial
  refine := process.refine
  antitone state :=
    RFAP.ConstructiveFraction.neg_le_neg_direct (process.monotone state)
  refinesInitial state :=
    RFAP.ConstructiveFraction.neg_le_neg_direct
      (process.refinesInitial state)

/-- A finite list of lower processes can be summed without imposing a common
state type or an infinite schedule. -/
def sum : List LowerProcess → LowerProcess
  | [] => exact 0
  | process :: remaining => process.add (sum remaining)

@[simp] theorem sum_nil : sum [] = exact 0 :=
  rfl

@[simp] theorem sum_cons (process : LowerProcess)
    (remaining : List LowerProcess) :
    sum (process :: remaining) = process.add (sum remaining) :=
  rfl

/-- Extract lower evidence from any certified two-sided refinement step. -/
def ofBoundRefinement (State : Type) (bound : State → Bound)
    (initial : State) (refine : State → State)
    (step : ∀ state, Bound.Refines (bound (refine state)) (bound state))
    (initialRefinement : ∀ state,
      Bound.Refines (bound state) (bound initial)) : LowerProcess where
  State := State
  bound state := (bound state).lower
  initial := initial
  refine := refine
  monotone state := (step state).lower
  refinesInitial state := (initialRefinement state).lower

end LowerProcess

namespace UpperProcess

/-- The newer upper observation contains at least the evidence in the older
one. -/
def Refines (process : UpperProcess)
    (newer older : process.State) : Prop :=
  process.bound newer ≤ process.bound older

namespace Refines

theorem refl (process : UpperProcess) (state : process.State) :
    process.Refines state state :=
  le_rfl

theorem trans {process : UpperProcess} {newest newer older : process.State}
    (newestNewer : process.Refines newest newer)
    (newerOlder : process.Refines newer older) :
    process.Refines newest older := by
  change process.bound newest ≤ process.bound older
  exact le_trans newestNewer newerOlder

end Refines

/-- Perform exactly the displayed finite number of upper refinements. -/
def advance (process : UpperProcess) : Nat → process.State → process.State
  | 0, state => state
  | count + 1, state => process.refine (advance process count state)

@[simp] theorem advance_zero (process : UpperProcess) (state : process.State) :
    process.advance 0 state = state :=
  rfl

theorem advance_succ (process : UpperProcess) (count : Nat)
    (state : process.State) :
    process.advance (count + 1) state =
      process.refine (process.advance count state) :=
  rfl

theorem advance_bound_le (process : UpperProcess) :
    ∀ (count : Nat) (state : process.State),
      process.bound (process.advance count state) ≤ process.bound state
  | 0, _ => le_rfl
  | count + 1, state =>
      (process.antitone (process.advance count state)).trans
        (process.advance_bound_le count state)

theorem advance_add (process : UpperProcess) (left right : Nat)
    (state : process.State) :
    process.advance (left + right) state =
      process.advance right (process.advance left state) := by
  induction right with
  | zero => rfl
  | succ right inductionHypothesis =>
      rw [Nat.add_succ, advance_succ, advance_succ,
        inductionHypothesis]

/-- Later finite schedules return at least as strong an upper bound. -/
theorem advance_antitone (process : UpperProcess) {earlier later : Nat}
    (order : earlier ≤ later) (state : process.State) :
    process.bound (process.advance later state) ≤
      process.bound (process.advance earlier state) := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [process.advance_add earlier extra state]
  exact process.advance_bound_le extra (process.advance earlier state)

/-- A direct common finite refinement for two upper-bound schedules. -/
def commonAdvance (process : UpperProcess) (left right : Nat)
    (state : process.State) : process.State :=
  process.advance (max left right) state

theorem commonAdvance_le_left (process : UpperProcess) (left right : Nat)
    (state : process.State) :
    process.bound (process.commonAdvance left right state) ≤
      process.bound (process.advance left state) :=
  process.advance_antitone (Nat.le_max_left left right) state

theorem commonAdvance_le_right (process : UpperProcess) (left right : Nat)
    (state : process.State) :
    process.bound (process.commonAdvance left right state) ≤
      process.bound (process.advance right state) :=
  process.advance_antitone (Nat.le_max_right left right) state

/-- Constant exact upper evidence. -/
def exact (value : Coordinate) : UpperProcess where
  State := Unit
  bound _ := value
  initial := ()
  refine state := state
  antitone _ := le_rfl
  refinesInitial _ := le_rfl

/-- Pointwise addition of independently refinable upper evidence. -/
def add (left right : UpperProcess) : UpperProcess where
  State := left.State × right.State
  bound state := left.bound state.1 + right.bound state.2
  initial := ⟨left.initial, right.initial⟩
  refine state := ⟨left.refine state.1, right.refine state.2⟩
  antitone state := add_le_add (left.antitone state.1)
    (right.antitone state.2)
  refinesInitial state := add_le_add (left.refinesInitial state.1)
    (right.refinesInitial state.2)

/-- Scaling upper evidence by an explicitly nonnegative rational preserves
its direction. -/
def scale (process : UpperProcess) (factor : Coordinate)
    (nonnegative : 0 ≤ factor) : UpperProcess where
  State := process.State
  bound state := factor * process.bound state
  initial := process.initial
  refine := process.refine
  antitone state :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (process.antitone state) nonnegative
  refinesInitial state :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (process.refinesInitial state) nonnegative

/-- Negation turns upper evidence into lower evidence. -/
def neg (process : UpperProcess) : LowerProcess where
  State := process.State
  bound state := -process.bound state
  initial := process.initial
  refine := process.refine
  monotone state :=
    RFAP.ConstructiveFraction.neg_le_neg_direct (process.antitone state)
  refinesInitial state :=
    RFAP.ConstructiveFraction.neg_le_neg_direct
      (process.refinesInitial state)

/-- A finite list of upper processes can be summed without imposing a common
state type or an infinite schedule. -/
def sum : List UpperProcess → UpperProcess
  | [] => exact 0
  | process :: remaining => process.add (sum remaining)

@[simp] theorem sum_nil : sum [] = exact 0 :=
  rfl

@[simp] theorem sum_cons (process : UpperProcess)
    (remaining : List UpperProcess) :
    sum (process :: remaining) = process.add (sum remaining) :=
  rfl

/-- Extract upper evidence from any certified two-sided refinement step. -/
def ofBoundRefinement (State : Type) (bound : State → Bound)
    (initial : State) (refine : State → State)
    (step : ∀ state, Bound.Refines (bound (refine state)) (bound state))
    (initialRefinement : ∀ state,
      Bound.Refines (bound state) (bound initial)) : UpperProcess where
  State := State
  bound state := (bound state).upper
  initial := initial
  refine := refine
  antitone state := (step state).upper
  refinesInitial state := (initialRefinement state).upper

end UpperProcess

/-! ## One-sided views of a fixed rational-bound request -/

namespace BoundProcess

/-- Repeating one explicitly chosen positive request exposes the lower
endpoints of a two-sided bound process as ordinary one-sided evidence.  This
view promises only monotonicity; repeating the same request need not produce
strict progress. -/
def lowerRequestProcess (process : BoundProcess) (epsilon : Coordinate)
    (positive : 0 < epsilon) : LowerProcess :=
  LowerProcess.ofBoundRefinement process.State process.bound process.initial
    (fun state => process.request state epsilon positive)
    (fun state => process.request_refines state epsilon positive)
    process.refinesInitial

/-- Repeating one explicitly chosen positive request exposes the upper
endpoints of a two-sided bound process as ordinary one-sided evidence. -/
def upperRequestProcess (process : BoundProcess) (epsilon : Coordinate)
    (positive : 0 < epsilon) : UpperProcess :=
  UpperProcess.ofBoundRefinement process.State process.bound process.initial
    (fun state => process.request state epsilon positive)
    (fun state => process.request_refines state epsilon positive)
    process.refinesInitial

end BoundProcess

/-! ## Pairing one-sided observations -/

/-- One compatible lower/upper observation at explicitly displayed states. -/
structure PairedObservation (lower : LowerProcess) (upper : UpperProcess) where
  lowerState : lower.State
  upperState : upper.State
  ordered : lower.bound lowerState ≤ upper.bound upperState

namespace PairedObservation

/-- The rational gap displayed by a paired observation. -/
def gap {lower : LowerProcess} {upper : UpperProcess}
    (observation : PairedObservation lower upper) : Coordinate :=
  upper.bound observation.upperState - lower.bound observation.lowerState

theorem gap_nonnegative {lower : LowerProcess} {upper : UpperProcess}
    (observation : PairedObservation lower upper) : 0 ≤ observation.gap :=
  RFAP.ConstructiveFraction.sub_nonneg_direct observation.ordered

/-- Forget the origins of the endpoints and retain an ordinary rational
enclosure. -/
def bound {lower : LowerProcess} {upper : UpperProcess}
    (observation : PairedObservation lower upper) : Bound where
  lower := lower.bound observation.lowerState
  upper := upper.bound observation.upperState
  valid := observation.ordered

@[simp] theorem bound_width {lower : LowerProcess} {upper : UpperProcess}
    (observation : PairedObservation lower upper) :
    observation.bound.width = observation.gap :=
  rfl

/-- A paired observation refines another when its lower endpoint rises and
its upper endpoint falls. -/
structure Refines {lower : LowerProcess} {upper : UpperProcess}
    (inner outer : PairedObservation lower upper) : Prop where
  lower : lower.bound outer.lowerState ≤ lower.bound inner.lowerState
  upper : upper.bound inner.upperState ≤ upper.bound outer.upperState

namespace Refines

theorem refl {lower : LowerProcess} {upper : UpperProcess}
    (observation : PairedObservation lower upper) :
    Refines observation observation :=
  ⟨le_rfl, le_rfl⟩

theorem trans {lower : LowerProcess} {upper : UpperProcess}
    {inner middle outer : PairedObservation lower upper}
    (innerMiddle : Refines inner middle)
    (middleOuter : Refines middle outer) : Refines inner outer :=
  ⟨middleOuter.lower.trans innerMiddle.lower,
    innerMiddle.upper.trans middleOuter.upper⟩

theorem bound {lower : LowerProcess} {upper : UpperProcess}
    {inner outer : PairedObservation lower upper}
    (refines : Refines inner outer) :
    Bound.Refines inner.bound outer.bound :=
  ⟨refines.lower, refines.upper⟩

end Refines

end PairedObservation

/-- A lower/upper pair equipped with an executable finite gap modulus.  This
extra request data, not one-sided monotonicity alone, licenses conversion to a
located two-sided process. -/
structure LocatedPair (lower : LowerProcess) (upper : UpperProcess) where
  State : Type
  observation : State → PairedObservation lower upper
  initial : State
  request : (state : State) → (epsilon : Coordinate) → 0 < epsilon → State
  request_refines : ∀ state epsilon positive,
    PairedObservation.Refines
      (observation (request state epsilon positive)) (observation state)
  accurate : ∀ state epsilon positive,
    (observation (request state epsilon positive)).gap < epsilon
  refinesInitial : ∀ state,
    PairedObservation.Refines (observation state) (observation initial)

namespace LocatedPair

/-- Convert an explicitly gap-controlled one-sided pair to the ordinary
finite rational enclosure protocol. -/
def toBoundProcess {lower : LowerProcess} {upper : UpperProcess}
    (pair : LocatedPair lower upper) : BoundProcess where
  State := pair.State
  bound state := (pair.observation state).bound
  initial := pair.initial
  request := pair.request
  request_refines state epsilon positive :=
    (pair.request_refines state epsilon positive).bound
  accurate state epsilon positive := by
    rw [PairedObservation.bound_width]
    exact pair.accurate state epsilon positive
  refinesInitial state := (pair.refinesInitial state).bound

theorem request_lower_mono {lower : LowerProcess} {upper : UpperProcess}
    (pair : LocatedPair lower upper) (state : pair.State)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    lower.bound (pair.observation state).lowerState ≤
      lower.bound
        (pair.observation (pair.request state epsilon positive)).lowerState :=
  (pair.request_refines state epsilon positive).lower

theorem request_upper_antitone {lower : LowerProcess} {upper : UpperProcess}
    (pair : LocatedPair lower upper) (state : pair.State)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    upper.bound
        (pair.observation (pair.request state epsilon positive)).upperState ≤
      upper.bound (pair.observation state).upperState :=
  (pair.request_refines state epsilon positive).upper

end LocatedPair

end FiniteMeasure
