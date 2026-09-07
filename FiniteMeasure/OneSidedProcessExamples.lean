import FiniteMeasure.OneSidedProcess
import FiniteMeasure.AlgebraicGap
import FiniteMeasure.ClassifiedProbability

/-!
# Worked one-sided rational process examples

All four examples are finite and executable.  They cover algebraic bisection,
staged rational classification, fuel-bounded inspection of finite routes, and
factorial-position radix prefixes associated with a Liouville-style target.

None of the constructions defines a limit, a completed real, or a hidden endpoint.
The conversion to `BoundProcess` occurs only because each example supplies a
separate finite gap request.
-/

namespace FiniteMeasure.OneSidedExamples

/-! ## Example 1: algebraic bisection around square three -/

namespace SquareThree

/-- One certified bisection, retaining reachability from the initial bracket. -/
def step (state : SqrtThree.State) : SqrtThree.State :=
  ⟨state.bracket.bisect,
    state.bracket.bisect_bound_refines.trans state.refines_initial⟩

theorem step_bound_refines (state : SqrtThree.State) :
    Bound.Refines (step state).bracket.bound state.bracket.bound :=
  state.bracket.bisect_bound_refines

/-- Increasing rational lower bounds obtained by square-three bisection. -/
def lower : LowerProcess :=
  LowerProcess.ofBoundRefinement SqrtThree.State
    (fun state => state.bracket.bound) SqrtThree.initialState step
    step_bound_refines (fun state => state.refines_initial)

/-- Decreasing rational upper bounds obtained by the same bisections. -/
def upper : UpperProcess :=
  UpperProcess.ofBoundRefinement SqrtThree.State
    (fun state => state.bracket.bound) SqrtThree.initialState step
    step_bound_refines (fun state => state.refines_initial)

/-- The lower and upper readings at one shared bisection state are ordered. -/
def observation (state : SqrtThree.State) : PairedObservation lower upper where
  lowerState := state
  upperState := state
  ordered := state.bracket.bound.valid

/-- The existing finite bisection budget is precisely the extra gap modulus
needed to locate the two one-sided processes. -/
def located : LocatedPair lower upper where
  State := SqrtThree.State
  observation := observation
  initial := SqrtThree.initialState
  request state epsilon _ := SqrtThree.request state epsilon
  request_refines state epsilon positive := by
    have refines := SqrtThree.process.request_refines state epsilon positive
    exact ⟨refines.lower, refines.upper⟩
  accurate state epsilon positive :=
    SqrtThree.process.accurate state epsilon positive
  refinesInitial state :=
    ⟨state.refines_initial.lower, state.refines_initial.upper⟩

/-- Four literal bisections are useful one-sided evidence even before asking
for a located output. -/
def fourSteps : SqrtThree.State :=
  lower.advance 4 lower.initial

/-- Exact execution of those four refinements produces `[27/16, 7/4]`. -/
theorem fourSteps_endpoints :
    lower.bound fourSteps = 27 / 16 ∧
      upper.bound fourSteps = 7 / 4 := by
  decide

/-- Addition and nonnegative scaling act directly on one-sided evidence.  At
the fourth state they certify `19/8` from below and `5/2` from above for the
finite affine calculation `2 * observation - 1`. -/
theorem affine_oneSided_bounds :
    ((lower.scale 2 (by decide)).add (LowerProcess.exact (-1))).bound
          ⟨fourSteps, ()⟩ = 19 / 8 ∧
      ((upper.scale 2 (by decide)).add (UpperProcess.exact (-1))).bound
          ⟨fourSteps, ()⟩ = 5 / 2 := by
  decide

/-- The executable square-three budget needs four bisections to beat an
eighth starting from `[1,2]`. -/
theorem eighth_bisection_count :
    SqrtThree.initialBracket.requiredBisections (1 / 8) = 4 := by
  decide

/-- The state actually returned for that request has exact rational endpoints
`27/16` and `7/4`, with width `1/16`. -/
theorem eighth_request_data :
    let state := SqrtThree.request SqrtThree.initialState (1 / 8)
    lower.bound state = 27 / 16 ∧
      upper.bound state = 7 / 4 ∧
      (observation state).gap = 1 / 16 := by
  decide

/-- Every finite state, including the computed eighth request above, retains
the algebraic separation certificates rather than merely a decimal-looking
approximation. -/
theorem every_state_straddles_three (state : SqrtThree.State) :
    (lower.bound state) ^ 2 < 3 ∧ 3 < (upper.bound state) ^ 2 := by
  change state.bracket.lower ^ 2 < 3 ∧ 3 < state.bracket.upper ^ 2
  exact ⟨state.bracket.lower_square_lt, state.bracket.upper_square_gt⟩

/-- Only the explicit gap modulus licenses the ordinary located enclosure. -/
theorem located_eighth_width :
    let process := located.toBoundProcess
    (process.bound
      (process.request process.initial (1 / 8) (by decide))).width <
        1 / 8 := by
  exact located.toBoundProcess.accurate _ _ (by decide)

end SquareThree

/-! ## Example 2: staged finite probability for `x² < 2` -/

namespace SquareTwoProbability

/-- Five displayed rational samples, kept distinct so their classification
history is visible in the finite state. -/
inductive Sample where
  | farNegative
  | nearNegative
  | center
  | nearPositive
  | farPositive
deriving DecidableEq, Repr

/-- Rational value attached to each displayed sample. -/
def value : Sample → Coordinate
  | .farNegative => -3 / 2
  | .nearNegative => -7 / 5
  | .center => 5 / 4
  | .nearPositive => 7 / 5
  | .farPositive => 3 / 2

/-- The executable strict square event. -/
def event (sample : Sample) : Bool :=
  decide (value sample ^ 2 < 2)

/-- A nonuniform finite rational law on the five samples. -/
def distribution : Distribution Sample where
  atoms :=
    [⟨.farNegative, 1 / 10, by decide⟩,
      ⟨.nearNegative, 1 / 5, by decide⟩,
      ⟨.center, 2 / 5, by decide⟩,
      ⟨.nearPositive, 1 / 5, by decide⟩,
      ⟨.farPositive, 1 / 10, by decide⟩]
  total_one := by decide

/-- Three finite classification stages: no information, all inside evidence,
then the remaining outside evidence. -/
inductive Stage where
  | unresolved
  | insideCertified
  | complete
deriving DecidableEq, Repr

def next : Stage → Stage
  | .unresolved => .insideCertified
  | .insideCertified => .complete
  | .complete => .complete

/-- At the middle stage, positive event tests are exposed as lower evidence
while negative tests remain unresolved. -/
def status : Stage → Sample → Status
  | .unresolved, _ => .unresolved
  | .insideCertified, sample =>
      if event sample then .inside else .unresolved
  | .complete, sample =>
      if event sample then .inside else .outside

theorem status_next_refines (stage : Stage) (sample : Sample) :
    (status (next stage) sample).Refines (status stage sample) := by
  cases stage with
  | unresolved => trivial
  | insideCertified =>
      cases selected : event sample <;>
        simp [next, status, Status.Refines, selected]
  | complete =>
      cases selected : event sample <;>
        simp [next, status, Status.Refines, selected]

theorem status_refines_unresolved (stage : Stage) (sample : Sample) :
    (status stage sample).Refines (status .unresolved sample) := by
  trivial

theorem status_complete_refines (stage : Stage) (sample : Sample) :
    (status .complete sample).Refines (status stage sample) := by
  cases stage with
  | unresolved => trivial
  | insideCertified =>
      cases selected : event sample <;>
        simp [status, Status.Refines, selected]
  | complete =>
      cases selected : event sample <;>
        simp [status, Status.Refines, selected]

theorem status_sound (stage : Stage) (sample : Sample) :
    (status stage sample).AdmitsSelection (event sample) := by
  cases stage with
  | unresolved => trivial
  | insideCertified =>
      cases selected : event sample <;>
        simp [status, Status.AdmitsSelection, selected]
  | complete =>
      cases selected : event sample <;>
        simp [status, Status.AdmitsSelection, selected]

/-- The two-sided bound is retained only as a finite observation extracted
from the current status table. -/
def bound (stage : Stage) : Bound :=
  eventBound (distribution.classifiedEventFrontier (status stage))

theorem next_bound_refines (stage : Stage) :
    Bound.Refines (bound (next stage)) (bound stage) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_next_refines stage atom.item

theorem bound_refines_initial (stage : Stage) :
    Bound.Refines (bound stage) (bound .unresolved) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_refines_unresolved stage atom.item

theorem complete_bound_refines (stage : Stage) :
    Bound.Refines (bound .complete) (bound stage) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_complete_refines stage atom.item

/-- Lower probability evidence rises as inside rows are certified. -/
def lower : LowerProcess :=
  LowerProcess.ofBoundRefinement Stage bound .unresolved next
    next_bound_refines bound_refines_initial

/-- Upper probability evidence falls only once rows are certified outside. -/
def upper : UpperProcess :=
  UpperProcess.ofBoundRefinement Stage bound .unresolved next
    next_bound_refines bound_refines_initial

/-- A standard finite classification process, included to show that the first
one-sided client is the existing finite-measure observation machinery. -/
def classification : ClassificationProcess distribution event where
  State := Stage
  status := status
  initial := .unresolved
  request _ _ _ := .complete
  sound stage atom member := status_sound stage atom.item
  request_refines state epsilon positive atom member :=
    status_complete_refines state atom.item
  accurate state epsilon positive := by
    have noneUnresolved :
        distribution.probability
            (unresolvedStatusEvent (status .complete)) = 0 := by
      decide
    rw [noneUnresolved]
    exact positive
  refinesInitial stage atom member :=
    status_refines_unresolved stage atom.item

/-- Pair the observations at a shared status-table stage. -/
def observation (stage : Stage) : PairedObservation lower upper where
  lowerState := stage
  upperState := stage
  ordered := (bound stage).valid

/-- Completion of this displayed five-row table is a finite zero-gap modulus. -/
def located : LocatedPair lower upper where
  State := Stage
  observation := observation
  initial := .unresolved
  request _ _ _ := .complete
  request_refines state epsilon positive := by
    have refines := complete_bound_refines state
    exact ⟨refines.lower, refines.upper⟩
  accurate state epsilon positive := by
    have zeroGap : (observation .complete).gap = 0 := by decide
    rw [zeroGap]
    exact positive
  refinesInitial state := by
    have refines := bound_refines_initial state
    exact ⟨refines.lower, refines.upper⟩

/-- These are genuine rational square decisions on every displayed row. -/
theorem event_table :
    event .farNegative = false ∧
      event .nearNegative = true ∧
      event .center = true ∧
      event .nearPositive = true ∧
      event .farPositive = false := by
  decide

/-- The middle stage has accumulated all `4/5` of the inside mass from below,
while the two far rows still contribute `1/5` of unresolved upper mass. -/
theorem staged_endpoints :
    lower.bound .unresolved = 0 ∧ upper.bound .unresolved = 1 ∧
      lower.bound .insideCertified = 4 / 5 ∧
      upper.bound .insideCertified = 1 ∧
      lower.bound .complete = 4 / 5 ∧
      upper.bound .complete = 4 / 5 := by
  decide

/-- The exact finite probability is independently computed from the event,
and every one-sided stage encloses it through the classification proof. -/
theorem exact_probability : distribution.probability event = 4 / 5 := by
  decide

theorem probability_inside_middle_bound :
    (bound .insideCertified).Contains (distribution.probability event) :=
  classification.probability_mem_bound .insideCertified

/-- Once the explicit finite gap request runs, conversion to `BoundProcess`
returns the exact rational enclosure `[4/5,4/5]`. -/
theorem located_request_exact :
    let process := located.toBoundProcess
    let state := process.request process.initial (1 / 10) (by decide)
    (process.bound state).lower = 4 / 5 ∧
      (process.bound state).upper = 4 / 5 ∧
      (process.bound state).width = 0 := by
  decide

end SquareTwoProbability

/-! ## Example 3: short-circuit inspection of finite graph routes -/

namespace FirstArrivalProbability

/-- Named sites in a finite route-inspection problem.  `home` and `trap` are
terminal; all other sites require the inspector to continue along the route. -/
inductive Site where
  | crossroads
  | market
  | forest
  | bridge
  | home
  | trap
deriving DecidableEq, Repr

abbrev Route := List Site

/-- The full finite event: does the route encounter `home` before `trap`?
Exhausting the displayed route without either terminal counts as failure. -/
def firstArrival : Route → Bool
  | [] => false
  | site :: remaining =>
      match site with
      | .home => true
      | .trap => false
      | .crossroads | .market | .forest | .bridge => firstArrival remaining

/-- A fuel-bounded short-circuit inspector.  `none` means that the displayed
budget has not yet resolved the route, not that the event is false. -/
def inspect : Nat → Route → Option Bool
  | 0, _ => none
  | _ + 1, [] => some false
  | fuel + 1, site :: remaining =>
      match site with
      | .home => some true
      | .trap => some false
      | .crossroads | .market | .forest | .bridge => inspect fuel remaining

/-- Every result returned by bounded inspection agrees with the full finite
route event. -/
theorem inspect_sound : ∀ (fuel : Nat) (route : Route) (result : Bool),
    inspect fuel route = some result → firstArrival route = result
  | 0, _, _, impossible => by
      cases impossible
  | _ + 1, [], result, equality => by
      simpa only [inspect, firstArrival, Option.some.injEq] using equality
  | fuel + 1, site :: remaining, result, equality => by
      cases site with
      | home =>
          simpa only [inspect, firstArrival, Option.some.injEq] using equality
      | trap =>
          simpa only [inspect, firstArrival, Option.some.injEq] using equality
      | crossroads =>
          simpa only [firstArrival] using
            inspect_sound fuel remaining result
              (by simpa only [inspect] using equality)
      | market =>
          simpa only [firstArrival] using
            inspect_sound fuel remaining result
              (by simpa only [inspect] using equality)
      | forest =>
          simpa only [firstArrival] using
            inspect_sound fuel remaining result
              (by simpa only [inspect] using equality)
      | bridge =>
          simpa only [firstArrival] using
            inspect_sound fuel remaining result
              (by simpa only [inspect] using equality)

/-- Once bounded inspection resolves a route, one more unit of fuel returns
the same result. -/
theorem inspect_succ : ∀ (fuel : Nat) (route : Route) (result : Bool),
    inspect fuel route = some result →
      inspect (fuel + 1) route = some result
  | 0, _, _, impossible => by
      cases impossible
  | fuel + 1, [], result, equality => by
      simpa only [inspect] using equality
  | fuel + 1, site :: remaining, result, equality => by
      cases site with
      | home => simpa only [inspect] using equality
      | trap => simpa only [inspect] using equality
      | crossroads =>
          simpa only [inspect] using
            inspect_succ fuel remaining result
              (by simpa only [inspect] using equality)
      | market =>
          simpa only [inspect] using
            inspect_succ fuel remaining result
              (by simpa only [inspect] using equality)
      | forest =>
          simpa only [inspect] using
            inspect_succ fuel remaining result
              (by simpa only [inspect] using equality)
      | bridge =>
          simpa only [inspect] using
            inspect_succ fuel remaining result
              (by simpa only [inspect] using equality)

theorem inspect_add_fuel (fuel extra : Nat) (route : Route) (result : Bool)
    (resolved : inspect fuel route = some result) :
    inspect (fuel + extra) route = some result := by
  induction extra with
  | zero => simpa only [Nat.add_zero] using resolved
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      exact inspect_succ (fuel + extra) route result inductionHypothesis

theorem inspect_mono {earlier later : Nat} (order : earlier ≤ later)
    (route : Route) (result : Bool)
    (resolved : inspect earlier route = some result) :
    inspect later route = some result := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  exact inspect_add_fuel earlier extra route result resolved

/-- Turn a bounded inspection result into one-sided finite-measure evidence. -/
def status (fuel : Nat) (route : Route) : Status :=
  match inspect fuel route with
  | none => .unresolved
  | some true => .inside
  | some false => .outside

theorem status_sound (fuel : Nat) (route : Route) :
    (status fuel route).AdmitsSelection (firstArrival route) := by
  cases inspected : inspect fuel route with
  | none => simp [status, inspected, Status.AdmitsSelection]
  | some result =>
      have sound := inspect_sound fuel route result inspected
      cases result <;>
        simp [status, inspected, Status.AdmitsSelection, sound]

theorem status_refines_of_le {earlier later : Nat}
    (order : earlier ≤ later) (route : Route) :
    (status later route).Refines (status earlier route) := by
  cases inspected : inspect earlier route with
  | none =>
      simp [status, inspected, Status.Refines]
  | some result =>
      have persists := inspect_mono order route result inspected
      cases result <;>
        simp [status, inspected, persists, Status.Refines]

/-- Four explicit scheduler states expose progressively more route evidence. -/
inductive Stage where
  | start
  | shallow
  | medium
  | complete
deriving DecidableEq, Repr

def Stage.fuel : Stage → Nat
  | .start => 0
  | .shallow => 3
  | .medium => 4
  | .complete => 6

def Stage.next : Stage → Stage
  | .start => .shallow
  | .shallow => .medium
  | .medium => .complete
  | .complete => .complete

theorem Stage.fuel_le_next (stage : Stage) :
    stage.fuel ≤ stage.next.fuel := by
  cases stage <;> decide

theorem Stage.fuel_le_complete (stage : Stage) :
    stage.fuel ≤ Stage.complete.fuel := by
  cases stage <;> decide

def routeA : Route := [.crossroads, .market, .home]
def routeB : Route := [.forest, .bridge, .trap, .home]
def routeC : Route := [.market, .forest, .crossroads, .home]
def routeD : Route := [.bridge, .market, .trap]
def routeE : Route := [.forest, .market, .bridge, .crossroads, .home]
def routeF : Route := [.market, .bridge]
def routeG : Route := [.forest, .market, .home]
def routeH : Route := [.forest, .market, .bridge, .trap]

/-- A nonuniform law on eight displayed routes through the finite graph. -/
def distribution : Distribution Route where
  atoms :=
    [⟨routeA, 1 / 10, by decide⟩,
      ⟨routeB, 3 / 20, by decide⟩,
      ⟨routeC, 1 / 5, by decide⟩,
      ⟨routeD, 1 / 10, by decide⟩,
      ⟨routeE, 1 / 4, by decide⟩,
      ⟨routeF, 1 / 10, by decide⟩,
      ⟨routeG, 1 / 20, by decide⟩,
      ⟨routeH, 1 / 20, by decide⟩]
  total_one := by decide

def stageStatus (stage : Stage) : Route → Status :=
  status stage.fuel

def bound (stage : Stage) : Bound :=
  eventBound (distribution.classifiedEventFrontier (stageStatus stage))

theorem next_bound_refines (stage : Stage) :
    Bound.Refines (bound stage.next) (bound stage) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_refines_of_le stage.fuel_le_next atom.item

theorem bound_refines_start (stage : Stage) :
    Bound.Refines (bound stage) (bound .start) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_refines_of_le (Nat.zero_le stage.fuel) atom.item

theorem complete_bound_refines (stage : Stage) :
    Bound.Refines (bound .complete) (bound stage) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_refines_of_le stage.fuel_le_complete atom.item

def lower : LowerProcess :=
  LowerProcess.ofBoundRefinement Stage bound .start Stage.next
    next_bound_refines bound_refines_start

def upper : UpperProcess :=
  UpperProcess.ofBoundRefinement Stage bound .start Stage.next
    next_bound_refines bound_refines_start

/-- The generic finite classifier is driven here by a partial combinatorial
search rather than a rational comparison. -/
def classification : ClassificationProcess distribution firstArrival where
  State := Stage
  status := stageStatus
  initial := .start
  request _ _ _ := .complete
  sound stage atom member := status_sound stage.fuel atom.item
  request_refines stage epsilon positive atom member :=
    status_refines_of_le stage.fuel_le_complete atom.item
  accurate stage epsilon positive := by
    have noneUnresolved :
        distribution.probability
            (unresolvedStatusEvent (stageStatus .complete)) = 0 := by
      decide
    rw [noneUnresolved]
    exact positive
  refinesInitial stage atom member :=
    status_refines_of_le (Nat.zero_le stage.fuel) atom.item

def observation (stage : Stage) : PairedObservation lower upper where
  lowerState := stage
  upperState := stage
  ordered := (bound stage).valid

def located : LocatedPair lower upper where
  State := Stage
  observation := observation
  initial := .start
  request _ _ _ := .complete
  request_refines stage epsilon positive := by
    have refines := complete_bound_refines stage
    exact ⟨refines.lower, refines.upper⟩
  accurate stage epsilon positive := by
    have zeroGap : (observation .complete).gap = 0 := by decide
    rw [zeroGap]
    exact positive
  refinesInitial stage := by
    have refines := bound_refines_start stage
    exact ⟨refines.lower, refines.upper⟩

/-- Concrete evidence that bounded inspection short-circuits at different
depths and honestly leaves the longer successful route unresolved. -/
theorem inspection_table :
    inspect 3 routeA = some true ∧
      inspect 3 routeB = some false ∧
      inspect 4 routeC = some true ∧
      inspect 4 routeE = none ∧
      inspect 6 routeE = some true := by
  decide

theorem route_outcomes :
    firstArrival routeA = true ∧ firstArrival routeB = false ∧
      firstArrival routeC = true ∧ firstArrival routeD = false ∧
      firstArrival routeE = true ∧ firstArrival routeF = false ∧
      firstArrival routeG = true ∧ firstArrival routeH = false := by
  decide

/-- Refinement moves mass on both sides as the combinatorial search resolves
more routes: `[0,1]`, `[3/20,13/20]`, `[7/20,3/5]`, then `[3/5,3/5]`. -/
theorem staged_endpoints :
    lower.bound .start = 0 ∧ upper.bound .start = 1 ∧
      lower.bound .shallow = 3 / 20 ∧ upper.bound .shallow = 13 / 20 ∧
      lower.bound .medium = 7 / 20 ∧ upper.bound .medium = 3 / 5 ∧
      lower.bound .complete = 3 / 5 ∧ upper.bound .complete = 3 / 5 := by
  decide

theorem exact_probability :
    distribution.probability firstArrival = 3 / 5 := by
  decide

theorem probability_inside_medium_bound :
    (bound .medium).Contains (distribution.probability firstArrival) :=
  classification.probability_mem_bound .medium

theorem located_request_exact :
    let process := located.toBoundProcess
    let state := process.request process.initial (1 / 10) (by decide)
    (process.bound state).lower = 3 / 5 ∧
      (process.bound state).upper = 3 / 5 ∧
      (process.bound state).width = 0 := by
  decide

end FirstArrivalProbability

/-! ## Example 4: finite prefixes of the base-four Liouville constant

Classically, the nested radix cylinders below approach
`L₄ = ∑ k ≥ 1, 4⁻ᵏ!`, a Liouville and hence transcendental number.  The Lean
construction never forms that infinite series or a completed endpoint: every
state contains only a finite digit prefix and an explicit rational cylinder.
-/

namespace LiouvilleDigits

/-- Executable factorial used only to decide finitely many displayed digit
positions. -/
def factorial : Nat → Nat
  | 0 => 1
  | index + 1 => factorial index * (index + 1)

/-- Does a positive digit position occur among the finitely searched
factorials up to that position? -/
def isFactorialPosition (position : Nat) : Bool :=
  (List.range (position + 1)).any fun index =>
    decide (factorial index = position)

/-- Base-four digit at zero-based index `index`: one exactly when `index + 1`
is a factorial position, otherwise zero. -/
def digit (index : Nat) : Coordinate :=
  if isFactorialPosition (index + 1) then 1 else 0

theorem digit_nonnegative (index : Nat) : 0 ≤ digit index := by
  unfold digit
  split <;> decide

theorem digit_le_one (index : Nat) : digit index ≤ 1 := by
  unfold digit
  split <;> decide

/-- Width remaining after `index` displayed base-four digits. -/
def place (index : Nat) : Coordinate :=
  (1 / 4 : Coordinate) ^ index

theorem place_nonnegative (index : Nat) : 0 ≤ place index :=
  RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) index

theorem place_positive (index : Nat) : 0 < place index :=
  RFAP.ConstructiveFraction.pow_pos_direct (by decide) index

theorem place_succ (index : Nat) :
    place (index + 1) = place index / 4 := by
  unfold place
  rw [pow_succ, RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveFraction.one_mul]

/-- Exact rational value of the displayed finite digit prefix. -/
def prefixValue : Nat → Coordinate
  | 0 => 0
  | index + 1 => prefixValue index + digit index * (place index / 4)

/-- The unresolved base-four cylinder gives a one-sided upper observation. -/
def prefixUpper (index : Nat) : Coordinate :=
  prefixValue index + place index

theorem prefix_step_mono (index : Nat) :
    prefixValue index ≤ prefixValue (index + 1) := by
  rw [prefixValue]
  exact le_add_of_nonneg_right
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (digit_nonnegative index)
      (RFAP.ConstructiveFraction.div_nonneg_direct
        (place_nonnegative index) (by decide)))

theorem prefixUpper_step_antitone (index : Nat) :
    prefixUpper (index + 1) ≤ prefixUpper index := by
  unfold prefixUpper
  rw [prefixValue, place_succ]
  have placeNonnegative := place_nonnegative index
  have placeQuarter : place index / 4 =
      (1 / 4 : Coordinate) * place index := by
    change place index * (4 : Coordinate)⁻¹ =
      (1 * (4 : Coordinate)⁻¹) * place index
    rw [RFAP.ConstructiveFraction.one_mul]
    ring1
  rw [placeQuarter]
  unfold digit
  split
  · calc
      prefixValue index + 1 * ((1 / 4 : Coordinate) * place index) +
            (1 / 4 : Coordinate) * place index =
          prefixValue index +
            ((1 / 4 : Coordinate) + 1 / 4) * place index := by ring1
      _ = prefixValue index + (1 / 2 : Coordinate) * place index := by
        rw [show (1 / 4 : Coordinate) + 1 / 4 = 1 / 2 by decide]
      _ ≤ prefixValue index + 1 * place index :=
        add_le_add le_rfl
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (by decide) placeNonnegative)
      _ = prefixValue index + place index := by ring1
  · calc
      prefixValue index + 0 * ((1 / 4 : Coordinate) * place index) +
            (1 / 4 : Coordinate) * place index =
          prefixValue index + (1 / 4 : Coordinate) * place index := by ring1
      _ ≤ prefixValue index + 1 * place index :=
        add_le_add le_rfl
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (by decide) placeNonnegative)
      _ = prefixValue index + place index := by ring1

theorem prefix_nonnegative : ∀ index : Nat, 0 ≤ prefixValue index
  | 0 => le_rfl
  | index + 1 =>
      (prefix_nonnegative index).trans (prefix_step_mono index)

theorem prefixUpper_le_one : ∀ index : Nat, prefixUpper index ≤ 1
  | 0 => by
      unfold prefixUpper prefixValue place
      decide
  | index + 1 =>
      (prefixUpper_step_antitone index).trans (prefixUpper_le_one index)

theorem prefix_mono_index {earlier later : Nat} (order : earlier ≤ later) :
    prefixValue earlier ≤ prefixValue later := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  clear order
  induction extra with
  | zero => exact le_rfl
  | succ extra inductionHypothesis =>
      exact inductionHypothesis.trans
        (by simpa only [Nat.add_succ] using prefix_step_mono (earlier + extra))

theorem prefixUpper_antitone_index {earlier later : Nat}
    (order : earlier ≤ later) : prefixUpper later ≤ prefixUpper earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  clear order
  induction extra with
  | zero => exact le_rfl
  | succ extra inductionHypothesis =>
      have step : prefixUpper (earlier + (extra + 1)) ≤
          prefixUpper (earlier + extra) := by
        simpa only [Nat.add_succ] using
          prefixUpper_step_antitone (earlier + extra)
      exact step.trans inductionHypothesis

/-- Increasing rational prefixes of the factorial-position digit process. -/
def lower : LowerProcess where
  State := Nat
  bound := prefixValue
  initial := 0
  refine index := index + 1
  monotone := prefix_step_mono
  refinesInitial := prefix_nonnegative

/-- Decreasing rational cylinder tops for the same finite prefixes. -/
def upper : UpperProcess where
  State := Nat
  bound := prefixUpper
  initial := 0
  refine index := index + 1
  antitone := prefixUpper_step_antitone
  refinesInitial state := by
    change prefixUpper state ≤ 1
    exact prefixUpper_le_one state

def observation (index : Nat) : PairedObservation lower upper where
  lowerState := index
  upperState := index
  ordered := by
    change prefixValue index ≤ prefixValue index + place index
    exact le_add_of_nonneg_right (place_nonnegative index)

@[simp] theorem observation_gap (index : Nat) :
    (observation index).gap = place index := by
  change prefixUpper index - prefixValue index = place index
  unfold prefixUpper
  ring1

/-- The finite quarter-power search is an explicit modulus for the displayed
digit-cylinder width. -/
def located : LocatedPair lower upper where
  State := Nat
  observation := observation
  initial := 0
  request index epsilon _ :=
    Geometric.firstQuarterBelow 1 index epsilon
  request_refines index epsilon positive := by
    have order := Geometric.firstQuarterBelow_ge 1 index epsilon
    exact ⟨prefix_mono_index order, prefixUpper_antitone_index order⟩
  accurate index epsilon positive := by
    rw [observation_gap, place]
    have accurate := Geometric.firstQuarterBelow_accurate
      1 (by decide) index epsilon positive
    rw [Geometric.quarterAllowance_eq_mul_pow] at accurate
    simpa only [RFAP.ConstructiveFraction.one_mul] using accurate
  refinesInitial index :=
    ⟨prefix_nonnegative index, prefixUpper_le_one index⟩

/-- The first six finite decisions display ones at positions `1`, `2`, and
`6 = 3!`, with the intervening digits zero. -/
theorem first_digits :
    digit 0 = 1 ∧ digit 1 = 1 ∧ digit 2 = 0 ∧
      digit 3 = 0 ∧ digit 4 = 0 ∧ digit 5 = 1 := by
  decide

theorem prefix_six :
    prefixValue 6 = 5 / 16 + place 5 / 4 := by
  rcases first_digits with ⟨_, _, digitTwo, digitThree, digitFour, digitFive⟩
  rw [prefixValue, prefixValue, prefixValue, prefixValue,
    digitTwo, digitThree, digitFour, digitFive]
  rw [show prefixValue 2 = 5 / 16 by decide]
  ring1

/-- Concrete nested rational observations.  No infinite radix expansion or
completed Liouville number is formed. -/
theorem displayed_prefixes :
    prefixValue 0 = 0 ∧ prefixUpper 0 = 1 ∧
      prefixValue 2 = 5 / 16 ∧ prefixUpper 2 = 3 / 8 ∧
      prefixValue 6 = 5 / 16 + place 5 / 4 ∧
      prefixUpper 6 = 5 / 16 + place 5 / 4 + place 6 := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · exact (by decide)
  constructor
  · decide
  constructor
  · exact prefix_six
  · unfold prefixUpper
    rw [prefix_six]

theorem tenth_request_index :
    Geometric.firstQuarterBelow 1 0 (1 / 10) = 2 := by
  decide

theorem tenth_request_width :
    let process := located.toBoundProcess
    (process.bound
      (process.request process.initial (1 / 10) (by decide))).width <
        1 / 10 :=
  located.toBoundProcess.accurate _ _ (by decide)

end LiouvilleDigits

end FiniteMeasure.OneSidedExamples
