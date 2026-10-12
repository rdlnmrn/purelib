module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Interval.Basic

import Purelib.Approximation.Bound.Process
import Purelib.Approximation.OneSided.Basic
public import Purelib.Approximation.OneSided.Located
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Classified.Split
import Purelib.Measure.Classified.Soundness
import Purelib.Data.List.Event
import Purelib.Measure.Classified.Distribution
public import Purelib.Measure.Classified.FixedLawProcess
import Purelib.Data.List.Prefix.Cursor
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Elab.Deriving.Repr

@[expose] public section

/-!
# Finite first-arrival probability

A six-site route model retains ordered paths, fuel-bounded inspection, and
classified lower and upper probability bounds. A finite gap request turns the
classification into a located bound process.
-/

namespace Purelib.Examples.Measure.Probability.Classification.FirstArrival.WorkedExamples

open Purelib.Measure
open Purelib.Examples
open Purelib
open Purelib.Data.Rat

/-- The six site labels of the finite first-arrival route model. -/
inductive Site where
  /-- A nonterminal crossroads site. -/ | crossroads
  /-- A nonterminal market site. -/ | market
  /-- A nonterminal forest site. -/ | forest
  /-- A nonterminal bridge site. -/ | bridge
  /-- The successful terminal site. -/ | home
  /-- The unsuccessful terminal site. -/ | trap
deriving DecidableEq

derive_exposed_repr Site

/-- An ordered finite list of route sites. -/
abbrev Route := List
  Site

/-- Whether a finite route reaches home before a trap.

Scans the original site order; an empty route or a first trap fails, and a first home succeeds. -/
def firstArrival :
  Route → Bool
  | [] => false
  | site :: remaining =>
      match site with
      | .home => true
      | .trap => false
      | .crossroads | .market | .forest | .bridge =>
        firstArrival remaining

/-- Inspect a route for first arrival using a finite step budget.

Returns none when no budget remains, preserving the distinction between an unresolved scan and a completed false result.
-/
def inspect : Nat →
  Route → Option Bool
  | 0, _ => none
  | _ + 1, [] => some false
  | fuel + 1, site :: remaining =>
      match site with
      | .home => some true
      | .trap => some false
      | .crossroads | .market | .forest | .bridge =>
        inspect fuel remaining

/-- Every resolved finite inspection agrees with the original first-arrival predicate.

Follows the exact original route and retained Boolean result through its budgeted scan. -/
theorem inspect_sound : ∀ (fuel :
  Nat) (route : Route) (result : Bool),
    inspect fuel route = some result →
      firstArrival route = result
  | 0, _, _, impossible => by
      cases impossible
  | _ + 1, [], result, equality => by
      simp only [-eq_self, -iff_self,
        inspect] at equality
      exact congrArg (fun value : Option Bool => value.getD false) equality
  | fuel + 1, site :: remaining, result, equality => by
      cases site with
      | home =>
          simp only [-eq_self, -iff_self,
            inspect] at equality
          exact congrArg (fun value : Option Bool => value.getD false) equality
      | trap =>
          simp only [-eq_self, -iff_self,
            inspect] at equality
          exact congrArg (fun value : Option Bool => value.getD false) equality
      | crossroads =>
          simpa only [firstArrival] using
            inspect_sound fuel remaining
              result
              (by simpa only [inspect] using equality)
      | market =>
          simpa only [firstArrival] using
            inspect_sound fuel remaining
              result
              (by simpa only [inspect] using equality)
      | forest =>
          simpa only [firstArrival] using
            inspect_sound fuel remaining
              result
              (by simpa only [inspect] using equality)
      | bridge =>
          simpa only [firstArrival] using
            inspect_sound fuel remaining
              result
              (by simpa only [inspect] using equality)

/-- One extra inspection step preserves any already resolved result. -/
theorem inspect_succ : ∀ (fuel :
  Nat) (route : Route) (result : Bool),
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
            inspect_succ fuel remaining
              result
              (by simpa only [inspect] using equality)
      | market =>
          simpa only [inspect] using
            inspect_succ fuel remaining
              result
              (by simpa only [inspect] using equality)
      | forest =>
          simpa only [inspect] using
            inspect_succ fuel remaining
              result
              (by simpa only [inspect] using equality)
      | bridge =>
          simpa only [inspect] using
            inspect_succ fuel remaining
              result
              (by simpa only [inspect] using equality)

/-- Adding any finite inspection budget preserves the original resolved result. -/
theorem inspect_add_fuel (fuel
  extra : Nat) (route : Route) (result : Bool)
    (resolved : inspect fuel route = some result) :
    inspect (fuel + extra) route = some result := by
  induction extra with
  | zero => simpa only [Nat.add_zero] using resolved
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      exact inspect_succ (fuel + extra) route result
        inductionHypothesis

/-- Increasing inspection fuel preserves its exact resolved Boolean outcome. -/
theorem inspect_mono {earlier
  later : Nat} (order : earlier ≤ later)
    (route : Route) (result : Bool)
    (resolved : inspect earlier route = some result) :
    inspect later route = some result := by
  have laterEquation : earlier + (later - earlier) = later :=
    Purelib.Data.Nat.Subtraction.add_sub_of_le order
  rw [← laterEquation]
  exact inspect_add_fuel earlier (later - earlier) route
    result resolved

/-- Classify a route as inside, outside or unresolved at the given fuel. -/
def status (fuel : Nat) (route :
  Route) : Status :=
  match inspect fuel route with
  | none => .unresolved
  | some true => .inside
  | some false => .outside

/-- The retained inspection status admits the route's actual first-arrival outcome. -/
theorem status_sound (fuel : Nat)
  (route : Route) :
    (status fuel route).AdmitsSelection
      (firstArrival route) := by
  cases inspected : inspect fuel route with
  | none =>
      simp only [-eq_self, -iff_self, status, inspected,
        Status.AdmitsSelection]
  | some result =>
      have sound := inspect_sound fuel route result
        inspected
      cases result <;>
        (simp only [-eq_self, -iff_self, status,
          inspected, Status.AdmitsSelection, sound]
         rfl)

/-- Larger inspection budgets refine the original route status. -/
theorem status_refines_of_le
  {earlier later : Nat}
    (order : earlier ≤ later) (route : Route) :
    (status later route).Refines
      (status earlier route) := by
  cases inspected : inspect earlier route with
  | none =>
      simp only [-eq_self, -iff_self, status, inspected,
        Status.Refines]
  | some result =>
      have persists := inspect_mono order route result
        inspected
      cases result <;>
        (simp only [-eq_self, -iff_self, status,
          inspected, persists, Status.Refines]
         rfl)

/-- The four retained finite inspection stages. -/
inductive Stage where
  /-- The initial stage with no inspection fuel. -/ | start
  /-- The stage with three inspection steps. -/ | shallow
  /-- The stage with four inspection steps. -/ | medium
  /-- The stage with six steps, sufficient for every retained route. -/ | complete
deriving DecidableEq

derive_exposed_repr Stage

/-- Inspection budgets zero, three, four and six for the four stages. -/
def Stage.fuel :
  Stage → Nat
  | .start => 0
  | .shallow => 3
  | .medium => 4
  | .complete => 6

/-- Advance the retained stage, keeping the complete stage fixed. -/
def Stage.next :
  Stage →
  Stage
  | .start => .shallow
  | .shallow => .medium
  | .medium => .complete
  | .complete => .complete

/-- Advancing a stage never decreases its inspection budget. -/
theorem Stage.fuel_le_next (stage
  : Stage) :
    stage.fuel ≤ stage.next.fuel := by
  cases stage <;> decide

/-- Every stage's inspection budget is at most the complete-stage budget. -/
theorem Stage.fuel_le_complete
  (stage : Stage) :
    stage.fuel ≤ Stage.fuel
      Stage.complete := by
  cases stage <;> decide

/-- The crossroads-market-home route. -/
def routeA :
  Route := [.crossroads, .market, .home]
/-- The forest-bridge-trap-home route, whose first terminal site is the trap. -/
def routeB :
  Route := [.forest, .bridge, .trap, .home]
/-- The market-forest-crossroads-home route. -/
def routeC :
  Route := [.market, .forest, .crossroads, .home]
/-- The bridge-market-trap route. -/
def routeD :
  Route := [.bridge, .market, .trap]
/-- The forest-market-bridge-crossroads-home route. -/
def routeE :
  Route := [.forest, .market, .bridge, .crossroads,
  .home]
/-- The market-bridge route with no terminal home or trap. -/
def routeF :
  Route := [.market, .bridge]
/-- The forest-market-home route. -/
def routeG :
  Route := [.forest, .market, .home]
/-- The forest-market-bridge-trap route. -/
def routeH :
  Route := [.forest, .market, .bridge, .trap]

/-- The certified eight-route probability law with its original rational weights.

Retains routes A through H in order and verifies that the nonnegative weights sum exactly to one. -/
def distribution :
  Measure.Distribution Route where
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

/-- The route classifier at the retained stage's actual inspection budget. -/
def stageStatus (stage :
  Stage) :
  Route → Status :=
  status stage.fuel

/-- The classified-event probability interval at the given retained stage. -/
def bound (stage :
  Stage) : Data.Rat.Interval :=
  Measure.eventBound
    (distribution.classifiedEventFrontier
    (stageStatus stage))

/-- The next stage's probability interval refines the current interval. -/
theorem next_bound_refines (stage
  : Stage) :
    Interval.Refines (bound stage.next)
      (bound stage) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_refines_of_le stage.fuel_le_next atom.item

/-- Every retained stage refines the initial probability interval. -/
theorem bound_refines_start
  (stage : Stage) :
    Interval.Refines (bound stage)
      (bound .start) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_refines_of_le (Nat.zero_le stage.fuel)
    atom.item

/-- The complete-stage probability interval refines every retained stage. -/
theorem complete_bound_refines
  (stage : Stage) :
    Interval.Refines (bound .complete)
      (bound stage) := by
  apply distribution.classifiedEventFrontier_refines
  intro atom member
  exact status_refines_of_le stage.fuel_le_complete
    atom.item

/-- The increasing lower-probability process induced by the four retained stages. -/
def lower :
  Approximation.LowerProcess :=
  Approximation.LowerProcess.ofBoundRefinement Stage
    bound .start
    Stage.next
    next_bound_refines
      bound_refines_start

/-- The decreasing upper-probability process induced by the same retained stages. -/
def upper :
  Approximation.UpperProcess :=
  Approximation.UpperProcess.ofBoundRefinement Stage
    bound .start
    Stage.next
    next_bound_refines
      bound_refines_start

/-- Certified finite classification of first arrival under the original route law.

Every positive accuracy request uses the complete stage, where unresolved probability is exactly zero; all status
refinements retain the original event. -/
def classification :
  Measure.ClassificationProcess distribution
  firstArrival where
  State := Stage
  status := stageStatus
  initial := .start
  request _ _ _ := .complete
  sound stage atom member := status_sound stage.fuel
    atom.item
  request_refines stage epsilon positive atom member :=
    status_refines_of_le stage.fuel_le_complete atom.item
  accurate stage epsilon positive := by
    have noneUnresolved :
        distribution.probability
            (unresolvedStatusEvent (stageStatus
              .complete)) = 0 := by
      decide
    rw [noneUnresolved]
    exact positive
  refinesInitial stage atom member :=
    status_refines_of_le (Nat.zero_le stage.fuel)
      atom.item

/-- Pair the lower and upper probability readings at the same retained stage. -/
def observation (stage :
  Stage) : Approximation.PairedObservation
  lower
  upper where
  lowerState := stage
  upperState := stage
  ordered := (bound stage).valid

/-- The located pair of retained lower and upper probability processes.

Accuracy requests move to the complete stage with exact zero gap, preserving the original stage-indexed observation and
refinement bounds. -/
def located :
  Approximation.LocatedPair lower
  upper where
  State := Stage
  observation := observation
  initial := .start
  request _ _ _ := .complete
  request_refines stage epsilon positive := by
    have refines := complete_bound_refines stage
    exact ⟨refines.lower, refines.upper⟩
  accurate stage epsilon positive := by
    have zeroGap : (observation .complete).gap = 0 := by
      decide
    rw [zeroGap]
    exact positive
  refinesInitial stage := by
    have refines := bound_refines_start stage
    exact ⟨refines.lower, refines.upper⟩

/-- The displayed finite inspections include both resolved routes and a retained unresolved scan.

Route E remains unresolved at fuel four and becomes true at fuel six; the other listed inspections retain their concrete
Boolean outcomes. -/
theorem inspection_table :
    inspect 3
      routeA = some true ∧
      inspect 3
        routeB = some false ∧
      inspect 4
        routeC = some true ∧
      inspect 4
        routeE = none ∧
      inspect 6
        routeE = some true := by
  decide

/-- The original route law has four successful and four unsuccessful first-arrival routes. -/
theorem route_outcomes :
    firstArrival
      routeA = true ∧
      firstArrival
      routeB = false ∧
      firstArrival
        routeC = true ∧
        firstArrival
        routeD = false ∧
      firstArrival
        routeE = true ∧
        firstArrival
        routeF = false ∧
      firstArrival
        routeG = true ∧
        firstArrival
        routeH = false := by
  decide

/-- The retained probability endpoints tighten to the exact value three fifths.

Lists the original start, shallow, medium and complete intervals with their distinct rational endpoints. -/
theorem staged_endpoints :
    lower.bound .start = 0 ∧
      upper.bound .start = 1 ∧
      lower.bound .shallow = 3 / 20 ∧
        upper.bound .shallow = 13 / 20 ∧
      lower.bound .medium = 7 / 20 ∧
        upper.bound .medium = 3 / 5 ∧
      lower.bound .complete = 3 / 5 ∧
        upper.bound .complete = 3 / 5 := by
  decide

/-- The original eight-route law assigns first-arrival probability three fifths. -/
theorem exact_probability :
    distribution.probability
      firstArrival = 3 / 5 := by
  decide

/-- The medium-stage interval contains the actual first-arrival probability. -/
theorem
  probability_inside_medium_bound
  :
    (bound .medium).Contains
      (distribution.probability
      firstArrival) :=
  classification.probability_mem_bound .medium

/-- A one-tenth request returns the exact three-fifths probability interval.

The retained requested state's lower and upper endpoints agree and its interval width is zero. -/
theorem located_request_exact :
    let process := located.toBoundProcess
    let state := process.request process.initial (1 / 10) (by decide)
    (process.bound state).lower = 3 / 5 ∧
      (process.bound state).upper = 3 / 5 ∧
      (process.bound state).width = 0 := by
  decide

end Purelib.Examples.Measure.Probability.Classification.FirstArrival.WorkedExamples

end
