module

public import Purelib.RootIsolation.SquareRoot.Newton.Observation
public import Purelib.Computation.Query.Program

/-!
# Expanding each actual finite root acceptance callback

The original axis order, grid, proposals and fuel remain fixed. Each
acceptance callback may run its own displayed protocol. Expansion retains
its same Boolean reply in the outer root-search log and its actual internal
checks in the inner log, without rerunning the evaluator to obtain a trace.
-/

public section

namespace Purelib.RootIsolation.SquareRoot.Newton.Search.Observation

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Computation
open Purelib.Computation.Query

namespace Expansion

/-- The finite root-query construction with its original point, Boolean reply and selected-point carriers. -/
abbrev Construction := Query.Program Canonical Bool (Option Canonical)

/-- Retain one original callback point and the numerical selection from its Boolean reply. -/
private def check (point : Canonical) : Construction :=
  (Query.Program.query point).map fun accepted => if accepted then some point else none

/-- Retain the original ordered axis checks and their exact short-circuit continuation. -/
private def select (parameter point : Canonical) : Construction :=
  if parameter.im = 0 then
    (check ⟨point.re, 0⟩).bind fun real =>
      match real with
      | some accepted => .pure (some accepted)
      | none => (check ⟨0, point.im⟩).bind fun imaginary =>
          match imaginary with
          | some accepted => .pure (some accepted)
          | none => check point
  else check point

/-- Retain the original rounded finite attempts and same actual Newton successor after a rejected attempt. -/
def search (parameter : Canonical) : Nat → Fraction.Rational → Canonical → Construction
  | 0, _, _ => .pure none
  | fuel + 1, grid, proposal =>
      let point := Grid.Nearest.Basic.rounded grid proposal
      (select parameter point).bind fun selected =>
        match selected with
        | some accepted => .pure (some accepted)
        | none => search parameter fuel (grid / 4) (Newton.Basic.step parameter point)

/-- The retained selector compiles to the complete original selection execution and callback trace. -/
private theorem select_execution (parameter point : Canonical) (oracle : Canonical → Bool) :
    (select parameter point).protocol.run oracle = (Observation.select parameter point).run oracle := by
  unfold select Observation.select
  by_cases axis : parameter.im = 0
  · rewrite [if_pos axis, if_pos axis, Query.Program.bind_execution]
    apply Protocol.bind_execution_eq _ _ _ _ oracle rfl
    cases ((check (⟨point.re, 0⟩ : Canonical)).protocol.run oracle).value with
    | some accepted => rfl
    | none =>
        rewrite [Query.Program.bind_execution]
        apply Protocol.bind_execution_eq _ _ _ _ oracle rfl
        cases ((check (⟨0, point.im⟩ : Canonical)).protocol.run oracle).value with
        | some accepted => rfl
        | none => rfl
  · rewrite [if_neg axis, if_neg axis]
    rfl

/-- Compilation preserves the original finite root-search result and complete ordered callback trace for all inputs. -/
theorem search_execution (parameter : Canonical) (fuel : Nat) (grid : Fraction.Rational)
    (proposal : Canonical) (oracle : Canonical → Bool) :
    (search parameter fuel grid proposal).protocol.run oracle =
      (Observation.search parameter fuel grid proposal).run oracle := by
  induction fuel generalizing grid proposal with
  | zero => rfl
  | succ fuel induction =>
      rewrite [search, Query.Program.bind_execution]
      unfold Observation.search
      apply Protocol.bind_execution_eq _ _ _ _ oracle (select_execution _ _ _)
      cases ((Observation.select parameter (Grid.Nearest.Basic.rounded grid proposal)).run oracle).value with
      | some accepted => rfl
      | none => exact induction _ _

/-- Expand the actual acceptance callbacks while retaining the complete original root-search execution as the value. -/
def computation {Question Reply : Type} (handlers : Canonical → Protocol Question Reply Bool)
    (parameter : Canonical) (fuel : Nat) (grid : Fraction.Rational) (proposal : Canonical) :
    Protocol Question Reply (Basic.Execution Canonical Bool (Option Canonical)) :=
  (search parameter fuel grid proposal).expand handlers

/-- The expanded run retains the exact original numerical root search and every original Boolean callback reply. -/
theorem computation_value {Question Reply : Type} (handlers : Canonical → Protocol Question Reply Bool)
    (parameter : Canonical) (fuel : Nat) (grid : Fraction.Rational) (proposal : Canonical)
    (oracle : Question → Reply) :
    ((computation handlers parameter fuel grid proposal).run oracle).value =
      (Observation.search parameter fuel grid proposal).run
        (fun point => ((handlers point).run oracle).value) :=
  (Query.Program.expand_value handlers (search parameter fuel grid proposal) oracle).trans
    (search_execution parameter fuel grid proposal _)

/-- Replay from the inner checks retains the complete original root-search result and outer callback log. -/
theorem computation_replay {Question Reply : Type} (handlers : Canonical → Protocol Question Reply Bool)
    (parameter : Canonical) (fuel : Nat) (grid : Fraction.Rational) (proposal : Canonical)
    (oracle : Question → Reply) :
    (computation handlers parameter fuel grid proposal).replayExact
      ((computation handlers parameter fuel grid proposal).run oracle).trace =
      .ok ((Observation.search parameter fuel grid proposal).run
        (fun point => ((handlers point).run oracle).value)) :=
  ((computation handlers parameter fuel grid proposal).replayExact_run oracle).trans
    (congrArg Except.ok (computation_value handlers parameter fuel grid proposal oracle))

/-- Outside-inner-check payload changes preserve the original root result, both logs and every repeated occurrence. -/
theorem payload_erasure {Question Reply Payload : Type} [DecidableEq Question]
    (handlers : Canonical → Protocol Question Reply Bool) (parameter : Canonical) (fuel : Nat)
    (grid : Fraction.Rational) (proposal : Canonical) (oracle : Question → Reply)
    (payload : Payload) (outside : Payload → Question → Reply) :
    let computation := computation handlers parameter fuel grid proposal
    computation.run (Boundary.Trace.overlay (computation.run oracle).trace (outside payload)) =
      computation.run oracle :=
  Protocol.annotation_erasure (computation handlers parameter fuel grid proposal) oracle payload outside

end Expansion

end Purelib.RootIsolation.SquareRoot.Newton.Search.Observation
