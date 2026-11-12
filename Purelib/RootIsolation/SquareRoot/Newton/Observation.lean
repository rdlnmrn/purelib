module

public import Purelib.RootIsolation.SquareRoot.Newton.Search
public import Purelib.Computation.Query.Boundary
import Purelib.Data.List.Append

/-!
# Predicate requests of the finite rounded square-root search

The original search's acceptance callback is an explicit query at each
tested rational point. Axis projections retain their original order and
short circuit. Rounding and Newton proposals are finite control work.
The returned point forgets the predicate proof; the complete trace retains
every actual check, including rejected and repeated points.
-/

public section

namespace Purelib.RootIsolation.SquareRoot.Newton.Search

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Computation.Query

namespace Observation

/-- Check one supplied point and return it precisely when its displayed predicate reply accepts. -/
@[expose] def check (point : Canonical) : Protocol Canonical Bool (Option Canonical) :=
  (Protocol.query point).map fun accepted => if accepted then some point else none

/-- Check the original real, imaginary and unprojected proposals in their original short-circuit order. -/
@[expose] def select (parameter point : Canonical) : Protocol Canonical Bool (Option Canonical) :=
  if parameter.im = 0 then
    (check ⟨point.re, 0⟩).bind fun real =>
      match real with
      | some accepted => Protocol.pure (some accepted)
      | none => (check ⟨0, point.im⟩).bind fun imaginary =>
          match imaginary with
          | some accepted => Protocol.pure (some accepted)
          | none => check point
  else check point

/-- Compile the finite rounded search, displaying every call of its acceptance predicate.

The same fuel, grid and rounded Newton point determine each subsequent
attempt. A failed finite search retains its complete check trace.
-/
@[expose] def search (parameter : Canonical) :
    Nat → Fraction.Rational → Canonical → Protocol Canonical Bool (Option Canonical)
  | 0, _, _ => Protocol.pure none
  | fuel + 1, grid, proposal =>
      let point := Grid.Nearest.Basic.rounded grid proposal
      (select parameter point).bind fun selected =>
        match selected with
        | some accepted => Protocol.pure (some accepted)
        | none => search parameter fuel (grid / 4) (Newton.Basic.step parameter point)

/-- Read the original predicate's exact decidable answer at the requested rational point. -/
@[expose] def answer (acceptable : Canonical → Prop) [DecidablePred acceptable]
    (point : Canonical) : Bool := decide (acceptable point)

/-- The displayed single check forgets only the original successful predicate proof. -/
private theorem check_value (acceptable : Canonical → Prop) [DecidablePred acceptable]
    (point : Canonical) :
    ((check point).run (answer acceptable)).value =
      if acceptable point then some point else none := by
  change (if decide (acceptable point) then some point else none) = _
  by_cases valid : acceptable point
  · rewrite [if_pos valid, decide_eq_true valid]
    rfl
  · rewrite [if_neg valid, decide_eq_false valid]
    rfl

/-- The compiled selector returns exactly the original selector's rational point. -/
theorem select_value (parameter point : Canonical) (acceptable : Canonical → Prop)
    [DecidablePred acceptable] :
    ((select parameter point).run (answer acceptable)).value =
      (Search.select parameter acceptable point).map Subtype.val := by
  by_cases axis : parameter.im = 0
  · unfold select
    rewrite [if_pos axis, Protocol.bind_run_value, check_value]
    by_cases real : acceptable (⟨point.re, 0⟩ : Canonical)
    · rewrite [if_pos real]
      unfold Search.select
      rewrite [if_pos axis, dif_pos real]
      rfl
    · rewrite [if_neg real]
      rewrite [Protocol.bind_run_value, check_value]
      by_cases imaginary : acceptable (⟨0, point.im⟩ : Canonical)
      · rewrite [if_pos imaginary]
        unfold Search.select
        rewrite [if_pos axis, dif_neg real, dif_pos imaginary]
        rfl
      · rewrite [if_neg imaginary, check_value]
        unfold Search.select
        rewrite [if_pos axis, dif_neg real, dif_neg imaginary]
        by_cases valid : acceptable point
        · rewrite [if_pos valid, dif_pos valid]
          rfl
        · rewrite [if_neg valid, dif_neg valid]
          rfl
  · unfold select
    rewrite [if_neg axis, check_value]
    unfold Search.select
    rewrite [if_neg axis]
    by_cases valid : acceptable point
    · rewrite [if_pos valid, dif_pos valid]
      rfl
    · rewrite [if_neg valid, dif_neg valid]
      rfl

/-- The compiled finite search returns exactly the original search's point for every input and predicate. -/
theorem search_value (parameter : Canonical) (acceptable : Canonical → Prop)
    [DecidablePred acceptable] (fuel : Nat) (grid : Fraction.Rational) (proposal : Canonical) :
    ((search parameter fuel grid proposal).run (answer acceptable)).value =
      (Search.search parameter acceptable fuel grid proposal).map Subtype.val := by
  induction fuel generalizing grid proposal with
  | zero => rfl
  | succ fuel induction =>
      rewrite [search, Protocol.bind_run_value, select_value, Search.search_step]
      cases selected : Search.select parameter acceptable (Grid.Nearest.Basic.rounded grid proposal) with
      | some accepted => rfl
      | none => exact induction _ _

/-- Retain the complete executed predicate trace with the original search's exact numerical result. -/
@[expose] def record (parameter : Canonical) (acceptable : Canonical → Prop)
    [DecidablePred acceptable] (fuel : Nat) (grid : Fraction.Rational) (proposal : Canonical) :
    Basic.Execution Canonical Bool (Option Canonical) :=
  (search parameter fuel grid proposal).run (answer acceptable)

/-- The complete recorded execution consists of the original numerical result and the same ordered predicate checks. -/
theorem recorded_execution (parameter : Canonical) (acceptable : Canonical → Prop)
    [DecidablePred acceptable] (fuel : Nat) (grid : Fraction.Rational) (proposal : Canonical) :
    (search parameter fuel grid proposal).run (answer acceptable) =
      ⟨(Search.search parameter acceptable fuel grid proposal).map Subtype.val,
        (record parameter acceptable fuel grid proposal).trace⟩ := by
  apply Basic.Execution.ext
  · exact search_value parameter acceptable fuel grid proposal
  · rfl

/-- Arbitrary predicate payload changes outside the consumed checks preserve the entire finite search execution. -/
theorem payload_erasure {Payload : Type} (parameter : Canonical) (acceptable : Canonical → Prop)
    [DecidablePred acceptable] (fuel : Nat) (grid : Fraction.Rational) (proposal : Canonical)
    (payload : Payload) (outside : Payload → Canonical → Bool) :
    (search parameter fuel grid proposal).run
        (Boundary.Trace.overlay (record parameter acceptable fuel grid proposal).trace (outside payload)) =
      record parameter acceptable fuel grid proposal :=
  Protocol.annotation_erasure (search parameter fuel grid proposal) (answer acceptable) payload outside

end Observation

end Purelib.RootIsolation.SquareRoot.Newton.Search
