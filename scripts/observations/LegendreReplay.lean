module
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.String.Parsing
public import Purelib.Data.List.ToString
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Examples.Curves.Legendre.Prepared.LoopBase
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Riemann.Paths.PreparedClearPathModels
public import Purelib.Riemann.Paths.PreparedClearPathModels.Execution
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Examples.Curves.Legendre.Replay
import Init.Prelude
import Init.System.IO
import Init.System.IOError
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Computation.Query.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Examples.Curves.Legendre.LoopBaseBranches
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.Periods.PeriodReplay
import Purelib.RootIsolation.State.WindingOne.Basic

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.List

open Purelib.Approximation.Rational.Geometric

open Purelib.CCL.Progressive

open Purelib.Data.CCL.Transducer.Emission.Initial

open Purelib.Examples.Curves.Legendre

open Purelib.Examples.Curves.Legendre.Prepared

open Purelib.Integration

open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath

public section

/-!
Short-iteration diagnostic for the actual cached period observation runner.
Build `legendre_replay_harness` once for native timing, then run the retained
binary in `.lake/build/bin/`.  `scripts/run-lake.sh env lean --run` on this
file remains useful for the shortest interpreted iteration.  The caller
must provide the repository's explicit timeout and systemd memory bound for
runtime probes.  These diagnostics are not proof gates.
-/

namespace LegendreReplayHarness

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming
  CoefficientPolynomial -> GaussianPolynomial
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction renaming Rational -> Coordinate
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

/-- Print and flush one retained-period replay diagnostic message. -/
@[expose] def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate one retained path report after the diagnostic clock starts. -/
@[noinline, expose] def evaluateAttempt {Value : Type} (attempt : Unit → Value) : IO Value :=
  pure (attempt ())

/-- Inspect one actual finite path execution and optionally resume its saved prefix.

The completed segment count and stop label describe this retained execution.
The typed report remains the authority; numerical failure is inconclusive. -/
@[expose] def bankTrial {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Gaussian}
    {path : ClearPath polynomial ambient start finish} {within : path.WithinAmbient}
    {owner : Owner (polynomial.eval start)} {policy : DyadicBank.Policy} {depth : Nat}
    {diameter : Coordinate} {positive : 0 < diameter}
    (label : String)
    (attempt : Unit → DyadicBank.Execution policy depth diameter positive path within owner)
    (additionalBudget : Nat := 0) : IO Unit := do
  let started ← IO.monoMsNow
  report s!"{label}: starting measured bank"
  let initial ← evaluateAttempt attempt
  report s!"{label}: completed={initial.completed}, consumed={initial.consumed}, budget={initial.budget}"
  let retained ← if additionalBudget = 0 then pure initial
    else evaluateAttempt fun _ => initial.resume additionalBudget
  match retained.stoppingReason with
  | some reason => report s!"{label}: finite attempt stopped: {reason}"
  | none => pure ()
  let succeeded := retained.bank?.isSome
  let finished ← IO.monoMsNow
  report
    s!"{label}: success={succeeded}, completed={retained.completed}, \
      consumed={retained.consumed}, budget={retained.budget}, {finished - started} ms"
  unless succeeded do
    throw (IO.userError "measured bank attempt remains inconclusive; its stopped prefix is retained")

/-- Run the selected exact finite bank-construction diagnostic. -/
@[expose] def bank (label : String) : IO Unit := do
  match label with
  | "a-forward" => bankTrial label fun _ =>
      (LoopBase.aForwardAttempt
        LoopBase.connectorInnerDepth)
  | "a-forward-uniform" => bankTrial label fun _ =>
      (DyadicBank.executeUniform
        LoopBase.workingAConnector
        LoopBase.workingAConnector_withinAmbient
        (LoopBase.branchSquareRootOwner 0 0)
        LoopBase.connectorInnerDepth
        LoopBase.workingRootDiameter
        LoopBase.workingRootDiameter_positive)
  | "a-forward-mesh" => bankTrial label fun _ =>
      (DyadicBank.executeMeshSafe
        LoopBase.workingAConnector
        LoopBase.workingAConnector_withinAmbient
        (LoopBase.branchSquareRootOwner 0 0)
        LoopBase.connectorInnerDepth
        LoopBase.workingRootDiameter
        LoopBase.workingRootDiameter_positive)
  | "a-right" => bankTrial label fun _ =>
      (LoopBase.aRightBoundaryAttempt
        LoopBase.rightBoundaryInnerDepth)
  | "a-backward" => bankTrial label fun _ =>
      (LoopBase.aBackwardAttempt
        LoopBase.connectorInnerDepth)
  | "a-left" => bankTrial label fun _ =>
      (LoopBase.aLeftBoundaryAttempt
        LoopBase.leftBoundaryInnerDepth)
  | "b-forward" => bankTrial label fun _ =>
      (LoopBase.bForwardAttempt
        LoopBase.bConnectorInnerDepth)
  | "b-backward" => bankTrial label fun _ =>
      (LoopBase.bBackwardAttempt
        LoopBase.bConnectorInnerDepth)
  | _ => throw (IO.userError "unknown measured bank")

/-- Execute a finite prefix of the original A connector and resume only its unresolved suffix.

Both budgets count original segments. The retained direct policy, depth,
diameter and starting owner remain fixed across continuation. -/
@[expose] def resumeBank (budget additionalBudget : Nat) : IO Unit :=
  bankTrial "a-forward-resume" (fun _ =>
    DyadicBank.executeBounded .direct LoopBase.workingAConnector LoopBase.workingAConnector_withinAmbient
      (LoopBase.branchSquareRootOwner 0 0) LoopBase.connectorInnerDepth
      LoopBase.workingRootDiameter LoopBase.workingRootDiameter_positive budget) additionalBudget

/-- Force the selected attempt before asking for its total witness, so a slow fallback is distinguishable from a slow
successful measured bank. -/
@[noinline, expose] def inspectAttempt (side : String)
    (context : LoopBase.PreparedLegendreContext) : IO Unit := do
  if side = "a" then
    match context.measuredA with
    | .ok _ => report "a: measured banks accepted"
    | .error stage => report s!"a: measured bank rejected at {repr stage.stage}; total witness will use fallback"
  else
    match context.measuredB with
    | .ok _ => report "b: measured banks accepted"
    | .error stage => report s!"b: measured bank rejected at {repr stage.stage}; total witness will use fallback"

/-- Isolate one retained numerical model, with no CCL prefix computation. Reading the sample and allowance forces the
same fields consumed by replay. -/
@[expose] def modelTrial (side : String) (index : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  report s!"{side}: preparing model {index} only"
  let context := LoopBase.preparedLegendreContext ()
  inspectAttempt side context
  let entry := if side = "a" then Replay.aEntry context (index + 1)
    else Replay.bEntry context
  report s!"{side}: control ready; producing model {index}"
  let stage := entry.cached.stage index
  report
    s!"{side}: cells={stage.model.cells.length}; sample denominator bits=({stage.sample.re.den.log2}, \
      {stage.sample.im.den.log2}); allowance denominator bits={stage.allowance.den.log2}"
  let finish ← IO.monoMsNow
  report s!"{side}: model {index} materialized in {finish - start} ms"

/-- Record and replay a finite CCL observation of the retained Legendre period program.

Check exact machine state, selected model, sample, allowance, ball and requested word length. -/
@[expose] def trial (side : String) (count : Nat) : IO Unit := do
  let start ← IO.monoMsNow
  report s!"{side}: allocating retained context"
  let context := LoopBase.preparedLegendreContext ()
  inspectAttempt side context
  let entry := if side = "a" then Replay.aEntry context 64
    else Replay.bEntry context
  let request : CertifiedProgram.Request := ⟨0, 1, by decide⟩
  report s!"{side}: selected model index {entry.selectedIndex request}; requesting {count} bits"
  let initialIndex := Search.firstQuarterBelow entry.cached.errorScale
    (entry.selectedIndex request) Budget.initialRadiusSq
  report s!"{side}: initial controller model index {initialIndex}"
  let recorded := entry.record request count
  report s!"{side}: word {recorded.observation.word}; queries {recorded.trace.map (·.query)}"
  match Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Transcript.replay (IntegrationReplay.control
    entry.cached) request count recorded.trace with
  | .error _ => throw (IO.userError "generated period transcript failed to replay")
  | .ok replayed =>
      unless replayed.machine = recorded.observation.machine ∧
          replayed.selected.index = recorded.observation.selected.index ∧
          replayed.selected.sample = recorded.observation.selected.sample ∧
          replayed.selected.allowance = recorded.observation.selected.allowance ∧
          replayed.selected.ball.center = recorded.observation.selected.ball.center ∧
          replayed.selected.ball.radiusSq = recorded.observation.selected.ball.radiusSq do
        throw (IO.userError "replayed observation differs from the generated observation")
      unless replayed.word.length = count do
        throw (IO.userError "wrong prefix length")
      let finish ← IO.monoMsNow
      report s!"{side}: full observation replay checked in {finish - start} ms"

end LegendreReplayHarness

/-- Parse and run the requested bank, model or finite-period observation diagnostic. -/
@[expose] def main (arguments : List String) : IO Unit :=
  match arguments with
  | ["bank", label] => LegendreReplayHarness.bank label
  | ["bank-resume", budget, additionalBudget] =>
      match Purelib.Data.String.toNat? budget, Purelib.Data.String.toNat? additionalBudget with
      | some initial, some additional => LegendreReplayHarness.resumeBank initial additional
      | _, _ => throw (IO.userError "segment budgets must be natural numbers")
  | ["model", side, index] =>
      match Purelib.Data.String.toNat? index with
      | some count =>
          if side = "a" ∨ side = "b" then LegendreReplayHarness.modelTrial side count
          else throw (IO.userError "side must be a or b")
      | none => throw (IO.userError "model index must be a natural number")
  | [side, bits] =>
      match Purelib.Data.String.toNat? bits with
      | some count =>
          if side = "a" ∨ side = "b" then LegendreReplayHarness.trial side count
          else throw (IO.userError "side must be a or b")
      | none => throw (IO.userError "bit count must be a natural number")
  | _ => throw (IO.userError
      "usage: a|b BIT_COUNT, bank BANK_NAME, bank-resume INITIAL_BUDGET EXTRA_BUDGET, or model a|b INDEX")
