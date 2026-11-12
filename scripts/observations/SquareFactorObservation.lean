module
import Purelib.System.IO
import Purelib.Data.String.Basic
import Purelib.Data.String.Parsing
import Purelib.Data.List.ToString
import Purelib.Data.Int.Decimal
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Integration.Algebraic.SquareFactor.Accuracy
import Purelib.Integration.Algebraic.SquareFactor.ObservationInput
import Purelib.Integration.Algebraic.SquareFactor.PathContinuation
import Purelib.Integration.Algebraic.SquareFactor.PathInput
import Purelib.Integration.Algebraic.SquareFactor.PathObservation
import Purelib.Integration.Algebraic.SquareFactor.PolynomialObservation
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Branches.ClearSheetContinuation

/-!
Observe an original-coordinate differential on `y² = x²(x³+1)` along the segment
from one to seventeen sixteenths. `budget LAYER` reports the computed resolution
without constructing an observation; `observe BIT_COUNT` runs integration and
checks its source-free replay and requested accuracy.
-/

open scoped Purelib.Data.String Purelib.Data.Int.Decimal Purelib.Data.List

namespace SquareFactorObservationHarness

open Purelib.Approximation.Rational
open Purelib.CCL.Progressive
open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Integration.Algebraic.SquareFactor.PathObservation (Policy ObservationRequest)
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation
open Purelib.Polynomial
open Purelib.Riemann.Branches

/-- `p=x²(x³+1)`: repeated input with a positive-genus squarefree reduction. The retained nonstationary path avoids the
removed coordinate zero. -/
def polynomial : GaussianPolynomial := ⟨[1, 0, 0, 1, 0, 0]⟩
/-- The nonstationary real segment from one to seventeen sixteenths. -/
def segment : Segment := ⟨1, ⟨17 / 16, 0⟩⟩
/-- The original-coordinate differential request of degree zero. -/
def differential : Request := .original 0

/-- The retained integration refinement and observation schedule for the fixture. -/
def policy : Policy := ⟨⟨0, 0⟩, ⟨4, [4]⟩⟩
/-- The original observation request at source index zero and target one. -/
def query : ObservationRequest := ⟨0, 1, by decide⟩

/-- Print and flush one square-factor integration diagnostic message. -/
def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Evaluate a thunk through IO without inlining its timing boundary. -/
@[noinline] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Render the exact numerator and denominator of a rational value. -/
def fractionText (value : PathInput.Coordinate) : String := s!"{value.num}/{value.den}"

/-- Prepare the original polynomial, differential and path and verify the intended squarefree reduction degrees. -/
def prepare : IO (ObservationInput.PreparedEntry
    polynomial differential segment 0 .originalCoordinate) := do
  report "square-factor: preparing raw polynomial and original-coordinate segment"
  let started ← IO.monoMsNow
  let result ← evaluate fun _ =>
    ObservationInput.prepare polynomial differential segment 0 .originalCoordinate
  match result with
  | .error _ => throw (IO.userError "raw repeated-factor input was rejected")
  | .ok entry =>
      report
        s!"square-factor: input accepted in {(← IO.monoMsNow) - started} ms; reduced \
          degree={entry.prepared.reduction.radicand.natDegree}; square-factor \
          degree={entry.prepared.reduction.squareFactor.natDegree}"
      unless entry.prepared.reduction.radicand.natDegree = 3 ∧
          entry.prepared.reduction.squareFactor.natDegree = 1 do
        throw (IO.userError "example does not have the intended positive-genus repeated-factor reduction")
      pure entry

/-- Report the original coefficient bounds and computed continuation resolution for a selected layer.

The diagnostic reads the actual parameter and root scales without constructing a numerical observation. -/
def budget (index : Nat) : IO Unit := do
  let entry ← prepare
  report
    s!"square-factor: numerator={entry.prepared.weight.numerator.coeffs.length} coefficients; \
      denominator={entry.prepared.weight.denominator.coeffs.length} coefficients"
  report
    s!"square-factor: numerator value ceiling={fractionText entry.data.numerator.valueBound}; squared \
      slope={fractionText entry.data.numerator.slopeBound}"
  report
    s!"square-factor: denominator value ceiling={fractionText entry.data.denominator.valueBound}; squared \
      floor={fractionText entry.data.denominator.lowerBound}; squared \
      slope={fractionText entry.data.denominator.slopeBound}"
  report
    s!"square-factor: radicand value ceiling={fractionText entry.data.radicand.valueBound}; squared \
      floor={fractionText entry.data.radicand.lowerBound}; coordinate \
      floor={fractionText entry.data.radicand.coordinateLower}"
  report s!"square-factor: root squared-norm floor={fractionText entry.data.rootNormFloor}"
  let clear := PathContinuation.clearSegment entry.safe
  let parameterPolynomial := ClearSheetContinuation.segmentPolynomial clear
  let slope ← evaluate fun _ => Dense.Gaussian.Bounds.Box.denseEvalNormLipschitzBound
    parameterPolynomial ClearSheetContinuation.parameterAmbient
  let clampedSlope ← evaluate fun _ => Dense.Gaussian.Bounds.Box.denseLipschitzBound
    parameterPolynomial ClearSheetContinuation.parameterAmbient
  report
    s!"square-factor: raw squared-slope bound={fractionText slope}; clamped continuation \
      slope={fractionText clampedSlope}"
  let target := Geometric.Basic.quarterRadius 1 index
  let resolution ← evaluate fun _ => Accuracy.resolve entry.safe 1 (by decide)
    target (Geometric.Basic.quarterRadius_pos (by decide) index)
  let depth ← evaluate fun _ => PathContinuation.maximumDepth entry.safe
    resolution.rootDiameter resolution.minimumDepth
  report
    s!"square-factor: parameter scale={fractionText resolution.parameterScale}; root \
      scale={fractionText resolution.rootScale}"
  report
    s!"square-factor: layer={index}; target={fractionText target}; root \
      diameter={fractionText resolution.rootDiameter}; numerical depth={resolution.minimumDepth}; maximum continuation \
      depth={depth}; maximum cells=2^{depth}"

/-- Run a nonempty original-differential observation and verify its exact source-free replay.

Check complete machine and selected model data, requested output length and both enclosure bounds. -/
def observe (count : Nat) : IO Unit := do
  unless 0 < count do throw (IO.userError "observation must emit a nonempty prefix")
  let entry ← prepare
  report s!"square-factor: starting actual original-differential observation, bits={count}"
  let started ← IO.monoMsNow
  report "square-factor: forcing the shared original-differential source"
  let source ← evaluate fun _ => entry.source
  report
    s!"square-factor: shared source ready in {(← IO.monoMsNow) - started} ms; error \
      scale={fractionText source.value.errorScale}"
  let observed ← evaluate fun _ =>
    PolynomialObservation.observePrepared entry policy query count
  let selected ← evaluate fun _ => observed.recorded.observation
  let preparedRequest ← evaluate fun _ => observed.preparedRequest
  report s!"square-factor: observed in {(← IO.monoMsNow) - started} ms; word={selected.word}"
  let replayed ← evaluate fun _ => Transcript.replay
    (IntegrationReplay.control (PathObservation.program entry.source policy))
    query count observed.recorded.trace
  match replayed with
  | .error _ => throw (IO.userError "observation failed source-free replay")
  | .ok replayed =>
      unless replayed.machine == selected.machine && replayed.selected.index == preparedRequest.index &&
          replayed.selected.sample == preparedRequest.cache.sample &&
          replayed.selected.allowance == preparedRequest.cache.allowance &&
          replayed.selected.ball.center == preparedRequest.cache.sample &&
          replayed.selected.ball.radiusSq == preparedRequest.radiusSq && replayed.word.length == count &&
          decide (replayed.selected.ball.radiusSq < query.target ∧ replayed.selected.allowance < query.target) do
        throw (IO.userError "actual original-differential observation failed its numerical/replay checks")
      report s!"square-factor: replay and accuracy passed; queries={observed.recorded.trace.map (·.query)}"

end SquareFactorObservationHarness

/-- Run the coefficient-bound report or a nonempty original-coordinate observation. -/
public def main (arguments : List String) : IO Unit :=
  match arguments with
  | ["budget", index] =>
      match Purelib.Data.String.toNat? index with
      | some index => SquareFactorObservationHarness.budget index
      | none => throw (IO.userError "layer index must be a natural number")
  | ["observe", count] =>
      match Purelib.Data.String.toNat? count with
      | some count => SquareFactorObservationHarness.observe count
      | none => throw (IO.userError "count must be a natural number")
  | _ => throw (IO.userError "usage: square_factor_observation_harness budget LAYER | observe BIT_COUNT")
