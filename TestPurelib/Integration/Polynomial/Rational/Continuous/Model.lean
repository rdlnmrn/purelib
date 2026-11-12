module
import Purelib.Integration.Polynomial.Rational.Continuous.Model
import Purelib.Integration.Cell.Source.Continuous.Observation

/-! Original rational and Gaussian polynomial samples in computed source enclosures. -/

namespace TestPurelib.Integration.Polynomial.Rational.Continuous.Model

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Integration.Polynomial.Rational.Continuous
open Purelib.Polynomial.Dense.Rational

/-- Original descending coefficients of the nonconstant quadratic source. -/
private def square : Basic.CoordinatePolynomial := ⟨[1, 0, 0]⟩

/-- Original descending coefficients of a nonconstant linear source. -/
private def linear : Basic.CoordinatePolynomial := ⟨[2, 3]⟩

/-- Independent positive requests for the same original polynomial. -/
private def first : AccuracyRequest := ⟨8, by decide⟩
private def second : AccuracyRequest := ⟨4, by decide⟩

example : (Model.rationalCell square).integralSample.re = (1 / 3 : Fraction.Rational) := by decide +kernel

example : (Model.rationalCell linear).integralSample.re = (4 : Fraction.Rational) := by decide +kernel

example : (integralBound (integrate square first).frontier.cells).Contains
    (Model.rationalCell square).integralSample.re := Model.rational_cell_contains square first

example : (integralBound (integrate square second).frontier.cells).Contains
    (Model.rationalCell square).integralSample.re := Model.rational_cell_contains square second

example : (integralBound (integrate linear first).frontier.cells).Contains
    (Model.rationalCell linear).integralSample.re := Model.rational_cell_contains linear first

example : (Purelib.Integration.Polynomial.Gaussian.Continuous.model (Model.gaussian square)).integralSample =
    (Model.rationalCell square).integralSample := Model.gaussian_cell_sample square

/-- The exact-source preparation retained by the original polynomial integration. -/
private def prepared := (integrate square first).preparation

open Purelib.Integration.SourceFrontier.Continuous.Observation

/-- The original polynomial result's retained exact point observations. -/
private def cached := (integrate square first).frontier.cells.map (fun cell => cell.item)

/-- The actual cache-aware observation of the same original preparation. -/
private def cachedProgram := cachedComputation prepared cached prepared.partition.intervals.attach

/-- A source reply with an intentionally incorrect tag for the first original interval. -/
private def wrongTag (_ : Entry prepared) : SourcePoint square.eval :=
  SourcePoint.observe square.eval ⟨0, 1⟩ 1 (by decide) (by decide)

example : (cachedProgram.protocol.run (originalReply prepared)).trace.length = 0 := by decide +kernel

example : (((cachedProgram.protocol.run (originalReply prepared)).value).map (List.map (cachedCell prepared))) =
    .ok (prepared.frontierCached cached).cells := cached_original_cells prepared cached

example : (cachedProgram.protocol.replayExact (cachedProgram.protocol.run (originalReply prepared)).trace).map
    (fun result => result.map (List.map (cachedCell prepared))) = .ok (.ok (prepared.frontierCached cached).cells) :=
  cached_replay_cells prepared cached

example : ((cachedResultComputation prepared cached).protocol.run (originalReply prepared)).value =
    .ok (SourceFrontier.Continuous.buildCached (Bounds.Uniform.modulus square) cached first) :=
  cachedResult_original (Bounds.Uniform.modulus square) cached first

example : (cachedResultComputation prepared cached).protocol.replayExact
    ((cachedResultComputation prepared cached).protocol.run (originalReply prepared)).trace =
      .ok (.ok (SourceFrontier.Continuous.buildCached (Bounds.Uniform.modulus square) cached first)) :=
  cachedResult_replay (Bounds.Uniform.modulus square) cached first

example : (match ((cachedComputation prepared [] prepared.partition.intervals.attach).protocol.run wrongTag).value with
    | .error invalid => decide (invalid.reported = 1)
    | .ok _ => false) = true := by decide +kernel

example : ((cachedComputation prepared [] prepared.partition.intervals.attach).protocol.run wrongTag).trace.length =
    1 := by decide +kernel

example : (((computation prepared).protocol.run (originalReply prepared)).value.map (cachedCell prepared)) =
    prepared.frontier.cells := original_cells prepared

example : ((computation prepared).protocol.replayExact
    ((computation prepared).protocol.run (originalReply prepared)).trace).map (List.map (cachedCell prepared)) =
      .ok prepared.frontier.cells := replay_cells prepared

example {Payload : Type} (payload : Payload)
    (outside : Payload → Entry prepared → SourcePoint _) :
    (computation prepared).protocol.run (Purelib.Computation.Query.Boundary.Trace.overlay
      ((computation prepared).protocol.run (originalReply prepared)).trace (outside payload)) =
        (computation prepared).protocol.run (originalReply prepared) :=
  payload_erasure prepared payload outside

end TestPurelib.Integration.Polynomial.Rational.Continuous.Model
