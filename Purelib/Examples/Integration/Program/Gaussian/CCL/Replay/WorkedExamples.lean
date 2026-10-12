module
import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Recipe.Request
import Purelib.Computation.Query.Basic
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
import Purelib.Data.CCL.Transducer.Initial.Observation
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.MachineProjection
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Representation
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.CCL.Progressive.IntegrationQueries
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Computation.Query.Replay
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic

@[expose] public section

/-!
# Finite query and complete integration-output replay regressions

The natural-number protocol tests genuine adaptive query selection and
repetition.  The polynomial client separately exercises the real CCL output
projection, with the original complex quadratic and repeated path traversal.
Malformed logs test missing, mismatched, trailing and invalid replies.
-/

namespace Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.WorkedExamples

open Purelib.Examples.Integration.Polynomial.Gaussian
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation
open Purelib.Data.CCL.Transducer

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Integration.CertifiedProgram (Request InvalidRequest)
open Purelib.CCL.Progressive.IntegrationReplay
  (CachedProgram CachedModel Control control selectedIndex refinedName)
open Purelib.CCL.Progressive.IntegrationPrograms (polynomialProgram polynomialProgram_sample)

/-- The cached complex-polynomial integration program on the repeated path with alternating partition policy. -/
def polynomial : CachedProgram :=
  polynomialProgram Partition.WorkedExamples.repeatedPath
  Partition.WorkedExamples.alternatingPolicy

/-- The zero-start replay request with positive target one. -/
def request : Request := ⟨0, 1, by
  decide⟩

/-- The retained one-bit observation and complete query trace of the polynomial program. -/
def recorded :
  Record.Recorded
  polynomial
  request 1 :=
  Record.record
  polynomial
  request 1

/-- The recorded one-bit polynomial trace replays to its original observation. -/
theorem polynomial_replay :
    Transcript.replay (control
      polynomial)
      request 1
      recorded.trace = .ok
      recorded.observation :=
  Transcript.observation_replay
    polynomial
    request 1

/-- The one-bit trace retains both zero-index queries in their original order. -/
theorem polynomial_query_indices :
  recorded.trace.map Computation.Query.Basic.Exchange.query = [0,
  0] := open Purelib.Approximation in by
  rw [recorded.trace_eq,
    Program.Gaussian.CCL.Replay.Observation.Representation.computation_trace,
    Program.Gaussian.CCL.Replay.MachineProjection.initial_one_trace]
  change [selectedIndex (control polynomial)
    request,
    Approximation.Gaussian.Process.Recipe.refine (control
      polynomial) .source
      (selectedIndex (control polynomial)
        request)
        Data.CCL.Transducer.Emission.Initial.Budget.initialRadiusSq] = [0, 0]
  decide

/-- The polynomial program's first emitted bit is true. -/
theorem polynomial_actual_first_bit :
  recorded.observation.word = [true] := by
  rw [recorded,
    Record.recorded_prefix]
  apply Data.CCL.Transducer.Initial.Observation.advance_one_large
  change (13 / 6 : Fraction.Rational) < Data.Gaussian.Norm.Basic.normSq
    ((polynomialProgram Partition.WorkedExamples.repeatedPath
      Partition.WorkedExamples.alternatingPolicy).approximation.sample _)
  rw [polynomialProgram_sample]
  decide

/-- The selected recorded integration ball satisfies the original requested radius bound. -/
theorem polynomial_accuracy :
  recorded.observation.selected.ball.radiusSq <
  request.target :=
  Record.recorded_accurate
    polynomial
    request 1

/-- The recorded word has an actual retained machine cursor realizing its refined source process. -/
theorem polynomial_real_cursor :
    ∃ actual : Machine,
      actual.emitted = recorded.observation.word ∧
      Machine.Semantics.Basic.ExactCursor
        (refinedName polynomial
          request).process (refinedName
          polynomial
          request).state actual :=
  Record.recorded_exactCursor
    polynomial
    request 1

/-- The retained eight-bit observation and complete query trace of the polynomial program. -/
def recordedEight :
  Record.Recorded
  polynomial
  request 8 :=
  Record.record
  polynomial
  request 8

/-- The recorded eight-bit polynomial trace replays to its original observation. -/
theorem polynomial_eight_replay :
    Transcript.replay (control
      polynomial)
      request 8
      recordedEight.trace = .ok
      recordedEight.observation :=
  Transcript.observation_replay
    polynomial
    request 8

/-- The recorded polynomial output contains exactly eight bits. -/
theorem polynomial_eight_bits :
  recordedEight.observation.word.length = 8 :=
  Record.recorded_length
    polynomial
    request 8

/-- The one-bit polynomial observation is a prefix of its eight-bit observation. -/
theorem polynomial_prefix_extends :
  recorded.observation.word.IsPrefix
  recordedEight.observation.word :=
  Record.recorded_extends
    polynomial
    request 1 7

/-- The replay control with zero center and zero allowance bounds. -/
def zeroControl : Control := ⟨0, le_rfl,
  0, le_rfl⟩

/-- The canonical exact constant-one cell model used as a replay response. -/
def unitReply : CachedModel :=
  CertifiedProgram.CachedModel.canonical (operations := Program.Gaussian.Cached.Basic.modelOperations)
    ⟨[Polynomial.Gaussian.Cell.Basic.CellModel.exact 0 1 (Ascending.Gaussian.Basic.constant 1)]⟩

/-- The zero-polynomial cell response with local allowance one. -/
def allowanceReply : CachedModel :=
  CertifiedProgram.CachedModel.canonical (operations := Program.Gaussian.Cached.Basic.modelOperations)
    ⟨[{ start := 0, finish := 1, polynomial := Ascending.Gaussian.Basic.zero,
        localAllowance := 1, localAllowance_nonneg := by decide, observations := [] }]⟩

/-- An empty replay transcript reports the missing initial model query. -/
theorem missing_model :
    Transcript.replay
      zeroControl
      request 8 [] = .error (.transcript (.missing 0)) := rfl

/-- A transcript beginning at query one reports the original zero-versus-one index mismatch. -/
theorem mismatched_model :
    Transcript.replay
      zeroControl
      request 8 [⟨1,
      unitReply⟩] = .error (.transcript (.mismatch 0 1 (by
      decide))) := rfl

/-- A unit-center response violates the retained zero center bound. -/
theorem invalid_center :
    Transcript.replay
      zeroControl
      request 8 [⟨0,
      unitReply⟩] =
      .error (.invalid (.source (.center 0 unitReply.sample 0 (by
        decide)))) := rfl

/-- A response with allowance one violates the retained zero allowance bound. -/
theorem invalid_allowance :
    Transcript.replay
      zeroControl
      request 8 [⟨0,
      allowanceReply⟩] =
      .error (.invalid (.source (.allowance 0
        allowanceReply.allowance 0 (by decide)))) := rfl

/-- A zero-target integration request returns its nonpositive-target certificate. -/
theorem nonpositive_request :
  Request.checked 0 0 = .error ⟨0, 0, by decide⟩ := rfl

/-- A negative-target integration request returns its nonpositive-target certificate. -/
theorem negative_request :
  Request.checked 7 (-1) = .error ⟨7, -1, by decide⟩ := by decide +kernel

/-- A target-one integration request is accepted with its retained start index. -/
theorem positive_request :
  Request.checked 7 1 = .ok ⟨7, 1, by decide⟩ := by decide +kernel

end Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.WorkedExamples

end
