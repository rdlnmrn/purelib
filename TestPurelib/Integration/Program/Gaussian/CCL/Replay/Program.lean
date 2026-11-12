module
import Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Cache.WorkedExamples
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Examples.Integration.Program.Gaussian.Cached.Policy.WorkedExamples
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.Cached.Policy
import Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.WorkedExamples
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
import Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.MachineProjection
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Representation
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Computation.Query.Replay
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

/-! Regression checks for the retained integration program gaussian ccl replay program contracts. -/

namespace TestPurelib.Integration.Program.Gaussian.CCL.Replay.Program

open Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.WorkedExamples

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

end TestPurelib.Integration.Program.Gaussian.CCL.Replay.Program

namespace TestPurelib.Integration.Program.Gaussian.CCL.Replay.Program.Cache

open Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Cache.WorkedExamples

open Purelib.Examples.Integration.Program.Gaussian.Cached
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.CCL
open Purelib.Examples
open Purelib.Integration

/-- The cached program emits the displayed ten-bit word. -/
theorem actual_word :
    observed.observation.word = [true, false, true, true,
      true, true, false, false, true, true] := by
  decide +kernel

end TestPurelib.Integration.Program.Gaussian.CCL.Replay.Program.Cache
