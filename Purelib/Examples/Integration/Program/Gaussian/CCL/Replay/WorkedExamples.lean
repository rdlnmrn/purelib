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
Recorded CCL observations of a complex polynomial path integral.

The repeated curved path is evaluated under an alternating partition policy.
One-bit and eight-bit observations retain their replay, accuracy and cursor
certificates.
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

end Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.WorkedExamples

end
