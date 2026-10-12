module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Exponential.Taylor.Integral.Bounds
import Purelib.Data.CCL.Transducer.Initial.Observation
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Exponential.Program
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay

import Purelib.CCL.Progressive.IntegrationQueries
public import Purelib.Examples.Integration.Exponential.Program.WorkedExamples
import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CCL.Program
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

@[expose] public section

/-!
# Automatically deepened exponential integration regressions

The coefficient tables are generated and integrated by the shared partition
kernel.  These examples exercise the degree selector and the actual CCL
output/replay path, not a constant cell containing the expected answer.
-/

namespace Purelib.Examples.Integration.Exponential.CCL.Replay.WorkedExamples

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Examples.Integration.Exponential
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.CCL
open Purelib
open Purelib.Examples
open Purelib.Integration

/-- The finite exponential integration request starting at zero with positive target one. -/
def request : CertifiedProgram.Request := ⟨0,
  1, by decide⟩
/-- The recorded first-bit observation of the retained exponential program. -/
def recorded :=
  Record.record Program.WorkedExamples.fixedProgram
  request 1

/-- The recorded first-bit trace replays to exactly its retained observation. -/
theorem initial_replay :
    Transcript.replay (Progressive.IntegrationReplay.control
      Program.WorkedExamples.fixedProgram)
      request 1
      recorded.trace =
      .ok recorded.observation :=
  Transcript.observation_replay
    Program.WorkedExamples.fixedProgram
    request 1

/-- The first recorded observation emits one bit. -/
theorem actual_nonempty_prefix :
  recorded.observation.word.length = 1 := by
  unfold recorded
  exact Record.recorded_length
    Program.WorkedExamples.fixedProgram
    request 1

/-- The exponential observation's first bit is true.

The retained sample's norm lower bound determines the initial transducer decision. -/
theorem actual_first_bit :
  recorded.observation.word = [true] := open Purelib.Approximation in
  open Purelib.Data in open Purelib.Data.Rat in by
  rw [recorded,
    Record.recorded_prefix]
  apply Data.CCL.Transducer.Initial.Observation.advance_one_large
  change (13 / 6 : Rational) < Data.Gaussian.Norm.Basic.normSq
    (Program.WorkedExamples.fixedProgram.approximation.sample _)
  rw [Program.WorkedExamples.fixedProgram, Exponential.Program.program_sample]
  exact (show (13 / 6 : Rational) < 9 / 4 from by decide).trans_le
    (Gaussian.Exponential.Taylor.Integral.Bounds.integral_norm_lower _)

/-- The recorded eight-bit observation of the same exponential program and request. -/
def recordedEight :=
  Record.record Program.WorkedExamples.fixedProgram
  request 8

/-- The eight-bit trace replays to exactly its retained observation. -/
theorem eight_bit_replay :
    Transcript.replay (Progressive.IntegrationReplay.control
      Program.WorkedExamples.fixedProgram)
      request 8
      recordedEight.trace =
      .ok recordedEight.observation :=
  Transcript.observation_replay
    Program.WorkedExamples.fixedProgram
    request 8

/-- The second recorded observation emits eight bits. -/
theorem eight_bit_length :
  recordedEight.observation.word.length = 8 :=
  Record.recorded_length
    Program.WorkedExamples.fixedProgram
    request 8

/-- The eight-bit observation extends the first recorded bit. -/
theorem observed_prefix_extends :
  recorded.observation.word.IsPrefix
  recordedEight.observation.word :=
  Record.recorded_extends
    Program.WorkedExamples.fixedProgram
    request 1 7

/-- Advancing the productive exponential output machine emits the requested number of bits. -/
theorem arbitrary_output_length (count : Nat)
  :
    (Data.CCL.Transducer.Machine.Advance.advance
      Program.WorkedExamples.fixedProgram.output.name.machine count).emitted.length = count :=
  (Program.WorkedExamples.fixedProgram.output.name.productive count).2

end Purelib.Examples.Integration.Exponential.CCL.Replay.WorkedExamples

end
