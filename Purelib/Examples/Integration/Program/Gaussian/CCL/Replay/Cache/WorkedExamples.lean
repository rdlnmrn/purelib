module
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay

import Purelib.CCL.Progressive.IntegrationQueries
public import Purelib.Examples.Integration.Program.Gaussian.Cached.Policy.WorkedExamples
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.Cached.Policy

@[expose] public section

/-! # Finite allocation, retained-thunk and complete observation regressions -/

namespace Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Cache.WorkedExamples

open Purelib.Examples.Integration.Program.Gaussian.Cached
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.CCL
open Purelib.Examples
open Purelib.Integration

/-- The zero-start integration request with positive target one. -/
def request :
  CertifiedProgram.Request := ⟨0, 1, by decide⟩

/-- The ten-bit observation recorded from the retained right-hand cached program. -/
def observed :=
  Program.Gaussian.CCL.Replay.Observation.Record.record
  (Policy.WorkedExamples.right.program
  Policy.WorkedExamples.source)
  request 10

/-- Replaying the complete recorded cache trace returns its original ten-bit observation. -/
theorem replay :
    Transcript.replay (Progressive.IntegrationReplay.control
      (Policy.WorkedExamples.right.program
      Policy.WorkedExamples.source))
      request 10
      observed.trace =
      .ok observed.observation :=
  Transcript.observation_replay _ _ _

/-- The cached program emits the displayed ten-bit word. -/
theorem actual_word :
    observed.observation.word = [true, false, true, true,
      true, true, false, false, true, true] := by
  decide +kernel

end Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Cache.WorkedExamples

end
