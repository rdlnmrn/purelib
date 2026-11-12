module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.CCL.Transducer.Replay.Check
import Purelib.Data.CCL.Transducer.Replay.Emission.Step
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
import Purelib.Data.CCL.Transducer.Replay.Machine.Consume
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Machine

import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Basic
public import Purelib.Examples.Integration.Program.Gaussian.Cached.Constant.WorkedExamples
public import Purelib.Integration.Program.Gaussian.CCL.Replay.MachineProjection
import Mathlib.Algebra.Ring.Defs
import Purelib.Approximation.Gaussian.Enclosure.Ball.Data
import Purelib.Approximation.Gaussian.Process.Recipe.Basic
import Purelib.Approximation.Gaussian.Process.Recipe.Cursor
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Computation.Query.Computation
import Purelib.Computation.Query.Replay
import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.CCL.Transducer.Replay.Emission
import Purelib.Data.CCL.Transducer.Replay.Mode
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

@[expose] public section

/-!
Replay controllers for exact constant integration programs.

Finite runs retain ordered source exchanges and project to the original
productive transducer. Their recorded exchanges replay to the complete
original result.
-/

namespace Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Controller.WorkedExamples

open Purelib.Examples.Integration.Program.Gaussian.Cached
open Purelib.Integration.Program.Gaussian.CCL
open Purelib.Data.CCL
open Purelib.Data.CCL.Transducer

open Purelib.CCL
open Purelib
open Purelib.Data
open Purelib.Examples
open Purelib.Integration

/-- Run the replay controller for a constant Gaussian integration program.

The finite run retains its ordered source exchanges and the resulting machine state or checked failure. -/
def run (value :
  Gaussian.Basic.Canonical) (count : Nat) :=
  (Replay.Machine.advance (Progressive.IntegrationReplay.control
    (Constant.WorkedExamples.program value))
    (Replay.Machine.initial 0) count).run
    (Constant.WorkedExamples.program value).stage

/-- The emitted word or retained failure of the finite controller run. -/
def word (value :
  Gaussian.Basic.Canonical) (count : Nat) : Except Replay.Failure (List Bool) :=
  (run value count).value.map
    Replay.Machine.emitted

/-- Every generated controller run projects to the original productive transducer state. -/
theorem generated_projects
  (value : Gaussian.Basic.Canonical) (count : Nat) :
    ∃ result, (run value count).value = .ok result ∧
      Replay.MachineProjection.MachineRep
        (Constant.WorkedExamples.program value)
        (Machine.Advance.advance
          (Machine.initial
            (Constant.WorkedExamples.program value).approximation.toProcess (0 :
            Nat)) count) result :=
  Replay.MachineProjection.initial_advance_rep
    (Constant.WorkedExamples.program value) 0 count

/-- Replaying the generated ordered trace reproduces the complete finite run result. -/
theorem generated_replays
  (value : Gaussian.Basic.Canonical) (count : Nat) :
    (Replay.Machine.advance (Progressive.IntegrationReplay.control
      (Constant.WorkedExamples.program value))
      (Replay.Machine.initial 0) count).replayExact
      (run value count).trace = .ok
        (run value count).value :=
  Replay.Machine.advance_replay _ _ _ _

end Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Controller.WorkedExamples

end
