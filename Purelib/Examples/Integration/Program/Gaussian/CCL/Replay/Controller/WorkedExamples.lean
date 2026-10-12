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
# Multi-step replay regressions

These are actual exact polynomial integration programs.  Zero exercises the
initial-low chart, one exercises residual padding, and three halves reaches
the silent residual inverse chart and its second model query.  Literal
arithmetic is checked by the kernel at ordinary elaboration limits.
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
    (Transducer.Replay.Machine.initial 0) count).run
    (Constant.WorkedExamples.program value).stage

/-- The emitted word or retained failure of the finite controller run. -/
def word (value :
  Gaussian.Basic.Canonical) (count : Nat) : Except Transducer.Replay.Failure (List Bool) :=
  (run value count).value.map
    Transducer.Replay.Machine.emitted

/-- Eight steps on zero emit false followed by seven true bits. -/
theorem zero_word :
  word 0 8 = .ok (false :: List.replicate 7 true) :=
  by decide +kernel

/-- The zero run retains seven source queries at index zero. -/
theorem zero_queries :
  (run 0 8).trace.map
  Computation.Query.Basic.Exchange.query = List.replicate 7 0 := by decide +kernel

/-- Ten steps on one emit the displayed initial bits, sector code and padding. -/
theorem one_word :
    word 1 10 = .ok ([false, false] ++
      (Data.ComplexContinuedFraction.Encoding.Sector.select 1).code ++ List.replicate 5 true) := by
  decide +kernel

/-- The one run retains six source queries at index zero. -/
theorem one_queries :
  (run 1 10).trace.map
  Computation.Query.Basic.Exchange.query = List.replicate 6 0 := by decide +kernel

/-- Ten steps on three halves emit the displayed inverse-chart word. -/
theorem inverse_word :
    word ⟨3 / 2, 0⟩ 10 = .ok [true, false, true, true,
      true, true, false, false, true, true] := by decide +kernel

/-- The six-step inverse-chart run retains four ordered queries at index zero, including repeated requests within one
productive chunk. -/
theorem inverse_queries :
    (run ⟨3 / 2, 0⟩ 6).trace.map
      Computation.Query.Basic.Exchange.query = [0, 0, 0, 0] := by decide +kernel

/-- Every generated controller run projects to the original productive transducer state. -/
theorem generated_projects
  (value : Gaussian.Basic.Canonical) (count : Nat) :
    ∃ result, (run value count).value = .ok result ∧
      Program.Gaussian.CCL.Replay.MachineProjection.MachineRep
        (Constant.WorkedExamples.program value)
        (Machine.Advance.advance
          (Machine.initial
            (Constant.WorkedExamples.program value).approximation.toProcess (0 :
            Nat)) count) result :=
  Program.Gaussian.CCL.Replay.MachineProjection.initial_advance_rep
    (Constant.WorkedExamples.program value) 0 count

/-- Replaying the generated ordered trace reproduces the complete finite run result. -/
theorem generated_replays
  (value : Gaussian.Basic.Canonical) (count : Nat) :
    (Replay.Machine.advance (Progressive.IntegrationReplay.control
      (Constant.WorkedExamples.program value))
      (Transducer.Replay.Machine.initial 0) count).replayExact
      (run value count).trace = .ok
        (run value count).value :=
  Replay.Machine.advance_replay _ _ _ _

/-- An empty trace is rejected when the controller requests source index zero. -/
theorem missing :
    (Replay.Machine.advance (Progressive.IntegrationReplay.control
      (Constant.WorkedExamples.program 1))
      (Transducer.Replay.Machine.initial 0) 10).replayExact [] =
      .error (.missing 0) := by decide +kernel

/-- A reply tagged with index one is rejected when index zero is requested. -/
theorem mismatch :
    (Replay.Machine.advance (Progressive.IntegrationReplay.control
      (Constant.WorkedExamples.program 1))
      (Transducer.Replay.Machine.initial 0) 10).replayExact
      [⟨1, (Constant.WorkedExamples.program 1).stage 0⟩] = .error (.mismatch 0 1 (by
        decide)) := by decide +kernel

/-- An unused source reply is rejected after a zero-step run. -/
theorem trailing :
    (Replay.Machine.advance (Progressive.IntegrationReplay.control
      (Constant.WorkedExamples.program 1))
      (Transducer.Replay.Machine.initial 0) 0).replayExact
      [⟨0, (Constant.WorkedExamples.program 1).stage 0⟩] = .error (.trailing 0) :=
        by decide +kernel

/-- A reply inconsistent with the retained source center produces the checked source failure. -/
theorem invalid_source_reply :
    (Replay.Machine.advance (Progressive.IntegrationReplay.control
      (Constant.WorkedExamples.program 0))
      (Transducer.Replay.Machine.initial 0) 1).replayExact
      [⟨0, (Constant.WorkedExamples.program 1).stage 0⟩] = .ok (.error (.source
        (.center 0 1 0 (by decide)))) := by decide +kernel

/-- A ball with negative radius is rejected with an accuracy witness. -/
theorem negative_radius :
    Transducer.Replay.Check.checkedBall 2 1 ⟨0, -1⟩ = .error (.inaccurate 2 1 ⟨0, -1⟩ (by decide)) := by
  decide +kernel

/-- A radius equal to the strict target is rejected as insufficiently accurate. -/
theorem insufficient_accuracy
  :
    Transducer.Replay.Check.checkedBall 2 1 ⟨0, 1⟩ = .error (.inaccurate 2 1 ⟨0, 1⟩ (by decide)) := by
  decide +kernel

/-- A nonpositive ball target is rejected with an accuracy witness. -/
theorem
  nonpositive_ball_target :
    Transducer.Replay.Check.checkedBall 2 0 ⟨0, 0⟩ = .error (.inaccurate 2 0 ⟨0, 0⟩ (by decide)) := by
  decide +kernel

/-- The exact zero ball is accepted for positive target one. -/
theorem valid_ball :
  Transducer.Replay.Check.checkedBall 2 1 ⟨0, 0⟩ = .ok ⟨0, 0⟩ := by decide +kernel

/-- The low chart rejects the displayed overshooting ball. -/
theorem invalid_low_chart :
    Transducer.Replay.Emission.Step.lowAfter (Progressive.IntegrationReplay.control
      (Constant.WorkedExamples.program 0)) 0 ⟨.source, 0⟩ ⟨2, 0⟩ =
      .error (.lowOvershoot ⟨.source, 0⟩ ⟨2, 0⟩ (by decide)) := by decide +kernel

/-- The loop chart rejects the displayed unnormalized zero ball. -/
theorem invalid_loop_chart :
    Transducer.Replay.Emission.Step.loopAfter (Progressive.IntegrationReplay.control
      (Constant.WorkedExamples.program 0)) .loop 0 ⟨.source, 0⟩ ⟨0, 0⟩ =
      .error (.unnormalized ⟨.source, 0⟩ ⟨0, 0⟩ (by decide)) := by decide +kernel

/-- A productive chunk with empty emission is rejected while retaining the original word and chunk. -/
theorem empty_emission :
    Transducer.Replay.Machine.Consume.consume [true] ⟨[], .initial ⟨.source, 0⟩⟩ =
      .error (.emptyEmission [true] ⟨[], .initial ⟨.source, 0⟩⟩ rfl) := rfl

/-- A nonempty chunk emits its first retained bit and keeps the remaining bit in the buffer. -/
theorem nonempty_emission :
    Transducer.Replay.Machine.Consume.consume [false] ⟨[true, false], .initial ⟨.source, 0⟩⟩ =
      .ok ⟨.initial ⟨.source, 0⟩, [false, true], [false]⟩ := rfl

end Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Controller.WorkedExamples

end
