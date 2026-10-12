module
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples
public import Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.WorkedExamples
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume

import Purelib.CCL.Progressive.IntegrationQueries
public import Purelib.Computation.Query.Boundary
public import Purelib.Examples.Integration.Exponential.CCL.Replay.WorkedExamples
import Purelib.Examples.Integration.Exponential.Program.WorkedExamples
public import Purelib.Examples.Integration.Program.Gaussian.Schedule.WorkedExamples
public import Purelib.Integration.Exponential.CCL.Observation
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Contract
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Noninterference
public import Purelib.Integration.Program.Gaussian.Polynomial.CCL.Observation
import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Computation
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Integration.Exponential.Program
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Integration.Program.Gaussian.Cached.Schedule

@[expose] public section

/-!
# Generated public contracts and noninterference regressions

The adaptive protocol genuinely changes its source outside the recorded
keys, while its complete result and repeated-query trace remain unchanged.
The same theorem is then instantiated for the real polynomial and
exponential integration controllers, including zero and nonzero bit counts.
No equality or decidability assumption on payloads is introduced.
-/

namespace Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Observation.WorkedExamples

open Purelib.Examples.Integration.Program.Gaussian.CCL
open Purelib.Examples.Integration
open Purelib.Examples.Integration.Exponential
open Purelib.Examples.Integration.Polynomial.Gaussian
open Purelib.Examples.Integration.Program.Gaussian
open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.CCL
open Purelib
open Purelib.Examples
open Purelib.Integration

universe u

/-- The complete eight-bit observation comparison between the fixed and alternating polynomial policies and schedules.
-/
def polynomialComparison :=
  Program.Gaussian.Polynomial.CCL.Observation.polynomial_contract
    Partition.WorkedExamples.repeatedPath
    (.fixed Partition.WorkedExamples.repeatedRequest)
    Partition.WorkedExamples.alternatingPolicy
    Schedule.WorkedExamples.slow Schedule.WorkedExamples.fast
    Replay.WorkedExamples.request 8

/-- The complete eight-bit observation comparison between the fixed and varying exponential policies and schedules. -/
def exponentialComparison :=
  Exponential.CCL.Observation.exponential_contract
    Program.WorkedExamples.fixedPolicy
    Program.WorkedExamples.varyingPolicy
    Program.WorkedExamples.unitStride
    Program.WorkedExamples.offsetStride 0 1
    Exponential.CCL.Replay.WorkedExamples.request 8

/-- Both polynomial presentations retain complete observation contracts without requiring a separate agreement
certificate. -/
theorem polynomial_contracts
  :
    Contract
      Schedule.WorkedExamples.fixed
      Replay.WorkedExamples.request 8
        (Record.record
          Schedule.WorkedExamples.fixed
          Replay.WorkedExamples.request 8) ∧
      Contract
        Schedule.WorkedExamples.alternating
        Replay.WorkedExamples.request 8
        (Record.record
          Schedule.WorkedExamples.alternating
          Replay.WorkedExamples.request 8) :=
  ⟨polynomialComparison.left_observation,
    polynomialComparison.right_observation⟩

/-- The original one-bit polynomial observation resumed for seven further bits. -/
def resumedPolynomial :=
  Replay.WorkedExamples.recorded.resume 7

/-- Resuming the polynomial observation yields exactly the original eight-bit receipt, including trace and machine
state. -/
theorem
  polynomial_resume_exact :
    resumedPolynomial.recorded =
      Replay.WorkedExamples.recordedEight :=
  resumedPolynomial.recorded_eq

/-- The resumed polynomial receipt satisfies its original eight-bit observation contract. -/
theorem
  polynomial_resume_contract
  :
    Contract
      Replay.WorkedExamples.polynomial
      Replay.WorkedExamples.request 8
      resumedPolynomial.recorded :=
  Program.Gaussian.CCL.Replay.Observation.Contract.resumed_contract
    resumedPolynomial

/-- The recorded resume trace replays to the exact resumed polynomial observation. -/
theorem
  polynomial_resume_replay :
    Program.Gaussian.CCL.Replay.Observation.Resume.IntegrationReplay.replayResume
        (Progressive.IntegrationReplay.control Replay.WorkedExamples.polynomial)
        Replay.WorkedExamples.recorded.observation 7
          resumedPolynomial.trace =
      .ok resumedPolynomial.observation :=
  resumedPolynomial.replay

/-- Resuming polynomial output preserves the original selected integration enclosure. -/
theorem
  polynomial_resume_same_enclosure
  :
    resumedPolynomial.observation.selected =
      Replay.WorkedExamples.recorded.observation.selected :=
  resumedPolynomial.selected_eq

/-- Both exponential presentations retain complete eight-bit observation contracts. -/
theorem exponential_contracts
  :
    Contract
      Program.WorkedExamples.fixedProgram
        Exponential.CCL.Replay.WorkedExamples.request 8
          Exponential.CCL.Replay.WorkedExamples.recordedEight ∧
      Contract
        Program.WorkedExamples.varyingProgram
        Exponential.CCL.Replay.WorkedExamples.request 8
        (Record.record
          Program.WorkedExamples.varyingProgram
          Exponential.CCL.Replay.WorkedExamples.request 8) :=
  ⟨exponentialComparison.left_observation,
    exponentialComparison.right_observation⟩

/-- Changing arbitrary payload-dependent replies outside recorded polynomial query keys preserves the complete result
and trace. -/
theorem
  polynomial_payload_erasure
  {Payload : Type u} (payload : Payload)
    (outside : Payload → Nat → Program.Gaussian.Cached.Basic.CachedModel) (count : Nat) :
    (Program.Gaussian.CCL.Replay.Observation.Basic.computation
        (Progressive.IntegrationReplay.control Replay.WorkedExamples.polynomial)
        Replay.WorkedExamples.request count).run
      (Computation.Query.Boundary.Trace.overlay
        (Record.record
          Replay.WorkedExamples.polynomial
          Replay.WorkedExamples.request count).trace (outside payload)) =
      ⟨.ok (Record.record
        Replay.WorkedExamples.polynomial
          Replay.WorkedExamples.request count).observation,
        (Record.record
          Replay.WorkedExamples.polynomial
          Replay.WorkedExamples.request count).trace⟩ :=
  Program.Gaussian.CCL.Replay.Observation.Noninterference.payload_erasure
    Replay.WorkedExamples.polynomial
    Replay.WorkedExamples.request count payload outside

/-- Changing arbitrary payload-dependent replies outside recorded exponential query keys preserves the complete result
and trace. -/
theorem
  exponential_payload_erasure
  {Payload : Type u} (payload : Payload)
    (outside : Payload → Nat → Program.Gaussian.Cached.Basic.CachedModel) (count : Nat) :
    (Program.Gaussian.CCL.Replay.Observation.Basic.computation
        (Progressive.IntegrationReplay.control Program.WorkedExamples.fixedProgram)
        Exponential.CCL.Replay.WorkedExamples.request count).run
      (Computation.Query.Boundary.Trace.overlay
        (Record.record
          Program.WorkedExamples.fixedProgram
          Exponential.CCL.Replay.WorkedExamples.request count).trace (outside payload)) =
      ⟨.ok (Record.record
        Program.WorkedExamples.fixedProgram
          Exponential.CCL.Replay.WorkedExamples.request count).observation,
        (Record.record
          Program.WorkedExamples.fixedProgram
          Exponential.CCL.Replay.WorkedExamples.request count).trace⟩ :=
  Program.Gaussian.CCL.Replay.Observation.Noninterference.payload_erasure
    Program.WorkedExamples.fixedProgram
    Exponential.CCL.Replay.WorkedExamples.request count payload outside

/-- A zero-bit polynomial observation retains the complete public contract. -/
theorem zero_bit_contract :
    Contract
      Replay.WorkedExamples.polynomial
      Replay.WorkedExamples.request 0
      (Record.record
        Replay.WorkedExamples.polynomial
        Replay.WorkedExamples.request 0) :=
  Program.Gaussian.CCL.Replay.Observation.Contract.observation_contract _ _ _

end Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Observation.WorkedExamples

end
