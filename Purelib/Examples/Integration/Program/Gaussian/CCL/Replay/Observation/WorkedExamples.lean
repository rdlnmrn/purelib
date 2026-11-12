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

open Purelib.Examples.Integration.Exponential.CCL.Replay.WorkedExamples

@[expose] public section

/-!
Observation contracts for polynomial and exponential integration.

The worked programs compare policies and schedules, resume a polynomial
observation and preserve complete results under changes to unqueried replies.
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
    WorkedExamples.request 8

/-- The complete eight-bit observation comparison between the fixed and varying exponential policies and schedules. -/
def exponentialComparison :=
  Exponential.CCL.Observation.exponential_contract
    Program.WorkedExamples.fixedPolicy
    Program.WorkedExamples.varyingPolicy
    Program.WorkedExamples.unitStride
    Program.WorkedExamples.offsetStride 0 1
    request 8

/-- Both polynomial presentations retain complete observation contracts without requiring a separate agreement
certificate. -/
theorem polynomial_contracts
  :
    Contract
      Schedule.WorkedExamples.fixed
      WorkedExamples.request 8
        (Record.record
          Schedule.WorkedExamples.fixed
          WorkedExamples.request 8) ∧
      Contract
        Schedule.WorkedExamples.alternating
        WorkedExamples.request 8
        (Record.record
          Schedule.WorkedExamples.alternating
          WorkedExamples.request 8) :=
  ⟨polynomialComparison.left_observation,
    polynomialComparison.right_observation⟩

/-- The original one-bit polynomial observation resumed for seven further bits. -/
def resumedPolynomial :=
  WorkedExamples.recorded.resume 7

/-- The resumed polynomial receipt satisfies its original eight-bit observation contract. -/
theorem
  polynomial_resume_contract
  :
    Contract
      WorkedExamples.polynomial
      WorkedExamples.request 8
      resumedPolynomial.recorded :=
  Contract.resumed_contract
    resumedPolynomial

/-- The recorded resume trace replays to the exact resumed polynomial observation. -/
theorem
  polynomial_resume_replay :
    Resume.IntegrationReplay.replayResume
        (Progressive.IntegrationReplay.control WorkedExamples.polynomial)
        WorkedExamples.recorded.observation 7
          resumedPolynomial.trace =
      .ok resumedPolynomial.observation :=
  resumedPolynomial.replay

/-- Both exponential presentations retain complete eight-bit observation contracts. -/
theorem exponential_contracts
  :
    Contract
      Program.WorkedExamples.fixedProgram
        request 8
          recordedEight ∧
      Contract
        Program.WorkedExamples.varyingProgram
        request 8
        (Record.record
          Program.WorkedExamples.varyingProgram
          request 8) :=
  ⟨exponentialComparison.left_observation,
    exponentialComparison.right_observation⟩

/-- Changing arbitrary payload-dependent replies outside recorded polynomial query keys preserves the complete result
and trace. -/
theorem
  polynomial_payload_erasure
  {Payload : Type u} (payload : Payload)
    (outside : Payload → Nat → Program.Gaussian.Cached.Basic.CachedModel) (count : Nat) :
    (Basic.computation
        (Progressive.IntegrationReplay.control WorkedExamples.polynomial)
        WorkedExamples.request count).run
      (Computation.Query.Boundary.Trace.overlay
        (Record.record
          WorkedExamples.polynomial
          WorkedExamples.request count).trace (outside payload)) =
      ⟨.ok (Record.record
        WorkedExamples.polynomial
          WorkedExamples.request count).observation,
        (Record.record
          WorkedExamples.polynomial
          WorkedExamples.request count).trace⟩ :=
  Noninterference.payload_erasure
    WorkedExamples.polynomial
    WorkedExamples.request count payload outside

/-- Changing arbitrary payload-dependent replies outside recorded exponential query keys preserves the complete result
and trace. -/
theorem
  exponential_payload_erasure
  {Payload : Type u} (payload : Payload)
    (outside : Payload → Nat → Program.Gaussian.Cached.Basic.CachedModel) (count : Nat) :
    (Basic.computation
        (Progressive.IntegrationReplay.control Program.WorkedExamples.fixedProgram)
        request count).run
      (Computation.Query.Boundary.Trace.overlay
        (Record.record
          Program.WorkedExamples.fixedProgram
          request count).trace (outside payload)) =
      ⟨.ok (Record.record
        Program.WorkedExamples.fixedProgram
          request count).observation,
        (Record.record
          Program.WorkedExamples.fixedProgram
          request count).trace⟩ :=
  Noninterference.payload_erasure
    Program.WorkedExamples.fixedProgram
    request count payload outside

end Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Observation.WorkedExamples

end
