module
import Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Observation.WorkedExamples
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples
import Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.WorkedExamples
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume

import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Boundary
import Purelib.Examples.Integration.Exponential.CCL.Replay.WorkedExamples
import Purelib.Examples.Integration.Exponential.Program.WorkedExamples
import Purelib.Examples.Integration.Program.Gaussian.Schedule.WorkedExamples
import Purelib.Integration.Exponential.CCL.Observation
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Contract
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Noninterference
import Purelib.Integration.Program.Gaussian.Polynomial.CCL.Observation
import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Computation
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Integration.Exponential.Program
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Integration.Program.Gaussian.Cached.Schedule

/-! Regression checks for the retained integration program gaussian ccl replay observation contracts. -/

namespace TestPurelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.Observation.WorkedExamples

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

open Purelib.Examples.Integration.Program.Gaussian.CCL.Replay.WorkedExamples
  (recordedEight recorded polynomial request)

universe u

/-- Resuming the polynomial observation yields exactly the original eight-bit receipt, including trace and machine
state. -/
theorem
  polynomial_resume_exact :
    resumedPolynomial.recorded =
      recordedEight :=
  resumedPolynomial.recorded_eq

/-- Resuming polynomial output preserves the original selected integration enclosure. -/
theorem
  polynomial_resume_same_enclosure
  :
    resumedPolynomial.observation.selected =
      recorded.observation.selected :=
  resumedPolynomial.selected_eq

/-- A zero-bit polynomial observation retains the complete public contract. -/
theorem zero_bit_contract :
    Contract
      polynomial
      request 0
      (Record.record
        polynomial
        request 0) :=
  Contract.observation_contract _ _ _

end TestPurelib.Integration.Program.Gaussian.CCL.Replay.Observation
