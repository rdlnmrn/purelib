module
import Purelib.Data.Nat.Schedule.PositiveStride
public import Purelib.Integration.Exponential.Equivalence.Policy
import Purelib.Integration.Exponential.Program
import Purelib.Integration.Exponential.Geometry.Policy

import Purelib.Integration.CertifiedProgram
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Contract

open Purelib.Integration

/-!
# Finite exponential integration observations

Two finite partition policies and positive-stride schedules select their own
retained integration programs on `[0,1]`. A common numerical request and bit
count index their observation comparison. The certificate retains both
observations, their exact replay and cursor semantics, and operational
equivalence of the original outputs.
-/

namespace Purelib.Integration.Exponential.CCL.Observation

open Purelib.Data.Nat
open Purelib.Integration.Exponential
open Purelib.Integration.Exponential.Equivalence
open Purelib.Integration.Polynomial
open Purelib.Integration.Program.Gaussian.CCL
/-- Retain comparable finite CCL observations of two original exponential integration programs.

The two partition policies, schedules and extra observation depths remain separate; the shared numerical request and bit
count index the exact retained output comparison. -/
@[expose] public def exponential_contract (left right :
  Exponential.Geometry.Policy)
    (leftSchedule rightSchedule : Data.Nat.Schedule.PositiveStride) (leftExtra rightExtra : Nat)
    (request : CertifiedProgram.Request) (count : Nat) :
    Replay.Observation.Contract.Comparison
      (Program.program left leftSchedule leftExtra)
      (Program.program right rightSchedule rightExtra) request count :=
  Replay.Observation.Contract.comparison _ _ request count
    (Policy.outputs_equivalent
      left right leftSchedule rightSchedule leftExtra rightExtra)

end Purelib.Integration.Exponential.CCL.Observation
