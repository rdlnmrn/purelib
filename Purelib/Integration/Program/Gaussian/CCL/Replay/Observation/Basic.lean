module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.CertifiedProgram
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Machine
import Purelib.Computation.Query.Computation

/-!
# Retained integration observations

The selected integration reading and advanced replay machine form one
retained successful observation. Request continuation keeps the original
query computation and explicit source or machine failure outcomes.
-/

namespace Purelib.Integration.Program.Gaussian.CCL.Replay

-- The established family namespace and its retained carrier both use
-- Observation; preserve their original public names in this owner.

open Purelib.CCL.Progressive.IntegrationReplay
open Purelib.Integration.CertifiedProgram (Request InvalidRequest)
open Purelib.Integration.Program.Gaussian.CCL.Replay
open Purelib.Computation.Query
open Purelib.Data.CCL.Transducer
open Purelib.Approximation.Gaussian

@[expose] public section

set_option genInjectivity false in
/-- The original selected integration reading together with its retained replay machine.

Both fields are the actual successful observation data, retaining the
selected reading's index and the machine's emitted and pending words. -/
structure Observation where
  /-- The original selected integration reading and its retained index. -/ selected : Reading
  /-- The exact replay machine advanced from the selected reading. -/ machine : Data.CCL.Transducer.Replay.Machine

constructive_injectivity Observation

end

namespace Observation

/-- Read the exact emitted word from the retained observation machine.

The word is read from the same retained replay machine; no machine
advance, source query or prefix reconstruction is performed. -/
@[expose] public def word (observation : Observation) : List Bool := observation.machine.emitted

end Observation

namespace Observation.Basic

/-- Start replay at the original selected reading and retain it alongside the advanced machine.

An invalid selected reply remains a source failure, and machine failures remain explicit without fabricating an
observation. -/
@[expose] public def continueObservation (control : Control) (count : Nat) :
    Except InvalidReply Reading → QueryComputation (Except Data.CCL.Transducer.Replay.Failure Observation)
  | .error error => .pure (.error (.source error))
  | .ok selected =>
      (Machine.advance control (.initial selected.index) count).map fun result =>
        result.map fun machine => ⟨selected, machine⟩

end Observation.Basic

namespace Observation.Basic

/-- Request the original integration reading and continue its retained replay machine for the requested bit count.

The original request-reading computation is bound to the same selected
reply continuation and requested finite bit count. -/
@[expose] public def computation (control : Control) (request : Request) (count : Nat) :
    QueryComputation (Except Data.CCL.Transducer.Replay.Failure Observation) :=
  (requestReading control request).bind (continueObservation control count)

end Observation.Basic

end Purelib.Integration.Program.Gaussian.CCL.Replay
