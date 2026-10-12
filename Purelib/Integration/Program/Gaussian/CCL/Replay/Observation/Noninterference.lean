module
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record

import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Computation.Query.Basic
public import Purelib.Computation.Query.Boundary
import Purelib.Integration.CertifiedProgram
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Contract
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Computation.Query.Computation
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Integration.Program.Gaussian.Cached.Basic

section
@[expose] public section

/-!
# Public finite integration observation contract

`Contract` bundles the actual recorded runner's replay, accuracy, complete
prefix and source-ownership laws.  It does not replace the executable
`IntegrationReplay.record` or duplicate its retained data.  The separate
payload-erasure theorem follows from the adaptive query boundary: outside
the generated finite trace the source may depend arbitrarily on a payload.
`resumed_contract` gives the same guarantees after continuing a saved receipt;
the complete observation and joined trace equal an uninterrupted run.

Assumption ledger:
* `Request` supplies a displayed source index and a checked positive rational
  squared-error target; `count` is the requested finite bit count.
* This generic theorem inherits the cached program's finite coherence and
  bound certificates.  Generated clients must derive those certificates.
* Replay itself receives only finite control data, request/count and the
  recorded finite replies.  Neither the source procedure nor the payload is
  an argument to replay.
* Payload erasure supplies no equality, decidability, analytic interpretation
  or comparison assumption on the payload.  It permits arbitrary changes
  outside the trace, not changes to the replies actually consumed.
* The boundary is a cached path-model query.  No claim is made to expose
  uninstrumented root isolation or integrand evaluations inside that query.
-/

namespace Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Noninterference

open Purelib.Integration.CertifiedProgram (Request InvalidRequest)

open Purelib.CCL.Progressive.IntegrationReplay

universe u

open Purelib.Computation.Query
open Purelib.Integration.Program.Gaussian.CCL.Replay
/-- The original computation execution equals its exact retained successful observation and transcript. -/
theorem recorded_execution (program :
  CachedProgram) (request : Request) (count : Nat) :
    (Observation.Basic.computation (control program) request count).run program.stage =
      ⟨.ok (Observation.Record.record program request count).observation, (Observation.Record.record program request
        count).trace⟩ := by
  change Basic.Execution.mk
    ((Observation.Basic.computation (control program) request count).run program.stage).value
    ((Observation.Basic.computation (control program) request count).run program.stage).trace = _
  rw [(Observation.Record.record program request count).value_eq, (Observation.Record.record program request
    count).trace_eq]

/-- Changing arbitrary payload-dependent oracle replies outside the recorded trace preserves the exact observation
execution.

The trace overlay retains every queried original reply, so both the successful value and ordered transcript remain
unchanged. -/
theorem payload_erasure {Payload :
  Type u} (program : CachedProgram) (request : Request) (count : Nat)
    (payload : Payload) (outside : Payload → Nat → CachedModel) :
    (Observation.Basic.computation (control program) request count).run
        (Boundary.Trace.overlay (Observation.Record.record program request count).trace (outside payload)) =
      ⟨.ok (Observation.Record.record program request count).observation, (Observation.Record.record program request
        count).trace⟩ := by
  have unchanged := Computation.Query.Protocol.annotation_erasure (Observation.Basic.computation (control program)
    request
    count) program.stage payload outside
  rw [← (Observation.Record.record program request count).trace_eq] at unchanged
  exact unchanged.trans (recorded_execution program request count)

/-- Outside-trace payload changes preserve the exact recorded execution together with its original certified observation
contract. -/
theorem payload_erasure_contract
  {Payload : Type u} (program : CachedProgram) (request : Request) (count : Nat)
    (payload : Payload) (outside : Payload → Nat → CachedModel) :
    (Observation.Basic.computation (control program) request count).run
        (Boundary.Trace.overlay (Observation.Record.record program request count).trace (outside payload)) =
      ⟨.ok (Observation.Record.record program request count).observation, (Observation.Record.record program request
        count).trace⟩ ∧
      Integration.Program.Gaussian.CCL.Replay.Observation.Contract program request count (Observation.Record.record
        program request count) :=
  ⟨payload_erasure program request count payload outside,
    Observation.Contract.observation_contract program request count⟩

end Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Noninterference

end
