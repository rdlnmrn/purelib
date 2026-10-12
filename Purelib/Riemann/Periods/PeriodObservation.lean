module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Resume
import Purelib.Computation.Query.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Contract
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Noninterference

public import Purelib.Computation.Query.Boundary
public import Purelib.Riemann.Periods.PeriodPolicies

@[expose] public section

/-!
# Canonical period integration: comparison and finite observation

This is the prepared-entry contract layer below the polynomial-first public
facade.  It consumes an existing certified entry and finite policies, and can
certify an already retained receipt without running its source again.
Canonical preparation, numerical bounds, cache correctness, all-later-tail
comparison, productive finite output and exact replay are generated above
this layer from polynomial coefficients and checked finite selections.

The contract retains the selected integral's actual source and every logged
model's differential, cycle, orientation and sheet certificates.  Comparison
fixes this preparation; it does not identify independently isolated branches,
different cycles/sheets or arbitrary independent period partitions.  The
explicit-entry constructor also applies to retained Legendre fixtures without
claiming that they are the automatic isolator's preparation.
Resuming a retained receipt uses `Recorded.resume` and the numerical
`IntegrationObservation.resumed_contract`; the source-sample and new-reply
certificate projections below preserve the period link as well.

The conditional boundary is explicit: an arbitrary `Entry` already carries
its period certificates, whereas the canonical constructor generates them
from the finite curve-validity input.  Replay uses only numerical control and
the finite cached-model trace, not the source or those generating procedures.
Uninstrumented work inside a model query is outside the trace's granularity.
Payload erasure fixes the consumed replies; arbitrary oracle changes at a
consumed query are not claimed to be irrelevant.
-/

namespace Purelib.Riemann.Periods.PeriodObservation

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Periods.PeriodPolicies

universe u

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

open Purelib.Curves in
open Purelib.Integration in
set_option genInjectivity false in
/-- Numerical and geometric certificates for one retained period observation.

The record links the selected source sample and every consumed reply to the fixed entry's differential and lifted cycle.
-/
structure Contract (entry : Entry curve) (policy : Policy) (request : Request) (count : Nat)
    (recorded : Program.Gaussian.CCL.Replay.Observation.Record.Recorded (program entry policy) request count) where
  /-- The numerical replay contract for this exact recorded observation. -/ numerical :
    Integration.Program.Gaussian.CCL.Replay.Observation.Contract
    (program entry policy) request count recorded
  /-- The selected sample is the retained model of the entry's actual integral source. -/ source_sample :
    recorded.observation.selected.sample =
    (entry.program.integral.model (sourceIndex entry policy request)).integralSample
  /-- Every logged model carries its differential, cycle, orientation and sheet certificates. -/ trace_certificates : ∀
    exchange ∈ recorded.trace,
    Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve entry.differential
      exchange.reply.model.cells
      (entry.cycle.liftedPath (policy.schedule.index exchange.query)).path

constructive_injectivity Contract

open Purelib.Riemann in
open Purelib.Integration in
/-- Certify a retained period receipt using its existing record equation.

The numerical contract, source-sample identity and trace certificates all concern the same prepared entry and policy. -/
def observation_contract (entry : Entry curve) (policy : Policy) (request : Request) (count : Nat)
    (recorded : Program.Gaussian.CCL.Replay.Observation.Record.Recorded (program entry policy) request count :=
      record entry policy request count) :
    Contract entry policy request count recorded := by
  rw [recorded.eq_record]
  exact ⟨Periods.PeriodPolicies.observation_contract entry policy request count,
    recorded_sample entry policy request count, traceCertificates entry policy request count⟩

open Purelib.Integration in
/-- Resuming a period receipt preserves the original selected source sample.

The saved receipt's record equation retains its connection to the prepared period, including after an earlier resume. -/
theorem resumed_sample (entry : Entry curve) (policy : Policy) (request : Request) (count extra : Nat)
    {saved : Program.Gaussian.CCL.Replay.Observation.Record.Recorded (program entry policy) request count}
    (resumed : Program.Gaussian.CCL.Replay.Observation.Resume.IntegrationReplay.Resumed saved extra) :
    resumed.observation.selected.sample =
      (entry.program.integral.model (sourceIndex entry policy request)).integralSample := by
  rw [resumed.selected_eq, saved.eq_record]
  exact recorded_sample entry policy request count

open Purelib.Curves in
open Purelib.Integration in
/-- Recover the period certificates for a newly consumed model in a resumed trace.

The retained reply equation identifies the original prepared differential and lifted cycle without evaluating a new
certificate bank. -/
def resumed_traceCertificates (entry : Entry curve) (policy : Policy) (request : Request) (count extra : Nat)
    {saved : Program.Gaussian.CCL.Replay.Observation.Record.Recorded (program entry policy) request count}
    (resumed : Program.Gaussian.CCL.Replay.Observation.Resume.IntegrationReplay.Resumed saved extra)
    (exchange : Purelib.Computation.Query.Basic.Exchange Nat Program.Gaussian.Cached.Basic.CachedModel)
    (member : exchange ∈ resumed.trace) :
    Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve entry.differential
      exchange.reply.model.cells
      (entry.cycle.liftedPath (policy.schedule.index exchange.query)).path := by
  rw [resumed.reply exchange member, program, policy.stage_eq]
  exact entry.program.certificates (policy.schedule.index exchange.query)

open Purelib.Approximation in
set_option genInjectivity false in
/-- Equivalent period outputs with separate certified observations under two policies.

Both policies use the same prepared entry; their finite observations and traces are retained independently. -/
structure Comparison (entry : Entry curve) (left right : Policy) (request : Request) (count : Nat) where
  /-- The two policy outputs represent equivalent Gaussian names. -/ outputs : Gaussian.Equivalence.NamedEquivalent
    (program entry left).output.name (program entry right).output.name
  /-- The certified finite observation under the left policy. -/ left_observation : Contract entry left request count
    (record entry left request count)
  /-- The certified finite observation under the right policy. -/ right_observation : Contract entry right request count
    (record entry right request count)

constructive_injectivity Comparison

/-- Construct output equivalence and both finite observation contracts for one entry. -/
def prepared_period_contract (entry : Entry curve) (left right : Policy) (request : Request) (count : Nat) :
    Comparison entry left right request count :=
  ⟨outputs_equivalent entry left right,
    observation_contract entry left request count, observation_contract entry right request count⟩

open Purelib.Integration in
/-- Preserve a period observation and its trace after erasing unused oracle payload.

The overlay fixes every consumed reply, so the same source ownership and numerical certificates continue to describe the
resulting observation. -/
theorem payload_erasure {Payload : Type u} (entry : Entry curve) (policy : Policy)
    (request : Request) (count : Nat) (payload : Payload)
    (outside : Payload → Nat → Program.Gaussian.Cached.Basic.CachedModel) :
    (Program.Gaussian.CCL.Replay.Observation.Basic.computation (Purelib.CCL.Progressive.IntegrationReplay.control
      (program entry policy)) request count).run
        (Purelib.Computation.Query.Boundary.Trace.overlay (record entry policy request count).trace (outside payload)) =
      ⟨.ok (record entry policy request count).observation, (record entry policy request count).trace⟩ :=
  Program.Gaussian.CCL.Replay.Observation.Noninterference.payload_erasure (program entry policy) request count payload
    outside

end Purelib.Riemann.Periods.PeriodObservation
