module
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
public import Purelib.Integration.Program.Gaussian.Cached.Policy
import Purelib.Computation.Query.Basic
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Contract

public import Purelib.Riemann.Periods.PeriodReplay

@[expose] public section

/-!
# Derived cache and schedule independence of one prepared period

A policy contains only positive-stride natural data and finite cache
allocation/extension chunks.  Complete cached models are retained after the
entry's existing preparation and any prepared-state cache.  This applies to
both explicit fixtures and the actual automatically prepared standard
program; no equality between independently prepared cycles is asserted.

Every model read keeps its original source index, differential and sheet
certificates.  Numerical comparison covers all pairs of later indices;
different schedules need not emit byte-identical CCL representations or logs.
-/

namespace Purelib.Riemann.Periods.PeriodPolicies

open Purelib.Riemann.Curves.AlgebraicDifferentials

open Purelib.Riemann in
open Purelib.Curves in
/-- A retained certified period replay entry on the same admissible curve. -/
abbrev Entry {genus : Nat} (curve : Hyperelliptic.Basic.HyperellipticCurve genus) := Periods.PeriodReplay.Entry curve
section
open Purelib.Integration
/-- The certified numerical request with current state and positive target. -/
abbrev Request := CertifiedProgram.Request
/-- Executable finite cache allocation and positive-stride scheduling data. -/
abbrev Policy := Integration.Program.Gaussian.Cached.Policy

end

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}

section
open Purelib.Integration
/-- Apply the retained execution policy to the entry's existing cached program. -/
def program (entry : Entry curve) (policy : Policy) : Program.Gaussian.Cached.Basic.CachedProgram :=
  policy.program entry.cached

/-- Record a finite requested observation using the policy's scheduled cached program. -/
def record (entry : Entry curve) (policy : Policy) (request : Request) (count : Nat) :
    Program.Gaussian.CCL.Replay.Observation.Record.Recorded (program entry policy) request count :=
  Program.Gaussian.CCL.Replay.Observation.Record.record (program entry policy) request count

end

/-- Translate the policy-selected observation index to the original program's source index. -/
def sourceIndex (entry : Entry curve) (policy : Policy) (request : Request) : Nat :=
  policy.schedule.index
    (Purelib.CCL.Progressive.IntegrationReplay.selectedIndex (Purelib.CCL.Progressive.IntegrationReplay.control (program
      entry policy)) request)

open Purelib.Curves in
/-- Read the original local path certificates at the policy's selected source index. -/
def selectedCertificates (entry : Entry curve) (policy : Policy) (request : Request) :
    Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve entry.differential
      (entry.program.integral.model (sourceIndex entry policy request)).cells
      (entry.cycle.liftedPath (sourceIndex entry policy request)).path :=
  entry.program.certificates (sourceIndex entry policy request)

section
open Purelib.Integration
/-- The policy-recorded sample is the original program sample at its retained source index. -/
theorem recorded_sample (entry : Entry curve) (policy : Policy) (request : Request) (count : Nat) :
    (record entry policy request count).observation.selected.sample =
      (entry.program.integral.model (sourceIndex entry policy request)).integralSample := by
  rw [record, Program.Gaussian.CCL.Replay.Observation.Record.recorded_selected]
  change ((program entry policy).stage _).sample = _
  rw [program, policy.stage_eq]
  exact (entry.cached.stage _).sample_eq

/-- Every recorded reply is the original cached model at the scheduled source index. -/
theorem recorded_reply (entry : Entry curve) (policy : Policy) (request : Request) (count : Nat)
    (exchange : Purelib.Computation.Query.Basic.Exchange Nat Program.Gaussian.Cached.Basic.CachedModel)
    (member : exchange ∈ (record entry policy request count).trace) :
    exchange.reply = entry.cached.stage (policy.schedule.index exchange.query) :=
  (Program.Gaussian.CCL.Replay.Observation.Record.recorded_reply (program entry policy) request count exchange
    member).trans
    (policy.stage_eq entry.cached exchange.query)

end

open Purelib.Curves in
open Purelib.Integration in
/-- Recover original geometric certificates for every consumed scheduled model.

Trace membership binds the reply to the same differential, lifted cycle and source index retained by the entry. -/
def traceCertificates (entry : Entry curve) (policy : Policy) (request : Request) (count : Nat)
    (exchange : Purelib.Computation.Query.Basic.Exchange Nat Program.Gaussian.Cached.Basic.CachedModel)
    (member : exchange ∈ (record entry policy request count).trace) :
    Hyperelliptic.Integration.Algebraic.Path.Basis.UniformPathCertificates curve entry.differential
      exchange.reply.model.cells
      (entry.cycle.liftedPath (policy.schedule.index exchange.query)).path := by
  rw [recorded_reply entry policy request count exchange member]
  exact entry.program.certificates (policy.schedule.index exchange.query)

section
open Purelib.Integration
open Purelib.Approximation
/-- Two execution policies on the same retained period give equivalent finite approximations. -/
def approximations_equivalent (entry : Entry curve) (left right : Policy) :
    Gaussian.Equivalence.Equivalent
      (program entry left).approximation (program entry right).approximation :=
  Program.Gaussian.Cached.Policy.policies_equivalent entry.cached left right

/-- Two execution policies on the same retained period give operationally equivalent output names. -/
def outputs_equivalent (entry : Entry curve) (left right : Policy) :
    Gaussian.Equivalence.NamedEquivalent
      (program entry left).output.name (program entry right).output.name :=
  Program.Gaussian.Cached.Policy.outputs_equivalent entry.cached left right

end

open Purelib.Integration in
/-- The recorded policy execution satisfies the complete finite observation contract. -/
theorem observation_contract (entry : Entry curve) (policy : Policy) (request : Request) (count : Nat) :
    Integration.Program.Gaussian.CCL.Replay.Observation.Contract (program entry policy) request count (record entry
      policy
      request count) :=
  Program.Gaussian.CCL.Replay.Observation.Contract.observation_contract (program entry policy) request count

end Purelib.Riemann.Periods.PeriodPolicies
