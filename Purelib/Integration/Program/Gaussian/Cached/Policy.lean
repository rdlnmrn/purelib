module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence.Schedule
import Purelib.Data.Nat.Schedule.PositiveStride
public import Purelib.Integration.Program.Gaussian.Cached.Allocation
public import Purelib.Integration.Program.Gaussian.Cached.Schedule
public import Purelib.Integration.Program.Gaussian.Cached.Prefix.Program
import Purelib.Integration.CCL.Program
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Integration.CertifiedProgram
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Name.Coherent

section
@[expose] public section

/-!
# Generated finite allocation and extension policies for integration models

The cache owns a finite prefix of lazy, complete cached models.  Extension
retains every earlier thunk verbatim; each new thunk computes its canonical
source stage only when requested.  A read outside the allocated prefix uses
the original source procedure.  All numerical equality laws are derived from
these constructors, not supplied by a policy's caller.

This cache applies to the actual program being wrapped, including canonical
period programs whose preparation differs from the explicit Legendre fixture.
It complements prepared-state caches by retaining the integrated model's
sample and allowance as well as the model itself.
-/

namespace Purelib.Integration.Program.Gaussian.Cached

open Purelib.Data.Nat in
open Purelib.Integration.Program.Gaussian.Cached in
set_option genInjectivity false in
/-- A retained positive-stride sampling schedule and exact prefix-cache allocation request. -/
structure Policy where
  /-- The retained positive-stride source-index schedule. -/ schedule : Data.Nat.Schedule.PositiveStride
  /-- The retained initial prefix size and ordered cache extensions. -/ allocation : Allocation
deriving DecidableEq

constructive_injectivity Policy

section
open Purelib.Integration.Program.Gaussian.Cached
namespace Policy

/-- Compile the original cache allocation once and select its retained stages with the original schedule. -/
def program (policy : Policy) (source :
  Basic.CachedProgram) : Basic.CachedProgram :=
  let retained := policy.allocation.compile source
  Schedule.reindexCached retained.cache.program policy.schedule

end Policy

namespace Policy

/-- The policy stage equals the exact original source stage at its retained scheduled index. -/
theorem stage_eq (policy : Policy) (source :
  Basic.CachedProgram) (index : Nat) :
    (policy.program source).stage index = source.stage (policy.schedule.index index) :=
  (policy.allocation.compile source).cache.lookup_eq _

end Policy

namespace Policy

/-- The policy sample equals the exact original source sample at its retained scheduled index. -/
theorem sample_eq (policy : Policy) (source :
  Basic.CachedProgram) (index : Nat) :
    (policy.program source).approximation.sample index = source.approximation.sample (policy.schedule.index index) :=
  congrArg (fun model : Basic.CachedModel => model.sample) (policy.stage_eq source index)

end Policy

end

open Purelib.Approximation.Gaussian
open Purelib.Integration.Program.Gaussian.Cached
namespace Policy

/-- Two retained cache-and-schedule policies give equivalent approximations of the same original source program. -/
def policies_equivalent (source : Basic.CachedProgram) (left
  right : Policy) :
    Equivalence.Equivalent (left.program source).approximation (right.program source).approximation :=
  Sequence.Schedule.equivalentOfScheduledSamples source.approximation _ _ left.schedule right.schedule
    (left.sample_eq source) (right.sample_eq source)

end Policy

namespace Policy

/-- Two retained policies give equivalent output names for the same original source program. -/
def outputs_equivalent (source : Basic.CachedProgram) (left
  right : Policy) :
    Equivalence.NamedEquivalent (left.program source).output.name (right.program source).output.name :=
  (Policy.policies_equivalent source left right).toNamed

end Policy

end Purelib.Integration.Program.Gaussian.Cached

end
