module
public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Schedule
import Purelib.Data.Nat.Schedule.PositiveStride
public import Purelib.Integration.CCL.Program
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Approximation.Gaussian.Name.Coherent
import Mathlib.Order.Basic

open Purelib.Data.Nat.Schedule (PositiveStride)

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

section
@[expose] public section

/-!
# Generated positive-stride integration schedules

A schedule is two natural numbers, with index `offset + (extraStride + 1)*n`.
Monotonicity, progress and the least local index reaching a requested source
index are proved internally.  Synchronization reuses the original
approximation's finite quarter-target comparison and covers every pair of
later indices, not just the two displayed synchronization indices.

The generic adapters inherit the original program's supplied coherence and
bounds.  The polynomial specialization derives those original fields from
finite coefficients and cuts; its caller supplies no comparison evidence.
-/

namespace Purelib.Integration.Program.Gaussian.Cached.Schedule

open Purelib.Approximation.Rational in
open Purelib.Data.Nat in
open Purelib.Integration.Program.Gaussian.Cached in
/-- Retain the exact cached program stages selected by the original positive-stride schedule.

The original error scale and center bound remain fixed; monotonicity and the schedule's index floor preserve the
geometric guarantees. -/
def reindexCached (program : Basic.CachedProgram) (schedule
  : PositiveStride) : Basic.CachedProgram where
  stage index := program.stage (schedule.index index)
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := fun stage =>
    (program.modelAllowance_le (schedule.index stage)).trans
      (quarterRadius_antitone program.errorScale_nonneg (schedule.index_ge stage))
  later_close := fun order =>
    (program.later_close (schedule.monotone order)).trans
      (quarterRadius_antitone program.errorScale_nonneg (schedule.index_ge _))
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := fun stage => program.sample_bounded (schedule.index stage)

open Purelib.Data.Nat in
open Purelib.Integration.Program.Gaussian.Cached in
/-- A reindexed sample is the exact original sample at the retained scheduled index. -/
theorem reindexCached_sample (program : Basic.CachedProgram)
  (schedule : PositiveStride) (index : Nat) :
    (reindexCached program schedule).approximation.sample index =
      program.approximation.sample (schedule.index index) := rfl

open Purelib.Approximation.Gaussian
open Purelib.Data.Nat
open Purelib.Integration.Program.Gaussian.Cached
/-- Two original positive-stride schedules give equivalent approximations of the same retained cached program. -/
def reindexed_cached_equivalent (program :
  Basic.CachedProgram) (left right : PositiveStride) :
    Equivalence.Equivalent
      (reindexCached program left).approximation (reindexCached program right).approximation :=
  Sequence.Schedule.equivalentOfScheduledSamples program.approximation _ _ left right
    (reindexCached_sample program left) (reindexCached_sample program right)

/-- Two retained schedules give equivalent output names for the same original cached program. -/
def reindexed_cached_outputs_equivalent (program :
  Basic.CachedProgram) (left right : PositiveStride) :
    Equivalence.NamedEquivalent
      (reindexCached program left).output.name (reindexCached program right).output.name :=
  (reindexed_cached_equivalent program left right).toNamed
end Purelib.Integration.Program.Gaussian.Cached.Schedule

end
