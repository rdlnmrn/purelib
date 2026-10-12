module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Sequence.Schedule
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Integration.Program.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Approximation
public import Purelib.Integration.Program.Gaussian.Name
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

open Purelib.Data.Nat.Schedule (PositiveStride)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)

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

namespace Purelib.Integration.Program.Gaussian.Schedule

open Purelib.Approximation.Rational in
open Purelib.Data.Nat in
open Purelib.Integration.Program in
/-- Reindex the original program through the retained positive-stride schedule.

The original models are selected at the schedule's exact indices, and its monotonicity and index lower bounds transport
the original geometric guarantees. -/
def reindexProgram (program : RefinementProgram)
  (schedule : PositiveStride) : RefinementProgram where
  model stage := program.model (schedule.index stage)
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
open Purelib.Integration.Program in
/-- A scheduled sample reads the original program sample at that exact retained schedule index. -/
theorem reindexProgram_sample (program :
  RefinementProgram) (schedule : PositiveStride) (index : Nat) :
    (reindexProgram program schedule).approximation.sample index =
      program.approximation.sample (schedule.index index) := rfl

open Purelib.Approximation.Gaussian
open Purelib.Data.Nat
open Purelib.Integration.Program
/-- Two retained positive-stride schedules of the original program yield equivalent approximation sequences. -/
def reindexed_programs_equivalent (program :
  RefinementProgram) (left right : PositiveStride) :
    Equivalence.Equivalent
      (reindexProgram program left).approximation (reindexProgram program
        right).approximation :=
  Sequence.Schedule.equivalentOfScheduledSamples program.approximation _ _ left right
    (reindexProgram_sample program left) (reindexProgram_sample program right)

/-- Two retained schedules of the original program yield equivalent coherent output names. -/
def reindexed_outputs_equivalent (program :
  RefinementProgram) (left right : PositiveStride) :
    Equivalence.NamedEquivalent
      (reindexProgram program left).output.name (reindexProgram program
        right).output.name :=
  (reindexed_programs_equivalent program left right).toNamed
end Purelib.Integration.Program.Gaussian.Schedule

end
