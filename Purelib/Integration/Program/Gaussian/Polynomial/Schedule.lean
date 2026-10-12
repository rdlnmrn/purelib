module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
public import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Integration.Polynomial.Gaussian.Partition.Source
public import Purelib.Integration.Program.Gaussian.Cached.Schedule
import Purelib.Integration.CCL.Program
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Integration.CertifiedProgram
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic

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

namespace Purelib.Integration.Program.Gaussian.Polynomial.Schedule

open Purelib.Approximation.Gaussian in
open Purelib.CCL.Progressive in
open Purelib.Data.Nat in
open Purelib.Integration.Polynomial.Gaussian.Partition in
open Purelib.Integration.Program in
/-- Two partition policies and positive-stride schedules for one original polynomial path have equivalent outputs.

Both retained scheduled programs read the exact original source sample at every stage, while their separate policies and
schedules remain unchanged. -/
def polynomial_scheduled_outputs_equivalent
    (source : Source.PolynomialPath)
    (left right : IntegrationPrograms.PartitionPolicy source)
    (leftSchedule rightSchedule : Data.Nat.Schedule.PositiveStride) :
    Equivalence.NamedEquivalent
      (Gaussian.Cached.Schedule.reindexCached (IntegrationPrograms.polynomialProgram source left)
        leftSchedule).output.name
      (Gaussian.Cached.Schedule.reindexCached (IntegrationPrograms.polynomialProgram source right)
        rightSchedule).output.name := by
  apply Equivalence.Equivalent.toNamed
  apply Equivalence.Equivalent.of_constant_samples _ _
    (Source.sourceSample source)
  · intro index
    rw [Gaussian.Cached.Schedule.reindexCached_sample, IntegrationPrograms.polynomialProgram_sample]
  · intro index
    rw [Gaussian.Cached.Schedule.reindexCached_sample, IntegrationPrograms.polynomialProgram_sample]

end Purelib.Integration.Program.Gaussian.Polynomial.Schedule

end
