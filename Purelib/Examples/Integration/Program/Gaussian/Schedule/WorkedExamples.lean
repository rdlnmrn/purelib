module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Nat.Schedule.PositiveStride
public import Purelib.Examples.Integration.Polynomial.Gaussian.Partition.WorkedExamples
import Purelib.Integration.Program.Gaussian.Cached.Schedule
public import Purelib.Integration.Program.Gaussian.Polynomial.Schedule

import Purelib.CCL.Progressive.IntegrationPrograms
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.CCL.Program
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

@[expose] public section

/-!
# Positive-stride integration regressions

Ceiling-division tests cover offsets, exact and inexact hits, large strides,
and an already advanced cursor.  The comparison test deliberately quantifies
over two independently advanced tails, not only a selected pair of samples.
-/

namespace Purelib.Examples.Integration.Program.Gaussian.Schedule.WorkedExamples

open Purelib.Data.Nat.Schedule (PositiveStride)
open Purelib.Examples.Integration.Polynomial.Gaussian
open Purelib.Integration.Program.Gaussian.Cached

open Purelib.Approximation
open Purelib.Data
open Purelib
open Purelib.Data.Rat
open Purelib.Examples
open Purelib.Integration
open Purelib.CCL.Progressive.IntegrationPrograms (polynomialProgram)

/-- The unit-stride schedule beginning at source index zero. -/
def slow :
  PositiveStride := ⟨0, 0⟩
/-- The stride-five schedule beginning at source index three. -/
def fast :
  PositiveStride := ⟨3, 4⟩

/-- The first three source indices of the stride-five schedule are 3, 8 and 13. -/
theorem positive_stride_indices :
    [fast.index 0,
      fast.index 1,
      fast.index 2] = [3, 8, 13] := by decide

/-- Seeking below the schedule offset retains local index zero. -/
theorem seek_before_offset :
  fast.seek 0 2 = 0 := by decide
/-- Seeking an exact source hit returns its corresponding local index. -/
theorem seek_exact_hit :
  fast.seek 0 13 = 2 := by decide
/-- Seeking between source hits advances to the next local index. -/
theorem seek_between_hits :
  fast.seek 0 14 = 3 := by decide
/-- Seeking preserves an already advanced local cursor. -/
theorem seek_preserves_cursor :
  fast.seek 7 14 = 7 := by decide
/-- A stride-one-thousand schedule reaches source threshold 1001 at local index two. -/
theorem seek_large_stride :
  (PositiveStride.mk 0 999).seek 0 1001 = 2 := by decide

/-- The computed seek is no greater than any candidate meeting both cursor and source thresholds. -/
theorem computed_seek_is_least (schedule :
  PositiveStride) (current required candidate : Nat)
    (cursorOrder : current ≤ candidate) (sourceOrder : required ≤ schedule.index candidate) :
    schedule.seek current required ≤ candidate :=
  (schedule.seek_le_iff current required candidate).mpr ⟨cursorOrder, sourceOrder⟩

/-- The retained fixed-policy polynomial program reindexed by the unit-stride schedule. -/
def fixed :=
  Schedule.reindexCached (polynomialProgram
  Partition.WorkedExamples.repeatedPath (.fixed
  Partition.WorkedExamples.repeatedRequest))
  slow
/-- The retained alternating-policy polynomial program reindexed by the stride-five schedule. -/
def alternating :=
  Schedule.reindexCached (polynomialProgram
  Partition.WorkedExamples.repeatedPath
  Partition.WorkedExamples.alternatingPolicy)
  fast

/-- Reindexing retains the original complete cached stage at the selected source index. -/
theorem cached_stage_retained (index : Nat)
  :
    alternating.stage index =
      (polynomialProgram Partition.WorkedExamples.repeatedPath
        Partition.WorkedExamples.alternatingPolicy).stage
        (fast.index index) := rfl

/-- The fixed and alternating polynomial policies produce equivalent names under their respective schedules. -/
def
  generated_policy_and_schedule_equivalence
  : Gaussian.Equivalence.NamedEquivalent
    fixed.output.name
      alternating.output.name :=
  Program.Gaussian.Polynomial.Schedule.polynomial_scheduled_outputs_equivalent
    Partition.WorkedExamples.repeatedPath _ _
    slow fast

/-- Both independently advanced tails remain close after synchronization.

The retained comparison uses the original cached program bounds for every pair of later local indices. -/
theorem all_independently_later_pairs
  (program : Program.Gaussian.Cached.Basic.CachedProgram)
    (leftSchedule rightSchedule : PositiveStride) (leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    let comparison := (Schedule.reindexed_cached_equivalent program leftSchedule
      rightSchedule).compare
      leftStart rightStart target positive
    ∀ leftLater rightLater,
      comparison.leftIndex ≤ leftLater → comparison.rightIndex ≤ rightLater →
      Data.Gaussian.Norm.Basic.normSq
        ((Schedule.reindexCached program leftSchedule).approximation.sample leftLater -
          (Schedule.reindexCached program rightSchedule).approximation.sample rightLater) <
            target := by
  intro comparison leftLater rightLater leftOrder rightOrder
  exact comparison.close leftOrder rightOrder

end Purelib.Examples.Integration.Program.Gaussian.Schedule.WorkedExamples

end
