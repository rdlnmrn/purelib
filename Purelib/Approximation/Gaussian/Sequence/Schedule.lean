module
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Sequence
public import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Data.Nat.Schedule

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

namespace Purelib.Approximation.Gaussian.Sequence.Schedule

/-- Structural sample identities permit different cached implementations of the same scheduled source. This generic
helper is conditional; the generated adapters below discharge both identities by construction. -/
def equivalentOfScheduledSamples (source left right :
  Gaussian.Sequence.ApproximationData)
    (leftSchedule rightSchedule : Data.Nat.Schedule.PositiveStride)
    (leftSample : ∀ index, left.sample index = source.sample (leftSchedule.index index))
    (rightSample : ∀ index, right.sample index = source.sample (rightSchedule.index index)) :
    Gaussian.Equivalence.Equivalent left right where
  compare := by
    intro leftStart rightStart target positive
    let sourceComparison := (Equivalent.refl source).compare
      (leftSchedule.index leftStart) (rightSchedule.index rightStart) target positive
    let leftIndex := leftSchedule.seek leftStart sourceComparison.leftIndex
    let rightIndex := rightSchedule.seek rightStart sourceComparison.rightIndex
    exact
      { leftIndex := leftIndex
        rightIndex := rightIndex
        left_ge := leftSchedule.seek_ge leftStart sourceComparison.leftIndex
        right_ge := rightSchedule.seek_ge rightStart sourceComparison.rightIndex
        close := by
          intro leftLater rightLater leftOrder rightOrder
          rw [leftSample, rightSample]
          exact sourceComparison.close
            ((leftSchedule.seek_reaches leftStart sourceComparison.leftIndex).trans
              (leftSchedule.monotone leftOrder))
            ((rightSchedule.seek_reaches rightStart sourceComparison.rightIndex).trans
              (rightSchedule.monotone rightOrder)) }
end Purelib.Approximation.Gaussian.Sequence.Schedule

end
