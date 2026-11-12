module
public import Purelib.Integration.Cell.Source.Continuous.Affine
public import Purelib.Integration.Cell.Source.Reverse
public import Purelib.Integration.Cell.Source.Comparison.Weights
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Comparing opposite orientations of the same rational source

The original forward frontier is reflected with its cached readings and
compared against an independently supplied reverse frontier. Exact affine
pullback equality identifies their rational queries; the signed endpoint
displacements then give an explicit finite orientation-reversal bound.
-/

public section

namespace Purelib.Integration.SourceFrontier.Continuous.Affine

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Integration.Partition

/-- Oppositely oriented affine source frontiers compare through their actual rational point readings.

Each answer belongs to its original frontier enclosure. The reflected
forward cells keep their exact original range, weight and cached reading;
the common refinement with the independent reverse frontier derives the
comparison without assuming an integral equality. -/
theorem reverse_answers_difference_le (source : Fraction.Rational → Fraction.Rational)
    (interval : Partition.Interval) (forward : SourceFrontier (pullback source interval))
    (backward : SourceFrontier (pullback source ⟨interval.finish, interval.start⟩))
    (forwardAnswer backwardAnswer : Fraction.Rational)
    (forwardInside : (integralBound forward.cells).Contains forwardAnswer)
    (backwardInside : (integralBound backward.cells).Contains backwardAnswer) :
    Fraction.abs (forwardAnswer - backwardAnswer) ≤
      (integralBound forward.cells).width + (integralBound backward.cells).width := by
  let reflected := SourceFrontier.Reverse.frontier forward
  have reflectedInside : (integralBound reflected.cells).Contains forwardAnswer := by
    rw [SourceFrontier.Reverse.integralBound_eq]
    exact forwardInside
  have compared := (SourceFrontier.commonReadings reflected backward).answers_difference_le_of_same
    forwardAnswer backwardAnswer reflectedInside backwardInside
    (fun point _ _ => (pullback_reversed source interval point).symm)
  rw [SourceFrontier.Reverse.integralBound_eq] at compared
  exact compared

/-- Signed answers for opposite endpoint orientations cancel up to the paid finite enclosure widths.

Both actual source frontiers and their supplied readings remain fixed. The
absolute signed discrepancy is bounded by the absolute endpoint displacement
times the sum of their two original rational enclosure widths. -/
theorem oriented_answers_sum_le (source : Fraction.Rational → Fraction.Rational)
    (interval : Partition.Interval) (forward : SourceFrontier (pullback source interval))
    (backward : SourceFrontier (pullback source ⟨interval.finish, interval.start⟩))
    (forwardAnswer backwardAnswer : Fraction.Rational)
    (forwardInside : (integralBound forward.cells).Contains forwardAnswer)
    (backwardInside : (integralBound backward.cells).Contains backwardAnswer) :
    Fraction.abs (interval.signedLength * forwardAnswer + (-interval.signedLength) * backwardAnswer) ≤
      Fraction.abs interval.signedLength *
        ((integralBound forward.cells).width + (integralBound backward.cells).width) := by
  have compared := reverse_answers_difference_le source interval forward backward forwardAnswer backwardAnswer
    forwardInside backwardInside
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct compared
    (Fraction.Order.Arithmetic.abs_nonneg_direct interval.signedLength)
  have identity : interval.signedLength * forwardAnswer + (-interval.signedLength) * backwardAnswer =
      interval.signedLength * (forwardAnswer - backwardAnswer) := by ring1
  rw [identity, Bounds.Abs.abs_mul_direct]
  exact paid

/-- Midpoints of independently saved opposite-orientation process states cancel within their actual widths.

The forward and reverse states are the original persistent unit-process
states. Positive scaling and negation are the same operations used by the
oriented endpoint process; each state can come from an arbitrary saved
history and need not share a partition or request with the other. -/
theorem saved_midpoints_sum_le (source : Fraction.Rational → Fraction.Rational)
    (interval : Partition.Interval) (positive : 0 < interval.signedLength)
    (forwardModulus : Rational.Uniform.Modulus (pullback source interval))
    (backwardModulus : Rational.Uniform.Modulus (pullback source ⟨interval.finish, interval.start⟩))
    (forwardState : (Continuous.producer forwardModulus).boundProcess.State)
    (backwardState : (Continuous.producer backwardModulus).boundProcess.State) :
    let forwardBound := ((Continuous.producer forwardModulus).boundProcess.scalePositive
      interval.signedLength positive).bound forwardState
    let backwardBound := (((Continuous.producer backwardModulus).boundProcess.scalePositive
      interval.signedLength positive).neg).bound backwardState
    Fraction.abs (forwardBound.midpoint + backwardBound.midpoint) ≤ forwardBound.width + backwardBound.width := by
  let forwardFrontier : SourceFrontier (pullback source interval) := forwardState.1
  let backwardFrontier : SourceFrontier (pullback source ⟨interval.finish, interval.start⟩) := backwardState.1
  let forwardBound := integralBound forwardFrontier.cells
  let backwardBound := integralBound backwardFrontier.cells
  have compared := oriented_answers_sum_le source interval forwardFrontier backwardFrontier
    forwardBound.midpoint backwardBound.midpoint forwardBound.midpoint_contains backwardBound.midpoint_contains
  have absolute : Fraction.abs interval.signedLength = interval.signedLength := by
    change max interval.signedLength (-interval.signedLength) = interval.signedLength
    apply Fraction.Order.Basic.max_eq_left
    have negative := Fraction.Order.Arithmetic.neg_le_neg_direct positive.le
    rw [neg_zero] at negative
    exact negative.trans positive.le
  rw [absolute] at compared
  change Fraction.abs ((forwardBound.scale interval.signedLength positive.le).midpoint +
      (backwardBound.scale interval.signedLength positive.le).neg.midpoint) ≤
    (forwardBound.scale interval.signedLength positive.le).width +
      (backwardBound.scale interval.signedLength positive.le).neg.width
  rw [Interval.midpoint_neg, Interval.midpoint_scale, Interval.midpoint_scale,
    Interval.neg_width, Interval.scale_width, Interval.scale_width]
  have leftIdentity : interval.signedLength * forwardBound.midpoint +
      -(interval.signedLength * backwardBound.midpoint) =
      interval.signedLength * forwardBound.midpoint + (-interval.signedLength) * backwardBound.midpoint := by ring1
  have rightIdentity : interval.signedLength * forwardBound.width + interval.signedLength * backwardBound.width =
      interval.signedLength * (forwardBound.width + backwardBound.width) := by ring1
  rw [leftIdentity, rightIdentity]
  exact compared

end Purelib.Integration.SourceFrontier.Continuous.Affine

end
