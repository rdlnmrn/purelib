module
import Purelib.Approximation.Gaussian.Representation.Ball
public import Purelib.Approximation.Gaussian.Representation.Sequence
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.SignedDigit.Cell
import Purelib.Approximation.Gaussian.SignedDigit.Geometry
public import Purelib.Approximation.Gaussian.SignedDigit.Representation
public import Purelib.Approximation.Gaussian.Translation.Realizer
import Purelib.Approximation.Gaussian.Translation.Request
import Purelib.Approximation.Rational.Geometric.Basic
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Representation.Basic
import Purelib.Approximation.Gaussian.Translation.Observation
import Purelib.Approximation.Gaussian.Translation.Schedule
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.SignedDigit.Binary.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Representation

open Purelib.Approximation.Gaussian.SignedDigit

open Purelib.Approximation.Gaussian.SignedDigit.Cell

open Purelib.Approximation.Gaussian.Translation

open Purelib.Approximation.Rational

open Purelib.Approximation.Rational.Geometric

open Purelib.Data.Rat

section
public section

/-!
# Redundant signed-digit interval observations

The positional representation here is genuinely redundant: digits are
`-1`, `0`, and `1`, and distinct finite words can determine the same centre.
Every observation is a closed rational square.  A finite greedy encoder keeps
an explicit residual in `[-1,1]`; no stream or completed real is formed.
-/

namespace Purelib.Approximation.Gaussian.SignedDigit.Translation

/-! ## Translation from finite fast-Cauchy observations -/

/-- The original approximation's uniform centre bound plus one, used as a common signed-digit coordinate scale. -/
@[expose] def ambientScale (approximation : Sequence.ApproximationData) : Fraction.Rational :=
  approximation.centerBound + 1

/-- The signed-digit ambient coordinate scale is strictly positive. -/
theorem ambientScale_pos (approximation : Sequence.ApproximationData) :
    0 < ambientScale approximation :=
  Arithmetic.add_pos_of_nonneg_of_pos_direct approximation.centerBound_nonneg (by decide)

/-- The approximation's retained centre bound is at most the square of its ambient coordinate scale. -/
private theorem centerBound_le_ambientScale_sq
    (approximation : Sequence.ApproximationData) :
    approximation.centerBound ≤ ambientScale approximation ^ 2 :=
      by
  apply Arithmetic.le_of_sub_nonneg_direct
  calc
    0 ≤ approximation.centerBound ^ 2 +
        approximation.centerBound + 1 :=
      add_nonneg
        (add_nonneg
          (Arithmetic.sq_nonneg_direct _)
          approximation.centerBound_nonneg) (by decide)
    _ = ambientScale approximation ^ 2 - approximation.centerBound := by
      unfold ambientScale
      ring1

/-- Both coordinates of every finite approximation sample lie between the signed ambient scale bounds. -/
theorem sample_coordinate_bounds (approximation : Sequence.ApproximationData)
    (index : Nat) :
    -ambientScale approximation ≤ (approximation.sample index).re ∧
      (approximation.sample index).re ≤ ambientScale approximation ∧
      -ambientScale approximation ≤ (approximation.sample index).im ∧
      (approximation.sample index).im ≤ ambientScale approximation := by
  have normBound := (approximation.sample_bounded index).trans
    (centerBound_le_ambientScale_sq approximation)
  have realSquare : (approximation.sample index).re ^ 2 ≤
      ambientScale approximation ^ 2 := by
    calc
      (approximation.sample index).re ^ 2 ≤
          (approximation.sample index).re ^ 2 +
            (approximation.sample index).im ^ 2 :=
        le_add_of_nonneg_right
          (Arithmetic.sq_nonneg_direct _)
      _ ≤ ambientScale approximation ^ 2 := normBound
  have imagSquare : (approximation.sample index).im ^ 2 ≤
      ambientScale approximation ^ 2 := by
    calc
      (approximation.sample index).im ^ 2 ≤
          (approximation.sample index).re ^ 2 +
            (approximation.sample index).im ^ 2 :=
        le_add_of_nonneg_left
          (Arithmetic.sq_nonneg_direct _)
      _ ≤ ambientScale approximation ^ 2 := normBound
  have scaleNonnegative := (ambientScale_pos approximation).le
  exact
    ⟨Arithmetic.neg_le_of_sq_le_sq_direct
        scaleNonnegative realSquare,
      Arithmetic.le_of_sq_le_sq_direct
        scaleNonnegative realSquare,
      Arithmetic.neg_le_of_sq_le_sq_direct
        scaleNonnegative imagSquare,
      Arithmetic.le_of_sq_le_sq_direct
        scaleNonnegative imagSquare⟩

/-- Compute a finite signed-digit depth whose scale-two squared-radius allowance meets the original positive request. -/
@[expose] def requestDepth (approximation : Sequence.ApproximationData)
    (request : Request) : Nat :=
  Search.firstQuarterBelow
    (2 * ambientScale approximation ^ 2) 0 request.targetSq

/-- A random-access approximation request translated into two persistent redundant signed-digit prefixes. -/
@[expose] def fromApproximation (approximation : Sequence.ApproximationData) :
    Realizer
      (Sequence.approximationRepresentation approximation)
      Representation.representation where
  translate index request := by
    let refined := approximation.refineIndex index request.targetSq
      request.positive
    let depth := requestDepth approximation request
    let output := Cell.ofPoint (approximation.sample refined)
      (ambientScale approximation)
        (ambientScale_pos approximation)
      (sample_coordinate_bounds approximation refined) depth
    exact
      { source' := refined
        output := output
        source_refines := approximation.refineIndex_ge index
          request.targetSq request.positive
        relates := fun sourceValue targetValue =>
          Data.Gaussian.Norm.Basic.normSq (targetValue - sourceValue) ≤
            approximation.radiusSq refined + 8 * output.tail ^ 2
        source_to_target := by
          rintro sourceValue ⟨later, order, rfl⟩
          refine ⟨approximation.sample refined,
            Cell.ofPoint_contains _ _ _ _ _, ?_⟩
          have closeForward := approximation.later_close order
          have closeReverse :
              Data.Gaussian.Norm.Basic.normSq (approximation.sample refined -
                approximation.sample later) ≤ approximation.radiusSq refined := by
            have identity : approximation.sample refined -
                approximation.sample later =
              -(approximation.sample later - approximation.sample refined) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
                  Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
            rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
            exact closeForward
          exact closeReverse.trans
            (le_add_of_nonneg_right
              (Arithmetic.mul_nonneg_direct (by decide)
                (Arithmetic.sq_nonneg_direct output.tail)))
        target_to_source := by
          intro targetValue targetPossible
          refine ⟨approximation.sample refined,
            approximation.sample_possible refined, ?_⟩
          have pairBound := Cell.normSq_sub_le_eight_tailSq targetPossible
            (Cell.ofPoint_contains _ _ _ _ _)
          exact pairBound.trans
            (le_add_of_nonneg_left
              (approximation.radiusSq_nonneg refined))
        precisionLoss := 0
        precisionLoss_nonneg := le_rfl
        precision := by
          change Basic.quarterRadius
              (2 * ambientScale approximation ^ 2) depth <
            request.targetSq + 0
          calc
            Basic.quarterRadius
                (2 * ambientScale approximation ^ 2) depth <
                request.targetSq :=
              Search.firstQuarterBelow_accurate _
                (Arithmetic.mul_nonneg_direct (by decide)
                  (Arithmetic.sq_nonneg_direct _))
                0 request.targetSq request.positive
            _ = request.targetSq + 0 := by ring1
        schedule :=
          { sourceRefinements := 1
            emittedUnits := 2 * depth
            arithmeticSteps := 2 * depth + 3 }
        costBound := 4 * depth + 4
        cost_le := by
          change 1 + 2 * depth + (2 * depth + 3) ≤ 4 * depth + 4
          omega }

/-- Nat-indexed executable entry point which hides the representation's definitionally equal observation type from
clients. -/
@[expose] def fromApproximationAt (approximation : Sequence.ApproximationData) (index : Nat)
    (request : Request) :=
  (fromApproximation approximation).translate index request

/-- The translated signed-digit cell has exactly the computed request depth. -/
@[simp] theorem fromApproximationAt_depth (approximation : Sequence.ApproximationData)
    (index : Nat) (request : Request) :
    (fromApproximationAt approximation index request).output.depth =
      requestDepth approximation request := rfl

/-- The translated real digit word has exactly the computed request depth. -/
@[simp] theorem fromApproximationAt_real_length
    (approximation : Sequence.ApproximationData) (index : Nat)
    (request : Request) :
    (fromApproximationAt approximation index
      request).output.realDigits.length =
      requestDepth approximation request :=
  (fromApproximationAt approximation index request).output.real_length

/-- The translated imaginary digit word has exactly the computed request depth. -/
@[simp] theorem fromApproximationAt_imag_length
    (approximation : Sequence.ApproximationData) (index : Nat)
    (request : Request) :
    (fromApproximationAt approximation index
      request).output.imagDigits.length =
      requestDepth approximation request :=
  (fromApproximationAt approximation index request).output.imag_length

/-- The translation cost bound is four times the computed request depth plus four. -/
@[simp] theorem fromApproximationAt_costBound
    (approximation : Sequence.ApproximationData) (index : Nat)
    (request : Request) :
    (fromApproximationAt approximation index request).costBound =
      4 * requestDepth approximation request + 4 := rfl

/-- The original translation result retains the computed depth, both digit lengths and the matching finite cost bound.
-/
theorem fromApproximationAt_data (approximation : Sequence.ApproximationData)
    (index : Nat) (request : Request) :
    let result := fromApproximationAt approximation index request
    result.output.depth = requestDepth approximation request ∧
      result.output.realDigits.length = requestDepth approximation
        request ∧
      result.output.imagDigits.length = requestDepth approximation
        request ∧
      result.costBound = 4 * requestDepth approximation request + 4 := by
  dsimp only
  exact ⟨fromApproximationAt_depth approximation index request,
    fromApproximationAt_real_length approximation index request,
    fromApproximationAt_imag_length approximation index request,
    fromApproximationAt_costBound approximation index request⟩

/-- The translated signed-digit cell's precision allowance is strictly below the original target. -/
theorem fromApproximationAt_precision (approximation : Sequence.ApproximationData)
    (index : Nat) (request : Request) :
    Representation.representation.precisionSq
        (fromApproximationAt approximation index request).output <
      request.targetSq := by
  let result := fromApproximationAt approximation index request
  calc
    Representation.representation.precisionSq result.output <
        request.targetSq + result.precisionLoss := result.precision
    _ = request.targetSq := by
      change request.targetSq + 0 = request.targetSq
      ring1

/-- Converting the translated signed-digit cell to its enclosing ball preserves the original strict precision target. -/
theorem fromApproximationAt_toBall_precision (approximation : Sequence.ApproximationData)
    (index : Nat) (request : Request) :
    Ball.ballRepresentation.precisionSq
        (Representation.toBall.map
          (fromApproximationAt approximation index request).output) <
      request.targetSq := by
  let output := (fromApproximationAt approximation index request).output
  calc
    Ball.ballRepresentation.precisionSq
        (Representation.toBall.map output) ≤
      Representation.representation.precisionSq output + Representation.toBall.precisionLoss output :=
        Representation.toBall.precision_le output
    _ = Representation.representation.precisionSq output := by
      change Representation.representation.precisionSq output + 0 = _
      ring1
    _ < request.targetSq :=
      fromApproximationAt_precision approximation index request
end Purelib.Approximation.Gaussian.SignedDigit.Translation

end
