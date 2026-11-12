module

public import Purelib.Approximation.Rational.Pi.Source
public import Purelib.Approximation.Rational.Pi.Endpoint
public import Purelib.Approximation.Gaussian.Process.RationalBound
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Sampling
public import Purelib.Integration.Cell.Source.Comparison.Intersection
import Purelib.Integration.Cell.Source.Comparison.Weights
import Purelib.Data.Rat.Interval.Comparison
import Purelib.Data.Rat.Bounds.Abs
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Gaussian.RationalEmbedding
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Coherent Gaussian observation of the circle-source integral

The process retains the original source-frontier history. Its finite Gaussian
balls observe the rational integral intervals at those same states; a common
refinement relates independently obtained histories.
-/

namespace Purelib.Approximation.Gaussian.Pi.Integral

open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational.Pi
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration

/-- The Gaussian observation process retains the original source producer's states and requests. -/
@[expose] public def process : Gaussian.Process :=
  Process.RationalBound.toProcess Source.boundProcess

/-- Select the midpoint answer of the exact frontier retained at a source-history state. -/
@[expose] public def answer (state : Source.boundProcess.State) : Fraction.Rational :=
  (Source.boundProcess.bound state).midpoint

/-- The original producer's initial result and initial history select the same answer. -/
public theorem answer_initial : answer Source.boundProcess.initial =
    (Source.producer.request ⟨1, by decide⟩).answer := rfl

/-- Each Gaussian witness is the selected answer of that exact retained history state. -/
public theorem witness_eq (state : Source.boundProcess.State) :
    (process.witness state).val = RationalEmbedding.realPoint (answer state) := rfl

/-- Refinement uses the original producer history and its finite width request. -/
public theorem refine_eq (state : Source.boundProcess.State) (target : Fraction.Rational) (positive : 0 < target) :
    process.refine state target positive =
      Source.boundProcess.request state (Rational.Request.Square.gapTarget target)
        (Rational.Request.Square.gapTarget_pos positive) := rfl

/-- Any two retained source histories have overlapping original integral bounds.

Their common source refinement gives one explicit rational point in both
intervals, regardless of how either history was independently refined. -/
public theorem bounds_overlap (left right : Source.boundProcess.State) :
    (Source.boundProcess.bound left).Overlaps (Source.boundProcess.bound right) := by
  change (integralBound left.1.cells).Overlaps (integralBound right.1.cells)
  let common := SourceFrontier.commonReadings left.1 right.1
  let shared := integralBound common.intersection.cells
  exact Interval.overlaps_of_common
    (common.intersection_refines_left.contains shared.sample_contains)
    (common.intersection_refines_right.contains shared.sample_contains)

/-- Compare the selected history answer with a reading of an independent source frontier.

The bound pays both actual frontier widths and uses their common rational
refinement. The independent reading need not lie in the history's interval. -/
public theorem answer_difference_le (state : Source.boundProcess.State)
    (other : SourceFrontier Source.value) (reading : Fraction.Rational)
    (inside : (integralBound other.cells).Contains reading) :
    Fraction.abs (answer state - reading) ≤
      (Source.boundProcess.bound state).width + (integralBound other.cells).width := by
  change Fraction.abs ((integralBound state.1.cells).midpoint - reading) ≤
    (integralBound state.1.cells).width + (integralBound other.cells).width
  exact (SourceFrontier.commonReadings state.1 other).answers_difference_le_of_same
    _ _ (integralBound state.1.cells).midpoint_contains inside (fun _ _ _ => rfl)

/-- Compare an actual history answer with a reading in a uniform endpoint frontier.

Both the history width and the endpoint-frontier width remain in the bound;
the reading need not belong to the history's own enclosure. -/
public theorem answer_endpoint_difference_le (state : Source.boundProcess.State) (extra : Nat)
    (reading : Fraction.Rational)
    (inside : (integralBound (Endpoint.frontier extra).cells).Contains reading) :
    Fraction.abs (answer state - reading) ≤
      (Source.boundProcess.bound state).width + (integralBound (Endpoint.frontier extra).cells).width :=
  answer_difference_le state (Endpoint.frontier extra) reading inside

/-- Compare a history answer with an indexed endpoint reading using its exact mesh width.

The history's actual retained width remains in the bound independently of
the endpoint grid's cell count. -/
public theorem answer_endpoint_difference_le_mesh (state : Source.boundProcess.State) (extra : Nat)
    (reading : Fraction.Rational)
    (inside : (integralBound (Endpoint.frontier extra).cells).Contains reading) :
    Fraction.abs (answer state - reading) ≤
      (Source.boundProcess.bound state).width + 2 / ((extra + 1 : Nat) : Fraction.Rational) := by
  have comparison := answer_endpoint_difference_le state extra reading inside
  rw [Endpoint.frontier_width] at comparison
  exact comparison

/-- The source history is coherent under its actual squared interval widths.

The pairwise comparison uses an explicit common source refinement; a bound
process's individual refinement laws alone do not provide this agreement. -/
@[expose] public def coherent : Process.Coherence.Basic.Coherent process where
  allowance state := (Source.boundProcess.bound state).width ^ 2
  allowance_nonneg _ := Arithmetic.sq_nonneg_direct _
  ball_radius_le _ := le_rfl
  possible_close := by
    intro leftState rightState leftValue rightValue leftPossible rightPossible
    change ∃ candidate : Fraction.Rational,
      (Source.boundProcess.bound leftState).Contains candidate ∧
        leftValue = RationalEmbedding.realPoint candidate at leftPossible
    change ∃ candidate : Fraction.Rational,
      (Source.boundProcess.bound rightState).Contains candidate ∧
        rightValue = RationalEmbedding.realPoint candidate at rightPossible
    rcases leftPossible with ⟨left, leftInside, rfl⟩
    rcases rightPossible with ⟨right, rightInside, rfl⟩
    have absolute := Interval.abs_sub_le_of_overlaps leftInside rightInside (bounds_overlap leftState rightState)
    have squared := Arithmetic.pow_le_pow_direct
      (Arithmetic.abs_nonneg_direct (left - right)) absolute 2
    rw [Bounds.Abs.abs_sq_direct] at squared
    rw [RationalEmbedding.realPoint_sub, RationalEmbedding.normSq_realPoint]
    have widthSquares : 0 ≤ (Source.boundProcess.bound leftState).width ^ 2 +
        (Source.boundProcess.bound rightState).width ^ 2 := by
      have both := Arithmetic.add_le_add_direct
        (Arithmetic.sq_nonneg_direct (Source.boundProcess.bound leftState).width)
        (Arithmetic.sq_nonneg_direct (Source.boundProcess.bound rightState).width)
      simpa only [Fraction.Field.zero_add] using both
    calc
      (left - right) ^ 2 ≤
          ((Source.boundProcess.bound leftState).width + (Source.boundProcess.bound rightState).width) ^ 2 := squared
      _ ≤ 2 * ((Source.boundProcess.bound leftState).width ^ 2 +
          (Source.boundProcess.bound rightState).width ^ 2) := Bounds.Square.add_sq_le_two _ _
      _ ≤ 4 * ((Source.boundProcess.bound leftState).width ^ 2 +
          (Source.boundProcess.bound rightState).width ^ 2) :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) widthSquares
  accuracyRequest target := target
  accuracyRequest_pos positive := positive
  refine_accurate := by
    intro state target _ request positive small
    exact (process.accurate state request positive).trans small

/-- The original persistent circle-source history as a coherent real Gaussian name. -/
@[expose] public def named : Name.Coherent.CoherentNamed :=
  { name := ⟨process, Source.boundProcess.initial⟩
    coherent := coherent }

/-- Canonical samples read the midpoint of the exact source history selected at each stage. -/
public theorem sample_eq (index : Nat) :
    (Name.Sampling.approximation named.name).sample index =
      RationalEmbedding.realPoint
        (answer (Process.Sampling.stateAt process Source.boundProcess.initial index)) := rfl

/-- Every canonical sample of the source-integral name lies on the real axis. -/
public theorem sample_im_zero (index : Nat) :
    ((Name.Sampling.approximation named.name).sample index).im = 0 := rfl

end Purelib.Approximation.Gaussian.Pi.Integral
