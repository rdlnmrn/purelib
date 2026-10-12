module

public import Purelib.Riemann.Normalization.InverseModelOverlap
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Geometry.Rational.Box.Segment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Affine

import Purelib.Riemann.Normalization.InverseModelEdgeOverlap
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

@[expose] public section

/-!
# Cached edge-wide inverse-model transitions

Endpoint containment constructs the full shared straight segment.  Its one
cached comparison bit is reused at every rational cut; evaluating a new cut
does not execute another sign comparison.  Generated endpoint evaluations
remain admissible through the existing exact cache equations.
-/

namespace Purelib.Riemann.Normalization.InverseModelEdgeTransition

open Purelib.Riemann.Normalization.InverseModelOverlap (SignAlignment OverlapSample)

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Geometry.Rational.Box (contains_line)

section
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
/-- The affine line at parameter zero is its original starting point. -/
theorem line_zero (origin direction : Gaussian) : Affine.line origin direction 0 = origin := by
  change origin + (0 : Gaussian) * direction = origin
  rw [Basic.zero_mul, Basic.add_zero]

/-- The affine line from the original start toward the original finish reaches that finish at parameter one. -/
theorem line_one (start finish : Gaussian) : Affine.line start (finish - start) 1 = finish := by
  change start + (1 : Gaussian) * (finish - start) = finish
  rw [Basic.one_mul]
  ring1

end

/-- A retained overlap sample has the same flip as the canonical sample built from the two original model evaluations.
-/
theorem OverlapSample.flip_eq_build {polynomial : Polynomial} {leftBox rightBox : Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {point : Gaussian}
    (sample : OverlapSample left right point)
    (leftInside : leftBox.Contains point) (rightInside : rightBox.Contains point) :
    sample.alignment.flip = (OverlapSample.build left right point).alignment.flip := by
  rcases sample with ⟨leftValue, leftEq, rightValue, rightEq, alignment⟩
  subst leftValue rightValue
  change alignment.flip = (SignAlignment.build _ _).flip
  apply alignment.flip_unique (SignAlignment.build _ _) (parameter := polynomial.eval point)
    (leftError := left.bound) (rightError := right.bound) ?_ ?_ left.bound_small right.bound_small
  · rw [← left.residual_eq]
    exact left.residualBound point leftInside
  · rw [← right.residual_eq]
    exact right.residualBound point rightInside

set_option genInjectivity false in
/-- A retained sign transition between two inverse-root models along a segment contained in both model boxes.

The four original endpoint containments and the start-point overlap sample determine the sign reused throughout the
segment and every restriction. -/
structure EdgeTransition {polynomial : Polynomial} {leftBox rightBox : Box}
    (left : Model polynomial leftBox) (right : Model polynomial rightBox) (start finish : Gaussian) where
  /-- The original start belongs to the left model box. -/ leftStart : leftBox.Contains start
  /-- The original finish belongs to the left model box. -/ leftFinish : leftBox.Contains finish
  /-- The original start belongs to the right model box. -/ rightStart : rightBox.Contains start
  /-- The original finish belongs to the right model box. -/ rightFinish : rightBox.Contains finish
  /-- The retained overlap sample at the exact original start point. -/ sample : OverlapSample left right start

constructive_injectivity EdgeTransition

namespace EdgeTransition

variable {polynomial : Polynomial} {leftBox rightBox : Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
    {left : Model polynomial leftBox} {right : Model polynomial rightBox} {start finish : Gaussian}

/-- Build a segment transition from the four original endpoint containments and the canonical start-point overlap
sample. -/
def build (left : Model polynomial leftBox) (right : Model polynomial rightBox) (start finish : Gaussian)
    (leftStart : leftBox.Contains start) (leftFinish : leftBox.Contains finish)
    (rightStart : rightBox.Contains start) (rightFinish : rightBox.Contains finish) : EdgeTransition left right start
      finish :=
  ⟨leftStart, leftFinish, rightStart, rightFinish, OverlapSample.build left right start⟩

section
open Purelib.Geometry.Rational
/-- Every unit-interval point on the retained segment lies in the original left model box. -/
theorem left_contains_at (edge : EdgeTransition left right start finish)
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    leftBox.Contains (Affine.line start (finish - start) parameter) :=
  Box.contains_line edge.leftStart edge.leftFinish inside

/-- Every unit-interval point on the retained segment lies in the original right model box. -/
theorem right_contains_at (edge : EdgeTransition left right start finish)
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    rightBox.Contains (Affine.line start (finish - start) parameter) :=
  Box.contains_line edge.rightStart edge.rightFinish inside

end

/-- The Gaussian unit sign selected by the retained start-point overlap sample. -/
def sign (edge : EdgeTransition left right start finish) : Gaussian :=
  if edge.sample.alignment.flip then -1 else 1

open Purelib.Data.Gaussian in
/-- The retained transition sign has squared norm one.

The original flip selects one or negative one, and Gaussian quadrance
has the same value in either retained Boolean branch. -/
theorem sign_norm (edge : EdgeTransition left right start finish) : normSq edge.sign = 1 := by
  unfold sign
  cases edge.sample.alignment.flip with
  | false => exact Basic.Canonical.normSq_one
  | true => exact (Basic.Canonical.normSq_neg (1 : Gaussian)).trans Basic.Canonical.normSq_one

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.Normalization in
/-- Every canonical overlap sample on the retained segment has the original start-point flip. -/
theorem flip_eq_at (edge : EdgeTransition left right start finish)
    {parameter : Coordinate} (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    edge.sample.alignment.flip =
      (OverlapSample.build left right (Affine.line start (finish - start) parameter)).alignment.flip := by
  have along := (InverseModelEdgeOverlap.Model.edge_flip_eq left) right start (finish - start)
    (⟨0, 1, by decide⟩ : Data.Rat.Interval.Bounds)
    (fun _ inside => Box.contains_line edge.leftStart edge.leftFinish inside)
    (fun _ inside => Box.contains_line edge.rightStart edge.rightFinish inside)
    (first := 0) (last := parameter) ⟨le_rfl, by decide⟩ inside
  rw [line_zero] at along
  exact (OverlapSample.flip_eq_build edge.sample edge.leftStart edge.rightStart).trans along

/-- The canonical finish-point overlap sample has the original start-point flip. -/
theorem flip_eq_finish (edge : EdgeTransition left right start finish) :
    edge.sample.alignment.flip = (OverlapSample.build left right finish).alignment.flip := by
  have same := edge.flip_eq_at (parameter := 1) ⟨by decide, le_rfl⟩
  rw [line_one] at same
  exact same

open Purelib.Geometry.Rational in
/-- Sample both original model evaluations at a unit-interval point using the retained segment flip.

The record caches the exact affine point and evaluations; nearestness follows from equality with the canonical pointwise
flip, without choosing a new sign. -/
def sampleAt (edge : EdgeTransition left right start finish)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    OverlapSample left right (Affine.line start (finish - start) parameter) :=
  let point := Affine.line start (finish - start) parameter
  let leftValue := left.value.eval point
  let rightValue := right.value.eval point
  { leftValue := leftValue
    leftValue_eq := rfl
    rightValue := rightValue
    rightValue_eq := rfl
    alignment :=
      { flip := edge.sample.alignment.flip
        value := if edge.sample.alignment.flip then -rightValue else rightValue
        value_eq := rfl
        nearest := by
          have same : edge.sample.alignment.flip = (SignAlignment.build leftValue rightValue).flip := edge.flip_eq_at
            inside
          rw [same, ← (SignAlignment.build leftValue rightValue).value_eq]
          exact (SignAlignment.build leftValue rightValue).nearest } }

/-- A sample made along the retained transition keeps its original start-point flip exactly. -/
theorem sampleAt_flip (edge : EdgeTransition left right start finish)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (edge.sampleAt parameter inside).alignment.flip = edge.sample.alignment.flip := rfl

section
open Purelib.Geometry.Rational
/-- The selected point sample equals the right-model value times the retained sign.

Both values use the same affine point and the original start-point flip;
this identity does not execute a new pointwise sign comparison. -/
theorem sampleAt_selected (edge : EdgeTransition left right start finish)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (edge.sampleAt parameter inside).alignment.value =
      edge.sign * right.value.eval (Affine.line start (finish - start) parameter) := by
  dsimp only [sampleAt, sign]
  cases edge.sample.alignment.flip with
  | false =>
      change right.value.eval (Affine.line start (finish - start) parameter) =
        (1 : Gaussian) * right.value.eval (Affine.line start (finish - start) parameter)
      exact (Purelib.Data.Gaussian.Basic.one_mul _).symm
  | true =>
      change -right.value.eval (Affine.line start (finish - start) parameter) =
        (-1 : Gaussian) * right.value.eval (Affine.line start (finish - start) parameter)
      ring1

/-- Restrict the transition to any two retained unit-interval parameters, keeping both original models and the original
flip.

The new endpoint containments follow from the original segment certificate, and the new start sample is the retained
sample at the first parameter. No ordering of the two parameters is required. -/
def restrict (edge : EdgeTransition left right start finish)
    (first last : Coordinate) (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    EdgeTransition left right (Affine.line start (finish - start) first)
      (Affine.line start (finish - start) last) where
  leftStart := Box.contains_line edge.leftStart edge.leftFinish firstInside
  leftFinish := Box.contains_line edge.leftStart edge.leftFinish lastInside
  rightStart := Box.contains_line edge.rightStart edge.rightFinish firstInside
  rightFinish := Box.contains_line edge.rightStart edge.rightFinish lastInside
  sample := edge.sampleAt first firstInside

end

/-- Restricting a retained transition preserves its original flip exactly. -/
theorem restrict_flip (edge : EdgeTransition left right start finish)
    (first last : Coordinate) (firstInside : 0 ≤ first ∧ first ≤ 1) (lastInside : 0 ≤ last ∧ last ≤ 1) :
    (edge.restrict first last firstInside lastInside).sample.alignment.flip = edge.sample.alignment.flip := rfl

open Purelib.Geometry.Rational in
/-- The retained point sample's squared alignment distance is bounded by six times the sum of model residual bounds
times the left-value squared norm. -/
theorem sampleAt_distance_le (edge : EdgeTransition left right start finish)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    normSq ((edge.sampleAt parameter inside).leftValue - (edge.sampleAt parameter inside).alignment.value) ≤
      6 * (left.bound + right.bound) * normSq (edge.sampleAt parameter inside).leftValue :=
  (edge.sampleAt parameter inside).distance_le
    (Box.contains_line edge.leftStart edge.leftFinish inside)
    (Box.contains_line edge.rightStart edge.rightFinish inside)

end EdgeTransition

end Purelib.Riemann.Normalization.InverseModelEdgeTransition
