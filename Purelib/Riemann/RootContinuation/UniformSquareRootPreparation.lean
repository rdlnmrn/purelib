module
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Bounds.Taylor
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Power
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Square.Anchored
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Geometry.Rational.Box.Square.Symmetric.Norm
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Interior
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Horner
import Purelib.Polynomial.Dense.Gaussian.Linear.Affine
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Bounds
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Square.Separated
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.Newton.Restart.Separated.Basic
import Purelib.RootIsolation.Newton.Restart.Separated.State
public import Purelib.RootIsolation.Newton.Restart.Separated.Track
public import Purelib.RootIsolation.SquareRoot.Newton.Search
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Newton.Build

import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
public import Purelib.Riemann.Branches.ClearSheetContinuation
public import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Polynomial.Bounds.Horner
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

/-!
# Uniform finite square-root preparation along a clear segment

The generic global isolator may choose a different auxiliary radius at every
base parameter.  For the structured quadratic `Y^2 - f(x)` this is
unnecessary.  This file constructs one rational root ambient from a finite
variation bound for the whole clear segment and proves a parameter-uniform
boundary clearance on that ambient.  It is the finite replacement for a
compactness argument in the persistent refinement schedule.
-/

namespace Purelib.Riemann.RootContinuation.UniformSquareRootPreparation

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier. -/
public abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
public abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- Dense Gaussian polynomials over exact rational coordinates. -/
public abbrev GaussianPolynomial :=
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The original rational box type with retained coordinate bounds. -/
public abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root owner indexed by its exact radicand. -/
public abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner

/-! ## Finite path-range bounds -/

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- Bound polynomial values along an affine segment by recursive dyadic subdivision.

Each leaf uses the exact composed polynomial's unit-parameter-box majorant; internal nodes retain the maximum of their
two half-segment bounds. -/
@[expose] public def dyadicLineNormMajorant (polynomial : GaussianPolynomial)
    (origin direction : Gaussian) : Nat -> Coordinate
  | 0 => Bounds.Box.denseEvalNormMajorant
      (Substitution.Affine.composeLine polynomial origin direction)
      ClearSheetContinuation.parameterAmbient
  | depth + 1 =>
      let half := Scale.scale (1 / 2) direction
      max (dyadicLineNormMajorant polynomial origin half depth)
        (dyadicLineNormMajorant polynomial (origin + half) half depth)

section

open Purelib.Data.Gaussian

/-- Halve the original direction once per depth to obtain a leaf-segment direction.

Each step retains the original direction scaled by one half. Structural recursion follows that same leftmost direction
for the supplied finite depth. -/
@[expose] public def dyadicLeftmostDirection (direction : Gaussian) : Nat → Gaussian
  | 0 => direction
  | depth + 1 =>
      dyadicLeftmostDirection (Scale.scale (1 / 2) direction) depth

/-- Follow the right half at each subdivision step to obtain the last leaf's origin.

Each step adds the retained half direction to the current origin and keeps that same half direction for the next step.
The supplied finite depth determines the final rightmost origin. -/
@[expose] public def dyadicRightmostOrigin (origin direction : Gaussian) : Nat → Gaussian
  | 0 => origin
  | depth + 1 =>
      let half := Scale.scale (1 / 2) direction
      dyadicRightmostOrigin (origin + half) half depth

end

section

open Purelib.Data.Gaussian
open Purelib.Data.Rat

/-- The leftmost leaf's exact evaluation majorant is at most the retained dyadic maximum.

Each original left half retains its halved direction and the same origin.
The leaf bound is compared with the actual recursively computed maximum. -/
public theorem dyadicLineNormMajorant_leftmost_le (polynomial : GaussianPolynomial)
    (origin direction : Gaussian) : ∀ depth : Nat,
    dyadicLineNormMajorant polynomial origin
        (dyadicLeftmostDirection direction depth) 0 ≤
      dyadicLineNormMajorant polynomial origin direction depth := by
  intro depth
  induction depth generalizing direction with
  | zero => exact le_rfl
  | succ depth inductionHypothesis =>
      rw [dyadicLineNormMajorant]
      exact (inductionHypothesis
        (Scale.scale (1 / 2) direction)).trans (Fraction.Order.Basic.le_max_left _ _)

/-- The rightmost leaf's exact evaluation majorant is at most the retained dyadic maximum.

The retained right-half origins and halved direction determine the same
last leaf. Its computed bound is one branch of the original dyadic maximum. -/
public theorem dyadicLineNormMajorant_rightmost_le (polynomial : GaussianPolynomial)
    (origin direction : Gaussian) : ∀ depth : Nat,
    dyadicLineNormMajorant polynomial
        (dyadicRightmostOrigin origin direction depth)
          (dyadicLeftmostDirection direction depth) 0 ≤
      dyadicLineNormMajorant polynomial origin direction depth := by
  intro depth
  induction depth generalizing origin direction with
  | zero => exact le_rfl
  | succ depth inductionHypothesis =>
      rw [dyadicLineNormMajorant]
      exact (inductionHypothesis
        (origin + Scale.scale (1 / 2) direction)
          (Scale.scale (1 / 2) direction)).trans (Fraction.Order.Basic.le_max_right _ _)

end

/-- Doubling one rational factor cancels halving the other factor. -/
private theorem half_double_mul (left right : Coordinate) :
    (2 * left) * ((1 / 2 : Coordinate) * right) = left * right := by
  calc
    (2 * left) * ((1 / 2 : Coordinate) * right) =
        (2 * (1 / 2 : Coordinate)) * (left * right) := by ring1
    _ = left * right := by
      rw [show (2 : Coordinate) * (1 / 2) = 1 by decide]
      ring1

/-- The right-half affine scalar formula equals the original product. -/
private theorem right_half_mul (left right : Coordinate) :
    (1 / 2 : Coordinate) * right +
        (2 * left - 1) * ((1 / 2 : Coordinate) * right) =
      left * right := by
  have coefficient : (1 / 2 : Coordinate) +
      (2 * left - 1) * (1 / 2) = left := by
    calc
      (1 / 2 : Coordinate) + (2 * left - 1) * (1 / 2) =
          left * (2 * (1 / 2 : Coordinate)) := by ring1
      _ = left := by
        rw [show (2 : Coordinate) * (1 / 2) = 1 by decide]
        ring1
  calc
    (1 / 2 : Coordinate) * right +
        (2 * left - 1) * ((1 / 2 : Coordinate) * right) =
      ((1 / 2 : Coordinate) + (2 * left - 1) * (1 / 2)) * right := by
        ring1
    _ = left * right := by rw [coefficient]

section

open Purelib.Data.Gaussian
open Purelib.Geometry.Rational

/-- The left half-segment at twice the parameter equals the original affine point.

The arbitrary rational parameter is doubled while the original direction
is halved. Coordinate identities identify the exact same affine point. -/
private theorem line_left_half (origin direction : Gaussian)
    (parameter : Coordinate) :
    Affine.line origin
        (Scale.scale (1 / 2) direction) (2 * parameter) =
      Affine.line origin direction parameter := by
  apply Basic.ext <;>
    simp only [Affine.line,
      Cast.ofCoordinate_re,
      Cast.ofCoordinate_im,
      Scale.scale_re, Scale.scale_im,
      Basic.add_re,
      Basic.add_im,
      Basic.mul_re,
      Basic.mul_im] <;>
    rw [half_double_mul] <;>
    ring1

/-- The right half-segment at twice the parameter minus one equals the original affine point.

The original half direction is added to the origin, and twice the same
parameter minus one selects the retained right-half affine point. -/
private theorem line_right_half (origin direction : Gaussian)
    (parameter : Coordinate) :
    Affine.line
        (origin + Scale.scale (1 / 2) direction)
        (Scale.scale (1 / 2) direction) (2 * parameter - 1) =
      Affine.line origin direction parameter := by
  apply Basic.ext
  · simp only [Affine.line, Cast.ofCoordinate_re, Cast.ofCoordinate_im,
      Scale.scale_re, Scale.scale_im, Basic.add_re, Basic.mul_re]
    calc
      _ = origin.re + ((1 / 2 : Coordinate) * direction.re +
          (2 * parameter - 1) * ((1 / 2 : Coordinate) * direction.re)) := by ring1
      _ = origin.re + parameter * direction.re :=
        congrArg (fun coordinate => origin.re + coordinate)
          (right_half_mul parameter direction.re)
      _ = _ := by ring1
  · simp only [Affine.line, Cast.ofCoordinate_re, Cast.ofCoordinate_im,
      Scale.scale_re, Scale.scale_im, Basic.add_im, Basic.mul_im]
    calc
      _ = origin.im + ((1 / 2 : Coordinate) * direction.im +
          (2 * parameter - 1) * ((1 / 2 : Coordinate) * direction.im)) := by ring1
      _ = origin.im + parameter * direction.im :=
        congrArg (fun coordinate => origin.im + coordinate)
          (right_half_mul parameter direction.im)
      _ = _ := by ring1

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- Every unit-interval affine sample satisfies the retained dyadic squared-norm majorant.

At each depth the parameter selects its exact half-interval, whose recursively retained majorant is bounded by the
parent maximum. -/
public theorem normSq_eval_line_le_dyadicLineNormMajorant
    (polynomial : GaussianPolynomial) (origin direction : Gaussian)
    (depth : Nat) (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval
          (Affine.line origin direction parameter)) <=
      dyadicLineNormMajorant polynomial origin direction depth := by
  induction depth generalizing origin direction parameter with
  | zero =>
      have bound :=
        Bounds.Box.normSq_eval_le_denseEvalNormMajorant
          (Substitution.Affine.composeLine polynomial origin direction)
          (ClearSheetContinuation.parameterAmbient_contains
            parameter inside)
      rw [Substitution.Affine.eval_composeLine] at bound
      exact bound
  | succ depth inductionHypothesis =>
      let half := Scale.scale (1 / 2) direction
      by_cases left : parameter <= 1 / 2
      · have localInside : (0 : Coordinate) <= 2 * parameter ∧
            2 * parameter <= 1 := by
          constructor
          · exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
              inside.1
          · calc
              2 * parameter <= 2 * (1 / 2) :=
                Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                  left (by decide)
              _ = 1 := by decide
        have localBound := inductionHypothesis origin half
          (2 * parameter) localInside
        rw [line_left_half] at localBound
        exact localBound.trans (Fraction.Order.Basic.le_max_left _ _)
      · have halfLt : (1 / 2 : Coordinate) < parameter :=
          Fraction.Order.Arithmetic.lt_of_not_ge_direct left
        have localInside : (0 : Coordinate) <= 2 * parameter - 1 ∧
            2 * parameter - 1 <= 1 := by
          constructor
          · apply Fraction.Order.Arithmetic.sub_nonneg_direct
            calc
              1 = 2 * (1 / 2 : Coordinate) := by decide
              _ <= 2 * parameter :=
                Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                  halfLt.le (by decide)
          · calc
              2 * parameter - 1 <= 2 * 1 - 1 :=
                Fraction.Order.Arithmetic.sub_le_sub_right_direct
                  (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                    inside.2 (by decide)) 1
              _ = 1 := by ring1
        have localBound := inductionHypothesis (origin + half) half
          (2 * parameter - 1) localInside
        rw [line_right_half] at localBound
        exact localBound.trans (Fraction.Order.Basic.le_max_right _ _)

open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Data.Rat in
/-- The recursive dyadic evaluation majorant is nonnegative.

Each original leaf uses the nonnegative finite evaluation majorant. The retained maximum at every internal node bounds
both nonnegative child values. -/
public theorem dyadicLineNormMajorant_nonneg (polynomial : GaussianPolynomial)
    (origin direction : Gaussian) (depth : Nat) :
    0 <= dyadicLineNormMajorant polynomial origin direction depth := by
  induction depth generalizing origin direction with
  | zero =>
      exact (Bounds.Box.denseEvalNormMajorant_pos _ _).le
  | succ depth inductionHypothesis =>
      exact (inductionHypothesis origin
        (Scale.scale (1 / 2) direction)).trans (Fraction.Order.Basic.le_max_left _ _)

/-- The fixed depth-four dyadic scan used for the radicand majorant. -/
@[expose] public def radicandScanDepth : Nat := 4

section

open Purelib.Polynomial
open Purelib.Riemann.RootContinuation

/-- The square-root quadratic for the polynomial value at the original segment parameter.

The polynomial value is read at the original segment's affine point for the supplied rational parameter. The same value
determines the exact degree-two root polynomial. -/
@[expose] public def rootPolynomialAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) : GaussianPolynomial :=
  SquareRootReconditioning.rootPolynomial
    (polynomial.eval (segment.pointAt parameter))

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- Twice the sum of original displacement and starting-point squared norms, plus one.

Both original endpoint data determine the displacement and starting-point quadrances. Their displayed sum yields a
positive radius for the same segment. -/
@[expose] public def segmentPointRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  2 *
      (Data.Gaussian.Norm.Basic.normSq (finish - start) +
        Data.Gaussian.Norm.Basic.normSq start) +
    1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The retained segment-point radius is at least one. -/
public theorem one_le_segmentPointRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    (1 : Coordinate) <= segmentPointRadius segment := by
  unfold segmentPointRadius
  have doubledNonnegative :
      0 <= 2 *
        (Data.Gaussian.Norm.Basic.normSq (finish - start) +
          Data.Gaussian.Norm.Basic.normSq start) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (Norm.Basic.normSq_nonneg _)
        (Norm.Basic.normSq_nonneg _))
  exact le_add_of_nonneg_left doubledNonnegative

open Purelib.Polynomial in
/-- The retained segment-point radius is strictly positive. -/
public theorem segmentPointRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < segmentPointRadius segment :=
  (show (0 : Coordinate) < 1 by decide).trans_le
    (one_le_segmentPointRadius segment)

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The symmetric rational box at the original segment's retained point radius.

The four signed bounds use the same retained segment-point radius. Its positivity certifies the symmetric box without
changing the original segment. -/
@[expose] public def segmentPointAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Box :=
  Box.symmetric (segmentPointRadius segment)
    (segmentPointRadius_positive segment).le

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Every unit-interval point of the original segment lies in its retained symmetric box.

The original rational parameter lies between zero and one. The affine sample's coordinate squares are controlled by the
same retained endpoint quadrances. -/
public theorem segmentPointAmbient_contains
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    (segmentPointAmbient segment).Contains (segment.pointAt parameter) := by
  let point := segment.pointAt parameter
  let radius := segmentPointRadius segment
  have differenceBound :
      Data.Gaussian.Norm.Basic.normSq (point - start) <=
        Data.Gaussian.Norm.Basic.normSq (finish - start) := by
    simpa only [point, Geometry.ClearPath.ClearSegment.pointAt_zero, Geometry.ClearPath.ClearSegment.pointAt_one]
      using segment.normSq_pointAt_sub_zero_le_full parameter inside
  have decomposition : point = (point - start) + start := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  have pointLeBase : Data.Gaussian.Norm.Basic.normSq point <=
      2 *
        (Data.Gaussian.Norm.Basic.normSq (finish - start) +
          Data.Gaussian.Norm.Basic.normSq start) := by
    rw [decomposition]
    exact (Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add differenceBound le_rfl) (by decide))
  have pointLeRadius :
      Data.Gaussian.Norm.Basic.normSq point <= radius := by
    exact pointLeBase.trans (by
      dsimp only [radius, segmentPointRadius]
      exact le_add_of_nonneg_right (by decide))
  have radiusLeSquare : radius <= radius ^ 2 := by
    rw [pow_two]
    calc
      radius = radius * 1 := by ring1
      _ <= radius * radius :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (one_le_segmentPointRadius segment)
          (segmentPointRadius_positive segment).le
  exact Norm.Bounds.coordinate_bounds_of_normSq_le
    (segmentPointRadius_positive segment).le
    (pointLeRadius.trans radiusLeSquare)

section

open Purelib.Polynomial

/-- One plus the depth-four dyadic squared-norm majorant for the original segment polynomial.

The original segment endpoints determine the affine line and its depth-four dyadic scan. Adding one to that retained
majorant supplies the same positive bound for every segment parameter. -/
@[irreducible, expose] public def radicandNormBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  dyadicLineNormMajorant polynomial start (finish - start)
    radicandScanDepth + 1

/-- The retained radicand squared-norm bound is at least one. -/
public theorem one_le_radicandNormBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (_segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    (1 : Coordinate) <= radicandNormBound _segment := by
  unfold radicandNormBound
  exact le_add_of_nonneg_left
    (dyadicLineNormMajorant_nonneg polynomial start (finish - start)
      radicandScanDepth)

/-- The retained radicand squared-norm bound is strictly positive. -/
public theorem radicandNormBound_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < radicandNormBound segment :=
  (show (0 : Coordinate) < 1 by decide).trans_le
    (one_le_radicandNormBound segment)

end

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- Every original segment sample's polynomial value satisfies the retained radicand bound.

The unit-interval parameter selects a point on the original cleared segment. The fixed-depth dyadic scan bounds the
polynomial value at that same point. -/
public theorem eval_normSq_le_radicandNormBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    Data.Gaussian.Norm.Basic.normSq
        (polynomial.eval (segment.pointAt parameter)) <=
      radicandNormBound segment := by
  have evaluated := normSq_eval_line_le_dyadicLineNormMajorant polynomial
    start (finish - start) radicandScanDepth parameter inside
  have lineEqual : Affine.line start (finish - start) parameter =
      segment.pointAt parameter := by
    apply Basic.ext <;>
      simp only [Affine.line, Geometry.ClearPath.ClearSegment.pointAt,
        Cast.ofCoordinate_re,
        Cast.ofCoordinate_im,
        Scale.scale_re, Scale.scale_im,
        Basic.add_re,
        Basic.add_im,
        Basic.sub_re,
        Basic.sub_im,
        Basic.mul_re,
        Basic.mul_im] <;>
      ring1
  rw [lineEqual] at evaluated
  exact evaluated.trans (by
    unfold radicandNormBound
    exact le_add_of_nonneg_right (by decide))

section

open Purelib.Polynomial

/-- Twice the retained radicand squared-norm bound. -/
@[expose] public def rootSampleCoordinateRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  2 * radicandNormBound segment

/-- Twice the sum of one quarter and the retained radicand squared-norm bound. -/
@[expose] public def rootSampleNormSqMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  2 * ((1 / 4 : Coordinate) + radicandNormBound segment)

end

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The retained root-sample squared-norm majorant is strictly positive.

The radicand norm bound is at least one. Adding the fixed one-quarter residual allowance and doubling therefore gives a
strictly positive sample bound. -/
public theorem rootSampleNormSqMajorant_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < rootSampleNormSqMajorant segment :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (add_pos_of_pos_of_nonneg (by decide)
      (radicandNormBound_positive segment).le)

open Purelib.Polynomial in
/-- The retained root-sample coordinate radius plus one. -/
@[expose] public def rootAmbientRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  rootSampleCoordinateRadius segment + 1

section

open Purelib.Data.Rat
open Purelib.Polynomial

/-- The common root ambient radius is at least three. -/
public theorem three_le_rootAmbientRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    (3 : Coordinate) <= rootAmbientRadius segment := by
  unfold rootAmbientRadius rootSampleCoordinateRadius
  calc
    (3 : Coordinate) = 2 * 1 + 1 := by decide
    _ <= 2 * radicandNormBound segment + 1 := by
      exact add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (one_le_radicandNormBound segment)
          (show (0 : Coordinate) <= 2 by decide)) le_rfl

/-- The common root ambient radius is strictly positive. -/
public theorem rootAmbientRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < rootAmbientRadius segment :=
  add_pos_of_pos_of_nonneg
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (radicandNormBound_positive segment)) (by decide)

end

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The common symmetric root box for every parameter of the original cleared segment.

All four coordinates use the same positive root ambient radius. The box belongs to the original cleared segment and is
independent of its sampled parameter. -/
@[expose] public def rootAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Box :=
  Box.symmetric (rootAmbientRadius segment)
    (rootAmbientRadius_positive segment).le

open Purelib.Data.Rat in
/-- For a rational bound at least one, twice one plus the bound is at most twice-bound to the fourth power. -/
private theorem two_one_add_le_sampleRadius_four
    {bound : Coordinate} (oneLe : (1 : Coordinate) <= bound) :
    2 * (1 + bound) <= (2 * bound) ^ 4 := by
  have boundNonnegative : (0 : Coordinate) <= bound :=
    (by decide : (0 : Coordinate) <= 1).trans oneLe
  have boundLeSquare : bound <= bound ^ 2 := by
    rw [pow_two]
    calc
      bound = bound * 1 := by ring1
      _ <= bound * bound :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct oneLe
          boundNonnegative
  have oneLeSquare : (1 : Coordinate) <= bound ^ 2 :=
    oneLe.trans boundLeSquare
  have squareLeFourth : bound ^ 2 <= bound ^ 4 := by
    rw [show bound ^ 4 = bound ^ 2 * bound ^ 2 by ring1]
    calc
      bound ^ 2 = bound ^ 2 * 1 := by ring1
      _ <= bound ^ 2 * bound ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct oneLeSquare
          (Fraction.Order.Arithmetic.sq_nonneg_direct bound)
  have boundLeFourth := boundLeSquare.trans squareLeFourth
  have oneLeFourth := oneLeSquare.trans squareLeFourth
  calc
    2 * (1 + bound) <= 2 * (bound ^ 4 + bound ^ 4) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add oneLeFourth boundLeFourth) (by decide)
    _ <= 16 * bound ^ 4 := by
      have fourthNonnegative : (0 : Coordinate) <= bound ^ 4 :=
        Fraction.Order.Arithmetic.pow_nonneg_direct boundNonnegative 4
      calc
        2 * (bound ^ 4 + bound ^ 4) = 4 * bound ^ 4 := by ring1
        _ <= 16 * bound ^ 4 :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by decide) fourthNonnegative
    _ = (2 * bound) ^ 4 := by ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- Certify boundary clearance one for every parameter quadratic in the common root box.

The uniform radicand majorant and symmetric-box boundary norm bound force the squared residual to be at least one on all
four sides. -/
@[expose] public def rootAmbientClearance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    Boundary.Basic.BoundaryClearance
      (rootPolynomialAt segment parameter) (rootAmbient segment) where
  bound := 1
  positive := by decide
  lower := by
    intro z boundary
    let bound := radicandNormBound segment
    let radius := rootAmbientRadius segment
    let radicand := polynomial.eval (segment.pointAt parameter)
    have radicandBound :
        Data.Gaussian.Norm.Basic.normSq radicand <= bound :=
      eval_normSq_le_radicandNormBound segment parameter inside
    have radial := Box.Square.Symmetric.Norm.symmetric_boundary_norm_bounds
      (rootAmbientRadius_positive segment).le boundary
    have powerLower : radius ^ 4 <=
        Data.Gaussian.Norm.Basic.normSq (z ^ 2) := by
      rw [Power.normSq_pow]
      calc
        radius ^ 4 = (radius ^ 2) ^ 2 := by ring1
        _ <= Data.Gaussian.Norm.Basic.normSq z ^ 2 :=
          Fraction.Order.Arithmetic.pow_le_pow_direct
            (Fraction.Order.Arithmetic.sq_nonneg_direct radius) radial.1 2
    have split : z ^ 2 = (z ^ 2 - radicand) + radicand := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.add_re,
          Basic.add_im] <;> ring1
    have upper :=
      Norm.Bounds.normSq_add_le_two
        (z ^ 2 - radicand) radicand
    rw [← split] at upper
    have sampleRadiusLe : rootSampleCoordinateRadius segment <= radius := by
      dsimp only [radius, rootAmbientRadius]
      exact le_add_of_nonneg_right (by decide)
    have scalarLower : 2 * (1 + bound) <= radius ^ 4 := by
      have baseScalar : 2 * (1 + bound) <=
          rootSampleCoordinateRadius segment ^ 4 := by
        simpa only [rootSampleCoordinateRadius, bound] using
          two_one_add_le_sampleRadius_four
            (one_le_radicandNormBound segment)
      exact baseScalar.trans
        (Fraction.Order.Arithmetic.pow_le_pow_direct
          (by
            unfold rootSampleCoordinateRadius
            exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
              (radicandNormBound_positive segment).le)
          sampleRadiusLe 4)
    have combined :
        2 * (1 + bound) <=
          2 *
            (Data.Gaussian.Norm.Basic.normSq
                (z ^ 2 - radicand) +
              Data.Gaussian.Norm.Basic.normSq radicand) :=
      scalarLower.trans (powerLower.trans upper)
    have boundedRight :
        2 *
            (Data.Gaussian.Norm.Basic.normSq
                (z ^ 2 - radicand) +
              Data.Gaussian.Norm.Basic.normSq radicand) <=
          2 *
            (Data.Gaussian.Norm.Basic.normSq
                (z ^ 2 - radicand) + bound) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add le_rfl radicandBound) (by decide)
    have reduced := combined.trans boundedRight
    have withoutTwo :
        1 + bound <=
          Data.Gaussian.Norm.Basic.normSq
              (z ^ 2 - radicand) + bound := by
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        (c := 2) ?_ (show (0 : Coordinate) < 2 by decide)
      simpa only [Fraction.Field.mul_comm] using reduced
    have result : (1 : Coordinate) <=
        Data.Gaussian.Norm.Basic.normSq (z ^ 2 - radicand) := by
      exact Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
        (c := bound) withoutTwo
    simpa only [rootPolynomialAt,
      SquareRootReconditioning.rootPolynomial,
      Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
      SquareRootDegree.degreeTwo_value, radicand, Norm.Basic.normSq_eq_canonical] using result

open Purelib.Polynomial in
/-- The common root-box clearance certificate retains the exact bound one. -/
@[simp] public theorem rootAmbientClearance_bound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    (rootAmbientClearance segment parameter inside).bound = 1 := rfl

section

open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Power
open Purelib.Riemann.RootContinuation

/-- The parameter quadratic's squared Lipschitz bound is the maximum of one and sixteen times the common box norm bound.

The original quadratic and common root box determine the finite Lipschitz scan. Its displayed maximum depends on the
retained box quadrance bound, not the segment parameter. -/
public theorem rootLipschitz_formula
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) :
    Bounds.Box.denseLipschitzBound
        (rootPolynomialAt segment parameter) (rootAmbient segment) =
      max 1 (16 * (rootAmbient segment).normSqBound) := by
  unfold Bounds.Box.denseLipschitzBound
    Bounds.Box.denseEvalNormLipschitzBound
    Bounds.Box.denseHornerNormBounds
    rootPolynomialAt SquareRootReconditioning.rootPolynomial
    Gaussian.rootPolynomial
  simp only [SquareRootDegree.degreeTwo_value, Nat.reduceSub,
    List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append, Bounds.Horner.step,
    List.foldl_cons, List.foldl_nil,
    Norm.Basic.normSq_zero,
    Norm.Basic.normSq_one]
  congr 1
  ring1

/-- The exact quadratic Taylor remainder bound in the common root box is eight. -/
public theorem rootTaylor_formula
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) :
    Bounds.Box.Taylor.denseTaylorRemainderBound
        (rootPolynomialAt segment parameter) (rootAmbient segment) = 8 := by
  unfold Bounds.Box.Taylor.denseTaylorRemainderBound
    Bounds.Box.Taylor.denseEvalTaylorRemainderBound
    Bounds.Box.Taylor.denseHornerTaylorNormBounds
    rootPolynomialAt SquareRootReconditioning.rootPolynomial
    Gaussian.rootPolynomial
  simp only [SquareRootDegree.degreeTwo_value, Nat.reduceSub,
    List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append, Bounds.Taylor.HornerTaylorNormBounds.step,
    List.foldl_cons, List.foldl_nil,
    Norm.Basic.normSq_zero,
    Norm.Basic.normSq_one]
  calc
    max 1 _ = max 1 (8 : Coordinate) := by congr 1; ring1
    _ = 8 := by decide

end

section

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian

/-- The common-box evaluation majorant of the quadratic derivative at parameter zero.

The derivative of the original parameter-zero quadratic is evaluated with the common root box's retained finite
majorant. The same derivative bounds all segment parameters. -/
@[expose] public def rootDerivativeMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  Bounds.Box.denseEvalNormMajorant
    (GCD.derivative (rootPolynomialAt segment 0))
    (rootAmbient segment)

/-- The retained quadratic derivative majorant is strictly positive. -/
public theorem rootDerivativeMajorant_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < rootDerivativeMajorant segment :=
  Bounds.Box.denseEvalNormMajorant_pos _ _

end

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- Every segment parameter gives the same retained quadratic derivative majorant.

Every original parameter quadratic has the same linear derivative. The common root box therefore supplies exactly the
same finite evaluation majorant. -/
public theorem rootDerivativeMajorant_formula
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) :
    Bounds.Box.denseEvalNormMajorant
        (GCD.derivative
          (rootPolynomialAt segment parameter))
        (rootAmbient segment) =
      rootDerivativeMajorant segment := by
  unfold rootDerivativeMajorant rootPolynomialAt
    SquareRootReconditioning.rootPolynomial
  rw [Gaussian.derivative_polynomial_eq
    (polynomial.eval (segment.pointAt parameter))
    (polynomial.eval (segment.pointAt 0))
    SquareRootDegree.degreeTwo]

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- The quadratic derivative's squared norm at a point is four times that point's squared norm.

Differentiating the original quadratic gives twice the supplied Gaussian point. Its canonical squared norm is four times
that same point's squared norm. -/
public theorem rootDerivative_normSq_formula
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate) (point : Gaussian) :
    Data.Gaussian.Norm.Basic.normSq
        ((GCD.derivative
          (rootPolynomialAt segment parameter)).eval point) =
      4 * Data.Gaussian.Norm.Basic.normSq point := by
  unfold rootPolynomialAt
    SquareRootReconditioning.rootPolynomial
    Gaussian.rootPolynomial
    GCD.derivative Dense.Derivative.derivative
    Dense.Derivative.derivativeState
  simp only [SquareRootDegree.degreeTwo_value, Nat.reduceSub,
    List.replicate_succ, List.replicate_zero, List.nil_append,
    List.cons_append, List.foldl_cons, List.foldl_nil,
    Dense.Derivative.derivativeStep,
    Dense.Basic.DensePolynomial.normalize_constant_of_ne
      (by decide : (1 : Gaussian) ≠ 0),
    Dense.Basic.DensePolynomial.shift_zero,
    Dense.Basic.DensePolynomial.zero_add_normalize,
    Dense.Basic.DensePolynomial.normalize_zero,
    Dense.Basic.DensePolynomial.eval_add,
    Dense.Basic.DensePolynomial.eval_shift,
    Dense.Basic.DensePolynomial.eval_constant, pow_one]
  simp only [one_mul, add_zero]
  unfold Data.Gaussian.Norm.Basic.normSq
  simp only [Basic.add_re,
    Basic.add_im]
  ring1

open Purelib.Polynomial in
/-- The common quadratic squared Lipschitz bound, independent of the segment parameter.

The same parameter-zero quadratic and common root ambient determine this finite majorant. The quadratic's fixed
nonconstant coefficients make it uniform in the original segment parameter. -/
@[expose] public def rootLipschitz
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  max 1 (16 * (rootAmbient segment).normSqBound)

open Purelib.Polynomial in
open Purelib.Data.Rat in
/-- The retained common squared Lipschitz bound is strictly positive. -/
public theorem rootLipschitz_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < rootLipschitz segment :=
  (show (0 : Coordinate) < 1 by decide).trans_le (Fraction.Order.Basic.le_max_left _ _)

open Purelib.Polynomial in
/-- The smaller of one and the reciprocal of four times the common squared Lipschitz bound.

The common squared Lipschitz bound is positive. Its positive reciprocal and the unit cap determine the retained minimum
radius. -/
@[expose] public def rootInteriorRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  min 1 (1 / (4 * rootLipschitz segment))

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The common residual interior radius is strictly positive.

Both entries of the original minimum are strictly positive: the unit cap and the reciprocal of four times the positive
retained Lipschitz bound. -/
public theorem rootInteriorRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < rootInteriorRadius segment :=
  Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (rootLipschitz_positive segment)))

open Purelib.Polynomial in
open Purelib.Polynomial.Clearance.Box in
/-- Every parameter's root-box clearance has exactly the retained common interior radius.

The original root-box clearance retains bound one and the same parameter-independent Lipschitz value. Its displayed
residual-interior formula consequently uses the retained common radius. -/
public theorem rootAmbient_residualInteriorRadius_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :
    (rootAmbientClearance segment parameter inside).residualInteriorRadius =
      rootInteriorRadius segment := by
  unfold Boundary.Basic.BoundaryClearance.residualInteriorRadius
    rootInteriorRadius rootLipschitz
  rw [rootAmbientClearance_bound,
    rootLipschitz_formula segment parameter]

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Choose a uniform radius capped by one eighth, the derivative margin and the requested diameter.

The two quantitative caps use exact dyadic square radii. The same radius applies to every parameter and root owner on
the original segment. -/
@[expose] public def preparationRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) : Coordinate :=
  min (1 / 8 : Coordinate)
    (min
      (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius
        (ClearSheetContinuation.squareRootDerivativeMargin
            segment / (72 * 8)))
      (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius (rootDiameter / 8)))

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
open Purelib.Data.Rat in
/-- The retained uniform preparation radius is strictly positive for a positive diameter target.

A positive diameter request and the original segment's positive derivative margin make every retained radius cap
positive. Their original nested minimum is therefore positive. -/
public theorem preparationRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {rootDiameter : Coordinate} (_rootDiameterPositive : 0 < rootDiameter) :
    0 < preparationRadius segment rootDiameter := by
  unfold preparationRadius
  exact Fraction.Order.Basic.lt_min
    (by decide)
    (Fraction.Order.Basic.lt_min
      (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive _)
      (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive _))

open Purelib.Polynomial in
/-- Four times the retained root-sample squared-norm majorant. -/
@[expose] public def rootSampleDerivativeMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  4 * rootSampleNormSqMajorant segment

section

open Purelib.Data.Rat
open Purelib.Polynomial

/-- The root-sample derivative majorant is at least ten. -/
public theorem ten_le_rootSampleDerivativeMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    (10 : Coordinate) <= rootSampleDerivativeMajorant segment := by
  unfold rootSampleDerivativeMajorant rootSampleNormSqMajorant
  calc
    (10 : Coordinate) = 4 * (2 * ((1 / 4 : Coordinate) + 1)) := by
      decide
    _ <= 4 * (2 * ((1 / 4 : Coordinate) + radicandNormBound segment)) := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      · apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        · exact add_le_add_right (one_le_radicandNormBound segment) (1 / 4)
        · decide
      · decide

/-- The root-sample derivative majorant is strictly positive. -/
public theorem rootSampleDerivativeMajorant_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < rootSampleDerivativeMajorant segment :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (rootSampleNormSqMajorant_positive segment)

end

open Purelib.Polynomial in
/-- Twice the retained sample derivative majorant times the uniform preparation radius squared. -/
@[expose] public def linearizationMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) : Coordinate :=
  2 * rootSampleDerivativeMajorant segment *
    preparationRadius segment rootDiameter ^ 2

section

open Purelib.Data.Rat
open Purelib.Polynomial

/-- Twenty times the preparation radius squared is at most the retained linearization majorant.

The retained sample derivative majorant is at least ten. Doubling its product with the same nonnegative radius square
gives the displayed lower bound. -/
public theorem twenty_mul_preparationRadius_sq_le_linearizationMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) :
    20 * preparationRadius segment rootDiameter ^ 2 <=
      linearizationMajorant segment rootDiameter := by
  unfold linearizationMajorant
  have doubled : (2 : Coordinate) * 10 <=
      2 * rootSampleDerivativeMajorant segment :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (ten_le_rootSampleDerivativeMajorant segment) (by decide)
  have twentyLe : (20 : Coordinate) <=
      2 * rootSampleDerivativeMajorant segment := by
    calc
      (20 : Coordinate) = 2 * 10 := by decide
      _ <= 2 * rootSampleDerivativeMajorant segment := doubled
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct twentyLe
    (Fraction.Order.Arithmetic.sq_nonneg_direct
      (preparationRadius segment rootDiameter))

/-- The retained linearization majorant is strictly positive for a positive diameter target.

The original sample derivative majorant is positive and the positive diameter request gives a positive preparation
radius. Their retained product is strictly positive. -/
public theorem linearizationMajorant_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < linearizationMajorant segment rootDiameter :=
  Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (rootSampleDerivativeMajorant_positive segment))
    (Fraction.Order.Arithmetic.pow_pos_direct
      (preparationRadius_positive segment rootDiameterPositive) 2)

end

open Purelib.Polynomial in
open Purelib.Data.Rat in
/-- The uniform preparation radius is at most one eighth. -/
public theorem preparationRadius_le_oneEighth
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) :
    preparationRadius segment rootDiameter <= 1 / 8 :=
  Fraction.Order.Basic.min_le_left _ _

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The preparation radius squared is below the derivative margin divided by seventy-two times eight.

The positive diameter request retains the original dyadic Taylor-radius cap. Its certified square is strictly below the
original positive derivative-margin ratio. -/
public theorem preparationRadius_sq_lt_taylorRatio
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    preparationRadius segment rootDiameter ^ 2 <
      ClearSheetContinuation.squareRootDerivativeMargin segment /
        (72 * 8) := by
  let target :=
    ClearSheetContinuation.squareRootDerivativeMargin segment /
      (72 * 8)
  let selected := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius target
  have radiusPositive :=
    preparationRadius_positive segment rootDiameterPositive
  have radiusLe : preparationRadius segment rootDiameter <= selected :=
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  have squareLe : preparationRadius segment rootDiameter ^ 2 <=
      selected ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le radiusLe 2
  have denominatorPositive : (0 : Coordinate) < 72 * 8 :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct (n := 8) (by decide))
  have targetPositive : 0 < target :=
    Fraction.Order.Field.div_pos_direct
      (ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment) denominatorPositive
  exact squareLe.trans_lt
    (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt targetPositive)

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- Eight times the uniform derivative-margin to Taylor-coefficient ratio.

The original positive derivative margin and fixed quadratic Taylor coefficient determine the displayed ratio. The finite
scale factor retains the same segment data. -/
@[expose] public def derivativeDiameterBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  8 *
    (ClearSheetContinuation.squareRootDerivativeMargin segment /
      (72 * 8))

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The retained derivative-controlled diameter bound is strictly positive.

The original derivative margin is positive, and the fixed Taylor denominator is positive. Their displayed scaled
quotient is therefore strictly positive. -/
public theorem derivativeDiameterBound_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < derivativeDiameterBound segment :=
  Fraction.Order.Arithmetic.mul_pos_direct (by decide)
    (Fraction.Order.Field.div_pos_direct
      (ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment)
      (Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide))
        (Fraction.Cast.Order.natCast_pos_direct (n := 8) (by decide))))

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
open Purelib.Data.Rat in
/-- The uniform preparation radius is at most the dyadic square radius of one eighth of the requested diameter. -/
public theorem preparationRadius_le_diameterCap
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) :
    preparationRadius segment rootDiameter <=
      SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius (rootDiameter / 8) :=
  (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)

open Purelib.Polynomial in
/-- The uniform preparation radius is at most one. -/
public theorem preparationRadius_le_one
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) :
    preparationRadius segment rootDiameter <= 1 := by
  exact (preparationRadius_le_oneEighth segment rootDiameter).trans (by decide)

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- Every parameter quadratic satisfies the Taylor remainder bound at the uniform preparation radius.

The uniform preparation radius retains its derivative-margin ratio cap. The original parameter quadratic has Taylor
coefficient eight, giving the same doubled remainder budget at every parameter. -/
public theorem preparation_taylorSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    2 *
        (36 *
          Bounds.Box.Taylor.denseTaylorRemainderBound
            (rootPolynomialAt segment parameter) (rootAmbient segment) *
          preparationRadius segment rootDiameter ^ 2) <=
      ClearSheetContinuation.squareRootDerivativeMargin
        segment := by
  let radius := preparationRadius segment rootDiameter
  let margin :=
    ClearSheetContinuation.squareRootDerivativeMargin segment
  have denominatorPositive : (0 : Coordinate) < 72 * 8 :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct (n := 8) (by decide))
  have scaled : radius ^ 2 * (72 * 8) <= margin :=
    (Fraction.Order.Field.le_div_iff_pos denominatorPositive).mp
      (preparationRadius_sq_lt_taylorRatio segment rootDiameterPositive).le
  rw [rootTaylor_formula segment parameter]
  calc
    2 * (36 * 8 * radius ^ 2) = (72 * 8) * radius ^ 2 := by ring1
    _ = radius ^ 2 * (72 * 8) := by ring1
    _ <= margin := scaled

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Twice the uniform preparation radius is strictly below one.

The retained preparation radius is at most one eighth. Doubling that same bound leaves a strict margin below the unit
radius. -/
public theorem two_preparationRadius_lt_one
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {rootDiameter : Coordinate} (_rootDiameterPositive : 0 < rootDiameter) :
    2 * preparationRadius segment rootDiameter < 1 := by
  let radius := preparationRadius segment rootDiameter
  have radiusLe : radius <= 1 / 8 :=
    preparationRadius_le_oneEighth segment rootDiameter
  calc
    2 * radius <= 2 * (1 / 8 : Coordinate) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusLe
        (by decide)
    _ < 1 := by decide

/-! ## A common inherited-occurrence bridge -/

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- Choose an owner-specific radius satisfying interior, preparation, residual and Taylor caps.

The common preparation radius is retained separately; the local quadratic Lipschitz and Taylor bounds are evaluated on
the original owner's box. -/
@[expose] public def bridgeRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Coordinate :=
  let p := rootPolynomialAt segment parameter
  let ownerBox := owner.track.initial.box
  min ((3 / 8 : Coordinate) *
      owner.track.initial.clearance.residualInteriorRadius)
    (min ((1 / 4 : Coordinate) * preparationRadius segment rootDiameter)
      (min
        (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius
          (ClearSheetContinuation.squareRootDerivativeThreshold
              segment /
            (2 * Bounds.Box.denseLipschitzBound p ownerBox)))
        (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius
          (ClearSheetContinuation.squareRootDerivativeMargin
              segment /
            (72 * Bounds.Box.Taylor.denseTaylorRemainderBound
              p ownerBox)))))

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The retained owner-specific bridge radius is strictly positive for a positive diameter target.

The diameter request, uniform preparation radius, original owner interior radius and retained derivative budgets are
positive. Each original bridge-radius cap is therefore positive. -/
public theorem bridgeRadius_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < bridgeRadius segment owner rootDiameter :=
  Fraction.Order.Basic.lt_min
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      owner.track.initial.clearance.residualInteriorRadius_pos)
    (Fraction.Order.Basic.lt_min
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
        (preparationRadius_positive segment rootDiameterPositive))
      (Fraction.Order.Basic.lt_min
        (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive _)
        (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive _)))

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The owner-specific bridge radius is at most the uniform preparation radius. -/
public theorem bridgeRadius_le_preparation
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    bridgeRadius segment owner rootDiameter <=
      preparationRadius segment rootDiameter := by
  have preparationNonnegative :=
    (preparationRadius_positive segment rootDiameterPositive).le
  exact ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)).trans
    (by
      calc
        (1 / 4 : Coordinate) * preparationRadius segment rootDiameter <=
            1 * preparationRadius segment rootDiameter :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (by decide) preparationNonnegative
        _ = preparationRadius segment rootDiameter := by ring1)

open Purelib.Polynomial in
open Purelib.Data.Rat in
/-- The bridge radius is at most three eighths of the original owner's residual interior radius. -/
public theorem bridgeRadius_le_ownerInteriorScale
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    bridgeRadius segment owner rootDiameter <=
      (3 / 8 : Coordinate) *
        owner.track.initial.clearance.residualInteriorRadius :=
  Fraction.Order.Basic.min_le_left _ _

section

open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.Branches

/-- The original owner's Lipschitz bound at the bridge radius satisfies the retained derivative threshold.

The same owner-specific bridge radius retains its source-budget cap. The original owner's squared Lipschitz value and
derivative threshold bound the actual source variation. -/
public theorem bridge_sourceThreshold
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Bounds.Box.denseLipschitzBound
        (rootPolynomialAt segment parameter) owner.track.initial.box *
        (2 * bridgeRadius segment owner rootDiameter ^ 2) <=
      ClearSheetContinuation.squareRootDerivativeThreshold
        segment := by
  let p := rootPolynomialAt segment parameter
  let ownerBox := owner.track.initial.box
  let radius := bridgeRadius segment owner rootDiameter
  let lipschitz := Bounds.Box.denseLipschitzBound p ownerBox
  let threshold :=
    ClearSheetContinuation.squareRootDerivativeThreshold segment
  have radiusPositive : 0 < radius :=
    bridgeRadius_positive segment owner rootDiameterPositive
  let selected := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius
    (threshold / (2 * lipschitz))
  have radiusLeSelected : radius <= selected :=
    (Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
  have denominatorPositive : 0 < 2 * lipschitz :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Bounds.Box.denseLipschitzBound_pos p ownerBox)
  have targetPositive : 0 < threshold / (2 * lipschitz) :=
    Fraction.Order.Field.div_pos_direct
      (ClearSheetContinuation.squareRootDerivativeThreshold_positive
        segment) denominatorPositive
  have squareLeTarget : radius ^ 2 <= threshold / (2 * lipschitz) :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
      radiusLeSelected 2).trans
        (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt targetPositive).le
  have scaled : radius ^ 2 * (2 * lipschitz) <= threshold :=
    (Fraction.Order.Field.le_div_iff_pos denominatorPositive).mp
      squareLeTarget
  change lipschitz * (2 * radius ^ 2) <= threshold
  calc
    lipschitz * (2 * radius ^ 2) = (2 * lipschitz) * radius ^ 2 := by ring1
    _ = radius ^ 2 * (2 * lipschitz) := by ring1
    _ <= threshold := scaled

/-- The original owner's Taylor remainder at the bridge radius satisfies the retained derivative margin.

The bridge radius retains its original Taylor-budget cap. The same original owner's finite Taylor bound fits within the
retained uniform derivative margin. -/
public theorem bridge_taylorSmall
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    2 *
        (36 *
          Bounds.Box.Taylor.denseTaylorRemainderBound
            (rootPolynomialAt segment parameter) owner.track.initial.box *
          bridgeRadius segment owner rootDiameter ^ 2) <=
      ClearSheetContinuation.squareRootDerivativeMargin
        segment := by
  let p := rootPolynomialAt segment parameter
  let ownerBox := owner.track.initial.box
  let radius := bridgeRadius segment owner rootDiameter
  let taylor := Bounds.Box.Taylor.denseTaylorRemainderBound p ownerBox
  let margin :=
    ClearSheetContinuation.squareRootDerivativeMargin segment
  have radiusPositive : 0 < radius :=
    bridgeRadius_positive segment owner rootDiameterPositive
  let selected := SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius
    (margin / (72 * taylor))
  have radiusLeSelected : radius <= selected :=
    (Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _))
  have denominatorPositive : 0 < 72 * taylor :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 72) (by decide))
      (Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ownerBox)
  have targetPositive : 0 < margin / (72 * taylor) :=
    Fraction.Order.Field.div_pos_direct
      (ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment) denominatorPositive
  have squareLeTarget : radius ^ 2 <= margin / (72 * taylor) :=
    (Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
      radiusLeSelected 2).trans
        (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt targetPositive).le
  have scaled : radius ^ 2 * (72 * taylor) <= margin :=
    (Fraction.Order.Field.le_div_iff_pos denominatorPositive).mp
      squareLeTarget
  change 2 * (36 * taylor * radius ^ 2) <= margin
  calc
    2 * (36 * taylor * radius ^ 2) = (72 * taylor) * radius ^ 2 := by ring1
    _ = radius ^ 2 * (72 * taylor) := by ring1
    _ <= margin := scaled

end

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- Combine uniform and owner-specific residual limits for the common preparation and bridge.

The same sample must satisfy the quarter and derivative thresholds, both source bounds, both displacement bounds and the
original owner's quarter-clearance limit. -/
@[expose] public def sampleResidualTarget
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Coordinate :=
  let radius := preparationRadius segment rootDiameter
  let bridge := bridgeRadius segment owner rootDiameter
  let p := rootPolynomialAt segment parameter
  let ownerLipschitz := Bounds.Box.denseLipschitzBound p
    owner.track.initial.box
  let margin :=
    ClearSheetContinuation.squareRootDerivativeMargin segment
  min
    (min (1 / 4 : Coordinate)
      (ClearSheetContinuation.squareRootDerivativeThreshold
        segment))
    (min (rootLipschitz segment * (2 * radius ^ 2))
      (min (margin * radius ^ 2)
        (min (ownerLipschitz * (2 * bridge ^ 2))
          (min (margin * bridge ^ 2)
            (owner.track.initial.clearance.bound / 4)))))

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
/-- Every retained sampling threshold is positive for a positive diameter target.

The positive diameter request and original owner's positive clearance, Lipschitz and derivative budgets make every
retained sampling cap positive. Their original nested minimum keeps that positivity. -/
public theorem sampleResidualTarget_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    0 < sampleResidualTarget segment owner rootDiameter := by
  let radius := preparationRadius segment rootDiameter
  let bridge := bridgeRadius segment owner rootDiameter
  let p := rootPolynomialAt segment parameter
  let ownerLipschitz := Bounds.Box.denseLipschitzBound p
    owner.track.initial.box
  let margin :=
    ClearSheetContinuation.squareRootDerivativeMargin segment
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment rootDiameterPositive
  have bridgePositive : 0 < bridge :=
    bridgeRadius_positive segment owner rootDiameterPositive
  have marginPositive : 0 < margin :=
    ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment
  unfold sampleResidualTarget
  exact Fraction.Order.Basic.lt_min
    (Fraction.Order.Basic.lt_min (by decide)
      (ClearSheetContinuation.squareRootDerivativeThreshold_positive
        segment))
    (Fraction.Order.Basic.lt_min
      (Fraction.Order.Arithmetic.mul_pos_direct
        (rootLipschitz_positive segment)
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
          (Fraction.Order.Arithmetic.pow_pos_direct radiusPositive 2)))
      (Fraction.Order.Basic.lt_min
        (Fraction.Order.Arithmetic.mul_pos_direct marginPositive
          (Fraction.Order.Arithmetic.pow_pos_direct radiusPositive 2))
        (Fraction.Order.Basic.lt_min
          (Fraction.Order.Arithmetic.mul_pos_direct
            (Bounds.Box.denseLipschitzBound_pos _ _)
            (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
              (Fraction.Order.Arithmetic.pow_pos_direct bridgePositive 2)))
          (Fraction.Order.Basic.lt_min
            (Fraction.Order.Arithmetic.mul_pos_direct marginPositive
              (Fraction.Order.Arithmetic.pow_pos_direct bridgePositive 2))
            (Fraction.Order.Field.div_pos_direct
              owner.track.initial.clearance.positive (by decide))))))

open Purelib.Approximation.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Search the original track's geometric residual scale for the exact combined threshold.

The original owner's track and positive combined sampling threshold determine the finite geometric search. The returned
natural index belongs to that same retained track. -/
@[expose] public def sampleIndex
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Nat :=
  Geometric.Search.firstQuarterBelow
    (CoherentRoot.residualScale
      (rootPolynomialAt segment parameter) owner.ambient owner.track)
    0 (sampleResidualTarget segment owner rootDiameter)

open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- Read the original track's sample at the retained residual search index.

The sample is read from the original owner's refinement track at the computed residual index. The same retained track
determines both the selected box and the point read from it. -/
@[expose] public def trackSample
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Gaussian :=
  (CoherentRoot.approximation owner.track).sample
    (sampleIndex segment owner rootDiameter)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- The fallback track sample meets the combined residual threshold.

The retained geometric search index satisfies the exact positive combined sampling threshold. The original track's
residual estimate controls the sample at that index. -/
public theorem trackSample_residual_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (trackSample segment owner rootDiameter)) <
      sampleResidualTarget segment owner rootDiameter :=
  (CoherentRoot.sample_residual_le owner.track (by
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]
    exact SquareRootDegree.degreeTwo.positive)
      (sampleIndex segment owner rootDiameter)).trans_lt
    (Geometric.Search.firstQuarterBelow_accurate
      (CoherentRoot.residualScale
        (rootPolynomialAt segment parameter) owner.ambient owner.track)
      (CoherentRoot.residualScale_nonneg
        (rootPolynomialAt segment parameter) owner.ambient owner.track)
      0 (sampleResidualTarget segment owner rootDiameter)
      (sampleResidualTarget_positive segment owner rootDiameterPositive))

open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- The fallback track sample stays in the original owner's initial box.

The retained track's nesting relates the indexed sample box to its original initial box. The sample remains inside that
same original owner. -/
public theorem trackSample_inside_owner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    owner.track.initial.box.Contains
      (trackSample segment owner rootDiameter) := by
  rw [trackSample, CoherentRoot.approximation_sample]
  exact (CoherentRoot.state_refines_of_le owner.track
    (Nat.zero_le _)).contains
      (CoherentRoot.state owner.track
        (sampleIndex segment owner rootDiameter)).box.contains_anchor

/-- The coordinatewise rational midpoint of the retained box. -/
@[expose] public def ownerMidpoint (box : Box) : Gaussian :=
  { re := (box.xLower + box.xUpper) / 2
    im := (box.yLower + box.yUpper) / 2 }

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- A candidate lies in the original owner's box and meets the exact residual threshold.

Both conjuncts concern the same supplied candidate and original owner: box containment and the displayed squared
residual threshold. The predicate retains the candidate in both comparisons. -/
@[expose] public def SampleAcceptable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (point : Gaussian) : Prop :=
  owner.track.initial.box.Contains point ∧
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval point) <
      sampleResidualTarget segment owner rootDiameter

open Purelib.Polynomial in
/-- Decide the exact original-box containment and rational residual comparisons for a candidate.

The original rational and Gaussian decision procedures check containment and residual comparisons for the same
candidate. The instance retains their exact executable conjunction decision. -/
public instance sampleAcceptableDecidable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    DecidablePred (SampleAcceptable segment owner rootDiameter) :=
  fun point => by
    unfold SampleAcceptable
    infer_instance

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Try the retained eight-step checked Newton search on the target-dependent rational grid.

The original box midpoint seeds the finite search. Any returned candidate carries exact owner containment and residual
certificates; failure leaves fallback sampling available. -/
@[expose] public def sampleCandidates
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    Option {point : Gaussian // SampleAcceptable segment owner rootDiameter point} :=
  let target := sampleResidualTarget segment owner rootDiameter
  let root := rootPolynomialAt segment parameter
  let box := owner.track.initial.box
  letI : DecidablePred (SampleAcceptable segment owner rootDiameter) :=
    fun point => (inferInstance : Decidable
      (box.Contains point ∧ Data.Gaussian.Norm.Basic.normSq
        (root.eval point) < target))
  SquareRoot.Newton.Search.search (polynomial.eval (segment.pointAt parameter))
    (SampleAcceptable segment owner rootDiameter) 8
    (SquareRoot.Radius.Dyadic.CheckedSquareRootNewton.gridFor target) (ownerMidpoint box)

section

open Purelib.Polynomial

/-- Use the certified checked-Newton candidate when available, otherwise retain the original track sample.

The original ordered finite checked candidates are tested against the same containment and residual predicate. If none
is acceptable, the original track sample supplies the retained certified fallback. -/
@[expose] public def sample
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) : Gaussian :=
  match sampleCandidates segment owner rootDiameter with
  | some accepted => accepted.val
  | none => trackSample segment owner rootDiameter

/-- The selected sample satisfies both original-owner containment and the combined residual threshold.

A successful candidate check supplies the exact original containment and residual evidence. The fallback track sample
satisfies those same conditions at its retained search index. -/
public theorem sample_acceptable
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    SampleAcceptable segment owner rootDiameter
      (sample segment owner rootDiameter) := by
  unfold sample
  split
  · exact ‹{point : Gaussian // SampleAcceptable segment owner rootDiameter point}›.property
  · exact ⟨trackSample_inside_owner segment owner rootDiameter,
      trackSample_residual_lt segment owner rootDiameterPositive⟩

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
/-- The selected sample's squared residual is strictly below the combined threshold. -/
public theorem sample_residual_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <
      sampleResidualTarget segment owner rootDiameter :=
  (sample_acceptable segment owner rootDiameterPositive).2

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Data.Rat in
/-- The selected sample's squared residual is strictly below one quarter. -/
public theorem sample_residual_lt_quarter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) < 1 / 4 :=
  (sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_left _ _))

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Data.Rat in
/-- The selected residual is at most the uniform derivative-separation threshold. -/
public theorem sample_residual_le_uniformThreshold
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      ClearSheetContinuation.squareRootDerivativeThreshold
        segment :=
  ((sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_left _ _).trans (Fraction.Order.Basic.min_le_right _ _))).le

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Data.Rat in
/-- The selected residual satisfies the uniform preparation source bound.

The combined retained threshold includes the uniform source-variation budget. The exact selected sample and preparation
radius satisfy that same original budget. -/
public theorem sample_residual_le_uniformSource
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      rootLipschitz segment *
        (2 * preparationRadius segment rootDiameter ^ 2) :=
  ((sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))).le

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Data.Rat in
/-- The selected residual satisfies the uniform preparation displacement bound.

The combined retained threshold includes the derivative-margin-scaled displacement budget. The selected sample's actual
squared residual fits the same preparation radius. -/
public theorem sample_residual_le_uniformDisplacement
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      ClearSheetContinuation.squareRootDerivativeMargin segment *
        preparationRadius segment rootDiameter ^ 2 :=
  ((sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))).le

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Data.Rat in
/-- The selected residual satisfies the original owner's bridge source bound.

The combined threshold retains the original owner's bridge source cap. The same selected residual satisfies that owner's
finite Lipschitz budget at the retained bridge radius. -/
public theorem sample_residual_le_bridgeSource
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      Bounds.Box.denseLipschitzBound
          (rootPolynomialAt segment parameter) owner.track.initial.box *
        (2 * bridgeRadius segment owner rootDiameter ^ 2) :=
  ((sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))))).le

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
open Purelib.Data.Rat in
/-- The selected residual satisfies the bridge displacement bound.

The combined threshold retains the derivative-margin-scaled bridge cap. The actual selected residual fits the same
owner-specific bridge radius. -/
public theorem sample_residual_le_bridgeDisplacement
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      ClearSheetContinuation.squareRootDerivativeMargin segment *
        bridgeRadius segment owner rootDiameter ^ 2 :=
  ((sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))))).le

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Data.Rat in
/-- The selected residual is below one quarter of the original owner's clearance. -/
public theorem sample_residual_lt_ownerQuarter
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <
      owner.track.initial.clearance.bound / 4 :=
  (sample_residual_lt segment owner rootDiameterPositive).trans_le
    ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans
        ((Fraction.Order.Basic.min_le_right _ _).trans
          ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)))))

open Purelib.Polynomial in
/-- The selected sample stays in the exact original owner's initial box. -/
public theorem sample_inside_owner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    owner.track.initial.box.Contains (sample segment owner rootDiameter) := by
  unfold sample
  split
  · exact ‹{point : Gaussian // SampleAcceptable segment owner rootDiameter point}›.property.1
  · exact trackSample_inside_owner segment owner rootDiameter

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Power in
open Purelib.Riemann.RootContinuation in
/-- The selected sample satisfies the retained uniform squared-norm majorant.

Its quarter-residual certificate and the original radicand majorant bound the squared norm of its square, then give the
stated scalar bound. -/
public theorem sample_normSq_le_rootSampleNormSqMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        (sample segment owner rootDiameter) <=
      rootSampleNormSqMajorant segment := by
  let point := sample segment owner rootDiameter
  let radicand := polynomial.eval (segment.pointAt parameter)
  let bound := radicandNormBound segment
  let residual := (rootPolynomialAt segment parameter).eval point
  have radicandBound :
      Data.Gaussian.Norm.Basic.normSq radicand <= bound :=
    eval_normSq_le_radicandNormBound segment parameter inside
  have residualBound :
      Data.Gaussian.Norm.Basic.normSq residual <= 1 / 4 :=
    (sample_residual_lt_quarter segment owner rootDiameterPositive).le
  have powerIdentity : point ^ 2 = residual + radicand := by
    dsimp only [residual, rootPolynomialAt,
      SquareRootReconditioning.rootPolynomial]
    rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_eval,
      SquareRootDegree.degreeTwo_value]
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  have pointSquareBound :
      Data.Gaussian.Norm.Basic.normSq point ^ 2 <=
        2 * ((1 / 4 : Coordinate) + bound) := by
    rw [← Power.normSq_pow point 2,
      powerIdentity]
    exact (Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add residualBound radicandBound) (by decide))
  have oneLeMajorant : (1 : Coordinate) <=
      2 * ((1 / 4 : Coordinate) + bound) := by
    calc
      1 <= 2 * ((1 / 4 : Coordinate) + 1) := by decide
      _ <= 2 * ((1 / 4 : Coordinate) + bound) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add le_rfl (one_le_radicandNormBound segment)) (by decide)
  let pointNorm := Data.Gaussian.Norm.Basic.normSq point
  have pointNormBound : pointNorm <=
      2 * ((1 / 4 : Coordinate) + bound) := by
    by_cases atMostOne : pointNorm <= 1
    · exact atMostOne.trans oneLeMajorant
    · have oneLePoint : (1 : Coordinate) <= pointNorm :=
        (Fraction.Order.Arithmetic.lt_of_not_ge_direct atMostOne).le
      have pointLeSquare : pointNorm <= pointNorm ^ 2 := by
        rw [pow_two]
        calc
          pointNorm = pointNorm * 1 := by ring1
          _ <= pointNorm * pointNorm :=
            Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
              oneLePoint
              (Norm.Basic.normSq_nonneg point)
      exact pointLeSquare.trans pointSquareBound
  simpa only [pointNorm, point, bound, rootSampleNormSqMajorant] using
    pointNormBound

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The derivative at the selected sample satisfies the retained uniform sample derivative majorant.

The retained selected sample's quadrance bound and the exact quadratic derivative formula give the original uniform
sample derivative majorant. -/
public theorem sample_rootDerivative_le_rootSampleDerivativeMajorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((GCD.derivative
          (rootPolynomialAt segment parameter)).eval
            (sample segment owner rootDiameter)) <=
      rootSampleDerivativeMajorant segment := by
  rw [rootDerivative_normSq_formula]
  unfold rootSampleDerivativeMajorant
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (sample_normSq_le_rootSampleNormSqMajorant segment parameter inside owner
      rootDiameterPositive) (by decide)

section

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial

/-- The selected sample's squared norm is at most the common coordinate radius squared.

The exact selected residual and retained radicand bound control the sample quadrance. Their original coordinate-radius
formula yields the displayed square bound. -/
public theorem sample_normSq_le_rootSampleCoordinateRadius_sq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    Data.Gaussian.Norm.Basic.normSq
        (sample segment owner rootDiameter) <=
      rootSampleCoordinateRadius segment ^ 2 := by
  let bound := radicandNormBound segment
  let radius := rootSampleCoordinateRadius segment
  have boundLeSquare : bound <= bound ^ 2 := by
    have oneLe := one_le_radicandNormBound segment
    have nonnegative : (0 : Coordinate) <= bound :=
      (by decide : (0 : Coordinate) <= 1).trans oneLe
    rw [pow_two]
    calc
      bound = bound * 1 := by ring1
      _ <= bound * bound :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct oneLe
          nonnegative
  have scalarBound :
      rootSampleNormSqMajorant segment <= radius ^ 2 := by
    have quarterLeBound : (1 / 4 : Coordinate) <= bound :=
      (by decide : (1 / 4 : Coordinate) <= 1).trans
        (one_le_radicandNormBound segment)
    dsimp only [rootSampleNormSqMajorant]
    change 2 * ((1 / 4 : Coordinate) + bound) <= radius ^ 2
    calc
      2 * ((1 / 4 : Coordinate) + bound) <= 2 * (bound + bound) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add quarterLeBound le_rfl) (by decide)
      _ = 4 * bound := by ring1
      _ <= 4 * bound ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          boundLeSquare (by decide)
      _ = radius ^ 2 := by
        dsimp only [radius, rootSampleCoordinateRadius]
        ring1
  exact (sample_normSq_le_rootSampleNormSqMajorant segment parameter inside
    owner rootDiameterPositive).trans scalarBound

/-- Both selected-sample coordinates lie between the signed common coordinate-radius bounds.

Each coordinate square is bounded by the same actual sample quadrance. The positive retained coordinate radius supplies
both signed endpoint bounds. -/
public theorem sample_rootSampleCoordinateBounds
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    -rootSampleCoordinateRadius segment <=
        (sample segment owner rootDiameter).re ∧
      (sample segment owner rootDiameter).re <=
        rootSampleCoordinateRadius segment ∧
      -rootSampleCoordinateRadius segment <=
        (sample segment owner rootDiameter).im ∧
      (sample segment owner rootDiameter).im <=
        rootSampleCoordinateRadius segment := by
  exact Norm.Bounds.coordinate_bounds_of_normSq_le
    (by
      unfold rootSampleCoordinateRadius
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (radicandNormBound_positive segment).le)
    (sample_normSq_le_rootSampleCoordinateRadius_sq segment parameter inside
      owner rootDiameterPositive)

end

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The selected sample lies in the same common root box for every segment parameter.

The retained signed coordinate bounds lie strictly within the same common ambient radius. Both real and imaginary
coordinates of the original selected sample therefore belong to that box. -/
public theorem sample_inside_rootAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (rootAmbient segment).Contains (sample segment owner rootDiameter) := by
  let core := rootSampleCoordinateRadius segment
  have bounds := sample_rootSampleCoordinateBounds segment parameter inside
    owner rootDiameterPositive
  change -rootAmbientRadius segment <=
      (sample segment owner rootDiameter).re ∧
    (sample segment owner rootDiameter).re <= rootAmbientRadius segment ∧
    -rootAmbientRadius segment <= (sample segment owner rootDiameter).im ∧
    (sample segment owner rootDiameter).im <= rootAmbientRadius segment
  dsimp only [rootAmbientRadius]
  exact
    ⟨(by
        calc
          -(core + 1) <= -core := by
            exact Fraction.Order.Arithmetic.neg_le_neg_direct
              (le_add_of_nonneg_right (by decide))
          _ <= (sample segment owner rootDiameter).re := bounds.1),
      bounds.2.1.trans (le_add_of_nonneg_right (by decide)),
      (by
        calc
          -(core + 1) <= -core := by
            exact Fraction.Order.Arithmetic.neg_le_neg_direct
              (le_add_of_nonneg_right (by decide))
          _ <= (sample segment owner rootDiameter).im := bounds.2.2.1),
      bounds.2.2.2.trans (le_add_of_nonneg_right (by decide))⟩

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation in
/-- Construct the separated restart input at the selected sample using the uniform preparation radius.

The common root box retains strict two-radius coordinate margins, while the same sample certificates pay the residual,
derivative, displacement and Taylor requirements. -/
@[expose] public def restartInput
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Newton.Restart.Separated.Basic.SeparatedRestartInput
      (ClearSheetContinuation.squareRootDerivativeSeparation
        (rootAmbient := rootAmbient segment) segment parameter inside) := by
  let p := rootPolynomialAt segment parameter
  let radius := preparationRadius segment rootDiameter
  let separation :=
    ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := rootAmbient segment) segment parameter inside
  let point := sample segment owner rootDiameter
  have bounds := sample_rootSampleCoordinateBounds segment parameter inside
    owner rootDiameterPositive
  have twiceRadiusLt : 2 * radius < 1 :=
    two_preparationRadius_lt_one segment rootDiameterPositive
  let core := rootSampleCoordinateRadius segment
  have leftMargin : (rootAmbient segment).xLower + 2 * radius < point.re :=
    (by
      have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
        twiceRadiusLt (-(core + 1))
      have coreLower : -(core + 1) + 2 * radius < -core := by
        calc
          -(core + 1) + 2 * radius < -(core + 1) + 1 := shifted
          _ = -core := by ring1
      change -(core + 1) + 2 * radius < point.re
      exact coreLower.trans_le bounds.1)
  have rightMargin : point.re + 2 * radius <
      (rootAmbient segment).xUpper :=
    (by
      change point.re + 2 * radius < core + 1
      exact (Fraction.Order.Arithmetic.add_le_add_right_direct bounds.2.1
          (2 * radius)).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct twiceRadiusLt core))
  have bottomMargin : (rootAmbient segment).yLower + 2 * radius < point.im :=
    (by
      have shifted := Fraction.Order.Arithmetic.add_lt_add_left_direct
        twiceRadiusLt (-(core + 1))
      have coreLower : -(core + 1) + 2 * radius < -core := by
        calc
          -(core + 1) + 2 * radius < -(core + 1) + 1 := shifted
          _ = -core := by ring1
      change -(core + 1) + 2 * radius < point.im
      exact coreLower.trans_le bounds.2.2.1)
  have topMargin : point.im + 2 * radius <
      (rootAmbient segment).yUpper :=
    (by
      change point.im + 2 * radius < core + 1
      exact (Fraction.Order.Arithmetic.add_le_add_right_direct bounds.2.2.2
          (2 * radius)).trans_lt
        (Fraction.Order.Arithmetic.add_lt_add_left_direct twiceRadiusLt core))
  apply Newton.Restart.Separated.Basic.SeparatedRestartInput.ofAnchored point radius
    (preparationRadius_positive segment rootDiameterPositive)
    leftMargin rightMargin bottomMargin topMargin
  · change Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      Bounds.Box.denseLipschitzBound
          (rootPolynomialAt segment parameter) (rootAmbient segment) *
        (2 * preparationRadius segment rootDiameter ^ 2)
    rw [rootLipschitz_formula segment parameter]
    exact sample_residual_le_uniformSource segment owner rootDiameterPositive
  · change Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <= separation.threshold
    simpa only [rootLipschitz, separation,
      ClearSheetContinuation.squareRootDerivativeSeparation_threshold]
      using sample_residual_le_uniformThreshold segment owner
        rootDiameterPositive
  · apply (Fraction.Order.Field.div_le_iff_pos
      (ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment)).2
    change Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      preparationRadius segment rootDiameter ^ 2 *
        ClearSheetContinuation.squareRootDerivativeMargin segment
    simpa only [Fraction.Field.mul_comm]
      using sample_residual_le_uniformDisplacement segment owner
        rootDiameterPositive
  · change 2 * (36 *
        Bounds.Box.Taylor.denseTaylorRemainderBound
          (rootPolynomialAt segment parameter) (rootAmbient segment) *
        preparationRadius segment rootDiameter ^ 2) <= separation.margin
    simpa only [separation,
      ClearSheetContinuation.squareRootDerivativeSeparation_margin]
      using preparation_taylorSmall segment parameter rootDiameterPositive

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Twice the bridge radius is strictly below the original owner's residual interior radius.

The original bridge radius is at most three eighths of the owner's positive residual interior radius. Doubling preserves
a strict margin within that same interior radius. -/
public theorem two_bridgeRadius_lt_ownerInterior
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) :
    2 * bridgeRadius segment owner rootDiameter <
      owner.track.initial.clearance.residualInteriorRadius := by
  let radius := bridgeRadius segment owner rootDiameter
  let interior := owner.track.initial.clearance.residualInteriorRadius
  have radiusLe : radius <= (3 / 8 : Coordinate) * interior :=
    bridgeRadius_le_ownerInteriorScale segment owner rootDiameter
  have interiorPositive : 0 < interior :=
    owner.track.initial.clearance.residualInteriorRadius_pos
  calc
    2 * radius <= 2 * ((3 / 8 : Coordinate) * interior) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct radiusLe
        (by decide)
    _ = (2 * (3 / 8 : Coordinate)) * interior := by ring1
    _ = (3 / 4 : Coordinate) * interior := by
      rw [show (2 : Coordinate) * (3 / 8) = 3 / 4 by decide]
    _ < 1 * interior :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (by decide) interiorPositive
    _ = interior := by ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation in
/-- Construct the bridge restart input at the same selected sample in the original owner's box.

Its separate retained radius satisfies the original interior margins and local residual and Taylor bounds, preserving
the exact source owner for comparison. -/
@[expose] public def bridgeRestartInput
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Newton.Restart.Separated.Basic.SeparatedRestartInput
      (ClearSheetContinuation.squareRootDerivativeSeparation
        (rootAmbient := owner.track.initial.box) segment parameter inside) := by
  let p := rootPolynomialAt segment parameter
  let ownerBox := owner.track.initial.box
  let radius := bridgeRadius segment owner rootDiameter
  let separation :=
    ClearSheetContinuation.squareRootDerivativeSeparation
      (rootAmbient := ownerBox) segment parameter inside
  let point := sample segment owner rootDiameter
  have margins := owner.track.initial.clearance.residualInteriorMargins
    (sample_inside_owner segment owner rootDiameter)
    (sample_residual_lt_ownerQuarter segment owner rootDiameterPositive)
  have twiceRadiusLt :
      2 * radius < owner.track.initial.clearance.residualInteriorRadius :=
    two_bridgeRadius_lt_ownerInterior segment owner rootDiameter
  have leftMargin : ownerBox.xLower + 2 * radius < point.re :=
    (Fraction.Order.Arithmetic.add_lt_add_left_direct twiceRadiusLt
      ownerBox.xLower).trans margins.1
  have rightMargin : point.re + 2 * radius < ownerBox.xUpper :=
    (Fraction.Order.Arithmetic.add_lt_add_left_direct twiceRadiusLt point.re).trans
      margins.2.1
  have bottomMargin : ownerBox.yLower + 2 * radius < point.im :=
    (Fraction.Order.Arithmetic.add_lt_add_left_direct twiceRadiusLt
      ownerBox.yLower).trans margins.2.2.1
  have topMargin : point.im + 2 * radius < ownerBox.yUpper :=
    (Fraction.Order.Arithmetic.add_lt_add_left_direct twiceRadiusLt point.im).trans
      margins.2.2.2
  apply Newton.Restart.Separated.Basic.SeparatedRestartInput.ofAnchored point radius
    (bridgeRadius_positive segment owner rootDiameterPositive)
    leftMargin rightMargin bottomMargin topMargin
  · change Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      Bounds.Box.denseLipschitzBound
          (rootPolynomialAt segment parameter) owner.track.initial.box *
        (2 * bridgeRadius segment owner rootDiameter ^ 2)
    exact sample_residual_le_bridgeSource segment owner rootDiameterPositive
  · change Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <= separation.threshold
    simpa only [separation,
      ClearSheetContinuation.squareRootDerivativeSeparation_threshold]
      using (sample_residual_le_bridgeSource segment owner
          rootDiameterPositive).trans
        (bridge_sourceThreshold segment owner rootDiameterPositive)
  · apply (Fraction.Order.Field.div_le_iff_pos
      (ClearSheetContinuation.squareRootDerivativeMargin_positive
        segment)).2
    change Data.Gaussian.Norm.Basic.normSq
        ((rootPolynomialAt segment parameter).eval
          (sample segment owner rootDiameter)) <=
      bridgeRadius segment owner rootDiameter ^ 2 *
        ClearSheetContinuation.squareRootDerivativeMargin segment
    simpa only [Fraction.Field.mul_comm]
      using sample_residual_le_bridgeDisplacement segment owner
        rootDiameterPositive
  · change 2 * (36 *
        Bounds.Box.Taylor.denseTaylorRemainderBound
          (rootPolynomialAt segment parameter) owner.track.initial.box *
        bridgeRadius segment owner rootDiameter ^ 2) <= separation.margin
    simpa only [separation,
      ClearSheetContinuation.squareRootDerivativeSeparation_margin]
      using bridge_taylorSmall segment owner rootDiameterPositive

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The uniform restart input's source anchor equals the exact selected sample. -/
@[simp] public theorem restartInput_source_anchor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (restartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).source.anchor =
        sample segment owner rootDiameter := by
  change (Box.Square.Anchored.anchoredSquare
      (sample segment owner rootDiameter)
      (preparationRadius segment rootDiameter)
      (preparationRadius_positive segment rootDiameterPositive).le).anchor = _
  exact Box.Square.Anchored.anchoredSquare_anchor _ _ _

open Purelib.Polynomial in
/-- The uniform restart input retains the exact preparation radius. -/
@[simp] public theorem restartInput_radius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (restartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        preparationRadius segment rootDiameter := rfl

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The retained linearization majorant bounds every point on the exact restart centered-box boundary.

The sample derivative estimate is multiplied by the same centered-square radial estimate, using the retained preparation
radius. -/
public theorem restart_newtonLinearization_boundary_le_majorant
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (z : Gaussian)
    (boundary : Box.Boundary.OnBoxBoundary
      (restartInput segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox z) :
    Data.Gaussian.Norm.Basic.normSq
        ((Newton.Box.Linearization.newtonLinearization
          (rootPolynomialAt segment parameter)
          (restartInput segment parameter inside owner rootDiameter
            rootDiameterPositive).source).eval z) <=
      linearizationMajorant segment rootDiameter := by
  let restart := restartInput segment parameter inside owner rootDiameter
    rootDiameterPositive
  have derivativeBound :
      Data.Gaussian.Norm.Basic.normSq
          ((GCD.derivative
            (rootPolynomialAt segment parameter)).eval
              restart.source.anchor) <=
        rootSampleDerivativeMajorant segment := by
    dsimp only [restart]
    rw [restartInput_source_anchor]
    exact sample_rootDerivative_le_rootSampleDerivativeMajorant segment
      parameter inside owner rootDiameterPositive
  have radial :
      Data.Gaussian.Norm.Basic.normSq
          (z - Newton.Box.Anchor.anchorNewtonCenter
            (rootPolynomialAt segment parameter) restart.source) <=
        2 * restart.radius ^ 2 := by
    apply Box.Square.Centered.centeredSquare_normSq_sub_center_le
      (Newton.Box.Anchor.anchorNewtonCenter
        (rootPolynomialAt segment parameter) restart.source)
      restart.radiusPositive.le
    exact boundary.1
  rw [Newton.Box.Linearization.newtonLinearization,
    Linear.Affine.affineCoordinate_eval,
    Norm.Basic.normSq_mul]
  calc
    Data.Gaussian.Norm.Basic.normSq
          ((GCD.derivative
            (rootPolynomialAt segment parameter)).eval restart.source.anchor) *
        Data.Gaussian.Norm.Basic.normSq
          (z - Newton.Box.Anchor.anchorNewtonCenter
            (rootPolynomialAt segment parameter) restart.source) <=
      rootSampleDerivativeMajorant segment * (2 * restart.radius ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_direct derivativeBound radial
          (Norm.Basic.normSq_nonneg _)
          (rootSampleDerivativeMajorant_positive segment).le
    _ = linearizationMajorant segment rootDiameter := by
      dsimp only [restart]
      rw [restartInput_radius]
      unfold linearizationMajorant
      ring1

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
/-- The bridge restart input's source anchor equals the same selected sample. -/
@[simp] public theorem bridgeRestartInput_source_anchor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeRestartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).source.anchor =
        sample segment owner rootDiameter := by
  change (Box.Square.Anchored.anchoredSquare
      (sample segment owner rootDiameter)
      (bridgeRadius segment owner rootDiameter)
      (bridgeRadius_positive segment owner rootDiameterPositive).le).anchor = _
  exact Box.Square.Anchored.anchoredSquare_anchor _ _ _

open Purelib.Polynomial in
/-- The bridge restart input retains the exact owner-specific radius. -/
@[simp] public theorem bridgeRestartInput_radius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeRestartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).radius =
        bridgeRadius segment owner rootDiameter := rfl

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The bridge radius is strictly below the positive uniform preparation radius.

The owner-specific bridge retains a three-eighths cap of the positive uniform preparation radius. That strict cap
compares the two original retained radii. -/
public theorem bridgeRadius_lt_preparation
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {parameter : Coordinate}
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    bridgeRadius segment owner rootDiameter <
      preparationRadius segment rootDiameter := by
  have bridgeLeQuarter : bridgeRadius segment owner rootDiameter <=
      (1 / 4 : Coordinate) * preparationRadius segment rootDiameter :=
    (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  calc
    bridgeRadius segment owner rootDiameter <=
        (1 / 4 : Coordinate) * preparationRadius segment rootDiameter :=
      bridgeLeQuarter
    _ < 1 * preparationRadius segment rootDiameter :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (by decide) (preparationRadius_positive segment rootDiameterPositive)
    _ = preparationRadius segment rootDiameter := by ring1

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The bridge and uniform restart inputs have exactly the same Newton center.

Both restart inputs retain the exact same selected sample as their source anchor. Their original polynomial and
derivative therefore determine the same Newton center. -/
public theorem restart_newtonCenter_eq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Newton.Box.Anchor.anchorNewtonCenter
        (rootPolynomialAt segment parameter)
        (bridgeRestartInput segment parameter inside owner rootDiameter
          rootDiameterPositive).source =
      Newton.Box.Anchor.anchorNewtonCenter
        (rootPolynomialAt segment parameter)
        (restartInput segment parameter inside owner rootDiameter
          rootDiameterPositive).source := by
  rw [Newton.Box.Anchor.anchorNewtonCenter_eq,
    Newton.Box.Anchor.anchorNewtonCenter_eq,
    bridgeRestartInput_source_anchor, restartInput_source_anchor]

section

open Purelib.Polynomial
open Purelib.Riemann.RootContinuation

/-- The explicit squarefree isolation input at the retained nonzero segment parameter.

The original segment parameter lies between zero and one, so its polynomial value is nonzero. The retained quadratic
squarefreeness and axis elimination certify that exact parameter polynomial. -/
@[expose] public def inputAt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1) :=
  SquareRootReconditioning.isolationInput
    (segment.pointAt_eval_ne_zero parameter inside)

end

open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The exact common dominance-margin square divided by four times the retained linearization majorant.

The quadratic Taylor coefficient is eight, so this expression depends on the segment and diameter request while
remaining independent of the parameter and starting owner. -/
@[expose] public def predictedClearance
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) : Coordinate :=
  let radius := preparationRadius segment rootDiameter
  (ClearSheetContinuation.squareRootDerivativeMargin segment *
        radius ^ 2 -
      36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
    (4 * linearizationMajorant segment rootDiameter)

/-- The square of one eighth is one sixty-fourth in the rational carrier. -/
private theorem oneEighth_sq_eq_one64 :
    (1 / 8 : Coordinate) ^ 2 = 1 / (8 * 8) := by decide

/-- One sixty-fourth times one squared is at most five eighths. -/
private theorem one64_mul_nineteenQuarter_sq_le_fiveEighth :
    (1 / (8 * 8) : Coordinate) * 1 ^ 2 <= 5 / 8 := by decide

/-- Five eighths equals eighty times one one-hundred-twenty-eighth. -/
private theorem fiveEighth_eq_one128_mul80 :
    (5 / 8 : Coordinate) = (1 / (16 * 8)) * (10 * 8) := by decide

open Purelib.Data.Rat in
/-- The rational product thirty-six times eight is nonnegative. -/
private theorem zero_le_288 : (0 : Coordinate) <= 36 * 8 :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 36) (by decide)).le
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 8) (by decide)).le
/-- The rational constant four is nonnegative. -/
private theorem zero_le_four : (0 : Coordinate) <= 4 := by decide
/-- The rational reciprocal of eight squared is nonnegative. -/
private theorem zero_le_one64 : (0 : Coordinate) <= 1 / (8 * 8) := by decide
/-- The rational reciprocal of sixteen times eight is nonnegative. -/
private theorem zero_le_one128 :
    (0 : Coordinate) <= 1 / (16 * 8) := by decide

section

open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Riemann.Branches

/-- A derivative margin at most one quarter makes predicted clearance at most one one-hundred-twenty-eighth.

The preparation radius cap and retained lower bound on the linearization majorant bound the exact dominance numerator
and positive denominator. -/
public theorem predictedClearance_le_oneOver128
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (marginLe :
      ClearSheetContinuation.squareRootDerivativeMargin segment <=
        (1 / 4 : Coordinate)) :
    predictedClearance segment rootDiameter <=
      (1 / (16 * 8) : Coordinate) := by
  let radius := preparationRadius segment rootDiameter
  let margin :=
    ClearSheetContinuation.squareRootDerivativeMargin segment
  let majorant := linearizationMajorant segment rootDiameter
  change
    (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
        (4 * majorant) <= (1 / (16 * 8) : Coordinate)
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment rootDiameterPositive
  have radiusSqLe : radius ^ 2 <= (1 / (8 * 8) : Coordinate) := by
    calc
      radius ^ 2 <= (1 / 8 : Coordinate) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
          (preparationRadius_le_oneEighth segment rootDiameter) 2
      _ = 1 / (8 * 8) := oneEighth_sq_eq_one64
  have marginNonnegative : 0 <= margin :=
    (ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment).le
  have bracketNonnegative :
      0 <= margin + (36 * 8) * radius ^ 2 :=
    add_nonneg marginNonnegative
      (Fraction.Order.Arithmetic.mul_nonneg_direct zero_le_288
        (Fraction.Order.Arithmetic.sq_nonneg_direct radius))
  have taylorDenominatorPositive : (0 : Coordinate) < 72 * 8 :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 72) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 8) (by decide))
  have scaledTaylor : radius ^ 2 * (72 * 8) <= margin :=
    (Fraction.Order.Field.le_div_iff_pos taylorDenominatorPositive).mp
      (preparationRadius_sq_lt_taylorRatio segment
        rootDiameterPositive).le
  have secondTermNonnegative : 0 <= (36 * 8) * radius ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct zero_le_288
      (Fraction.Order.Arithmetic.sq_nonneg_direct radius)
  have secondTermLeMargin : (36 * 8) * radius ^ 2 <= margin := by
    calc
      (36 * 8) * radius ^ 2 = 1 * ((36 * 8) * radius ^ 2) := by ring1
      _ <= 2 * ((36 * 8) * radius ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) <= 2 by decide) secondTermNonnegative
      _ = radius ^ 2 * (72 * 8) := by ring1
      _ <= margin := scaledTaylor
  have bracketLe :
      margin + (36 * 8) * radius ^ 2 <= (1 : Coordinate) := by
    calc
      margin + (36 * 8) * radius ^ 2 <= margin + margin :=
        add_le_add le_rfl secondTermLeMargin
      _ <= (1 / 4 : Coordinate) + 1 / 4 := add_le_add marginLe marginLe
      _ <= 1 := by decide
  have bracketSqLe :
      (margin + (36 * 8) * radius ^ 2) ^ 2 <=
        (1 : Coordinate) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct bracketNonnegative bracketLe 2
  have scaledBracketLe :
      radius ^ 2 * (margin + (36 * 8) * radius ^ 2) ^ 2 <=
        (5 / 8 : Coordinate) := by
    calc
      radius ^ 2 * (margin + (36 * 8) * radius ^ 2) ^ 2 <=
          (1 / (8 * 8) : Coordinate) *
            (margin + (36 * 8) * radius ^ 2) ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct radiusSqLe
          (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      _ <= (1 / (8 * 8) : Coordinate) * (1 : Coordinate) ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bracketSqLe
          zero_le_one64
      _ <= 5 / 8 := one64_mul_nineteenQuarter_sq_le_fiveEighth
  have firstTermNonnegative : 0 <= margin * radius ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct marginNonnegative
      (Fraction.Order.Arithmetic.sq_nonneg_direct radius)
  have quadraticTermNonnegative :
      0 <= (36 * 8) * (radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct zero_le_288
      (Fraction.Order.Arithmetic.sq_nonneg_direct (radius ^ 2))
  have correctionNonnegative :
      0 <= 4 * (margin * radius ^ 2) * ((36 * 8) * (radius ^ 2) ^ 2) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct zero_le_four
        firstTermNonnegative) quadraticTermNonnegative
  have differenceSquareLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
        (margin * radius ^ 2 + (36 * 8) * (radius ^ 2) ^ 2) ^ 2 := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
          (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 +
            4 * (margin * radius ^ 2) *
              ((36 * 8) * (radius ^ 2) ^ 2) :=
        le_add_of_nonneg_right
          correctionNonnegative
      _ = (margin * radius ^ 2 + (36 * 8) * (radius ^ 2) ^ 2) ^ 2 := by
        ring1
  have numeratorLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
        (5 / 8 : Coordinate) * radius ^ 2 := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
          (margin * radius ^ 2 + (36 * 8) * (radius ^ 2) ^ 2) ^ 2 :=
        differenceSquareLe
      _ = radius ^ 2 *
          (radius ^ 2 * (margin + (36 * 8) * radius ^ 2) ^ 2) := by ring1
      _ <= radius ^ 2 * (5 / 8 : Coordinate) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          scaledBracketLe (Fraction.Order.Arithmetic.sq_nonneg_direct radius)
      _ = (5 / 8 : Coordinate) * radius ^ 2 := by ring1
  have majorantLower :
      (10 * 8) * radius ^ 2 <= 4 * majorant := by
    have base :=
      twenty_mul_preparationRadius_sq_le_linearizationMajorant segment
        rootDiameter
    calc
      (10 * 8) * radius ^ 2 = 4 * (20 * radius ^ 2) := by ring1
      _ <= 4 * majorant :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct base
          zero_le_four
  have numeratorLeScaledMajorant :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
        (1 / (16 * 8) : Coordinate) * (4 * majorant) := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 <=
          (5 / 8 : Coordinate) * radius ^ 2 := numeratorLe
      _ = (1 / (16 * 8) : Coordinate) * ((10 * 8) * radius ^ 2) := by
        rw [← mul_assoc, ← fiveEighth_eq_one128_mul80]
      _ <= (1 / (16 * 8) : Coordinate) * (4 * majorant) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          majorantLower zero_le_one128
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment rootDiameterPositive)
  exact (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
    numeratorLeScaledMajorant

/-- Bound predicted clearance by the quarter transport floor when the radius is at most one sixty-fourth.

The derivative margin is at most one quarter and the diameter request is positive; both constraints apply to the same
retained preparation formula. -/
public theorem predictedClearance_le_quarterTransportFloor_of_radius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (marginLe :
      ClearSheetContinuation.squareRootDerivativeMargin segment <=
        (1 / 4 : Coordinate))
    (radiusLe : preparationRadius segment rootDiameter ≤
      (1 / 64 : Coordinate)) :
    predictedClearance segment rootDiameter ≤
      (1 / 4 : Coordinate) ^ 2 / (4 * 65536) := by
  let radius := preparationRadius segment rootDiameter
  let margin :=
    ClearSheetContinuation.squareRootDerivativeMargin segment
  let majorant := linearizationMajorant segment rootDiameter
  change
    (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
        (4 * majorant) ≤ (1 / 4 : Coordinate) ^ 2 / (4 * 65536)
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment rootDiameterPositive
  have radiusSqNonnegative : 0 ≤ radius ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct radius
  have radiusSqLe : radius ^ 2 ≤ (1 / 4096 : Coordinate) := by
    calc
      radius ^ 2 ≤ (1 / 64 : Coordinate) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
          radiusLe 2
      _ = (1 / 4096 : Coordinate) := by
        rw [pow_two, Fraction.Field.div_mul_div_direct]
        rw [one_mul]
        rw [show (64 : Coordinate) * 64 = 4096 by ring1]
  have marginNonnegative : 0 ≤ margin :=
    (ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment).le
  have taylorDenominatorPositive : (0 : Coordinate) < 72 * 8 :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 72) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 8) (by decide))
  have scaledTaylor : radius ^ 2 * (72 * 8) ≤ margin :=
    (Fraction.Order.Field.le_div_iff_pos taylorDenominatorPositive).mp
      (preparationRadius_sq_lt_taylorRatio segment
        rootDiameterPositive).le
  have secondTermNonnegative : 0 ≤ (36 * 8) * radius ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct zero_le_288
      radiusSqNonnegative
  have secondTermLeMargin : (36 * 8) * radius ^ 2 ≤ margin := by
    calc
      (36 * 8) * radius ^ 2 = 1 * ((36 * 8) * radius ^ 2) := by ring1
      _ ≤ 2 * ((36 * 8) * radius ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) ≤ 2 by decide) secondTermNonnegative
      _ = radius ^ 2 * (72 * 8) := by ring1
      _ ≤ margin := scaledTaylor
  have correctionNonnegative : 0 ≤ (36 * 8) * (radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct zero_le_288
      (Fraction.Order.Arithmetic.sq_nonneg_direct (radius ^ 2))
  have correctionLeFirst :
      (36 * 8) * (radius ^ 2) ^ 2 ≤ margin * radius ^ 2 := by
    calc
      (36 * 8) * (radius ^ 2) ^ 2 =
          ((36 * 8) * radius ^ 2) * radius ^ 2 := by ring1
      _ ≤ margin * radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          secondTermLeMargin radiusSqNonnegative
  have differenceNonnegative :
      0 ≤ margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.sub_nonneg_direct correctionLeFirst
  have differenceLeFirst :
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
        margin * radius ^ 2 := by
    calc
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
          margin * radius ^ 2 - 0 :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct
          correctionNonnegative _
      _ = margin * radius ^ 2 := by ring1
  have differenceSquareLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (margin * radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct differenceNonnegative
      differenceLeFirst 2
  have marginSquareLe : margin ^ 2 ≤ (1 / 16 : Coordinate) := by
    calc
      margin ^ 2 ≤ (1 / 4 : Coordinate) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct marginNonnegative
          marginLe 2
      _ = (1 / 16 : Coordinate) := by decide
  have radiusFourthLe : (radius ^ 2) ^ 2 ≤
      (1 / 4096 : Coordinate) * radius ^ 2 := by
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      radiusSqLe radiusSqNonnegative
  have numeratorLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (1 / 65536 : Coordinate) * radius ^ 2 := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (margin * radius ^ 2) ^ 2 := differenceSquareLe
      _ = margin ^ 2 * (radius ^ 2) ^ 2 := by ring1
      _ ≤ (1 / 16 : Coordinate) * (radius ^ 2) ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          marginSquareLe
            (Fraction.Order.Arithmetic.sq_nonneg_direct (radius ^ 2))
      _ ≤ (1 / 16 : Coordinate) *
          ((1 / 4096 : Coordinate) * radius ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusFourthLe (by decide)
      _ = ((1 / 16 : Coordinate) * (1 / 4096)) * radius ^ 2 := by ring1
      _ = (1 / 65536 : Coordinate) * radius ^ 2 := by
        have coefficientProduct :
            (1 / 16 : Coordinate) * (1 / 4096) = 1 / 65536 := by
          rw [Fraction.Field.div_mul_div_direct]
          rw [one_mul]
          rw [show (16 : Coordinate) * 4096 = 65536 by ring1]
        rw [coefficientProduct]
  have majorantLower : (80 : Coordinate) * radius ^ 2 ≤ 4 * majorant := by
    have base :=
      twenty_mul_preparationRadius_sq_le_linearizationMajorant segment
        rootDiameter
    calc
      (80 : Coordinate) * radius ^ 2 = 4 * (20 * radius ^ 2) := by ring1
      _ ≤ 4 * majorant :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct base
          zero_le_four
  let floor : Coordinate := (1 / 4 : Coordinate) ^ 2 / (4 * 65536)
  have largeDenominatorPositive : (0 : Coordinate) < 4 * 65536 :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 4) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 65536) (by decide))
  have largeDenominatorNonzero : (4 * 65536 : Coordinate) ≠ 0 :=
    largeDenominatorPositive.ne'
  have sixtyFiveThousandFiveHundredThirtySixNonzero :
      (65536 : Coordinate) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 65536) (by decide)).ne'
  have coefficientLe : (1 / 65536 : Coordinate) ≤ floor * 80 := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct _
      largeDenominatorPositive
    calc
      (1 / 65536 : Coordinate) * (4 * 65536) =
          ((1 / 65536 : Coordinate) * 65536) * 4 := by ring1
      _ = 4 := by
        rw [Fraction.Field.div_mul_cancel_of_ne _ _
          sixtyFiveThousandFiveHundredThirtySixNonzero]
        ring1
      _ ≤ 5 := by decide
      _ = (floor * 80) * (4 * 65536) := by
        dsimp only [floor]
        rw [show (((1 / 4 : Coordinate) ^ 2 / (4 * 65536)) * 80) *
            (4 * 65536) =
          (((1 / 4 : Coordinate) ^ 2 / (4 * 65536)) *
            (4 * 65536)) * 80 by ring1]
        rw [Fraction.Field.div_mul_cancel_of_ne _ _
          largeDenominatorNonzero]
        rw [pow_two, Fraction.Field.div_mul_div_direct]
        rw [one_mul]
        rw [show (4 : Coordinate) * 4 = 16 by ring1]
        rw [show (80 : Coordinate) = 16 * 5 by ring1]
        rw [← mul_assoc,
          Fraction.Field.div_mul_cancel_of_ne _ _
            (show (16 : Coordinate) ≠ 0 by decide)]
        ring1
  have numeratorLeFloorMajorant :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        floor * (4 * majorant) := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (1 / 65536 : Coordinate) * radius ^ 2 := numeratorLe
      _ ≤ (floor * 80) * radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          coefficientLe radiusSqNonnegative
      _ = floor * (80 * radius ^ 2) := by ring1
      _ ≤ floor * (4 * majorant) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          majorantLower
            (Fraction.Order.Field.div_nonneg_direct
              (Fraction.Order.Arithmetic.sq_nonneg_direct (1 / 4))
                largeDenominatorPositive.le)
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment rootDiameterPositive)
  exact (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
    numeratorLeFloorMajorant

/-- Bound predicted clearance by the eighth transport floor using the stronger supplied majorant bound.

The radius is at most one sixty-fourth, the derivative margin at most one quarter, and four times the original majorant
dominates 256 times radius squared. -/
public theorem predictedClearance_le_eighthTransportFloor_of_radius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (marginLe :
      ClearSheetContinuation.squareRootDerivativeMargin segment <=
        (1 / 4 : Coordinate))
    (radiusLe : preparationRadius segment rootDiameter ≤
      (1 / 64 : Coordinate))
    (majorantLower :
      256 * preparationRadius segment rootDiameter ^ 2 ≤
        4 * linearizationMajorant segment rootDiameter) :
    predictedClearance segment rootDiameter ≤
      (1 / 8 : Coordinate) ^ 2 / (4 * 65536) := by
  let radius := preparationRadius segment rootDiameter
  let margin :=
    ClearSheetContinuation.squareRootDerivativeMargin segment
  let majorant := linearizationMajorant segment rootDiameter
  change
    (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
        (4 * majorant) ≤ (1 / 8 : Coordinate) ^ 2 / (4 * 65536)
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment rootDiameterPositive
  have radiusSqNonnegative : 0 ≤ radius ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct radius
  have radiusSqLe : radius ^ 2 ≤ (1 / 4096 : Coordinate) := by
    calc
      radius ^ 2 ≤ (1 / 64 : Coordinate) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
          radiusLe 2
      _ = (1 / 4096 : Coordinate) := by
        rw [pow_two, Fraction.Field.div_mul_div_direct]
        rw [one_mul]
        rw [show (64 : Coordinate) * 64 = 4096 by ring1]
  have marginNonnegative : 0 ≤ margin :=
    (ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment).le
  have taylorDenominatorPositive : (0 : Coordinate) < 72 * 8 :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 72) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 8) (by decide))
  have scaledTaylor : radius ^ 2 * (72 * 8) ≤ margin :=
    (Fraction.Order.Field.le_div_iff_pos taylorDenominatorPositive).mp
      (preparationRadius_sq_lt_taylorRatio segment
        rootDiameterPositive).le
  have secondTermNonnegative : 0 ≤ (36 * 8) * radius ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct zero_le_288
      radiusSqNonnegative
  have secondTermLeMargin : (36 * 8) * radius ^ 2 ≤ margin := by
    calc
      (36 * 8) * radius ^ 2 = 1 * ((36 * 8) * radius ^ 2) := by ring1
      _ ≤ 2 * ((36 * 8) * radius ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 : Coordinate) ≤ 2 by decide) secondTermNonnegative
      _ = radius ^ 2 * (72 * 8) := by ring1
      _ ≤ margin := scaledTaylor
  have correctionNonnegative : 0 ≤ (36 * 8) * (radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct zero_le_288
      (Fraction.Order.Arithmetic.sq_nonneg_direct (radius ^ 2))
  have correctionLeFirst :
      (36 * 8) * (radius ^ 2) ^ 2 ≤ margin * radius ^ 2 := by
    calc
      (36 * 8) * (radius ^ 2) ^ 2 =
          ((36 * 8) * radius ^ 2) * radius ^ 2 := by ring1
      _ ≤ margin * radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          secondTermLeMargin radiusSqNonnegative
  have differenceNonnegative :
      0 ≤ margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.sub_nonneg_direct correctionLeFirst
  have differenceLeFirst :
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
        margin * radius ^ 2 := by
    calc
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
          margin * radius ^ 2 - 0 :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct
          correctionNonnegative _
      _ = margin * radius ^ 2 := by ring1
  have differenceSquareLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (margin * radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct differenceNonnegative
      differenceLeFirst 2
  have marginSquareLe : margin ^ 2 ≤ (1 / 16 : Coordinate) := by
    calc
      margin ^ 2 ≤ (1 / 4 : Coordinate) ^ 2 :=
        Fraction.Order.Arithmetic.pow_le_pow_direct marginNonnegative
          marginLe 2
      _ = (1 / 16 : Coordinate) := by decide
  have radiusFourthLe : (radius ^ 2) ^ 2 ≤
      (1 / 4096 : Coordinate) * radius ^ 2 := by
    rw [pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      radiusSqLe radiusSqNonnegative
  have numeratorLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (1 / 65536 : Coordinate) * radius ^ 2 := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (margin * radius ^ 2) ^ 2 := differenceSquareLe
      _ = margin ^ 2 * (radius ^ 2) ^ 2 := by ring1
      _ ≤ (1 / 16 : Coordinate) * (radius ^ 2) ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          marginSquareLe
            (Fraction.Order.Arithmetic.sq_nonneg_direct (radius ^ 2))
      _ ≤ (1 / 16 : Coordinate) *
          ((1 / 4096 : Coordinate) * radius ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusFourthLe (by decide)
      _ = ((1 / 16 : Coordinate) * (1 / 4096)) * radius ^ 2 := by ring1
      _ = (1 / 65536 : Coordinate) * radius ^ 2 := by
        have coefficientProduct :
            (1 / 16 : Coordinate) * (1 / 4096) = 1 / 65536 := by
          rw [Fraction.Field.div_mul_div_direct]
          rw [one_mul]
          rw [show (16 : Coordinate) * 4096 = 65536 by ring1]
        rw [coefficientProduct]
  let floor : Coordinate := (1 / 8 : Coordinate) ^ 2 / (4 * 65536)
  have largeDenominatorPositive : (0 : Coordinate) < 4 * 65536 :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 4) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 65536) (by decide))
  have largeDenominatorNonzero : (4 * 65536 : Coordinate) ≠ 0 :=
    largeDenominatorPositive.ne'
  have sixtyFiveThousandFiveHundredThirtySixNonzero :
      (65536 : Coordinate) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 65536) (by decide)).ne'
  have sixtyFourNonzero : (64 : Coordinate) ≠ 0 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 64) (by decide)).ne'
  have coefficientEq :
      (1 / 65536 : Coordinate) = floor * 256 := by
    apply Fraction.Field.mul_right_cancel_of_ne
      largeDenominatorNonzero
    calc
      (1 / 65536 : Coordinate) * (4 * 65536) = 4 := by
        rw [show (1 / 65536 : Coordinate) * (4 * 65536) =
          ((1 / 65536 : Coordinate) * 65536) * 4 by ring1]
        rw [Fraction.Field.div_mul_cancel_of_ne _ _
          sixtyFiveThousandFiveHundredThirtySixNonzero]
        ring1
      _ = (floor * 256) * (4 * 65536) := by
        dsimp only [floor]
        rw [show (((1 / 8 : Coordinate) ^ 2 / (4 * 65536)) * 256) *
            (4 * 65536) =
          (((1 / 8 : Coordinate) ^ 2 / (4 * 65536)) *
            (4 * 65536)) * 256 by ring1]
        rw [Fraction.Field.div_mul_cancel_of_ne _ _
          largeDenominatorNonzero]
        rw [pow_two, Fraction.Field.div_mul_div_direct]
        rw [one_mul]
        rw [show (8 : Coordinate) * 8 = 64 by ring1]
        rw [show (256 : Coordinate) = 64 * 4 by ring1]
        rw [← mul_assoc,
          Fraction.Field.div_mul_cancel_of_ne _ _
            sixtyFourNonzero]
        ring1
  have floorNonnegative : 0 ≤ floor :=
    Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct (1 / 8))
      largeDenominatorPositive.le
  have numeratorLeFloorMajorant :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        floor * (4 * majorant) := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (1 / 65536 : Coordinate) * radius ^ 2 := numeratorLe
      _ = (floor * 256) * radius ^ 2 := by rw [coefficientEq]
      _ = floor * (256 * radius ^ 2) := by ring1
      _ ≤ floor * (4 * majorant) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          majorantLower floorNonnegative
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment rootDiameterPositive)
  exact (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
    numeratorLeFloorMajorant

/-- The exact quarter margin and one-sixty-fourth radius satisfy the eighth transport floor.

The retained sample derivative majorant is at least 26; the rational calculation preserves the exact numerator and
denominator of predicted clearance. -/
public theorem predictedClearance_le_eighthTransportFloor_of_exactRadius
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate)
    (marginEq :
      ClearSheetContinuation.squareRootDerivativeMargin segment =
        (1 / 4 : Coordinate))
    (radiusEq : preparationRadius segment rootDiameter =
      (1 / 64 : Coordinate))
    (derivativeLower : (26 : Coordinate) ≤
      rootSampleDerivativeMajorant segment) :
    predictedClearance segment rootDiameter ≤
      (1 / 8 : Coordinate) ^ 2 / (4 * 65536) := by
  unfold predictedClearance linearizationMajorant
  rw [marginEq, radiusEq]
  have derivativePositive : (0 : Coordinate) <
      rootSampleDerivativeMajorant segment :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 26) (by omega)).trans_le derivativeLower
  have radiusPositive : (0 : Coordinate) < (1 / 64 : Coordinate) :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 1) (by omega))
      (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by omega))
  have denominatorPositive : (0 : Coordinate) <
      4 * (2 * rootSampleDerivativeMajorant segment * (1 / 64) ^ 2) :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 4) (by omega))
      (Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Order.Arithmetic.mul_pos_direct
          (Fraction.Cast.Order.natCast_pos_direct (n := 2) (by omega))
          derivativePositive)
        (Fraction.Order.Arithmetic.pow_pos_direct radiusPositive 2))
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
  have denominatorLower :
      4 * (2 * (26 : Coordinate) * (1 / 64) ^ 2) ≤
        4 * (2 * rootSampleDerivativeMajorant segment * (1 / 64) ^ 2) := by
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    · apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      · exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          derivativeLower (by decide)
      · exact Fraction.Order.Arithmetic.sq_nonneg_direct _
    · decide
  calc
    ((1 / 4 : Coordinate) * (1 / 64) ^ 2 -
          36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 ≤
        ((1 / 8 : Coordinate) ^ 2 / (4 * 65536)) *
          (4 * (2 * (26 : Coordinate) * (1 / 64) ^ 2)) := by
      let radius : Coordinate := 1 / 64
      let floor : Coordinate := (1 / 8) ^ 2 / (4 * 65536)
      have sixtyFourPositive : (0 : Coordinate) < 64 :=
        Fraction.Cast.Order.natCast_pos_direct (n := 64) (by omega)
      have sixtyFourNonzero : (64 : Coordinate) ≠ 0 := sixtyFourPositive.ne'
      have radiusCancel : radius * 64 = 1 := by
        dsimp only [radius]
        exact Fraction.Field.div_mul_cancel_of_ne _ _
          sixtyFourNonzero
      have radiusSqCancel : radius ^ 2 * 4096 = 1 := by
        rw [show (4096 : Coordinate) = 64 ^ 2 by ring1]
        rw [show radius ^ 2 * 64 ^ 2 = (radius * 64) ^ 2 by ring1,
          radiusCancel, one_pow]
      have radiusTimesTwo : radius * 2 = (1 / 32 : Coordinate) := by
        apply Fraction.Field.mul_right_cancel_of_ne
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 32) (by omega)).ne'
        calc
          (radius * 2) * (32 : Coordinate) = radius * 64 := by ring1
          _ = 1 := radiusCancel
          _ = (1 / 32 : Coordinate) * 32 :=
            (Fraction.Field.div_mul_cancel_of_ne _ _
              (Fraction.Cast.Order.natCast_pos_direct
                (n := 32) (by omega)).ne').symm
      have radiusSqTimesOneTwentyEight :
          radius ^ 2 * 128 = (1 / 32 : Coordinate) := by
        calc
          radius ^ 2 * 128 = (radius * 64) * (radius * 2) := by ring1
          _ = 1 / 32 := by rw [radiusCancel, radiusTimesTwo]; ring1
      have quarterTimesOneTwentyEight :
          (1 / 4 : Coordinate) * 128 = 32 := by
        calc
          (1 / 4 : Coordinate) * 128 = ((1 / 4) * 4) * 32 := by ring1
          _ = 1 * 32 := congrArg (fun value : Coordinate => value * 32)
            (Fraction.Field.div_mul_cancel_of_ne _ _
              (Fraction.Cast.Order.natCast_pos_direct
                (n := 4) (by omega)).ne')
          _ = 32 := by ring1
      have differenceScaled :
          ((1 / 4 : Coordinate) * radius ^ 2 -
              36 * 8 * (radius ^ 2) ^ 2) * 524288 = 23 := by
        rw [show (524288 : Coordinate) = 4096 * 128 by ring1]
        rw [show
          ((1 / 4 : Coordinate) * radius ^ 2 -
              36 * 8 * (radius ^ 2) ^ 2) * (4096 * 128) =
            ((1 / 4 : Coordinate) * 128) * (radius ^ 2 * 4096) -
              (36 * 8) * (radius ^ 2 * 4096) *
                (radius ^ 2 * 128) by ring1]
        rw [quarterTimesOneTwentyEight, radiusSqCancel,
          radiusSqTimesOneTwentyEight]
        have correction : (36 * 8 : Coordinate) * (1 / 32) = 9 := by
          calc
            (36 * 8 : Coordinate) * (1 / 32) =
                (9 * 32) * (1 / 32) := by ring1
            _ = 9 * ((1 / 32 : Coordinate) * 32) := by ring1
            _ = 9 * 1 := congrArg (fun value : Coordinate => 9 * value)
              (Fraction.Field.div_mul_cancel_of_ne _ _
                (Fraction.Cast.Order.natCast_pos_direct
                  (n := 32) (by omega)).ne')
            _ = 9 := by ring1
        calc
          (32 : Coordinate) * 1 - 36 * 8 * 1 * (1 / 32) =
              32 - (36 * 8) * (1 / 32) := by ring1
          _ = 32 - 9 := by rw [correction]
          _ = 23 := by ring1
      have eighthCancel : (1 / 8 : Coordinate) * 8 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne _ _
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 8) (by omega)).ne'
      have floorScaled : floor * 16777216 = 1 := by
        dsimp only [floor]
        have denominatorNonzero : (4 * 65536 : Coordinate) ≠ 0 :=
          (Fraction.Order.Arithmetic.mul_pos_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 4) (by omega))
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 65536) (by omega))).ne'
        rw [show (16777216 : Coordinate) = (4 * 65536) * 64 by ring1]
        rw [show (((1 / 8 : Coordinate) ^ 2 / (4 * 65536)) *
            ((4 * 65536) * 64)) =
          (((1 / 8 : Coordinate) ^ 2 / (4 * 65536)) *
            (4 * 65536)) * 64 by ring1,
          Fraction.Field.div_mul_cancel_of_ne _ _
            denominatorNonzero]
        rw [show (1 / 8 : Coordinate) ^ 2 * 64 =
          ((1 / 8 : Coordinate) * 8) ^ 2 by ring1,
          eighthCancel, one_pow]
      apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
        (c := (274877906944 : Coordinate)) _
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 274877906944) (by omega))
      calc
        (((1 / 4 : Coordinate) * (1 / 64) ^ 2 -
              36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2) * 274877906944 =
            529 := by
          change (((1 / 4 : Coordinate) * radius ^ 2 -
              36 * 8 * (radius ^ 2) ^ 2) ^ 2) * 274877906944 = 529
          rw [show (274877906944 : Coordinate) = 524288 ^ 2 by ring1]
          rw [show
            (((1 / 4 : Coordinate) * radius ^ 2 -
                36 * 8 * (radius ^ 2) ^ 2) ^ 2) * 524288 ^ 2 =
              (((1 / 4 : Coordinate) * radius ^ 2 -
                36 * 8 * (radius ^ 2) ^ 2) * 524288) ^ 2 by ring1,
            differenceScaled]
          ring1
        _ ≤ 832 := Fraction.Cast.Order.natCast_le_direct
          (m := 529) (n := 832) (by omega)
        _ = (((1 / 8 : Coordinate) ^ 2 / (4 * 65536)) *
              (4 * (2 * (26 : Coordinate) * (1 / 64) ^ 2))) *
                274877906944 := by
          change 832 = (floor * (4 * (2 * (26 : Coordinate) *
            radius ^ 2))) * 274877906944
          rw [show (274877906944 : Coordinate) = 16777216 * 16384 by ring1]
          rw [show (floor * (4 * (2 * (26 : Coordinate) * radius ^ 2))) *
              (16777216 * 16384) =
            (4 * 2 * 26) * (floor * 16777216) *
              (radius ^ 2 * 16384) by ring1,
            floorScaled]
          rw [show radius ^ 2 * 16384 =
            (radius ^ 2 * 4096) * 4 by ring1, radiusSqCancel]
          ring1
    _ ≤ ((1 / 8 : Coordinate) ^ 2 / (4 * 65536)) *
        (4 * (2 * rootSampleDerivativeMajorant segment *
          (1 / 64) ^ 2)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        denominatorLower
        (Fraction.Order.Field.div_nonneg_direct
          (Fraction.Order.Arithmetic.sq_nonneg_direct (1 / 8))
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 4) (by omega)).le
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 65536) (by omega)).le))

end

section

open Purelib.Data.Rat

/-- The rational constant thirty-two is strictly positive. -/
private theorem floorThirtyTwo_positive : (0 : Coordinate) < 32 := by
  rw [show (32 : Coordinate) = 2 ^ 5 by ring1]
  exact Fraction.Order.Arithmetic.pow_pos_direct (by decide) 5

/-- Every natural power of a nonzero rational value is nonzero.

The zero exponent uses the original nonzero unit. Each successor multiplies the retained nonzero preceding power by the
same nonzero base. -/
private theorem floor_pow_ne_zero (value : Coordinate)
    (nonzero : value ≠ 0) : ∀ exponent : Nat, value ^ exponent ≠ 0
  | 0 => by
      simpa only [pow_zero] using (show (1 : Coordinate) ≠ 0 by decide)
  | exponent + 1 => by
      rw [pow_succ]
      exact Fraction.Field.mul_ne_zero_direct
        (floor_pow_ne_zero value nonzero exponent) nonzero

end

/-- The rational constant sixty-four is nonzero. -/
private theorem floorSixtyFour_ne : (64 : Coordinate) ≠ 0 := by
  rw [show (64 : Coordinate) = 2 ^ 6 by ring1]
  exact floor_pow_ne_zero 2 (by decide) 6

open Purelib.Data.Rat in
/-- The cube of one quarter is one sixty-fourth. -/
private theorem oneQuarter_cube : (1 / 4 : Coordinate) ^ 3 = 1 / 64 := by
  rw [show (1 / 4 : Coordinate) ^ 3 =
    (1 / 4) * (1 / 4) * (1 / 4) by ring1]
  rw [Fraction.Field.div_mul_div_direct,
    Fraction.Field.div_mul_div_direct]
  apply Fraction.Field.div_eq_div_of_cross_mul
    (Fraction.Field.mul_ne_zero_direct
      (Fraction.Field.mul_ne_zero_direct (by decide) (by decide))
      (by decide))
    floorSixtyFour_ne
  ring1

/-- The rational constant 65536 is nonzero. -/
private theorem floorSixtyFiveThousandFiveHundredThirtySix_ne :
    (65536 : Coordinate) ≠ 0 := by
  rw [show (65536 : Coordinate) = 2 ^ 16 by ring1]
  exact floor_pow_ne_zero 2 (by decide) 16

section

open Purelib.Data.Rat

/-- The rational constant 65536 is strictly positive. -/
private theorem floorSixtyFiveThousandFiveHundredThirtySix_positive :
    (0 : Coordinate) < 65536 := by
  rw [show (65536 : Coordinate) = 2 ^ 16 by ring1]
  exact Fraction.Order.Arithmetic.pow_pos_direct (by decide) 16

/-- Eight times one thirty-second equals one quarter. -/
private theorem floorOneOverThirtyTwo_mul_eight :
    (1 / 32 : Coordinate) * 8 = 1 / 4 := by
  rw [show (8 : Coordinate) = 8 / 1 by decide,
    Fraction.Field.div_mul_div_direct]
  apply Fraction.Field.div_eq_div_of_cross_mul
    (Fraction.Field.mul_ne_zero_direct
      floorThirtyTwo_positive.ne' (by decide))
    (by decide)
  ring1

/-- Multiplying the half transport floor by 32768 gives one thirty-second. -/
private theorem clearanceFloor_mul_thirtyTwoThousandSevenHundredSixtyEight :
    ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 32768 = 1 / 32 := by
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (8 : Coordinate) ≠ 0 by decide)
  calc
    (((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 32768) * 8 =
        ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * (32768 * 8) := by ring1
    _ = ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) *
        (4 * 65536) := by
      rw [show (32768 : Coordinate) * 8 = 4 * 65536 by ring1]
    _ = (1 / 2 : Coordinate) ^ 2 :=
      Fraction.Field.div_mul_cancel_of_ne _ _
        (Fraction.Field.mul_ne_zero_direct (by decide)
          floorSixtyFiveThousandFiveHundredThirtySix_ne)
    _ = 1 / 4 := by decide
    _ = (1 / 32 : Coordinate) * 8 := floorOneOverThirtyTwo_mul_eight.symm

/-- One sixty-fourth is at most one thirty-second. -/
private theorem floorOneOverSixtyFour_le_oneOverThirtyTwo :
    (1 / 64 : Coordinate) ≤ 1 / 32 := by
  apply Fraction.Order.Field.div_le_div_of_nonneg_left_direct
    (by decide) floorThirtyTwo_positive
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  rw [show (64 : Coordinate) - 32 = 2 ^ 5 by ring1]
  exact Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) 5

/-- The half transport floor scaled by eighty and seventy-two times eight dominates one sixty-fourth. -/
private theorem oneOverSixtyFour_le_clearanceFloor_scaled :
    (1 / 64 : Coordinate) ≤
      (((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 80) * (72 * 8) := by
  have floorNonnegative : (0 : Coordinate) ≤
      (1 / 2 : Coordinate) ^ 2 / (4 * 65536) :=
    Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct (1 / 2))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        floorSixtyFiveThousandFiveHundredThirtySix_positive.le)
  have scaleLe : (32768 : Coordinate) ≤ 80 * (72 * 8) := by
    apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
    rw [show (80 : Coordinate) * (72 * 8) - 32768 =
      13 * 2 ^ 10 by ring1]
    exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) 10)
  calc
    (1 / 64 : Coordinate) ≤ 1 / 32 :=
      floorOneOverSixtyFour_le_oneOverThirtyTwo
    _ = ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 32768 :=
      clearanceFloor_mul_thirtyTwoThousandSevenHundredSixtyEight.symm
    _ ≤ ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) *
        (80 * (72 * 8)) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        scaleLe floorNonnegative
    _ = (((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 80) *
        (72 * 8) := by ring1

end

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- A derivative margin at most one quarter bounds predicted clearance by the half transport floor.

The retained Taylor constraint controls margin cubed, and the original majorant lower bound pays the exact positive
denominator. -/
public theorem predictedClearance_le_transportFloor
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter)
    (marginLe :
      ClearSheetContinuation.squareRootDerivativeMargin segment ≤
        (1 / 4 : Coordinate)) :
    predictedClearance segment rootDiameter ≤
      (1 / 2 : Coordinate) ^ 2 / (4 * 65536) := by
  let radius := preparationRadius segment rootDiameter
  let margin :=
    ClearSheetContinuation.squareRootDerivativeMargin segment
  let majorant := linearizationMajorant segment rootDiameter
  change
    (margin * radius ^ 2 - 36 * 8 * (radius ^ 2) ^ 2) ^ 2 /
        (4 * majorant) ≤ (1 / 2 : Coordinate) ^ 2 / (4 * 65536)
  have radiusSqNonnegative : (0 : Coordinate) ≤ radius ^ 2 :=
    Fraction.Order.Arithmetic.sq_nonneg_direct radius
  have marginNonnegative : (0 : Coordinate) ≤ margin :=
    (ClearSheetContinuation.squareRootDerivativeMargin_positive
      segment).le
  have taylorDenominatorPositive : (0 : Coordinate) < 72 * 8 :=
    Fraction.Order.Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 72) (by decide))
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 8) (by decide))
  have scaledTaylor : radius ^ 2 * (72 * 8) ≤ margin :=
    (Fraction.Order.Field.le_div_iff_pos
      taylorDenominatorPositive).mp
      (preparationRadius_sq_lt_taylorRatio segment
        rootDiameterPositive).le
  have correctionCoefficientNonnegative :
      (0 : Coordinate) ≤ 36 * 8 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 36) (by decide)).le
      (by decide)
  have correctionNonnegative :
      (0 : Coordinate) ≤ (36 * 8) * (radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct
      correctionCoefficientNonnegative
      (Fraction.Order.Arithmetic.sq_nonneg_direct (radius ^ 2))
  have correctionCoefficientLeMargin :
      (36 * 8) * radius ^ 2 ≤ margin := by
    calc
      (36 * 8) * radius ^ 2 = 1 * ((36 * 8) * radius ^ 2) := by ring1
      _ ≤ 2 * ((36 * 8) * radius ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide) (Fraction.Order.Arithmetic.mul_nonneg_direct
            correctionCoefficientNonnegative radiusSqNonnegative)
      _ = radius ^ 2 * (72 * 8) := by ring1
      _ ≤ margin := scaledTaylor
  have correctionLeFirst :
      (36 * 8) * (radius ^ 2) ^ 2 ≤ margin * radius ^ 2 := by
    calc
      (36 * 8) * (radius ^ 2) ^ 2 =
          ((36 * 8) * radius ^ 2) * radius ^ 2 := by ring1
      _ ≤ margin * radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          correctionCoefficientLeMargin radiusSqNonnegative
  have differenceNonnegative :
      (0 : Coordinate) ≤
        margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.sub_nonneg_direct correctionLeFirst
  have differenceLeFirst :
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
        margin * radius ^ 2 := by
    calc
      margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2 ≤
          margin * radius ^ 2 - 0 :=
        Fraction.Order.Arithmetic.sub_le_sub_left_direct
          correctionNonnegative (margin * radius ^ 2)
      _ = margin * radius ^ 2 := by ring1
  have numeratorLe :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        (margin * radius ^ 2) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      differenceNonnegative differenceLeFirst 2
  have marginCubeLe : margin ^ 3 ≤ (1 / 4 : Coordinate) ^ 3 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct marginNonnegative marginLe 3
  have scaledCore :
      (margin ^ 2 * radius ^ 2) * (72 * 8) ≤ (1 / 64 : Coordinate) := by
    calc
      (margin ^ 2 * radius ^ 2) * (72 * 8) =
          margin ^ 2 * (radius ^ 2 * (72 * 8)) := by ring1
      _ ≤ margin ^ 2 * margin :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          scaledTaylor (Fraction.Order.Arithmetic.sq_nonneg_direct margin)
      _ = margin ^ 3 := by ring1
      _ ≤ (1 / 4 : Coordinate) ^ 3 := marginCubeLe
      _ = 1 / 64 := oneQuarter_cube
  have coreLe : margin ^ 2 * radius ^ 2 ≤
      ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 80 := by
    apply Fraction.Order.Arithmetic.le_of_mul_le_mul_right_direct
      _ taylorDenominatorPositive
    exact scaledCore.trans oneOverSixtyFour_le_clearanceFloor_scaled
  have majorantLower : (80 : Coordinate) * radius ^ 2 ≤ 4 * majorant := by
    have base := twenty_mul_preparationRadius_sq_le_linearizationMajorant
      segment rootDiameter
    calc
      (80 : Coordinate) * radius ^ 2 = 4 * (20 * radius ^ 2) := by ring1
      _ ≤ 4 * majorant :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          base (by decide)
  have floorNonnegative : (0 : Coordinate) ≤
      (1 / 2 : Coordinate) ^ 2 / (4 * 65536) :=
    Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct (1 / 2))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        floorSixtyFiveThousandFiveHundredThirtySix_positive.le)
  have numeratorLeScaledMajorant :
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
        ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * (4 * majorant) := by
    calc
      (margin * radius ^ 2 - (36 * 8) * (radius ^ 2) ^ 2) ^ 2 ≤
          (margin * radius ^ 2) ^ 2 := numeratorLe
      _ = (margin ^ 2 * radius ^ 2) * radius ^ 2 := by ring1
      _ ≤ (((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 80) *
          radius ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          coreLe radiusSqNonnegative
      _ = ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) *
          (80 * radius ^ 2) := by ring1
      _ ≤ ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) *
          (4 * majorant) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          majorantLower floorNonnegative
  have denominatorPositive : (0 : Coordinate) < 4 * majorant :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment rootDiameterPositive)
  exact (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
    numeratorLeScaledMajorant

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- Build the centered winding-one state using the uniform restart input and its exact linearization majorant.

The state retains the same centered box, original parameter quadratic and boundary estimate at the selected sample. -/
@[expose] public def state
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    State.WindingOne.Basic.WindingOneState
      (rootPolynomialAt segment parameter)
      (restartInput segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox := by
  let restart := restartInput segment parameter inside owner
    rootDiameter rootDiameterPositive
  let isolation := inputAt segment parameter inside
  let majorant := linearizationMajorant segment rootDiameter
  let majorantPositive :=
    linearizationMajorant_positive segment rootDiameterPositive
  let majorantUpper : forall z : Gaussian,
      Box.Boundary.OnBoxBoundary restart.centeredBox z ->
        Data.Gaussian.Norm.Basic.normSq
          ((Newton.Box.Linearization.newtonLinearization
            (rootPolynomialAt segment parameter) restart.source).eval z) <=
          majorant := by
    intro z boundary
    change Data.Gaussian.Norm.Basic.normSq
        ((Newton.Box.Linearization.newtonLinearization
          (rootPolynomialAt segment parameter) restart.source).eval z) <=
      linearizationMajorant segment rootDiameter
    exact restart_newtonLinearization_boundary_le_majorant segment parameter
      inside owner rootDiameter rootDiameterPositive z boundary
  exact restart.centeredStateWithMajorant isolation.degreeAtLeastTwo majorant
    majorantPositive majorantUpper

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.RootIsolation in
/-- The constructed state's actual clearance equals the retained parameter-independent predicted formula.

The original centered restart retains the uniform radius and linearization majorant. Its exact derivative margin and
Taylor coefficient identify the displayed parameter-independent clearance. -/
@[simp] public theorem state_clearance_bound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (state segment parameter inside owner rootDiameter
      rootDiameterPositive).clearance.bound =
        predictedClearance segment rootDiameter := by
  unfold state
  rw [Newton.Restart.Separated.Basic.SeparatedRestartInput.centeredStateWithMajorant_clearance_bound]
  unfold predictedClearance Newton.Box.Square.Separated.separatedNewtonDominanceMargin
    Newton.Box.Square.Bounds.newtonErrorBudget
  rw [ClearSheetContinuation.squareRootDerivativeSeparation_margin]
  change
    (ClearSheetContinuation.squareRootDerivativeMargin segment *
          (restartInput segment parameter inside owner rootDiameter
            rootDiameterPositive).radius ^ 2 -
        36 * Bounds.Box.Taylor.denseTaylorRemainderBound
            (rootPolynomialAt segment parameter) (rootAmbient segment) *
          ((restartInput segment parameter inside owner rootDiameter
            rootDiameterPositive).radius ^ 2) ^ 2) ^ 2 /
      (4 * linearizationMajorant segment rootDiameter) = _
  rw [restartInput_radius, rootTaylor_formula segment parameter]

open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
/-- The retained common predicted clearance is strictly positive for a positive diameter request.

The original derivative separation and doubled Taylor budget certify a
positive common dominance margin. Its square divided by four times the
positive retained linearization majorant gives the displayed uniform bound. -/
public theorem predictedClearance_positive
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    0 < predictedClearance segment rootDiameter := by
  let parameter : Coordinate := 0
  have inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1 := by
    dsimp only [parameter]
    decide
  let separation := ClearSheetContinuation.squareRootDerivativeSeparation
    (rootAmbient := rootAmbient segment) segment parameter inside
  have radiusPositive := preparationRadius_positive segment rootDiameterPositive
  have taylorSmall := preparation_taylorSmall segment parameter rootDiameterPositive
  have dominancePositive := Newton.Box.Square.Separated.separatedNewtonDominanceMargin_pos
    separation radiusPositive taylorSmall
  have numeratorPositive := Fraction.Order.Arithmetic.pow_pos_direct dominancePositive 2
  unfold Newton.Box.Square.Separated.separatedNewtonDominanceMargin
    Newton.Box.Square.Bounds.newtonErrorBudget at numeratorPositive
  rewrite [ClearSheetContinuation.squareRootDerivativeSeparation_margin] at numeratorPositive
  change 0 <
    (ClearSheetContinuation.squareRootDerivativeMargin segment *
        preparationRadius segment rootDiameter ^ 2 -
      36 * Bounds.Box.Taylor.denseTaylorRemainderBound
        (rootPolynomialAt segment parameter) (rootAmbient segment) *
        (preparationRadius segment rootDiameter ^ 2) ^ 2) ^ 2 at numeratorPositive
  rewrite [rootTaylor_formula segment parameter] at numeratorPositive
  exact Fraction.Order.Field.div_pos_direct numeratorPositive
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (linearizationMajorant_positive segment rootDiameterPositive))

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Start the exact centered Newton track from the uniform restart input and original quadratic elimination.

The retained squarefree input, degree and majorant evidence belong to the same parameter quadratic and selected sample.
-/
@[expose] public def track
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Track.Basic.WindingOneTrack
      (rootPolynomialAt segment parameter)
      (restartInput segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox := by
  let restart := restartInput segment parameter inside owner
    rootDiameter rootDiameterPositive
  let isolation := inputAt segment parameter inside
  let majorant := linearizationMajorant segment rootDiameter
  let majorantPositive :=
    linearizationMajorant_positive segment rootDiameterPositive
  let majorantUpper : forall z : Gaussian,
      Box.Boundary.OnBoxBoundary restart.centeredBox z ->
        Data.Gaussian.Norm.Basic.normSq
          ((Newton.Box.Linearization.newtonLinearization
            (rootPolynomialAt segment parameter) restart.source).eval z) <=
          majorant := by
    intro z boundary
    change Data.Gaussian.Norm.Basic.normSq
        ((Newton.Box.Linearization.newtonLinearization
          (rootPolynomialAt segment parameter) restart.source).eval z) <=
      linearizationMajorant segment rootDiameter
    exact restart_newtonLinearization_boundary_le_majorant segment parameter
      inside owner rootDiameter rootDiameterPositive z boundary
  exact restart.centeredTrackWithMajorant isolation.squarefree
    (QuadraticAxisElimination.quadraticAxisElimination
      (polynomial.eval (segment.pointAt parameter)))
    isolation.degreeAtLeastTwo majorant majorantPositive
    majorantUpper

open Purelib.Polynomial in
/-- Package the uniformly prepared owner at the original segment parameter.

Its ambient box is exactly the restart input's centered box, and the retained track carries the common radius and
clearance guarantees. -/
@[expose] public def prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Owner (polynomial.eval (segment.pointAt parameter)) where
  parameterNonzero := segment.pointAt_eval_ne_zero parameter inside
  ambient := (restartInput segment parameter inside owner rootDiameter
    rootDiameterPositive).centeredBox
  track := track segment parameter inside owner rootDiameter
    rootDiameterPositive

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The prepared owner's initial box is exactly the uniform restart input's centered box.

The retained prepared owner starts from the same centered restart state. Its subsequent refinement program preserves
that exact original initial box. -/
@[simp] public theorem prepared_initial_box
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.box =
        (restartInput segment parameter inside owner rootDiameter
          rootDiameterPositive).centeredBox := by
  unfold prepared track Newton.Restart.Separated.Basic.SeparatedRestartInput.centeredTrackWithMajorant
    Track.Newton.Build.ofInitial
  rfl

open Purelib.Polynomial in
/-- The prepared owner's actual clearance is exactly the common predicted bound. -/
@[simp] public theorem prepared_clearance_bound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.clearance.bound =
        predictedClearance segment rootDiameter := by
  exact state_clearance_bound segment parameter inside owner
    rootDiameter rootDiameterPositive

open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The prepared initial box's squared diagonal is eight times the uniform radius squared. -/
@[simp] public theorem prepared_diagonalSq
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.box.diagonalSq =
        8 * preparationRadius segment rootDiameter ^ 2 := by
  change (restartInput segment parameter inside owner rootDiameter
    rootDiameterPositive).centeredBox.diagonalSq = _
  rw [Newton.Restart.Separated.Basic.SeparatedRestartInput.centeredBox_diagonalSq,
    restartInput_radius]

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The prepared squared diagonal is below the retained derivative-controlled diameter bound.

The exact prepared diagonal is eight times the retained radius square. The original strict Taylor-radius cap gives the
displayed derivative-controlled upper bound. -/
public theorem prepared_diagonal_lt_derivativeDiameterBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.box.diagonalSq <
        derivativeDiameterBound segment := by
  rw [prepared_diagonalSq segment parameter inside owner rootDiameterPositive]
  unfold derivativeDiameterBound
  exact Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
    (preparationRadius_sq_lt_taylorRatio segment rootDiameterPositive)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The prepared squared diagonal is below the requested positive target.

The diameter request is positive, and the retained dyadic diameter cap bounds the same preparation radius square. The
exact initial-box diagonal is strictly below the original request. -/
public theorem prepared_diagonal_lt
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (prepared segment parameter inside owner rootDiameter
      rootDiameterPositive).track.initial.box.diagonalSq < rootDiameter := by
  let radius := preparationRadius segment rootDiameter
  let diameterCap :=
    SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius (rootDiameter / 8)
  have radiusPositive : 0 < radius :=
    preparationRadius_positive segment rootDiameterPositive
  have radiusLe := preparationRadius_le_diameterCap segment rootDiameter
  have squareLe : radius ^ 2 <= diameterCap ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le radiusLe 2
  have targetPositive : 0 < rootDiameter / 8 :=
    Fraction.Order.Field.div_pos_direct rootDiameterPositive (by decide)
  have capSquareLt : diameterCap ^ 2 < rootDiameter / 8 :=
    SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_sq_lt targetPositive
  rw [prepared_diagonalSq segment parameter inside owner rootDiameterPositive]
  calc
    8 * radius ^ 2 <= 8 * diameterCap ^ 2 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct squareLe
        (by decide)
    _ < 8 * (rootDiameter / 8) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide) capSquareLt
    _ = rootDiameter := by
      calc
        8 * (rootDiameter / 8) = (rootDiameter / 8) * 8 :=
          Fraction.Field.mul_comm _ _
        _ = rootDiameter :=
          Fraction.Field.div_mul_cancel_of_ne rootDiameter 8
            (by decide)

open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Start a centered bridge track using the same selected sample and the owner-specific restart input.

The explicit local linearization majorant and original quadratic elimination retain a common comparison track for both
owners. -/
@[expose] public def bridgeTrack
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    (rootDiameter : Coordinate) (rootDiameterPositive : 0 < rootDiameter) :
    Track.Basic.WindingOneTrack
      (rootPolynomialAt segment parameter)
      (bridgeRestartInput segment parameter inside owner rootDiameter
        rootDiameterPositive).centeredBox := by
  let restart := bridgeRestartInput segment parameter inside owner
    rootDiameter rootDiameterPositive
  let isolation := inputAt segment parameter inside
  let majorant :=
    Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant
      (rootPolynomialAt segment parameter) owner.track.initial.box
      (bridgeRadius segment owner rootDiameter)
  let majorantPositive :=
    Newton.Box.Square.Bounds.separatedNewtonLinearizationMajorant_pos
      (rootPolynomialAt segment parameter) owner.track.initial.box
      (bridgeRadius_positive segment owner rootDiameterPositive)
  let majorantUpper : forall z : Gaussian,
      Box.Boundary.OnBoxBoundary restart.centeredBox z ->
        Data.Gaussian.Norm.Basic.normSq
          ((Newton.Box.Linearization.newtonLinearization
            (rootPolynomialAt segment parameter) restart.source).eval z) <=
          majorant := fun _z boundary =>
    Newton.Box.Square.Bounds.newtonLinearization_boundary_le_majorant
      restart.sourceRefines restart.radiusPositive boundary
  exact restart.centeredTrackWithMajorant isolation.squarefree
    (QuadraticAxisElimination.quadraticAxisElimination
      (polynomial.eval (segment.pointAt parameter)))
    isolation.degreeAtLeastTwo majorant majorantPositive
    majorantUpper

open Purelib.Polynomial in
/-- The bridge initial box lies strictly inside the exact original owner's initial box.

The retained bridge restart's original margin bounds place its centered initial box strictly inside the same original
owner's initial box. -/
public theorem bridgeTrack_initial_strict_owner
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeTrack segment parameter inside owner rootDiameter
      rootDiameterPositive).initial.box.StrictInterior
        owner.track.initial.box := by
  change (bridgeRestartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).centeredBox.StrictInterior owner.track.initial.box
  exact (bridgeRestartInput segment parameter inside owner rootDiameter
    rootDiameterPositive).centeredBox_strict

open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.RootIsolation in
/-- The bridge initial box lies strictly inside the exact uniformly prepared owner's initial box.

The two retained restarts use the same Newton center, and the bridge radius is strictly smaller. Their actual centered
boxes satisfy the displayed strict containment. -/
public theorem bridgeTrack_initial_strict_prepared
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (parameter : Coordinate)
    (inside : (0 : Coordinate) <= parameter ∧ parameter <= 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter)))
    {rootDiameter : Coordinate} (rootDiameterPositive : 0 < rootDiameter) :
    (bridgeTrack segment parameter inside owner rootDiameter
      rootDiameterPositive).initial.box.StrictInterior
        (prepared segment parameter inside owner rootDiameter
          rootDiameterPositive).track.initial.box := by
  change (bridgeRestartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).centeredBox.StrictInterior
    (restartInput segment parameter inside owner rootDiameter
      rootDiameterPositive).centeredBox
  unfold Newton.Restart.Separated.Basic.SeparatedRestartInput.centeredBox
  change
    (Box.Square.Centered.Affine.centeredSquare
      (Newton.Box.Anchor.anchorNewtonCenter
        (rootPolynomialAt segment parameter)
        (bridgeRestartInput segment parameter inside owner rootDiameter
          rootDiameterPositive).source)
      (bridgeRadius segment owner rootDiameter)
      (bridgeRadius_positive segment owner rootDiameterPositive).le).StrictInterior
    (Box.Square.Centered.Affine.centeredSquare
      (Newton.Box.Anchor.anchorNewtonCenter
        (rootPolynomialAt segment parameter)
        (restartInput segment parameter inside owner rootDiameter
          rootDiameterPositive).source)
      (preparationRadius segment rootDiameter)
      (preparationRadius_positive segment rootDiameterPositive).le)
  rw [restart_newtonCenter_eq segment parameter inside owner
    rootDiameter rootDiameterPositive]
  exact Box.Square.Centered.centeredSquare_strictInterior_of_lt _
    (bridgeRadius_positive segment owner rootDiameterPositive).le
    (preparationRadius_positive segment rootDiameterPositive).le
    (bridgeRadius_lt_preparation segment owner rootDiameterPositive)

attribute [irreducible] prepared

end Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
