module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Algebra.Field.ExplicitField
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Based
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Request.Division
import Purelib.Approximation.Rational.Budget.Quotient
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Value
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Observation
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Quotient
import Purelib.Data.Gaussian.Power
public import Purelib.Data.Gaussian.Power.Bounds
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Integration.Path.Lifted.Model
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.ComparisonAllowance
public import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.Riemann.Topology.SquareRootContinuationChain

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.Curves.Hyperelliptic.Sheets.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Integration.Polynomial.Gaussian

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

@[expose] public section

/-!
# Shrinking constant models on prepared hyperelliptic cells

A prepared edge keeps every later square-root candidate inside one explicitly
small source box.  Combining that finite fact with the rational power and
quotient estimates produces a constant coefficient model whose allowance is
linear in the squared edge displacement and the requested root-box diameter.
-/

namespace Purelib.Riemann.Integration.PreparedConstantModels

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Data.Rat in
/-- The exact rational coordinate carrier of model bounds and tolerances. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier. -/
abbrev Gaussian := Basic.Canonical
/-- The original rational box retaining its coordinate bounds. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The original square-root owner indexed by its exact radicand. -/
abbrev Owner := Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
/-- The retained unit-interval endpoint of a cleared segment. -/
abbrev Endpoint := Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint
/-- The exact endpoint and positive root-diameter request for preparation. -/
abbrev StepRequest := Purelib.Riemann.Branches.PreparedSheetContinuation.StepRequest
/-- The original polynomial cell model retaining endpoints, allowance, and observations. -/
abbrev CellModel := Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel
/-- The original coherent Gaussian name with its executable approximation process. -/
abbrev CoherentNamed := Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

/-- Sixteen is nonnegative in the rational coordinate carrier. -/
theorem sixteen_nonnegative :
    (0 : Coordinate) <= 16 := by decide

/-- Four is at most sixteen in the rational coordinate carrier. -/
private theorem four_le_sixteen :
    (4 : Coordinate) <= 16 := by decide

/-- Nine is at most sixteen in the rational coordinate carrier. -/
private theorem nine_le_sixteen :
    (9 : Coordinate) <= 16 := by decide

/-- Fourteen is at most sixteen in the rational coordinate carrier. -/
private theorem fourteen_le_sixteen :
    (14 : Coordinate) <= 16 := by decide

/-- Compute a squared-norm lower bound from the positive lower or negative upper endpoint, using zero when neither
applies.

The original sign comparisons select the same positive lower endpoint,
negative upper endpoint or zero, without changing either squared value. -/
def intervalSqLower (lower upper : Coordinate) : Coordinate :=
  if 0 < lower then lower ^ 2 else if upper < 0 then upper ^ 2 else 0

section
open Purelib.Data.Rat
/-- The interval squared-norm lower bound is nonnegative. -/
private theorem intervalSqLower_nonnegative (lower upper : Coordinate) :
    0 <= intervalSqLower lower upper := by
  unfold intervalSqLower
  split
  · exact Fraction.Order.Arithmetic.sq_nonneg_direct lower
  · split
    · exact Fraction.Order.Arithmetic.sq_nonneg_direct upper
    · exact le_rfl

/-- An interval's computed lower bound is no greater than the square of any contained coordinate.

The retained sign branch selects the same interval endpoint or zero.
Direct rational order reversal compares both squares in the negative branch. -/
private theorem intervalSqLower_le_sq {lower value upper : Coordinate}
    (lowerLe : lower <= value) (valueLe : value <= upper) :
    intervalSqLower lower upper <= value ^ 2 := by
  unfold intervalSqLower
  by_cases lowerPositive : 0 < lower
  · rw [if_pos lowerPositive]
    rw [pow_two, pow_two]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct lowerLe lowerLe
      lowerPositive.le (lowerPositive.le.trans lowerLe)
  · rw [if_neg lowerPositive]
    by_cases upperNegative : upper < 0
    · rw [if_pos upperNegative]
      have negOrder : -upper <= -value :=
        Fraction.Order.Arithmetic.neg_le_neg_direct valueLe
      have negUpperNonnegative : 0 <= -upper := by
        have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct upperNegative.le
        simpa only [neg_zero] using reversed
      have negValueNonnegative : 0 <= -value :=
        by
          have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct (valueLe.trans upperNegative.le)
          simpa only [neg_zero] using reversed
      rw [pow_two, pow_two]
      calc
        upper * upper = (-upper) * (-upper) := by ring1
        _ <= (-value) * (-value) :=
          Fraction.Order.Arithmetic.mul_le_mul_direct negOrder negOrder
            negUpperNonnegative negValueNonnegative
        _ = value * value := by ring1
    · rw [if_neg upperNegative]
      exact Fraction.Order.Arithmetic.sq_nonneg_direct value

end

/-- Sum the interval squared-norm lower bounds for the two coordinate intervals of the original box.

The original horizontal and vertical interval floors use the exact
retained box endpoints; their unchanged sum is the same rational estimate. -/
def boxNormSqLower (box : Box) : Coordinate :=
  intervalSqLower box.xLower box.xUpper +
    intervalSqLower box.yLower box.yUpper

/-- The box's computed squared-norm lower bound is nonnegative. -/
private theorem boxNormSqLower_nonnegative (box : Box) :
    0 <= boxNormSqLower box := by
  exact add_nonneg (intervalSqLower_nonnegative _ _)
    (intervalSqLower_nonnegative _ _)

open Purelib.Data.Gaussian in
/-- The computed box lower bound bounds the squared norm of every contained Gaussian value. -/
private theorem boxNormSqLower_le_of_contains {box : Box}
    {candidate : Gaussian} (inside : box.Contains candidate) :
    boxNormSqLower box <=
      Data.Gaussian.Norm.Basic.normSq candidate := by
  exact add_le_add
    (intervalSqLower_le_sq inside.1 inside.2.1)
    (intervalSqLower_le_sq inside.2.2.1 inside.2.2.2)

/-- Compute the squared-norm lower bound for sums of two values in the same original box.

The exact doubled box endpoints bound sums of two values in that same
box. Their unchanged horizontal and vertical squared floors are added. -/
def boxSumNormSqLower (box : Box) : Coordinate :=
  intervalSqLower (2 * box.xLower) (2 * box.xUpper) +
    intervalSqLower (2 * box.yLower) (2 * box.yUpper)

/-- The computed lower bound for the sum of two box-contained values is nonnegative. -/
private theorem boxSumNormSqLower_nonnegative (box : Box) :
    0 <= boxSumNormSqLower box := by
  exact add_nonneg (intervalSqLower_nonnegative _ _)
    (intervalSqLower_nonnegative _ _)

open Purelib.Data.Gaussian in
/-- The computed sum lower bound bounds the squared norm of the sum of two values in the original box. -/
private theorem boxSumNormSqLower_le_of_contains {box : Box}
    {left right : Gaussian} (leftInside : box.Contains left)
    (rightInside : box.Contains right) :
    boxSumNormSqLower box <=
      Data.Gaussian.Norm.Basic.normSq (left + right) := by
  apply add_le_add
  · apply intervalSqLower_le_sq
    · calc
        2 * box.xLower = box.xLower + box.xLower := by ring1
        _ <= left.re + right.re := add_le_add leftInside.1 rightInside.1
    · calc
        left.re + right.re <= box.xUpper + box.xUpper :=
          add_le_add leftInside.2.1 rightInside.2.1
        _ = 2 * box.xUpper := by ring1
  · apply intervalSqLower_le_sq
    · calc
        2 * box.yLower = box.yLower + box.yLower := by ring1
        _ <= left.im + right.im :=
          add_le_add leftInside.2.2.1 rightInside.2.2.1
    · calc
        left.im + right.im <= box.yUpper + box.yUpper :=
          add_le_add leftInside.2.2.2 rightInside.2.2.2
        _ = 2 * box.yUpper := by ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Bound the squared distance between two approximate square roots using their residuals and radicand displacement.

A positive lower bound for the squared norm of their sum permits division; the numerator is four times the sum of the
two residual bounds and parameter-movement bound. -/
theorem normSq_root_sub_le_of_residuals
    {leftRoot rightRoot leftParameter rightParameter : Gaussian}
    {sumLower leftResidual parameterMovement rightResidual : Coordinate}
    (sumPositive : 0 < sumLower)
    (sumBound : sumLower <=
      Data.Gaussian.Norm.Basic.normSq (leftRoot + rightRoot))
    (leftResidualBound :
      Data.Gaussian.Norm.Basic.normSq
          (leftRoot * leftRoot - leftParameter) <= leftResidual)
    (parameterMovementBound :
      Data.Gaussian.Norm.Basic.normSq
          (leftParameter - rightParameter) <= parameterMovement)
    (rightResidualBound :
      Data.Gaussian.Norm.Basic.normSq
          (rightRoot * rightRoot - rightParameter) <= rightResidual) :
    Data.Gaussian.Norm.Basic.normSq (leftRoot - rightRoot) <=
      4 * (leftResidual + parameterMovement + rightResidual) / sumLower := by
  have identity :
      (leftRoot - rightRoot) * (leftRoot + rightRoot) =
        (leftRoot * leftRoot - leftParameter) +
            (leftParameter - rightParameter) -
          (rightRoot * rightRoot - rightParameter) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im,
        Basic.mul_re,
        Basic.mul_im] <;> ring1
  have rightResidualNonnegative : 0 <= rightResidual :=
    (Norm.Basic.normSq_nonneg _).trans
      rightResidualBound
  have firstTwo :
      Data.Gaussian.Norm.Basic.normSq
          ((leftRoot * leftRoot - leftParameter) +
            (leftParameter - rightParameter)) <=
        2 * (leftResidual + parameterMovement) := by
    exact (Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add leftResidualBound parameterMovementBound) (by decide))
  have residualBound :
      Data.Gaussian.Norm.Basic.normSq
          ((leftRoot * leftRoot - leftParameter) +
              (leftParameter - rightParameter) -
            (rightRoot * rightRoot - rightParameter)) <=
        4 * (leftResidual + parameterMovement + rightResidual) := by
    calc
      Data.Gaussian.Norm.Basic.normSq
          ((leftRoot * leftRoot - leftParameter) +
              (leftParameter - rightParameter) -
            (rightRoot * rightRoot - rightParameter)) <=
          2 *
            (Data.Gaussian.Norm.Basic.normSq
                ((leftRoot * leftRoot - leftParameter) +
                  (leftParameter - rightParameter)) +
              Data.Gaussian.Norm.Basic.normSq
                (rightRoot * rightRoot - rightParameter)) :=
        Norm.Bounds.normSq_sub_le_two _ _
      _ <= 2 * (2 * (leftResidual + parameterMovement) + rightResidual) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add firstTwo rightResidualBound) (by decide)
      _ <= 4 * (leftResidual + parameterMovement + rightResidual) := by
        have twiceLeFour : 2 * rightResidual <= 4 * rightResidual :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (show (2 : Coordinate) <= 4 by decide) rightResidualNonnegative
        calc
          2 * (2 * (leftResidual + parameterMovement) + rightResidual) =
              4 * (leftResidual + parameterMovement) + 2 * rightResidual := by
            ring1
          _ <= 4 * (leftResidual + parameterMovement) + 4 * rightResidual :=
            add_le_add le_rfl twiceLeFour
          _ = 4 * (leftResidual + parameterMovement + rightResidual) := by
            ring1
  apply (Fraction.Order.Field.le_div_iff_pos sumPositive).2
  calc
    Data.Gaussian.Norm.Basic.normSq (leftRoot - rightRoot) *
        sumLower <=
      Data.Gaussian.Norm.Basic.normSq (leftRoot - rightRoot) *
        Data.Gaussian.Norm.Basic.normSq (leftRoot + rightRoot) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
        (Norm.Basic.normSq_nonneg _)
    _ = Data.Gaussian.Norm.Basic.normSq
        ((leftRoot - rightRoot) * (leftRoot + rightRoot)) := by
      rw [Norm.Basic.normSq_mul]
    _ = Data.Gaussian.Norm.Basic.normSq
        ((leftRoot * leftRoot - leftParameter) +
            (leftParameter - rightParameter) -
          (rightRoot * rightRoot - rightParameter)) := by rw [identity]
    _ <= 4 * (leftResidual + parameterMovement + rightResidual) :=
      residualBound

open Purelib in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Polynomial in
open Purelib.Riemann.Branches in
set_option genInjectivity false in
/-- A cleared segment step with its original root owner, exact preparation cache, request, and sheet index.

The certificate retains ambient containment, ordered endpoints, and enough prepared clearance for the whole requested
variation. It is indexed by the original curve and differential. -/
structure PreparedEdge {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus) where
  /-- The original ambient box of the cleared segment. -/ ambient : Box
  /-- The original start point of the cleared segment. -/ start : Gaussian
  /-- The original finish point of the cleared segment. -/ finish : Gaussian
  /-- The exact polynomial segment with its retained nonzero clearance. -/ segment : Geometry.ClearPath.ClearSegment
    curve.polynomial ambient start finish
  /-- The original segment lies within its retained ambient box. -/ within : segment.WithinAmbient
  /-- The original source endpoint of the prepared step. -/ left : Endpoint
  /-- The exact original square-root owner at the source polynomial value. -/ owner : Owner (curve.polynomial.eval
    (segment.pointAt left.parameter))
  /-- The retained target endpoint and positive root-diameter request. -/ request : StepRequest
  /-- The exact prepared-owner cache bound to the original source and request. -/ cached :
    PreparedSheetContinuation.CachedSource segment left
    owner request
  /-- The original source parameter is no greater than the request parameter. -/ ordered : left.parameter <=
    request.endpoint.parameter
  /-- The requested variation fits the actual canonical prepared clearance. -/ small :
    ClearSheetContinuation.variationBound segment
    left.parameter request.endpoint.parameter <
      (PreparedSheetContinuation.prepared segment left owner
        request).track.initial.clearance.bound
  /-- The retained original sheet index. -/ sheet : Fin 2

constructive_injectivity PreparedEdge

namespace PreparedEdge

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials

/-- The local source parameter zero lies in the unit interval. -/
theorem baseInside {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (_prepared : PreparedEdge curve differential) :
    (0 : Coordinate) <= 0 ∧ (0 : Coordinate) <= 1 := by decide

/-- Restrict the original cleared segment to the retained source and request endpoints. -/
def localSegment {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :=
  PreparedModels.edge curve prepared.segment
    prepared.within prepared.left prepared.request

/-- Read the exact affine point on the retained local segment at a rational fraction. -/
def point {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate) :
    Gaussian :=
  prepared.localSegment.pointAt fraction

section
open Purelib.Riemann.Branches
/-- The local source point is exactly the original segment point at the retained left endpoint. -/
@[simp] theorem point_zero_eq_source {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.point 0 =
      prepared.segment.pointAt prepared.left.parameter := by
  unfold point localSegment PreparedModels.edge
  simpa only [PreparedSheetContinuation.parameterAt_zero] using
    (PreparedSheetContinuation.pointAt_parameterAt
      prepared.segment prepared.within prepared.left prepared.request 0).symm

/-- The local source point is exactly the original segment point at the retained left endpoint. -/
@[simp] theorem point_zero {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.point 0 =
      prepared.segment.pointAt prepared.left.parameter := by
  unfold point localSegment PreparedModels.edge
  simpa only [PreparedSheetContinuation.parameterAt_zero] using
    (PreparedSheetContinuation.pointAt_parameterAt
      prepared.segment prepared.within prepared.left prepared.request 0).symm

/-- The local target point is exactly the original segment point at the request endpoint. -/
@[simp] theorem point_one {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.point 1 =
      prepared.segment.pointAt prepared.request.endpoint.parameter := by
  unfold point localSegment PreparedModels.edge
  simpa only [PreparedSheetContinuation.parameterAt_one] using
    (PreparedSheetContinuation.pointAt_parameterAt
      prepared.segment prepared.within prepared.left prepared.request 1).symm

end

/-- Read the certified nonzero sheet value using the exact prepared-owner cache at the requested fraction. -/
def sheetValue {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :=
  PreparedModels.sheetValueAtCached curve differential
    prepared.segment prepared.within prepared.left prepared.owner
      prepared.request prepared.cached prepared.ordered prepared.small
        prepared.sheet fraction inside

/-- Read the coherent differential coefficient from the cached sheet value at the exact local point. -/
def coefficient {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) : CoherentNamed :=
  PreparedModels.coefficientAtCached curve differential
    prepared.segment prepared.within prepared.left prepared.owner
      prepared.request prepared.cached prepared.ordered prepared.small
        prepared.sheet fraction inside

open Purelib.Approximation.Gaussian in
/-- Read the coherent root name from the cached direct query owner at the requested fraction. -/
@[irreducible] def rootName {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Name.Basic.Named :=
  (PreparedModels.rootAtCached curve prepared.segment
    prepared.within prepared.left prepared.owner prepared.request
      prepared.cached prepared.ordered prepared.small fraction inside).value.name

section
open Purelib.Approximation.Gaussian
open Purelib.Riemann.Branches
/-- Read the root name of canonical preparation at the original source endpoint. -/
@[irreducible] def preparedRootName {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    Name.Basic.Named :=
  PreparedSheetContinuation.preparedRootName prepared.segment
    prepared.left prepared.owner prepared.request

/-- Read the transported root name at the retained request endpoint. -/
@[irreducible] def transportedRootName {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    Name.Basic.Named :=
  PreparedSheetContinuation.transportedRootName prepared.segment
    prepared.within prepared.left prepared.owner prepared.request prepared.small

end

open Purelib.Riemann.Branches in
open Purelib.RootIsolation.SquareRoot.Clearance in
/-- Transport the retained cached owner directly to the interpolated radicand with the original transport reserve.

The supplied fraction and interval evidence determine the exact target, and the cache equality transfers the original
squared-displacement certificate. -/
def directQueryOwner {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Owner (curve.polynomial.eval (prepared.segment.pointAt
      (PreparedSheetContinuation.parameterAt prepared.left
        prepared.request fraction))) :=
  ExactQuadraticOwnerClearance.reservedTransport
    prepared.cached.preparedOwner
      (prepared.segment.pointAt_eval_ne_zero
        (PreparedSheetContinuation.parameterAt prepared.left
          prepared.request fraction)
        (PreparedSheetContinuation.parameterAt_inside prepared.left
          prepared.request prepared.ordered fraction inside))
      (by
        rw [prepared.cached.preparedOwner_eq]
        exact PreparedSheetContinuation.pointNormSmall
          prepared.segment prepared.within prepared.left prepared.owner
            prepared.request prepared.ordered prepared.small fraction inside)
      (PreparedSheetContinuation.transportReserve prepared.segment
        prepared.left prepared.request)

section
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
/-- The root-name query reads exactly the retained direct query owner's name. -/
theorem rootName_eq_directQueryOwnerRootName {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    prepared.rootName fraction inside =
      SquareRootTrackEquivalence.ownerRootName
        (prepared.segment.pointAt_eval_ne_zero
          (PreparedSheetContinuation.parameterAt prepared.left
            prepared.request fraction)
          (PreparedSheetContinuation.parameterAt_inside
            prepared.left prepared.request prepared.ordered fraction inside))
        (prepared.directQueryOwner fraction inside) := by
  unfold rootName directQueryOwner
    PreparedModels.rootAtCached
  rfl

/-- The sheet-value query reads exactly the retained direct query owner's name. -/
theorem sheetValue_name_eq_directQueryOwnerRootName {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (prepared.sheetValue fraction inside).value.name =
      SquareRootTrackEquivalence.ownerRootName
        (prepared.segment.pointAt_eval_ne_zero
          (PreparedSheetContinuation.parameterAt prepared.left
            prepared.request fraction)
          (PreparedSheetContinuation.parameterAt_inside
            prepared.left prepared.request prepared.ordered fraction inside))
        (prepared.directQueryOwner fraction inside) := by
  have same := prepared.rootName_eq_directQueryOwnerRootName fraction inside
  unfold rootName at same
  unfold sheetValue
    PreparedModels.sheetValueAtCached
  exact same

end

section
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Riemann.Branches
open Purelib.Riemann.RootContinuation
/-- The prepared source root and its exact zero-fraction query name equivalent roots. -/
def preparedRootEquivalent_baseQuery {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    Equivalence.NamedEquivalent prepared.preparedRootName
      (prepared.rootName 0 prepared.baseInside) := by
  let source := PreparedSheetContinuation.prepared
    prepared.segment prepared.left prepared.owner prepared.request
  have sameSmall :
      Data.Gaussian.Norm.Basic.normSq
          (curve.polynomial.eval
              (prepared.segment.pointAt prepared.left.parameter) -
            curve.polynomial.eval
              (prepared.segment.pointAt prepared.left.parameter)) <
        source.track.initial.clearance.bound := by
    rw [Basic.sub_self,
      Norm.Basic.normSq_zero]
    exact source.track.initial.clearance.positive
  have preparedToGeneric :=
    SquareRootTrackEquivalence.rootEquivalent_advance_same
      (prepared.segment.pointAt_eval_ne_zero prepared.left.parameter
        prepared.left.inside) source (by simpa only [Norm.Basic.normSq_eq_canonical] using sameSmall)
  have genericToDirect :=
    PreparedSheetContinuation.reservedTransportRootEquivalentGeneric
      source
      (prepared.segment.pointAt_eval_ne_zero prepared.left.parameter
        prepared.left.inside)
      sameSmall
      (PreparedSheetContinuation.transportReserve prepared.segment
        prepared.left prepared.request)
  have equivalent := Equivalence.NamedEquivalent.trans
    preparedToGeneric genericToDirect
  unfold PreparedEdge.preparedRootName PreparedEdge.rootName
  rw [PreparedModels.rootAtCached_zero_name_eq_zeroMoveRootName]
  unfold PreparedSheetContinuation.preparedRootName
    PreparedSheetContinuation.zeroMoveRootName
  exact equivalent

/-- The original source owner and the cached zero-fraction query name equivalent roots. -/
def ownerRootEquivalent_baseQuery {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    Equivalence.NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName
        (prepared.segment.pointAt_eval_ne_zero prepared.left.parameter
          prepared.left.inside) prepared.owner)
      (prepared.rootName 0 prepared.baseInside) := by
  unfold rootName
  have sourceToPrepared :=
    PreparedSheetContinuation.sourceRootEquivalent
      prepared.segment prepared.left prepared.owner prepared.request
  let source := prepared.cached.preparedOwner
  let sourceNonzero := prepared.segment.pointAt_eval_ne_zero
    prepared.left.parameter prepared.left.inside
  have sourceToCached : Equivalence.NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName sourceNonzero
        prepared.owner)
      (SquareRootTrackEquivalence.ownerRootName sourceNonzero
        source) := by
    change Equivalence.NamedEquivalent
      (SquareRootTrackEquivalence.ownerRootName sourceNonzero
        prepared.owner)
      (SquareRootTrackEquivalence.ownerRootName sourceNonzero
        prepared.cached.preparedOwner)
    rw [prepared.cached.preparedOwner_eq]
    exact sourceToPrepared
  let moveSmall : Data.Gaussian.Norm.Basic.normSq
      (curve.polynomial.eval
          (prepared.segment.pointAt prepared.left.parameter) -
        curve.polynomial.eval
          (prepared.segment.pointAt prepared.left.parameter)) <
        source.track.initial.clearance.bound := by
    change Data.Gaussian.Norm.Basic.normSq
      (curve.polynomial.eval
          (prepared.segment.pointAt prepared.left.parameter) -
        curve.polynomial.eval
          (prepared.segment.pointAt prepared.left.parameter)) <
        prepared.cached.preparedOwner.track.initial.clearance.bound
    rw [prepared.cached.preparedOwner_eq]
    simpa only [PreparedSheetContinuation.parameterAt_zero] using
      (PreparedSheetContinuation.pointNormSmall prepared.segment
        prepared.within prepared.left prepared.owner prepared.request
          prepared.ordered prepared.small 0 prepared.baseInside)
  have preparedToGenericZero :=
    SquareRootTrackEquivalence.rootEquivalent_advance_same
      sourceNonzero source (by simpa only [Norm.Basic.normSq_eq_canonical] using moveSmall)
  have genericToDirectZero :=
    PreparedSheetContinuation.reservedTransportRootEquivalentGeneric
      source sourceNonzero moveSmall
      (PreparedSheetContinuation.transportReserve prepared.segment
        prepared.left prepared.request)
  have preparedToZero := Equivalence.NamedEquivalent.trans
    preparedToGenericZero genericToDirectZero
  have sourceToZero := Equivalence.NamedEquivalent.trans
    sourceToCached preparedToZero
  unfold PreparedModels.rootAtCached
  convert sourceToZero using 1
  apply
    PreparedSheetContinuation.reservedTransportRootName_proof_irrel

end

open Purelib.Approximation.Gaussian in
/-- Equal query points and equivalent retained root names give equivalent differential coefficient names.

The comparison keeps both prepared edges and their original root witnesses, including the nonzero certificates used by
division. -/
def coefficientEquivalent_of_rootEquivalent {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (point_eq : parent.point fraction = child.point 0)
    (rootEquivalent :
      Equivalence.NamedEquivalent
        (parent.rootName fraction inside)
        (child.rootName 0 child.baseInside)) :
    Equivalence.NamedEquivalent
      (parent.coefficient fraction inside).name
      (child.coefficient 0 child.baseInside).name := by
  let parentRoot := PreparedModels.rootAtCached curve
    parent.segment parent.within parent.left parent.owner parent.request
      parent.cached parent.ordered parent.small fraction inside
  let childRoot := PreparedModels.rootAtCached curve
    child.segment child.within child.left child.owner child.request
      child.cached child.ordered child.small 0 child.baseInside
  have roots : Equivalence.NamedEquivalent
      parentRoot.value.name childRoot.value.name := by
    unfold rootName at rootEquivalent
    simpa only [parentRoot, childRoot] using rootEquivalent
  have coefficients := Value.differentialValue_respects_sheet differential
    (child.point 0) parentRoot.value childRoot.value parentRoot.apart
      childRoot.apart roots
  unfold coefficient
    PreparedModels.coefficientAtCached
  change Equivalence.NamedEquivalent
    (Value.differentialValue differential (parent.point fraction)
      parentRoot.value parentRoot.apart).name
    (Value.differentialValue differential (child.point 0)
      childRoot.value childRoot.apart).name
  rw [point_eq]
  exact coefficients

open Purelib.Data.Gaussian in
/-- The squared displacement between the retained local segment's target and source points. -/
def pointMovement {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  Data.Gaussian.Norm.Basic.normSq
    (prepared.point 1 - prepared.point 0)

/-- The squared diagonal of the initial box read from the exact prepared-owner cache. -/
def preparedRootDiameter {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.cached.preparedOwner.track.initial.box.diagonalSq

open Purelib.Riemann.Branches in
/-- The cached prepared diameter equals the diameter of canonical preparation. -/
theorem preparedRootDiameter_eq_canonical {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.preparedRootDiameter =
      (PreparedSheetContinuation.prepared prepared.segment
        prepared.left prepared.owner
        prepared.request).track.initial.box.diagonalSq := by
  unfold preparedRootDiameter
  rw [prepared.cached.preparedOwner_eq]

open Purelib.Riemann.RootContinuation in
/-- The actual prepared root box has positive squared diameter. -/
theorem preparedRootDiameter_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 < prepared.preparedRootDiameter := by
  exact CoherentRoot.scale_positive
    prepared.cached.preparedOwner.track

open Purelib.Riemann.Branches in
/-- The actual prepared squared diameter is strictly below the original request. -/
theorem preparedRootDiameter_lt_requested {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.preparedRootDiameter < prepared.request.rootDiameter := by
  rw [prepared.preparedRootDiameter_eq_canonical]
  exact PreparedSheetContinuation.prepared_diagonal_lt
    prepared.segment prepared.left prepared.owner prepared.request

open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
/-- The local point displacement equals the displacement along the original retained parameter edge. -/
theorem pointMovement_eq_parameterEdge {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.pointMovement =
      Data.Gaussian.Norm.Basic.normSq
        (prepared.segment.pointAt prepared.request.endpoint.parameter -
          prepared.segment.pointAt prepared.left.parameter) := by
  unfold pointMovement
  change Data.Gaussian.Norm.Basic.normSq
      (prepared.localSegment.pointAt 1 - prepared.localSegment.pointAt 0) = _
  simp only [localSegment, PreparedModels.edge]
  rw [← PreparedSheetContinuation.pointAt_parameterAt
      prepared.segment prepared.within prepared.left prepared.request 1,
    ← PreparedSheetContinuation.pointAt_parameterAt
      prepared.segment prepared.within prepared.left prepared.request 0,
    PreparedSheetContinuation.parameterAt_one,
    PreparedSheetContinuation.parameterAt_zero]

/-- Read the squared diagonal directly from the retained prepared-owner cache. -/
def cachedRootDiameter {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.cached.preparedOwner.track.initial.box.diagonalSq

/-- Read the box-derived squared-norm lower bound from the exact cached root box. -/
def cachedGeometricDenominatorLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  PreparedConstantModels.boxNormSqLower prepared.cached.preparedOwner.track.initial.box

/-- Read the squared-norm lower bound for sums of two values in the exact cached root box. -/
def cachedRootSumLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  boxSumNormSqLower prepared.cached.preparedOwner.track.initial.box

/-- A strictly positive real lower endpoint contributes its square to the cached geometric denominator lower bound. -/
theorem xLower_sq_le_cachedGeometricDenominatorLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (positive :
      0 < prepared.cached.preparedOwner.track.initial.box.xLower) :
    prepared.cached.preparedOwner.track.initial.box.xLower ^ 2 <=
      prepared.cachedGeometricDenominatorLower := by
  unfold cachedGeometricDenominatorLower PreparedConstantModels.boxNormSqLower
  unfold intervalSqLower
  rw [if_pos positive]
  exact le_add_of_nonneg_right
    (intervalSqLower_nonnegative
      prepared.cached.preparedOwner.track.initial.box.yLower
      prepared.cached.preparedOwner.track.initial.box.yUpper)

/-- A strictly negative real upper endpoint contributes its square to the cached geometric denominator lower bound. -/
theorem xUpper_sq_le_cachedGeometricDenominatorLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (negative :
      prepared.cached.preparedOwner.track.initial.box.xUpper < 0) :
    prepared.cached.preparedOwner.track.initial.box.xUpper ^ 2 <=
      prepared.cachedGeometricDenominatorLower := by
  have lowerNotPositive :
      ¬0 < prepared.cached.preparedOwner.track.initial.box.xLower := by
    intro lowerPositive
    have upperPositive :
        0 < prepared.cached.preparedOwner.track.initial.box.xUpper :=
      lowerPositive.trans_le
        prepared.cached.preparedOwner.track.initial.box.x_valid
    exact (not_lt_of_ge negative.le) upperPositive
  unfold cachedGeometricDenominatorLower PreparedConstantModels.boxNormSqLower intervalSqLower
  rw [if_neg lowerNotPositive, if_pos negative]
  exact le_add_of_nonneg_right
    (intervalSqLower_nonnegative
      prepared.cached.preparedOwner.track.initial.box.yLower
      prepared.cached.preparedOwner.track.initial.box.yUpper)

section
open Purelib.Data.Rat
/-- A strictly positive real lower endpoint contributes the square of twice that endpoint to the cached root-sum lower
bound. -/
theorem two_xLower_sq_le_cachedRootSumLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (positive :
      0 < prepared.cached.preparedOwner.track.initial.box.xLower) :
    (2 * prepared.cached.preparedOwner.track.initial.box.xLower) ^ 2 <=
      prepared.cachedRootSumLower := by
  have doubledPositive :
      0 < 2 * prepared.cached.preparedOwner.track.initial.box.xLower :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive
  unfold cachedRootSumLower boxSumNormSqLower intervalSqLower
  rw [if_pos doubledPositive]
  exact le_add_of_nonneg_right
    (intervalSqLower_nonnegative
      (2 * prepared.cached.preparedOwner.track.initial.box.yLower)
      (2 * prepared.cached.preparedOwner.track.initial.box.yUpper))

/-- A strictly negative real upper endpoint contributes the square of twice that endpoint to the cached root-sum lower
bound. -/
theorem two_xUpper_sq_le_cachedRootSumLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (negative :
      prepared.cached.preparedOwner.track.initial.box.xUpper < 0) :
    (2 * prepared.cached.preparedOwner.track.initial.box.xUpper) ^ 2 <=
      prepared.cachedRootSumLower := by
  have lowerNegative :
      prepared.cached.preparedOwner.track.initial.box.xLower < 0 :=
    prepared.cached.preparedOwner.track.initial.box.x_valid.trans_lt negative
  have doubledLowerNegative :
      2 * prepared.cached.preparedOwner.track.initial.box.xLower < 0 :=
    Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
      (by decide) lowerNegative
  have doubledUpperNegative :
      2 * prepared.cached.preparedOwner.track.initial.box.xUpper < 0 :=
    Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
      (by decide) negative
  unfold cachedRootSumLower boxSumNormSqLower intervalSqLower
  rw [if_neg (not_lt_of_ge doubledLowerNegative.le),
    if_pos doubledUpperNegative]
  exact le_add_of_nonneg_right
    (intervalSqLower_nonnegative
      (2 * prepared.cached.preparedOwner.track.initial.box.yLower)
      (2 * prepared.cached.preparedOwner.track.initial.box.yUpper))

end

/-- A strictly positive imaginary lower endpoint contributes its square to the cached geometric denominator lower bound.
-/
theorem yLower_sq_le_cachedGeometricDenominatorLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (positive :
      0 < prepared.cached.preparedOwner.track.initial.box.yLower) :
    prepared.cached.preparedOwner.track.initial.box.yLower ^ 2 <=
      prepared.cachedGeometricDenominatorLower := by
  unfold cachedGeometricDenominatorLower PreparedConstantModels.boxNormSqLower
  have imaginaryLower :
      intervalSqLower
          prepared.cached.preparedOwner.track.initial.box.yLower
          prepared.cached.preparedOwner.track.initial.box.yUpper =
        prepared.cached.preparedOwner.track.initial.box.yLower ^ 2 := by
    unfold intervalSqLower
    rw [if_pos positive]
  rw [imaginaryLower]
  exact le_add_of_nonneg_left
    (intervalSqLower_nonnegative
      prepared.cached.preparedOwner.track.initial.box.xLower
      prepared.cached.preparedOwner.track.initial.box.xUpper)

/-- A strictly negative imaginary upper endpoint contributes its square to the cached geometric denominator lower bound.
-/
theorem yUpper_sq_le_cachedGeometricDenominatorLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (negative :
      prepared.cached.preparedOwner.track.initial.box.yUpper < 0) :
    prepared.cached.preparedOwner.track.initial.box.yUpper ^ 2 <=
      prepared.cachedGeometricDenominatorLower := by
  have lowerNotPositive :
      ¬0 < prepared.cached.preparedOwner.track.initial.box.yLower := by
    intro lowerPositive
    have upperPositive :
        0 < prepared.cached.preparedOwner.track.initial.box.yUpper :=
      lowerPositive.trans_le
        prepared.cached.preparedOwner.track.initial.box.y_valid
    exact (not_lt_of_ge negative.le) upperPositive
  unfold cachedGeometricDenominatorLower PreparedConstantModels.boxNormSqLower
  have imaginaryLower :
      intervalSqLower
          prepared.cached.preparedOwner.track.initial.box.yLower
          prepared.cached.preparedOwner.track.initial.box.yUpper =
        prepared.cached.preparedOwner.track.initial.box.yUpper ^ 2 := by
    unfold intervalSqLower
    rw [if_neg lowerNotPositive, if_pos negative]
  rw [imaginaryLower]
  exact le_add_of_nonneg_left
    (intervalSqLower_nonnegative
      prepared.cached.preparedOwner.track.initial.box.xLower
      prepared.cached.preparedOwner.track.initial.box.xUpper)

section
open Purelib.Data.Rat
/-- A strictly positive imaginary lower endpoint contributes the square of twice that endpoint to the cached root-sum
lower bound. -/
theorem two_yLower_sq_le_cachedRootSumLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (positive :
      0 < prepared.cached.preparedOwner.track.initial.box.yLower) :
    (2 * prepared.cached.preparedOwner.track.initial.box.yLower) ^ 2 <=
      prepared.cachedRootSumLower := by
  have doubledPositive :
      0 < 2 * prepared.cached.preparedOwner.track.initial.box.yLower :=
    Fraction.Order.Arithmetic.mul_pos_direct (by decide) positive
  unfold cachedRootSumLower boxSumNormSqLower
  have imaginaryLower :
      intervalSqLower
          (2 * prepared.cached.preparedOwner.track.initial.box.yLower)
          (2 * prepared.cached.preparedOwner.track.initial.box.yUpper) =
        (2 * prepared.cached.preparedOwner.track.initial.box.yLower) ^ 2 := by
    unfold intervalSqLower
    rw [if_pos doubledPositive]
  rw [imaginaryLower]
  exact le_add_of_nonneg_left
    (intervalSqLower_nonnegative
      (2 * prepared.cached.preparedOwner.track.initial.box.xLower)
      (2 * prepared.cached.preparedOwner.track.initial.box.xUpper))

/-- A strictly negative imaginary upper endpoint contributes the square of twice that endpoint to the cached root-sum
lower bound. -/
theorem two_yUpper_sq_le_cachedRootSumLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (negative :
      prepared.cached.preparedOwner.track.initial.box.yUpper < 0) :
    (2 * prepared.cached.preparedOwner.track.initial.box.yUpper) ^ 2 <=
      prepared.cachedRootSumLower := by
  have lowerNegative :
      prepared.cached.preparedOwner.track.initial.box.yLower < 0 :=
    prepared.cached.preparedOwner.track.initial.box.y_valid.trans_lt negative
  have doubledLowerNegative :
      2 * prepared.cached.preparedOwner.track.initial.box.yLower < 0 :=
    Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
      (by decide) lowerNegative
  have doubledUpperNegative :
      2 * prepared.cached.preparedOwner.track.initial.box.yUpper < 0 :=
    Fraction.Order.Arithmetic.mul_neg_of_pos_of_neg_direct
      (by decide) negative
  unfold cachedRootSumLower boxSumNormSqLower
  have imaginaryLower :
      intervalSqLower
          (2 * prepared.cached.preparedOwner.track.initial.box.yLower)
          (2 * prepared.cached.preparedOwner.track.initial.box.yUpper) =
        (2 * prepared.cached.preparedOwner.track.initial.box.yUpper) ^ 2 := by
    unfold intervalSqLower
    rw [if_neg (not_lt_of_ge doubledLowerNegative.le),
      if_pos doubledUpperNegative]
  rw [imaginaryLower]
  exact le_add_of_nonneg_left
    (intervalSqLower_nonnegative
      (2 * prepared.cached.preparedOwner.track.initial.box.xLower)
      (2 * prepared.cached.preparedOwner.track.initial.box.xUpper))

/-- Separation of any coordinate side from zero by a positive amount bounds the cached denominator lower bound by its
square.

The selected coordinate side remains separated from zero by the supplied
positive amount. Its original cached squared interval floor bounds that square. -/
theorem separation_sq_le_cachedGeometricDenominatorLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (separation : Coordinate)
    (separationPositive : 0 < separation)
    (separated :
      separation <= prepared.cached.preparedOwner.track.initial.box.xLower ∨
      prepared.cached.preparedOwner.track.initial.box.xUpper <= -separation ∨
      separation <= prepared.cached.preparedOwner.track.initial.box.yLower ∨
      prepared.cached.preparedOwner.track.initial.box.yUpper <= -separation) :
    separation ^ 2 <= prepared.cachedGeometricDenominatorLower := by
  have separationNegative : -separation < (0 : Coordinate) := by
    have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct separationPositive
    simpa only [neg_zero] using reversed
  rcases separated with xLower | xUpper | yLower | yUpper
  · exact (Fraction.Order.Arithmetic.pow_le_pow_direct separationPositive.le
      xLower 2).trans
        (prepared.xLower_sq_le_cachedGeometricDenominatorLower
          (separationPositive.trans_le xLower))
  · have upperNegative :
        prepared.cached.preparedOwner.track.initial.box.xUpper < 0 :=
      xUpper.trans_lt separationNegative
    have separationLeNegUpper :
        separation <=
          -prepared.cached.preparedOwner.track.initial.box.xUpper := by
      have reversed :=
        Fraction.Order.Arithmetic.neg_le_neg_direct xUpper
      simpa only [neg_neg] using reversed
    have powers := Fraction.Order.Arithmetic.pow_le_pow_direct
      separationPositive.le separationLeNegUpper 2
    rw [show (-prepared.cached.preparedOwner.track.initial.box.xUpper) ^ 2 =
        prepared.cached.preparedOwner.track.initial.box.xUpper ^ 2 by ring1]
      at powers
    exact powers.trans
      (prepared.xUpper_sq_le_cachedGeometricDenominatorLower upperNegative)
  · exact (Fraction.Order.Arithmetic.pow_le_pow_direct separationPositive.le
      yLower 2).trans
        (prepared.yLower_sq_le_cachedGeometricDenominatorLower
          (separationPositive.trans_le yLower))
  · have upperNegative :
        prepared.cached.preparedOwner.track.initial.box.yUpper < 0 :=
      yUpper.trans_lt separationNegative
    have separationLeNegUpper :
        separation <=
          -prepared.cached.preparedOwner.track.initial.box.yUpper := by
      have reversed :=
        Fraction.Order.Arithmetic.neg_le_neg_direct yUpper
      simpa only [neg_neg] using reversed
    have powers := Fraction.Order.Arithmetic.pow_le_pow_direct
      separationPositive.le separationLeNegUpper 2
    rw [show (-prepared.cached.preparedOwner.track.initial.box.yUpper) ^ 2 =
        prepared.cached.preparedOwner.track.initial.box.yUpper ^ 2 by ring1]
      at powers
    exact powers.trans
      (prepared.yUpper_sq_le_cachedGeometricDenominatorLower upperNegative)

end

/-- Positive coordinate-side separation gives the equivalent product lower bound for the cached denominator estimate. -/
theorem separation_mul_self_le_cachedGeometricDenominatorLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (separation : Coordinate)
    (separationPositive : 0 < separation)
    (separated :
      separation <= prepared.cached.preparedOwner.track.initial.box.xLower ∨
      prepared.cached.preparedOwner.track.initial.box.xUpper <= -separation ∨
      separation <= prepared.cached.preparedOwner.track.initial.box.yLower ∨
      prepared.cached.preparedOwner.track.initial.box.yUpper <= -separation) :
    separation * separation <= prepared.cachedGeometricDenominatorLower := by
  rw [← pow_two]
  exact prepared.separation_sq_le_cachedGeometricDenominatorLower separation
    separationPositive separated

open Purelib.Data.Rat in
/-- Positive coordinate-side separation gives the squared doubled-separation lower bound for sums in the cached root
box.

The supplied positive separation doubles in the original sum-coordinate
interval. Its unchanged squared interval floor bounds the same doubled square. -/
theorem two_separation_sq_le_cachedRootSumLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (separation : Coordinate)
    (separationPositive : 0 < separation)
    (separated :
      separation <= prepared.cached.preparedOwner.track.initial.box.xLower ∨
      prepared.cached.preparedOwner.track.initial.box.xUpper <= -separation ∨
      separation <= prepared.cached.preparedOwner.track.initial.box.yLower ∨
      prepared.cached.preparedOwner.track.initial.box.yUpper <= -separation) :
    (2 * separation) ^ 2 <= prepared.cachedRootSumLower := by
  have twoPositive : (0 : Coordinate) < 2 := by decide
  have doubledSeparationPositive : 0 < 2 * separation :=
    Fraction.Order.Arithmetic.mul_pos_direct twoPositive separationPositive
  have separationNegative : -separation < (0 : Coordinate) := by
    have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct separationPositive
    simpa only [neg_zero] using reversed
  rcases separated with xLower | xUpper | yLower | yUpper
  · have doubled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct xLower
        twoPositive.le
    exact (Fraction.Order.Arithmetic.pow_le_pow_direct
      doubledSeparationPositive.le doubled 2).trans
        (prepared.two_xLower_sq_le_cachedRootSumLower
          (separationPositive.trans_le xLower))
  · have upperNegative :
        prepared.cached.preparedOwner.track.initial.box.xUpper < 0 :=
      xUpper.trans_lt separationNegative
    have separationLeNegUpper :
        separation <=
          -prepared.cached.preparedOwner.track.initial.box.xUpper := by
      have reversed :=
        Fraction.Order.Arithmetic.neg_le_neg_direct xUpper
      simpa only [neg_neg] using reversed
    have doubled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        separationLeNegUpper twoPositive.le
    have powers := Fraction.Order.Arithmetic.pow_le_pow_direct
      doubledSeparationPositive.le doubled 2
    rw [show (2 * -prepared.cached.preparedOwner.track.initial.box.xUpper) ^ 2 =
        (2 * prepared.cached.preparedOwner.track.initial.box.xUpper) ^ 2 by
      ring1] at powers
    exact powers.trans
      (prepared.two_xUpper_sq_le_cachedRootSumLower upperNegative)
  · have doubled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct yLower
        twoPositive.le
    exact (Fraction.Order.Arithmetic.pow_le_pow_direct
      doubledSeparationPositive.le doubled 2).trans
        (prepared.two_yLower_sq_le_cachedRootSumLower
          (separationPositive.trans_le yLower))
  · have upperNegative :
        prepared.cached.preparedOwner.track.initial.box.yUpper < 0 :=
      yUpper.trans_lt separationNegative
    have separationLeNegUpper :
        separation <=
          -prepared.cached.preparedOwner.track.initial.box.yUpper := by
      have reversed :=
        Fraction.Order.Arithmetic.neg_le_neg_direct yUpper
      simpa only [neg_neg] using reversed
    have doubled :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        separationLeNegUpper twoPositive.le
    have powers := Fraction.Order.Arithmetic.pow_le_pow_direct
      doubledSeparationPositive.le doubled 2
    rw [show (2 * -prepared.cached.preparedOwner.track.initial.box.yUpper) ^ 2 =
        (2 * prepared.cached.preparedOwner.track.initial.box.yUpper) ^ 2 by
      ring1] at powers
    exact powers.trans
      (prepared.two_yUpper_sq_le_cachedRootSumLower upperNegative)

/-- The cached root-sum lower bound is nonnegative. -/
theorem cachedRootSumLower_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 <= prepared.cachedRootSumLower :=
  boxSumNormSqLower_nonnegative _

open Purelib.Data.Gaussian in
/-- The cached root-sum lower bound bounds the squared norm of any two values from the retained box. -/
theorem cachedRootSumLower_le_of_contains {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) {leftRoot rightRoot : Gaussian}
    (leftInside : prepared.cached.preparedOwner.track.initial.box.Contains
      leftRoot)
    (rightInside : prepared.cached.preparedOwner.track.initial.box.Contains
      rightRoot) :
    prepared.cachedRootSumLower <=
      Data.Gaussian.Norm.Basic.normSq (leftRoot + rightRoot) := by
  exact boxSumNormSqLower_le_of_contains leftInside rightInside

/-- Choose the smaller of the prepared diameter and the movement-plus-cached-diameter budget divided by two to the
twentieth power.

This positive tolerance controls the squared residual of root candidates used by coefficient readings. -/
def rootResidualTarget {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  min ((prepared.pointMovement + prepared.cachedRootDiameter) / (2 ^ 20)) prepared.preparedRootDiameter

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The selected root-residual tolerance is strictly positive.

Both original target branches are positive: the movement-plus-diameter
quotient and the prepared root diameter. Their unchanged minimum retains positivity. -/
theorem rootResidualTarget_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 < prepared.rootResidualTarget := by
  apply Fraction.Order.Basic.lt_min
  · exact Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (Norm.Basic.normSq_nonneg _)
        (CoherentRoot.scale_positive prepared.cached.preparedOwner.track))
      (Fraction.Order.Arithmetic.pow_pos_direct (by decide) 20)
  · exact prepared.preparedRootDiameter_positive

open Purelib.Algebra in
open Purelib.Data.Rat in
/-- A movement-plus-diameter bound of two to the eighth power makes the residual target at most two to the negative
twelfth power.

The original target minimum is bounded by its movement-plus-diameter
quotient. The supplied bound and unchanged powers of two give the stated floor. -/
theorem rootResidualTarget_le_one_div_two_pow_twelve_of_add_le_two_pow_eight
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (bounded : prepared.pointMovement + prepared.cachedRootDiameter <= 2 ^ 8) :
    prepared.rootResidualTarget <= 1 / (2 ^ 12) := by
  apply (Fraction.Order.Basic.min_le_left _ _).trans
  apply (Fraction.Order.Field.div_le_iff_pos
    (Fraction.Order.Arithmetic.pow_pos_direct (by decide) 20)).2
  calc
    prepared.pointMovement + prepared.cachedRootDiameter <= 2 ^ 8 := bounded
    _ = 1 * (2 ^ 8 : Coordinate) := by ring1
    _ = ((1 / (2 ^ 12 : Coordinate)) * (2 ^ 12 : Coordinate)) *
          (2 ^ 8 : Coordinate) := by
      rw [Field.ExplicitField.div_mul_cancel]
      exact (Fraction.Order.Arithmetic.pow_pos_direct (by decide) 12).ne'
    _ = (1 / (2 ^ 12 : Coordinate)) *
          ((2 ^ 12 : Coordinate) * (2 ^ 8 : Coordinate)) := by
      rw [Fraction.Field.mul_assoc]
    _ = (1 / (2 ^ 12 : Coordinate)) * (2 ^ 20 : Coordinate) := by
      rw [show (20 : Nat) = 12 + 8 by omega, pow_add]

section
open Purelib.Riemann.Branches
/-- The original cleared segment's variation bound over the retained requested parameter edge. -/
def radicandMovementBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  ClearSheetContinuation.variationBound prepared.segment
    prepared.left.parameter prepared.request.endpoint.parameter

/-- The retained radicand variation bound is nonnegative. -/
theorem radicandMovementBound_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 <= prepared.radicandMovementBound := by
  exact ClearSheetContinuation.variationBound_nonneg
    prepared.segment prepared.left.parameter
      prepared.request.endpoint.parameter

end

/-- Compute the residual-based squared root-displacement estimate using both residual targets and the retained radicand
movement.

The denominator is the cached root-sum lower bound; its use as a distance estimate requires that lower bound to be
positive. -/
def residualRootMovement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  4 * (prepared.rootResidualTarget + prepared.radicandMovementBound +
    prepared.rootResidualTarget) / prepared.cachedRootSumLower

open Purelib.Data.Rat in
/-- The computed residual root-movement expression is nonnegative. -/
theorem residualRootMovement_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 <= prepared.residualRootMovement := by
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg
        (add_nonneg prepared.rootResidualTarget_positive.le
          prepared.radicandMovementBound_nonnegative)
        prepared.rootResidualTarget_positive.le))
    prepared.cachedRootSumLower_nonnegative

/-- Use the smaller cached-diameter and residual bound when the root-sum lower bound is positive, otherwise retain the
cached diameter. -/
def rootMovementBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  if 0 < prepared.cachedRootSumLower then
    min prepared.cachedRootDiameter prepared.residualRootMovement
  else
    prepared.cachedRootDiameter

open Purelib.Riemann.RootContinuation in
open Purelib.Data.Rat in
/-- The selected squared root-movement bound is nonnegative. -/
theorem rootMovementBound_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 <= prepared.rootMovementBound := by
  unfold rootMovementBound
  split
  · exact Fraction.Order.Basic.le_min
      (CoherentRoot.scale_positive
        prepared.cached.preparedOwner.track).le
      prepared.residualRootMovement_nonnegative
  · exact (CoherentRoot.scale_positive
      prepared.cached.preparedOwner.track).le

open Purelib.Data.Rat in
/-- The selected root-movement bound never exceeds the cached root diameter.

The retained movement minimum includes the original cached root diameter.
Its selected value is therefore bounded by that same diameter. -/
theorem rootMovementBound_le_cachedRootDiameter {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.rootMovementBound <= prepared.cachedRootDiameter := by
  unfold rootMovementBound
  split
  · exact Fraction.Order.Basic.min_le_left _ _
  · exact le_rfl

open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Refine the exact direct query root process until its candidates meet the retained residual target.

The resulting state belongs to the original sheet-value process via its exact direct-owner name equality. -/
def residualRootState {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (prepared.sheetValue fraction inside).value.name.process.State := by
  let parameter := curve.polynomial.eval (prepared.segment.pointAt
    (PreparedSheetContinuation.parameterAt prepared.left
      prepared.request fraction))
  let parameterNonzero := prepared.segment.pointAt_eval_ne_zero
    (PreparedSheetContinuation.parameterAt prepared.left
      prepared.request fraction)
    (PreparedSheetContinuation.parameterAt_inside prepared.left
      prepared.request prepared.ordered fraction inside)
  let direct := prepared.directQueryOwner fraction inside
  rw [prepared.sheetValue_name_eq_directQueryOwnerRootName fraction inside]
  exact CertifiedSquareRoot.residualState parameterNonzero
    direct.track prepared.rootResidualTarget
      prepared.rootResidualTarget_positive

open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Every possible candidate at the retained residual state has squared polynomial residual below the selected target.
-/
theorem residualRootState_candidate_residual_lt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    {candidate : Gaussian}
    (possible :
      (prepared.sheetValue fraction inside).value.name.process.Possible
        (prepared.residualRootState fraction inside) candidate) :
    Data.Gaussian.Norm.Basic.normSq
        (candidate * candidate - curve.polynomial.eval
          (prepared.point fraction)) < prepared.rootResidualTarget := by
  let parameter := curve.polynomial.eval (prepared.segment.pointAt
    (PreparedSheetContinuation.parameterAt prepared.left
      prepared.request fraction))
  let parameterNonzero := prepared.segment.pointAt_eval_ne_zero
    (PreparedSheetContinuation.parameterAt prepared.left
      prepared.request fraction)
    (PreparedSheetContinuation.parameterAt_inside prepared.left
      prepared.request prepared.ordered fraction inside)
  let direct := prepared.directQueryOwner fraction inside
  have residual :=
    CertifiedSquareRoot.residualState_candidate_residual_lt
      parameterNonzero direct.track prepared.rootResidualTarget
        prepared.rootResidualTarget_positive possible
  rw [PreparedSheetContinuation.pointAt_parameterAt
    prepared.segment prepared.within prepared.left prepared.request fraction]
    at residual
  unfold point localSegment PreparedModels.edge
  simpa only [Norm.Basic.normSq_eq_canonical] using residual

/-- Take the maximum of the segment denominator estimate and the cached box's squared-norm lower bound. -/
def cachedDenominatorLower {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  max (PreparedModels.denominatorLower
      prepared.segment) prepared.cachedGeometricDenominatorLower

open Purelib.Data.Rat in
/-- The cached denominator lower bound includes the original segment denominator estimate.

The original nested maxima retain the same denominator lower bound.
Their cached value therefore bounds it through its two exact maximum inclusions. -/
theorem denominatorLower_le_cachedDenominatorLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    PreparedModels.denominatorLower
        prepared.segment <= prepared.cachedDenominatorLower := by
  exact Fraction.Order.Basic.le_max_left _ _

/-- The combined cached denominator lower bound is strictly positive. -/
theorem cachedDenominatorLower_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 < prepared.cachedDenominatorLower :=
  (PreparedModels.denominatorLower_positive
    prepared.segment).trans_le prepared.denominatorLower_le_cachedDenominatorLower

open Purelib.Data.Gaussian in
/-- The cached geometric lower bound bounds every value contained in the exact prepared box. -/
theorem cachedGeometricDenominatorLower_le_of_contains {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) {candidate : Gaussian}
    (inside : prepared.cached.preparedOwner.track.initial.box.Contains
      candidate) :
    prepared.cachedGeometricDenominatorLower <=
      Data.Gaussian.Norm.Basic.normSq candidate := by
  unfold cachedGeometricDenominatorLower
  exact boxNormSqLower_le_of_contains inside

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A value in the cached box that meets the segment estimate also meets the combined denominator lower bound.

Each original cached interval floor bounds the quadrance of the same
contained root. Their unchanged maximum retains that common bound. -/
theorem cachedDenominatorLower_le_of_contains {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) {candidate : Gaussian}
    (inside : prepared.cached.preparedOwner.track.initial.box.Contains
      candidate)
    (globalLower :
      PreparedModels.denominatorLower
          prepared.segment <=
        Data.Gaussian.Norm.Basic.normSq candidate) :
    prepared.cachedDenominatorLower <=
      Data.Gaussian.Norm.Basic.normSq candidate := by
  exact Fraction.Order.Basic.max_le globalLower
    (prepared.cachedGeometricDenominatorLower_le_of_contains inside)

open Purelib.Riemann.RootContinuation in
/-- The squared diagonal read from the cached root box is positive. -/
theorem cachedRootDiameter_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 < prepared.cachedRootDiameter := by
  exact CoherentRoot.scale_positive
    prepared.cached.preparedOwner.track

section
open Purelib.Riemann.Branches
/-- The cached root diameter is strictly below the retained request. -/
theorem cachedRootDiameter_lt_request {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.cachedRootDiameter < prepared.request.rootDiameter := by
  unfold cachedRootDiameter
  rw [prepared.cached.preparedOwner_eq]
  exact PreparedSheetContinuation.prepared_diagonal_lt
    prepared.segment prepared.left prepared.owner prepared.request

/-- Canonical preparation's squared diagonal equals the exact cached root diameter. -/
theorem preparedRootDiameter_eq_cachedRootDiameter {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    (PreparedSheetContinuation.prepared prepared.segment
      prepared.left prepared.owner
      prepared.request).track.initial.box.diagonalSq =
        prepared.cachedRootDiameter := by
  unfold cachedRootDiameter
  rw [prepared.cached.preparedOwner_eq]

end

/-- Compute a coordinate-square lower bound using a nonnegative lower endpoint, a nonpositive upper endpoint, or zero.
-/
def intervalNormSqLower (lower upper : Coordinate) : Coordinate :=
  if _lowerNonnegative : 0 <= lower then lower ^ 2
  else if _upperNonpositive : upper <= 0 then upper ^ 2
  else 0

section
open Purelib.Data.Rat
/-- The coordinate-square interval lower bound is nonnegative. -/
theorem intervalNormSqLower_nonnegative (lower upper : Coordinate) :
    0 <= intervalNormSqLower lower upper := by
  unfold intervalNormSqLower
  split <;> rename_i first
  · exact Fraction.Order.Arithmetic.sq_nonneg_direct lower
  · split <;> rename_i second
    · exact Fraction.Order.Arithmetic.sq_nonneg_direct upper
    · exact le_rfl

/-- Every coordinate in the original interval has square at least its computed lower bound.

The original interval sign branch selects its endpoint square or zero.
Direct order reversal bounds the same negative endpoint and contained value. -/
theorem intervalNormSqLower_le {lower value upper : Coordinate}
    (lowerLe : lower <= value) (valueLe : value <= upper) :
    intervalNormSqLower lower upper <= value ^ 2 := by
  unfold intervalNormSqLower
  split
  · rename_i lowerNonnegative
    exact Fraction.Order.Arithmetic.pow_le_pow_direct lowerNonnegative lowerLe 2
  · rename_i lowerNegative
    split
    · rename_i upperNonpositive
      have negOrder : -upper <= -value :=
        Fraction.Order.Arithmetic.neg_le_neg_direct valueLe
      have negUpperNonnegative : 0 <= -upper :=
        by
          have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct upperNonpositive
          simpa only [neg_zero] using reversed
      have squares := Fraction.Order.Arithmetic.pow_le_pow_direct
        negUpperNonnegative negOrder 2
      simpa only [show (-upper) ^ 2 = upper ^ 2 by ring1,
        show (-value) ^ 2 = value ^ 2 by ring1] using squares
    · exact Fraction.Order.Arithmetic.sq_nonneg_direct value

end

/-- Sum the interval squared-norm lower bounds for the two coordinate intervals of the original box. -/
def boxNormSqLower (box : Box) : Coordinate :=
  intervalNormSqLower box.xLower box.xUpper +
    intervalNormSqLower box.yLower box.yUpper

/-- The box's computed squared-norm lower bound is nonnegative. -/
theorem boxNormSqLower_nonnegative (box : Box) :
    0 <= boxNormSqLower box :=
  add_nonneg
    (intervalNormSqLower_nonnegative box.xLower box.xUpper)
    (intervalNormSqLower_nonnegative box.yLower box.yUpper)

open Purelib.Data.Gaussian in
/-- Every Gaussian value in the original box meets the computed squared-norm lower bound. -/
theorem boxNormSqLower_le {box : Box} {value : Gaussian}
    (inside : box.Contains value) :
    boxNormSqLower box <=
      Data.Gaussian.Norm.Basic.normSq value := by
  unfold boxNormSqLower Data.Gaussian.Norm.Basic.normSq
  exact add_le_add
    (intervalNormSqLower_le inside.1 inside.2.1)
    (intervalNormSqLower_le inside.2.2.1 inside.2.2.2)

/-- Strengthen the segment denominator floor with the squared-norm lower bound of the actual cached root box. -/
def preparedDenominatorLower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  max
    (PreparedModels.segmentDenominatorLower
      prepared.segment)
    (boxNormSqLower prepared.cached.preparedOwner.track.initial.box)

open Purelib.Data.Rat in
/-- The prepared denominator floor is strictly positive.

The original maximum retains the positive segment denominator floor
alongside its cached root-box norm estimate. -/
theorem preparedDenominatorLower_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 < prepared.preparedDenominatorLower :=
  (PreparedModels.segmentDenominatorLower_positive
    prepared.segment).trans_le (Fraction.Order.Basic.le_max_left _ _)

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Compute the quotient-variation allowance from point movement, prepared root diameter, ambient power bounds, and the
prepared denominator floor.

The original differential exponent controls the numerator slope; the denominator estimate belongs to the same retained
prepared edge. -/
def rawVariation {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  Budget.Quotient.quotientBound
    (Power.Bounds.IntegrationQuotientVariation.powerSlope
      prepared.ambient.normSqBound differential.exponent)
    (prepared.ambient.normSqBound ^ differential.exponent)
    (UniformSquareRootPreparation.rootAmbient
      prepared.segment).normSqBound
    prepared.preparedDenominatorLower
    prepared.pointMovement prepared.preparedRootDiameter

/-- Add the prepared root diameter to the raw quotient-variation allowance. -/
def modelErrorAllowance {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.rawVariation + prepared.preparedRootDiameter

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The raw quotient-variation allowance is nonnegative. -/
theorem rawVariation_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 <= prepared.rawVariation := by
  apply Budget.Quotient.IntegrationQuotientVariation.quotientBound_nonnegative
  · exact Power.Bounds.IntegrationQuotientVariation.powerSlope_nonnegative
      prepared.ambient.normSqBound_nonneg differential.exponent
  · exact Fraction.Order.Arithmetic.pow_nonneg_direct
      prepared.ambient.normSqBound_nonneg differential.exponent
  · exact (UniformSquareRootPreparation.rootAmbient
      prepared.segment).normSqBound_nonneg
  · exact
      prepared.preparedDenominatorLower_positive.le
  · exact Norm.Basic.normSq_nonneg _
  · exact prepared.preparedRootDiameter_positive.le

section
open Purelib.Data.Rat
/-- The model-error allowance is strictly positive.

The original nonnegative variation and positive prepared root diameter
are the two retained summands of this allowance. -/
theorem modelErrorAllowance_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
  0 < prepared.modelErrorAllowance :=
  Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct prepared.rawVariation_nonnegative
    prepared.preparedRootDiameter_positive

/-- The root-residual target is no larger than the model-error allowance.

The retained target minimum is bounded by the original prepared root
diameter, which is one nonnegative summand of the model allowance. -/
theorem rootResidualTarget_le_modelErrorAllowance {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.rootResidualTarget ≤ prepared.modelErrorAllowance :=
  (Fraction.Order.Basic.min_le_right _ _).trans (le_add_of_nonneg_left prepared.rawVariation_nonnegative)

end

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- The point-movement coefficient using the original segment denominator floor and ambient numerator slope. -/
def pointErrorCoefficient {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish) :
    Coordinate :=
  (2 *
      (Power.Bounds.IntegrationQuotientVariation.powerSlope ambient.normSqBound
          differential.exponent *
        (UniformSquareRootPreparation.rootAmbient
          segment).normSqBound)) /
    (PreparedModels.segmentDenominatorLower segment *
      PreparedModels.segmentDenominatorLower segment)

open Purelib.Polynomial in
/-- The root-movement coefficient using the original segment denominator floor, including the added unit allowance. -/
def rootErrorCoefficient {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish) :
    Coordinate :=
  (2 * ambient.normSqBound ^ differential.exponent) /
      (PreparedModels.segmentDenominatorLower segment *
        PreparedModels.segmentDenominatorLower segment) +
    1

open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The point-movement coefficient strengthened by the actual prepared denominator floor. -/
def preparedPointErrorCoefficient {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  (2 *
      (Power.Bounds.IntegrationQuotientVariation.powerSlope
          prepared.ambient.normSqBound differential.exponent *
        (UniformSquareRootPreparation.rootAmbient
          prepared.segment).normSqBound)) /
    (prepared.preparedDenominatorLower * prepared.preparedDenominatorLower)

/-- The root-movement coefficient strengthened by the actual prepared denominator floor, including the unit allowance.
-/
def preparedRootErrorCoefficient {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  (2 * prepared.ambient.normSqBound ^ differential.exponent) /
      (prepared.preparedDenominatorLower * prepared.preparedDenominatorLower) +
    1

open Purelib.Data.Rat in
/-- The prepared root-movement coefficient is nonnegative. -/
theorem preparedRootErrorCoefficient_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 <= prepared.preparedRootErrorCoefficient := by
  unfold preparedRootErrorCoefficient
  exact add_nonneg
    (Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.pow_nonneg_direct
          prepared.ambient.normSqBound_nonneg differential.exponent))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        prepared.preparedDenominatorLower_positive.le
        prepared.preparedDenominatorLower_positive.le))
    (by decide)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.RootContinuation in
/-- The segment point-movement coefficient is nonnegative. -/
theorem pointErrorCoefficient_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish) :
    0 <= pointErrorCoefficient differential segment := by
  unfold pointErrorCoefficient
  exact Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Power.Bounds.IntegrationQuotientVariation.powerSlope_nonnegative
          ambient.normSqBound_nonneg differential.exponent)
        (UniformSquareRootPreparation.rootAmbient
          segment).normSqBound_nonneg))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (PreparedModels.segmentDenominatorLower_positive
        segment).le
      (PreparedModels.segmentDenominatorLower_positive
        segment).le)

open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The segment root-movement coefficient is nonnegative. -/
theorem rootErrorCoefficient_nonnegative {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    (differential : Basic.Differential genus)
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish) :
    0 <= rootErrorCoefficient differential segment := by
  unfold rootErrorCoefficient
  exact add_nonneg
    (Fraction.Order.Field.div_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.pow_nonneg_direct
          ambient.normSqBound_nonneg differential.exponent))
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (PreparedModels.segmentDenominatorLower_positive
          segment).le
        (PreparedModels.segmentDenominatorLower_positive
          segment).le))
    (by decide)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.RootContinuation in
/-- The prepared denominator floor can only decrease the point-movement coefficient.

The retained maximum keeps the same point-error coefficient as an input.
Its unchanged value therefore bounds that coefficient weakly. -/
theorem preparedPointErrorCoefficient_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.preparedPointErrorCoefficient <=
      pointErrorCoefficient differential prepared.segment := by
  apply Fraction.Order.Field.scaled_div_square_antitone
  · exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Power.Bounds.IntegrationQuotientVariation.powerSlope_nonnegative
          prepared.ambient.normSqBound_nonneg differential.exponent)
        (UniformSquareRootPreparation.rootAmbient
          prepared.segment).normSqBound_nonneg)
  · exact
      PreparedModels.segmentDenominatorLower_positive
        prepared.segment
  · exact Fraction.Order.Basic.le_max_left _ _

open Purelib.Data.Rat in
/-- The prepared denominator floor can only decrease the root-movement coefficient.

The retained maximum keeps the same root-error coefficient as an input.
Its unchanged value therefore bounds that coefficient weakly. -/
theorem preparedRootErrorCoefficient_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.preparedRootErrorCoefficient <=
      rootErrorCoefficient differential prepared.segment := by
  unfold preparedRootErrorCoefficient rootErrorCoefficient
  apply add_le_add
  · apply Fraction.Order.Field.scaled_div_square_antitone
    · exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.pow_nonneg_direct
          prepared.ambient.normSqBound_nonneg differential.exponent)
    · exact
        PreparedModels.segmentDenominatorLower_positive
          prepared.segment
    · exact Fraction.Order.Basic.le_max_left _ _
  · exact le_rfl

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- The model-error allowance equals the sum of the prepared point and root coefficients times their respective
movements. -/
theorem modelErrorAllowance_eq_preparedLinear {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.modelErrorAllowance =
      prepared.preparedPointErrorCoefficient * prepared.pointMovement +
        prepared.preparedRootErrorCoefficient *
          prepared.preparedRootDiameter := by
  simpa only [modelErrorAllowance, rawVariation,
    preparedPointErrorCoefficient, preparedRootErrorCoefficient] using
    Budget.Quotient.quotientBound_add_rootMovement_eq_linear
      (Power.Bounds.IntegrationQuotientVariation.powerSlope
        prepared.ambient.normSqBound differential.exponent)
      (prepared.ambient.normSqBound ^ differential.exponent)
      (UniformSquareRootPreparation.rootAmbient
        prepared.segment).normSqBound
      prepared.preparedDenominatorLower prepared.pointMovement
        prepared.preparedRootDiameter

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The segment's point and root coefficients give an upper bound for the actual model-error allowance. -/
theorem modelErrorAllowance_le_linear {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.modelErrorAllowance <=
      pointErrorCoefficient differential prepared.segment *
          prepared.pointMovement +
        rootErrorCoefficient differential prepared.segment *
          prepared.preparedRootDiameter := by
  rw [prepared.modelErrorAllowance_eq_preparedLinear]
  exact add_le_add
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      prepared.preparedPointErrorCoefficient_le
      (Norm.Basic.normSq_nonneg _))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      prepared.preparedRootErrorCoefficient_le
      prepared.preparedRootDiameter_positive.le)

open Purelib.Data.Rat in
/-- Separate upper bounds for point movement and root diameter give the corresponding weighted model-error bound. -/
theorem modelErrorAllowance_le_of_separate_targets {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (pointTarget rootTarget : Coordinate)
    (pointLe : prepared.pointMovement <= pointTarget)
    (rootLe : prepared.preparedRootDiameter <= rootTarget) :
    prepared.modelErrorAllowance <=
      pointErrorCoefficient differential prepared.segment * pointTarget +
        rootErrorCoefficient differential prepared.segment * rootTarget := by
  exact prepared.modelErrorAllowance_le_linear.trans
    (add_le_add
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct pointLe
        (pointErrorCoefficient_nonnegative differential prepared.segment))
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct rootLe
        (rootErrorCoefficient_nonnegative differential prepared.segment)))

/-- A common target for point movement and the requested root diameter bounds the model allowance by the sum of its
coefficients times that target. -/
theorem modelErrorAllowance_le_of_targets {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (target : Coordinate)
    (pointTarget : prepared.pointMovement <= target)
    (rootTarget : prepared.request.rootDiameter <= target) :
    prepared.modelErrorAllowance <=
      (pointErrorCoefficient differential prepared.segment +
        rootErrorCoefficient differential prepared.segment) * target := by
  calc
    prepared.modelErrorAllowance <=
        pointErrorCoefficient differential prepared.segment * target +
          rootErrorCoefficient differential prepared.segment * target :=
      prepared.modelErrorAllowance_le_of_separate_targets target target
        pointTarget (prepared.preparedRootDiameter_lt_requested.le.trans
          rootTarget)
    _ = (pointErrorCoefficient differential prepared.segment +
          rootErrorCoefficient differential prepared.segment) * target := by
      ring1

/-- Allocate one eighth of the model-error allowance to the coefficient reading's squared radius. -/
def readingTarget {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.modelErrorAllowance / 8

open Purelib.Data.Rat in
/-- The allocated coefficient-reading target is strictly positive. -/
theorem readingTarget_positive {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    0 < prepared.readingTarget :=
  Fraction.Order.Field.div_pos_direct
    prepared.modelErrorAllowance_positive (by decide)

open Purelib.Approximation.Gaussian in
/-- Pair the coefficient's original numerator state with the residual-certified root state at the exact query point. -/
def residualCoefficientState {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (prepared.coefficient fraction inside).name.process.State := by
  change
    (Name.Coherent.Power.namedPower
      (Name.Coherent.CoherentNamed.Coherence.exact (prepared.point fraction))
        differential.exponent).name.process.State ×
      (prepared.sheetValue fraction inside).value.name.process.State
  exact ((prepared.coefficient fraction inside).name.state.1,
    prepared.residualRootState fraction inside)

/-- Refine the retained residual coefficient state to the positive reading target. -/
def readingState {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (prepared.coefficient fraction inside).name.process.State :=
  (prepared.coefficient fraction inside).name.process.refine
    (prepared.residualCoefficientState fraction inside) prepared.readingTarget
      prepared.readingTarget_positive

/-- Read the exact witness of the refined coefficient state at the requested fraction. -/
def reading {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) : Gaussian :=
  ((prepared.coefficient fraction inside).name.process.witness
    (prepared.readingState fraction inside)).val

/-- The coefficient reading is possible in the exact refined state from which it is read. -/
theorem reading_possible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (prepared.coefficient fraction inside).name.process.Possible
      (prepared.readingState fraction inside)
        (prepared.reading fraction inside) :=
  ((prepared.coefficient fraction inside).name.process.witness
    (prepared.readingState fraction inside)).property

/-- The refined coefficient state's squared ball radius is strictly below its allocated reading target. -/
theorem reading_radius_lt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    ((prepared.coefficient fraction inside).name.process.ball
      (prepared.readingState fraction inside)).radiusSq <
        prepared.readingTarget :=
  (prepared.coefficient fraction inside).name.process.accurate
    (prepared.residualCoefficientState fraction inside) prepared.readingTarget
      prepared.readingTarget_positive

/-- Read the coefficient witness at the original local source point. -/
def baseReading {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Gaussian :=
  prepared.reading 0 prepared.baseInside

set_option genInjectivity false in
/-- A retained base coefficient state with cached value and denominator witnesses, exact quotient identity, and accuracy
certificates.

The thunks preserve the chosen witnesses. Possibility, persistence to the original reading state, and the squared-radius
bound all concern this same retained state. -/
structure CenterState {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) where
  /-- The exact retained coefficient process state. -/ state : (prepared.coefficient 0
    prepared.baseInside).name.process.State
  /-- The thunk retaining the selected base coefficient witness. -/ cachedValue : Thunk Gaussian
  /-- The cached coefficient witness is possible at the same retained state. -/ cachedValue_possible :
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
      state cachedValue.get
  /-- The thunk retaining the selected denominator witness. -/ cachedDenominator : Thunk Gaussian
  /-- The cached denominator is possible at the retained state's denominator component. -/ cachedDenominator_possible :
    (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
      state.2 cachedDenominator.get
  /-- The cached coefficient equals the original point power divided by its exact cached denominator. -/
    cachedValue_eq_power_div_denominator :
    cachedValue.get =
      prepared.point 0 ^ differential.exponent / cachedDenominator.get
  /-- Every possible retained-state value remains possible at the original reading state. -/ persists : forall {value :
    Gaussian},
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
        state value ->
      (prepared.coefficient 0 prepared.baseInside).name.process.Possible
        (prepared.readingState 0 prepared.baseInside) value
  /-- The retained state's squared ball radius is below the original reading target. -/ radius_lt :
    ((prepared.coefficient 0 prepared.baseInside).name.process.ball
      state).radiusSq < prepared.readingTarget

constructive_injectivity CenterState

namespace CenterState

/-- Retain the exact coefficient witness of a supplied base state in a thunk. -/
def valueThunk {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (state :
      (prepared.coefficient 0 prepared.baseInside).name.process.State) :
    Thunk Gaussian :=
  ⟨fun _ =>
    ((prepared.coefficient 0 prepared.baseInside).name.process.witness
      state).val⟩

/-- Retain the exact denominator witness of a supplied base coefficient state in a thunk. -/
def denominatorThunk {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (state :
      (prepared.coefficient 0 prepared.baseInside).name.process.State) :
    Thunk Gaussian :=
  ⟨fun _ =>
    ((prepared.sheetValue 0 prepared.baseInside).value.name.process.witness
      state.2).val⟩

section
open Purelib.Approximation.Gaussian
/-- Build a center cache from a retained base state and its persistence and accuracy proofs.

Both witness thunks are constructed from that exact state, and the cached coefficient is certified as the original point
power divided by its cached denominator. -/
def ofState {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (state :
      (prepared.coefficient 0 prepared.baseInside).name.process.State)
    (persists : forall {value : Gaussian},
      (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          state value ->
        (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          (prepared.readingState 0 prepared.baseInside) value)
    (radius_lt :
      ((prepared.coefficient 0 prepared.baseInside).name.process.ball
        state).radiusSq < prepared.readingTarget) :
    CenterState prepared := by
  let cachedValue := valueThunk prepared state
  let cachedDenominator := denominatorThunk prepared state
  exact
    { state := state
      cachedValue := cachedValue
      cachedValue_possible := by
        change (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          state
            ((prepared.coefficient 0 prepared.baseInside).name.process.witness
              state).val
        exact ((prepared.coefficient 0
          prepared.baseInside).name.process.witness state).property
      cachedDenominator := cachedDenominator
      cachedDenominator_possible := by
        change
          (prepared.sheetValue 0
            prepared.baseInside).value.name.process.Possible state.2
              ((prepared.sheetValue 0
                prepared.baseInside).value.name.process.witness state.2).val
        exact ((prepared.sheetValue 0
          prepared.baseInside).value.name.process.witness state.2).property
      cachedValue_eq_power_div_denominator := by
        change
          ((Name.Coherent.Power.namedPower
            (Name.Coherent.CoherentNamed.Coherence.exact
              (prepared.point 0)) differential.exponent).name.process.witness
                state.1).val /
              ((prepared.sheetValue 0
                prepared.baseInside).value.name.process.witness state.2).val =
            prepared.point 0 ^ differential.exponent /
              ((prepared.sheetValue 0
                prepared.baseInside).value.name.process.witness state.2).val
        rw [Name.Coherent.Power.namedPower_exact_possible_eq (prepared.point 0)
          differential.exponent state.1
            ((Name.Coherent.Power.namedPower
              (Name.Coherent.CoherentNamed.Coherence.exact
                (prepared.point 0)) differential.exponent).name.process.witness
                  state.1).property]
      persists := persists
      radius_lt := radius_lt }

/-- Build a center cache from supplied exact value and denominator witnesses.

The denominator must be possible at the retained state, and the supplied value must equal the original point power
divided by that same denominator; persistence and accuracy are retained unchanged. -/
def ofCertified {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (state :
      (prepared.coefficient 0 prepared.baseInside).name.process.State)
    (value : Gaussian)
    (denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator)
    (persists : forall {value : Gaussian},
      (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          state value ->
        (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          (prepared.readingState 0 prepared.baseInside) value)
    (radius_lt :
      ((prepared.coefficient 0 prepared.baseInside).name.process.ball
        state).radiusSq < prepared.readingTarget) :
    CenterState prepared := by
  let numerator := Name.Coherent.Power.namedPower
    (Name.Coherent.CoherentNamed.Coherence.exact (prepared.point 0))
      differential.exponent
  let numeratorWitness := numerator.name.process.witness state.1
  have numeratorEq : numeratorWitness.val =
      prepared.point 0 ^ differential.exponent :=
    Name.Coherent.Power.namedPower_exact_possible_eq (prepared.point 0) differential.exponent
      state.1 numeratorWitness.property
  exact
    { state := state
      cachedValue := ⟨fun _ => value⟩
      cachedValue_possible := by
        change ∃ x y : Gaussian,
          numerator.name.process.Possible state.1 x ∧
            (prepared.sheetValue 0
              prepared.baseInside).value.name.process.Possible state.2 y ∧
              value = x / y
        exact ⟨numeratorWitness.val, denominator, numeratorWitness.property,
          denominatorPossible, by rw [numeratorEq, valueEq]⟩
      cachedDenominator := ⟨fun _ => denominator⟩
      cachedDenominator_possible := denominatorPossible
      cachedValue_eq_power_div_denominator := valueEq
      persists := persists
      radius_lt := radius_lt }

end

/-- Build a center cache from a certified denominator, computing the coefficient with that exact retained denominator.
-/
def ofCertifiedDenominator {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (state :
      (prepared.coefficient 0 prepared.baseInside).name.process.State)
    (denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        state.2 denominator)
    (persists : forall {value : Gaussian},
      (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          state value ->
        (prepared.coefficient 0 prepared.baseInside).name.process.Possible
          (prepared.readingState 0 prepared.baseInside) value)
    (radius_lt :
      ((prepared.coefficient 0 prepared.baseInside).name.process.ball
        state).radiusSq < prepared.readingTarget) :
    CenterState prepared :=
  ofCertified prepared state
    (prepared.point 0 ^ differential.exponent / denominator) denominator
      denominatorPossible rfl persists radius_lt

/-- Replace the cached value and denominator witnesses at the same retained center state using certified possibilities
and quotient equality. -/
def recache {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    CenterState prepared :=
  ofCertified prepared center.state value denominator denominatorPossible
    valueEq center.persists center.radius_lt

/-- Recaching witnesses preserves the exact original center state. -/
@[simp] theorem recache_state {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    (center.recache value denominator denominatorPossible valueEq).state =
      center.state := rfl

open Purelib.Approximation.Gaussian in
/-- Construct a center state at a later sampling index whose refinement target fits the reading tolerance. -/
def atIndex {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (index : Nat)
    (accurate : Process.Sampling.refinementTarget index <
      prepared.readingTarget) :
    CenterState prepared := by
  let state := Process.Sampling.stateAt
    (prepared.coefficient 0 prepared.baseInside).name.process
      (prepared.readingState 0 prepared.baseInside) index
  exact ofState prepared state
    (by
        intro value possible
        exact Process.Sampling.stateAt_possible_at_start
          (prepared.coefficient 0 prepared.baseInside).name.process
            (prepared.readingState 0 prepared.baseInside) index possible)
    ((Process.Sampling.stateAt_accurate
      (prepared.coefficient 0 prepared.baseInside).name.process
        (prepared.readingState 0 prepared.baseInside) index).trans accurate)

open Purelib.Approximation.Rational in
/-- Search from zero for a geometric sampling target strictly below the original reading tolerance. -/
def canonicalIndex {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Nat :=
  Geometric.Search.firstQuarterBelow 1 0 prepared.readingTarget

/-- Cache the exact base reading state and its witnesses with its retained accuracy proof. -/
def canonical {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : CenterState prepared := by
  let state := prepared.readingState 0 prepared.baseInside
  exact ofState prepared state (fun possible => possible)
    (prepared.reading_radius_lt 0 prepared.baseInside)

/-- Read the retained cached coefficient witness. -/
def value {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Gaussian :=
  center.cachedValue.get

/-- The retained cached coefficient witness is possible at the indexed state. -/
theorem value_possible {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
      center.state center.value := by
  exact center.cachedValue_possible

/-- The retained coefficient witness remains possible at the original reading state. -/
theorem value_possible_at_readingState {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
      (prepared.readingState 0 prepared.baseInside) center.value :=
  center.persists center.value_possible

/-- Read the exact cached denominator witness. -/
def denominator {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Gaussian :=
  center.cachedDenominator.get

/-- The cached denominator is possible in the denominator component of the retained coefficient state. -/
theorem denominator_possible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
      center.state.2 center.denominator :=
  center.cachedDenominator_possible

/-- The cached coefficient equals the original base-point power divided by its retained denominator. -/
theorem value_eq_power_div_denominator {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    center.value =
      prepared.point 0 ^ differential.exponent / center.denominator := by
  exact center.cachedValue_eq_power_div_denominator

/-- Recaching reads back the exact supplied coefficient value. -/
@[simp] theorem recache_value {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    (center.recache value denominator denominatorPossible valueEq).value =
      value := rfl

/-- Recaching reads back the exact supplied denominator. -/
@[simp] theorem recache_denominator {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    (center.recache value denominator denominatorPossible valueEq).denominator =
      denominator := rfl

/-- For exponent zero, the cached coefficient equals the reciprocal of its retained denominator. -/
theorem value_eq_one_div_denominator_of_exponent_zero {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    center.value = 1 / center.denominator := by
  rw [center.value_eq_power_div_denominator, exponentZero, pow_zero]

open Purelib.Riemann.Branches in
/-- The cached denominator lies in the original canonical prepared root box. -/
theorem denominator_in_prepared_box {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    (PreparedSheetContinuation.prepared prepared.segment
      prepared.left prepared.owner prepared.request).track.initial.box.Contains
        center.denominator := by
  exact
    PreparedModels.sheetValueAtCached_candidate_in_prepared_box
      curve differential prepared.segment prepared.within prepared.left
        prepared.owner prepared.request prepared.cached prepared.ordered
          prepared.small prepared.sheet 0 prepared.baseInside center.state.2
            center.denominator_possible

/-- The cached denominator lies in the exact retained prepared-owner box. -/
theorem denominator_in_cached_prepared_box {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    prepared.cached.preparedOwner.track.initial.box.Contains
      center.denominator := by
  rw [prepared.cached.preparedOwner_eq]
  exact center.denominator_in_prepared_box

open Purelib.Approximation.Gaussian in
/-- Read the ball of the retained denominator state. -/
def denominatorBall {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Approximation.Gaussian.Enclosure.Ball :=
  (prepared.sheetValue 0 prepared.baseInside).value.name.process.ball
    center.state.2

/-- The retained denominator witness lies in its own process ball. -/
theorem denominator_in_ball {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    center.denominatorBall.Contains center.denominator := by
  exact
    (prepared.sheetValue 0 prepared.baseInside).value.name.process.possible_inside
      center.denominator_possible

/-- The fixed one-tenth coordinate radius for a sufficiently small denominator ball. -/
def denominatorSectorRadius : Coordinate := 1 / 10

/-- The fixed denominator-sector radius is nonnegative. -/
theorem denominatorSectorRadius_nonnegative :
    (0 : Coordinate) <= denominatorSectorRadius := by decide

open Purelib.Geometry.Rational in
/-- Use the one-tenth square about a sufficiently small denominator ball, otherwise the original cached prepared box. -/
def denominatorProjectionBox {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Box :=
  let ball := center.denominatorBall
  if ball.radiusSq <= denominatorSectorRadius ^ 2 then
    Box.Square.Centered.Affine.centeredSquare ball.center
      denominatorSectorRadius denominatorSectorRadius_nonnegative
  else
    prepared.cached.preparedOwner.track.initial.box

open Purelib.Data.Gaussian in
/-- The retained denominator witness lies in whichever projection box was selected. -/
theorem denominator_in_projection_box {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    center.denominatorProjectionBox.Contains center.denominator := by
  unfold denominatorProjectionBox
  dsimp only
  split
  · rename_i radiusSmall
    have distanceBound :
        Data.Gaussian.Norm.Basic.normSq
            (center.denominator - center.denominatorBall.center) <=
          denominatorSectorRadius ^ 2 :=
      center.denominator_in_ball.trans radiusSmall
    have bounds := Norm.Bounds.coordinate_bounds_of_normSq_le
      denominatorSectorRadius_nonnegative distanceBound
    have realLower : -denominatorSectorRadius <=
        center.denominator.re - center.denominatorBall.center.re := by
      simpa only [Basic.sub_re] using bounds.1
    have realUpper :
        center.denominator.re - center.denominatorBall.center.re <=
          denominatorSectorRadius := by
      simpa only [Basic.sub_re] using bounds.2.1
    have imaginaryLower : -denominatorSectorRadius <=
        center.denominator.im - center.denominatorBall.center.im := by
      simpa only [Basic.sub_im] using bounds.2.2.1
    have imaginaryUpper :
        center.denominator.im - center.denominatorBall.center.im <=
          denominatorSectorRadius := by
      simpa only [Basic.sub_im] using bounds.2.2.2
    exact
      ⟨by
        calc
          center.denominatorBall.center.re - denominatorSectorRadius =
              -denominatorSectorRadius + center.denominatorBall.center.re := by
                ring1
          _ <= (center.denominator.re -
                center.denominatorBall.center.re) +
              center.denominatorBall.center.re :=
            add_le_add_left realLower center.denominatorBall.center.re
          _ = center.denominator.re := by ring1,
        by
          calc
            center.denominator.re =
                (center.denominator.re - center.denominatorBall.center.re) +
                  center.denominatorBall.center.re := by ring1
            _ <= denominatorSectorRadius +
                center.denominatorBall.center.re :=
              add_le_add_left realUpper center.denominatorBall.center.re
            _ = center.denominatorBall.center.re +
                denominatorSectorRadius := by ring1,
        by
          calc
            center.denominatorBall.center.im - denominatorSectorRadius =
                -denominatorSectorRadius +
                  center.denominatorBall.center.im := by ring1
            _ <= (center.denominator.im -
                  center.denominatorBall.center.im) +
                center.denominatorBall.center.im :=
              add_le_add_left imaginaryLower center.denominatorBall.center.im
            _ = center.denominator.im := by ring1,
        by
          calc
            center.denominator.im =
                (center.denominator.im - center.denominatorBall.center.im) +
                  center.denominatorBall.center.im := by ring1
            _ <= denominatorSectorRadius +
                center.denominatorBall.center.im :=
              add_le_add_left imaginaryUpper center.denominatorBall.center.im
            _ = center.denominatorBall.center.im +
                denominatorSectorRadius := by ring1⟩
  · exact center.denominator_in_cached_prepared_box

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The real part of displacement divided by a Gaussian denominator is its coordinate projection divided by the
denominator's squared norm. -/
theorem mul_one_div_re (displacement denominator : Gaussian) :
    (displacement * (1 / denominator)).re =
      (displacement.re * denominator.re +
        displacement.im * denominator.im) /
          Data.Gaussian.Norm.Basic.normSq denominator := by
  have oneDiv : (1 / denominator : Gaussian) = denominator⁻¹ := by
    change 1 * denominator⁻¹ = denominator⁻¹
    exact Basic.one_mul _
  rw [oneDiv]
  rw [Field.inv_eq]
  change displacement.re *
          (denominator.re /
            Data.Gaussian.Norm.Basic.normSq denominator) -
        displacement.im *
          (-denominator.im /
            Data.Gaussian.Norm.Basic.normSq denominator) = _
  rw [Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct,
    Fraction.Field.div_eq_mul_inv_direct]
  ring1

open Purelib.Approximation.Gaussian
/-- Rebase the original coefficient process at the retained state. -/
def named {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Name.Basic.Named :=
  { process := (prepared.coefficient 0 prepared.baseInside).name.process
    state := center.state }

/-- The original coefficient name is operationally equivalent to its rebasing at the retained state. -/
def equivalent {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    Equivalence.NamedEquivalent
      (prepared.coefficient 0 prepared.baseInside).name center.named :=
  Name.Coherent.CoherentNamed.rebaseEquivalent
    (prepared.coefficient 0 prepared.baseInside) center.state

/-- Rebase the original base coefficient process at its canonical reading state. -/
def baseNamed {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    Name.Basic.Named :=
  { process := (prepared.coefficient 0 prepared.baseInside).name.process
    state := prepared.readingState 0 prepared.baseInside }

/-- The original base coefficient name is equivalent to its canonical reading-state rebasing. -/
def baseEquivalent {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    Equivalence.NamedEquivalent
      (prepared.coefficient 0 prepared.baseInside).name
      (baseNamed prepared) :=
  Name.Coherent.CoherentNamed.rebaseEquivalent
    (prepared.coefficient 0 prepared.baseInside)
      (prepared.readingState 0 prepared.baseInside)

end CenterState

/-! ## Finite box projection bounds -/

/-- Choose the lower coordinate product using the interval endpoint appropriate to the coefficient's sign. -/
def signedCoordinateLower (coefficient lower upper : Coordinate) : Coordinate :=
  if 0 <= coefficient then coefficient * lower else coefficient * upper

open Purelib.Data.Rat in
/-- The sign-selected endpoint product bounds the product with every coordinate inside the original interval.

The same coefficient sign selects the original lower or upper endpoint.
Nonnegative scaling and direct order reversal certify that retained product. -/
theorem signedCoordinateLower_le (coefficient lower value upper : Coordinate)
    (lowerLe : lower <= value) (valueLe : value <= upper) :
    signedCoordinateLower coefficient lower upper <= coefficient * value := by
  by_cases nonnegative : 0 <= coefficient
  · rw [signedCoordinateLower, if_pos nonnegative]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      lowerLe nonnegative
  · rw [signedCoordinateLower, if_neg nonnegative]
    have nonpositive : coefficient <= 0 := le_of_not_ge nonnegative
    have negNonnegative : 0 <= -coefficient := by
      have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct nonpositive
      simpa only [neg_zero] using reversed
    have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      valueLe negNonnegative
    calc
      coefficient * upper = -((-coefficient) * upper) := by ring1
      _ <= -((-coefficient) * value) :=
        Fraction.Order.Arithmetic.neg_le_neg_direct scaled
      _ = coefficient * value := by ring1

/-- Sum the two sign-selected coordinate lower bounds for projection of a box onto a displacement. -/
def boxProjectionLower (box : Box) (displacement : Gaussian) : Coordinate :=
  signedCoordinateLower displacement.re box.xLower box.xUpper +
    signedCoordinateLower displacement.im box.yLower box.yUpper

/-- The computed box projection bounds the coordinate dot product with every contained Gaussian value. -/
theorem boxProjectionLower_le {box : Box} {displacement value : Gaussian}
    (inside : box.Contains value) :
    boxProjectionLower box displacement <=
      displacement.re * value.re + displacement.im * value.im := by
  exact add_le_add
    (signedCoordinateLower_le displacement.re box.xLower value.re box.xUpper
      inside.1 inside.2.1)
    (signedCoordinateLower_le displacement.im box.yLower value.im box.yUpper
      inside.2.2.1 inside.2.2.2)

/-- Select the upper or lower denominator bound according to the numerator's sign. -/
def signedQuotientLower (numerator denominatorLower denominatorUpper : Coordinate) :
    Coordinate :=
  if 0 <= numerator then numerator / denominatorUpper
  else numerator / denominatorLower

open Purelib.Data.Rat in
/-- With a positive denominator lower bound, the sign-selected quotient bounds division by every retained denominator in
the interval.

The numerator sign selects the original upper or positive lower denominator.
Direct division monotonicity and order reversal retain the same quotient bound. -/
theorem signedQuotientLower_le (numerator denominatorLower denominator
    denominatorUpper : Coordinate) (denominatorLowerPositive : 0 < denominatorLower)
    (lowerLe : denominatorLower <= denominator)
    (upperLe : denominator <= denominatorUpper) :
    signedQuotientLower numerator denominatorLower denominatorUpper <=
      numerator / denominator := by
  by_cases numeratorNonnegative : 0 <= numerator
  · rw [signedQuotientLower, if_pos numeratorNonnegative]
    exact Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      numeratorNonnegative (denominatorLowerPositive.trans_le lowerLe) upperLe
  · rw [signedQuotientLower, if_neg numeratorNonnegative]
    have numeratorNonpositive : numerator <= 0 := le_of_not_ge numeratorNonnegative
    have negNumeratorNonnegative : 0 <= -numerator :=
      by
        have reversed := Fraction.Order.Arithmetic.neg_le_neg_direct numeratorNonpositive
        simpa only [neg_zero] using reversed
    have positiveDivision :
        (-numerator) / denominator <=
          (-numerator) / denominatorLower :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        negNumeratorNonnegative denominatorLowerPositive lowerLe
    calc
      numerator / denominatorLower =
          -((-numerator) / denominatorLower) := by
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct]
        ring1
      _ <= -((-numerator) / denominator) :=
        Fraction.Order.Arithmetic.neg_le_neg_direct positiveDivision
      _ = numerator / denominator := by
        rw [Fraction.Field.div_eq_mul_inv_direct,
          Fraction.Field.div_eq_mul_inv_direct]
        ring1

/-- The fixed thirty-two-bit precision for downward dyadic rounding of real lower bounds. -/
def realLowerDyadicPrecision : Nat := 32

/-- The rational scale two to the thirty-second power used for downward rounding. -/
def realLowerDyadicScale : Coordinate :=
  (2 : Coordinate) ^ realLowerDyadicPrecision

section
open Purelib.Data.Rat
/-- Round an exact rational downward to the fixed thirty-two-bit dyadic grid. -/
def dyadicRealLower (source : Coordinate) : Coordinate :=
  Fraction.Cast.fromInt
      (Rounding.Floor.floor (source * realLowerDyadicScale)) /
    realLowerDyadicScale

/-- The fixed dyadic rounding scale is strictly positive. -/
private theorem realLowerDyadicScale_positive :
    (0 : Coordinate) < realLowerDyadicScale := by
  unfold realLowerDyadicScale
  exact Fraction.Order.Arithmetic.pow_pos_direct (by decide)
    realLowerDyadicPrecision

/-- Downward dyadic rounding never exceeds the original rational value.

The original exact floor is retained at the fixed dyadic scale.
Its direct rational floor certificate survives division by that positive scale. -/
theorem dyadicRealLower_le (source : Coordinate) :
    dyadicRealLower source <= source := by
  unfold dyadicRealLower
  apply (Fraction.Order.Field.div_le_iff_pos
    realLowerDyadicScale_positive).2
  have floorBound := Rounding.Floor.intCast_floor_le
    (source * realLowerDyadicScale)
  rw [Fraction.Cast.intCast_eq_fromInt] at floorBound
  exact floorBound

/-- Round the box's nonnegative squared-norm upper bound upward to a natural number. -/
def boxNormSqCeil (box : Box) : Coordinate :=
  (Rounding.Floor.ceilNat box.normSqBound : Nat)

/-- The natural ceiling bounds the original box squared-norm estimate. -/
theorem normSqBound_le_boxNormSqCeil (box : Box) :
    box.normSqBound <= boxNormSqCeil box := by
  exact Rounding.Floor.le_natCast_ceilNat_of_nonneg
    box.normSqBound_nonneg

end

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Read the original cleared segment's magnitude-based denominator floor. -/
def cellDenominatorLower
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start
      finish) : Coordinate :=
  PreparedModels.magnitudeDenominatorLower segment

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The segment's magnitude-based denominator floor is strictly positive. -/
theorem cellDenominatorLower_positive
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start
      finish) :
    0 < cellDenominatorLower segment := by
  unfold cellDenominatorLower
    PreparedModels.magnitudeDenominatorLower
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct
    (SquareRoot.Radius.Dyadic.Geometric.dyadicSquareRadius_positive _) (by decide))
    (by decide)

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Combine the segment magnitude floor with the squared-norm lower bound of the supplied original box. -/
def geometricDenominatorLower
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start
      finish) (box : Box) : Coordinate :=
  max (cellDenominatorLower segment) (boxNormSqLower box)

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Data.Rat in
/-- The combined segment-and-box denominator floor is strictly positive.

The unchanged maximum includes the original positive geometric
denominator floor from the retained clear segment. -/
theorem geometricDenominatorLower_positive
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start
      finish) (box : Box) :
    0 < geometricDenominatorLower segment box :=
  (cellDenominatorLower_positive segment).trans_le (Fraction.Order.Basic.le_max_left _ _)

open Purelib.Data.Rat in
/-- Twice the sum of two reading targets equals half the model-error allowance. -/
private theorem twice_readingTarget_sum_eq_half {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    2 * (prepared.readingTarget + prepared.readingTarget) =
      prepared.modelErrorAllowance / 2 := by
  unfold readingTarget
  apply Fraction.Field.mul_right_cancel_of_ne
    (show (8 : Coordinate) ≠ 0 by decide)
  calc
    (2 * (prepared.modelErrorAllowance / 8 +
        prepared.modelErrorAllowance / 8)) * 8 =
      2 * ((prepared.modelErrorAllowance / 8) * 8 +
        (prepared.modelErrorAllowance / 8) * 8) := by ring1
    _ = 2 * (prepared.modelErrorAllowance +
        prepared.modelErrorAllowance) := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ 8 (by decide)]
    _ = prepared.modelErrorAllowance * 4 := by ring1
    _ = ((prepared.modelErrorAllowance / 2) * 2) * 4 := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ 2 (by decide)]
    _ = (prepared.modelErrorAllowance / 2) * 8 := by ring1

section
open Purelib.Approximation.Gaussian
/-- Read a later sampling witness from the original base reading state. -/
def laterBaseValue {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (index : Nat) : Gaussian :=
  Process.Sampling.witnessAt
    (prepared.coefficient 0 prepared.baseInside).name.process
      (prepared.readingState 0 prepared.baseInside) index

/-- Every later base sample remains possible at the original base reading state. -/
theorem laterBaseValue_possible_at_state {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (index : Nat) :
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
      (prepared.readingState 0 prepared.baseInside)
        (prepared.laterBaseValue index) :=
  Process.Sampling.witnessAt_possible_start
    (prepared.coefficient 0 prepared.baseInside).name.process
      (prepared.readingState 0 prepared.baseInside) index

end

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Every later base sample is within the model-error allowance in squared distance of the original base reading. -/
theorem laterBaseValue_sub_baseReading_lt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (prepared.laterBaseValue index - prepared.baseReading) <
      prepared.modelErrorAllowance := by
  let process := (prepared.coefficient 0 prepared.baseInside).name.process
  let ball := process.ball (prepared.readingState 0 prepared.baseInside)
  have laterInside : ball.Contains (prepared.laterBaseValue index) :=
    process.possible_inside (prepared.laterBaseValue_possible_at_state index)
  have baseInside : ball.Contains prepared.baseReading :=
    process.possible_inside
      (prepared.reading_possible 0 prepared.baseInside)
  have identity : prepared.laterBaseValue index - prepared.baseReading =
      (prepared.laterBaseValue index - ball.center) +
        (ball.center - prepared.baseReading) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  have baseReverse :
      Data.Gaussian.Norm.Basic.normSq
          (ball.center - prepared.baseReading) <= ball.radiusSq := by
    have reverse : ball.center - prepared.baseReading =
        -(prepared.baseReading - ball.center) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [reverse, Norm.Basic.normSq_neg]
    exact baseInside
  rw [identity]
  calc
    Data.Gaussian.Norm.Basic.normSq
        ((prepared.laterBaseValue index - ball.center) +
          (ball.center - prepared.baseReading)) <=
      2 * (ball.radiusSq + ball.radiusSq) :=
      (Norm.Bounds.normSq_add_le_two _ _).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add laterInside baseReverse) (by decide))
    _ < 2 * (prepared.readingTarget + prepared.readingTarget) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide)
        (Fraction.Order.Arithmetic.add_lt_add_direct
          (prepared.reading_radius_lt 0 prepared.baseInside)
          (prepared.reading_radius_lt 0 prepared.baseInside))
    _ = prepared.modelErrorAllowance / 2 :=
      twice_readingTarget_sum_eq_half prepared
    _ < prepared.modelErrorAllowance :=
      Purelib.Data.Rat.Fraction.Order.Field.half_lt_self prepared.modelErrorAllowance_positive

/-- A certified replacement witness at the same center state differs from the original cached value by less than the
model allowance in squared norm. -/
theorem CenterState.recache_value_sub_value_lt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    Data.Gaussian.Norm.Basic.normSq
        ((center.recache value denominator denominatorPossible valueEq).value -
          center.value) < prepared.modelErrorAllowance := by
  let replacement :=
    center.recache value denominator denominatorPossible valueEq
  let process := (prepared.coefficient 0 prepared.baseInside).name.process
  let ball := process.ball center.state
  have replacementPossible : process.Possible center.state replacement.value := by
    exact replacement.value_possible
  have replacementInside : ball.Contains replacement.value :=
    process.possible_inside replacementPossible
  have centerInside : ball.Contains center.value :=
    process.possible_inside center.value_possible
  have identity : replacement.value - center.value =
      (replacement.value - ball.center) + (ball.center - center.value) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  have centerReverse :
      Data.Gaussian.Norm.Basic.normSq
          (ball.center - center.value) <= ball.radiusSq := by
    have reverse : ball.center - center.value =
        -(center.value - ball.center) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [reverse, Norm.Basic.normSq_neg]
    exact centerInside
  change Data.Gaussian.Norm.Basic.normSq
      (replacement.value - center.value) < prepared.modelErrorAllowance
  calc
    Data.Gaussian.Norm.Basic.normSq
        (replacement.value - center.value) =
      Data.Gaussian.Norm.Basic.normSq
        ((replacement.value - ball.center) +
          (ball.center - center.value)) := by rw [identity]
    _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
      (Norm.Bounds.normSq_add_le_two _ _).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add replacementInside centerReverse) (by decide))
    _ < 2 * (prepared.readingTarget + prepared.readingTarget) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide)
        (Fraction.Order.Arithmetic.add_lt_add_direct
          replacement.radius_lt center.radius_lt)
    _ = prepared.modelErrorAllowance / 2 :=
      twice_readingTarget_sum_eq_half prepared
    _ < prepared.modelErrorAllowance :=
      Purelib.Data.Rat.Fraction.Order.Field.half_lt_self prepared.modelErrorAllowance_positive

end

section
open Purelib.Approximation.Gaussian
/-- Read a later sampling witness from the exact retained coefficient state. -/
def CenterState.laterValue {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (index : Nat) : Gaussian :=
  Process.Sampling.witnessAt
    (prepared.coefficient 0 prepared.baseInside).name.process
      center.state index

/-- A later sampling witness remains possible at the retained starting state. -/
theorem CenterState.laterValue_possible_at_state {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (index : Nat) :
    (prepared.coefficient 0 prepared.baseInside).name.process.Possible
      center.state (center.laterValue index) :=
  Process.Sampling.witnessAt_possible_start
    (prepared.coefficient 0 prepared.baseInside).name.process
      center.state index

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A later witness differs from the retained value by less than the model-error allowance in squared norm. -/
theorem CenterState.laterValue_sub_value_lt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (center.laterValue index - center.value) <
      prepared.modelErrorAllowance := by
  let process := (prepared.coefficient 0 prepared.baseInside).name.process
  let ball := process.ball center.state
  have laterInside : ball.Contains (center.laterValue index) :=
    process.possible_inside (center.laterValue_possible_at_state index)
  have centerInside : ball.Contains center.value :=
    process.possible_inside center.value_possible
  have identity : center.laterValue index - center.value =
      (center.laterValue index - ball.center) +
        (ball.center - center.value) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  have centerReverse :
      Data.Gaussian.Norm.Basic.normSq
          (ball.center - center.value) <= ball.radiusSq := by
    have reverse : ball.center - center.value =
        -(center.value - ball.center) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [reverse, Norm.Basic.normSq_neg]
    exact centerInside
  calc
    Data.Gaussian.Norm.Basic.normSq
        (center.laterValue index - center.value) =
      Data.Gaussian.Norm.Basic.normSq
        ((center.laterValue index - ball.center) +
          (ball.center - center.value)) := by rw [identity]
    _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
      (Norm.Bounds.normSq_add_le_two _ _).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add laterInside centerReverse) (by decide))
    _ < 2 * (prepared.readingTarget + prepared.readingTarget) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide)
        (Fraction.Order.Arithmetic.add_lt_add_direct
          center.radius_lt center.radius_lt)
    _ = prepared.modelErrorAllowance / 2 :=
      twice_readingTarget_sum_eq_half prepared
    _ < prepared.modelErrorAllowance :=
      Purelib.Data.Rat.Fraction.Order.Field.half_lt_self prepared.modelErrorAllowance_positive

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- A child center state with a quantitative comparison to the original retained parent center.

The squared difference is below twice the sum of the requested comparison tolerance and the parent's model-error
allowance. -/
structure CenterAlignment {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    (parentCenter : CenterState parent) (target : Coordinate) where
  /-- The exact selected center state of the original child edge. -/ childCenter : CenterState child
  /-- The actual child-to-parent value difference is bounded in squared norm by twice the sum of the comparison target
    and the parent model allowance. -/ close :
    Data.Gaussian.Norm.Basic.normSq
        (childCenter.value - parentCenter.value) <
      2 * (target + parent.modelErrorAllowance)

constructive_injectivity CenterAlignment

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Align an equivalent child coefficient to the retained parent center using the requested positive comparison
tolerance.

The operational name comparison chooses actual later indices; the resulting child center retains that state and its own
reading accuracy. -/
def alignRight {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    (parentCenter : CenterState parent)
    (coefficientEquivalent :
      Equivalence.NamedEquivalent
        (parent.coefficient 0 parent.baseInside).name
        (child.coefficient 0 child.baseInside).name)
    (target : Coordinate) (positive : 0 < target) :
    CenterAlignment parent child parentCenter target := by
  let alignedEquivalent : Equivalence.NamedEquivalent
      parentCenter.named (CenterState.baseNamed child) :=
    Equivalence.NamedEquivalent.trans
      parentCenter.equivalent.symm
      (Equivalence.NamedEquivalent.trans coefficientEquivalent
        (CenterState.baseEquivalent child))
  let childStart := CenterState.canonicalIndex child
  let comparison := alignedEquivalent.compare 0 childStart target positive
  let childState := Process.Sampling.stateAt
    (child.coefficient 0 child.baseInside).name.process
      (child.readingState 0 child.baseInside) comparison.rightIndex
  let childCenter : CenterState child :=
    CenterState.ofState child childState
      (by
        intro value possible
        exact Process.Sampling.stateAt_possible_at_start
          (child.coefficient 0 child.baseInside).name.process
            (child.readingState 0 child.baseInside)
              comparison.rightIndex possible)
      (by
        have indexOrder : Process.Sampling.refinementTarget
            comparison.rightIndex <=
          Process.Sampling.refinementTarget childStart := by
          unfold Process.Sampling.refinementTarget
          exact quarterRadius_antitone
            (by decide) comparison.right_ge
        exact
          ((Process.Sampling.stateAt_accurate
            (child.coefficient 0 child.baseInside).name.process
              (child.readingState 0 child.baseInside)
                comparison.rightIndex).trans_le indexOrder).trans
            (Geometric.Search.firstQuarterBelow_accurate
              1 (by decide) 0 child.readingTarget
                child.readingTarget_positive))
  exact
    { childCenter := childCenter
      close := by
        let parentLater := parentCenter.laterValue comparison.leftIndex
        have alignedClose := comparison.close
          (Nat.le_refl comparison.leftIndex)
          (Nat.le_refl comparison.rightIndex)
        have alignedCloseReverse :
            Data.Gaussian.Norm.Basic.normSq
                (childCenter.value - parentLater) < target := by
          have reverse : childCenter.value - parentLater =
              -(parentLater - childCenter.value) := by
            apply Basic.ext <;>
              simp only [Basic.sub_re,
                Basic.sub_im,
                Basic.neg_re,
                Basic.neg_im] <;> ring1
          rw [reverse, Norm.Basic.normSq_neg]
          exact alignedClose
        have parentTail :=
          parentCenter.laterValue_sub_value_lt comparison.leftIndex
        have identity : childCenter.value - parentCenter.value =
            (childCenter.value - parentLater) +
              (parentLater - parentCenter.value) := by
          apply Basic.ext <;>
            simp only [Basic.sub_re,
              Basic.sub_im,
              Basic.add_re,
              Basic.add_im] <;> ring1
        rw [identity]
        exact
          (Norm.Bounds.normSq_add_le_two _ _).trans_lt
            (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              (by decide)
              (Fraction.Order.Arithmetic.add_lt_add_direct
                alignedCloseReverse parentTail)) }

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained center value differs from the original base reading by less than the model allowance in squared norm.
-/
theorem CenterState.value_sub_baseReading_lt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    Data.Gaussian.Norm.Basic.normSq
        (center.value - prepared.baseReading) <
      prepared.modelErrorAllowance := by
  let process := (prepared.coefficient 0 prepared.baseInside).name.process
  let ball := process.ball
    (prepared.readingState 0 prepared.baseInside)
  have centerInside : ball.Contains center.value :=
    process.possible_inside center.value_possible_at_readingState
  have baseInside : ball.Contains prepared.baseReading :=
    process.possible_inside
      (prepared.reading_possible 0 prepared.baseInside)
  have centerDifference :
      center.value - prepared.baseReading =
        (center.value - ball.center) +
          (ball.center - prepared.baseReading) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  have centerToBaseCenter :
      Data.Gaussian.Norm.Basic.normSq
          (ball.center - prepared.baseReading) <= ball.radiusSq := by
    have identity : ball.center - prepared.baseReading =
        -(prepared.baseReading - ball.center) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [identity, Norm.Basic.normSq_neg]
    exact baseInside
  have radiusSmall : ball.radiusSq < prepared.readingTarget :=
    prepared.reading_radius_lt 0 prepared.baseInside
  calc
    Data.Gaussian.Norm.Basic.normSq
        (center.value - prepared.baseReading) =
      Data.Gaussian.Norm.Basic.normSq
        ((center.value - ball.center) +
          (ball.center - prepared.baseReading)) := by rw [centerDifference]
    _ <= 2 *
        (Data.Gaussian.Norm.Basic.normSq
            (center.value - ball.center) +
          Data.Gaussian.Norm.Basic.normSq
            (ball.center - prepared.baseReading)) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add centerInside centerToBaseCenter) (by decide)
    _ < 2 * (prepared.readingTarget + prepared.readingTarget) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide)
        (Fraction.Order.Arithmetic.add_lt_add_direct radiusSmall radiusSmall)
    _ = prepared.modelErrorAllowance / 2 :=
      twice_readingTarget_sum_eq_half prepared
    _ < prepared.modelErrorAllowance :=
      Purelib.Data.Rat.Fraction.Order.Field.half_lt_self prepared.modelErrorAllowance_positive

open Purelib.Riemann.Branches in
/-- Every unit-interval point on the retained local segment lies in the original ambient box. -/
theorem point_contains {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    prepared.ambient.Contains (prepared.point fraction) := by
  change prepared.ambient.Contains (prepared.localSegment.pointAt fraction)
  simp only [localSegment, PreparedModels.edge]
  rw [← PreparedSheetContinuation.pointAt_parameterAt
    prepared.segment prepared.within prepared.left prepared.request fraction]
  exact prepared.segment.pointAt_contains prepared.within
    (PreparedSheetContinuation.parameterAt prepared.left
      prepared.request fraction)
    (PreparedSheetContinuation.parameterAt_inside prepared.left
      prepared.request prepared.ordered fraction inside)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The squared endpoint displacement is at most four times the ambient squared-norm bound. -/
theorem pointMovement_le_four_ambient {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.pointMovement <= 4 * prepared.ambient.normSqBound := by
  have first := prepared.ambient.normSq_le_normSqBound
    (prepared.point_contains 1 (by decide))
  have second := prepared.ambient.normSq_le_normSqBound
    (prepared.point_contains 0 prepared.baseInside)
  calc
    prepared.pointMovement <=
        2 * (Data.Gaussian.Norm.Basic.normSq (prepared.point 1) +
          Data.Gaussian.Norm.Basic.normSq (prepared.point 0)) :=
      Norm.Bounds.normSq_sub_le_two _ _
    _ <= 2 * (prepared.ambient.normSqBound +
          prepared.ambient.normSqBound) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add first second) (by decide)
    _ = 4 * prepared.ambient.normSqBound := by ring1

open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
/-- The squared polynomial-value change from the source to any local point is bounded by the retained edge variation. -/
theorem radicandDifference_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Data.Gaussian.Norm.Basic.normSq
        (curve.polynomial.eval (prepared.point 0) -
          curve.polynomial.eval (prepared.point fraction)) <=
      prepared.radicandMovementBound := by
  change Data.Gaussian.Norm.Basic.normSq
      (curve.polynomial.eval (prepared.localSegment.pointAt 0) -
        curve.polynomial.eval (prepared.localSegment.pointAt fraction)) <= _
  simp only [localSegment, PreparedModels.edge]
  rw [← PreparedSheetContinuation.pointAt_parameterAt
      prepared.segment prepared.within prepared.left prepared.request 0,
    ← PreparedSheetContinuation.pointAt_parameterAt
      prepared.segment prepared.within prepared.left prepared.request fraction,
    PreparedSheetContinuation.parameterAt_zero]
  exact
    (ClearSheetContinuation.evaluation_variation_le
      prepared.segment prepared.within prepared.left.parameter
      (PreparedSheetContinuation.parameterAt prepared.left
        prepared.request fraction)
      prepared.left.inside
      (PreparedSheetContinuation.parameterAt_inside prepared.left
        prepared.request prepared.ordered fraction inside)).trans
      (ClearSheetContinuation.variationBound_le_of_between
        prepared.segment
        (PreparedSheetContinuation.parameterAt_between
          prepared.left prepared.request prepared.ordered fraction inside).1
        (PreparedSheetContinuation.parameterAt_between
          prepared.left prepared.request prepared.ordered fraction inside).2)

/-- Every coefficient reading has a possible denominator witness and the exact original point-power quotient
decomposition. -/
theorem reading_components {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    ∃ denominator : Gaussian,
      (prepared.sheetValue fraction inside).value.name.process.Possible
          (prepared.readingState fraction inside).2 denominator ∧
        prepared.reading fraction inside =
          prepared.point fraction ^ differential.exponent / denominator := by
  exact Value.differentialValue_possible_components differential
    (prepared.point fraction) (prepared.sheetValue fraction inside).value
      (prepared.sheetValue fraction inside).apart
      (prepared.readingState fraction inside)
      (prepared.reading_possible fraction inside)

open Purelib.Riemann.Branches in
/-- Every possible query denominator lies in the canonical prepared source box. -/
theorem denominator_candidate_in_source {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (prepared.sheetValue fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (prepared.sheetValue fraction inside).value.name.process.Possible
      state candidate) :
    (PreparedSheetContinuation.prepared prepared.segment
      prepared.left prepared.owner
      prepared.request).track.initial.box.Contains candidate :=
  PreparedModels.sheetValueAtCached_candidate_in_prepared_box
    curve differential prepared.segment prepared.within prepared.left
      prepared.owner prepared.request prepared.cached prepared.ordered
        prepared.small prepared.sheet fraction inside state possible

/-- Every possible query denominator lies in the exact cached prepared source box. -/
theorem denominator_candidate_in_cached_source {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (prepared.sheetValue fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (prepared.sheetValue fraction inside).value.name.process.Possible
      state candidate) :
    prepared.cached.preparedOwner.track.initial.box.Contains candidate := by
  rw [prepared.cached.preparedOwner_eq]
  exact prepared.denominator_candidate_in_source fraction inside state possible

open Purelib.Data.Gaussian in
open Purelib.Riemann.Branches in
/-- Every possible query denominator meets the original segment's squared-norm lower bound. -/
theorem denominator_candidate_lower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (prepared.sheetValue fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (prepared.sheetValue fraction inside).value.name.process.Possible
      state candidate) :
    PreparedModels.segmentDenominatorLower
        prepared.segment <=
      Data.Gaussian.Norm.Basic.normSq candidate := by
  have pointwiseLower :
      PreparedModels.segmentDenominatorLower
          prepared.segment <=
        (prepared.sheetValue fraction inside).apart.certificate.lowerSq := by
    change PreparedModels.segmentDenominatorLower
        prepared.segment <=
      (PreparedModels.sheetValueAtCached curve
        differential
        prepared.segment prepared.within prepared.left prepared.owner
          prepared.request prepared.cached prepared.ordered prepared.small
            prepared.sheet fraction inside).apart.certificate.lowerSq
    rw [PreparedModels.sheetValueAtCached_apart_lowerSq]
    exact
      PreparedModels.segmentDenominatorLower_le_point
        prepared.segment prepared.within
        (PreparedSheetContinuation.parameterAt prepared.left
          prepared.request fraction)
        (PreparedSheetContinuation.parameterAt_inside prepared.left
          prepared.request prepared.ordered fraction inside)
  exact pointwiseLower.trans
    ((prepared.sheetValue fraction inside).apart.certificate.lower state
      ((prepared.sheetValue fraction inside).value.name.process.possible_inside
        possible))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Every possible query denominator meets the strengthened prepared squared-norm lower bound.

Both original denominator floors bound the same retained root candidate.
Their unchanged maximum retains this common lower bound. -/
theorem preparedDenominator_candidate_lower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (prepared.sheetValue fraction inside).value.name.process.State)
    {candidate : Gaussian}
    (possible : (prepared.sheetValue fraction inside).value.name.process.Possible
      state candidate) :
    prepared.preparedDenominatorLower <=
      Data.Gaussian.Norm.Basic.normSq candidate := by
  apply Fraction.Order.Basic.max_le
  · exact prepared.denominator_candidate_lower fraction inside state possible
  · have candidateInside :=
      prepared.denominator_candidate_in_source fraction inside state possible
    rw [prepared.cached.preparedOwner_eq]
    exact boxNormSqLower_le candidateInside

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- The coefficient process's center bound is no greater than the segment's automatic differential bound.

The retained automatic coefficient maximum includes this same process
center bound at the displayed query. -/
theorem coefficient_centerBound_le_automatic {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    (prepared.coefficient fraction inside).name.process.centerBound <=
      PreparedModels.automaticBoundValue differential
        prepared.segment := by
  have pointNormBound :
      Data.Gaussian.Norm.Basic.normSq (prepared.point fraction) <=
        prepared.ambient.normSqBound :=
    prepared.ambient.normSq_le_normSqBound
      (prepared.point_contains fraction inside)
  have numeratorBound :
      Data.Gaussian.Norm.Basic.normSq (prepared.point fraction) ^
          differential.exponent <=
        prepared.ambient.normSqBound ^ differential.exponent :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Norm.Basic.normSq_nonneg _)
      pointNormBound differential.exponent
  have segmentLower :
      PreparedModels.denominatorLower
          prepared.segment <=
        PreparedModels.segmentDenominatorLower
          prepared.segment :=
    (Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _)
  have pointwiseLower :
      PreparedModels.segmentDenominatorLower
          prepared.segment <=
        (prepared.sheetValue fraction inside).apart.certificate.lowerSq := by
    change PreparedModels.segmentDenominatorLower
        prepared.segment <=
      (PreparedModels.sheetValueAtCached curve
        differential prepared.segment prepared.within prepared.left
          prepared.owner prepared.request prepared.cached prepared.ordered
            prepared.small prepared.sheet fraction inside).apart.certificate.lowerSq
    rw [PreparedModels.sheetValueAtCached_apart_lowerSq]
    exact
      PreparedModels.segmentDenominatorLower_le_point
        prepared.segment prepared.within
        (PreparedSheetContinuation.parameterAt prepared.left
          prepared.request fraction)
        (PreparedSheetContinuation.parameterAt_inside prepared.left
          prepared.request prepared.ordered fraction inside)
  have denominatorBound :
      PreparedModels.denominatorLower
          prepared.segment <=
        (prepared.sheetValue fraction inside).apart.certificate.lowerSq :=
    segmentLower.trans pointwiseLower
  have actualPositive :
      0 < (prepared.sheetValue fraction inside).apart.certificate.lowerSq :=
    (PreparedModels.denominatorLower_positive
      prepared.segment).trans_le denominatorBound
  unfold coefficient
    PreparedModels.coefficientAtCached
  rw [Value.differentialValue_centerBound]
  unfold PreparedModels.automaticBoundValue
  calc
    Data.Gaussian.Norm.Basic.normSq (prepared.point fraction) ^
          differential.exponent /
          (prepared.sheetValue fraction inside).apart.certificate.lowerSq <=
        prepared.ambient.normSqBound ^ differential.exponent /
          (prepared.sheetValue fraction inside).apart.certificate.lowerSq := by
      rw [Fraction.Field.div_eq_mul_inv_direct,
        Fraction.Field.div_eq_mul_inv_direct]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        numeratorBound
        (Fraction.Order.Field.inv_pos_direct actualPositive).le
    _ <= prepared.ambient.normSqBound ^ differential.exponent /
          PreparedModels.denominatorLower
            prepared.segment :=
      Fraction.Order.Field.div_le_div_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.pow_nonneg_direct
          prepared.ambient.normSqBound_nonneg differential.exponent)
        (PreparedModels.denominatorLower_positive
          prepared.segment)
        denominatorBound

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Bound a center value by twice the reading-radius allowance plus the segment's automatic coefficient bound. -/
def centerValueNormSqBound {genus : Nat}
    (differential : Basic.Differential genus)
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (errorBound : Coordinate) : Coordinate :=
  2 * (errorBound / 8 +
    PreparedModels.automaticBoundValue differential
      segment)

open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- The center-value squared-norm bound is nonnegative for a nonnegative error allowance. -/
theorem centerValueNormSqBound_nonnegative {genus : Nat}
    (differential : Basic.Differential genus)
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {errorBound : Coordinate} (errorBoundNonnegative : 0 <= errorBound) :
    0 <= centerValueNormSqBound differential segment errorBound := by
  unfold centerValueNormSqBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (Fraction.Order.Field.div_nonneg_direct errorBoundNonnegative
        (by decide))
      (PreparedModels.automaticBoundValue_nonnegative
        differential segment))

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Bound coefficient magnitude using the ambient numerator power and the segment's residual denominator floor. -/
def residualAutomaticBoundValue {genus : Nat}
    (differential : Basic.Differential genus)
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) : Coordinate :=
  ambient.normSqBound ^ differential.exponent /
    PreparedModels.residualDenominatorLower segment

section
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- The original cleared segment's residual denominator floor is strictly positive. -/
private theorem residualDenominatorLower_positive
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 < PreparedModels.residualDenominatorLower
      segment := by
  unfold PreparedModels.residualDenominatorLower
  exact Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Basic.lt_min (by decide)
      (Fraction.Order.Field.div_pos_direct
        segment.clearanceBound_positive (by decide)))
    (by decide)

/-- The residual-only coefficient bound dominates the strengthened automatic bound.

The retained maximum includes the original residual-based bound.
Its same cached automatic value therefore bounds that term. -/
theorem automaticBoundValue_le_residual {genus : Nat}
    (differential : Basic.Differential genus)
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    PreparedModels.automaticBoundValue differential
        segment <=
      residualAutomaticBoundValue differential segment := by
  unfold PreparedModels.automaticBoundValue
    residualAutomaticBoundValue
  apply Fraction.Order.Field.div_le_div_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_nonneg_direct
      ambient.normSqBound_nonneg differential.exponent)
    (residualDenominatorLower_positive segment)
  unfold PreparedModels.denominatorLower
  exact Fraction.Order.Basic.le_max_left _ _

/-- The residual-only automatic coefficient bound is nonnegative. -/
theorem residualAutomaticBoundValue_nonnegative {genus : Nat}
    (differential : Basic.Differential genus)
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) :
    0 <= residualAutomaticBoundValue differential segment :=
  Fraction.Order.Field.div_nonneg_direct
    (Fraction.Order.Arithmetic.pow_nonneg_direct
      ambient.normSqBound_nonneg differential.exponent)
    (residualDenominatorLower_positive segment).le

end

open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
/-- Bound a center value using its reading-radius allowance and the residual-only automatic coefficient estimate. -/
def centerValueNormSqResidualBound {genus : Nat}
    (differential : Basic.Differential genus)
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (errorBound : Coordinate) : Coordinate :=
  2 * (errorBound / 8 + residualAutomaticBoundValue differential segment)

section
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
/-- The residual-only center estimate dominates the original automatic center estimate. -/
theorem centerValueNormSqBound_le_residual {genus : Nat}
    (differential : Basic.Differential genus)
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    (errorBound : Coordinate) :
    centerValueNormSqBound differential segment errorBound <=
      centerValueNormSqResidualBound differential segment errorBound := by
  unfold centerValueNormSqBound centerValueNormSqResidualBound
  have sumOrder :
      errorBound / 8 +
          PreparedModels.automaticBoundValue
            differential segment <=
        errorBound / 8 + residualAutomaticBoundValue differential segment :=
    Fraction.Order.Arithmetic.add_le_add_direct (le_refl _)
      (automaticBoundValue_le_residual differential segment)
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    sumOrder (by decide)

/-- The residual-only center estimate is nonnegative for a nonnegative error allowance. -/
theorem centerValueNormSqResidualBound_nonnegative {genus : Nat}
    (differential : Basic.Differential genus)
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {ambient : Box} {start finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
    {errorBound : Coordinate} (errorBoundNonnegative : 0 <= errorBound) :
    0 <= centerValueNormSqResidualBound differential segment errorBound := by
  unfold centerValueNormSqResidualBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (Fraction.Order.Field.div_nonneg_direct errorBoundNonnegative
        (by decide))
      (residualAutomaticBoundValue_nonnegative differential segment))

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained center value meets the automatic squared-norm bound whenever the supplied error budget covers the model
allowance. -/
theorem CenterState.value_normSq_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (errorBound : Coordinate)
    (errorLe : prepared.modelErrorAllowance <= errorBound) :
    Data.Gaussian.Norm.Basic.normSq center.value <=
      centerValueNormSqBound differential prepared.segment errorBound := by
  let process := (prepared.coefficient 0 prepared.baseInside).name.process
  let ball := process.ball center.state
  have centerInside :
      Data.Gaussian.Norm.Basic.normSq
          (center.value - ball.center) <= ball.radiusSq :=
    process.possible_inside center.value_possible
  have ballCenterBound :
      Data.Gaussian.Norm.Basic.normSq ball.center <=
        process.centerBound :=
    process.center_bounded center.state
  have processBound : process.centerBound <=
      PreparedModels.automaticBoundValue differential
        prepared.segment :=
    prepared.coefficient_centerBound_le_automatic 0 prepared.baseInside
  have radiusBound : ball.radiusSq <= errorBound / 8 :=
    center.radius_lt.le.trans (by
      unfold readingTarget
      rw [Fraction.Field.div_eq_mul_inv_direct]
      exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        errorLe
        (Fraction.Order.Field.inv_pos_direct
          (show (0 : Coordinate) < 8 by decide)).le)
  have identity : center.value =
      (center.value - ball.center) + ball.center := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  rw [identity]
  exact
    (Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (centerInside.trans radiusBound)
          (ballCenterBound.trans processBound)) (by decide))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
open Purelib.Riemann.RootContinuation in
/-- Every coefficient reading on the retained edge differs from its base reading by at most the model allowance in
squared norm.

The quotient estimate uses the exact denominator witnesses in the common prepared box and the original point and
root-movement bounds. -/
theorem reading_difference_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Data.Gaussian.Norm.Basic.normSq
        (prepared.reading fraction inside - prepared.baseReading) <=
      prepared.modelErrorAllowance := by
  rcases prepared.reading_components fraction inside with
    ⟨queryRoot, queryRootPossible, queryReadingEqual⟩
  rcases prepared.reading_components 0 prepared.baseInside with
    ⟨baseRoot, baseRootPossible, baseReadingEqual⟩
  have queryRootInside := prepared.denominator_candidate_in_source fraction
    inside (prepared.readingState fraction inside).2 queryRootPossible
  have baseRootInside := prepared.denominator_candidate_in_source 0
    prepared.baseInside (prepared.readingState 0 prepared.baseInside).2
      baseRootPossible
  have queryRootLower := prepared.preparedDenominator_candidate_lower
    fraction inside (prepared.readingState fraction inside).2 queryRootPossible
  have baseRootLower := prepared.preparedDenominator_candidate_lower 0
    prepared.baseInside (prepared.readingState 0 prepared.baseInside).2
      baseRootPossible
  have queryPointBound := prepared.ambient.normSq_le_normSqBound
    (prepared.point_contains fraction inside)
  have basePointBound := prepared.ambient.normSq_le_normSqBound
    (prepared.point_contains 0 prepared.baseInside)
  have pointDifference :
      Data.Gaussian.Norm.Basic.normSq
          (prepared.point fraction - prepared.point 0) <=
        prepared.pointMovement := by
    change Data.Gaussian.Norm.Basic.normSq
        (prepared.localSegment.pointAt fraction -
          prepared.localSegment.pointAt 0) <= _
    unfold pointMovement
    change _ <= Data.Gaussian.Norm.Basic.normSq
      (prepared.localSegment.pointAt 1 - prepared.localSegment.pointAt 0)
    exact prepared.localSegment.normSq_pointAt_sub_zero_le_full fraction inside
  have numeratorDifference :
      Data.Gaussian.Norm.Basic.normSq
          (prepared.point fraction ^ differential.exponent -
            prepared.point 0 ^ differential.exponent) <=
        Power.Bounds.IntegrationQuotientVariation.powerSlope
            prepared.ambient.normSqBound differential.exponent *
          prepared.pointMovement :=
    (Power.Bounds.IntegrationQuotientVariation.normSq_pow_sub_pow_le
      prepared.ambient.normSqBound_nonneg differential.exponent
      queryPointBound basePointBound).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          pointDifference
          (Power.Bounds.IntegrationQuotientVariation.powerSlope_nonnegative
            prepared.ambient.normSqBound_nonneg differential.exponent))
  have baseNumeratorBound :
      Data.Gaussian.Norm.Basic.normSq
          (prepared.point 0 ^ differential.exponent) <=
        prepared.ambient.normSqBound ^ differential.exponent := by
    rw [Power.normSq_pow]
    exact Fraction.Order.Arithmetic.pow_le_pow_direct
      (Norm.Basic.normSq_nonneg (prepared.point 0))
      basePointBound differential.exponent
  have baseRootBound :
      Data.Gaussian.Norm.Basic.normSq baseRoot <=
        (UniformSquareRootPreparation.rootAmbient
          prepared.segment).normSqBound := by
    apply (UniformSquareRootPreparation.rootAmbient
      prepared.segment).normSq_le_normSqBound
    have refines :
        (PreparedSheetContinuation.prepared prepared.segment
          prepared.left prepared.owner
          prepared.request).track.initial.box.Refines
            (UniformSquareRootPreparation.rootAmbient
              prepared.segment) := by
      exact
        PreparedSheetContinuation.prepared_initial_box_refines_rootAmbient
          prepared.segment prepared.left prepared.owner prepared.request
    exact refines.contains baseRootInside
  have rootDifference :
      Data.Gaussian.Norm.Basic.normSq
          (baseRoot - queryRoot) <= prepared.preparedRootDiameter := by
    rw [prepared.preparedRootDiameter_eq_canonical]
    exact (PreparedSheetContinuation.prepared prepared.segment
      prepared.left prepared.owner
      prepared.request).track.initial.box.normSq_sub_le_diagonalSq
        baseRootInside queryRootInside
  have quotientDifference :=
    Norm.Quotient.IntegrationQuotientVariation.normSq_div_sub_div_le
      prepared.preparedDenominatorLower_positive
      numeratorDifference baseNumeratorBound baseRootBound rootDifference
        queryRootLower baseRootLower
  have rawBound :
      Data.Gaussian.Norm.Basic.normSq
          (prepared.reading fraction inside - prepared.baseReading) <=
        prepared.rawVariation := by
    rw [queryReadingEqual]
    unfold baseReading
    rw [baseReadingEqual]
    exact quotientDifference
  exact rawBound.trans
    (le_add_of_nonneg_right prepared.preparedRootDiameter_positive.le)

/-- Read the canonical center state's retained denominator witness. -/
def residualRootCenter {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Gaussian :=
  (CenterState.canonical prepared).denominator

open Purelib.Approximation.Gaussian in
/-- The retained canonical denominator is possible at the original residual-certified root state. -/
theorem residualRootCenter_possible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
      (prepared.residualRootState 0 prepared.baseInside) prepared.residualRootCenter := by
  exact (prepared.sheetValue 0 prepared.baseInside).value.name.process.refine_persists
    _ _ (Request.Basic.Name.divisionInputTarget_pos _ _ _
      (prepared.sheetValue 0 prepared.baseInside).apart.certificate.positive
      prepared.readingTarget_positive)
    (CenterState.canonical prepared).denominator_possible

/-- The residual root center lies in the exact cached root box. -/
theorem residualRootCenter_in_cachedBox {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.cached.preparedOwner.track.initial.box.Contains
      prepared.residualRootCenter := by
  have inside := prepared.denominator_candidate_in_source 0
    prepared.baseInside (prepared.residualRootState 0 prepared.baseInside)
      prepared.residualRootCenter_possible
  rw [prepared.cached.preparedOwner_eq]
  exact inside

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained residual root center meets the combined cached denominator lower bound.

The retained root-center norm floor includes the original residual
component in its unchanged maximum. -/
theorem residualRootCenter_normSq_lower {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    prepared.cachedDenominatorLower ≤ Data.Gaussian.Norm.Basic.normSq prepared.residualRootCenter := by
  apply prepared.cachedDenominatorLower_le_of_contains prepared.residualRootCenter_in_cachedBox
  exact ((Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _)).trans
    (prepared.denominator_candidate_lower 0 prepared.baseInside
      (prepared.residualRootState 0 prepared.baseInside) prepared.residualRootCenter_possible)

section
open Purelib.Data.Gaussian
/-- A positive lower bound for the sum norm turns a candidate residual into a squared-distance bound from the retained
root center. -/
theorem residualRootCenter_sub_candidate_le_of_sumBound {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) {candidate : Gaussian}
    {sumLower : Coordinate} (sumPositive : 0 < sumLower)
    (sumBound : sumLower <=
      Data.Gaussian.Norm.Basic.normSq
        (prepared.residualRootCenter + candidate)) :
    Data.Gaussian.Norm.Basic.normSq
        (prepared.residualRootCenter - candidate) <=
      4 *
          (prepared.rootResidualTarget +
              Data.Gaussian.Norm.Basic.normSq
                (candidate * candidate -
                  curve.polynomial.eval (prepared.point 0))) /
        sumLower := by
  have centerResidual :=
    (prepared.residualRootState_candidate_residual_lt 0
      prepared.baseInside prepared.residualRootCenter_possible).le
  have zeroMovement :
      Data.Gaussian.Norm.Basic.normSq
          (curve.polynomial.eval (prepared.point 0) -
            curve.polynomial.eval (prepared.point 0)) <= 0 := by
    rw [Basic.sub_self,
      Norm.Basic.normSq_zero]
  have difference := normSq_root_sub_le_of_residuals sumPositive sumBound
    centerResidual zeroMovement (le_refl _)
  simpa only [_root_.add_zero] using difference

/-- A candidate in the cached box satisfies the residual distance estimate when the cached root-sum lower bound is
positive. -/
theorem residualRootCenter_sub_candidate_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) {candidate : Gaussian}
    (candidateInside :
      prepared.cached.preparedOwner.track.initial.box.Contains candidate)
    (sumPositive : 0 < prepared.cachedRootSumLower) :
    Data.Gaussian.Norm.Basic.normSq
        (prepared.residualRootCenter - candidate) <=
      4 *
          (prepared.rootResidualTarget +
              Data.Gaussian.Norm.Basic.normSq
                (candidate * candidate -
                  curve.polynomial.eval (prepared.point 0))) /
        prepared.cachedRootSumLower := by
  exact prepared.residualRootCenter_sub_candidate_le_of_sumBound sumPositive
    (prepared.cachedRootSumLower_le_of_contains
      prepared.residualRootCenter_in_cachedBox candidateInside)

end

/-- Divide the original base-point power by the retained residual root center. -/
def residualCoefficientCenter {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Gaussian :=
  prepared.point 0 ^ differential.exponent / prepared.residualRootCenter

/-- The canonical cached coefficient is exactly the residual coefficient center. -/
theorem canonical_value_eq_residualCoefficientCenter {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    (CenterState.canonical prepared).value = prepared.residualCoefficientCenter :=
  (CenterState.canonical prepared).value_eq_power_div_denominator

open Purelib.Data.Gaussian in
/-- The residual coefficient center differs from the canonical base reading by at most the raw variation allowance. -/
theorem residualCoefficientCenter_sub_baseReading_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) :
    Data.Gaussian.Norm.Basic.normSq
      (prepared.residualCoefficientCenter - prepared.baseReading) ≤ prepared.rawVariation := by
  rw [← prepared.canonical_value_eq_residualCoefficientCenter]
  change Data.Gaussian.Norm.Basic.normSq (prepared.baseReading - prepared.baseReading) ≤ _
  rw [Basic.sub_self, Norm.Basic.normSq_zero]
  exact prepared.rawVariation_nonnegative

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
/-- At exponent zero, a common positive squared-norm floor bounds the inverse-coefficient error by twice the root error
over its square. -/
theorem residualCoefficientCenter_sub_candidateInverse_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (exponentZero : differential.exponent = 0)
    {candidate : Gaussian} {lowerSq rootMovement : Coordinate}
    (lowerPositive : 0 < lowerSq)
    (centerLower : lowerSq <= prepared.cachedDenominatorLower)
    (candidateLower : lowerSq <=
      Data.Gaussian.Norm.Basic.normSq candidate)
    (rootClose :
      Data.Gaussian.Norm.Basic.normSq
        (prepared.residualRootCenter - candidate) <= rootMovement) :
    Data.Gaussian.Norm.Basic.normSq
        (prepared.residualCoefficientCenter - 1 / candidate) <=
      (2 * rootMovement) / (lowerSq * lowerSq) := by
  have residualRootLower : lowerSq <=
      Data.Gaussian.Norm.Basic.normSq
        prepared.residualRootCenter := by
    exact centerLower.trans prepared.residualRootCenter_normSq_lower
  have reversedRootClose :
      Data.Gaussian.Norm.Basic.normSq
          (candidate - prepared.residualRootCenter) <= rootMovement := by
    have reverse : candidate - prepared.residualRootCenter =
        -(prepared.residualRootCenter - candidate) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [reverse, Norm.Basic.normSq_neg]
    exact rootClose
  have comparison :=
    Norm.Quotient.IntegrationQuotientVariation.normSq_div_sub_div_le
      (leftNumerator := (1 : Gaussian))
      (rightNumerator := (1 : Gaussian))
      (leftDenominator := prepared.residualRootCenter)
      (rightDenominator := candidate)
      (numeratorSlope := (0 : Coordinate))
      (numeratorBound := (1 : Coordinate))
      (denominatorBound :=
        Data.Gaussian.Norm.Basic.normSq candidate)
      (lowerSq := lowerSq) (pointMovement := (0 : Coordinate))
      (rootMovement := rootMovement) lowerPositive
      (by
        rw [Basic.sub_self,
          Norm.Basic.normSq_zero]
        change (0 : Coordinate) <= 0
        exact le_rfl)
      (by rw [Norm.Basic.normSq_one])
      (le_refl _)
      reversedRootClose residualRootLower candidateLower
  unfold residualCoefficientCenter
  rw [exponentZero, pow_zero]
  simpa only [Budget.Quotient.quotientBound,
    zero_mul, zero_add, one_mul] using comparison

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- At exponent zero, separate positive center and candidate squared-norm floors bound inverse error by root error over
their product. -/
theorem residualCoefficientCenter_sub_candidateInverse_le_separate
    {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (exponentZero : differential.exponent = 0)
    {candidate : Gaussian}
    {centerLowerSq candidateLowerSq rootMovement : Coordinate}
    (centerLowerPositive : 0 < centerLowerSq)
    (candidateLowerPositive : 0 < candidateLowerSq)
    (centerLower : centerLowerSq <= prepared.cachedDenominatorLower)
    (candidateLower : candidateLowerSq <=
      Data.Gaussian.Norm.Basic.normSq candidate)
    (rootClose :
      Data.Gaussian.Norm.Basic.normSq
        (prepared.residualRootCenter - candidate) <= rootMovement) :
    Data.Gaussian.Norm.Basic.normSq
        (prepared.residualCoefficientCenter - 1 / candidate) <=
      rootMovement / (centerLowerSq * candidateLowerSq) := by
  have residualRootLower : centerLowerSq <=
      Data.Gaussian.Norm.Basic.normSq
        prepared.residualRootCenter := by
    exact centerLower.trans prepared.residualRootCenter_normSq_lower
  have centerNormPositive : 0 <
      Data.Gaussian.Norm.Basic.normSq
        prepared.residualRootCenter :=
    centerLowerPositive.trans_le residualRootLower
  have candidateNormPositive : 0 <
      Data.Gaussian.Norm.Basic.normSq candidate :=
    candidateLowerPositive.trans_le candidateLower
  have centerNonzero : prepared.residualRootCenter ≠ 0 := by
    intro equal
    have zeroNorm :=
      Norm.Basic.normSq_eq_zero.mpr equal
    rw [zeroNorm] at centerNormPositive
    exact (lt_irrefl _ centerNormPositive)
  have candidateNonzero : candidate ≠ 0 := by
    intro equal
    have zeroNorm :=
      Norm.Basic.normSq_eq_zero.mpr equal
    rw [zeroNorm] at candidateNormPositive
    exact (lt_irrefl _ candidateNormPositive)
  have productNonzero :
      prepared.residualRootCenter * candidate ≠ 0 :=
    Field.mul_ne_zero_direct centerNonzero
      candidateNonzero
  have reversedRootClose :
      Data.Gaussian.Norm.Basic.normSq
          (candidate - prepared.residualRootCenter) <= rootMovement := by
    have reverse : candidate - prepared.residualRootCenter =
        -(prepared.residualRootCenter - candidate) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [reverse, Norm.Basic.normSq_neg]
    exact rootClose
  have quotientIdentity :
      prepared.residualCoefficientCenter - 1 / candidate =
        (candidate - prepared.residualRootCenter) /
          (prepared.residualRootCenter * candidate) := by
    unfold residualCoefficientCenter
    rw [exponentZero, pow_zero]
    simpa only [Basic.one_mul] using
      Purelib.Data.Gaussian.Field.div_sub_div 1 1
        prepared.residualRootCenter candidate centerNonzero candidateNonzero
  have actualProductPositive : 0 <
      Data.Gaussian.Norm.Basic.normSq
          prepared.residualRootCenter *
        Data.Gaussian.Norm.Basic.normSq candidate :=
    Fraction.Order.Arithmetic.mul_pos_direct centerNormPositive
      candidateNormPositive
  have lowerProductPositive : 0 < centerLowerSq * candidateLowerSq :=
    Fraction.Order.Arithmetic.mul_pos_direct centerLowerPositive
      candidateLowerPositive
  have productLower : centerLowerSq * candidateLowerSq <=
      Data.Gaussian.Norm.Basic.normSq
          prepared.residualRootCenter *
        Data.Gaussian.Norm.Basic.normSq candidate :=
    Fraction.Order.Arithmetic.mul_le_mul_direct residualRootLower candidateLower
      candidateLowerPositive.le centerNormPositive.le
  have rootMovementNonnegative : 0 <= rootMovement :=
    (Norm.Basic.normSq_nonneg
      (prepared.residualRootCenter - candidate)).trans rootClose
  rw [quotientIdentity,
    Field.normSq_div _ _ productNonzero,
    Norm.Basic.normSq_mul,
    ← Fraction.Field.div_eq_mul_inv_direct]
  apply (Fraction.Order.Field.div_le_iff_pos actualProductPositive).2
  calc
    Data.Gaussian.Norm.Basic.normSq
        (candidate - prepared.residualRootCenter) <= rootMovement :=
      reversedRootClose
    _ = (rootMovement / (centerLowerSq * candidateLowerSq)) *
        (centerLowerSq * candidateLowerSq) :=
      (Fraction.Field.div_mul_cancel_of_ne _ _
        lowerProductPositive.ne').symm
    _ <= (rootMovement / (centerLowerSq * candidateLowerSq)) *
        (Data.Gaussian.Norm.Basic.normSq
            prepared.residualRootCenter *
          Data.Gaussian.Norm.Basic.normSq candidate) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct productLower
        (Fraction.Order.Field.div_nonneg_direct rootMovementNonnegative
          lowerProductPositive.le)

/-- Every query reading differs from the retained center value by at most four model allowances in squared norm. -/
theorem CenterState.reading_sub_value_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Data.Gaussian.Norm.Basic.normSq
        (prepared.reading fraction inside - center.value) <=
      4 * prepared.modelErrorAllowance := by
  have identity :
      prepared.reading fraction inside - center.value =
        (prepared.reading fraction inside - prepared.baseReading) +
          (prepared.baseReading - center.value) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  have reversedCenter :
      Data.Gaussian.Norm.Basic.normSq
          (prepared.baseReading - center.value) <=
        prepared.modelErrorAllowance := by
    have reversed : prepared.baseReading - center.value =
        -(center.value - prepared.baseReading) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [reversed, Norm.Basic.normSq_neg]
    exact center.value_sub_baseReading_lt.le
  rw [identity]
  calc
    Data.Gaussian.Norm.Basic.normSq
        ((prepared.reading fraction inside - prepared.baseReading) +
          (prepared.baseReading - center.value)) <=
      2 *
        (Data.Gaussian.Norm.Basic.normSq
            (prepared.reading fraction inside - prepared.baseReading) +
          Data.Gaussian.Norm.Basic.normSq
            (prepared.baseReading - center.value)) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ <= 2 * (prepared.modelErrorAllowance +
        prepared.modelErrorAllowance) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add (prepared.reading_difference_le fraction inside)
          reversedCenter) (by decide)
    _ = 4 * prepared.modelErrorAllowance := by ring1

end

set_option genInjectivity false in
/-- A retained coefficient state at an exact local fraction, with reading-state persistence and squared-radius accuracy.

The original prepared edge and interval witness remain indices; every possible value is certified against the same
original reading state. -/
structure QueryState {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) where
  /-- The exact retained coefficient process state. -/ state : (prepared.coefficient fraction inside).name.process.State
  /-- Every possible retained-state value remains possible at the original reading state. -/ persists : forall {value :
    Gaussian},
    (prepared.coefficient fraction inside).name.process.Possible state value ->
      (prepared.coefficient fraction inside).name.process.Possible
        (prepared.readingState fraction inside) value
  /-- The retained state's squared ball radius is below the original reading target. -/ radius_lt :
    ((prepared.coefficient fraction inside).name.process.ball state).radiusSq <
      prepared.readingTarget

constructive_injectivity QueryState

namespace QueryState

/-- Retain the exact canonical reading state at the indexed fraction and its persistence and accuracy proofs. -/
def canonical {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    QueryState prepared fraction inside where
  state := prepared.readingState fraction inside
  persists := by
    intro value possible
    exact possible
  radius_lt := prepared.reading_radius_lt fraction inside

/-- Read the exact witness of the retained query state. -/
def value {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) : Gaussian :=
  ((prepared.coefficient fraction inside).name.process.witness query.state).val

/-- The query witness is possible at the exact retained query state. -/
theorem value_possible {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) :
    (prepared.coefficient fraction inside).name.process.Possible
      query.state query.value :=
  ((prepared.coefficient fraction inside).name.process.witness
    query.state).property

/-- The query witness remains possible at the original reading state for that fraction. -/
theorem value_possible_at_readingState {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) :
    (prepared.coefficient fraction inside).name.process.Possible
      (prepared.readingState fraction inside) query.value :=
  query.persists query.value_possible

open Purelib.Approximation.Gaussian
/-- Rebase the original coefficient process at the retained state. -/
def named {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) :
    Name.Basic.Named :=
  { process := (prepared.coefficient fraction inside).name.process
    state := query.state }

/-- The original coefficient name is operationally equivalent to its rebasing at the retained state. -/
def equivalent {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) :
    Equivalence.NamedEquivalent
      (prepared.coefficient fraction inside).name query.named :=
  Name.Coherent.CoherentNamed.rebaseEquivalent
    (prepared.coefficient fraction inside) query.state

/-- Read a later sampling witness from the exact retained coefficient state. -/
def laterValue {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) (index : Nat) : Gaussian :=
  Process.Sampling.witnessAt
    (prepared.coefficient fraction inside).name.process query.state index

/-- A later sampling witness remains possible at the retained starting state. -/
theorem laterValue_possible_at_state {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) (index : Nat) :
    (prepared.coefficient fraction inside).name.process.Possible
      query.state (query.laterValue index) :=
  Process.Sampling.witnessAt_possible_start
    (prepared.coefficient fraction inside).name.process query.state index

end QueryState

set_option genInjectivity false in
/-- A retained query state whose squared ball radius also meets a separately requested target.

The exact original parent and displayed indices identify every retained
field and certificate. The record preserves their original cache and witness ownership. -/
structure TargetedQueryState {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (target : Coordinate) where
  /-- The original query state retained with its persistence and reading-accuracy certificates. -/ query : QueryState
    prepared fraction inside
  /-- The retained query state's squared radius is strictly below the separate target. -/ radius_lt_target :
    ((prepared.coefficient fraction inside).name.process.ball
      query.state).radiusSq < target

constructive_injectivity TargetedQueryState

namespace TargetedQueryState

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Refine the exact query to the smaller of a positive supplied target and the original reading target.

A geometric index search supplies the retained state; both accuracy requirements and persistence to the original reading
state are preserved. -/
def atTarget {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (target : Coordinate) (targetPositive : 0 < target) :
    TargetedQueryState prepared fraction inside target := by
  let accuracy := min target prepared.readingTarget
  have accuracyPositive : 0 < accuracy :=
    Fraction.Order.Basic.lt_min targetPositive prepared.readingTarget_positive
  let index := Geometric.Search.firstQuarterBelow 1 0 accuracy
  let state := Process.Sampling.stateAt
    (prepared.coefficient fraction inside).name.process
      (prepared.readingState fraction inside) index
  have stateAccurate :
      ((prepared.coefficient fraction inside).name.process.ball state).radiusSq <
        accuracy :=
    (Process.Sampling.stateAt_accurate
      (prepared.coefficient fraction inside).name.process
        (prepared.readingState fraction inside) index).trans
      (Geometric.Search.firstQuarterBelow_accurate
        1 (by decide) 0 accuracy accuracyPositive)
  exact
    { query :=
        { state := state
          persists := by
            intro value possible
            exact Process.Sampling.stateAt_possible_at_start
              (prepared.coefficient fraction inside).name.process
                (prepared.readingState fraction inside) index possible
          radius_lt := stateAccurate.trans_le (Fraction.Order.Basic.min_le_right _ _) }
      radius_lt_target := stateAccurate.trans_le (Fraction.Order.Basic.min_le_left _ _) }

end TargetedQueryState

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Every later query witness is within four retained ball squared radii of the current query witness. -/
theorem QueryState.laterValue_sub_value_le_radius {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (query.laterValue index - query.value) <=
      4 * ((prepared.coefficient fraction inside).name.process.ball
        query.state).radiusSq := by
  let process := (prepared.coefficient fraction inside).name.process
  let ball := process.ball query.state
  have laterInside : ball.Contains (query.laterValue index) :=
    process.possible_inside (query.laterValue_possible_at_state index)
  have queryInside : ball.Contains query.value :=
    process.possible_inside query.value_possible
  have identity : query.laterValue index - query.value =
      (query.laterValue index - ball.center) +
        (ball.center - query.value) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  have queryReverse :
      Data.Gaussian.Norm.Basic.normSq
          (ball.center - query.value) <= ball.radiusSq := by
    have reverse : ball.center - query.value =
        -(query.value - ball.center) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [reverse, Norm.Basic.normSq_neg]
    exact queryInside
  rw [identity]
  calc
    Data.Gaussian.Norm.Basic.normSq
        ((query.laterValue index - ball.center) +
          (ball.center - query.value)) <=
      2 * (Data.Gaussian.Norm.Basic.normSq
          (query.laterValue index - ball.center) +
        Data.Gaussian.Norm.Basic.normSq
          (ball.center - query.value)) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ <= 2 * (ball.radiusSq + ball.radiusSq) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add laterInside queryReverse) (by decide)
    _ = 4 * ball.radiusSq := by ring1

/-- Two values possible at a sufficiently accurate coefficient state differ by less than the model allowance in squared
norm. -/
private theorem coefficientCandidates_sub_lt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (state : (prepared.coefficient fraction inside).name.process.State)
    (radiusSmall :
      ((prepared.coefficient fraction inside).name.process.ball state).radiusSq <
        prepared.readingTarget)
    {left right : Gaussian}
    (leftPossible :
      (prepared.coefficient fraction inside).name.process.Possible state left)
    (rightPossible :
      (prepared.coefficient fraction inside).name.process.Possible state right) :
    Data.Gaussian.Norm.Basic.normSq (left - right) <
      prepared.modelErrorAllowance := by
  let process := (prepared.coefficient fraction inside).name.process
  let ball := process.ball state
  have leftInside : ball.Contains left :=
    process.possible_inside leftPossible
  have rightInside : ball.Contains right :=
    process.possible_inside rightPossible
  have identity : left - right =
      (left - ball.center) + (ball.center - right) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  have rightReverse :
      Data.Gaussian.Norm.Basic.normSq
          (ball.center - right) <= ball.radiusSq := by
    have reverse : ball.center - right = -(right - ball.center) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [reverse, Norm.Basic.normSq_neg]
    exact rightInside
  rw [identity]
  calc
    Data.Gaussian.Norm.Basic.normSq
        ((left - ball.center) + (ball.center - right)) <=
      2 * (ball.radiusSq + ball.radiusSq) :=
      (Norm.Bounds.normSq_add_le_two _ _).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftInside rightReverse) (by decide))
    _ < 2 * (prepared.readingTarget + prepared.readingTarget) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide)
        (Fraction.Order.Arithmetic.add_lt_add_direct radiusSmall radiusSmall)
    _ = prepared.modelErrorAllowance / 2 :=
      twice_readingTarget_sum_eq_half prepared
    _ < prepared.modelErrorAllowance :=
      Purelib.Data.Rat.Fraction.Order.Field.half_lt_self prepared.modelErrorAllowance_positive

end

section
open Purelib.Data.Gaussian
/-- A later witness differs from the retained value by less than the model-error allowance in squared norm. -/
theorem QueryState.laterValue_sub_value_lt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        (query.laterValue index - query.value) <
      prepared.modelErrorAllowance :=
  coefficientCandidates_sub_lt prepared fraction inside query.state
    query.radius_lt (query.laterValue_possible_at_state index)
      query.value_possible

/-- The retained query value differs from its original canonical reading by less than the model allowance in squared
norm. -/
theorem QueryState.value_sub_reading_lt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside) :
    Data.Gaussian.Norm.Basic.normSq
        (query.value - prepared.reading fraction inside) <
      prepared.modelErrorAllowance :=
  coefficientCandidates_sub_lt prepared fraction inside
    (prepared.readingState fraction inside)
    (prepared.reading_radius_lt fraction inside)
      query.value_possible_at_readingState
      (prepared.reading_possible fraction inside)

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The retained query value differs from the retained base center by less than ten model allowances in squared norm. -/
theorem QueryState.value_sub_center_lt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential} {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState prepared fraction inside)
    (center : CenterState prepared) :
    Data.Gaussian.Norm.Basic.normSq
        (query.value - center.value) <
      10 * prepared.modelErrorAllowance := by
  have identity : query.value - center.value =
      (query.value - prepared.reading fraction inside) +
        (prepared.reading fraction inside - center.value) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  rw [identity]
  calc
    Data.Gaussian.Norm.Basic.normSq
        ((query.value - prepared.reading fraction inside) +
          (prepared.reading fraction inside - center.value)) <=
      2 *
        (Data.Gaussian.Norm.Basic.normSq
            (query.value - prepared.reading fraction inside) +
          Data.Gaussian.Norm.Basic.normSq
            (prepared.reading fraction inside - center.value)) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ < 2 * (prepared.modelErrorAllowance +
        4 * prepared.modelErrorAllowance) :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        (by decide)
        ((Fraction.Order.Arithmetic.add_lt_add_right_direct
            query.value_sub_reading_lt
            (Data.Gaussian.Norm.Basic.normSq
              (prepared.reading fraction inside - center.value))).trans_le
          (Fraction.Order.Arithmetic.add_le_add_direct le_rfl
            (center.reading_sub_value_le fraction inside)))
    _ = 10 * prepared.modelErrorAllowance := by ring1

open Purelib.Data.Gaussian in
set_option genInjectivity false in
/-- A child center aligned to an exact parent query, with separate radius-based and model-allowance distance bounds.

Both certificates concern the same retained child center and original query value. -/
structure QueryCenterAlignment {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState parent fraction inside) (target : Coordinate) where
  /-- The exact selected center state of the original child edge. -/ childCenter : CenterState child
  /-- The actual child-to-query difference is below twice the sum of the target and four times the retained query
    squared radius. -/ close_radius :
    Data.Gaussian.Norm.Basic.normSq
        (childCenter.value - query.value) <
      2 * (target +
        4 * ((parent.coefficient fraction inside).name.process.ball
          query.state).radiusSq)
  /-- The actual child-to-parent value difference is bounded in squared norm by twice the sum of the comparison target
    and the parent model allowance. -/ close :
    Data.Gaussian.Norm.Basic.normSq
        (childCenter.value - query.value) <
      2 * (target + parent.modelErrorAllowance)

constructive_injectivity QueryCenterAlignment

open Purelib.Approximation.Gaussian in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- Align an equivalent child base coefficient with the original retained parent query at a positive comparison
tolerance.

The actual comparison indices determine the retained child state; both its distance bounds preserve the parent query's
exact radius and model allowance. -/
def alignQueryRight {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState parent fraction inside)
    (coefficientEquivalent :
      Equivalence.NamedEquivalent
        (parent.coefficient fraction inside).name
        (child.coefficient 0 child.baseInside).name)
    (target : Coordinate) (positive : 0 < target) :
    QueryCenterAlignment parent child query target := by
  let alignedEquivalent : Equivalence.NamedEquivalent
      query.named (CenterState.baseNamed child) :=
    Equivalence.NamedEquivalent.trans query.equivalent.symm
      (Equivalence.NamedEquivalent.trans coefficientEquivalent
        (CenterState.baseEquivalent child))
  let childStart := CenterState.canonicalIndex child
  let comparison := alignedEquivalent.compare 0 childStart target positive
  let childState := Process.Sampling.stateAt
    (child.coefficient 0 child.baseInside).name.process
      (child.readingState 0 child.baseInside) comparison.rightIndex
  let childCenter : CenterState child :=
    CenterState.ofState child childState
      (by
        intro value possible
        exact Process.Sampling.stateAt_possible_at_start
          (child.coefficient 0 child.baseInside).name.process
            (child.readingState 0 child.baseInside)
              comparison.rightIndex possible)
      (by
        have indexOrder : Process.Sampling.refinementTarget
            comparison.rightIndex <=
          Process.Sampling.refinementTarget childStart := by
          unfold Process.Sampling.refinementTarget
          exact quarterRadius_antitone
            (by decide) comparison.right_ge
        exact
          ((Process.Sampling.stateAt_accurate
            (child.coefficient 0 child.baseInside).name.process
              (child.readingState 0 child.baseInside)
                comparison.rightIndex).trans_le indexOrder).trans
            (Geometric.Search.firstQuarterBelow_accurate
              1 (by decide) 0 child.readingTarget
                child.readingTarget_positive))
  exact
    { childCenter := childCenter
      close_radius := by
        let queryLater := query.laterValue comparison.leftIndex
        have alignedClose := comparison.close
          (Nat.le_refl comparison.leftIndex)
          (Nat.le_refl comparison.rightIndex)
        have alignedCloseReverse :
            Data.Gaussian.Norm.Basic.normSq
                (childCenter.value - queryLater) < target := by
          have reverse : childCenter.value - queryLater =
              -(queryLater - childCenter.value) := by
            apply Basic.ext <;>
              simp only [Basic.sub_re,
                Basic.sub_im,
                Basic.neg_re,
                Basic.neg_im] <;> ring1
          rw [reverse, Norm.Basic.normSq_neg]
          exact alignedClose
        have queryTail := query.laterValue_sub_value_le_radius
          comparison.leftIndex
        have identity : childCenter.value - query.value =
            (childCenter.value - queryLater) +
              (queryLater - query.value) := by
          apply Basic.ext <;>
            simp only [Basic.sub_re,
              Basic.sub_im,
              Basic.add_re,
              Basic.add_im] <;> ring1
        rw [identity]
        exact (Norm.Bounds.normSq_add_le_two _ _).trans_lt
          (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
            (by decide)
            ((Fraction.Order.Arithmetic.add_lt_add_right_direct
              alignedCloseReverse
                (Data.Gaussian.Norm.Basic.normSq
                  (queryLater - query.value))).trans_le
              (add_le_add le_rfl queryTail)))
      close := by
        let queryLater := query.laterValue comparison.leftIndex
        have alignedClose := comparison.close
          (Nat.le_refl comparison.leftIndex)
          (Nat.le_refl comparison.rightIndex)
        have alignedCloseReverse :
            Data.Gaussian.Norm.Basic.normSq
                (childCenter.value - queryLater) < target := by
          have reverse : childCenter.value - queryLater =
              -(queryLater - childCenter.value) := by
            apply Basic.ext <;>
              simp only [Basic.sub_re,
                Basic.sub_im,
                Basic.neg_re,
                Basic.neg_im] <;> ring1
          rw [reverse, Norm.Basic.normSq_neg]
          exact alignedClose
        have queryTail := query.laterValue_sub_value_lt comparison.leftIndex
        have identity : childCenter.value - query.value =
            (childCenter.value - queryLater) +
              (queryLater - query.value) := by
          apply Basic.ext <;>
            simp only [Basic.sub_re,
              Basic.sub_im,
              Basic.add_re,
              Basic.add_im] <;> ring1
        rw [identity]
        exact
          (Norm.Bounds.normSq_add_le_two _ _).trans_lt
            (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              (by decide)
              (Fraction.Order.Arithmetic.add_lt_add_direct
                alignedCloseReverse queryTail)) }

open Purelib.Approximation.Gaussian in
/-- Select the child center aligned to the retained query using the parent's model allowance as tolerance. -/
def alignedChildAt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (query : QueryState parent fraction inside)
    (coefficientEquivalent :
      Equivalence.NamedEquivalent
        (parent.coefficient fraction inside).name
        (child.coefficient 0 child.baseInside).name) :
    CenterState child :=
  (alignQueryRight parent child query coefficientEquivalent
    parent.modelErrorAllowance parent.modelErrorAllowance_positive).childCenter

section
open Purelib.Data.Rat
open Purelib.Polynomial
/-- Construct the constant cell model at the original base reading with four times the model-error allowance.

The exact local endpoints are retained, and the initial observation list is empty; the uniform certificate supplies
certified queries separately. -/
def model {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : CellModel :=
  { start := prepared.point 0
    finish := prepared.point 1
    polynomial := Ascending.Gaussian.Basic.constant prepared.baseReading
    localAllowance := 4 * prepared.modelErrorAllowance
    localAllowance_nonneg :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        prepared.modelErrorAllowance_positive.le
    observations := [] }

/-- Construct the constant cell model at the retained cached center with sixteen times the model-error allowance.

The original endpoints and exact cached value are retained; changing the center requires its explicit comparison
certificate. -/
def centeredModel {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared) : CellModel :=
  { start := prepared.point 0
    finish := prepared.point 1
    polynomial := Ascending.Gaussian.Basic.constant center.value
    localAllowance := 16 * prepared.modelErrorAllowance
    localAllowance_nonneg :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        sixteen_nonnegative
        prepared.modelErrorAllowance_positive.le
    observations := [] }

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Certify a one-cell replacement obtained by recaching the center's exact value and denominator.

The certificate retains both original cell models, the actual value difference, its bound, and equality of their total
displacement. -/
def centeredModelRecachePartitionCertificate
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared)
    (value denominator : Gaussian)
    (denominatorPossible :
      (prepared.sheetValue 0 prepared.baseInside).value.name.process.Possible
        center.state.2 denominator)
    (valueEq :
      value = prepared.point 0 ^ differential.exponent / denominator) :
    Basic.PathModel.ConstantPartitionCertificate
      (prepared.centeredModel center)
      (Basic.PathModel.mk
        [prepared.centeredModel
          (center.recache value denominator denominatorPossible valueEq)]) := by
  let replacement :=
    center.recache value denominator denominatorPossible valueEq
  let error := replacement.value - center.value
  have errorLe : Data.Gaussian.Norm.Basic.normSq error <=
      (prepared.centeredModel replacement).localAllowance := by
    have localBound := center.recache_value_sub_value_lt value denominator
      denominatorPossible valueEq
    apply localBound.le.trans
    change prepared.modelErrorAllowance <=
      16 * prepared.modelErrorAllowance
    calc
      prepared.modelErrorAllowance = 1 * prepared.modelErrorAllowance := by
        ring1
      _ <= 16 * prepared.modelErrorAllowance :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (by decide) prepared.modelErrorAllowance_positive.le
  exact
    { reference := center.value
      parent_polynomial_eq := rfl
      errors := [error]
      comparison := .cons replacement.value error rfl rfl (by simpa only [Norm.Basic.normSq_eq_canonical] using errorLe)
        .nil
      displacement_eq := by
        apply Basic.ext <;>
          simp only [Basic.PathModel.displacementSum,
            List.foldr_cons, List.foldr_nil,
            Basic.CellModel.displacement,
            centeredModel, Basic.add_re,
            Basic.add_im,
            Basic.zero_re,
            Basic.zero_im,
            Basic.sub_re,
            Basic.sub_im] <;> ring1 }

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- At exponent zero, the centered integral sample is the original displacement times the reciprocal cached denominator.
-/
theorem centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    (prepared.centeredModel center).integralSample =
      (prepared.centeredModel center).displacement * (1 / center.denominator) := by
  rw [Cell.Basic.CellModel.integralSample_constant
    (prepared.centeredModel center) center.value rfl,
      center.value_eq_one_div_denominator_of_exponent_zero exponentZero]

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- A positive denominator projection lower bound gives a real integral-sample lower bound for exponent zero. -/
theorem centeredModel_integralSample_re_lower_of_projection
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0)
    (projectionLower : Coordinate) (projectionPositive : 0 < projectionLower)
    (projectionLe : projectionLower <=
      (prepared.centeredModel center).displacement.re * center.denominator.re +
        (prepared.centeredModel center).displacement.im * center.denominator.im) :
    projectionLower /
        (PreparedSheetContinuation.prepared prepared.segment
          prepared.left prepared.owner prepared.request).track.initial.box.normSqBound <=
      (prepared.centeredModel center).integralSample.re := by
  let box :=
    (PreparedSheetContinuation.prepared prepared.segment
      prepared.left prepared.owner prepared.request).track.initial.box
  let displacement := (prepared.centeredModel center).displacement
  let denominator := center.denominator
  have inside : box.Contains denominator := center.denominator_in_prepared_box
  have denominatorNonzero : denominator ≠ 0 := by
    intro equal
    have realZero := congrArg Basic.Canonical.re equal
    have imaginaryZero := congrArg Basic.Canonical.im equal
    change center.denominator.re = 0 at realZero
    change center.denominator.im = 0 at imaginaryZero
    rw [realZero, imaginaryZero] at projectionLe
    simp only [Fraction.Field.mul_zero_direct,
      Fraction.Field.zero_add] at projectionLe
    exact (not_lt_of_ge projectionLe) projectionPositive
  have normPositive : 0 <
      Data.Gaussian.Norm.Basic.normSq denominator :=
    Norm.Basic.normSq_pos denominatorNonzero
  have normLe :
      Data.Gaussian.Norm.Basic.normSq denominator <= box.normSqBound :=
    box.normSq_le_normSqBound inside
  have lowerToSameNumerator :
      projectionLower / box.normSqBound <=
        projectionLower /
          Data.Gaussian.Norm.Basic.normSq denominator :=
    Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      projectionPositive.le normPositive normLe
  have sameDenominator :
      projectionLower /
          Data.Gaussian.Norm.Basic.normSq denominator <=
        (displacement.re * denominator.re +
          displacement.im * denominator.im) /
            Data.Gaussian.Norm.Basic.normSq denominator := by
    rw [Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      projectionLe
      (Fraction.Order.Field.inv_pos_direct normPositive).le
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero, CenterState.mul_one_div_re]
  exact lowerToSameNumerator.trans sameDenominator

/-- The exact target-minus-source displacement of the retained local segment. -/
def integralDisplacement
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Gaussian :=
  prepared.point 1 - prepared.point 0

/-- Compute a signed reciprocal projection lower bound from the original cached box and segment denominator floor.

The numerator projection is rounded downward, and its sign selects the certified denominator endpoint before division.
-/
def geometricIntegralProjectionLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (displacement : Gaussian) : Coordinate :=
  let box := prepared.cached.preparedOwner.track.initial.box
  signedQuotientLower
    (dyadicRealLower
      (boxProjectionLower box displacement))
    (geometricDenominatorLower prepared.segment box)
    (boxNormSqCeil box)

/-- Round the cached-box reciprocal projection bound downward to the fixed dyadic grid. -/
def geometricIntegralProjectionDyadicLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (displacement : Gaussian) : Coordinate :=
  dyadicRealLower
    (prepared.geometricIntegralProjectionLower displacement)

/-- Evaluate the cached-box reciprocal projection bound on the original integral displacement. -/
def geometricIntegralRealLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.geometricIntegralProjectionLower prepared.integralDisplacement

/-- Read the center-independent geometric real lower bound associated with the original prepared edge. -/
def centeredModelIntegralRealLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (_center : CenterState prepared) : Coordinate :=
  prepared.geometricIntegralRealLower

/-- Read the downward dyadic real lower bound for the original integral displacement. -/
def geometricIntegralRealDyadicLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.geometricIntegralProjectionDyadicLower
    prepared.integralDisplacement

/-- Read the downward dyadic real lower bound for the negated original integral displacement. -/
def geometricNegatedIntegralRealDyadicLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) : Coordinate :=
  prepared.geometricIntegralProjectionDyadicLower
    (-prepared.integralDisplacement)

/-- Read the downward dyadic projection bound using the conjugate direction times the original displacement. -/
def geometricDirectionalIntegralDyadicLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (direction : Gaussian) : Coordinate :=
  prepared.geometricIntegralProjectionDyadicLower
    (direction.conj * prepared.integralDisplacement)

/-- Combine the segment magnitude floor with the retained center's denominator projection box. -/
def centeredBallDenominatorLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Coordinate :=
  geometricDenominatorLower prepared.segment center.denominatorProjectionBox

/-- The center-specific projection-box denominator floor is strictly positive. -/
theorem centeredBallDenominatorLower_positive
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) :
    0 < centeredBallDenominatorLower center :=
  geometricDenominatorLower_positive prepared.segment
    center.denominatorProjectionBox

/-- Compute the signed reciprocal projection bound using the retained center's denominator projection box. -/
def centeredBallIntegralProjectionLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) : Coordinate :=
  let box := center.denominatorProjectionBox
  let lowerSq := geometricDenominatorLower prepared.segment box
  signedQuotientLower
    (dyadicRealLower
      (boxProjectionLower box displacement))
    lowerSq
    (boxNormSqCeil box)

/-- Round the center-specific reciprocal projection bound downward to the fixed dyadic grid. -/
def centeredBallIntegralProjectionDyadicLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) : Coordinate :=
  dyadicRealLower
    (centeredBallIntegralProjectionLower center displacement)

/-- Read the center-specific dyadic lower bound on the original integral displacement. -/
def centeredBallIntegralRealDyadicLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Coordinate :=
  centeredBallIntegralProjectionDyadicLower center
    prepared.integralDisplacement

/-- Read the center-specific dyadic lower bound on the negated original displacement. -/
def centeredBallNegatedIntegralRealDyadicLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) : Coordinate :=
  centeredBallIntegralProjectionDyadicLower center
    (-prepared.integralDisplacement)

/-- Read the center-specific dyadic lower bound on the displacement projected in a supplied Gaussian direction. -/
def centeredBallDirectionalIntegralDyadicLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (direction : Gaussian) : Coordinate :=
  centeredBallIntegralProjectionDyadicLower center
    (direction.conj * prepared.integralDisplacement)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The center-specific projection estimate bounds the exact coordinate quotient of the retained denominator.

The original centered-ball and geometric projection estimates bound
the same retained quotient. Their unchanged maxima combine those bounds. -/
theorem centeredBallIntegralProjectionLower_le_quotient
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) :
    centeredBallIntegralProjectionLower center displacement <=
      (displacement.re * center.denominator.re +
        displacement.im * center.denominator.im) /
          Data.Gaussian.Norm.Basic.normSq center.denominator := by
  let box := center.denominatorProjectionBox
  let denominator := center.denominator
  let projection := boxProjectionLower box displacement
  let roundedProjection := dyadicRealLower projection
  let lowerSq := centeredBallDenominatorLower center
  let upperSq := boxNormSqCeil box
  have denominatorInsideBox : box.Contains denominator :=
    center.denominator_in_projection_box
  have lowerPositive : 0 < lowerSq :=
    centeredBallDenominatorLower_positive center
  have cellLowerLeNorm : cellDenominatorLower prepared.segment <=
        Data.Gaussian.Norm.Basic.normSq denominator :=
    ((Fraction.Order.Basic.le_max_right
        (PreparedModels.residualDenominatorLower
          prepared.segment)
        (PreparedModels.magnitudeDenominatorLower
          prepared.segment)).trans
      ((Fraction.Order.Basic.le_max_left _ _).trans (Fraction.Order.Basic.le_max_left _ _))).trans
      (prepared.denominator_candidate_lower 0 prepared.baseInside center.state.2
        center.denominator_possible)
  have boxLowerLeNorm : boxNormSqLower box <=
      Data.Gaussian.Norm.Basic.normSq denominator :=
    boxNormSqLower_le denominatorInsideBox
  have lowerLeNorm : lowerSq <=
      Data.Gaussian.Norm.Basic.normSq denominator :=
    Fraction.Order.Basic.max_le cellLowerLeNorm boxLowerLeNorm
  have normLeUpper :
      Data.Gaussian.Norm.Basic.normSq denominator <= upperSq :=
    (box.normSq_le_normSqBound denominatorInsideBox).trans
      (normSqBound_le_boxNormSqCeil box)
  have signedLower := signedQuotientLower_le roundedProjection lowerSq
    (Data.Gaussian.Norm.Basic.normSq denominator) upperSq
      lowerPositive lowerLeNorm normLeUpper
  have projectionLe : projection <=
      displacement.re * denominator.re + displacement.im * denominator.im :=
    boxProjectionLower_le denominatorInsideBox
  have roundedProjectionLe : roundedProjection <=
      displacement.re * denominator.re + displacement.im * denominator.im :=
    (dyadicRealLower_le projection).trans projectionLe
  have normPositive : 0 <
      Data.Gaussian.Norm.Basic.normSq denominator :=
    lowerPositive.trans_le lowerLeNorm
  have quotientProjectionLe :
      roundedProjection /
          Data.Gaussian.Norm.Basic.normSq denominator <=
        (displacement.re * denominator.re +
          displacement.im * denominator.im) /
            Data.Gaussian.Norm.Basic.normSq denominator := by
    rw [Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      roundedProjectionLe
        (Fraction.Order.Field.inv_pos_direct normPositive).le
  change signedQuotientLower roundedProjection lowerSq upperSq <= _
  exact signedLower.trans quotientProjectionLe

open Purelib.Data.Gaussian in
/-- The rounded center-specific projection estimate bounds the exact retained-denominator quotient. -/
theorem centeredBallIntegralProjectionDyadicLower_le_quotient
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) :
    centeredBallIntegralProjectionDyadicLower center displacement <=
      (displacement.re * center.denominator.re +
        displacement.im * center.denominator.im) /
          Data.Gaussian.Norm.Basic.normSq center.denominator :=
  (dyadicRealLower_le _).trans
    (centeredBallIntegralProjectionLower_le_quotient center displacement)

/-- For exponent zero, the center-specific dyadic bound is below the actual integral sample's real part. -/
theorem centeredBallIntegralRealDyadicLower_le
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    centeredBallIntegralRealDyadicLower center <=
      (prepared.centeredModel center).integralSample.re := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero, CenterState.mul_one_div_re]
  exact centeredBallIntegralProjectionDyadicLower_le_quotient center
    prepared.integralDisplacement

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- For exponent zero, the center-specific negative-displacement bound is below the negative real integral sample. -/
theorem centeredBallNegatedIntegralRealDyadicLower_le
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    centeredBallNegatedIntegralRealDyadicLower center <=
      -(prepared.centeredModel center).integralSample.re := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero, CenterState.mul_one_div_re]
  change centeredBallNegatedIntegralRealDyadicLower center <=
    -((prepared.integralDisplacement.re * center.denominator.re +
      prepared.integralDisplacement.im * center.denominator.im) /
        Data.Gaussian.Norm.Basic.normSq center.denominator)
  have bound := centeredBallIntegralProjectionDyadicLower_le_quotient
    center (-prepared.integralDisplacement)
  convert bound using 1
  · rfl
  · simp only [Basic.neg_re,
      Basic.neg_im,
      Fraction.Field.div_eq_mul_inv_direct]
    ring1

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- For exponent zero, the center-specific directional bound is below the actual integral sample's coordinate
projection. -/
theorem centeredBallDirectionalIntegralDyadicLower_le
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    centeredBallDirectionalIntegralDyadicLower center direction <=
      direction.re * (prepared.centeredModel center).integralSample.re +
        direction.im * (prepared.centeredModel center).integralSample.im := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero]
  have lower := centeredBallIntegralProjectionDyadicLower_le_quotient center
    (direction.conj * prepared.integralDisplacement)
  apply lower.trans_eq
  rw [← CenterState.mul_one_div_re]
  unfold integralDisplacement centeredModel
    Basic.CellModel.displacement
  simp only [Basic.Canonical.conj,
    Basic.mul_re,
    Basic.mul_im]
  ring1

/-- Read the center-independent dyadic real bound of the original prepared edge. -/
def centeredModelIntegralRealDyadicLower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (_center : CenterState prepared) : Coordinate :=
  prepared.geometricIntegralRealDyadicLower

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Riemann.Branches in
/-- The original cached-box projection bound is below the exact quotient using any retained center denominator.

The original line and box projection estimates bound the same retained
quotient. Their unchanged maximum retains both estimates. -/
theorem geometricIntegralProjectionLower_le_quotient
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) :
    prepared.geometricIntegralProjectionLower displacement <=
      (displacement.re * center.denominator.re +
        displacement.im * center.denominator.im) /
          Data.Gaussian.Norm.Basic.normSq center.denominator := by
  let box := prepared.cached.preparedOwner.track.initial.box
  let denominator := center.denominator
  let projection := boxProjectionLower box displacement
  let roundedProjection := dyadicRealLower projection
  let lowerSq := geometricDenominatorLower prepared.segment box
  let upperSq := boxNormSqCeil box
  have denominatorInsideBox : box.Contains denominator :=
    center.denominator_in_cached_prepared_box
  have denominatorInsideBall :
      ((prepared.sheetValue 0 prepared.baseInside).value.name.process.ball
        center.state.2).Contains denominator :=
    (prepared.sheetValue 0 prepared.baseInside).value.name.process.possible_inside
      center.denominator_possible
  have lowerPositive : 0 < lowerSq :=
    geometricDenominatorLower_positive prepared.segment box
  have segmentLowerLeApart : cellDenominatorLower prepared.segment <=
      (prepared.sheetValue 0 prepared.baseInside).apart.certificate.lowerSq := by
    change PreparedModels.magnitudeDenominatorLower
        prepared.segment <=
      (PreparedModels.sheetValueAtCached curve
        differential prepared.segment prepared.within prepared.left
          prepared.owner prepared.request prepared.cached prepared.ordered
            prepared.small prepared.sheet 0
              prepared.baseInside).apart.certificate.lowerSq
    rw [PreparedModels.sheetValueAtCached_apart_lowerSq]
    exact (Fraction.Order.Basic.le_max_right _ _).trans
      (PreparedModels.denominatorLower_le_point
        prepared.segment
          (prepared.segment.pointAt_onCertifiedLine
            (PreparedSheetContinuation.parameterAt prepared.left
              prepared.request 0)
            (PreparedSheetContinuation.parameterAt_inside
              prepared.left prepared.request prepared.ordered 0
                prepared.baseInside)))
  have segmentLowerLeNorm : cellDenominatorLower prepared.segment <=
      Data.Gaussian.Norm.Basic.normSq denominator :=
    segmentLowerLeApart.trans
      ((prepared.sheetValue 0 prepared.baseInside).apart.certificate.lower
        center.state.2 denominatorInsideBall)
  have boxLowerLeNorm : boxNormSqLower box <=
      Data.Gaussian.Norm.Basic.normSq denominator :=
    boxNormSqLower_le denominatorInsideBox
  have lowerLeNorm : lowerSq <=
      Data.Gaussian.Norm.Basic.normSq denominator :=
    Fraction.Order.Basic.max_le segmentLowerLeNorm boxLowerLeNorm
  have normLeUpper :
      Data.Gaussian.Norm.Basic.normSq denominator <= upperSq :=
    (box.normSq_le_normSqBound denominatorInsideBox).trans
      (normSqBound_le_boxNormSqCeil box)
  have signedLower := signedQuotientLower_le
    roundedProjection lowerSq
      (Data.Gaussian.Norm.Basic.normSq denominator) upperSq
        lowerPositive lowerLeNorm normLeUpper
  have projectionLe : projection <=
      displacement.re * denominator.re + displacement.im * denominator.im :=
    boxProjectionLower_le denominatorInsideBox
  have roundedProjectionLe : roundedProjection <=
      displacement.re * denominator.re + displacement.im * denominator.im :=
    (dyadicRealLower_le projection).trans projectionLe
  have normPositive : 0 <
      Data.Gaussian.Norm.Basic.normSq denominator :=
    lowerPositive.trans_le lowerLeNorm
  have quotientProjectionLe :
      roundedProjection /
          Data.Gaussian.Norm.Basic.normSq denominator <=
        (displacement.re * denominator.re +
          displacement.im * denominator.im) /
            Data.Gaussian.Norm.Basic.normSq denominator := by
    rw [Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.div_eq_mul_inv_direct]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      roundedProjectionLe
        (Fraction.Order.Field.inv_pos_direct normPositive).le
  change signedQuotientLower roundedProjection lowerSq upperSq <= _
  exact signedLower.trans quotientProjectionLe

open Purelib.Data.Gaussian in
/-- The rounded cached-box projection bound is below the exact retained-denominator quotient. -/
theorem geometricIntegralProjectionDyadicLower_le_quotient
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (displacement : Gaussian) :
    prepared.geometricIntegralProjectionDyadicLower displacement <=
      (displacement.re * center.denominator.re +
        displacement.im * center.denominator.im) /
          Data.Gaussian.Norm.Basic.normSq center.denominator :=
  (dyadicRealLower_le _).trans
    (prepared.geometricIntegralProjectionLower_le_quotient center displacement)

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- For exponent zero, the cached-box directional bound is below the actual centered integral sample's projection. -/
theorem geometricDirectionalIntegralDyadicLower_le
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared)
    (direction : Gaussian)
    (exponentZero : differential.exponent = 0) :
    prepared.geometricDirectionalIntegralDyadicLower direction <=
      direction.re * (prepared.centeredModel center).integralSample.re +
        direction.im * (prepared.centeredModel center).integralSample.im := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero]
  have lower := prepared.geometricIntegralProjectionDyadicLower_le_quotient
    center (direction.conj * prepared.integralDisplacement)
  apply lower.trans_eq
  rw [← CenterState.mul_one_div_re]
  unfold integralDisplacement centeredModel
    Basic.CellModel.displacement
  simp only [Basic.Canonical.conj,
    Basic.mul_re,
    Basic.mul_im]
  ring1

/-- For exponent zero, the geometric real bound is below the actual centered integral sample's real part. -/
theorem centeredModelIntegralRealLower_le
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    centeredModelIntegralRealLower center <=
      (prepared.centeredModel center).integralSample.re := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero, CenterState.mul_one_div_re]
  exact prepared.geometricIntegralProjectionLower_le_quotient center
    prepared.integralDisplacement

/-- For exponent zero, the rounded geometric bound is below the centered integral sample's real part. -/
theorem centeredModelIntegralRealDyadicLower_le
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0) :
    centeredModelIntegralRealDyadicLower center <=
      (prepared.centeredModel center).integralSample.re :=
  (dyadicRealLower_le _).trans
    (centeredModelIntegralRealLower_le center exponentZero)

/-- For exponent zero, the retained edge's dyadic real bound is below its centered integral sample. -/
theorem geometricIntegralRealDyadicLower_le
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared)
    (exponentZero : differential.exponent = 0) :
    prepared.geometricIntegralRealDyadicLower <=
      (prepared.centeredModel center).integralSample.re :=
  prepared.centeredModelIntegralRealDyadicLower_le center exponentZero

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- For exponent zero, the negative-displacement dyadic bound is below the negative real integral sample. -/
theorem geometricNegatedIntegralRealDyadicLower_le
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared)
    (exponentZero : differential.exponent = 0) :
    prepared.geometricNegatedIntegralRealDyadicLower <=
      -(prepared.centeredModel center).integralSample.re := by
  rw [centeredModel_integralSample_eq_mul_one_div_denominator_of_exponent_zero
    center exponentZero, CenterState.mul_one_div_re]
  change prepared.geometricNegatedIntegralRealDyadicLower <=
    -((prepared.integralDisplacement.re * center.denominator.re +
      prepared.integralDisplacement.im * center.denominator.im) /
        Data.Gaussian.Norm.Basic.normSq center.denominator)
  have bound := prepared.geometricIntegralProjectionDyadicLower_le_quotient
    center (-prepared.integralDisplacement)
  convert bound using 1
  · rfl
  · simp only [Basic.neg_re,
      Basic.neg_im,
      Fraction.Field.div_eq_mul_inv_direct]
    ring1

open Purelib.Riemann.Branches in
/-- A positive cached-box projection yields its quotient lower bound for the real integral sample at exponent zero. -/
theorem centeredModel_integralSample_re_lower
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {prepared : PreparedEdge curve differential}
    (center : CenterState prepared) (exponentZero : differential.exponent = 0)
    (positive : 0 < boxProjectionLower
      (PreparedSheetContinuation.prepared prepared.segment
        prepared.left prepared.owner prepared.request).track.initial.box
      (prepared.centeredModel center).displacement) :
    boxProjectionLower
        (PreparedSheetContinuation.prepared prepared.segment
          prepared.left prepared.owner prepared.request).track.initial.box
        (prepared.centeredModel center).displacement /
      (PreparedSheetContinuation.prepared prepared.segment
        prepared.left prepared.owner prepared.request).track.initial.box.normSqBound <=
      (prepared.centeredModel center).integralSample.re := by
  apply centeredModel_integralSample_re_lower_of_projection center exponentZero
    _ positive
  exact boxProjectionLower_le center.denominator_in_prepared_box

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- At exponent zero, the canonical centered integral sample is displacement divided by the retained residual root
center. -/
theorem canonicalCenteredModel_integralSample_eq_residualRootCenter
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (exponentZero : differential.exponent = 0) :
    (prepared.centeredModel (CenterState.canonical prepared)).integralSample =
      (prepared.point 1 - prepared.point 0) *
        (1 / prepared.residualRootCenter) := by
  rw [Cell.Basic.CellModel.integralSample_constant
    (prepared.centeredModel (CenterState.canonical prepared))
      (CenterState.canonical prepared).value rfl, prepared.canonical_value_eq_residualCoefficientCenter]
  unfold residualCoefficientCenter
  rw [exponentZero, pow_zero]
  rfl

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Path
/-- At exponent zero, a common positive denominator floor bounds integral-sample error by point movement times the
inverse-root error allowance. -/
theorem canonicalCenteredModel_integralSample_sub_candidate_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (exponentZero : differential.exponent = 0)
    {candidate : Gaussian} {lowerSq rootMovement : Coordinate}
    (lowerPositive : 0 < lowerSq)
    (centerLower : lowerSq <= prepared.cachedDenominatorLower)
    (candidateLower : lowerSq <=
      Data.Gaussian.Norm.Basic.normSq candidate)
    (rootClose :
      Data.Gaussian.Norm.Basic.normSq
        (prepared.residualRootCenter - candidate) <= rootMovement) :
    Data.Gaussian.Norm.Basic.normSq
        ((prepared.centeredModel (CenterState.canonical prepared)).integralSample -
          (prepared.point 1 - prepared.point 0) * (1 / candidate)) <=
      prepared.pointMovement *
        ((2 * rootMovement) / (lowerSq * lowerSq)) := by
  rw [Cell.Basic.CellModel.integralSample_constant
    (prepared.centeredModel (CenterState.canonical prepared))
      (CenterState.canonical prepared).value rfl, prepared.canonical_value_eq_residualCoefficientCenter]
  change Data.Gaussian.Norm.Basic.normSq
      ((prepared.point 1 - prepared.point 0) *
          prepared.residualCoefficientCenter -
        (prepared.point 1 - prepared.point 0) * (1 / candidate)) <= _
  have identity :
      (prepared.point 1 - prepared.point 0) *
            prepared.residualCoefficientCenter -
          (prepared.point 1 - prepared.point 0) * (1 / candidate) =
        (prepared.point 1 - prepared.point 0) *
          (prepared.residualCoefficientCenter - 1 / candidate) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.mul_re,
        Basic.mul_im] <;> ring1
  rw [identity, Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (prepared.residualCoefficientCenter_sub_candidateInverse_le exponentZero
      lowerPositive centerLower candidateLower rootClose)
    (Norm.Basic.normSq_nonneg _)

/-- At exponent zero, separate positive center and candidate floors give the product-denominator integral-sample error
bound. -/
theorem canonicalCenteredModel_integralSample_sub_candidate_le_separate
    {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (exponentZero : differential.exponent = 0)
    {candidate : Gaussian}
    {centerLowerSq candidateLowerSq rootMovement : Coordinate}
    (centerLowerPositive : 0 < centerLowerSq)
    (candidateLowerPositive : 0 < candidateLowerSq)
    (centerLower : centerLowerSq <= prepared.cachedDenominatorLower)
    (candidateLower : candidateLowerSq <=
      Data.Gaussian.Norm.Basic.normSq candidate)
    (rootClose :
      Data.Gaussian.Norm.Basic.normSq
        (prepared.residualRootCenter - candidate) <= rootMovement) :
    Data.Gaussian.Norm.Basic.normSq
        ((prepared.centeredModel (CenterState.canonical prepared)).integralSample -
          (prepared.point 1 - prepared.point 0) * (1 / candidate)) <=
      prepared.pointMovement *
        (rootMovement / (centerLowerSq * candidateLowerSq)) := by
  rw [Cell.Basic.CellModel.integralSample_constant
    (prepared.centeredModel (CenterState.canonical prepared))
      (CenterState.canonical prepared).value rfl, prepared.canonical_value_eq_residualCoefficientCenter]
  change Data.Gaussian.Norm.Basic.normSq
      ((prepared.point 1 - prepared.point 0) *
          prepared.residualCoefficientCenter -
        (prepared.point 1 - prepared.point 0) * (1 / candidate)) <= _
  have identity :
      (prepared.point 1 - prepared.point 0) *
            prepared.residualCoefficientCenter -
          (prepared.point 1 - prepared.point 0) * (1 / candidate) =
        (prepared.point 1 - prepared.point 0) *
          (prepared.residualCoefficientCenter - 1 / candidate) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.mul_re,
        Basic.mul_im] <;> ring1
  rw [identity, Norm.Basic.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (prepared.residualCoefficientCenter_sub_candidateInverse_le_separate
      exponentZero centerLowerPositive candidateLowerPositive centerLower
        candidateLower rootClose)
    (Norm.Basic.normSq_nonneg _)

end

open Purelib.Approximation.Gaussian in
/-- Select the child center aligned with the retained parent center at the parent's model-error tolerance. -/
def alignedChildCenter {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    (parentCenter : CenterState parent)
    (coefficientEquivalent :
      Equivalence.NamedEquivalent
        (parent.coefficient 0 parent.baseInside).name
        (child.coefficient 0 child.baseInside).name) :
    CenterState child :=
  (alignRight parent child parentCenter coefficientEquivalent
    parent.modelErrorAllowance parent.modelErrorAllowance_positive).childCenter

section
open Purelib.Approximation.Gaussian
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Path
/-- The aligned child's actual center difference is paid by the original parent-child model allowance. -/
theorem alignedChildCenter_error_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    (parentCenter : CenterState parent)
    (coefficientEquivalent :
      Equivalence.NamedEquivalent
        (parent.coefficient 0 parent.baseInside).name
        (child.coefficient 0 child.baseInside).name) :
    Data.Gaussian.Norm.Basic.normSq
        ((alignedChildCenter parent child parentCenter coefficientEquivalent).value -
          parentCenter.value) <=
      Basic.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel
          (alignedChildCenter parent child parentCenter
            coefficientEquivalent)) := by
  let alignment := alignRight parent child parentCenter coefficientEquivalent
    parent.modelErrorAllowance parent.modelErrorAllowance_positive
  have close :
      Data.Gaussian.Norm.Basic.normSq
          (alignment.childCenter.value - parentCenter.value) <
        4 * parent.modelErrorAllowance := by
    exact alignment.close.trans_eq (by ring1)
  change Data.Gaussian.Norm.Basic.normSq
      (alignment.childCenter.value - parentCenter.value) <= _
  calc
    Data.Gaussian.Norm.Basic.normSq
        (alignment.childCenter.value - parentCenter.value) <=
      4 * parent.modelErrorAllowance := close.le
    _ <= 16 * parent.modelErrorAllowance :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        four_le_sixteen
          parent.modelErrorAllowance_positive.le
    _ <= 16 * parent.modelErrorAllowance +
        16 * parent.modelErrorAllowance :=
      le_add_of_nonneg_right
        (Fraction.Order.Arithmetic.mul_nonneg_direct
          sixteen_nonnegative parent.modelErrorAllowance_positive.le)
    _ <= (16 * parent.modelErrorAllowance +
          16 * parent.modelErrorAllowance) +
        (16 * child.modelErrorAllowance +
          16 * child.modelErrorAllowance) :=
      le_add_of_nonneg_right
        (add_nonneg
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            sixteen_nonnegative child.modelErrorAllowance_positive.le)
          (Fraction.Order.Arithmetic.mul_nonneg_direct
            sixteen_nonnegative child.modelErrorAllowance_positive.le))
    _ = Basic.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel alignment.childCenter) := by
      unfold Basic.PathModel.parentChildAllowance
      change (16 * parent.modelErrorAllowance +
            16 * parent.modelErrorAllowance) +
          (16 * child.modelErrorAllowance +
            16 * child.modelErrorAllowance) =
        2 * (16 * parent.modelErrorAllowance +
          16 * child.modelErrorAllowance)
      ring1

/-- Alignment through a retained parent query pays the actual child-to-parent center difference from the original model
allowances. -/
theorem alignedChildAt_error_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (parentCenter : CenterState parent)
    (query : QueryState parent fraction inside)
    (coefficientEquivalent :
      Equivalence.NamedEquivalent
        (parent.coefficient fraction inside).name
        (child.coefficient 0 child.baseInside).name) :
    Data.Gaussian.Norm.Basic.normSq
        ((alignedChildAt parent child query coefficientEquivalent).value -
          parentCenter.value) <=
      Basic.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel
          (alignedChildAt parent child query coefficientEquivalent)) := by
  let alignment := alignQueryRight parent child query coefficientEquivalent
    parent.modelErrorAllowance parent.modelErrorAllowance_positive
  have childQuery :
      Data.Gaussian.Norm.Basic.normSq
          (alignment.childCenter.value - query.value) <=
        4 * parent.modelErrorAllowance :=
    alignment.close.trans_eq (by ring1) |>.le
  have queryParent :
      Data.Gaussian.Norm.Basic.normSq
          (query.value - parentCenter.value) <=
        10 * parent.modelErrorAllowance :=
    (query.value_sub_center_lt parentCenter).le
  have identity : alignment.childCenter.value - parentCenter.value =
      (alignment.childCenter.value - query.value) +
        (query.value - parentCenter.value) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  change Data.Gaussian.Norm.Basic.normSq
      (alignment.childCenter.value - parentCenter.value) <= _
  rw [identity]
  calc
    Data.Gaussian.Norm.Basic.normSq
        ((alignment.childCenter.value - query.value) +
          (query.value - parentCenter.value)) <=
      2 *
        (Data.Gaussian.Norm.Basic.normSq
            (alignment.childCenter.value - query.value) +
          Data.Gaussian.Norm.Basic.normSq
            (query.value - parentCenter.value)) :=
      Norm.Bounds.normSq_add_le_two _ _
    _ <= 2 * (4 * parent.modelErrorAllowance +
        10 * parent.modelErrorAllowance) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add childQuery queryParent) (by decide)
    _ = 2 * (14 * parent.modelErrorAllowance) := by ring1
    _ <= 2 * (16 * parent.modelErrorAllowance) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          fourteen_le_sixteen parent.modelErrorAllowance_positive.le)
        (by decide)
    _ <= 2 * (16 * parent.modelErrorAllowance +
        16 * child.modelErrorAllowance) :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.mul_nonneg_direct sixteen_nonnegative
            child.modelErrorAllowance_positive.le)) (by decide)
    _ = Basic.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel alignment.childCenter) := by
      unfold Basic.PathModel.parentChildAllowance
      rfl

/-- Any retained child center with coefficient equivalence at the parent query satisfies the original parent-child model
allowance.

The proof compares actual later witnesses and both retained centers; the allowance retains separate contributions from
the parent and child models. -/
theorem arbitraryChildAt_error_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    {fraction : Coordinate}
    {inside : (0 : Coordinate) <= fraction ∧ fraction <= 1}
    (parentCenter : CenterState parent)
    (childCenter : CenterState child)
    (query : QueryState parent fraction inside)
    (coefficientEquivalent :
      Equivalence.NamedEquivalent
        (parent.coefficient fraction inside).name
        (child.coefficient 0 child.baseInside).name) :
    Data.Gaussian.Norm.Basic.normSq
        (childCenter.value - parentCenter.value) <=
      Basic.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel childCenter) := by
  let target := parent.modelErrorAllowance + child.modelErrorAllowance
  have targetPositive : 0 < target :=
    Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
      parent.modelErrorAllowance_positive child.modelErrorAllowance_positive.le
  let centerEquivalent : Equivalence.NamedEquivalent
      query.named childCenter.named :=
    Equivalence.NamedEquivalent.trans query.equivalent.symm
      (Equivalence.NamedEquivalent.trans coefficientEquivalent
        childCenter.equivalent)
  let comparison := centerEquivalent.compare 0 0 target targetPositive
  let queryLater := query.laterValue comparison.leftIndex
  let childLater := childCenter.laterValue comparison.rightIndex
  have laterClose :
      Data.Gaussian.Norm.Basic.normSq
          (childLater - queryLater) < target := by
    have forward := comparison.close
      (Nat.le_refl comparison.leftIndex)
      (Nat.le_refl comparison.rightIndex)
    have reverse : childLater - queryLater = -(queryLater - childLater) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [reverse, Norm.Basic.normSq_neg]
    exact forward
  have childTail :
      Data.Gaussian.Norm.Basic.normSq
          (childCenter.value - childLater) < child.modelErrorAllowance := by
    have forward := childCenter.laterValue_sub_value_lt comparison.rightIndex
    have reverse : childCenter.value - childLater =
        -(childLater - childCenter.value) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.neg_re,
          Basic.neg_im] <;> ring1
    rw [reverse, Norm.Basic.normSq_neg]
    exact forward
  have childToQueryLater :
      Data.Gaussian.Norm.Basic.normSq
          (childCenter.value - queryLater) <
        2 * (child.modelErrorAllowance + target) := by
    have identity : childCenter.value - queryLater =
        (childCenter.value - childLater) + (childLater - queryLater) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.add_re,
          Basic.add_im] <;> ring1
    rw [identity]
    exact
      (Norm.Bounds.normSq_add_le_two _ _).trans_lt
        (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide)
          (Fraction.Order.Arithmetic.add_lt_add_direct childTail laterClose))
  have queryTail := query.laterValue_sub_value_lt comparison.leftIndex
  have childToQuery :
      Data.Gaussian.Norm.Basic.normSq
          (childCenter.value - query.value) <
        2 * (2 * (child.modelErrorAllowance + target) +
          parent.modelErrorAllowance) := by
    have identity : childCenter.value - query.value =
        (childCenter.value - queryLater) + (queryLater - query.value) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re,
          Basic.sub_im,
          Basic.add_re,
          Basic.add_im] <;> ring1
    rw [identity]
    exact
      (Norm.Bounds.normSq_add_le_two _ _).trans_lt
        (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide)
          (Fraction.Order.Arithmetic.add_lt_add_direct childToQueryLater
            queryTail))
  have queryToParent := query.value_sub_center_lt parentCenter
  have identity : childCenter.value - parentCenter.value =
      (childCenter.value - query.value) +
        (query.value - parentCenter.value) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  rw [identity]
  apply le_trans
    (Norm.Bounds.normSq_add_le_two _ _)
  apply le_trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add childToQuery.le queryToParent.le) (by decide))
  unfold target
  change
    2 *
        (2 *
            (2 *
                (child.modelErrorAllowance +
                  (parent.modelErrorAllowance + child.modelErrorAllowance)) +
              parent.modelErrorAllowance) +
          10 * parent.modelErrorAllowance) <=
      Basic.PathModel.parentChildAllowance
        (parent.centeredModel parentCenter)
        (child.centeredModel childCenter)
  unfold Basic.PathModel.parentChildAllowance
    centeredModel
  change
    2 *
        (2 *
            (2 *
                (child.modelErrorAllowance +
                  (parent.modelErrorAllowance + child.modelErrorAllowance)) +
              parent.modelErrorAllowance) +
          10 * parent.modelErrorAllowance) <=
      2 * (16 * parent.modelErrorAllowance +
        16 * child.modelErrorAllowance)
  have childPart : 16 * child.modelErrorAllowance <=
      32 * child.modelErrorAllowance := by
    calc
      16 * child.modelErrorAllowance <=
          16 * child.modelErrorAllowance +
            16 * child.modelErrorAllowance :=
        le_add_of_nonneg_right
          (Fraction.Order.Arithmetic.mul_nonneg_direct sixteen_nonnegative
            child.modelErrorAllowance_positive.le)
      _ = 32 * child.modelErrorAllowance := by ring1
  calc
    2 *
        (2 *
            (2 *
                (child.modelErrorAllowance +
                  (parent.modelErrorAllowance + child.modelErrorAllowance)) +
              parent.modelErrorAllowance) +
          10 * parent.modelErrorAllowance) =
      32 * parent.modelErrorAllowance +
        16 * child.modelErrorAllowance := by ring1
    _ <= 32 * parent.modelErrorAllowance +
        32 * child.modelErrorAllowance := add_le_add le_rfl childPart
    _ = 2 * (16 * parent.modelErrorAllowance +
        16 * child.modelErrorAllowance) := by ring1

end

open Purelib.Approximation.Gaussian in
set_option genInjectivity false in
/-- A retained child edge and center with a parent query and operational coefficient equivalence.

The parent center remains an index, and the child center is supplied explicitly; this certificate preserves both
original model owners. -/
structure CenteredChildAt {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent : PreparedEdge curve differential)
    (parentCenter : CenterState parent) where
  /-- The original prepared child edge being compared with the retained parent. -/ child : PreparedEdge curve
    differential
  /-- The exact supplied center state of this original child edge. -/ center : CenterState child
  /-- The retained parent query fraction. -/ fraction : Coordinate
  /-- The query fraction lies in the unit interval. -/ inside : (0 : Coordinate) <= fraction ∧ fraction <= 1
  /-- The exact retained parent query state at the indexed fraction. -/ query : QueryState parent fraction inside
  /-- Operational equivalence of the exact parent query coefficient and original child base coefficient. -/
    coefficientEquivalent :
    Equivalence.NamedEquivalent
      (parent.coefficient fraction inside).name
      (child.coefficient 0 child.baseInside).name

constructive_injectivity CenteredChildAt

namespace CenteredChildAt

open Purelib.Approximation.Gaussian in
/-- Construct the child comparison from equal points and equivalent root names, retaining the supplied parent and child
centers. -/
def ofRootEquivalent {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (parent child : PreparedEdge curve differential)
    (parentCenter : CenterState parent)
    (childCenter : CenterState child)
    (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1)
    (point_eq : parent.point fraction = child.point 0)
    (rootEquivalent :
      Equivalence.NamedEquivalent
        (parent.rootName fraction inside)
        (child.rootName 0 child.baseInside)) :
    CenteredChildAt parent parentCenter where
  child := child
  center := childCenter
  fraction := fraction
  inside := inside
  query := QueryState.canonical parent fraction inside
  coefficientEquivalent :=
    coefficientEquivalent_of_rootEquivalent parent child fraction inside
      point_eq rootEquivalent

/-- Read the exact constant cell model of the retained child edge and its supplied center. -/
def model {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent}
    (child : CenteredChildAt parent parentCenter) : CellModel :=
  child.child.centeredModel child.center

/-- The actual child-center coefficient minus the retained parent-center coefficient. -/
def error {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent}
    (child : CenteredChildAt parent parentCenter) : Gaussian :=
  child.center.value - parentCenter.value

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The actual child-center error is bounded by the comparison cell's retained allowance. -/
theorem error_le {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent}
    (child : CenteredChildAt parent parentCenter) :
    Data.Gaussian.Norm.Basic.normSq child.error <=
      (Basic.PathModel.comparisonCell
        (parent.centeredModel parentCenter) child.model).localAllowance := by
  simpa only [error, model,
    Basic.PathModel.comparisonCell,
    Basic.CellModel.withAllowance] using
      arbitraryChildAt_error_le parent child.child parentCenter child.center
        child.query child.coefficientEquivalent

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Construct the ordered constant-comparison certificate for the exact list of retained child models and errors. -/
def comparison {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent} :
    (children : List (CenteredChildAt parent parentCenter)) ->
      Basic.PathModel.ConstantComparison
        parentCenter.value
        (Basic.PathModel.comparisonBlock
          (parent.centeredModel parentCenter)
          (Basic.PathModel.mk
            (children.map model))).cells
        (children.map error)
  | [] => .nil
  | child :: remaining =>
      .cons child.center.value child.error rfl rfl (by simpa only [Norm.Basic.normSq_eq_canonical] using child.error_le)
        (comparison remaining)

section
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Replacing allowances by comparison allowances preserves the exact child models' total displacement. -/
theorem displacementSum_comparison {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent} :
    forall children : List (CenteredChildAt parent parentCenter),
      Basic.PathModel.displacementSum
          (Basic.PathModel.comparisonBlock
            (parent.centeredModel parentCenter)
            (Basic.PathModel.mk
              (children.map model))).cells =
        Basic.PathModel.displacementSum
          (children.map model)
  | [] => rfl
  | child :: remaining => by
      change
        (Basic.PathModel.comparisonCell
            (parent.centeredModel parentCenter) child.model).displacement +
            Basic.PathModel.displacementSum
              (Basic.PathModel.comparisonBlock
                (parent.centeredModel parentCenter)
                (Basic.PathModel.mk
                  (remaining.map model))).cells =
          child.model.displacement +
            Basic.PathModel.displacementSum
              (remaining.map model)
      rw [displacementSum_comparison remaining]
      rfl

/-- Certify the original child block against its retained parent using exact total-displacement equality.

The certificate retains the parent reference value, each original child model, the actual ordered error list, and its
comparison bounds. -/
def partitionCertificate {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent}
    (children : List (CenteredChildAt parent parentCenter))
    (displacement_eq :
      Basic.PathModel.displacementSum
          (children.map model) =
        (parent.centeredModel parentCenter).displacement) :
    Basic.PathModel.ConstantPartitionCertificate
      (parent.centeredModel parentCenter)
      (Basic.PathModel.comparisonBlock
        (parent.centeredModel parentCenter)
        (Basic.PathModel.mk
          (children.map model))) where
  reference := parentCenter.value
  parent_polynomial_eq := rfl
  errors := children.map error
  comparison := comparison children
  displacement_eq := by
    rw [displacementSum_comparison children]
    exact displacement_eq

end

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Obtain the exact displacement equality from a retained lifted path followed by the original child models.

The path's source and target coordinate equalities identify the original parent endpoints; the same children and
comparison certificates are retained. -/
def partitionCertificateOfFollowedBy {genus sheets : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    {parent : PreparedEdge curve differential}
    {parentCenter : CenterState parent}
    (children : List (CenteredChildAt parent parentCenter))
    {start finish : Lifted.Basic.LiftedPoint sheets}
    {path : Lifted.Basic.LiftedPath sheets start finish}
    (follows : Lifted.Basic.LiftedPath.FollowedBy
      (children.map model) path)
    (start_eq : (parent.centeredModel parentCenter).start = start.coordinate)
    (finish_eq : (parent.centeredModel parentCenter).finish =
      finish.coordinate) :
    Basic.PathModel.ConstantPartitionCertificate
      (parent.centeredModel parentCenter)
      (Basic.PathModel.comparisonBlock
        (parent.centeredModel parentCenter)
        (Basic.PathModel.mk
          (children.map model))) :=
  partitionCertificate children (by
    rw [Lifted.Basic.LiftedPath.followedBy_displacementSum follows]
    unfold Basic.CellModel.displacement
    rw [start_eq, finish_eq])

end CenteredChildAt

open Purelib.Integration.Polynomial.Gaussian.Path in
set_option genInjectivity false in
/-- An ordered refinement of original centered parent models by retained centered child blocks.

Each block carries its exact displacement equality and parent-centered comparison data, preserving the original ordered
model lists. -/
inductive CenteredPathRefinement {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    List CellModel -> List CellModel -> Type
  /-- Retain the empty centered refinement between empty model lists. -/ | nil : CenteredPathRefinement [] []
  /-- Prepend the exact parent and child block with their total-displacement equality and retained refinement tail. -/ |
    cons
      (parent : PreparedEdge curve differential)
      (parentCenter : CenterState parent)
      {parents children : List CellModel}
      (childBlock : List (CenteredChildAt parent parentCenter))
      (displacement_eq :
        Basic.PathModel.displacementSum
            (childBlock.map CenteredChildAt.model) =
          (parent.centeredModel parentCenter).displacement)
      (remaining : CenteredPathRefinement
        (curve := curve) (differential := differential) parents children) :
      CenteredPathRefinement
        (parent.centeredModel parentCenter :: parents)
        (childBlock.map CenteredChildAt.model ++ children)

constructive_injectivity CenteredPathRefinement

namespace CenteredPathRefinement

open Purelib.Integration.Polynomial.Gaussian.Path in
set_option backward.match.sparseCases false in
/-- Convert the retained centered refinement to compatible constant-path refinement using each exact child-block
certificate. -/
def toCompatible {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus} :
    forall {parents children : List CellModel},
      CenteredPathRefinement
          (curve := curve) (differential := differential) parents children ->
        Basic.PathModel.CompatibleConstantPathRefinement
          parents children
  | [], [], .nil => .nil
  | _, _, .cons parent parentCenter childBlock displacement_eq remaining =>
      .cons
        (CenteredChildAt.partitionCertificate childBlock displacement_eq)
        (toCompatible remaining)

end CenteredPathRefinement

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Polynomial
/-- Certify the actual coefficient reading against the original base-reading constant model at the exact local fraction.
-/
def observation {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Basic.LocalObservation
      prepared.model.polynomial prepared.model.localAllowance where
  parameter := fraction
  integrandReading := prepared.reading fraction inside
  error := prepared.reading fraction inside - prepared.baseReading
  decomposition := by
    change prepared.reading fraction inside -
        Ascending.Gaussian.Evaluation.eval
          (Ascending.Gaussian.Basic.constant prepared.baseReading)
            ⟨fraction, 0⟩ =
      prepared.reading fraction inside - prepared.baseReading
    rw [Ascending.Gaussian.Evaluation.eval_constant]
  error_le := by
    have scalar := prepared.reading_difference_le fraction inside
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans
      (by
        change prepared.modelErrorAllowance <=
          4 * prepared.modelErrorAllowance
        simpa only [Fraction.Field.one_mul] using
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            (show (1 : Coordinate) <= 4 by decide)
            prepared.modelErrorAllowance_positive.le)

/-- Certify the actual coefficient reading against the retained center's constant model at the exact local fraction. -/
def centeredObservation {genus : Nat}
    {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Basic.Differential genus}
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared) (fraction : Coordinate)
    (inside : (0 : Coordinate) <= fraction ∧ fraction <= 1) :
    Basic.LocalObservation
      (prepared.centeredModel center).polynomial
      (prepared.centeredModel center).localAllowance where
  parameter := fraction
  integrandReading := prepared.reading fraction inside
  error := prepared.reading fraction inside - center.value
  decomposition := by
    change prepared.reading fraction inside -
        Ascending.Gaussian.Evaluation.eval
          (Ascending.Gaussian.Basic.constant center.value)
            ⟨fraction, 0⟩ =
      prepared.reading fraction inside - center.value
    rw [Ascending.Gaussian.Evaluation.eval_constant]
  error_le := by
    have scalar := center.reading_sub_value_le fraction inside
    rw [Norm.Basic.normSq_eq_canonical] at scalar
    exact scalar.trans
      (by
        change 4 * prepared.modelErrorAllowance <=
          16 * prepared.modelErrorAllowance
        exact
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            four_le_sixteen
              prepared.modelErrorAllowance_positive.le)

end

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Polynomial in
/-- Certify the original constant model uniformly over its exact lifted cleared segment.

Each query retains the original sheet value, refined reading state and witness, local observation, and semantic error
bound paid by four model allowances. -/
def uniformCertificate {genus : Nat} (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (prepared : PreparedEdge curve differential) :
    Curves.Hyperelliptic.Integration.Algebraic.Uniform.Basis.UniformCellCertificate curve differential
      (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
      prepared.model where
  query := by
    intro fraction lower upper
    let inside : (0 : Coordinate) <= fraction ∧ fraction <= 1 :=
      ⟨lower, upper⟩
    let localObservation := prepared.observation fraction inside
    let localSheetValue := prepared.sheetValue fraction inside
    let localCoefficient := prepared.coefficient fraction inside
    let localState := prepared.readingState fraction inside
    let localReading := prepared.reading fraction inside
    let algebraic : Curves.Hyperelliptic.Integration.Algebraic.Observation.Basis.AlgebraicObservation curve differential
        (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
        prepared.model localObservation :=
      { point := prepared.point fraction
        point_eq := by
          apply Basic.ext <;>
            simp only [Cell.Basic.CellModel.observationPoint, localObservation, observation, model,
              Basic.CellModel.displacement,
              point, Geometry.ClearPath.ClearSegment.pointAt,
              Scale.scale_re, Scale.scale_im,
              Basic.add_re,
              Basic.add_im,
              Basic.sub_re,
              Basic.sub_im] <;> ring1
        sheetValue := localSheetValue
        chosenSheet_eq := rfl
        readingState := localState
        readingPossible := prepared.reading_possible fraction inside }
    exact
      { observation := localObservation
        parameter_eq := rfl
        algebraic := algebraic
        semantic_error_le := by
          let ball := localCoefficient.name.process.ball localState
          have radiusSmall : ball.radiusSq < prepared.readingTarget :=
            prepared.reading_radius_lt fraction inside
          have errorBound :
              Data.Gaussian.Norm.Basic.normSq
                  (localReading - prepared.baseReading) <=
                prepared.modelErrorAllowance :=
            prepared.reading_difference_le fraction inside
          change 2 * (4 * ball.radiusSq +
              Data.Gaussian.Norm.Basic.normSq
                (localReading - prepared.baseReading)) <=
            4 * prepared.modelErrorAllowance
          calc
            2 * (4 * ball.radiusSq +
                Data.Gaussian.Norm.Basic.normSq
                  (localReading - prepared.baseReading)) <=
              2 * (4 * prepared.readingTarget +
                prepared.modelErrorAllowance) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add
                  (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                    radiusSmall.le (by decide)) errorBound) (by decide)
            _ = 3 * prepared.modelErrorAllowance := by
              unfold readingTarget
              calc
                2 * (4 * (prepared.modelErrorAllowance / 8) +
                    prepared.modelErrorAllowance) =
                  (prepared.modelErrorAllowance / 8) * 8 +
                    prepared.modelErrorAllowance * 2 := by ring1
                _ = prepared.modelErrorAllowance +
                    prepared.modelErrorAllowance * 2 := by
                  rw [Fraction.Field.div_mul_cancel_of_ne _ 8
                    (by decide)]
                _ = 3 * prepared.modelErrorAllowance := by ring1
            _ <= 4 * prepared.modelErrorAllowance :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
                (by decide) prepared.modelErrorAllowance_positive.le }

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- Certify the retained center's constant model uniformly over the original lifted cleared segment.

Queries retain their actual reading states and sheet values; their semantic errors are paid by the sixteenfold allowance
of this exact centered model. -/
def centeredUniformCertificate {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared) :
    Curves.Hyperelliptic.Integration.Algebraic.Uniform.Basis.UniformCellCertificate curve differential
      (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
      (prepared.centeredModel center) where
  query := by
    intro fraction lower upper
    let inside : (0 : Coordinate) <= fraction ∧ fraction <= 1 :=
      ⟨lower, upper⟩
    let localObservation :=
      prepared.centeredObservation center fraction inside
    let localSheetValue := prepared.sheetValue fraction inside
    let localCoefficient := prepared.coefficient fraction inside
    let localState := prepared.readingState fraction inside
    let localReading := prepared.reading fraction inside
    let algebraic : Curves.Hyperelliptic.Integration.Algebraic.Observation.Basis.AlgebraicObservation curve differential
        (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
        (prepared.centeredModel center) localObservation :=
      { point := prepared.point fraction
        point_eq := by
          change prepared.point fraction =
            prepared.point 0 + Scale.scale fraction
              ((prepared.point 1) - prepared.point 0)
          apply Basic.ext <;>
            simp only [point,
              Geometry.ClearPath.ClearSegment.pointAt,
              Scale.scale_re, Scale.scale_im,
              Basic.add_re,
              Basic.add_im,
              Basic.sub_re,
              Basic.sub_im] <;> ring1
        sheetValue := localSheetValue
        chosenSheet_eq := rfl
        readingState := localState
        readingPossible := prepared.reading_possible fraction inside }
    exact
      { observation := localObservation
        parameter_eq := rfl
        algebraic := algebraic
        semantic_error_le := by
          let ball := localCoefficient.name.process.ball localState
          have radiusSmall : ball.radiusSq < prepared.readingTarget :=
            prepared.reading_radius_lt fraction inside
          have errorBound :
              Data.Gaussian.Norm.Basic.normSq
                  (localReading - center.value) <=
                4 * prepared.modelErrorAllowance :=
            center.reading_sub_value_le fraction inside
          change 2 * (4 * ball.radiusSq +
              Data.Gaussian.Norm.Basic.normSq
                (localReading - center.value)) <=
            16 * prepared.modelErrorAllowance
          calc
            2 * (4 * ball.radiusSq +
                Data.Gaussian.Norm.Basic.normSq
                  (localReading - center.value)) <=
              2 * (4 * prepared.readingTarget +
                4 * prepared.modelErrorAllowance) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add
                  (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                    radiusSmall.le (by decide)) errorBound) (by decide)
            _ = 9 * prepared.modelErrorAllowance := by
              unfold readingTarget
              calc
                2 * (4 * (prepared.modelErrorAllowance / 8) +
                    4 * prepared.modelErrorAllowance) =
                  (prepared.modelErrorAllowance / 8) * 8 +
                    prepared.modelErrorAllowance * 8 := by ring1
                _ = prepared.modelErrorAllowance +
                    prepared.modelErrorAllowance * 8 := by
                  rw [Fraction.Field.div_mul_cancel_of_ne _ 8
                    (by decide)]
                _ = 9 * prepared.modelErrorAllowance := by ring1
            _ <= 16 * prepared.modelErrorAllowance :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
                nine_le_sixteen
                  prepared.modelErrorAllowance_positive.le }

/-- Package the original model's uniform certificate as a valid cell certificate on its retained lifted segment. -/
def validCertificate {genus : Nat} (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (prepared : PreparedEdge curve differential) :
    Curves.Hyperelliptic.Integration.Algebraic.Uniform.Basis.ValidCellCertificate curve differential
      (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
      prepared.model :=
  .uniform (uniformCertificate curve differential prepared)

/-- Package the retained centered model's uniform certificate as its valid cell certificate on the original lifted
segment. -/
def centeredValidCertificate {genus : Nat}
    (curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus)
    (differential : Basic.Differential genus)
    (prepared : PreparedEdge curve differential)
    (center : CenterState prepared) :
    Curves.Hyperelliptic.Integration.Algebraic.Uniform.Basis.ValidCellCertificate curve differential
      (ClearSegment.liftOnSheet prepared.sheet prepared.localSegment)
      (prepared.centeredModel center) :=
  .uniform (centeredUniformCertificate curve differential prepared center)

end PreparedEdge

end Purelib.Riemann.Integration.PreparedConstantModels
