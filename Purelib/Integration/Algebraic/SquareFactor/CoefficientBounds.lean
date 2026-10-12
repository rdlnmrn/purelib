module
public import Purelib.Approximation.Rational.Budget.Quotient
import Purelib.Approximation.Rational.SquareRoot.Radius.Scaled
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Quotient
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Algebraic.SquareFactor.PathInput
public import Purelib.Riemann.Branches.SquareRootSheets
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.SquareFactor.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Bounds.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Finite local error bounds for square-factor differential transport

The cancelled coefficient is `N(x)/(D(x)z)`.  Polynomial value/variation
bounds come from the retained path data.  The radicand clearance generates
a uniform root-denominator floor for finite residual-certified readings.
Root movement remains explicit here: the continuation layer must obtain it
from the same retained owner, not from unrelated roots of the same equation.
-/

namespace Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds

open Purelib.Curves.Hyperelliptic.Differentials.SquareFactor
open Purelib.Integration.Algebraic.SquareFactor.PathInput
open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Data.Rat in
/-- The rational carrier for coefficient, parameter and root bounds. -/
abbrev Coordinate := Fraction.Rational

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
/-- Successive division by two nonzero Gaussian values equals division by their product. -/
private theorem nested_div (numerator denominator root : SquareFactor.Gaussian)
    (denominatorNonzero : denominator ≠ 0) (rootNonzero : root ≠ 0) :
    numerator / denominator / root = numerator / (denominator * root) := by
  have productNonzero := Field.mul_ne_zero_direct
    denominatorNonzero rootNonzero
  apply Field.mul_right_cancel_of_ne productNonzero
  calc
    numerator / denominator / root * (denominator * root) =
        (numerator / denominator / root * root) * denominator := by ring1
    _ = numerator := by
      rw [Field.ExplicitField.div_mul_cancel _ rootNonzero,
        Field.ExplicitField.div_mul_cancel _ denominatorNonzero]
    _ = numerator / (denominator * root) * (denominator * root) :=
      (Field.ExplicitField.div_mul_cancel _ productNonzero).symm

variable {polynomial : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.GaussianPolynomial} {request :
  Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Request}
  {prepared : Purelib.Curves.Hyperelliptic.Differentials.SquareFactor.Prepared polynomial request} {segment :
    Purelib.Integration.Algebraic.SquareFactor.PathInput.Segment}

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Integration.Algebraic.SquareFactor
/-- Evaluate the retained numerator divided by denominator and the supplied root at the original segment parameter. -/
@[expose] def coefficient (data : PathInput.Data prepared segment) (parameter : Coordinate) (root :
  SquareFactor.Gaussian) :
    Gaussian := data.numerator.value parameter / data.denominator.value parameter / root

/-- The cached path-bound coefficient equals the prepared differential's coefficient at the same original point and
root. -/
theorem coefficient_eq (data : PathInput.Data prepared segment) (parameter : Coordinate) (root :
  SquareFactor.Gaussian) :
    coefficient data parameter root = prepared.weight.coefficient (segment.point parameter) root := by
  rw [coefficient, data.numerator.value_eq, data.denominator.value_eq]
  rfl

end

open Purelib.Integration.Algebraic.SquareFactor in
/-- Read the retained path data's cached root squared-norm floor. -/
@[expose] def rootLower (data : PathInput.Data prepared segment) : Coordinate :=
  data.rootNormFloor

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Safe path data has a strictly positive retained root norm floor.

The minimum baseline is strictly positive and bounds the retained nested maximum from below. -/
theorem rootLower_positive {data : PathInput.Data prepared segment} (safe : data.Safe) :
    0 < rootLower data := by
  rw [rootLower, data.rootNormFloor_eq]
  exact ((Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct safe.radicandPositive (by decide))).trans_le
      (Fraction.Order.Basic.le_max_left _ _)).trans_le (Fraction.Order.Basic.le_max_left _ _)

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- The retained root norm floor bounds every in-range root sample satisfying the original square-residual target.

The proof combines the baseline, scaled-radius and coordinate lower estimates stored in the exact radicand bounds. -/
theorem rootLower_le {data : PathInput.Data prepared segment} (safe : data.Safe)
    {parameter : Coordinate} (inside : PathInput.unitInterval.Contains parameter) {root :
      SquareFactor.Gaussian}
    (residual : Data.Gaussian.Norm.Basic.normSq (root * root - prepared.reduction.radicand.eval (segment.point
      parameter)) ≤
      SquareRootSheets.residualTarget (prepared.reduction.radicand.eval (segment.point parameter))) :
    rootLower data ≤ Data.Gaussian.Norm.Basic.normSq root := by
  have positive : 0 < data.radicand.lowerBound := by
    -- The cached floor is only consumed on a certified root-safe path.
    exact safe.radicandPositive
  have radicandLower := data.radicand.lowerBound_le inside
  rw [Norm.Basic.normSq_eq_canonical] at radicandLower
  have coordinateSquare := SquareRootSheets.normSq_le_two_coordinateNormLower_sq
    (prepared.reduction.radicand.eval (segment.point parameter))
  rw [← Norm.Basic.normSq_eq_canonical] at coordinateSquare
  have canonicalResidual := residual
  rw [Norm.Basic.normSq_eq_canonical] at canonicalResidual
  have rootSample := SquareRootSheets.normSq_lower_of_square_residual canonicalResidual
  rw [← Norm.Basic.normSq_eq_canonical] at rootSample
  have quarterLe : data.radicand.lowerBound / 4 ≤
      SquareRootSheets.residualTarget (prepared.reduction.radicand.eval (segment.point parameter)) := by
    unfold SquareRootSheets.residualTarget
    simp only [Field.ExplicitField.div_eq_mul_inv]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      radicandLower (by decide)
  have baseline : min 1 (data.radicand.lowerBound / 4) ≤
      SquareRootSheets.sampleNormLower (prepared.reduction.radicand.eval (segment.point parameter)) :=
    (Fraction.Order.Basic.min_le_min (le_rfl : (1 : Coordinate) ≤ 1) quarterLe).trans
      (Fraction.Order.Basic.le_max_left _ _)
  have coordinateBound : SquareRoot.Radius.Scaled.radius (data.radicand.lowerBound / 2) ≤
      SquareRootSheets.coordinateNormLower (prepared.reduction.radicand.eval (segment.point parameter)) := by
    apply Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
      ((Fraction.Order.Arithmetic.abs_nonneg_direct _).trans (Fraction.Order.Basic.le_max_left _ _))
    apply (SquareRoot.Radius.Scaled.sq_lt
      (Fraction.Order.Field.div_pos_direct positive (by decide))).le.trans
    apply (Fraction.Order.Field.div_le_iff_pos (show (0 : Coordinate) < 2 by decide)).2
    calc
      data.radicand.lowerBound ≤
          Data.Gaussian.Norm.Basic.normSq (prepared.reduction.radicand.eval (segment.point parameter)) :=
            data.radicand.lowerBound_le inside
      _ ≤ 2 * SquareRootSheets.coordinateNormLower
          (prepared.reduction.radicand.eval (segment.point parameter)) ^ 2 :=
        coordinateSquare
      _ = _ := Fraction.Field.mul_comm _ _
  have scaled : SquareRoot.Radius.Scaled.radius (data.radicand.lowerBound / 2) / 2 ≤
      SquareRootSheets.sampleNormLower (prepared.reduction.radicand.eval (segment.point parameter)) := by
    apply (show SquareRoot.Radius.Scaled.radius (data.radicand.lowerBound / 2) / 2 ≤
      SquareRootSheets.coordinateNormLower (prepared.reduction.radicand.eval (segment.point parameter)) / 2 from
        ?_).trans
      (Fraction.Order.Basic.le_max_right _ _)
    simp only [Field.ExplicitField.div_eq_mul_inv]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coordinateBound (by decide)
  have intervalCoordinate : data.radicand.coordinateLower ≤
      SquareRootSheets.coordinateNormLower (prepared.reduction.radicand.eval (segment.point parameter)) :=
    data.radicand.coordinateLower_le inside
  have intervalSample : data.radicand.coordinateLower / 2 ≤
      SquareRootSheets.sampleNormLower (prepared.reduction.radicand.eval (segment.point parameter)) := by
    apply (show data.radicand.coordinateLower / 2 ≤
      SquareRootSheets.coordinateNormLower (prepared.reduction.radicand.eval (segment.point parameter)) / 2 from
        ?_).trans
      (Fraction.Order.Basic.le_max_right _ _)
    simp only [Field.ExplicitField.div_eq_mul_inv]
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct intervalCoordinate (by decide)
  rw [rootLower, data.rootNormFloor_eq]
  exact (Fraction.Order.Basic.max_le (Fraction.Order.Basic.max_le baseline scaled) intervalSample).trans
    rootSample

open Purelib.Integration.Algebraic.SquareFactor in
/-- The generated root squared-norm upper bound, one plus four times the retained radicand value bound. -/
@[expose] def rootUpper (data : PathInput.Data prepared segment) : Coordinate :=
  1 + 4 * data.radicand.valueBound

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The generated root upper bound is nonnegative. -/
theorem rootUpper_nonnegative (data : PathInput.Data prepared segment) : 0 ≤ rootUpper data :=
  add_nonneg (by decide)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) data.radicand.valueBound_nonnegative)

open Purelib.Algebra in
open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- An in-range root sample satisfying the original residual target obeys the generated root upper bound. -/
theorem normSq_root_le {data : PathInput.Data prepared segment}
    {parameter : Coordinate} (inside : PathInput.unitInterval.Contains parameter) {root :
      SquareFactor.Gaussian}
    (residual : Data.Gaussian.Norm.Basic.normSq (root * root - prepared.reduction.radicand.eval (segment.point
      parameter)) ≤
      SquareRootSheets.residualTarget (prepared.reduction.radicand.eval (segment.point parameter))) :
    Data.Gaussian.Norm.Basic.normSq root ≤ rootUpper data := by
  let radicand := prepared.reduction.radicand.eval (segment.point parameter)
  have radicandBound : Data.Gaussian.Norm.Basic.normSq radicand ≤ data.radicand.valueBound := by
    dsimp only [radicand, PathInput.Segment.point]
    rw [← data.radicand.value_eq]
    exact data.radicand.normSq_value_le inside
  have targetBound : SquareRootSheets.residualTarget radicand ≤ Data.Gaussian.Norm.Basic.normSq radicand := by
    unfold SquareRootSheets.residualTarget
    rw [← Norm.Basic.normSq_eq_canonical]
    rw [Field.ExplicitField.div_eq_mul_inv]
    calc
      Data.Gaussian.Norm.Basic.normSq radicand * (4 : Coordinate)⁻¹ ≤ Data.Gaussian.Norm.Basic.normSq
        radicand *
        1 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide) (Norm.Basic.normSq_nonneg _)
      _ = Data.Gaussian.Norm.Basic.normSq radicand := Fraction.Field.mul_one_direct _
  have identity : root * root = (root * root - radicand) + radicand := by ring1
  have squareBound : Data.Gaussian.Norm.Basic.normSq root * Data.Gaussian.Norm.Basic.normSq root ≤ 4 *
    data.radicand.valueBound :=
    by
    rw [← Norm.Basic.normSq_mul, identity]
    calc
      Data.Gaussian.Norm.Basic.normSq _ ≤ _ := Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * (data.radicand.valueBound + data.radicand.valueBound) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add ((residual.trans targetBound).trans radicandBound) radicandBound) (by decide)
      _ = _ := by ring1
  by_cases small : Data.Gaussian.Norm.Basic.normSq root ≤ 1
  · exact small.trans (le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) data.radicand.valueBound_nonnegative))
  · have oneLe : (1 : Coordinate) ≤ Data.Gaussian.Norm.Basic.normSq root := le_of_not_ge small
    have normLeSquare : Data.Gaussian.Norm.Basic.normSq root ≤ Data.Gaussian.Norm.Basic.normSq root *
      Data.Gaussian.Norm.Basic.normSq
      root := by
      calc
        Data.Gaussian.Norm.Basic.normSq root = 1 * Data.Gaussian.Norm.Basic.normSq root := (_root_.one_mul _).symm
        _ ≤ _ := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct oneLe (Norm.Basic.normSq_nonneg _)
    exact (normLeSquare.trans squareBound).trans (le_add_of_nonneg_left (by decide))

open Purelib.Integration.Algebraic.SquareFactor in
/-- Combine parameter and root movement bounds for the retained denominator-times-root product.

The original denominator slope and value bounds weight the two movements separately before their sum is doubled. -/
@[expose] def denominatorMovement (data : PathInput.Data prepared segment)
    (rootBound parameterMovement rootMovement : Coordinate) : Coordinate :=
  2 * (data.denominator.slopeBound * parameterMovement * rootBound +
    data.denominator.valueBound * rootMovement)

open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Nonnegative root, parameter and root-movement bounds give a nonnegative combined denominator movement allowance. -/
theorem denominatorMovement_nonnegative (data : PathInput.Data prepared segment)
    {rootBound parameterMovement rootMovement : Coordinate}
    (rootNonnegative : 0 ≤ rootBound) (parameterNonnegative : 0 ≤ parameterMovement)
    (movementNonnegative : 0 ≤ rootMovement) :
    0 ≤ denominatorMovement data rootBound parameterMovement rootMovement :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.mul_nonneg_direct data.denominator.slopeBound_nonnegative
          parameterNonnegative) rootNonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct data.denominator.valueBound_nonnegative
        movementNonnegative))

open Purelib.Approximation.Rational in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The retained quotient-variation bound for the numerator divided by denominator times root.

It keeps the original numerator bounds, product denominator floor, parameter movement and separate root movement
contribution. -/
@[expose] def variation (data : PathInput.Data prepared segment)
    (rootBound parameterMovement rootMovement : Coordinate) : Coordinate :=
  Budget.Quotient.quotientBound
    data.numerator.slopeBound data.numerator.valueBound
    (data.denominator.valueBound * rootBound)
    (data.denominator.lowerBound * rootLower data)
    parameterMovement (denominatorMovement data rootBound parameterMovement rootMovement)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- Safe retained margins and nonnegative movement inputs make the quotient-variation allowance nonnegative. -/
theorem variation_nonnegative {data : PathInput.Data prepared segment} (safe : data.Safe)
    {rootBound parameterMovement rootMovement : Coordinate}
    (rootNonnegative : 0 ≤ rootBound) (parameterNonnegative : 0 ≤ parameterMovement)
    (movementNonnegative : 0 ≤ rootMovement) :
    0 ≤ variation data rootBound parameterMovement rootMovement :=
  Budget.Quotient.ApproximationQuotientVariation.quotientBound_nonnegative
    data.numerator.slopeBound_nonnegative data.numerator.valueBound_nonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct data.denominator.valueBound_nonnegative
      rootNonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct safe.denominatorPositive.le
      (rootLower_positive safe).le)
    parameterNonnegative
    (denominatorMovement_nonnegative data rootNonnegative parameterNonnegative movementNonnegative)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
/-- The denominator-times-root difference obeys the retained combined movement bound.

Both parameters stay in the original interval; the estimate uses the left root size and the directed right-minus-left
root movement. -/
theorem normSq_denominator_sub_le (data : PathInput.Data prepared segment)
    {left right : Coordinate} (leftInside : PathInput.unitInterval.Contains left)
    (rightInside : PathInput.unitInterval.Contains right)
    {leftRoot rightRoot : SquareFactor.Gaussian} {rootBound parameterMovement rootMovement :
      Coordinate}
    (parameterBound : (left - right) ^ 2 ≤ parameterMovement)
    (leftRootBound : Data.Gaussian.Norm.Basic.normSq leftRoot ≤ rootBound)
    (rootDifference : Data.Gaussian.Norm.Basic.normSq (rightRoot - leftRoot) ≤ rootMovement) :
    Data.Gaussian.Norm.Basic.normSq (data.denominator.value right * rightRoot - data.denominator.value left * leftRoot)
      ≤
      denominatorMovement data rootBound parameterMovement rootMovement := by
  have movementNonnegative := (Fraction.Order.Arithmetic.sq_nonneg_direct (left - right)).trans
    parameterBound
  have difference : Data.Gaussian.Norm.Basic.normSq (data.denominator.value right - data.denominator.value left) ≤
      data.denominator.slopeBound * parameterMovement := by
    have reverse : (right - left) ^ 2 = (left - right) ^ 2 := by ring1
    have bound := data.denominator.normSq_value_sub_le rightInside leftInside
    rw [reverse] at bound
    exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      parameterBound data.denominator.slopeBound_nonnegative)
  have identity : data.denominator.value right * rightRoot -
      data.denominator.value left * leftRoot =
      (data.denominator.value right - data.denominator.value left) * leftRoot +
        data.denominator.value right * (rightRoot - leftRoot) := by ring1
  rw [identity]
  calc
    Data.Gaussian.Norm.Basic.normSq _ ≤ _ := Norm.Bounds.normSq_add_le_two _ _
    _ = 2 * (Data.Gaussian.Norm.Basic.normSq (data.denominator.value right - data.denominator.value left) *
      Data.Gaussian.Norm.Basic.normSq leftRoot +
        Data.Gaussian.Norm.Basic.normSq (data.denominator.value right) * Data.Gaussian.Norm.Basic.normSq (rightRoot -
          leftRoot))
          := by
      rw [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul]
    _ ≤ denominatorMovement data rootBound parameterMovement rootMovement := by
      apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by decide)
      exact add_le_add
        (Fraction.Order.Arithmetic.mul_le_mul_direct difference leftRootBound
          (Norm.Basic.normSq_nonneg leftRoot)
          (Fraction.Order.Arithmetic.mul_nonneg_direct data.denominator.slopeBound_nonnegative
            movementNonnegative))
        (Fraction.Order.Arithmetic.mul_le_mul_direct
          (data.denominator.normSq_value_le rightInside) rootDifference
          (Norm.Basic.normSq_nonneg (rightRoot - leftRoot)) data.denominator.valueBound_nonnegative)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- Two residual-certified root samples with retained size and movement bounds obey the coefficient variation estimate.

The exact original segment, positive denominator and radicand margins, and both root residual targets remain part of the
comparison. -/
theorem normSq_coefficient_sub_le {data : PathInput.Data prepared segment} (safe : data.Safe)
    {left right : Coordinate} (leftInside : PathInput.unitInterval.Contains left)
    (rightInside : PathInput.unitInterval.Contains right)
    {leftRoot rightRoot : SquareFactor.Gaussian} {rootBound parameterMovement rootMovement :
      Coordinate}
    (parameterBound : (left - right) ^ 2 ≤ parameterMovement)
    (leftRootBound : Data.Gaussian.Norm.Basic.normSq leftRoot ≤ rootBound) (rightRootBound :
      Data.Gaussian.Norm.Basic.normSq
      rightRoot ≤ rootBound)
    (rootDifference : Data.Gaussian.Norm.Basic.normSq (rightRoot - leftRoot) ≤ rootMovement)
    (leftResidual : Data.Gaussian.Norm.Basic.normSq (leftRoot * leftRoot -
        prepared.reduction.radicand.eval (segment.point left)) ≤
      SquareRootSheets.residualTarget (prepared.reduction.radicand.eval (segment.point left)))
    (rightResidual : Data.Gaussian.Norm.Basic.normSq (rightRoot * rightRoot -
        prepared.reduction.radicand.eval (segment.point right)) ≤
      SquareRootSheets.residualTarget (prepared.reduction.radicand.eval (segment.point right))) :
    Data.Gaussian.Norm.Basic.normSq (coefficient data left leftRoot - coefficient
      data
      right rightRoot) ≤
      variation data rootBound parameterMovement rootMovement := by
  have leftLower := rootLower_le safe leftInside leftResidual
  have rightLower := rootLower_le safe rightInside rightResidual
  have rootNonzero {root : SquareFactor.Gaussian} (lower : rootLower data ≤
    Data.Gaussian.Norm.Basic.normSq
    root) : root ≠ 0 := by
    intro zero
    have positive := (rootLower_positive safe).trans_le lower
    rw [zero, Norm.Basic.normSq_zero] at positive
    exact (lt_irrefl _ positive).elim
  have denominatorNonzero {parameter : Coordinate} (inside : PathInput.unitInterval.Contains
    parameter) :
      data.denominator.value parameter ≠ 0 := by
    rw [data.denominator.value_eq]
    exact safe.denominator_nonzero inside
  rw [coefficient, coefficient, nested_div _ _ _
    (denominatorNonzero leftInside) (rootNonzero leftLower),
    nested_div _ _ _ (denominatorNonzero rightInside) (rootNonzero rightLower)]
  apply Norm.Quotient.ApproximationQuotientVariation.normSq_div_sub_div_le
    (Fraction.Order.Arithmetic.mul_pos_direct safe.denominatorPositive (rootLower_positive safe))
  · exact (data.numerator.normSq_value_sub_le leftInside rightInside).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        parameterBound data.numerator.slopeBound_nonnegative)
  · exact data.numerator.normSq_value_le rightInside
  · rw [Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct (data.denominator.normSq_value_le rightInside)
      rightRootBound (Norm.Basic.normSq_nonneg rightRoot) data.denominator.valueBound_nonnegative
  · exact normSq_denominator_sub_le data leftInside rightInside parameterBound leftRootBound
      rootDifference
  · rw [Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct (data.denominator.lowerBound_le_value leftInside)
      leftLower (rootLower_positive safe).le (Norm.Basic.normSq_nonneg (data.denominator.value left))
  · rw [Norm.Basic.normSq_mul]
    exact Fraction.Order.Arithmetic.mul_le_mul_direct (data.denominator.lowerBound_le_value rightInside)
      rightLower (rootLower_positive safe).le (Norm.Basic.normSq_nonneg (data.denominator.value
        right))

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data.Gaussian in
open Purelib.Integration.Algebraic.SquareFactor in
open Purelib.Riemann.Branches in
/-- The coefficient variation estimate uses the generated root upper bound for both residual-certified root samples. -/
theorem normSq_coefficient_sub_le_generated {data : PathInput.Data prepared segment} (safe : data.Safe)
    {left right : Coordinate} (leftInside : PathInput.unitInterval.Contains left)
    (rightInside : PathInput.unitInterval.Contains right)
    {leftRoot rightRoot : SquareFactor.Gaussian} {parameterMovement rootMovement : Coordinate}
    (parameterBound : (left - right) ^ 2 ≤ parameterMovement)
    (rootDifference : Data.Gaussian.Norm.Basic.normSq (rightRoot - leftRoot) ≤ rootMovement)
    (leftResidual : Data.Gaussian.Norm.Basic.normSq (leftRoot * leftRoot -
        prepared.reduction.radicand.eval (segment.point left)) ≤
      SquareRootSheets.residualTarget (prepared.reduction.radicand.eval (segment.point left)))
    (rightResidual : Data.Gaussian.Norm.Basic.normSq (rightRoot * rightRoot -
        prepared.reduction.radicand.eval (segment.point right)) ≤
      SquareRootSheets.residualTarget (prepared.reduction.radicand.eval (segment.point right))) :
    Data.Gaussian.Norm.Basic.normSq (coefficient data left leftRoot - coefficient
      data
      right rightRoot) ≤
      variation data (rootUpper data) parameterMovement rootMovement :=
  normSq_coefficient_sub_le safe leftInside rightInside parameterBound
    (normSq_root_le leftInside leftResidual) (normSq_root_le rightInside
      rightResidual)
    rootDifference leftResidual rightResidual

section
open Purelib.Integration.Algebraic.SquareFactor
/-- The rational coefficient multiplying parameter movement in the generated-root variation formula. -/
@[expose] def parameterSlope (data : PathInput.Data prepared segment) : Coordinate :=
  (2 * (data.numerator.slopeBound * data.denominator.valueBound * rootUpper data +
    2 * data.numerator.valueBound * data.denominator.slopeBound * rootUpper data)) /
      ((data.denominator.lowerBound * rootLower data) *
        (data.denominator.lowerBound * rootLower data))

/-- The rational coefficient multiplying root movement in the generated-root variation formula. -/
@[expose] def rootSlope (data : PathInput.Data prepared segment) : Coordinate :=
  (4 * data.numerator.valueBound * data.denominator.valueBound) /
    ((data.denominator.lowerBound * rootLower data) *
      (data.denominator.lowerBound * rootLower data))

end

open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Integration.Algebraic.SquareFactor in
/-- With the generated root upper bound, variation is the sum of parameter-slope and root-slope movement terms. -/
theorem variation_eq_linear (data : PathInput.Data prepared segment) (parameterMovement rootMovement :
  Coordinate) :
    variation data (rootUpper data) parameterMovement rootMovement =
      parameterSlope data * parameterMovement + rootSlope data * rootMovement := by
  unfold variation Budget.Quotient.quotientBound denominatorMovement
    parameterSlope rootSlope
  simp only [Field.ExplicitField.div_eq_mul_inv]
  ring1

open Purelib.Data.Rat
open Purelib.Integration.Algebraic.SquareFactor
/-- Safe retained path data makes the parameter-movement coefficient nonnegative. -/
theorem parameterSlope_nonnegative {data : PathInput.Data prepared segment} (safe : data.Safe) :
    0 ≤ parameterSlope data := by
  have bound := variation_nonnegative safe (rootUpper_nonnegative data)
    (show (0 : Coordinate) ≤ 1 by decide) (show (0 : Coordinate) ≤ 0 from le_rfl)
  simpa only [variation_eq_linear, Fraction.Field.mul_one_direct,
    Fraction.Field.mul_zero_direct, _root_.add_zero] using bound

/-- Safe retained path data makes the root-movement coefficient nonnegative. -/
theorem rootSlope_nonnegative {data : PathInput.Data prepared segment} (safe : data.Safe) :
    0 ≤ rootSlope data := by
  have bound := variation_nonnegative safe (rootUpper_nonnegative data)
    (show (0 : Coordinate) ≤ 0 from le_rfl) (show (0 : Coordinate) ≤ 1 by decide)
  simpa only [variation_eq_linear, Fraction.Field.mul_zero_direct,
    Fraction.Field.mul_one_direct, _root_.zero_add] using bound

end Purelib.Integration.Algebraic.SquareFactor.CoefficientBounds
