module

public import Purelib.Curves.Legendre.Periods.Jets.Connection.Euler
public import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Rational.Geometric.Search.Selection
import Purelib.Curves.Legendre.PicardFuchs.Clearance.Increment
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # One original-strip request paying the synchronized connection residual

The fixed original parameter clearance computes a positive denominator
floor. Its width-squared payment is valid at every admitted target frame,
including the literal source frame, before any target model is prepared.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Connection

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic

/-- The original exact frame clearance has the exact squared norm of its retained common denominator. -/
private theorem frame_floor_eq {parameter : Canonical} (frame : Paths.Frame parameter) :
    (ParameterClearance.ofFrame frame).connectionLowerSq =
      Norm.Basic.normSq (ParameterClearance.connectionDenominator parameter) := by
  change 4 * Norm.Basic.normSq parameter * Norm.Basic.normSq (parameter - 1) =
    Norm.Basic.normSq (2 * parameter * (1 - parameter))
  have opposite : (1 - parameter : Canonical) = -(parameter - 1) := by ring1
  rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, opposite, Norm.Basic.normSq_neg]
  change 4 * Norm.Basic.normSq parameter * Norm.Basic.normSq (parameter - 1) =
    (2 * 2 + 0 * 0) * Norm.Basic.normSq parameter * Norm.Basic.normSq (parameter - 1)
  ring1

/-- Compute the original positive width-squared connection-residual request from fixed clearance. -/
@[expose] def residualRequest {parameter : Canonical} (clearance : ParameterClearance parameter)
    (width : Rational) (positive : 0 < width) : AccuracyRequest :=
  ⟨width ^ 2 * denominatorFloor clearance,
    mul_pos_direct (pow_pos_direct positive 2) (denominatorFloor_positive clearance)⟩

/-- The request tolerance retains its exact original width-squared and common denominator factor. -/
theorem residualRequest_tolerance {parameter : Canonical} (clearance : ParameterClearance parameter)
    (width : Rational) (positive : 0 < width) :
    (residualRequest clearance width positive).tolerance = width ^ 2 * denominatorFloor clearance := rfl

/-- The fixed request pays every actual retained frame throughout the original admitted parameter ball. -/
theorem residualRequest_le_frame {parameter : Canonical} (clearance : ParameterClearance parameter)
    (width : Rational) (positive : 0 < width) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ clearance.incrementBound)
    (target : Paths.Frame (parameter + increment)) :
    (residualRequest clearance width positive).tolerance ≤
      width ^ 2 * (ParameterClearance.ofFrame target).connectionLowerSq :=
  (residualRequest_tolerance clearance width positive).trans_le
    (mul_le_mul_of_nonneg_left_direct
      ((denominatorFloor_le clearance increment admitted).trans_eq (frame_floor_eq target).symm)
      (sq_nonneg_direct width))

/-- The same fixed request pays the literal original frame without replacing it by a zero-offset frame. -/
theorem residualRequest_le_source {parameter : Canonical} (frame : Paths.Frame parameter)
    (width : Rational) (positive : 0 < width) :
    (residualRequest (ParameterClearance.ofFrame frame) width positive).tolerance ≤
      width ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq := by
  let clearance := ParameterClearance.ofFrame frame
  have zero : Norm.Basic.normSq (0 : Canonical) ≤ clearance.incrementBound :=
    Norm.Basic.normSq_zero.trans_le clearance.incrementBound_positive.le
  have same : Norm.Basic.normSq (ParameterClearance.connectionDenominator (parameter + 0)) =
      Norm.Basic.normSq (ParameterClearance.connectionDenominator parameter) :=
    congrArg (fun value => Norm.Basic.normSq (ParameterClearance.connectionDenominator value))
      (Data.Gaussian.Basic.add_zero parameter)
  have floor := ((denominatorFloor_le clearance 0 zero).trans_eq same).trans_eq (frame_floor_eq frame).symm
  exact (residualRequest_tolerance clearance width positive).trans_le
    (mul_le_mul_of_nonneg_left_direct floor (sq_nonneg_direct width))

/-- An already paid sample stage is the exact stage of its original same-frame connection Selection factory. -/
theorem connectionSelection_stage_eq_of_accurate {parameter : Canonical} (frame : Paths.Frame parameter)
    (width : Rational) (positive : 0 < width) (index : Nat)
    (accurate : Geometric.Basic.quarterRadius 1 index <
      width ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq) :
    (connectionSelection frame width positive index).stage = index :=
  (congrArg (fun selection : Geometric.Search.Selection 1 index
      (width ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq) => selection.stage)
    (connectionSelection_eq frame width positive index)).trans
      (Geometric.Search.Selection.build_stage_eq_of_accurate 1 (by decide)
        index _ (mul_pos_direct (pow_pos_direct positive 2)
          (ParameterClearance.ofFrame frame).connectionLowerSq_positive) accurate)

end Purelib.Curves.Legendre.Periods.Jets.Connection

end
