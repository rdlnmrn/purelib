module

public import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.Polynomial.Dense.Gaussian.Bounds.Path.Majorant
import Purelib.Geometry.Rational.Box.Intervals
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Uniform contour floors for the original direct quadratic transport

The source owner and its four original ambient-line certificates determine
four fixed finite Horner majorants. A common movement ceiling below those
same line clearances gives a positive floor for every actual transported
contour, including the unchanged owner in the equal-parameter branch.
-/

public section

namespace Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Bounds.Path
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.Power.Clearance.Box

variable {source target : Canonical}

/-- The exact fixed source-polynomial Horner majorant of the retained left ambient line. -/
private def leftMajorant (owner : Owner source) : Fraction.Rational :=
  Majorant.boundarySideMajorant (rootPolynomial source)
    (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xLower) Gaussian.Constants.imaginaryUnit
    (Box.Intervals.verticalInterval owner.ambient)

/-- The exact fixed source-polynomial majorant of the original right ambient line. -/
private def rightMajorant (owner : Owner source) : Fraction.Rational :=
  Majorant.boundarySideMajorant (rootPolynomial source)
    (Gaussian.Cast.Winding.verticalBase owner.track.initial.box.xUpper) Gaussian.Constants.imaginaryUnit
    (Box.Intervals.verticalInterval owner.ambient)

/-- The exact fixed source-polynomial majorant of the original bottom ambient line. -/
private def bottomMajorant (owner : Owner source) : Fraction.Rational :=
  Majorant.boundarySideMajorant (rootPolynomial source)
    (Gaussian.Cast.Imaginary.horizontalBase owner.track.initial.box.yLower) Gaussian.Constants.horizontalDirection
    (Box.Intervals.horizontalInterval owner.ambient)

/-- The exact fixed source-polynomial majorant of the original top ambient line. -/
private def topMajorant (owner : Owner source) : Fraction.Rational :=
  Majorant.boundarySideMajorant (rootPolynomial source)
    (Gaussian.Cast.Imaginary.horizontalBase owner.track.initial.box.yUpper) Gaussian.Constants.horizontalDirection
    (Box.Intervals.horizontalInterval owner.ambient)

/-- Each retained boundary-side majorant is positive because its original scalar maximum has floor one. -/
private theorem majorant_positive (polynomial : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (origin direction : Canonical) (interval : Data.Rat.Interval.Bounds) :
    0 < Majorant.boundarySideMajorant polynomial origin direction interval := by
  unfold Majorant.boundarySideMajorant
  exact (show (0 : Fraction.Rational) < 1 by decide +kernel).trans_le (Fraction.Order.Basic.le_max_left _ _)

/-- The source line margin and its exact fixed majorant determine a scalar transported-clearance floor. -/
private def sideFloor (clearance majorant ceiling : Fraction.Rational) : Fraction.Rational :=
  (clearance - ceiling) ^ 2 / (4 * majorant)

/-- A strict original line margin and positive majorant make the computed side floor positive. -/
private theorem sideFloor_positive {clearance majorant ceiling : Fraction.Rational}
    (small : ceiling < clearance) (positive : 0 < majorant) : 0 < sideFloor clearance majorant ceiling :=
  Fraction.Order.Field.div_pos_direct
    (Arithmetic.pow_pos_direct (Arithmetic.sub_pos_direct small) 2)
    (Arithmetic.mul_pos_direct (by decide +kernel) positive)

/-- Decreasing the actual movement from a retained common ceiling only increases this original side clearance. -/
private theorem sideFloor_le {clearance majorant ceiling actual : Fraction.Rational}
    (small : ceiling < clearance) (paid : actual ≤ ceiling) (positive : 0 < majorant) :
    sideFloor clearance majorant ceiling ≤ sideFloor clearance majorant actual := by
  unfold sideFloor
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  exact Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.pow_le_pow_direct (Arithmetic.sub_pos_direct small).le
      (Arithmetic.sub_le_sub_left_direct paid clearance) 2)
    (Fraction.Order.Field.inv_pos_direct
      (Arithmetic.mul_pos_direct (by decide +kernel) positive)).le

/-- The unchanged contour and four computed original-side floors bound every permitted direct transport.

The minimum includes the original contour for the equal-parameter branch.
All four side majorants concern the same retained source polynomial,
ambient box and original line coordinates; no target owner is constructed.
-/
def transportFloor (owner : Owner source) (ceiling : Fraction.Rational) : Fraction.Rational :=
  min owner.track.initial.clearance.bound
    (min (sideFloor owner.track.initial.ambientLeftClearance.bound (leftMajorant owner) ceiling)
      (min (sideFloor owner.track.initial.ambientRightClearance.bound (rightMajorant owner) ceiling)
        (min (sideFloor owner.track.initial.ambientBottomClearance.bound (bottomMajorant owner) ceiling)
          (sideFloor owner.track.initial.ambientTopClearance.bound (topMajorant owner) ceiling))))

/-- The four original strict ambient-line payments make the uniform direct-transport floor positive. -/
theorem transportFloor_positive (owner : Owner source) (ceiling : Fraction.Rational)
    (left : ceiling < owner.track.initial.ambientLeftClearance.bound)
    (right : ceiling < owner.track.initial.ambientRightClearance.bound)
    (bottom : ceiling < owner.track.initial.ambientBottomClearance.bound)
    (top : ceiling < owner.track.initial.ambientTopClearance.bound) :
    0 < transportFloor owner ceiling := by
  have leftPositive : 0 < leftMajorant owner := majorant_positive _ _ _ _
  have rightPositive : 0 < rightMajorant owner := majorant_positive _ _ _ _
  have bottomPositive : 0 < bottomMajorant owner := majorant_positive _ _ _ _
  have topPositive : 0 < topMajorant owner := majorant_positive _ _ _ _
  unfold transportFloor
  exact Fraction.Order.Basic.lt_min owner.track.initial.clearance.positive
    (Fraction.Order.Basic.lt_min (sideFloor_positive left leftPositive)
      (Fraction.Order.Basic.lt_min (sideFloor_positive right rightPositive)
        (Fraction.Order.Basic.lt_min (sideFloor_positive bottom bottomPositive)
          (sideFloor_positive top topPositive))))

/-- The actual original direct transport retains the computed common contour floor at every paid movement.

Equality of source and target retains the original owner. Otherwise the
original ambient Rouché cache supplies the actual selected contour as the
minimum of its four original transported line clearances. The retained
movement ceiling bounds each of those exact clearances from below.
-/
theorem directTransport_clearance_lower (owner : Owner source) (targetNonzero : target ≠ 0)
    (small : Norm.Basic.normSq (source - target) < owner.track.initial.clearance.bound)
    (ceiling : Fraction.Rational)
    (left : ceiling < owner.track.initial.ambientLeftClearance.bound)
    (right : ceiling < owner.track.initial.ambientRightClearance.bound)
    (bottom : ceiling < owner.track.initial.ambientBottomClearance.bound)
    (top : ceiling < owner.track.initial.ambientTopClearance.bound)
    (paid : Norm.Basic.normSq (source - target) ≤ ceiling) :
    transportFloor owner ceiling ≤ (directTransport owner targetNonzero small).track.initial.clearance.bound := by
  have leftPositive : 0 < leftMajorant owner := majorant_positive _ _ _ _
  have rightPositive : 0 < rightMajorant owner := majorant_positive _ _ _ _
  have bottomPositive : 0 < bottomMajorant owner := majorant_positive _ _ _ _
  have topPositive : 0 < topMajorant owner := majorant_positive _ _ _ _
  by_cases same : source = target
  · subst target
    unfold directTransport reservedTransport
    rewrite [dif_pos rfl]
    unfold transportFloor
    exact Fraction.Order.Basic.min_le_left _ _
  · have leftSmall := paid.trans_lt left
    have rightSmall := paid.trans_lt right
    have bottomSmall := paid.trans_lt bottom
    have topSmall := paid.trans_lt top
    let actual := reservedTransportAmbientCache owner targetNonzero small 0 same
      leftSmall rightSmall bottomSmall topSmall
      (SquareRootContinuation.transportedOwner owner.track.initial small).clearance.positive
    have leftBound :
        sideFloor owner.track.initial.ambientLeftClearance.bound (leftMajorant owner) ceiling ≤
          (ambientLeftAfterMove owner leftSmall).bound := by
      unfold ambientLeftAfterMove
      rewrite [Transport.verticalClearanceAfterMove_bound]
      exact sideFloor_le left paid leftPositive
    have rightBound :
        sideFloor owner.track.initial.ambientRightClearance.bound (rightMajorant owner) ceiling ≤
          (ambientRightAfterMove owner rightSmall).bound := by
      unfold ambientRightAfterMove
      rewrite [Transport.verticalClearanceAfterMove_bound]
      exact sideFloor_le right paid rightPositive
    have bottomBound :
        sideFloor owner.track.initial.ambientBottomClearance.bound (bottomMajorant owner) ceiling ≤
          (ambientBottomAfterMove owner bottomSmall).bound := by
      unfold ambientBottomAfterMove
      rewrite [Transport.horizontalClearanceAfterMove_bound]
      exact sideFloor_le bottom paid bottomPositive
    have topBound :
        sideFloor owner.track.initial.ambientTopClearance.bound (topMajorant owner) ceiling ≤
          (ambientTopAfterMove owner topSmall).bound := by
      unfold ambientTopAfterMove
      rewrite [Transport.horizontalClearanceAfterMove_bound]
      exact sideFloor_le top paid topPositive
    have sides : transportFloor owner ceiling ≤
        min (sideFloor owner.track.initial.ambientLeftClearance.bound (leftMajorant owner) ceiling)
          (min (sideFloor owner.track.initial.ambientRightClearance.bound (rightMajorant owner) ceiling)
            (min (sideFloor owner.track.initial.ambientBottomClearance.bound (bottomMajorant owner) ceiling)
              (sideFloor owner.track.initial.ambientTopClearance.bound (topMajorant owner) ceiling))) := by
      unfold transportFloor
      exact Fraction.Order.Basic.min_le_right _ _
    unfold directTransport
    rewrite [actual.clearanceBound]
    exact Fraction.Order.Basic.le_min
      ((sides.trans (Fraction.Order.Basic.min_le_left _ _)).trans leftBound)
      (Fraction.Order.Basic.le_min
        ((sides.trans ((Fraction.Order.Basic.min_le_right _ _).trans
          (Fraction.Order.Basic.min_le_left _ _))).trans rightBound)
        (Fraction.Order.Basic.le_min
          ((sides.trans ((Fraction.Order.Basic.min_le_right _ _).trans
            ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))).trans bottomBound)
          ((sides.trans ((Fraction.Order.Basic.min_le_right _ _).trans
            ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_right _ _)))).trans topBound)))

end Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance

end
