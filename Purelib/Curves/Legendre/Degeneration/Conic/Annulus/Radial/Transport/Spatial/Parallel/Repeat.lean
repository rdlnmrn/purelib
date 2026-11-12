module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Distance
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Parameter.Bounds
public import Purelib.Polynomial.Geometry.ClearPath.HalfOpen
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Ordinate
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Actual repeated-route visits pay neighboring normalized seed windows

Two retained sharp Routes may belong to different original quarter and
Anchor families. Their literal half-open visits give both source-distance
payments at the SAME physical point. Actual depth-ten chart widths then
pay the original signed-seed near-window bound, without distinctness,
coordinate-based root identification or a returning-loop assumption.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Geometry

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {firstQuarter lastQuarter : UnitCircuitQuarter}
variable {firstPositive lastPositive : (0 : Fraction.Rational) < 2}
variable {firstActual : Transport.Quarter site parameter 2 firstQuarter firstPositive}
variable {lastActual : Transport.Quarter site parameter 2 lastQuarter lastPositive}
variable {firstReference firstTargetTime lastReference lastTargetTime : Fraction.Rational}
variable {firstReferenceInside : FixedRootBoxPath.Inside firstReference}
variable {firstTargetInside : FixedRootBoxPath.Inside firstTargetTime}
variable {lastReferenceInside : FixedRootBoxPath.Inside lastReference}
variable {lastTargetInside : FixedRootBoxPath.Inside lastTargetTime}
variable {firstSource : Transport.Reading firstActual firstReference firstReferenceInside}
variable {firstTarget : Transport.Reading firstActual firstTargetTime firstTargetInside}
variable {lastSource : Transport.Reading lastActual lastReference lastReferenceInside}
variable {lastTarget : Transport.Reading lastActual lastTargetTime lastTargetInside}
variable {firstAnchor : Parameter.Anchor firstSource.lift} {lastAnchor : Parameter.Anchor lastSource.lift}
variable {firstPayment : (firstTargetTime - firstReference) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {lastPayment : (lastTargetTime - lastReference) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable (firstGeometry : Geometry firstSource firstTarget firstAnchor.regular firstPayment)
variable (lastGeometry : Geometry lastSource lastTarget lastAnchor.regular lastPayment)

/-- The original depth-ten quarter radius pays the exact two-route ordinate multiplier and seed-radius floor. -/
private theorem depth_ten_payment :
    (Fraction.Cast.fromInt 1250 / 9 : Fraction.Rational) * Geometric.Basic.quarterRadius 1 10 ≤
      (9 / 128) / Fraction.Cast.fromInt 256 := by
  have decay : Geometric.Basic.quarterRadius 1 10 =
      (1 / Fraction.Cast.fromInt 1048576 : Fraction.Rational) := by
    unfold Geometric.Basic.quarterRadius
    decide +kernel
  rewrite [decay]
  decide +kernel

/-- Two literal visits of the retained original Routes bound their original curved source-center displacement. -/
theorem source_distance_le_of_repeat
    (firstWidth : (firstReference - firstTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
    (lastWidth : (lastReference - lastTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
    (point : Canonical) (firstVisit : firstGeometry.route.path.HalfOpen point)
    (lastVisit : lastGeometry.route.path.HalfOpen point) :
    Norm.Basic.normSq
      ((Parameter.sourcePoint site parameter (Waist.direction lastQuarter lastReference)).base -
        (Parameter.sourcePoint site parameter (Waist.direction firstQuarter firstReference)).base) ≤
      50 * Norm.Basic.normSq (halfGap site parameter) * Geometric.Basic.quarterRadius 1 10 := by
  have firstLocal := firstVisit.pointBound firstGeometry.route_pointBound
  have lastLocal := lastVisit.pointBound lastGeometry.route_pointBound
  have firstPaid := firstLocal.trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct firstWidth
      (distanceFactor_nonnegative site parameter))
  have lastPaid := lastLocal.trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct lastWidth
      (distanceFactor_nonnegative site parameter))
  have triangle := Norm.Bounds.normSq_sub_le_via
    (Parameter.sourcePoint site parameter (Waist.direction lastQuarter lastReference)).base point
    (Parameter.sourcePoint site parameter (Waist.direction firstQuarter firstReference)).base
  rewrite [Norm.Bounds.normSq_sub_symm point
    (Parameter.sourcePoint site parameter (Waist.direction firstQuarter firstReference)).base] at triangle
  have both := Arithmetic.add_le_add_direct lastPaid firstPaid
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct both
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2)
  apply triangle.trans
  apply paid.trans_eq
  unfold distanceFactor
  calc
    _ = (2 * ((25 / 2 : Fraction.Rational) + 25 / 2)) *
        Norm.Basic.normSq (halfGap site parameter) * Geometric.Basic.quarterRadius 1 10 := by ring1
    _ = _ := congrArg (fun coefficient => coefficient * Norm.Basic.normSq (halfGap site parameter) *
      Geometric.Basic.quarterRadius 1 10)
      (of_decide_eq_true rfl : (2 * ((25 / 2 : Fraction.Rational) + 25 / 2)) = 50)

/-- Actual repeated Route visits at sufficient widths pay the original source Seed's normalized-window condition.

The scale-two ellipse law retains both original source coordinates and exact
ordinates. Its finite factor and the actual two Route payments are bounded
by the same original seed-radius floor. All four quarter pairings, arbitrary
half-gap component signs and degenerate Route branches use this same proof.
-/
theorem source_ordinates_near_of_repeat
    (firstWidth : (firstReference - firstTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
    (lastWidth : (lastReference - lastTargetTime) ^ 2 ≤ Geometric.Basic.quarterRadius 1 10)
    (point : Canonical) (firstVisit : firstGeometry.route.path.HalfOpen point)
    (lastVisit : lastGeometry.route.path.HalfOpen point) :
    Norm.Basic.normSq
      ((Parameter.sourcePoint site parameter (Waist.direction lastQuarter lastReference)).ordinate -
        (Parameter.sourcePoint site parameter (Waist.direction firstQuarter firstReference)).ordinate) ≤
      firstAnchor.seed.separation.radius ^ 2 / Fraction.Cast.fromInt 256 := by
  have sources := source_distance_le_of_repeat (firstAnchor := firstAnchor) (lastAnchor := lastAnchor)
    firstGeometry lastGeometry firstWidth lastWidth point firstVisit lastVisit
  have ellipse := parallel_ordinate_distance_le_base site parameter (Waist.direction lastQuarter lastReference)
    (Waist.direction firstQuarter firstReference) firstPositive
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct sources
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 25 / 9)
  have near : Norm.Basic.normSq
      ((Parameter.sourcePoint site parameter (Waist.direction lastQuarter lastReference)).ordinate -
        (Parameter.sourcePoint site parameter (Waist.direction firstQuarter firstReference)).ordinate) ≤
      ((Fraction.Cast.fromInt 1250 / 9) * Geometric.Basic.quarterRadius 1 10) *
        Norm.Basic.normSq (halfGap site parameter) := by
    apply ellipse.trans
    apply scaled.trans_eq
    calc
      _ = ((25 / 9 : Fraction.Rational) * 50) * Geometric.Basic.quarterRadius 1 10 *
          Norm.Basic.normSq (halfGap site parameter) := by ring1
      _ = _ := congrArg (fun coefficient => coefficient * Geometric.Basic.quarterRadius 1 10 *
        Norm.Basic.normSq (halfGap site parameter))
        (of_decide_eq_true rfl : ((25 / 9 : Fraction.Rational) * 50) = Fraction.Cast.fromInt 1250 / 9)
  have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct depth_ten_payment
    (Norm.Basic.normSq_nonneg (halfGap site parameter))
  have radius := Arithmetic.mul_le_mul_of_nonneg_right_direct firstAnchor.radius_lower
    (Fraction.Order.Field.inv_pos_direct
      (of_decide_eq_true rfl : (0 : Fraction.Rational) < Fraction.Cast.fromInt 256)).1
  apply near.trans
  apply paid.trans
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  exact (show (((9 / 128 : Fraction.Rational) * (Fraction.Cast.fromInt 256)⁻¹) *
      Norm.Basic.normSq (halfGap site parameter)) =
        ((9 / 128) * Norm.Basic.normSq (halfGap site parameter)) * (Fraction.Cast.fromInt 256)⁻¹ by
          ring1).trans_le radius

end Geometry

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
