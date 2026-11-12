module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
public import Purelib.Riemann.Paths.ClearBoxPaths.Distance
public import Purelib.Approximation.AccuracyRequest
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Computed whole-source distances on the SAME retained sharp L-route

The existing Geometry.route factory identity binds the path. Its actual
ordered edge points are bounded from the old curved source by the original
radial endpoint time law. A positive physical request computes a sufficient
chart width and finite depth before any factor or source query is selected.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Geometry

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Paths
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2} {actual : Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {source : Reading actual first firstInside} {target : Reading actual last lastInside}
variable {regular : parameter ≠ criticalValue site}
variable {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}

/-- The original radial endpoint budget and both actual orthogonal route legs have this time multiplier. -/
@[expose] def distanceFactor (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  (25 / 2) * Norm.Basic.normSq (halfGap site parameter)

/-- The actual radial route-distance multiplier is nonnegative. -/
theorem distanceFactor_nonnegative (site : Fin 2) (parameter : Canonical) :
    0 ≤ distanceFactor site parameter :=
  Arithmetic.mul_nonneg_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 25 / 2)
    (Norm.Basic.normSq_nonneg _)

/-- Every point of every stored route edge obeys the SAME old curved-source distance bound. -/
theorem route_pointBound (geometry : Geometry source target regular payment) :
    ClearPath.PointBound (coordinate site parameter 2 quarter positive first)
      (distanceFactor site parameter * (first - last) ^ 2) geometry.route.path := by
  have actual := ClearBoxPaths.Route.build_pointBound geometry.clearance
    (coordinate site parameter 2 quarter positive first) (coordinate site parameter 2 quarter positive last)
    (source_inside (positive := positive) regular) (target_inside (positive := positive) regular payment)
  rewrite [← geometry.route_eq] at actual
  have endpoints := Radial.quarter_base_distance_le site parameter 2 quarter positive
    (of_decide_eq_true rfl : (1 : Fraction.Rational) ≤ 2)
    (Fraction.Order.Basic.le_refl (2 : Fraction.Rational)) first last
  change Norm.Basic.normSq (coordinate site parameter 2 quarter positive first -
    coordinate site parameter 2 quarter positive last) ≤ _ at endpoints
  rewrite [Norm.Bounds.normSq_sub_symm
    (coordinate site parameter 2 quarter positive first) (coordinate site parameter 2 quarter positive last)]
    at endpoints
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct endpoints
    (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 2)
  have coefficient : (2 * (25 / 4) : Fraction.Rational) = 25 / 2 := of_decide_eq_true rfl
  have scalar : 2 * ((25 / 4) * Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) =
      distanceFactor site parameter * (first - last) ^ 2 := by
    calc
      _ = (2 * (25 / 4)) * (Norm.Basic.normSq (halfGap site parameter) * (first - last) ^ 2) := by ring1
      _ = _ := by rewrite [coefficient]; unfold distanceFactor; ring1
  exact actual.mono (scaled.trans_eq scalar)

/-- A positive physical quadrance tolerance determines a sufficient original chart-width request. -/
def widthRequest (site : Fin 2) (parameter : Canonical) (physical : AccuracyRequest) : AccuracyRequest :=
  ⟨physical.tolerance / (1 + distanceFactor site parameter),
    Fraction.Order.Field.div_pos_direct physical.positive
      (Arithmetic.add_pos_of_pos_of_nonneg_direct
        (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) (distanceFactor_nonnegative site parameter))⟩

/-- The computed chart-width request pays its actual whole-source route-distance multiplier. -/
theorem width_payment (site : Fin 2) (parameter : Canonical) (physical : AccuracyRequest) :
    distanceFactor site parameter * (widthRequest site parameter physical).tolerance ≤ physical.tolerance := by
  have denominator := Arithmetic.add_pos_of_pos_of_nonneg_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) (distanceFactor_nonnegative site parameter)
  have ratio : distanceFactor site parameter / (1 + distanceFactor site parameter) ≤ 1 := by
    apply (Fraction.Order.Field.div_le_iff_pos denominator).mpr
    exact (Fraction.Field.zero_add (distanceFactor site parameter)).symm.trans_le
      ((Arithmetic.add_le_add_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1)
        (Fraction.Order.Basic.le_refl _)).trans_eq (Fraction.Field.one_mul _).symm)
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct ratio physical.positive.le
  exact (show distanceFactor site parameter * (widthRequest site parameter physical).tolerance =
    physical.tolerance * (distanceFactor site parameter / (1 + distanceFactor site parameter)) by
      change distanceFactor site parameter * (physical.tolerance / (1 + distanceFactor site parameter)) =
        physical.tolerance * (distanceFactor site parameter / (1 + distanceFactor site parameter))
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      ring1).trans_le (scaled.trans_eq (Fraction.Field.mul_one_direct _))

/-- An actual retained route whose chart width meets the computed request pays the physical tolerance at every edge. -/
theorem route_pointBound_of_width (geometry : Geometry source target regular payment) (physical : AccuracyRequest)
    (paid : (first - last) ^ 2 ≤ (widthRequest site parameter physical).tolerance) :
    ClearPath.PointBound (coordinate site parameter 2 quarter positive first) physical.tolerance
      geometry.route.path :=
  geometry.route_pointBound.mono
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct paid
      (distanceFactor_nonnegative site parameter)).trans (width_payment site parameter physical))

/-- The original finite quarter search computes a sufficient chart depth from the actual physical tolerance. -/
def widthMinimum (site : Fin 2) (parameter : Canonical) (physical : AccuracyRequest) : Nat :=
  Geometric.Search.firstQuarterBelow 1 0 (widthRequest site parameter physical).tolerance

/-- The computed chart depth pays the SAME positive physical request on every actual retained route edge. -/
theorem route_pointBound_of_depth (geometry : Geometry source target regular payment) (physical : AccuracyRequest)
    (paid : (first - last) ^ 2 ≤ Geometric.Basic.quarterRadius 1 (widthMinimum site parameter physical)) :
    ClearPath.PointBound (coordinate site parameter 2 quarter positive first) physical.tolerance
      geometry.route.path :=
  geometry.route_pointBound_of_width physical
    (paid.trans (Geometric.Search.firstQuarterBelow_accurate 1
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1) 0
      (widthRequest site parameter physical).tolerance (widthRequest site parameter physical).positive).le)

end Geometry

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
