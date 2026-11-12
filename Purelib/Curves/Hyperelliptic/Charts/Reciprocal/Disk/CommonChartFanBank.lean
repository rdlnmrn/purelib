module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.RootRadialPairedArcs
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.RootRadialPairedBoundary
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Budget

public section

/-! Complete-bank fan acquisition pays both finite counts and preserves
the exact open radial/arc boundary of every retained common interval. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib
open Purelib.Riemann
open Purelib.Data.Rat

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Riemann.RootContinuation

variable {genus count otherCount depth floor index : Nat} {curve : Basic.HyperellipticCurve genus}
  {differential other : Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {otherPatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch
    (Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : UniformReciprocalModels.Data patch count} {otherData :
    UniformReciprocalModels.Data otherPatch otherCount}
  {cover : UniformReciprocalCover.Cover data} {otherCover :
    UniformReciprocalCover.Cover otherData}
  {regular : RegularBounds.Data cap} {common :
    UniformReciprocalCommonCover.CommonCover cover otherCover}
  {target : Normalization.InverseRootPolynomial.Coordinate} {request :
    CommonChartBank.ChartRequest regular common depth target floor}
  (evaluated : CommonChartBank.ChartRequest.Evaluation request index)

/-- The actual edge count of one retained common-interval chart plan. -/
@[expose] def fanEdgeWeight (i : Fin common.intervals.length)
    (plan : CommonChartBank.ChartPlan regular common depth request.allowance floor
      i) : Nat := plan.geometry.tail.length

set_option genInjectivity false in
/-- A complete-bank fan request paying both the interval count and the maximum retained edge count.

Its two positive allowances are fixed from the original chart plans before fan acquisition. -/
structure FanBankRequest (requested : Normalization.InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The maximum actual edge count among the retained chart plans. -/ maximumEdges : Nat
  /-- The maximum is computed from the original plan bank. -/ maximumEdges_eq : maximumEdges = request.plans.maximum
    (fanEdgeWeight (request := request))
  /-- The allocated scalar allowance for each original interval. -/ intervalAllowance :
    Normalization.InverseRootPolynomial.Coordinate
  /-- The allowance is exactly the original count-based per-term allocation. -/ intervalAllowance_eq : intervalAllowance
    = Aggregate.perTerm requested common.intervals.length
  /-- The interval allowance is positive. -/ intervalPositive : 0 < intervalAllowance
  /-- The squared original interval count is paid by the requested target. -/ intervalPaid : (common.intervals.length :
    Normalization.InverseRootPolynomial.Coordinate) * ((common.intervals.length :
    Normalization.InverseRootPolynomial.Coordinate) * intervalAllowance) < requested
  /-- The allocated allowance for each retained fan. -/ fanAllowance : Normalization.InverseRootPolynomial.Coordinate
  /-- The fan allowance is allocated from the original interval allowance and maximum edge count. -/ fanAllowance_eq :
    fanAllowance = Aggregate.perTerm intervalAllowance maximumEdges
  /-- The fan allowance is positive. -/ fanPositive : 0 < fanAllowance
  /-- The squared maximum edge count is paid by the retained interval allowance. -/ fanPaid : (maximumEdges :
    Normalization.InverseRootPolynomial.Coordinate) * ((maximumEdges : Normalization.InverseRootPolynomial.Coordinate) *
    fanAllowance) < intervalAllowance
  /-- The actual original fan request at the allocated allowance. -/ fan :
    CommonChartFans.FanRequest evaluated fanAllowance minimum

constructive_injectivity FanBankRequest

namespace FanBankRequest

/-- Allocate the interval and per-fan allowances from the actual retained counts, then prepare the original fan request.
-/
@[expose] def build (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested) (minimum :
  Nat) : FanBankRequest evaluated requested minimum :=
  let maximumEdges := request.plans.maximum (fanEdgeWeight
    (request := request))
  let intervalAllowance := Aggregate.perTerm requested common.intervals.length
  have intervalPositive := Aggregate.perTerm_positive positive common.intervals.length
  let fanAllowance := Aggregate.perTerm intervalAllowance maximumEdges
  have fanPositive := Aggregate.perTerm_positive intervalPositive maximumEdges
  ⟨maximumEdges, rfl, intervalAllowance, rfl, intervalPositive,
    Aggregate.count_mul_perTerm_lt positive common.intervals.length,
    fanAllowance, rfl, fanPositive, Aggregate.count_mul_perTerm_lt intervalPositive maximumEdges,
    CommonChartFans.FanRequest.build evaluated fanAllowance fanPositive minimum⟩

variable {evaluated} {requested : Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Raise only the retained fan depth, preserving its original allowances and count payments. -/
@[expose] def atDepth (planned : FanBankRequest evaluated
  requested minimum) (depth : Nat)
    (later : planned.fan.depth ≤ depth) : FanBankRequest
      evaluated requested minimum :=
  { planned with fan := CommonChartFans.FanRequest.atDepth planned.fan depth later
    }

/-- The actual dependent fan family for every edge of one retained common interval. -/
@[expose] def IntervalFans (planned : FanBankRequest evaluated
  requested minimum) (i : Fin common.intervals.length) :=
  Data.Vector.DependentVector (fun edge : Fin (request.plans.get i).geometry.tail.length =>
    CommonChartFans.FanRequest.Fan planned.fan i edge)

/-- Sum the original paired radial-arc areas along one complete common interval. -/
@[expose] def ArcArea (radialDepth : Nat) (i : Fin common.intervals.length) : Gaussian :=
  FiniteSum.Fin.sumFin (fun edge : Fin (request.plans.get i).geometry.tail.length =>
    RootRadialPairedArcs.Bilinear.arcArea
      (CommonChartRadialJunctions.radialValues evaluated) radialDepth
      (CommonChartConnections.Evaluation.chartCoordinate evaluated i edge.castSucc)
        (CommonChartConnections.Evaluation.chartCoordinate evaluated i edge.succ))

/-- The original initial radial potential plus the full arc area minus the terminal radial potential. -/
@[expose] def IntervalBoundary (radialDepth : Nat) (i : Fin common.intervals.length) : Gaussian :=
  CommonChartRadialJunctions.radialPotential evaluated radialDepth i 0 +
    ArcArea (evaluated := evaluated) radialDepth
    i -
    CommonChartRadialJunctions.radialPotential evaluated radialDepth i (Fin.last
      (request.plans.get i).geometry.tail.length)

set_option genInjectivity false in
/-- Cached actual fans and their summed area, with the paid bound and exact open radial/arc boundary. -/
structure Interval (planned : FanBankRequest evaluated requested
  minimum) (i : Fin common.intervals.length) where
  /-- The actual acquired original edge fans. -/ fans : planned.IntervalFans i
  /-- Their cached summed area. -/ area : Gaussian.Basic.Canonical
  /-- The cache equals the finite sum of those exact fan areas. -/ area_eq : area = FiniteSum.Fin.sumFin (fun edge =>
    (fans.get edge).sampled.area)
  /-- The actual area satisfies the retained interval allowance. -/ bounded : Gaussian.Norm.Basic.normSq area <
    planned.intervalAllowance
  /-- The area equals the original open radial/arc boundary expression. -/ boundary_eq : area =
    IntervalBoundary (evaluated := evaluated)
    planned.fan.depth i

constructive_injectivity Interval

/-- The sum of actual fan areas satisfies the retained interval allowance using the original maximum edge count. -/
theorem interval_bounded (planned : FanBankRequest evaluated
  requested minimum)
    (i : Fin common.intervals.length) (fans : planned.IntervalFans i) :
    Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun edge => (fans.get edge).sampled.area)) <
      planned.intervalAllowance := open Purelib.Data.Rat in by
  have bound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le (fun edge => (fans.get edge).sampled.area)
    planned.fanAllowance (fun edge => (fans.get edge).accurate.le)
  have count : (request.plans.get i).geometry.tail.length ≤ planned.maximumEdges :=
    (Data.Vector.DependentVector.get_le_maximum (fanEdgeWeight
      (request := request)) request.plans i).trans_eq planned.maximumEdges_eq.symm
  have squares := Fraction.Order.Arithmetic.pow_le_pow_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    (request.plans.get i).geometry.tail.length))
    (Fraction.Cast.Order.natCast_le_direct count) 2
  have counted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct squares planned.fanPositive.le
  have paid : (planned.maximumEdges : Normalization.InverseRootPolynomial.Coordinate)^2 * planned.fanAllowance <
    planned.intervalAllowance :=
    (by ring1 : (planned.maximumEdges : Normalization.InverseRootPolynomial.Coordinate)^2 * planned.fanAllowance =
      (planned.maximumEdges : Normalization.InverseRootPolynomial.Coordinate) * ((planned.maximumEdges :
        Normalization.InverseRootPolynomial.Coordinate) * planned.fanAllowance)).trans_lt planned.fanPaid
  exact bound.trans_lt (counted.trans_lt paid)

/-- Telescoping the actual fan boundaries retains the original initial and terminal radial potentials. -/
theorem interval_boundary (planned : FanBankRequest evaluated
  requested minimum)
    (i : Fin common.intervals.length) (fans : planned.IntervalFans i) :
    FiniteSum.Fin.sumFin (fun edge => (fans.get edge).sampled.area) =
      IntervalBoundary (evaluated := evaluated)
      planned.fan.depth i := open Purelib.Integration in by
  have edges := FiniteSum.Fin.sumFin_congr (fun edge =>
    CommonChartFans.FanRequest.Fan.boundary_eq (fans.get edge))
  have telescoping := Path.BoundaryRibbon.sum_increasing
    (CommonChartRadialJunctions.radialPotential evaluated planned.fan.depth i)
  rw [FiniteSum.Fin.sumFin_sub] at telescoping
  calc
    _ = ArcArea (evaluated := evaluated)
      planned.fan.depth i -
        (FiniteSum.Fin.sumFin (fun edge : Fin (request.plans.get i).geometry.tail.length =>
          CommonChartRadialJunctions.radialPotential evaluated planned.fan.depth i
          edge.succ) -
          FiniteSum.Fin.sumFin (fun edge : Fin (request.plans.get i).geometry.tail.length =>
            CommonChartRadialJunctions.radialPotential evaluated planned.fan.depth
            i edge.castSucc)) := by
      rw [edges, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_add]
      unfold ArcArea
      ring1
    _ = _ := by
      rw [telescoping];
      unfold IntervalBoundary;
      ring1

/-- Evaluate each original interval fan once and cache their area with its bound and exact boundary identity. -/
@[expose] def acquireInterval (planned : FanBankRequest
  evaluated requested minimum)
    (branch : HyperellipticReciprocal.originOrder curve = 1) (i : Fin
      common.intervals.length) : planned.Interval i :=
  let fans := Data.Vector.DependentVector.ofFn (fun edge =>
    CommonChartFans.FanRequest.acquire planned.fan branch i edge)
  ⟨fans, FiniteSum.Fin.sumFin (fun edge => (fans.get edge).sampled.area), rfl,
    interval_bounded planned i fans,
      interval_boundary planned i fans⟩

/-- The dependent family of cached original interval fan acquisitions. -/
@[expose] def Intervals (planned : FanBankRequest evaluated
  requested minimum) :=
  Data.Vector.DependentVector (planned.Interval)

set_option genInjectivity false in
/-- The cached complete interval bank and total area with both its paid bound and exact boundary sum. -/
structure Bank (planned : FanBankRequest evaluated requested
  minimum) where
  /-- The cached original interval acquisitions. -/ intervals : planned.Intervals
  /-- The cached sum of their actual areas. -/ area : Gaussian.Basic.Canonical
  /-- The total equals the finite sum of the retained interval areas. -/ area_eq : area = FiniteSum.Fin.sumFin (fun i =>
    (intervals.get i).area)
  /-- The total area satisfies the original requested target. -/ bounded : Gaussian.Norm.Basic.normSq area <
    requested
  /-- The total is the exact sum of the retained open interval boundaries. -/ boundary_eq : area = FiniteSum.Fin.sumFin
    (IntervalBoundary (evaluated := evaluated)
    planned.fan.depth)

constructive_injectivity Bank

/-- Each fan is evaluated once on the shared mesh. Both levels of totals
read those cached areas; the exact boundary identity keeps all radial ends. -/
@[expose] def acquire (planned : FanBankRequest evaluated
  requested minimum)
    (branch : HyperellipticReciprocal.originOrder curve = 1) : planned.Bank := by
  let intervals := Data.Vector.DependentVector.ofFn (fun i => planned.acquireInterval branch i)
  let area := FiniteSum.Fin.sumFin (fun i => (intervals.get i).area)
  have bound := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le (fun i => (intervals.get i).area)
    planned.intervalAllowance (fun i => (intervals.get i).bounded.le)
  have paid : (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * planned.intervalAllowance <
    requested :=
    (by ring1 : (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate)^2 * planned.intervalAllowance
      =
      (common.intervals.length : Normalization.InverseRootPolynomial.Coordinate) * ((common.intervals.length :
        Normalization.InverseRootPolynomial.Coordinate) * planned.intervalAllowance)).trans_lt planned.intervalPaid
  exact ⟨intervals, area, rfl, bound.trans_lt paid, FiniteSum.Fin.sumFin_congr (fun i => (intervals.get i).boundary_eq)⟩

end FanBankRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
