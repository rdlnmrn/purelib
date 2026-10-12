module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartRadialJunctions
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedPairedRadialRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
import Purelib.Riemann.RootContinuation.RootRadialGeometry
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Tactic.Ring

public section

/-! Shared cap bounds and synchronized physical-coordinate fans over the
actual retained parent bank. No root-coordinate radial formula is used. -/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartFans.FanBankRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularPolynomialArcs.SourceChartRequest
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path.Dyadic.RadialTriangles
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Periods
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.RootRadialGeometry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_sub)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartBankRequest ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFanBank (FanBankRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartFans (FanRequest)
open Purelib.Integration.Path.Dyadic.RadialTriangles (Parameters)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target requested : Coordinate} {minimum depth : Nat}
  {original : Request regular other parents
    target minimum}
  {request : ChartBankRequest original depth
    requested}
  (evaluated : Evaluation
    request)

/-- The original physical-coordinate fan request on one retained parent chart evaluation. -/
@[expose] def RegularFanPlan (allowance : InverseRootPolynomial.Coordinate) (floor : Nat) (i : Fin
  original.plans.length) :=
  CommonChartFanBank.FanBankRequest (evaluated.entries.get i) allowance floor

/-- Prepare one parent fan from the two shared original cap energy bounds and nested interval/edge allowances. -/
@[expose] def sharedFanPlan
    (firstBounds : Cap.EnergyBounds evaluated.firstCap RootRadialGeometry.domain)
    (otherBounds : Cap.EnergyBounds evaluated.otherCap RootRadialGeometry.domain)
    (allowance : InverseRootPolynomial.Coordinate) (positive : 0 < allowance) (floor : Nat) (i : Fin
      original.plans.length) :
    RegularFanPlan evaluated allowance floor i := by
  let entry := evaluated.entries.get i
  let left : Cap.EnergyBounds entry.samples.firstCap RootRadialGeometry.domain := (evaluated.shared i).1.symm ▸
    firstBounds
  let right : Cap.EnergyBounds entry.samples.otherCap RootRadialGeometry.domain := (evaluated.shared i).2.symm
    ▸ otherBounds
  let maximumEdges := (request.plans.get i).plans.maximum
    (CommonChartFanBank.fanEdgeWeight (request := request.plans.get i))
  let intervalAllowance := Aggregate.perTerm allowance (PairedParentCharts.ChartParent original
    i).common.intervals.length
  have intervalPositive := Aggregate.perTerm_positive positive (PairedParentCharts.ChartParent original
    i).common.intervals.length
  let fanAllowance := Aggregate.perTerm intervalAllowance maximumEdges
  have fanPositive := Aggregate.perTerm_positive intervalPositive maximumEdges
  let scale : Coordinate := 128^2 * 64 * ReciprocalCapBilinearBounds.bilinearScale left right
  have nonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _) (by decide +kernel))
      (ReciprocalCapBilinearBounds.bilinearScale_nonnegative left right)
  let radialDepth := Search.firstQuarterBelow scale floor fanAllowance
  let fan : CommonChartFans.FanRequest entry fanAllowance floor :=
    ⟨left, right, scale, rfl, radialDepth, Nat.le_refl _,
      Search.firstQuarterBelow_ge scale floor fanAllowance,
      Parameters.build radialDepth, Geometric.Basic.quarterRadius scale radialDepth, rfl,
      Search.firstQuarterBelow_accurate scale nonnegative floor fanAllowance fanPositive⟩
  exact ⟨maximumEdges, rfl, intervalAllowance, rfl, intervalPositive,
    Aggregate.count_mul_perTerm_lt positive _, fanAllowance, rfl, fanPositive,
    Aggregate.count_mul_perTerm_lt intervalPositive _, fan⟩

/-- The actual radial depth of the retained original parent fan request. -/
@[expose] def regularFanDepth {allowance : InverseRootPolynomial.Coordinate} {floor : Nat} (i : Fin
  original.plans.length)
    (plan : RegularFanPlan evaluated allowance floor
      i) : Nat := plan.fan.depth

set_option genInjectivity false in
/-- A complete physical-coordinate fan schedule over the retained original parent bank.

Both shared cap energy bounds are computed once, every parent receives a paid allowance, and all fans are synchronized
to their retained maximum depth. -/
structure RegularFanRequest (error : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original first cap energy bound on the physical radial domain. -/ firstBounds : Cap.EnergyBounds
    evaluated.firstCap RootRadialGeometry.domain
  /-- The original second cap energy bound on that same physical domain. -/ otherBounds : Cap.EnergyBounds
    evaluated.otherCap RootRadialGeometry.domain
  /-- The retained common per-parent fan allowance. -/ allowance : InverseRootPolynomial.Coordinate
  /-- The common allowance is exactly the aggregate share of the original target over the retained parent count. -/
    allowance_eq : allowance = Aggregate.perTerm error original.plans.length
  /-- The retained per-parent allowance is strictly positive. -/ positive : 0 < allowance
  /-- The original squared parent count times the retained allowance is strictly below the requested error. -/ paid :
    (original.plans.length : InverseRootPolynomial.Coordinate) * ((original.plans.length :
    InverseRootPolynomial.Coordinate) * allowance) < error
  /-- The original dependent bank of fan plans, retaining each actual parent index. -/ plans :
    Data.Vector.DependentVector (RegularFanPlan
    evaluated allowance floor)
  /-- The cached common radial depth for the original complete fan bank. -/ radialDepth : Nat
  /-- The shared radial depth is exactly the maximum of the retained original fan depths. -/ radialDepth_eq :
    radialDepth = plans.maximum (regularFanDepth
    evaluated)

constructive_injectivity RegularFanRequest

namespace RegularFanRequest

/-- Compute both shared cap bounds once, prepare every original parent fan and cache their common maximum radial depth.
-/
@[expose] def build (error : InverseRootPolynomial.Coordinate) (positive : 0 < error) (floor : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest evaluated error floor :=
  let firstBounds := EnergyBounds.build evaluated.firstCap RootRadialGeometry.domain
  let otherBounds := EnergyBounds.build evaluated.otherCap RootRadialGeometry.domain
  let allowance := Aggregate.perTerm error original.plans.length
  have allowancePositive := Aggregate.perTerm_positive positive original.plans.length
  let plans := DependentVector.ofFn (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.sharedFanPlan
    evaluated firstBounds otherBounds allowance allowancePositive floor)
  ⟨firstBounds, otherBounds, allowance, rfl, allowancePositive,
    Aggregate.count_mul_perTerm_lt positive original.plans.length,
    plans, plans.maximum (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.regularFanDepth evaluated),
      rfl⟩

variable {evaluated} {error : Coordinate} {floor : Nat}

/-- Refine the selected original parent fan to the shared retained radial depth. -/
@[expose] def synchronized (planned :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest evaluated error floor) (i : Fin
  original.plans.length) :=
  FanBankRequest.atDepth (planned.plans.get i) planned.radialDepth
    ((DependentVector.get_le_maximum (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.regularFanDepth
      evaluated) planned.plans i).trans_eq planned.radialDepth_eq.symm)

/-- The actual dependent bank of regular physical-coordinate fans at their common retained depth. -/
@[expose] def Banks (planned : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest
  evaluated error floor) :=
  Data.Vector.DependentVector (fun i => FanBankRequest.RegularBank
    (synchronized planned i))

/-- The total actual regular physical-arc area over every original parent and interval at the retained depth. -/
@[expose] def arcArea (planned : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest
  evaluated error floor) : Gaussian :=
  FiniteSum.Fin.sumFin (fun i => FiniteSum.Fin.sumFin (ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get
    i) planned.radialDepth))

/-- The shared original cap-pair radial area at the inverse physical endpoint and retained common depth. -/
@[expose] def radialValue (planned :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest evaluated error floor) (point :
  InverseRootPolynomial.Gaussian) : Gaussian :=
  Bilinear.radialArea
    (ReciprocalCapBilinearBounds.pairedValue evaluated.firstCap evaluated.otherCap) planned.radialDepth point⁻¹

/-- Each original parent radial value reads the same retained shared cap samples. -/
theorem radial_readback (planned : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest
  evaluated error floor)
    (i : Fin original.plans.length) (point : InverseRootPolynomial.Gaussian) :
    Bilinear.radialArea (CommonChartRadialJunctions.radialValues (evaluated.entries.get i)) planned.radialDepth point⁻¹
      =
      radialValue planned point :=
  (congrArg (fun sample : Primitives.Sample cap differential request.index collar.box =>
    Bilinear.radialArea
      (ReciprocalCapBilinearBounds.pairedValue sample (evaluated.entries.get i).samples.otherCap)
      planned.radialDepth point⁻¹) (evaluated.shared i).1).trans
    (congrArg (fun sample : Primitives.Sample cap other request.index collar.box =>
      Bilinear.radialArea
        (ReciprocalCapBilinearBounds.pairedValue evaluated.firstCap sample)
        planned.radialDepth point⁻¹) (evaluated.shared i).2)

set_option genInjectivity false in
/-- The acquired original fan bank with its cached total area and exact physical open-boundary identity.

The retained target bounds the actual fan area, while the boundary keeps both original outer radial endpoint
contributions. -/
structure Certificate (planned : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest
  evaluated error floor) where
  /-- The complete actual original regular fan bank at the synchronized depth. -/ banks :
    Banks planned
  /-- The cached total area of the original acquired fans. -/ area : InverseRootPolynomial.Gaussian
  /-- The retained area is exactly the finite sum of the original fan-bank areas. -/ area_eq : area =
    FiniteSum.Fin.sumFin (fun i => (banks.get i).area)
  /-- The actual retained fan area has squared norm strictly below the original requested error. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq area < error
  /-- The cached fan area equals the original physical arc total plus the signed outer radial endpoint contributions. -/
    boundary_eq : area = arcArea
    planned + FiniteSum.Fin.sumFin (fun i =>
    radialValue planned
      ((PairedParentCharts.ChartParent original i).parent.edge.point 0) -
      radialValue planned
        ((PairedParentCharts.ChartParent original i).parent.edge.point 1))

constructive_injectivity Certificate

/-- Acquire every original regular fan at the synchronized depth and cache its complete area sum with the paid bound and
physical boundary identity. -/
@[expose] def acquire (planned : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest
  evaluated error floor) :
  Certificate planned := by
  let banks := DependentVector.ofFn (fun i => FanBankRequest.acquireRegular
    (synchronized planned i))
  let area := FiniteSum.Fin.sumFin (fun i => (banks.get i).area)
  have bound := Indexed.normSq_sumFin_le (fun i => (banks.get i).area)
    planned.allowance (fun i => (banks.get i).bounded.le)
  have paid : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * planned.allowance < error :=
    (by ring1 : (original.plans.length : InverseRootPolynomial.Coordinate)^2 * planned.allowance =
      (original.plans.length : InverseRootPolynomial.Coordinate) * ((original.plans.length :
        InverseRootPolynomial.Coordinate) * planned.allowance)).trans_lt planned.paid
  have readback (i : Fin original.plans.length) : (banks.get i).area =
      FiniteSum.Fin.sumFin (ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get i) planned.radialDepth) +
        radialValue planned
          ((PairedParentCharts.ChartParent original i).parent.edge.point 0) -
        radialValue planned
          ((PairedParentCharts.ChartParent original i).parent.edge.point 1) := by
    have equal := RegularBank.open_boundary (banks.get i)
    change (banks.get i).area = FiniteSum.Fin.sumFin (ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get
      i) planned.radialDepth) +
      Bilinear.radialArea (CommonChartRadialJunctions.radialValues (evaluated.entries.get i)) planned.radialDepth
        ((PairedParentCharts.ChartParent original i).parent.edge.point 0)⁻¹ -
      Bilinear.radialArea (CommonChartRadialJunctions.radialValues (evaluated.entries.get i)) planned.radialDepth
        ((PairedParentCharts.ChartParent original i).parent.edge.point 1)⁻¹ at equal
    rw [planned.radial_readback, planned.radial_readback] at equal
    exact equal
  refine ⟨banks, area, rfl, bound.trans_lt paid, ?_⟩
  change FiniteSum.Fin.sumFin (fun i => (banks.get i).area) = _
  rw [FiniteSum.Fin.sumFin_congr readback, FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_add, FiniteSum.Fin.sumFin_sub]
  unfold arcArea
  ring1

/-- Summing a mapped original list by its retained finite indices equals the Gaussian sum of that same mapped list. -/
private theorem indexed_sum {α : Type _} (values : List α) (f : α → InverseRootPolynomial.Gaussian) :
    FiniteSum.Fin.sumFin (fun i : Fin values.length => f (values[i.val]'i.isLt)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (values.map f) := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      change f first + FiniteSum.Fin.sumFin (fun i : Fin rest.length => f (rest[i.val]'i.isLt)) =
        f first + Data.Gaussian.Norm.Sum.Basic.gaussianSum (rest.map f)
      exact congrArg (f first + ·) ih

/-- The signed endpoint values telescope along the original retained physical parent chain. -/
private theorem chain_radial (value : InverseRootPolynomial.Gaussian → InverseRootPolynomial.Gaussian)
    {parents : List (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (parents.map (fun parent => value (parent.edge.point 0) - value (parent.edge.point 1))) =
      value start.coordinate - value finish.coordinate := by
  induction chain with
  | nil point => change (0 : InverseRootPolynomial.Gaussian) = value point.coordinate - value point.coordinate; ring1
  | cons parent tail ih =>
      change value (parent.edge.point 0) - value (parent.edge.point 1) + _ = _
      rw [ih, parent.edge.point_zero, parent.edge.point_one]
      ring1

/-- Closing is established from the retained physical chain. No equation between independently sampled sheet coordinates
is assumed. -/
theorem Certificate.closed_area {planned :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest evaluated error floor} (certified
  : Certificate planned)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    (closed : start.coordinate = finish.coordinate) : certified.area =
      arcArea planned := by
  obtain ⟨chain⟩ := chain
  have readback := indexed_sum
    original.plans (fun plan =>
    radialValue planned
      (plan.parent.edge.point 0) -
      radialValue planned
      (plan.parent.edge.point 1))
  have mapped : original.plans.map (fun plan =>
      radialValue planned
        (plan.parent.edge.point 0) -
        radialValue planned
        (plan.parent.edge.point 1)) =
      parents.map (fun parent =>
        radialValue planned
        (parent.edge.point 0) -
        radialValue planned
        (parent.edge.point 1)) := by
    have transported := congrArg (fun retained : List (PreparedSubdivisionModelCore.CenteredEdge curve differential) =>
      retained.map (fun parent =>
        radialValue planned
        (parent.edge.point 0) -
        radialValue planned
        (parent.edge.point 1)))
      original.parents_eq
    rw [Data.List.Map.map_map] at transported
    exact transported
  rw [mapped, chain_radial
    (radialValue planned) chain,
    closed, sub_self] at readback
  rw [certified.boundary_eq]
  exact (congrArg (arcArea planned
    + ·) readback).trans (add_zero _)

/-- For a physically closed retained parent chain, the original total arc area has squared norm below the fan request
target. -/
theorem Certificate.closed_bounded {planned :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest evaluated error floor} (certified
  : Certificate planned)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    (closed : start.coordinate = finish.coordinate) : Data.Gaussian.Norm.Basic.normSq
      (arcArea planned) < error :=
  (congrArg Data.Gaussian.Norm.Basic.normSq (certified.closed_area chain closed).symm).trans_lt
    certified.bounded

/-- The physical source open boundary: the retained source area, its origin correction, and the outer radial ends of the
parent family. The internal physical junctions cancel exactly, so no connector sum appears. Closing the retained chain
cancels the remaining outer ends. -/
@[expose] def sourceOpenBoundary (planned :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest evaluated error floor) : Gaussian
  :=
  evaluated.sourceArea - evaluated.correction +
    FiniteSum.Fin.sumFin (fun i =>
      radialValue planned
      ((PairedParentCharts.ChartParent original i).parent.edge.point 0) -
      radialValue planned
        ((PairedParentCharts.ChartParent original i).parent.edge.point 1))

/-- The actual physical open boundary is bounded using the certified fan boundary (which contains the curved arcs), the
source-to-chart comparison, and the requested chart-versus-arc budget. No connector sum or caller transport equality
remains. -/
theorem Certificate.sourceOpenBoundary_bound {planned :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest evaluated error floor}
    (certified : Certificate
      planned) {arcBudget : InverseRootPolynomial.Coordinate}
    (chartArc : Data.Gaussian.Norm.Basic.normSq (evaluated.chartArea -
      arcArea planned) ≤ arcBudget)
      :
    Data.Gaussian.Norm.Basic.normSq
      (sourceOpenBoundary
      planned) ≤
      2 * (requested + 2 * (error + arcBudget)) := by
  have identity :
    sourceOpenBoundary planned =
      (evaluated.sourceArea - evaluated.chartArea - evaluated.correction) +
        (certified.area + (evaluated.chartArea -
          arcArea planned)) := by
    unfold sourceOpenBoundary
    rw [certified.boundary_eq]
    ring1
  have inner : Data.Gaussian.Norm.Basic.normSq (certified.area + (evaluated.chartArea -
    arcArea planned)) ≤
      2 * (error + arcBudget) :=
    (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
        certified.bounded.le chartArc)
        (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      evaluated.bounded.le inner)
      (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))

/-- Sum the per-parent chart-versus-physical-arc budgets into the one budget used by the open-boundary comparison. Each
parent bound is the conclusion of `chartArea_arcArea_aggregate`. -/
theorem chartArea_arcArea_total (planned :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest evaluated error floor)
    (arcBudget : InverseRootPolynomial.Coordinate) (positive : 0 < arcBudget)
    (each : ∀ p : Fin original.plans.length,
      Data.Gaussian.Norm.Basic.normSq ((evaluated.entries.get p).chartArea -
        FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
          ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) planned.radialDepth i)) ≤
      Aggregate.perTerm arcBudget original.plans.length) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.chartArea -
      arcArea planned) <
      arcBudget := by
  rw [evaluated.chartArea_eq]
  unfold arcArea
  rw [← FiniteSum.Fin.sumFin_sub]
  have bound := Indexed.normSq_sumFin_le
    (fun p : Fin original.plans.length =>
      (evaluated.entries.get p).chartArea -
        FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
          ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) planned.radialDepth i))
    (Aggregate.perTerm arcBudget original.plans.length) each
  refine bound.trans_lt ?_
  have paid := Aggregate.count_mul_perTerm_lt positive original.plans.length
  exact (by ring1 : ((original.plans.length : InverseRootPolynomial.Coordinate)^2 *
      Aggregate.perTerm arcBudget original.plans.length) =
      (original.plans.length : InverseRootPolynomial.Coordinate) *
        ((original.plans.length : InverseRootPolynomial.Coordinate) *
          Aggregate.perTerm arcBudget original.plans.length)).trans_lt paid

/-- The closed physical boundary. The retained chain closes, so the outer radial ends cancel and only the source area
and origin correction remain. The fan closure supplies the physical-arc smallness. -/
theorem Certificate.sourceClosedBoundary_bound {planned :
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest evaluated error floor}
    (certified : Certificate
      planned) {arcBudget : InverseRootPolynomial.Coordinate}
    (chartArc : Data.Gaussian.Norm.Basic.normSq (evaluated.chartArea -
      arcArea planned) ≤ arcBudget)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents
      (start := start) (finish := finish)))
    (closed : start.coordinate = finish.coordinate) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceArea - evaluated.correction) ≤
      2 * (requested + 2 * (arcBudget + error)) := by
  have arcBound := (certified.closed_bounded chain closed).le
  have identity : evaluated.sourceArea - evaluated.correction =
      (evaluated.sourceArea - evaluated.chartArea - evaluated.correction) +
        ((evaluated.chartArea -
          arcArea planned) +
          arcArea planned) := by
    ring1
  have inner : Data.Gaussian.Norm.Basic.normSq ((evaluated.chartArea -
    arcArea planned) +
    arcArea planned) ≤
      2 * (arcBudget + error) :=
    (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct chartArc
        arcBound)
        (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  rw [identity]
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      evaluated.bounded.le inner)
      (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))

end RegularFanRequest

open RegularFanRequest (arcArea Certificate)

/-- Aggregate the requested per-interval arc comparisons of one retained parent into its single
chart-versus-physical-arc budget. The per-interval hypotheses are the `regular_chart_arcs_requested` conclusions; this
packages them for the parent boundary comparison. -/
theorem chartArea_arcArea_aggregate (evaluated : ChartBankRequest.Evaluation request)
    (p : Fin original.plans.length) (radialDepth : Nat)
    (error : InverseRootPolynomial.Coordinate) (positive : 0 < error)
    (each : ∀ i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length),
      Data.Gaussian.Norm.Basic.normSq (ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p)
        radialDepth i -
        ((evaluated.entries.get p).entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea) ≤
      Aggregate.perTerm error ((PairedParentCharts.ChartParent original p).common.intervals.length)) :
    Data.Gaussian.Norm.Basic.normSq ((evaluated.entries.get p).chartArea -
      FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
        ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) radialDepth i)) < error := by
  have flipped : ∀ i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length),
      Data.Gaussian.Norm.Basic.normSq (((evaluated.entries.get p).entries.get
        i).evaluated.chart.retained.area.evaluated.chart.originalArea -
        ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) radialDepth i) ≤
      Aggregate.perTerm error ((PairedParentCharts.ChartParent original p).common.intervals.length) := by
    intro i
    have equal : ((evaluated.entries.get p).entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea -
          ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) radialDepth i =
        -(ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) radialDepth i -
          ((evaluated.entries.get p).entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea) := by
      ring1
    exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_le
      ((le_of_eq (Data.Gaussian.Norm.Basic.normSq_neg _)).trans (each i))
  rw [(evaluated.entries.get p).chartArea_eq, ← FiniteSum.Fin.sumFin_sub]
  have bound := Indexed.normSq_sumFin_le
    (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
      ((evaluated.entries.get p).entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea -
        ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) radialDepth i)
    (Aggregate.perTerm error ((PairedParentCharts.ChartParent original p).common.intervals.length)) flipped
  refine bound.trans_lt ?_
  have paid := Aggregate.count_mul_perTerm_lt positive
    ((PairedParentCharts.ChartParent original p).common.intervals.length)
  exact (by ring1 : (((PairedParentCharts.ChartParent original p).common.intervals.length :
    InverseRootPolynomial.Coordinate)^2 *
      Aggregate.perTerm error ((PairedParentCharts.ChartParent original p).common.intervals.length)) =
      ((PairedParentCharts.ChartParent original p).common.intervals.length : InverseRootPolynomial.Coordinate) *
        (((PairedParentCharts.ChartParent original p).common.intervals.length : InverseRootPolynomial.Coordinate) *
          Aggregate.perTerm error ((PairedParentCharts.ChartParent original p).common.intervals.length))).trans_lt paid

/-- The requested area error of one retained interval is positive. -/
theorem intervalRequested_positive (p : Fin original.plans.length)
    (i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length)) :
    0 < ((request.plans.get p).plans.get i).budget.tolerance / 4 / 4 :=
  Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct
      ((request.plans.get p).plans.get i).budget.positive (by
          decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 4))
    (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 4)

/-- The retained chart target is bounded by the requested area error. -/
theorem intervalTarget_le (p : Fin original.plans.length)
    (i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length)) :
    ((request.plans.get p).plans.get i).request.chart.budget.tolerance ≤
      ((request.plans.get p).plans.get i).budget.tolerance / 4 / 4 := by
  have magnitude : 0 ≤ ((request.plans.get p).plans.get i).request.chart.magnitude :=
    (SourceChartRequest.magnitude_nonnegative ((request.plans.get p).plans.get i).prepared).trans_eq
      ((request.plans.get p).plans.get i).request.chart.magnitude_eq.symm
  have requestedPositive : 0 < (((request.plans.get p).plans.get i).budget.tolerance / 4) / 4 :=
    Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct
        ((request.plans.get p).plans.get i).budget.positive (by
            decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 4))
      (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) < 4)
  have halfLe : ((((request.plans.get p).plans.get i).budget.tolerance / 4) / 4) / 2 ≤
      (((request.plans.get p).plans.get i).budget.tolerance / 4) / 4 := by
    apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)).mpr
    exact (by ring1 : (((request.plans.get p).plans.get i).budget.tolerance / 4) / 4 =
        1 * ((((request.plans.get p).plans.get i).budget.tolerance / 4) / 4)).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (by decide : (1 : InverseRootPolynomial.Coordinate) ≤ 2)
        (Fraction.Order.Field.div_nonneg_direct
          (Fraction.Order.Field.div_nonneg_direct
            ((request.plans.get p).plans.get i).budget.positive.le
            (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 4))
          (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 4))).trans_eq (by ring1))
  exact (((request.plans.get p).plans.get i).request.chart.budget.tolerance_le magnitude
    requestedPositive).trans halfLe

/-- The retained bank index dominates both the chart reading index and the regular slope threshold of every interval. -/
theorem intervalLater (p : Fin original.plans.length)
    (i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length)) :
    max (((request.plans.get p).plans.get i).request.chart.refined.index)
      (ReciprocalRegularCoordinatePolynomial.regularSlopeRequest
        ((request.plans.get p).plans.get i).request.first
        (4 * (((request.plans.get p).plans.get i).request.chart.budget.tolerance))
        (Fraction.Order.Arithmetic.mul_pos_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 4)
          ((request.plans.get p).plans.get i).request.chart.budget.positive)
        minimum).val ≤ request.index := by
  have planIndex : (((request.plans.get p).plans.get i).request.chart.refined.index) ≤
      ((request.plans.get p).plans.get i).request.index := by
    rw [((request.plans.get p).plans.get i).request.index_eq]
    exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)
  have weightIndex : CommonChartBank.planWeight
        regular (PairedParentCharts.ChartParent original p).common i ((request.plans.get p).plans.get i) ≤
      (request.plans.get p).index :=
    ((DependentVector.get_le_maximum
        (CommonChartBank.planWeight regular (PairedParentCharts.ChartParent original p).common)
        (request.plans.get p).plans i).trans
      (Data.Nat.Order.le_max_right _ _)).trans_eq (request.plans.get p).index_eq.symm
  have planIndexLe : ((request.plans.get p).plans.get i).request.index ≤
      (request.plans.get p).index :=
    (CommonChartBank.planWeight_index_le
      (regular := regular) (common := (PairedParentCharts.ChartParent original p).common) i
      ((request.plans.get p).plans.get i)).trans weightIndex
  have bankIndex : (request.plans.get p).index ≤ request.index :=
    ((DependentVector.get_le_maximum (PairedParentCharts.chartIndexWeight original) request.plans p).trans
      (Data.Nat.Order.le_max_right _ _)).trans_eq request.index_eq.symm
  have slopeLe := CommonChartBank.planWeight_slope_le
    (regular := regular) (common := (PairedParentCharts.ChartParent original p).common) i ((request.plans.get
      p).plans.get i)
  refine Data.Nat.Order.max_le ?_ ?_
  · exact planIndex.trans (planIndexLe.trans bankIndex)
  · exact slopeLe.trans (weightIndex.trans bankIndex)

/-- Every retained interval's chart-versus-arc discrepancy is bounded by its concrete budget, with all structural
obligations discharged internally. -/
private theorem chartArea_arcArea_raw_bound (evaluated : ChartBankRequest.Evaluation request)
    (p : Fin original.plans.length)
    (i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length))
    (radialDepth : Nat)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    Data.Gaussian.Norm.Basic.normSq (ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p)
      radialDepth i -
      ((evaluated.entries.get p).entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea) ≤
      (ReciprocalRegularChartFans.chartArcBudget ((request.plans.get p).plans.get i)) :=
  Evaluation.regular_area_perTerm
    (prepared := (((request.plans.get p).plans.get i).request.chart).refined)
    (requested := (((request.plans.get p).plans.get i).budget.tolerance / 4 / 4))
    (sample := (evaluated.entries.get p).samples.firstCap)
    (otherSample := (evaluated.entries.get p).samples.otherCap)
    (first := ((evaluated.entries.get p).entries.get i).first)
    (second := ((evaluated.entries.get p).entries.get i).second)
    (radialDepth := radialDepth)
    ((evaluated.entries.get p).entries.get i).evaluated.chart.retained
    unramified
    ((request.plans.get p).plans.get i).request.chart.budget.positive
    (intervalRequested_positive p i)
      (intervalTarget_le p i) minimum
      (intervalLater p i)
    (le_refl ((ReciprocalRegularChartFans.chartArcBudget ((request.plans.get p).plans.get i))))

/-- One interval of `chartArea_arcArea_aggregate` follows from the concrete budget and the requested share. Only the
numeric split remains. -/
theorem chartArea_arcArea_each (evaluated : ChartBankRequest.Evaluation request)
    (p : Fin original.plans.length)
    (i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length))
    (radialDepth : Nat) (error : InverseRootPolynomial.Coordinate)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (small : (ReciprocalRegularChartFans.chartArcBudget ((request.plans.get p).plans.get i)) ≤
      Aggregate.perTerm error ((PairedParentCharts.ChartParent original p).common.intervals.length)) :
    Data.Gaussian.Norm.Basic.normSq (ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p)
      radialDepth i -
      ((evaluated.entries.get p).entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea) ≤
      Aggregate.perTerm error ((PairedParentCharts.ChartParent original p).common.intervals.length) :=
  (chartArea_arcArea_raw_bound evaluated p i
    radialDepth unramified).trans small

/-- The parent chart-versus-arc budget follows from the per-interval numeric split. All structural obligations are
discharged internally. -/
theorem chartArea_arcArea_aggregate_of_intervals (evaluated : ChartBankRequest.Evaluation request)
    (p : Fin original.plans.length) (radialDepth : Nat)
    (error : InverseRootPolynomial.Coordinate) (positive : 0 < error)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (small : ∀ i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length),
      (ReciprocalRegularChartFans.chartArcBudget ((request.plans.get p).plans.get i)) ≤
        Aggregate.perTerm error ((PairedParentCharts.ChartParent original p).common.intervals.length)) :
    Data.Gaussian.Norm.Basic.normSq ((evaluated.entries.get p).chartArea -
      FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
        ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) radialDepth i)) < error :=
  chartArea_arcArea_aggregate evaluated p radialDepth
    error positive (fun i =>
    chartArea_arcArea_each evaluated p i radialDepth
      error unramified (small i))

/-- A finite sum of pointwise nonnegative rational values is nonnegative. -/
private theorem sumFin_nonnegative {n : Nat} (values : Fin n → InverseRootPolynomial.Coordinate)
    (positive : ∀ i, 0 ≤ values i) : 0 ≤ FiniteSum.Fin.sumFin values := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [FiniteSum.Fin.sumFin_succ]
    exact add_nonneg (positive 0) (ih _ (fun i => positive i.succ))

/-- The original chart/arc discrepancy for one parent is bounded by its squared interval count times the sum of the
actual interval budgets. -/
theorem chartArea_arcArea_aggregate_bound (evaluated : ChartBankRequest.Evaluation request)
    (p : Fin original.plans.length) (radialDepth : Nat)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    Data.Gaussian.Norm.Basic.normSq ((evaluated.entries.get p).chartArea -
      FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
        ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) radialDepth i)) ≤
      (((PairedParentCharts.ChartParent original p).common.intervals.length : InverseRootPolynomial.Coordinate)^2 *
        FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
          ReciprocalRegularChartFans.chartArcBudget
            ((request.plans.get p).plans.get i))) := by
  have each : ∀ i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length),
      Data.Gaussian.Norm.Basic.normSq (((evaluated.entries.get p).entries.get
        i).evaluated.chart.retained.area.evaluated.chart.originalArea -
        ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) radialDepth i) ≤
      ReciprocalRegularChartFans.chartArcBudget
        ((request.plans.get p).plans.get i) := by
    intro i
    have raw := chartArea_arcArea_raw_bound evaluated
      p i radialDepth unramified
    have equal : ((evaluated.entries.get p).entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea -
          ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) radialDepth i =
        -(ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) radialDepth i -
          ((evaluated.entries.get p).entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea) := by
      ring1
    exact (congrArg Data.Gaussian.Norm.Basic.normSq equal).trans_le
      ((le_of_eq (Data.Gaussian.Norm.Basic.normSq_neg _)).trans raw)
  have nonnegative : ∀ i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length),
      0 ≤ ReciprocalRegularChartFans.chartArcBudget
        ((request.plans.get p).plans.get i) := fun i =>
    (Data.Gaussian.Norm.Basic.normSq_nonneg _).trans (each i)
  rw [(evaluated.entries.get p).chartArea_eq, ← FiniteSum.Fin.sumFin_sub]
  exact Indexed.normSq_sumFin_le _ _
    (fun i => (each i).trans (FiniteSum.Fin.Rational.entry_le_sum _ nonnegative i))

/-- The total chart-versus-arc budget follows from the per-interval numeric split alone. Each parent consumes
`chartArea_arcArea_aggregate_of_intervals`. -/
theorem chartArea_arcArea_total_of_intervals {fanFloor : Nat}
    (planned : RegularFanRequest evaluated error
      fanFloor)
    (arcBudget : InverseRootPolynomial.Coordinate) (positive : 0 < arcBudget)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (small : ∀ (p : Fin original.plans.length)
      (i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length)),
      ReciprocalRegularChartFans.chartArcBudget
          ((request.plans.get p).plans.get i) ≤
        Aggregate.perTerm
          (Aggregate.perTerm arcBudget original.plans.length)
          ((PairedParentCharts.ChartParent original p).common.intervals.length)) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.chartArea - arcArea planned) < arcBudget :=
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest.chartArea_arcArea_total planned
    arcBudget positive (fun p =>
    (chartArea_arcArea_aggregate_of_intervals
      evaluated p planned.radialDepth
      (Aggregate.perTerm arcBudget original.plans.length)
      (Aggregate.perTerm_positive positive original.plans.length)
      unramified (small p)).le)

/-- The closed physical boundary bound with the chart-versus-arc budget derived from the actual per-interval numeric
split. No caller `chartArc` hypothesis remains. -/
theorem Certificate.sourceClosedBoundary_bound_of_intervals
    {fanFloor : Nat} {planned : RegularFanRequest
      evaluated error fanFloor}
    (certified : Certificate planned) (arcBudget : InverseRootPolynomial.Coordinate) (positive : 0 < arcBudget)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (small : ∀ (p : Fin original.plans.length)
      (i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length)),
      ReciprocalRegularChartFans.chartArcBudget
          ((request.plans.get p).plans.get i) ≤
        Aggregate.perTerm
          (Aggregate.perTerm arcBudget original.plans.length)
          ((PairedParentCharts.ChartParent original p).common.intervals.length))
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents
      (start := start) (finish := finish)))
    (closed : start.coordinate = finish.coordinate) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceArea - evaluated.correction) ≤
      2 * (requested + 2 * (arcBudget + error)) :=
  certified.sourceClosedBoundary_bound
    (chartArea_arcArea_total_of_intervals evaluated
      planned arcBudget positive unramified small).le chain closed

/-- The original complete chart/arc discrepancy is bounded by the squared parent count times the sum of the retained
squared-count interval budgets. -/
theorem chartArea_arcArea_total_bound {fanFloor : Nat}
    (planned : RegularFanRequest evaluated error
      fanFloor)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.chartArea - arcArea planned) ≤
      ((original.plans.length : InverseRootPolynomial.Coordinate)^2 *
        FiniteSum.Fin.sumFin (fun p : Fin original.plans.length =>
          (((PairedParentCharts.ChartParent original p).common.intervals.length : InverseRootPolynomial.Coordinate)^2 *
            FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
              ReciprocalRegularChartFans.chartArcBudget
                ((request.plans.get p).plans.get i))))) := by
  have each : ∀ p : Fin original.plans.length,
      Data.Gaussian.Norm.Basic.normSq ((evaluated.entries.get p).chartArea -
        FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
          ReciprocalRegularChartFans.regularArcArea (evaluated.entries.get p) planned.radialDepth i)) ≤
      (((PairedParentCharts.ChartParent original p).common.intervals.length : InverseRootPolynomial.Coordinate)^2 *
        FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
          ReciprocalRegularChartFans.chartArcBudget
            ((request.plans.get p).plans.get i))) := fun p =>
    chartArea_arcArea_aggregate_bound evaluated p
      planned.radialDepth unramified
  have nonnegative : ∀ p : Fin original.plans.length,
      0 ≤ (((PairedParentCharts.ChartParent original p).common.intervals.length : InverseRootPolynomial.Coordinate)^2 *
        FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
          ReciprocalRegularChartFans.chartArcBudget
            ((request.plans.get p).plans.get i))) := fun p =>
    (Data.Gaussian.Norm.Basic.normSq_nonneg _).trans (each p)
  rw [evaluated.chartArea_eq]
  unfold Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest.arcArea
  rw [← FiniteSum.Fin.sumFin_sub]
  exact Indexed.normSq_sumFin_le _ _
    (fun p => (each p).trans (FiniteSum.Fin.Rational.entry_le_sum _ nonnegative p))

/-- The closed physical boundary bound with the concrete chart-versus-arc budget. No caller budget or numeric split
hypothesis remains. -/
theorem Certificate.sourceClosedBoundary_bound_concrete {fanFloor : Nat}
    {planned : RegularFanRequest evaluated error
      fanFloor}
    (certified : Certificate planned)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents
      (start := start) (finish := finish)))
    (closed : start.coordinate = finish.coordinate) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceArea - evaluated.correction) ≤
      2 * (requested + 2 *
        (((original.plans.length : InverseRootPolynomial.Coordinate)^2 *
          FiniteSum.Fin.sumFin (fun p : Fin original.plans.length =>
            (((PairedParentCharts.ChartParent original p).common.intervals.length : InverseRootPolynomial.Coordinate)^2
              *
              FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
                ReciprocalRegularChartFans.chartArcBudget
                  ((request.plans.get p).plans.get i))))) + error)) :=
  certified.sourceClosedBoundary_bound
    (chartArea_arcArea_total_bound evaluated planned
      unramified) chain closed

/-- The open physical boundary bound with the concrete chart-versus-arc budget. No caller budget or numeric split
hypothesis remains. -/
theorem Certificate.sourceOpenBoundary_bound_concrete {fanFloor : Nat}
    {planned : RegularFanRequest evaluated error
      fanFloor}
    (certified : Certificate planned)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans.RegularFanRequest.sourceOpenBoundary planned)
      ≤
      2 * (requested + 2 * (error +
        (((original.plans.length : InverseRootPolynomial.Coordinate)^2 *
          FiniteSum.Fin.sumFin (fun p : Fin original.plans.length =>
            (((PairedParentCharts.ChartParent original p).common.intervals.length : InverseRootPolynomial.Coordinate)^2
              *
              FiniteSum.Fin.sumFin (fun i : Fin ((PairedParentCharts.ChartParent original p).common.intervals.length) =>
                ReciprocalRegularChartFans.chartArcBudget
                  ((request.plans.get p).plans.get i)))))))) :=
  certified.sourceOpenBoundary_bound
    (chartArea_arcArea_total_bound evaluated planned
      unramified)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentFans
