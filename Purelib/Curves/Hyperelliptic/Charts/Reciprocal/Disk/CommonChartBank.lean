module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
public import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAdjacency
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitiveReadback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularCoordinatePolynomial
import Init.Data.List.OfFn
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedRootGeometry
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The complete common mesh shares its source, cap and reciprocal primitive
banks. Its count-paid comparison retains every interval correction. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank

open Purelib
open Purelib.Algebra
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonAreaReadback
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartJunctions.SourceChartRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Data.Gaussian.Norm.Sum
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Branches
open Purelib.Riemann.Meshes
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
open Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts.SourceComparisonRequest
open Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts.SourceComparisonRequest.PathReplacement
open Purelib.Riemann.Periods
open Purelib.Topology.Polygon
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover CommonInterval)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths (ChartGeometry)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources (SourceChartRequest)
open Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts (SourceComparisonRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation (IntervalAt ChartPreparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives (SourcePrimitive PrimitiveCells)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus count otherCount : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch
    (Purelib.Riemann.Integration.PreparedEdgeRecasting.recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  (regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (common :
    CommonCover cover otherCover)

set_option genInjectivity false in
/-- A positive local tolerance paying the actual source-path restoration rate.

The tolerance also retains the padded-root ceiling, unit ceiling and original interval allowance. -/
structure RestorationBudget {interval : UniformReciprocalCommonCover.CommonInterval cover otherCover} {depth : Nat}
    {geometry : CommonChartPaths.ChartGeometry (cap := cap) interval depth} {target : InverseRootPolynomial.Coordinate}
      {floor : Nat}
    (prepared : CommonChartSources.SourceChartRequest regular geometry target floor) (allowance :
      InverseRootPolynomial.Coordinate) where
  /-- The cached restoration-rate coefficient of the original source comparison request. -/ rate :
    InverseRootPolynomial.Coordinate
  /-- The cached rate equals the original source request's restoration rate. -/ rate_eq : rate =
    SourceComparisonRequest.restorationRate prepared
  /-- The cached positive local restoration tolerance. -/ tolerance : InverseRootPolynomial.Coordinate
  /-- The tolerance is the minimum of the original padded ceiling, unit ceiling, allowance and weighted half-allowance.
  -/
  tolerance_eq : tolerance = min regular.padded.squareTolerance
    (min 1 (min allowance (Weighted.allowance (allowance / 2) rate)))
  /-- The retained tolerance or interval allowance is strictly positive. -/ positive : 0 < tolerance
  /-- The retained restoration tolerance is at most one. -/ small : tolerance ≤ 1
  /-- The retained restoration tolerance does not exceed its original interval allowance. -/ bounded : tolerance ≤
    allowance
  /-- The retained tolerance satisfies the original padded-root square tolerance. -/ padded_paid : tolerance ≤
    regular.padded.squareTolerance
  /-- The retained restoration-rate cost is strictly below its original interval allowance. -/ paid : rate * tolerance <
    allowance

constructive_injectivity RestorationBudget

/-- Select a positive minimum tolerance satisfying the original padded-root and weighted restoration budgets. -/
@[expose] def RestorationBudget.build {interval : UniformReciprocalCommonCover.CommonInterval cover otherCover} {depth :
  Nat}
    {geometry : CommonChartPaths.ChartGeometry (cap := cap) interval depth} {target : InverseRootPolynomial.Coordinate}
      {floor : Nat}
    (prepared : CommonChartSources.SourceChartRequest regular geometry target floor) (allowance :
      InverseRootPolynomial.Coordinate) (positive : 0 < allowance) :
    RestorationBudget regular prepared allowance := by
  let rate := SourceComparisonRequest.restorationRate prepared
  have nonnegative := SourceComparisonRequest.restorationRate_nonnegative prepared
  have halfPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
  let tolerance := min regular.padded.squareTolerance
    (min 1 (min allowance (Weighted.allowance (allowance / 2) rate)))
  have small : tolerance ≤ 1 := (Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)
  have bounded : tolerance ≤ allowance := (Fraction.Order.Basic.min_le_right _ _).trans
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))
  have allocated : tolerance ≤ Weighted.allowance (allowance / 2) rate :=
    (Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
      (Fraction.Order.Basic.min_le_right _ _))
  have halfEq : allowance / 2 + allowance / 2 = allowance :=
    (by ring1 : allowance / 2 + allowance / 2 = (allowance / 2) * 2).trans
      (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  have halfLess := (Fraction.Field.zero_add _ ▸ Fraction.Order.Arithmetic.add_lt_add_right_direct halfPositive
    _).trans_eq halfEq
  exact ⟨rate, rfl, tolerance, rfl,
    Fraction.Order.Basic.lt_min regular.padded.squareTolerance_positive
      (Fraction.Order.Basic.lt_min (by decide) (Fraction.Order.Basic.lt_min positive (Weighted.allowance_positive
        halfPositive nonnegative))),
    small, bounded, Fraction.Order.Basic.min_le_left _ _,
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct allocated nonnegative).trans
      (Weighted.mul_allowance_le halfPositive.le nonnegative)).trans_lt halfLess⟩

set_option genInjectivity false in
/-- One actual common-cover interval's chart geometry, source preparation and paid restoration request. -/
structure ChartPlan (depth : Nat) (allowance : InverseRootPolynomial.Coordinate) (floor : Nat) (i : Fin
  common.intervals.length) where
  /-- The cached chart geometry on this exact retained common interval and depth. -/ geometry :
    CommonChartPaths.ChartGeometry (cap := cap) (CommonChartPreparation.IntervalAt common i) depth
  /-- The original source-to-chart request on the cached interval geometry. -/ prepared :
    CommonChartSources.SourceChartRequest regular geometry allowance floor
  /-- The retained restoration budget for this exact source preparation. -/ budget :
    RestorationBudget regular prepared allowance
  /-- The source comparison request consuming the original interval preparations and retained tolerance. -/ request :
    ReciprocalDiskCommonSourceCharts.SourceComparisonRequest prepared budget.tolerance

constructive_injectivity ChartPlan

/-- Read a common model stage paying both the original source comparison and its regular coordinate-slope request. -/
@[expose] def planWeight {depth : Nat} {allowance : InverseRootPolynomial.Coordinate} {floor : Nat} (i : Fin
  common.intervals.length)
    (plan : ChartPlan regular common depth allowance floor
      i) : Nat :=
  max plan.request.index
    (ReciprocalRegularCoordinatePolynomial.regularSlopeRequest plan.request.first
      (4 * plan.request.chart.budget.tolerance)
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 4)
        plan.request.chart.budget.positive)
      floor).val

/-- The original interval comparison stage is below its retained combined model weight. -/
theorem planWeight_index_le {depth : Nat} {allowance : InverseRootPolynomial.Coordinate} {floor : Nat}
    (i : Fin common.intervals.length) (plan : ChartPlan
      regular common depth allowance floor i) :
    plan.request.index ≤ planWeight regular common i plan :=
      by
  rw [planWeight]
  exact Data.Nat.Order.le_max_left _ _

/-- The retained regular-slope request stage is below the same combined model weight. -/
theorem planWeight_slope_le {depth : Nat} {allowance : InverseRootPolynomial.Coordinate} {floor : Nat}
    (i : Fin common.intervals.length) (plan : ChartPlan
      regular common depth allowance floor i) :
    (ReciprocalRegularCoordinatePolynomial.regularSlopeRequest plan.request.first
      (4 * plan.request.chart.budget.tolerance)
      (Fraction.Order.Arithmetic.mul_pos_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 4)
        plan.request.chart.budget.positive)
      floor).val ≤ planWeight regular common i plan := by
  rw [planWeight]
  exact Data.Nat.Order.le_max_right _ _

/-- The bounded original left interval index of a retained adjacent junction. -/
@[expose] def junctionLeft (i : Fin (common.intervals.length - 1)) : Fin common.intervals.length := ⟨i.val, by omega0⟩

/-- The bounded original right interval index of a retained adjacent junction. -/
@[expose] def junctionRight (i : Fin (common.intervals.length - 1)) : Fin common.intervals.length := ⟨i.val + 1, by
  omega0⟩

/-- The actual adjacent-chart junction request between the retained original interval plans. -/
@[expose] def ChartJunctionAt {depth : Nat} {allowance : InverseRootPolynomial.Coordinate} {floor : Nat}
    (plans : Data.Vector.DependentVector (ChartPlan regular
      common depth allowance floor))
    (i : Fin (common.intervals.length - 1)) :=
  SourceChartRequest.JunctionRequest (plans.get
    (junctionLeft common i)).prepared
    (plans.get (junctionRight common i)).geometry (allowance
      / 16) floor

/-- Read the sufficient stage of the actual retained junction request. -/
@[expose] def junctionWeight {depth : Nat} {allowance : InverseRootPolynomial.Coordinate} {floor : Nat}
    (plans : Data.Vector.DependentVector (ChartPlan regular
      common depth allowance floor))
    (i : Fin (common.intervals.length - 1)) (junction :
      ChartJunctionAt regular common plans i) : Nat :=
      junction.index

set_option genInjectivity false in
/-- The complete original common-cover chart request bank with paid interval and join allowances.

The retained preparation, interval plans and actual adjacent junctions determine model and reading maxima before
numerical acquisition. -/
structure ChartRequest (depth : Nat) (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original complete retained chart preparation on this common cover. -/ preparation :
    CommonChartPreparation.ChartPreparation regular common
  /-- The cached path-replacement join budget for the actual common interval count. -/ joinBudget :
    PathReplacement.JoinBudget common.intervals.length target
  /-- The cached positive per-interval allowance. -/ allowance : InverseRootPolynomial.Coordinate
  /-- The interval allowance is exactly that retained by the original join budget. -/ allowance_eq : allowance =
    joinBudget.allowance
  /-- The retained tolerance or interval allowance is strictly positive. -/ positive : 0 < allowance
  /-- The actual common interval count squared times the retained allowance is strictly below the original target. -/
    paid : (common.intervals.length : InverseRootPolynomial.Coordinate) * ((common.intervals.length :
    InverseRootPolynomial.Coordinate) * allowance) < target
  /-- The dependent vector of plans on every actual original common interval. -/ plans : Data.Vector.DependentVector
    (ChartPlan regular common depth allowance floor)
  /-- Both comparison owners in every actual interval plan are exactly the original prepared entries. -/ comparisons_eq
    : ∀ i, (plans.get i).request.first = (preparation.entries.get i).first ∧
    (plans.get i).request.second = (preparation.entries.get i).second
  /-- The dependent vector of requests on every actual adjacent interval junction. -/ junctions :
    Data.Vector.DependentVector (ChartJunctionAt regular
    common plans)
  /-- The cached common reading-stage floor paying every original junction request. -/ readingFloor : Nat
  /-- The reading floor is exactly the maximum of the original caller floor and all retained junction stages. -/
    readingFloor_eq : readingFloor = max floor (junctions.maximum
    (junctionWeight regular common plans))
  /-- The cached sufficient common model stage. -/ index : Nat
  /-- The model stage is exactly the maximum of the caller floor and all retained interval weights. -/ index_eq : index
    = max floor (plans.maximum (planWeight regular common))

constructive_injectivity ChartRequest

namespace ChartRequest

/-- Cache all original interval geometries, comparison plans and adjacent junction requests before selecting their exact
common stages. -/
@[expose] def build (preparation : CommonChartPreparation.ChartPreparation regular common) (depth : Nat) (target :
  InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest regular common depth target floor :=
  let joinBudget := JoinBudget.build common.intervals.length target positive
  let allowance := joinBudget.allowance
  have allowancePositive := joinBudget.positive
  let plans := DependentVector.ofFn (fun i =>
    let geometry := ChartGeometry.build (cap := cap) (CommonChartPreparation.IntervalAt common i) depth
    let prepared := SourceChartRequest.build regular geometry allowance allowancePositive floor
    let budget := Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.RestorationBudget.build regular prepared
      allowance allowancePositive
    (⟨geometry, prepared, budget, SourceComparisonRequest.build prepared
      (preparation.entries.get i).first (preparation.entries.get i).second budget.tolerance budget.positive⟩ :
        Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartPlan regular common depth allowance floor i))
  have comparisons : ∀ i, (plans.get i).request.first = (preparation.entries.get i).first ∧
      (plans.get i).request.second = (preparation.entries.get i).second := by
    intro i
    dsimp only [plans, -eq_self, -iff_self]
    rw [DependentVector.ofFn_get]
    exact ⟨rfl, rfl⟩
  let junctions := DependentVector.ofFn (fun i =>
    JunctionRequest.build (plans.get (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.junctionLeft common
      i)).prepared
      (plans.get (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.junctionRight common i)).geometry
      (common.adjacent i.val (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.junctionRight common i).isLt)
        (allowance / 16)
      (Fraction.Order.Field.div_pos_direct allowancePositive (by decide +kernel)) floor)
  ⟨preparation, joinBudget, allowance, rfl, allowancePositive, joinBudget.count_paid,
    plans, comparisons, junctions, max floor (junctions.maximum
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.junctionWeight regular common plans)), rfl,
    max floor (plans.maximum (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.planWeight regular common)),
      rfl⟩

end ChartRequest

set_option genInjectivity false in
/-- The original paired source and cap samples with both complete primitive-cell banks at one common model stage. -/
structure SampleBank (index : Nat) where
  /-- The first original source primitive at the retained common model stage. -/ source :
    UniformReciprocalPrimitives.SourcePrimitive data index
  /-- The second original source primitive at that same model stage. -/ otherSource :
    UniformReciprocalPrimitives.SourcePrimitive otherData index
  /-- The retained cap polynomial sample for the first original differential. -/ firstCap : Primitives.Sample cap
    differential index collar.box
  /-- The retained cap polynomial sample for the second original differential. -/ otherCap : Primitives.Sample cap other
    index collar.box
  /-- The actual primitive-cell bank on the first original cover mesh. -/ firstCells :
    UniformReciprocalPrimitives.PrimitiveCells data index cover.mesh.edges
  /-- The actual primitive-cell bank on the second original cover mesh. -/ secondCells :
    UniformReciprocalPrimitives.PrimitiveCells otherData index otherCover.mesh.edges

constructive_injectivity SampleBank

/-- Retain the supplied paired cap samples and cache both original source and primitive-cell banks at their shared
stage. -/
@[expose] def SampleBank.ofCapSamples {index : Nat}
    (firstCap : Primitives.Sample cap differential index collar.box)
    (otherCap : Primitives.Sample cap other index collar.box) :
    SampleBank (cap := cap) (cover := cover) (otherCover :=
      otherCover) index :=
  ⟨SourcePrimitive.build data index, SourcePrimitive.build otherData index,
    firstCap, otherCap,
    PrimitiveCells.build index cover.cells, PrimitiveCells.build index otherCover.cells⟩

variable {regular common} {depth floor index : Nat} {target allowance :
  Coordinate}

set_option genInjectivity false in
/-- The actual paired interval samples and source comparison consuming the shared retained sample bank. -/
structure ChartEntry (samples : SampleBank (cap := cap)
  (cover := cover) (otherCover := otherCover) index)
    {i : Fin common.intervals.length} (plan : ChartPlan
      regular common depth allowance floor i) (readingFloor : Nat) where
  /-- The original first interval sample on the retained first cap polynomial. -/ first : ArcSamples.Sample
    plan.request.first samples.firstCap
  /-- The original second interval sample on the retained second cap polynomial. -/ second : ArcSamples.Sample
    plan.request.second samples.otherCap
  /-- The cached comparison using these exact original interval and source samples. -/ evaluated :
    SourceComparisonRequest.Evaluation plan.request samples.source samples.otherSource first second
  /-- The actual refined chart reading stage meets its retained floor. -/ readingLater : readingFloor ≤
    evaluated.chart.retained.area.refined.stage

constructive_injectivity ChartEntry

/-- Reuse the actual retained source-cell and cap samples to cache this original interval comparison. -/
@[expose] def ChartEntry.build (samples : SampleBank (cap :=
  cap) (cover := cover) (otherCover := otherCover) index)
    {i : Fin common.intervals.length} (plan : ChartPlan
      regular common depth allowance floor i)
    (later : plan.request.index ≤ index) (readingFloor : Nat) :
      ChartEntry samples plan readingFloor :=
  let interval := CommonChartPreparation.IntervalAt common i
  let firstRead := samples.firstCells.readCell interval.first.cell interval.first.member
  let secondRead := samples.secondCells.readCell interval.second.cell interval.second.member
  let first := ArcSamples.Sample.ofPrimitive plan.request.first samples.firstCap firstRead.primitive firstRead.cell_eq
  let second := ArcSamples.Sample.ofPrimitive plan.request.second samples.otherCap secondRead.primitive
    secondRead.cell_eq
  let evaluated := plan.request.evaluate samples.source samples.otherSource first second later readingFloor
  ⟨first, second, evaluated, evaluated.chart.retained.readingFloor_le⟩

namespace ChartRequest
variable (request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest regular common
  depth target floor)

/-- The dependent bank of actual interval comparisons consuming one retained shared sample bank. -/
@[expose] def Entries (samples : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.SampleBank (cap := cap)
  (cover := cover) (otherCover := otherCover) index) :=
  Data.Vector.DependentVector (fun i => Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartEntry samples
    (request.plans.get i) request.readingFloor)

/-- Evaluate every actual interval from the supplied shared sample bank above both original request and external reading
floors. -/
@[expose] def acquireEntries (samples : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.SampleBank (cap :=
  cap) (cover := cover) (otherCover := otherCover) index)
    (later : request.index ≤ index) (externalFloor : Nat) : request.Entries samples :=
  DependentVector.ofFn (fun i =>
    let entry := Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartEntry.build samples (request.plans.get
      i)
      ((Data.Nat.Order.le_max_left _ _).trans
        ((DependentVector.get_le_maximum (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.planWeight regular
          common) request.plans i).trans
          (((Data.Nat.Order.le_max_right _ _).trans_eq request.index_eq.symm).trans later))) (max request.readingFloor
            externalFloor)
    ⟨entry.first, entry.second, entry.evaluated, (Data.Nat.Order.le_max_left _ _).trans entry.readingLater⟩)

/-- Every actual retained interval reading meets the supplied external stage floor. -/
@[expose] def ReadingsLater (samples : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.SampleBank (cap :=
  cap) (cover := cover) (otherCover := otherCover) index)
    (entries : request.Entries samples) (externalFloor : Nat) : Prop :=
  ∀ i, externalFloor ≤ (entries.get i).evaluated.chart.retained.area.refined.stage

/-- All acquired actual interval readings respect the retained external stage floor. -/
theorem acquireEntries_later (samples : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.SampleBank (cap :=
  cap) (cover := cover) (otherCover := otherCover) index)
    (later : request.index ≤ index) (externalFloor : Nat) :
    request.ReadingsLater samples (request.acquireEntries samples later externalFloor) externalFloor := by
  intro i
  dsimp only [acquireEntries, -eq_self,
    -iff_self]
  rw [DependentVector.ofFn_get]
  exact (Data.Nat.Order.le_max_right _ _).trans
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartEntry.build samples (request.plans.get i)
    ((Data.Nat.Order.le_max_left _ _).trans
      ((DependentVector.get_le_maximum (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.planWeight regular
        common) request.plans i).trans
        (((Data.Nat.Order.le_max_right _ _).trans_eq request.index_eq.symm).trans later)))
    (max request.readingFloor externalFloor)).readingLater

set_option genInjectivity false in
/-- The complete paired common-chart evaluation with cached finite area sums and paid discrepancies.

The same original source and cap samples feed every retained interval; both centered and uncentered sums retain their
exact correction readbacks. -/
structure Evaluation (index : Nat) where
  /-- The actual common model stage meets the original complete chart request. -/ later : request.index ≤ index
  /-- The exact shared original source and cap sample bank consumed by every interval. -/ samples :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.SampleBank (cap := cap) (cover := cover) (otherCover :=
    otherCover) index
  /-- The cached actual interval comparisons on this retained sample bank. -/ entries : request.Entries samples
  /-- The retained caller-supplied lower reading stage. -/ externalFloor : Nat
  /-- Every actual cached interval reading meets the retained external floor. -/ readingsLater : request.ReadingsLater
    samples entries externalFloor
  /-- The cached sum of the actual original interval source areas. -/ sourceArea : InverseRootPolynomial.Gaussian
  /-- The source-area cache equals the complete finite sum of retained interval source areas. -/ sourceArea_eq :
    sourceArea = FiniteSum.Fin.sumFin (fun i => (entries.get i).evaluated.sourceArea)
  /-- The cached sum of actual original interval chart areas. -/ chartArea : InverseRootPolynomial.Gaussian
  /-- The chart-area cache equals the complete finite sum of retained uncentered chart areas. -/ chartArea_eq :
    chartArea = FiniteSum.Fin.sumFin (fun i => (entries.get
    i).evaluated.chart.retained.area.evaluated.chart.originalArea)
  /-- The cached sum of all actual interval restoration corrections. -/ correction : InverseRootPolynomial.Gaussian
  /-- The correction cache equals the complete finite sum of original retained corrections. -/ correction_eq :
    correction = FiniteSum.Fin.sumFin (fun i => (entries.get i).evaluated.correction)
  /-- The complete original source area minus chart area and retained correction satisfies the requested squared-norm
    target. -/ bounded : Data.Gaussian.Norm.Basic.normSq (sourceArea - chartArea - correction) < target
  /-- The cached sum of actual locally centered source areas. -/ sourceCenteredArea : InverseRootPolynomial.Gaussian
  /-- The centered-source cache equals the complete finite sum of original interval centered areas. -/
    sourceCenteredArea_eq : sourceCenteredArea = FiniteSum.Fin.sumFin (fun i => (entries.get
    i).evaluated.sourceCenteredArea)
  /-- The cached sum of actual locally centered chart areas. -/ chartCenteredArea : InverseRootPolynomial.Gaussian
  /-- The centered-chart cache equals the complete finite sum of original interval centered areas. -/
    chartCenteredArea_eq : chartCenteredArea = FiniteSum.Fin.sumFin (fun i => (entries.get
    i).evaluated.chart.retained.area.evaluated.chart.centeredArea)
  /-- The actual centered source and chart sums satisfy the original complete target. -/ centered_bounded :
    Data.Gaussian.Norm.Basic.normSq (sourceCenteredArea - chartCenteredArea) < target

constructive_injectivity Evaluation

/-- A parent comparison consumes the already selected shared sample bank at any certified later stage, without
rebuilding its cap polynomials. -/
@[expose] def evaluate (samples : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.SampleBank (cap := cap)
  (cover := cover) (otherCover := otherCover) index)
    (later : request.index ≤ index) (externalFloor : Nat) :
      Evaluation request index := by
  let entries := request.acquireEntries samples later externalFloor
  let sourceArea := FiniteSum.Fin.sumFin (fun i => (entries.get i).evaluated.sourceArea)
  let chartArea := FiniteSum.Fin.sumFin (fun i => (entries.get
    i).evaluated.chart.retained.area.evaluated.chart.originalArea)
  let correction := FiniteSum.Fin.sumFin (fun i => (entries.get i).evaluated.correction)
  have estimate := Indexed.normSq_sumFin_le
    (fun i => (entries.get i).evaluated.sourceArea -
      (entries.get i).evaluated.chart.retained.area.evaluated.chart.originalArea - (entries.get i).evaluated.correction)
    request.allowance (fun i => ((entries.get i).evaluated.bounded.trans_le (request.plans.get i).budget.bounded).le)
  rw [FiniteSum.Fin.sumFin_sub, FiniteSum.Fin.sumFin_sub] at estimate
  have paid : (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * request.allowance < target :=
    (by ring1 : (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * request.allowance =
      (common.intervals.length : InverseRootPolynomial.Coordinate) * ((common.intervals.length :
        InverseRootPolynomial.Coordinate) * request.allowance)).trans_lt request.paid
  let sourceCenteredArea := FiniteSum.Fin.sumFin (fun i => (entries.get i).evaluated.sourceCenteredArea)
  let chartCenteredArea := FiniteSum.Fin.sumFin (fun i => (entries.get
    i).evaluated.chart.retained.area.evaluated.chart.centeredArea)
  have centered := Indexed.normSq_sumFin_le
    (fun i => (entries.get i).evaluated.sourceCenteredArea - (entries.get
      i).evaluated.chart.retained.area.evaluated.chart.centeredArea)
    request.allowance (fun i => ((entries.get i).evaluated.centered_bounded.trans_le (request.plans.get
      i).budget.bounded).le)
  rw [FiniteSum.Fin.sumFin_sub] at centered
  exact ⟨later, samples, entries, externalFloor, request.acquireEntries_later samples later externalFloor,
    sourceArea, rfl, chartArea, rfl, correction, rfl, estimate.trans_lt paid,
    sourceCenteredArea, rfl, chartCenteredArea, rfl, centered.trans_lt paid⟩

/-- Evaluation retains exactly the supplied original shared sample bank. -/
theorem evaluate_samples (samples : Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.SampleBank (cap := cap)
  (cover := cover) (otherCover := otherCover) index)
    (later : request.index ≤ index) (externalFloor : Nat) : (request.evaluate samples later externalFloor).samples =
      samples := rfl

/-- Build both cap samples once at the retained common stage and evaluate the complete original chart request. -/
@[expose] def acquire : Evaluation request
  request.index :=
  let firstCap := Primitives.Sample.build cap differential request.index collar.box
  let otherCap := Primitives.Sample.build cap other request.index collar.box
  request.evaluate (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.SampleBank.ofCapSamples (cover := cover)
    (otherCover := otherCover) firstCap otherCap) le_rfl 0

/-- The complete finite indexed sum equals the Gaussian sum of the actual ordered list readings. -/
private theorem sum_get {α : Type} (values : α → InverseRootPolynomial.Gaussian) (entries : List α) :
    FiniteSum.Fin.sumFin (fun i : Fin entries.length => values (entries[i.val]'i.isLt)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map values) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    rw [FiniteSum.Fin.sumFin_succ]
    change values head + FiniteSum.Fin.sumFin (fun i : Fin tail.length => values (tail[i.val]'i.isLt)) =
      values head + Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.map values)
    exact congrArg (fun value => values head + value) ih

/-- Mapping actual common intervals to their retained edges preserves the corresponding Gaussian sum. -/
private theorem sum_edges (values : ClearSheetContinuation.Subdivision.ParameterEdge → InverseRootPolynomial.Gaussian)
    (entries : List (UniformReciprocalCommonCover.CommonInterval cover otherCover)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun interval => values interval.edge)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((entries.map CommonInterval.edge).map values) := by
  induction entries with
  | nil => rfl
  | cons head tail ih => exact congrArg (fun value => values head.edge + value) ih

/-- The complete actual common-interval area sum equals the full original parent trace at the combined coarse and fine
depths. -/
private theorem sum_interval_areas (values : InverseRootPolynomial.Coordinate → Stokes.PrimitivePoint)
    (traceDepth : Nat) :
    FiniteSum.Fin.sumFin (fun i : Fin common.intervals.length => DyadicBilinearBoundaryRibbon.dyadicArea values
      traceDepth (CommonChartPreparation.IntervalAt common i).edge.left.parameter (CommonChartPreparation.IntervalAt
        common i).edge.right.parameter) =
      DyadicBilinearBoundaryRibbon.dyadicArea values (common.depth + traceDepth) 0 1 := by
  dsimp only [CommonChartPreparation.IntervalAt, -eq_self, -iff_self]
  rw [sum_get (fun interval :
    UniformReciprocalCommonCover.CommonInterval cover otherCover =>
    DyadicBilinearBoundaryRibbon.dyadicArea values
      traceDepth interval.edge.left.parameter interval.edge.right.parameter) common.intervals]
  rw [sum_edges (fun edge =>
    DyadicBilinearBoundaryRibbon.dyadicArea values
    traceDepth edge.left.parameter edge.right.parameter) common.intervals, common.edges_eq]
  exact Bilinear.dyadicEdges_sum_area _ common.depth traceDepth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint

/-- The source total is the entire original parent trace, not a selected subfamily. Completeness comes from the common
cover's exact edge list. -/
theorem Evaluation.sourceArea_full (evaluated :
  Evaluation request index) :
    evaluated.sourceArea = DyadicBilinearBoundaryRibbon.dyadicArea
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
      (common.depth + depth) 0 1 := by
  rw [evaluated.sourceArea_eq]
  have each (i : Fin common.intervals.length) := (evaluated.entries.get i).evaluated.sourceArea_eq
  rw [FiniteSum.Fin.sumFin_congr each]
  exact sum_interval_areas _ _

/-- Local centering removes precisely the common mesh's coarse polygon, not the full parent area. Its cross-interval
contribution remains explicit. -/
theorem Evaluation.sourceCenteredArea_full (evaluated :
  Evaluation request index) :
    evaluated.sourceCenteredArea = evaluated.sourceArea - DyadicBilinearBoundaryRibbon.dyadicArea
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
      common.depth 0 1 := by
  rw [evaluated.sourceCenteredArea_eq]
  have each (i : Fin common.intervals.length) :=
    (evaluated.entries.get i).evaluated.source_centered_decomposition
  rw [FiniteSum.Fin.sumFin_congr each, FiniteSum.Fin.sumFin_sub, ← evaluated.sourceArea_eq,
    sum_interval_areas, Nat.add_zero]

/-- Subtracting the actual coarse source polygon leaves a full centered-chart discrepancy below the original target. -/
theorem Evaluation.full_centered_bounded (evaluated :
  Evaluation request index) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicArea
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
      (common.depth + depth) 0 1 -
      DyadicBilinearBoundaryRibbon.dyadicArea
        (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
        common.depth 0 1 - evaluated.chartCenteredArea) < target := by
  rw [← evaluated.sourceArea_full, ← evaluated.sourceCenteredArea_full]
  exact evaluated.centered_bounded

/-- Read the coarse polygon from retained areas, without resampling or reevaluating the source polynomial on the coarse
mesh. -/
@[expose] def Evaluation.coarseSourceArea (evaluated :
  Evaluation request index) : Gaussian :=
  evaluated.sourceArea - evaluated.sourceCenteredArea

/-- The coarse area read from cached differences equals the original source polygon at the retained common-cover depth.
-/
theorem Evaluation.coarseSourceArea_eq (evaluated :
  Evaluation request index) :
    evaluated.coarseSourceArea = DyadicBilinearBoundaryRibbon.dyadicArea
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
      common.depth 0 1 := by
  unfold CommonChartBank.ChartRequest.Evaluation.coarseSourceArea
  rw [evaluated.sourceCenteredArea_full]
  ring1

/-- The full original parent source area, retained chart sum and actual restoration correction satisfy the original
target. -/
theorem Evaluation.full_bounded (evaluated :
  Evaluation request index) :
    Data.Gaussian.Norm.Basic.normSq (DyadicBilinearBoundaryRibbon.dyadicArea
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
      (common.depth + depth) 0 1 - evaluated.chartArea - evaluated.correction) < target := by
  rw [← evaluated.sourceArea_full]
  exact evaluated.bounded

/-- Read every actual original common-interval paired increment block in retained index order. -/
@[expose] def Evaluation.sourceBlocks (evaluated :
  Evaluation request index) :=
  List.ofFn (fun i : Fin common.intervals.length => DyadicPairedPrimitivePaths.increments
    (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
    depth (CommonChartPreparation.IntervalAt common i).edge.left.parameter (CommonChartPreparation.IntervalAt common
      i).edge.right.parameter)

/-- Every restored interval is joined in the retained common-cover order. The summary composes cached totals and areas,
including all cross terms. -/
@[expose] def Evaluation.joinedCharts (evaluated :
  Evaluation request index) :
    SourceComparisonRequest.PathReplacement evaluated.sourceBlocks.flatten :=
  PathReplacement.join _ (fun i => (evaluated.entries.get i).evaluated.sourceReplacement)

/-- Each actual interval replacement bound is strictly below its original retained allowance. -/
theorem Evaluation.localRestoration_paid (evaluated :
  Evaluation request index) (i : Fin
  common.intervals.length) :
    (evaluated.entries.get i).evaluated.sourceReplacement.bound < request.allowance := by
  have bound := Evaluation.sourceReplacement_bound _ _ _ _ _
    (evaluated.entries.get i).evaluated (request.plans.get i).budget.positive (request.plans.get i).budget.small
  rw [← (request.plans.get i).budget.rate_eq] at bound
  exact bound.trans_lt (request.plans.get i).budget.paid

/-- The complete retained join bound is strictly below the original parent target. -/
theorem Evaluation.joinedCharts_paid (evaluated :
  Evaluation request index) :
  evaluated.joinedCharts.bound < target := by
  have bound := PathReplacement.join_bound _
    (fun i => (evaluated.entries.get i).evaluated.sourceReplacement) (fun i =>
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.Evaluation.localRestoration_paid request
      evaluated i).le)
  have paid := (congrArg₂ (fun a b : InverseRootPolynomial.Coordinate => a * b) request.joinBudget.rate_eq.symm
    request.allowance_eq).trans_lt
    request.joinBudget.join_paid
  exact bound.trans_lt paid

/-- Flattening all actual retained source blocks gives the exact full original parent increment list. -/
theorem Evaluation.sourceBlocks_full (evaluated :
  Evaluation request index) :
    evaluated.sourceBlocks.flatten = DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
      (common.depth + depth) 0 1 := by
  let values := CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource
  let read := fun interval : UniformReciprocalCommonCover.CommonInterval cover otherCover =>
    DyadicPairedPrimitivePaths.increments values
    depth interval.edge.left.parameter interval.edge.right.parameter
  have mapped : List.ofFn (fun i : Fin common.intervals.length => read (common.intervals[i.val]'i.isLt)) =
      common.intervals.map read :=
    (OfFn.Basic.map_ofFn (transform := read)
      (function := fun i : Fin common.intervals.length => common.intervals[i.val]'i.isLt)).symm.trans
      (congrArg (List.map read) (OfFn.Basic.ofFn_getElem common.intervals))
  change (List.ofFn (fun i : Fin common.intervals.length => read (common.intervals[i.val]'i.isLt))).flatten = _
  rw [mapped]
  have edges : common.intervals.map read = (common.intervals.map CommonInterval.edge).map
      (fun edge => DyadicPairedPrimitivePaths.increments values depth edge.left.parameter edge.right.parameter) := by
    rw [Data.List.Map.map_map]
    rfl
  rw [edges, common.edges_eq]
  exact Bilinear.dyadicEdges_flatten_increments values common.depth depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint

/-- The restored joined chart total is exactly the original complete parent source increment total. -/
theorem Evaluation.joinedCharts_total (evaluated :
  Evaluation request index) :
    evaluated.joinedCharts.chart.totalValue = PairedIncrementArea.total (DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
      (common.depth + depth) 0 1) := by
  rw [evaluated.joinedCharts.total_eq, evaluated.joinedCharts.source.total_eq, evaluated.sourceBlocks_full]

/-- The actual complete source-area discrepancy satisfies the retained joined-chart bound. -/
theorem Evaluation.joinedCharts_bounded (evaluated :
  Evaluation request index) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
      (common.depth + depth) 0 1) - evaluated.joinedCharts.chart.areaValue) ≤ evaluated.joinedCharts.bound := by
  rw [← evaluated.sourceBlocks_full, ← evaluated.joinedCharts.source.area_eq]
  exact evaluated.joinedCharts.bounded

/-- The actual complete source and restored joined-chart areas satisfy the original requested target. -/
theorem Evaluation.joinedCharts_accurate (evaluated :
  Evaluation request index) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
      (common.depth + depth) 0 1) - evaluated.joinedCharts.chart.areaValue) < target :=
  (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.Evaluation.joinedCharts_bounded request
    evaluated).trans_lt
    (Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest.Evaluation.joinedCharts_paid request
    evaluated)

end ChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
