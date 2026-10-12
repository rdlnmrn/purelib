module
import Purelib.Data.Gaussian.Norm.Sum.Indexed
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
public import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
public import Purelib.Integration.Path.PairedBlockComparison
import Init.Data.List.OfFn
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

public section

/-! Compare the full cumulative source and unmodified chart paths. The
polygon of interval totals is paid, rather than hidden in origin corrections. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas.SourceAreaRequest.Evaluation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonFamily
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
open Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts.SourceComparisonRequest
open Purelib.Riemann.Periods
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Topology.Polygon
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank (ChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank.ChartRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation (IntervalAt)
open Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts (SourceComparisonRequest)
variable {genus count otherCount depth floor index : Nat} {curve : HyperellipticCurve
  genus}
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
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {common :
    CommonCover cover otherCover}
  {target : Coordinate} {request :
    ChartRequest regular common depth target floor}
  (evaluated : ChartRequest.Evaluation request
    index)

/-- The actual original source increment block on the selected retained common-cover interval. -/
@[expose] def SourceBlock (i : Fin common.intervals.length) := DyadicPairedPrimitivePaths.increments
  (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
  depth (CommonChartPreparation.IntervalAt common i).edge.left.parameter (CommonChartPreparation.IntervalAt common
    i).edge.right.parameter

/-- The actual unmodified chart increment block cached for that same original interval. -/
@[expose] def ChartBlock (i : Fin common.intervals.length) :=
  CenteredPathIncrements.Sample.increments
    (evaluated.entries.get i).evaluated.chart.retained.area.evaluated.chart

/-- The original interval chart's retained increment comparison data. -/
@[expose] def IncrementData (i : Fin common.intervals.length) := (evaluated.entries.get i).evaluated.chart.Increments

set_option genInjectivity false in
/-- A paired source/chart interval comparison with cached summaries, discrepancy and magnitude bounds.

The actual paths retain their original increments and area values; both component totals satisfy the same retained error
and magnitude bounds. -/
structure BlockComparison (i : Fin common.intervals.length) where
  /-- The actual retained chart increment comparison on this original interval. -/ increments :
    (IncrementData evaluated) i
  /-- The cached exact increment and area summary of this original source block. -/ source : PairedIncrementArea.Summary
    ((SourceBlock evaluated) i)
  /-- The cached exact increment and area summary of this original chart block. -/ chart : PairedIncrementArea.Summary
    ((ChartBlock evaluated) i)
  /-- The actual source/chart area discrepancy satisfies the original interval tolerance. -/ area_bounded :
    Data.Gaussian.Norm.Basic.normSq (source.areaValue - chart.areaValue) < (request.plans.get
    i).budget.tolerance
  /-- The cached total discrepancy allowance combining original source and chart increment errors. -/ error :
    InverseRootPolynomial.Coordinate
  /-- The allowance is exactly twice the sum of the original source and retained chart increment errors. -/ error_eq :
    error = 2 * (SourceComparisonRequest.incrementError (index := index) (request.plans.get i).request +
    increments.error)
  /-- Both actual source-minus-chart total components satisfy the retained interval error. -/ total_bounded :
    PrimitivePoint.Bounded (source.totalValue.sub chart.totalValue) error
  /-- The retained squared-norm total-error allowance is nonnegative. -/ error_nonnegative : 0 ≤ error
  /-- The cached common total magnitude allowance for this actual source/chart interval. -/ magnitude :
    InverseRootPolynomial.Coordinate
  /-- The magnitude cache is exactly twice the original source-slope sum plus retained error. -/ magnitude_eq :
    magnitude = 2 * (data.sourceSlope + otherData.sourceSlope + error)
  /-- The retained common squared-norm magnitude allowance is nonnegative. -/ magnitude_nonnegative : 0 ≤ magnitude
  /-- Both components of the actual source total satisfy the retained common magnitude bound. -/ source_bounded :
    PrimitivePoint.Bounded source.totalValue magnitude
  /-- Both components of the actual chart total satisfy that same common magnitude bound. -/ chart_bounded :
    PrimitivePoint.Bounded chart.totalValue magnitude

constructive_injectivity BlockComparison

/-- Cache the actual source and chart summaries and derive their retained interval area, total and magnitude bounds. -/
@[expose] def blockComparison (i : Fin common.intervals.length) :
  (BlockComparison evaluated) i := by
  let entry := (evaluated.entries.get i).evaluated
  let increments := entry.chart.increments
  let sourceTotal := SourceComparisonRequest.sourceIncrement (interval := CommonChartPreparation.IntervalAt common i)
    evaluated.samples.source evaluated.samples.otherSource
  let chart := entry.chart.retained.area.evaluated.chart
  have chartTotal : increments.chart = PairedIncrementArea.total (CenteredPathIncrements.Sample.increments chart) := by
    rw [increments.chart_eq, (CenteredPathIncrements.Sample.increments_total chart), chart.centered_eq]
  let source : PairedIncrementArea.Summary
    ((SourceBlock evaluated) i) :=
    ⟨sourceTotal, (DyadicPairedPrimitivePaths.increments_total _ _ _ _).symm,
      entry.sourceCenteredArea, by
        unfold SourceBlock
        rw [DyadicPairedPrimitivePaths.increments_area, ← DyadicBilinearBoundaryRibbon.dyadicArea_zero,
          ← entry.sourceArea_eq, ← entry.source_centered_decomposition]⟩
  let capSummary : PairedIncrementArea.Summary
    ((ChartBlock evaluated) i) :=
    ⟨increments.chart, chartTotal, chart.centeredArea, (CenteredPathIncrements.Sample.increments_area chart).symm⟩
  let error := 2 * (SourceComparisonRequest.incrementError (index := index) (request.plans.get i).request +
    increments.error)
  have before := Evaluation.source_increment_error (request.plans.get i).request
    evaluated.samples.source evaluated.samples.otherSource (evaluated.entries.get i).first (evaluated.entries.get
      i).second entry increments
  have after := increments.bounded
  have scalar (a b c : InverseRootPolynomial.Gaussian) {x y : InverseRootPolynomial.Coordinate} (first :
    Data.Gaussian.Basic.Canonical.normSq (a - b) ≤ x) (last : Data.Gaussian.Basic.Canonical.normSq (b - c) ≤ y) :
      Data.Gaussian.Basic.Canonical.normSq (a - c) ≤ 2 * (x + y) := by
    have triangle := Data.Gaussian.Norm.Bounds.normSq_sub_le_via a b c
    simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at triangle
    exact triangle.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first
          last) (by decide))
  have totalBound : PrimitivePoint.Bounded (source.totalValue.sub capSummary.totalValue) error :=
    ⟨scalar _ _ _ before.1 after.1, scalar _ _ _ before.2 after.2⟩
  have nonnegative : 0 ≤ error := (Data.Gaussian.Basic.Canonical.normSq_nonneg _).trans totalBound.1
  have sourceMagnitude := SourceComparisonRequest.sourceIncrement_magnitude (interval :=
    CommonChartPreparation.IntervalAt common i)
    evaluated.samples.source evaluated.samples.otherSource
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical, Data.Gaussian.Norm.Basic.normSq_eq_canonical] at sourceMagnitude
  have sourceFirst : Data.Gaussian.Basic.Canonical.normSq source.totalValue.left ≤ data.sourceSlope +
    otherData.sourceSlope :=
    (le_add_of_nonneg_right (Data.Gaussian.Basic.Canonical.normSq_nonneg _)).trans sourceMagnitude
  have sourceSecond : Data.Gaussian.Basic.Canonical.normSq source.totalValue.right ≤ data.sourceSlope +
    otherData.sourceSlope :=
    (le_add_of_nonneg_left (Data.Gaussian.Basic.Canonical.normSq_nonneg _)).trans sourceMagnitude
  let magnitude := 2 * (data.sourceSlope + otherData.sourceSlope + error)
  have larger : data.sourceSlope + otherData.sourceSlope ≤ magnitude := by
    have sum := add_nonneg data.sourceSlope_nonnegative otherData.sourceSlope_nonnegative
    have doubled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
        decide : (1 : InverseRootPolynomial.Coordinate) ≤ 2) (add_nonneg sum nonnegative)
    rw [Fraction.Field.one_mul] at doubled
    exact (le_add_of_nonneg_right nonnegative).trans doubled
  have capBound (a b : InverseRootPolynomial.Gaussian) (sourceBound : Data.Gaussian.Basic.Canonical.normSq a ≤
    data.sourceSlope + otherData.sourceSlope)
      (difference : Data.Gaussian.Basic.Canonical.normSq (a - b) ≤ error) : Data.Gaussian.Basic.Canonical.normSq b ≤
        magnitude := by
    have estimate := Data.Gaussian.Norm.Bounds.normSq_sub_le_two a (a - b)
    rw [show a - (a - b) = b by ring1] at estimate
    simp only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at estimate
    exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct sourceBound difference) (by decide))
  exact ⟨increments, source, capSummary, entry.centered_bounded, error, rfl, totalBound, nonnegative,
    magnitude, rfl, Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (add_nonneg
      data.sourceSlope_nonnegative otherData.sourceSlope_nonnegative) nonnegative),
    ⟨sourceFirst.trans larger, sourceSecond.trans larger⟩,
    ⟨capBound _ _ sourceFirst totalBound.1, capBound _ _ sourceSecond totalBound.2⟩⟩

/-- The retained interval total-error allowance is at most four times its original prepared tolerance. -/
theorem BlockComparison.error_prepared {i : Fin common.intervals.length} (comparison :
  (BlockComparison evaluated) i) :
    comparison.error ≤ 4 * (request.plans.get i).budget.tolerance := by
  let entry := (evaluated.entries.get i).evaluated
  have before := SourceComparisonRequest.incrementError_paid (request.plans.get i).request entry.later
  have after := Increments.error_prepared entry.chart comparison.increments
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
    before.le after) (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
  rw [← comparison.error_eq] at bound
  have exactScale : 2 * (ReciprocalDiskCommonSourceCharts.sourceRibbonTarget (request.plans.get i).budget.tolerance +
      40 * ((((request.plans.get i).budget.tolerance / 4) / 4) / 2)) =
      (81 / 32 : InverseRootPolynomial.Coordinate) * (request.plans.get i).budget.tolerance := by
    calc
      _ = (2 * ((4 : InverseRootPolynomial.Coordinate)⁻¹ ^ 3 + 40 * ((4 : InverseRootPolynomial.Coordinate)⁻¹ ^ 2 * (2 :
        InverseRootPolynomial.Coordinate)⁻¹))) *
          (request.plans.get i).budget.tolerance := by
        unfold ReciprocalDiskCommonSourceCharts.sourceRibbonTarget
        simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
        ring1
      _ = _ := congrArg (fun scalar : InverseRootPolynomial.Coordinate => scalar * (request.plans.get
        i).budget.tolerance) (by decide +kernel)
  exact bound.trans (exactScale.trans_le
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) (request.plans.get
      i).budget.positive.le))

/-- The actual interval magnitude is bounded by the original source slopes and fixed prepared allowance. -/
theorem BlockComparison.magnitude_prepared {i : Fin common.intervals.length} (comparison :
  (BlockComparison evaluated) i) :
    comparison.magnitude ≤ 2 * (data.sourceSlope + otherData.sourceSlope + 4) := by
  have error := (comparison.error_prepared evaluated).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.plans.get i).budget.small (by
      decide)).trans_eq (by rw [mul_one]))
  rw [comparison.magnitude_eq]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct le_rfl
    error) (by decide)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

/-- Combine the actual retained block summaries, preserving the full polygon of their totals in the flattened path area.
-/
@[expose] def summarize {n : Nat} (paths : Fin n → List Stokes.PrimitivePoint)
    (entries : (i : Fin n) → PairedIncrementArea.Summary (paths i)) :
    PairedIncrementArea.Summary (List.ofFn paths).flatten := by
  let totals := List.ofFn (fun i => (entries i).totalValue)
  let polygon := PairedIncrementArea.Summary.build totals
  have totalsEq : (List.ofFn paths).map PairedIncrementArea.total = totals := by
    rw [OfFn.Basic.map_ofFn]
    exact OfFn.Basic.ofFn_congr (fun i => (entries i).total_eq.symm)
  have areasEq : Data.Gaussian.Norm.Sum.Basic.gaussianSum ((List.ofFn paths).map PairedIncrementArea.area) =
      FiniteSum.Fin.sumFin (fun i => (entries i).areaValue) := by
    rw [OfFn.Basic.map_ofFn, ← Data.Gaussian.Norm.Sum.Indexed.sumFin_eq_gaussianSum]
    exact FiniteSum.Fin.sumFin_congr (fun i => (entries i).area_eq.symm)
  exact ⟨polygon.totalValue, polygon.total_eq.trans (by rw [PairedAreaBlocks.total_flatten, totalsEq]),
    FiniteSum.Fin.sumFin (fun i => (entries i).areaValue) + polygon.areaValue,
    by rw [PairedAreaBlocks.area_flatten, totalsEq, areasEq, polygon.area_eq]⟩

/-- The dependent vector of actual source/chart comparisons on every retained common interval. -/
@[expose] def BlockComparisons := Data.Vector.DependentVector
  (BlockComparison evaluated)
/-- The original retained chart increment blocks in common-interval order. -/
@[expose] def ChartBlocks := List.ofFn
  (ChartBlock evaluated)

set_option genInjectivity false in
/-- The complete retained source/chart block comparison and its full cumulative area bound.

Both flattened path summaries and the actual maxima of local errors and magnitudes determine the cached whole-path
discrepancy. -/
structure BlockBank where
  /-- The cached complete dependent bank of actual interval comparisons. -/ entries :
    (BlockComparisons evaluated)
  /-- The exact summary of the complete flattened original source path. -/ source : PairedIncrementArea.Summary
    evaluated.sourceBlocks.flatten
  /-- The exact summary of the complete flattened original chart path. -/ chart : PairedIncrementArea.Summary
    (ChartBlocks evaluated).flatten
  /-- The cached maximum of the original interval area tolerances and zero. -/ areaError :
    InverseRootPolynomial.Coordinate
  /-- The area-error cache is exactly the retained finite maximum of original interval tolerances. -/ areaError_eq :
    areaError = FiniteSum.Fin.Rational.maximum (fun i => (request.plans.get i).budget.tolerance)
  /-- The cached maximum of all actual interval total-error allowances and zero. -/ totalError :
    InverseRootPolynomial.Coordinate
  /-- The total-error cache is exactly the retained finite maximum of interval total errors. -/ totalError_eq :
    totalError = FiniteSum.Fin.Rational.maximum (fun i => (entries.get i).error)
  /-- The cached maximum of actual interval total magnitudes and zero. -/ magnitude : InverseRootPolynomial.Coordinate
  /-- The common magnitude cache is exactly the retained finite maximum of interval magnitudes. -/ magnitude_eq :
    magnitude = FiniteSum.Fin.Rational.maximum (fun i => (entries.get i).magnitude)
  /-- The cached complete area allowance including the full polygon of original interval totals. -/ error :
    InverseRootPolynomial.Coordinate
  /-- The error cache is exactly the prescribed count-weighted local-area and total-discrepancy expression. -/ error_eq
    : error = 2 * ((common.intervals.length : InverseRootPolynomial.Coordinate)^2 * areaError +
    16 * (common.intervals.length : InverseRootPolynomial.Coordinate)^4 * totalError * magnitude)
  /-- The full actual source/chart area discrepancy is bounded by the cached whole-path error. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq (source.areaValue - chart.areaValue) ≤ error

constructive_injectivity BlockBank

/-- The comparison pays the whole polygon of retained interval totals. Neither path is replaced by endpoint chords or by
equal total increments. -/
@[expose] def blockBank : (BlockBank evaluated)
  := by
  let entries := DependentVector.ofFn
    (blockComparison evaluated)
  let source := summarize
    (SourceBlock evaluated) (fun i =>
    (entries.get i).source)
  let chart := summarize
    (ChartBlock evaluated) (fun i => (entries.get
    i).chart)
  let areaError := FiniteSum.Fin.Rational.maximum (fun i => (request.plans.get i).budget.tolerance)
  let totalError := FiniteSum.Fin.Rational.maximum (fun i => (entries.get i).error)
  let magnitude := FiniteSum.Fin.Rational.maximum (fun i => (entries.get i).magnitude)
  let pairs := List.ofFn (fun i => ((SourceBlock
    evaluated) i, (ChartBlock evaluated) i))
  have areas : ∀ pair ∈ pairs, Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area pair.1 -
    PairedIncrementArea.area pair.2) ≤ areaError := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    rw [← (entries.get i).source.area_eq, ← (entries.get i).chart.area_eq]
    exact (entries.get i).area_bounded.le.trans (FiniteSum.Fin.Rational.le_maximum _ i)
  have totals : ∀ pair ∈ pairs, PrimitivePoint.Bounded ((PairedIncrementArea.total pair.1).sub
    (PairedIncrementArea.total pair.2)) totalError := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    rw [← (entries.get i).source.total_eq, ← (entries.get i).chart.total_eq]
    exact ⟨(entries.get i).total_bounded.1.trans (FiniteSum.Fin.Rational.le_maximum _ i), (entries.get
      i).total_bounded.2.trans (FiniteSum.Fin.Rational.le_maximum _ i)⟩
  have left : ∀ pair ∈ pairs, PrimitivePoint.Bounded (PairedIncrementArea.total pair.1) magnitude := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    rw [← (entries.get i).source.total_eq]
    exact ⟨(entries.get i).source_bounded.1.trans (FiniteSum.Fin.Rational.le_maximum _ i), (entries.get
      i).source_bounded.2.trans (FiniteSum.Fin.Rational.le_maximum _ i)⟩
  have right : ∀ pair ∈ pairs, PrimitivePoint.Bounded (PairedIncrementArea.total pair.2) magnitude := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    rw [← (entries.get i).chart.total_eq]
    exact ⟨(entries.get i).chart_bounded.1.trans (FiniteSum.Fin.Rational.le_maximum _ i), (entries.get
      i).chart_bounded.2.trans (FiniteSum.Fin.Rational.le_maximum _ i)⟩
  have bound := PairedBlockComparison.blocks_area_difference_bound pairs
    (FiniteSum.Fin.Rational.maximum_nonnegative _) (FiniteSum.Fin.Rational.maximum_nonnegative _) areas totals left
      right
  have sourceEq : pairs.map Prod.fst = List.ofFn
    (SourceBlock evaluated) := by
    rw [OfFn.Basic.map_ofFn];
    rfl
  have chartEq : pairs.map Prod.snd = List.ofFn
    (ChartBlock evaluated) := by
    rw [OfFn.Basic.map_ofFn];
    rfl
  rw [sourceEq, chartEq, ← source.area_eq, ← chart.area_eq] at bound
  have countEq : pairs.length = common.intervals.length := Data.List.OfFn.Basic.length_ofFn
  rw [countEq] at bound
  exact ⟨entries, source, chart, areaError, rfl, totalError, rfl, magnitude, rfl,
    2 * ((common.intervals.length : InverseRootPolynomial.Coordinate)^2 * areaError +
      16 * (common.intervals.length : InverseRootPolynomial.Coordinate)^4 * totalError * magnitude), rfl, bound⟩

/-- The retained complete source area is exactly the original full parent dyadic increment area. -/
theorem BlockBank.source_readback (bank :
  (BlockBank evaluated)) :
    bank.source.areaValue = PairedIncrementArea.area (DyadicPairedPrimitivePaths.increments
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource)
      (common.depth + depth) 0 1) := bank.source.area_eq.trans (congrArg PairedIncrementArea.area
        evaluated.sourceBlocks_full)

/-- Both actual full-path total discrepancies satisfy the original interval-count squared times the retained total
error. -/
theorem BlockBank.total_bounded (bank :
  (BlockBank evaluated)) :
    PrimitivePoint.Bounded (bank.source.totalValue.sub bank.chart.totalValue)
      ((common.intervals.length : InverseRootPolynomial.Coordinate)^2 * bank.totalError) := by
  let pairs := List.ofFn (fun i => ((bank.entries.get i).source.totalValue, (bank.entries.get i).chart.totalValue))
  have bounded : ∀ value ∈ pairs.map (fun pair => pair.1.sub pair.2), PrimitivePoint.Bounded value bank.totalError := by
    intro value member
    obtain ⟨pair, present, rfl⟩ := Map.mem_map.mp member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp present
    have upper : (bank.entries.get i).error ≤ bank.totalError :=
      (FiniteSum.Fin.Rational.le_maximum (fun i => (bank.entries.get i).error) i).trans_eq bank.totalError_eq.symm
    exact ⟨(bank.entries.get i).total_bounded.1.trans upper, (bank.entries.get i).total_bounded.2.trans upper⟩
  have bound := PairedIncrementArea.total_bound
    (bank.totalError_eq ▸ FiniteSum.Fin.Rational.maximum_nonnegative _) bounded (count := common.intervals.length)
    (by rw [Data.List.Map.length_map, Data.List.OfFn.Basic.length_ofFn])
  have left : pairs.map Prod.fst = evaluated.sourceBlocks.map PairedIncrementArea.total := by
    dsimp only [pairs, Evaluation.sourceBlocks, -eq_self, -iff_self]
    rw [OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn]
    exact OfFn.Basic.ofFn_congr (fun i => (bank.entries.get i).source.total_eq)
  have right : pairs.map Prod.snd = (ChartBlocks
    evaluated).map PairedIncrementArea.total := by
    dsimp only [pairs, ChartBlocks, -eq_self,
      -iff_self]
    rw [OfFn.Basic.map_ofFn, OfFn.Basic.map_ofFn]
    exact OfFn.Basic.ofFn_congr (fun i => (bank.entries.get i).chart.total_eq)
  rw [PairedIncrementComparison.total_differences, left, right,
    ← PairedAreaBlocks.total_flatten, ← PairedAreaBlocks.total_flatten,
    ← bank.source.total_eq, ← bank.chart.total_eq] at bound
  exact bound

/-- Both actual full-path total discrepancies satisfy four times the original requested target. -/
theorem BlockBank.total_accurate (bank :
  (BlockBank evaluated)) :
    Data.Gaussian.Norm.Basic.normSq (bank.source.totalValue.left - bank.chart.totalValue.left) < 4 * target ∧
      Data.Gaussian.Norm.Basic.normSq (bank.source.totalValue.right - bank.chart.totalValue.right) < 4 * target
        := by
  have totals : bank.totalError ≤ 4 * request.allowance := bank.totalError_eq ▸
    FiniteSum.Fin.Rational.maximum_le _ (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) request.positive.le)
      (fun i =>
      ((bank.entries.get i).error_prepared evaluated).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.plans.get i).budget.bounded (by decide)))
  have counted := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totals
    (Fraction.Order.Arithmetic.sq_nonneg_direct (common.intervals.length : InverseRootPolynomial.Coordinate))
  have paid : (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * (4 * request.allowance) < 4 * target :=
    (by ring1 : (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * (4 * request.allowance) =
      4 * ((common.intervals.length : InverseRootPolynomial.Coordinate) * ((common.intervals.length :
        InverseRootPolynomial.Coordinate) * request.allowance))).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide) request.paid)
  have first := (bank.total_bounded evaluated).1
  have second := (bank.total_bounded evaluated).2
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at first second
  exact ⟨first.trans_lt (counted.trans_lt paid), second.trans_lt (counted.trans_lt paid)⟩

/-- The actual full source total equals the original endpoint reading difference. -/
theorem BlockBank.source_total (bank : (BlockBank
  evaluated)) :
    bank.source.totalValue =
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource 1).sub
      (CommonRibbonRequest.sourceValues evaluated.samples.source evaluated.samples.otherSource 0) := by
  rw [bank.source.total_eq, evaluated.sourceBlocks_full, DyadicPairedPrimitivePaths.increments_total]

/-- Both components of the actual full source total are bounded by the original source-slope sum. -/
theorem BlockBank.source_magnitude (bank :
  (BlockBank evaluated)) :
    PrimitivePoint.Bounded bank.source.totalValue (data.sourceSlope + otherData.sourceSlope) := by
  have first := SourcePrimitive.increment_bound evaluated.samples.source (first := 0) (last := 1) (by decide) (by
    decide)
  have second := SourcePrimitive.increment_bound evaluated.samples.otherSource (first := 0) (last := 1) (by decide) (by
    decide)
  rw [show ((1 : InverseRootPolynomial.Coordinate) - 0)^2 = 1 by decide, mul_one] at first second
  rw [bank.source_total evaluated]
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at first second
  exact ⟨first.trans (le_add_of_nonneg_right otherData.sourceSlope_nonnegative),
    second.trans (le_add_of_nonneg_left data.sourceSlope_nonnegative)⟩

/-- The original interval-count and source-slope coefficient paying the full cumulative block comparison. -/
@[expose] def blockComparisonScale : Coordinate := 2 * ((common.intervals.length : InverseRootPolynomial.Coordinate)^2 +
  64 * (common.intervals.length : InverseRootPolynomial.Coordinate)^4 * (2 * (data.sourceSlope + otherData.sourceSlope +
    4)))

/-- The cached whole-path error is bounded by the original full-block coefficient times its retained common allowance.
-/
theorem BlockBank.error_prepared (bank :
  (BlockBank evaluated)) :
    bank.error ≤ blockComparisonScale
      (common := common) * request.allowance := by
  have areas : bank.areaError ≤ request.allowance := bank.areaError_eq ▸
    FiniteSum.Fin.Rational.maximum_le _ request.positive.le (fun i => (request.plans.get i).budget.bounded)
  have totals : bank.totalError ≤ 4 * request.allowance := bank.totalError_eq ▸
    FiniteSum.Fin.Rational.maximum_le _ (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) request.positive.le)
      (fun i =>
      ((bank.entries.get i).error_prepared evaluated).trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (request.plans.get i).budget.bounded (by decide)))
  have magnitudeNonnegative : 0 ≤ 2 * (data.sourceSlope + otherData.sourceSlope + 4) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (add_nonneg data.sourceSlope_nonnegative
      otherData.sourceSlope_nonnegative) (by decide))
  have magnitude : bank.magnitude ≤ 2 * (data.sourceSlope + otherData.sourceSlope + 4) := bank.magnitude_eq ▸
    FiniteSum.Fin.Rational.maximum_le _ magnitudeNonnegative (fun i => (bank.entries.get i).magnitude_prepared
      evaluated)
  have nonnegative : 0 ≤ bank.magnitude := bank.magnitude_eq ▸ FiniteSum.Fin.Rational.maximum_nonnegative _
  have product := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct totals nonnegative).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct magnitude (Fraction.Order.Arithmetic.mul_nonneg_direct
      (by decide) request.positive.le))
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
        common.intervals.length)) 4))
  rw [bank.error_eq]
  have estimate := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct areas
      (Fraction.Order.Arithmetic.sq_nonneg_direct (common.intervals.length : InverseRootPolynomial.Coordinate))) scaled)
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
  exact (by ring1 : 2 * ((common.intervals.length : InverseRootPolynomial.Coordinate)^2 * bank.areaError +
    16 * (common.intervals.length : InverseRootPolynomial.Coordinate)^4 * bank.totalError * bank.magnitude) =
    2 * ((common.intervals.length : InverseRootPolynomial.Coordinate)^2 * bank.areaError +
      (16 * (common.intervals.length : InverseRootPolynomial.Coordinate)^4) * (bank.totalError *
        bank.magnitude))).trans_le
    (estimate.trans_eq (by
        unfold blockComparisonScale;
        ring1))

/-- The original full-block comparison coefficient is nonnegative. -/
theorem blockComparisonScale_nonnegative : 0 ≤
  blockComparisonScale (common := common) :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
        common.intervals.length)) 4))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (add_nonneg data.sourceSlope_nonnegative
        otherData.sourceSlope_nonnegative) (by decide)))))

/-- The cached whole-path area error is bounded by the original full-block coefficient times the requested target. -/
theorem BlockBank.error_target (bank : (BlockBank
  evaluated)) :
    bank.error ≤ blockComparisonScale (common :=
      common) * target := by
  have count : (1 : InverseRootPolynomial.Coordinate) ≤ (common.intervals.length : InverseRootPolynomial.Coordinate) :=
    Fraction.Cast.Order.natCast_le_direct common.nonempty
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1)
    count 2
  rw [show (1 : InverseRootPolynomial.Coordinate)^2 = 1 by decide] at square
  have lower := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct square request.positive.le
  rw [Fraction.Field.one_mul] at lower
  have paid : (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * request.allowance < target :=
    (by ring1 : (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * request.allowance =
      (common.intervals.length : InverseRootPolynomial.Coordinate) * ((common.intervals.length :
        InverseRootPolynomial.Coordinate) * request.allowance)).trans_lt request.paid
  exact (bank.error_prepared evaluated).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (lower.trans paid.le)
      (blockComparisonScale_nonnegative (common
      := common)))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison
