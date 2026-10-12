module
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBlockComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRequestedBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTraceIncrements
import Purelib.Integration.Path.PairedBlockComparison
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentReadings
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Raw source area transport on the retained regular parent bank. The
finite block scale is fixed before choosing numerical source samples. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentArea

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational.Budget
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace.Evaluation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentReadings
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Data.Vector
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path
open Purelib.Integration.Path.JoinedTraceIncrements
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartBankRequest ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints (RegularEndpointRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction.Compatibility

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

/-- The fixed common magnitude ceiling for the retained parent source and chart increments. -/
@[expose] def parentMagnitude (original : PairedParentRequest.Request regular other parents target minimum) : Coordinate
  :=
  4 * (original.slope + 8)

/-- The common parent magnitude ceiling is at least one. -/
theorem parentMagnitude_one_le (original : PairedParentRequest.Request regular other parents target minimum) :
    1 ≤ parentMagnitude original := by
  have extra : 0 ≤ 4 * original.slope + 31 := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) original.slope_nonnegative) (by decide +kernel)
  exact (le_add_of_nonneg_right extra).trans_eq (by
      unfold parentMagnitude;
      ring1)

/-- The maximum retained joined-block area scale across all original parents. -/
@[expose] def parentAreaScale (original : PairedParentRequest.Request regular other parents target minimum) : Coordinate
  :=
  Algebra.FiniteSum.Fin.Rational.maximum (fun i : Fin original.plans.length =>
    CommonRequestedBoundary.joinedBlockScale (PairedParentCharts.ChartParent original i).common)

/-- The aggregate source-to-chart area scale, including internal parent areas and the polygon of parent totals. -/
@[expose] def sourceParentAreaScale (original : PairedParentRequest.Request regular other parents target minimum) :
  Coordinate :=
  2 * ((original.plans.length : InverseRootPolynomial.Coordinate)^2 *
    parentAreaScale original +
    256 * (original.plans.length : InverseRootPolynomial.Coordinate)^4 *
      parentMagnitude original)

/-- The complete retained source-to-chart area scale is nonnegative. -/
theorem sourceParentAreaScale_nonnegative (original : PairedParentRequest.Request regular other parents target minimum)
  :
    0 ≤ sourceParentAreaScale original := by
  have count := Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    original.plans.length)) 4
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Algebra.FiniteSum.Fin.Rational.maximum_nonnegative _))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) count)
      ((by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1).trans
        (parentMagnitude_one_le original))))

/-- Each actual retained source block has both increment components bounded by twice the common slope. -/
private theorem source_magnitude (evaluated : request.Evaluation) (i : Fin original.plans.length) :
    PrimitivePoint.Bounded (CommonChartBlockComparison.blockBank (evaluated.entries.get i)).source.totalValue (2 *
      original.slope) := by
  have bounds := PairedParentRequest.Request.plan_bounds original (PairedParentCharts.ChartParent original i)
    (List.getElem_mem i.isLt)
  have combined := Fraction.Order.Arithmetic.add_le_add_direct bounds.1 bounds.2
  rw [show original.slope + original.slope = 2 * original.slope by ring1] at combined
  have before := (CommonChartBlockComparison.blockBank (evaluated.entries.get i)).source_magnitude
    (evaluated.entries.get i)
  exact ⟨before.1.trans combined, before.2.trans combined⟩

/-- At a unit-bounded chart allowance, each actual parent chart increment obeys the fixed common magnitude ceiling. -/
theorem Evaluation.parent_chart_magnitude (evaluated : request.Evaluation)
    (small : request.allowance ≤ 1) (i : Fin original.plans.length) :
    PrimitivePoint.Bounded (PairedIncrementArea.total (VertexTrace.increments (Evaluation.chartTrace
      (evaluated.entries.get i)) id))
      (parentMagnitude original) := by
  have source := source_magnitude evaluated i
  have difference := BlockBank.joined_total_accurate (evaluated.entries.get i) (CommonChartBlockComparison.blockBank
    (evaluated.entries.get i)) small
  have paid : 16 * request.allowance ≤ 16 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)).trans_eq (by ring1)
  have scalar (a b : InverseRootPolynomial.Gaussian) (source : Data.Gaussian.Norm.Basic.normSq a ≤ 2 *
    original.slope)
      (difference : Data.Gaussian.Norm.Basic.normSq (a - b) ≤ 16 * request.allowance) :
        Data.Gaussian.Norm.Basic.normSq b ≤
        parentMagnitude original := by
    have bound := Data.Gaussian.Norm.Bounds.normSq_sub_le_two a (a - b)
    rw [show a - (a - b) = b by ring1] at bound
    exact bound.trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct source (difference.trans paid)) (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)).trans_eq
      (by unfold parentMagnitude; ring1))
  have oldBound {value : Data.Gaussian.Basic.Canonical} {limit : InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Basic.Canonical.normSq value ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using bound
  have canonicalBound {value : Data.Gaussian.Basic.Canonical} {limit : InverseRootPolynomial.Coordinate}
      (bound : Data.Gaussian.Norm.Basic.normSq value ≤ limit) :
      Data.Gaussian.Basic.Canonical.normSq value ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at bound ⊢
    simpa only [Data.Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using bound
  exact ⟨canonicalBound (scalar _ _ (oldBound source.1) (oldBound difference.1)),
    canonicalBound (scalar _ _ (oldBound source.2) (oldBound difference.2))⟩

/-- Include both the internal parent areas and the polygon of parent totals when comparing the full raw source path to
the separate chart increments. -/
theorem Evaluation.source_parent_area_bound (evaluated : request.Evaluation)
    (small : request.allowance ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area evaluated.sourcePaths.flatten -
      PairedIncrementArea.area (List.ofFn (fun i : Fin original.plans.length =>
        VertexTrace.increments (Evaluation.chartTrace (evaluated.entries.get i)) id)).flatten) ≤
      sourceParentAreaScale original *
        request.allowance := by
  let pairs := List.ofFn (fun i : Fin original.plans.length =>
    ((evaluated.entries.get i).sourceBlocks.flatten, VertexTrace.increments (Evaluation.chartTrace
      (evaluated.entries.get i)) id))
  have areas : ∀ pair ∈ pairs,
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area pair.1 - PairedIncrementArea.area pair.2) ≤
        parentAreaScale original * request.allowance
          := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    have before := BlockBank.joined_source_bound (evaluated.entries.get i) (CommonChartBlockComparison.blockBank
      (evaluated.entries.get i)) small
    rw [(CommonChartBlockComparison.blockBank (evaluated.entries.get i)).source.area_eq] at before
    exact before.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Algebra.FiniteSum.Fin.Rational.le_maximum _ i) request.positive.le)
  have totals : ∀ pair ∈ pairs,
      PrimitivePoint.Bounded ((PairedIncrementArea.total pair.1).sub (PairedIncrementArea.total pair.2))
        (16 * request.allowance) := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    have before := BlockBank.joined_total_accurate (evaluated.entries.get i) (CommonChartBlockComparison.blockBank
      (evaluated.entries.get i)) small
    rw [(CommonChartBlockComparison.blockBank (evaluated.entries.get i)).source.total_eq] at before
    exact before
  have left : ∀ pair ∈ pairs, PrimitivePoint.Bounded (PairedIncrementArea.total pair.1)
    (parentMagnitude original) := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    have before := source_magnitude evaluated i
    rw [(CommonChartBlockComparison.blockBank (evaluated.entries.get i)).source.total_eq] at before
    have larger : 2 * original.slope ≤
      parentMagnitude original :=
      (le_add_of_nonneg_right (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2)
        original.slope_nonnegative) (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 32))).trans_eq
          (by unfold parentMagnitude; ring1)
    exact ⟨before.1.trans larger, before.2.trans larger⟩
  have right : ∀ pair ∈ pairs, PrimitivePoint.Bounded (PairedIncrementArea.total pair.2)
    (parentMagnitude original) := by
    intro pair member
    obtain ⟨i, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    exact Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentArea.Evaluation.parent_chart_magnitude evaluated
      small i
  have bound := PairedBlockComparison.blocks_area_difference_bound pairs
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 16)
      request.positive.le)
    ((by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1).trans
      (parentMagnitude_one_le original)) areas totals
      left right
  have leftEq : pairs.map Prod.fst = evaluated.sourcePaths := by
    rw [OfFn.Basic.map_ofFn]
    apply OfFn.Basic.ofFn_congr
    intro i
    have full := (evaluated.entries.get i).sourceBlocks_full
    rw [PairedParentCharts.chartDepth_eq original depth i] at full
    exact full
  have rightEq : pairs.map Prod.snd = List.ofFn (fun i : Fin original.plans.length =>
      VertexTrace.increments (Evaluation.chartTrace (evaluated.entries.get i)) id) := by
    rw [OfFn.Basic.map_ofFn]
    rfl
  rw [leftEq, rightEq, Data.List.OfFn.Basic.length_ofFn] at bound
  exact bound.trans_eq (by
      unfold sourceParentAreaScale;
      ring1)

/-- Choose one later chart reading for all joins. The raw source path is preserved, and its full area is compared to the
retained closed chart area. -/
theorem Evaluation.regular_source_area_comparison (evaluated : request.Evaluation)
    (small : request.allowance ≤ 1) (present : 0 < original.plans.length)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate)
    (returned : Gaussian.Equivalence.NamedEquivalent last first)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (error : InverseRootPolynomial.Coordinate) (positive : 0 < error) :
    ∃ retained : request.Evaluation, retained.sourcePaths = evaluated.sourcePaths ∧
      Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area evaluated.sourcePaths.flatten -
        retained.chartArea) ≤
        2 * (sourceParentAreaScale original *
          request.allowance + error) := by
  let scale : Coordinate := 32 * ((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 *
    parentMagnitude original
  have magnitudeNonnegative : 0 ≤ parentMagnitude
    original :=
    (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1).trans
      (parentMagnitude_one_le original)
  have scaleNonnegative : 0 ≤ scale := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 32)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
        magnitudeNonnegative
  let tolerance := min 1 (Weighted.allowance error scale)
  have tolerancePositive : 0 < tolerance := Fraction.Order.Basic.lt_min (by decide)
    (Weighted.allowance_positive positive scaleNonnegative)
  let joins := ReciprocalRegularParentTrace.sourceJoins request chain roots
  let endpoints := DependentVector.ofFn (fun i : Fin (original.plans.length - 1) =>
    RegularEndpointRequest.build evaluated _ _ (joins i) tolerance tolerancePositive minimum)
  let endpointWeight := fun (i : Fin (original.plans.length - 1))
    (entry : ReciprocalRegularParentEndpoints.RegularEndpointRequest evaluated _ _ (joins i) tolerance minimum) =>
      entry.index
  let stage := endpoints.maximum endpointWeight
  let retained := Evaluation.atReadingFloor evaluated stage
  have gaps : ∀ i : Fin (original.plans.length - 1),
      PrimitivePoint.Bounded ((Evaluation.chartTrace (retained.entries.get ⟨i.val + 1, by omega0⟩)).first.sub
        (Evaluation.chartTrace (retained.entries.get ⟨i.val, by omega0⟩)).last) tolerance := by
    intro i
    have later := endpoints.get_le_maximum endpointWeight i
    dsimp only [endpoints, endpointWeight, -eq_self, -iff_self] at later
    rw [DependentVector.ofFn_get] at later
    exact RegularEndpointRequest.atReadingFloor_bound evaluated _ _ (joins i) tolerance tolerancePositive minimum stage
      later unramified
  have inserted := Evaluation.regularTrace_area_insertion retained tolerancePositive.le magnitudeNonnegative
    ((Fraction.Order.Basic.min_le_left _ _).trans
      (parentMagnitude_one_le original))
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentArea.Evaluation.parent_chart_magnitude retained
      small) gaps
  have paid : 32 * ((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * tolerance *
    parentMagnitude original ≤ error :=
    (by ring1 : 32 * ((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * tolerance *
      parentMagnitude original =
      scale * tolerance).trans_le ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Basic.min_le_right _ _) scaleNonnegative).trans
        (Weighted.mul_allowance_le positive.le scaleNonnegative))
  have chartEq := (Evaluation.regularTrace_increment_area retained).trans
    (Evaluation.regularTrace_closed_area retained unramified present chain roots closed returned)
  rw [chartEq] at inserted
  have source := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentArea.Evaluation.source_parent_area_bound
    retained small
  have estimate := Data.Gaussian.Norm.Bounds.normSq_sub_le_via
    (PairedIncrementArea.area retained.sourcePaths.flatten)
    (PairedIncrementArea.area (List.ofFn (fun i : Fin original.plans.length =>
      VertexTrace.increments (Evaluation.chartTrace (retained.entries.get i)) id)).flatten) retained.chartArea
  have bounded := estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct source (inserted.trans paid)) (by
        decide : (0 : InverseRootPolynomial.Coordinate) ≤ 2))
  have same := Evaluation.atReadingFloor_sourcePaths evaluated stage
  rw [same] at bounded
  exact ⟨retained, same, bounded⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentArea
