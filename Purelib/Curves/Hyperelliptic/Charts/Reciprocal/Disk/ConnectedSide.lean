module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideEstimates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaJoins
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedReciprocalControlledRequests
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideConnections
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Riemann.Normalization

/-!
# Requested connected cap paths on complete retained exterior tours

The public path acquisition uses retained source-root joins to insert every
inter-parent connector. Its full path telescopes to the retained endpoint
readings; both integrator and area comparisons pay all connector costs.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Path.IncrementArea (Summary)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins.Path (Preparation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison (Request)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}

set_option genInjectivity false in
/-- A retained separated-side comparison and all actual junction accuracy requests.

Quarter targets and a fixed parent-count budget pay for the connectors before choosing the shared sample and reading
stage. -/
structure ConnectedRequest (prepared : Path.Preparation regular parents) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate) (minimum : Nat) where
  /-- The original separated-side request or its exact retained evaluation at quarter targets. -/ separated :
    SideComparison.Request prepared (totalTarget / 4) (areaTarget / 4) minimum
  /-- The cached common squared-norm ceiling for actual parent totals. -/ bound : InverseRootPolynomial.Coordinate
  /-- The cached bound is twice one plus the original source-slope maximum. -/ bound_eq : bound = 2 *
    ((ParentCovers.sourceSlopeMaximum prepared.covers) + 1)
  /-- The retained parent-total ceiling is nonnegative. -/ bound_nonnegative : 0 ≤ bound
  /-- The retained connector tolerance budget for the actual original parent count and quarter targets. -/ budget :
    PathArea.SideAreaBudget bound parents.length (totalTarget / 4) (areaTarget / 4)
  /-- The cached requests for every actual junction in the original retained parent bank. -/ junctions :
    SideConnections.JunctionRequests budget.tolerance minimum prepared.bank prepared.links
  /-- The cached common sufficient endpoint-reading stage. -/ readingIndex : Nat
  /-- The cached reading stage is exactly the maximum of the separated and junction request stages. -/ readingIndex_eq :
    readingIndex = max separated.readingIndex junctions.maximum

constructive_injectivity ConnectedRequest

namespace ConnectedRequest

/-- Cache the original separated request, fixed parent-total bound and all actual junction requests with their common
reading stage. -/
@[expose] def build (prepared : Path.Preparation regular parents) (totalTarget areaTarget :
  InverseRootPolynomial.Coordinate)
    (totalPositive : 0 < totalTarget) (areaPositive : 0 < areaTarget) (minimum : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest prepared totalTarget areaTarget minimum
      :=
  have totalQuarter := Fraction.Order.Field.div_pos_direct totalPositive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  have areaQuarter := Fraction.Order.Field.div_pos_direct areaPositive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  let separated := SideComparison.Request.build prepared (totalTarget / 4) (areaTarget / 4) totalQuarter areaQuarter
    minimum
  let bound := 2 * ((ParentCovers.sourceSlopeMaximum prepared.covers) + 1)
  have boundNonnegative : 0 ≤ bound := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (ParentCovers.sourceSlopeMaximum_nonnegative prepared.covers) (by decide))
  let budget := SideAreaBudget.build bound boundNonnegative parents.length
    (totalTarget / 4) (areaTarget / 4) totalQuarter areaQuarter
  let junctions := JunctionRequests.build budget.tolerance budget.positive minimum prepared.bank prepared.links
  ⟨separated, bound, rfl, boundNonnegative, budget, junctions, max separated.readingIndex junctions.maximum, rfl⟩

variable {prepared : Preparation regular parents}
  {totalTarget areaTarget : Coordinate} {minimum : Nat}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest in
/-- Read the source-model index already retained by the original separated request. -/
@[expose] def index (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest prepared
  totalTarget areaTarget minimum) : Nat := request.separated.index

variable {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest in
set_option genInjectivity false in
/-- The original separated comparison joined by its actual cached endpoint connectors.

The complete connected cap summary retains exact endpoint telescoping, total and area budgets, and operational
coordinate connections. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest prepared
  totalTarget areaTarget minimum)
    (sample : Primitives.Sample cap differential index box) (depth readingIndex : Nat) where
  /-- The original separated-side request or its exact retained evaluation at quarter targets. -/ separated :
    SideComparison.Request.Evaluation request.separated sample depth readingIndex
  /-- The actual first primitive value of the retained parent bank. -/ firstValue : InverseRootPolynomial.Gaussian
  /-- The first cache is exactly the original bank's first-value readback. -/ firstValue_eq : firstValue =
    Evaluations.firstValue separated.parents
  /-- The actual last primitive value of the retained parent bank. -/ lastValue : InverseRootPolynomial.Gaussian
  /-- The last cache is exactly the original last-value readback using the retained first value for an empty bank. -/
    lastValue_eq : lastValue = Evaluations.lastValue separated.parents firstValue
  /-- The retained ordered parent paths with their actual leading connector values. -/ blocks : List
    (InverseRootPolynomial.Gaussian × List InverseRootPolynomial.Gaussian)
  /-- The cached blocks are exactly the original connected-block construction on the retained first value. -/ blocks_eq
    : blocks = Evaluations.connectedBlocks separated.parents firstValue
  /-- There is exactly one connected block per actual original parent. -/ blocks_length : blocks.length = parents.length
  /-- Every actual cached connector satisfies the retained common squared-norm tolerance. -/ connectors_small : ∀ block
    ∈ blocks, Data.Gaussian.Norm.Basic.normSq block.1 ≤ request.budget.tolerance
  /-- The cached increment and area summary of the actual connector-prepended block flattening. -/ cap :
    IncrementArea.Summary (blocks.map (fun block => block.1 :: block.2)).flatten
  /-- The complete connected total telescopes to the actual last value minus the first. -/ total_eq : cap.total =
    lastValue - firstValue
  /-- The actual source and connected-cap totals satisfy the original total target. -/ total_close :
    Data.Gaussian.Norm.Basic.normSq (separated.left.total - cap.total) < totalTarget
  /-- The original integral sample and actual connected-cap total satisfy the retained total target. -/ integral_close :
    Data.Gaussian.Norm.Basic.normSq (separated.compared.source.integralSample - cap.total) < totalTarget
  /-- The actual source and connected-cap areas satisfy the original area target. -/ area_close :
    Data.Gaussian.Norm.Basic.normSq (separated.left.area - cap.area) < areaTarget
  /-- Operational coordinate connections on the same actual retained parent evaluations. -/ coordinates :
    Evaluations.CoordinateConnections separated.parents
  /-- The actual reading stage meets every retained junction request. -/ junction_later : request.junctions.maximum ≤
    readingIndex

constructive_injectivity Evaluation

/-- A positive rational quarter target is strictly below its original target. -/
private theorem quarter_lt {target : InverseRootPolynomial.Coordinate} (positive : 0 < target) : target / 4 < target :=
  by
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  have ordered := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct quarterPositive (by
      decide : (1 : InverseRootPolynomial.Coordinate) < 4)
  rw [_root_.mul_one] at ordered
  exact ordered.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

/-- A positive rational quarter target is strictly below its original target. -/
theorem quarter_lt_for_evaluation {target : InverseRootPolynomial.Coordinate} (positive : 0 < target) : target / 4 <
  target := by
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 4)
  have ordered := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct quarterPositive (by
      decide : (1 : InverseRootPolynomial.Coordinate) < 4)
  rw [_root_.mul_one] at ordered
  exact ordered.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest
/-- Retain the supplied side evaluation and add its actual certified connectors without repeating parent acquisition. -/
@[expose] def evaluateWithSeparated (request :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest prepared totalTarget areaTarget minimum)
    {depth readingIndex : Nat} {sample : Primitives.Sample cap differential index box}
    (separated : SideComparison.Request.Evaluation request.separated sample depth readingIndex)
    (readingLater : request.readingIndex ≤ readingIndex) :
      Evaluation request sample depth
      readingIndex := by
  have readingIndices := request.readingIndex_eq ▸ readingLater
  let first := Evaluations.firstValue separated.parents
  let last := Evaluations.lastValue separated.parents first
  let blocks := Evaluations.connectedBlocks separated.parents first
  let chart := Evaluations.connectedSummary separated.parents first
  have gaps := Evaluations.gaps_small separated.parents request.junctions ((Data.Nat.Order.le_max_right _ _).trans
    readingIndices) first (by
    change Data.Gaussian.Norm.Basic.normSq (first - first) ≤ request.budget.tolerance
    rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
    exact request.budget.positive.le)
  have small : ∀ block ∈ blocks, Data.Gaussian.Norm.Basic.normSq block.1 ≤ request.budget.tolerance :=
    Evaluations.connected_small separated.parents first gaps
  have blockCount : blocks.length = parents.length := Evaluations.connected_length separated.parents first
  have paths : blocks.map Prod.snd = separated.parents.pairs.map Prod.snd := Evaluations.connected_paths
    separated.parents first
  have bounded : ∀ block ∈ blocks, Data.Gaussian.Norm.Basic.normSq
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum block.2) ≤ request.bound := by
    intro block member
    have retained : block.2 ∈ separated.parents.pairs.map Prod.snd := paths ▸ Map.mem_map.mpr ⟨block, member, rfl⟩
    obtain ⟨pair, retained, equal⟩ := Map.mem_map.mp retained
    rw [← equal, request.bound_eq]
    exact (SideEstimates.bounds separated.parents request.separated.parent_le_one
      (ParentCovers.sourceSlopeMaximum_nonnegative prepared.covers) le_rfl pair retained).2.2.2
  have totalClose : Data.Gaussian.Norm.Basic.normSq (separated.cap.total - chart.total) < totalTarget / 4 := by
    rw [show separated.cap.total - chart.total = -(chart.total - separated.cap.total) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg,
      chart.total_eq, separated.cap.total_eq, ← paths]
    have estimate := IncrementAreaJoins.joined_blocks_total_bound blocks small
    rw [blockCount] at estimate
    have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct (parents.length : InverseRootPolynomial.Coordinate))
        request.budget.positive.le
    exact estimate.trans_lt (((le_add_of_nonneg_right
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 3)
        nonnegative)).trans_eq (by ring1)).trans_lt
        request.budget.total_paid)
  have areaClose : Data.Gaussian.Norm.Basic.normSq (separated.cap.area - chart.area) < areaTarget / 4 := by
    rw [show separated.cap.area - chart.area = -(chart.area - separated.cap.area) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg,
      chart.area_eq, separated.cap.area_eq, ← paths]
    have estimate := IncrementAreaJoins.joined_blocks_area_bound blocks request.budget.positive.le
      request.bound_nonnegative small bounded
    rw [blockCount] at estimate
    have cost := IncrementAreaJoins.joined_blocks_cost (parents.length : InverseRootPolynomial.Coordinate)
      request.budget.tolerance request.bound
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) request.budget.positive.le request.bound_nonnegative
    rw [← request.budget.scale_eq] at cost
    exact (estimate.trans cost).trans_lt request.budget.area_paid
  exact ⟨separated, first, rfl, last, rfl, blocks, rfl, blockCount, small, chart, Evaluations.connected_total
    separated.parents first,
    Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_lt_of_quarter_bounds
      (separated.total_close.trans
      (quarter_lt_for_evaluation
      request.separated.positive)) totalClose,
    Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_lt_of_quarter_bounds
      separated.integral_close totalClose,
      Purelib.Data.Gaussian.Norm.Bounds.normSq_sub_lt_of_quarter_bounds
      separated.area_close areaClose,
    Evaluations.coordinateConnections separated.parents request.junctions ((Data.Nat.Order.le_max_right _ _).trans
      readingIndices),
    (Data.Nat.Order.le_max_right _ _).trans readingIndices⟩

/-- Consume one shared cap sample and reading stage. All acquisition paths use the same constructor for the complete
connected boundary. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest prepared
  totalTarget areaTarget minimum)
    (sample : Primitives.Sample cap differential index box) (depth readingIndex : Nat)
    (later : request.index ≤ index) (readingLater : request.readingIndex ≤ readingIndex) :
      Evaluation request sample depth
      readingIndex :=
  request.evaluateWithSeparated
    (request.separated.evaluate sample depth readingIndex later
      ((Data.Nat.Order.le_max_left _ _).trans (request.readingIndex_eq.ge.trans readingLater))) readingLater

end

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest in
/-- Compare full traces at a supplied common primitive origin. The endpoint term is paid using the very totals cached by
this evaluation. -/
theorem Evaluation.trace_error {request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest
  prepared totalTarget areaTarget minimum}
    {sample : Primitives.Sample cap differential index box} {depth readingIndex : Nat}
    (evaluated : Evaluation request sample
      depth readingIndex) (start : InverseRootPolynomial.Gaussian) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.traceArea start (evaluated.separated.parents.pairs.map
      Prod.fst).flatten -
      IncrementArea.traceArea start (evaluated.blocks.map (fun block => block.1 :: block.2)).flatten) <
        2 * (areaTarget + 4 * Data.Gaussian.Norm.Basic.normSq start * totalTarget) := by
  rw [IncrementArea.traceArea_eq, IncrementArea.traceArea_eq,
    ← evaluated.separated.left.area_eq, ← evaluated.cap.area_eq,
    ← evaluated.separated.left.total_eq, ← evaluated.cap.total_eq]
  have identity : evaluated.separated.left.area + BoundaryRibbon.area start evaluated.separated.left.total -
      (evaluated.cap.area + BoundaryRibbon.area start evaluated.cap.total) =
      (evaluated.separated.left.area - evaluated.cap.area) +
        BoundaryRibbon.area start (evaluated.separated.left.total - evaluated.cap.total) := by
    apply Data.Gaussian.Basic.ext <;> simp only [BoundaryRibbon.area, Data.Gaussian.Basic.conj,
      Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
      Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im, -eq_self, -iff_self] <;> ring1
  rw [identity]
  have endpointBound : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area start
    (evaluated.separated.left.total - evaluated.cap.total)) ≤
      4 * Data.Gaussian.Norm.Basic.normSq start * totalTarget :=
    (BoundaryRibbon.area_bound _ _).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct evaluated.total_close.le
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Data.Gaussian.Norm.Basic.normSq_nonneg start)))
  exact (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl endpointBound) (by decide)).trans_lt
      (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
        (Fraction.Order.Arithmetic.add_lt_add_right_direct evaluated.area_close _)))

set_option genInjectivity false in
/-- One cached cap polynomial sample and its complete connected-side evaluation at the retained request stages. -/
structure Acquisition (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest prepared
  totalTarget areaTarget minimum) (depth : Nat) where
  /-- The actual cap sample cached at the request's original model index and collar box. -/ sample : Primitives.Sample
    cap differential request.index collar.box
  /-- The connected-side evaluation consuming this exact cached sample at the retained reading stage. -/ evaluated :
    Evaluation request sample depth
    request.readingIndex

constructive_injectivity Acquisition

/-- Cache one cap sample at the retained model stage and evaluate the complete connected side using that same sample. -/
@[expose] def acquire (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide.ConnectedRequest prepared
  totalTarget areaTarget minimum) (depth : Nat) :
  Acquisition request depth :=
  let sample := Primitives.Sample.build cap differential request.index collar.box
  ⟨sample, request.evaluate sample depth request.readingIndex le_rfl le_rfl⟩

end ConnectedRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
