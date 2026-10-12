module
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges
import Purelib.Integration.Path.CenteredPathIncrements
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Path.JoinedTraceIncrements
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedClosedBoundary
import Init.Data.List.Lemmas
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAdjacency
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Join the existing parity-independent parent chart bank. Shared cap
certificates and retained endpoint owners cancel all even-chart connectors. -/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace

open Purelib
open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges
open Purelib.Geometry.Path.Gaussian
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path.JoinedTrace
open Purelib.Integration.Path.JoinedTraceIncrements
open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings.PrimitiveAreaBounds
open Purelib.Riemann.Topology
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request Plan)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartBankRequest ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest (Evaluation)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Join)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

/-- Join the complete original finite trace bank with all connectors, using a single zero vertex for an empty bank. -/
@[expose] def joinedTrace {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint) :
  JoinedTrace.VertexTrace PrimitivePoint :=
  match n, traces with
  | 0, _ => ⟨PrimitivePoint.zero, []⟩
  | _ + 1, traces => VertexTrace.concatenate traces

/-- The complete original joined area retains every actual trace area and each intervening endpoint connector. -/
private theorem joinedTrace_area {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint) :
    (joinedTrace traces).area id =
      FiniteSum.Fin.sumFin (fun i => (traces i).area id) +
      FiniteSum.Fin.sumFin (fun i : Fin (n - 1) => Stokes.edgeArea (traces ⟨i.val, by omega0⟩).last
        (traces ⟨i.val + 1, by omega0⟩).first) := by
  cases n with
  | zero => change (0 : InverseRootPolynomial.Gaussian) = 0 + 0; ring1
  | succ n =>
      rw [joinedTrace, VertexTrace.concatenate_area,
        VertexTrace.joiningArea_ofFn]
      rfl

/-- The joined nonempty original trace bank starts at its actual first retained endpoint. -/
private theorem joinedTrace_first {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint)
    (positive : 0 < n) : (joinedTrace traces).first
      = (traces ⟨0, positive⟩).first := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ n => exact VertexTrace.glue_first _ _

/-- The joined nonempty original trace bank ends at its actual last retained endpoint. -/
private theorem joinedTrace_last {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint)
    (positive : 0 < n) : (joinedTrace traces).last =
      (traces ⟨n - 1, by omega0⟩).last := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ positive).elim
  | succ n => exact VertexTrace.concatenate_last traces

/-- The total change from inserting all actual original trace connectors satisfies the retained squared-count gap bound.
-/
private theorem joinedTrace_total_insertion {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint)
    {error : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ error)
    (gaps : ∀ i : Fin (n - 1), PrimitivePoint.Bounded
      ((traces ⟨i.val + 1, by omega0⟩).first.sub
      (traces ⟨i.val, by omega0⟩).last) error) :
    PrimitivePoint.Bounded
      ((PairedIncrementArea.total (List.ofFn (fun i => VertexTrace.increments (traces i) id)).flatten).sub
      (PairedIncrementArea.total (VertexTrace.increments
        (joinedTrace traces) id)))
      (((2 * n - 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * error) := by
  cases n with
  | zero =>
      constructor <;> change Data.Gaussian.Basic.Canonical.normSq (0 - 0) ≤ (0 : InverseRootPolynomial.Coordinate)^2 *
        error <;>
        rw [sub_self, Data.Gaussian.Basic.Canonical.normSq_zero] <;>
        simp only [zero_pow (by decide : 2 ≠ 0), zero_mul, -eq_self, -iff_self] <;> exact le_rfl
  | succ n =>
      rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega0]
      exact PairedChartTrace.concatenate_total_insertion traces nonnegative gaps

/-- The area change from inserting all actual original trace connectors satisfies the retained fourth-power count and
magnitude bound. -/
private theorem joinedTrace_area_insertion {n : Nat} (traces : Fin n → JoinedTrace.VertexTrace Stokes.PrimitivePoint)
    {error magnitude : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ error) (magnitudeNonnegative : 0 ≤
      magnitude)
    (small : error ≤ magnitude)
    (totals : ∀ i, PrimitivePoint.Bounded
      (PairedIncrementArea.total (VertexTrace.increments (traces i) id)) magnitude)
    (gaps : ∀ i : Fin (n - 1), PrimitivePoint.Bounded
      ((traces ⟨i.val + 1, by omega0⟩).first.sub
      (traces ⟨i.val, by omega0⟩).last) error) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (List.ofFn (fun i => VertexTrace.increments
      (traces i) id)).flatten -
      PairedIncrementArea.area (VertexTrace.increments
        (joinedTrace traces) id)) ≤
      32 * ((2 * n - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * error * magnitude := by
  cases n with
  | zero =>
      change Data.Gaussian.Norm.Basic.normSq (0 - 0) ≤ 32 * (0 : InverseRootPolynomial.Coordinate)^4 * error *
        magnitude
      rw [sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      simp only [zero_pow (by decide : 4 ≠ 0), mul_zero, zero_mul, -eq_self, -iff_self]
      exact le_rfl
  | succ n =>
      rw [show 2 * (n + 1) - 1 = 2 * n + 1 by omega0]
      exact PairedChartTrace.concatenate_area_insertion traces nonnegative magnitudeNonnegative small totals gaps

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

/-- The physical and root-owner join between the original last chart point of one retained parent and the first of
another. -/
@[expose] def EndpointJoin (request : PairedParentCharts.ChartBankRequest original depth requested) (i j : Fin
  original.plans.length) :=
  ArcOwners.Join (ChartRequest.lastPoint (request.plans.get i)) (ChartRequest.firstPoint (request.plans.get j))

/-- Read the physical and root joins from the retained parent chain, for either parity. No radial fan certificate is
needed for this construction. -/
@[expose] def sourceJoins (request : PairedParentCharts.ChartBankRequest original depth requested)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents
      (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (i : Fin (original.plans.length - 1)) :
    EndpointJoin request ⟨i.val, by omega0⟩ ⟨i.val +
      1, by omega0⟩ := by
  have physical : ∀ k h, PairedBoundaryClosure.PhysicalAt (original.plans.map Plan.parent) k h := by
    obtain ⟨chain⟩ := chain
    exact PairedBoundaryClosure.physicalAt (original.parents_eq.symm ▸ chain)
  let retained : PreparedRefinementRootChains.RootChain
      (original.plans.map Plan.parent) first last := original.parents_eq.symm ▸ roots
  have bound : i.val + 1 < (original.plans.map Plan.parent).length := by
    rw [Data.List.Map.length_map]
    omega0
  have same := physical i.val bound
  let link := PairedBoundaryClosure.rootAt retained i.val bound
  have leftMapped := Data.List.Map.getElem_map Plan.parent original.plans i.val
    (PairedBoundaryClosure.leftParent i).isLt ((Nat.lt_succ_self i.val).trans bound)
  have rightMapped := Data.List.Map.getElem_map Plan.parent original.plans (i.val + 1)
    (PairedBoundaryClosure.rightParent i).isLt bound
  rw [PairedBoundaryClosure.PhysicalAt, leftMapped, rightMapped] at same
  rw [PairedBoundaryClosure.RootAt, leftMapped, rightMapped] at link
  apply ReciprocalDiskArcOwners.sourceEndpointJoin _ _
    (ChartRequest.lastParameter_eq (request.plans.get ⟨i.val, by omega0⟩))
    (ChartRequest.firstParameter_eq (request.plans.get ⟨i.val + 1, by omega0⟩))
  · dsimp only [PairedParentCharts.ChartParent]
    convert same using 1 <;> rfl
  · dsimp only [PairedParentCharts.ChartParent]
    convert link using 1 <;> rfl

/-- The actual connector between two original parent chart traces has zero area in the unramified chart when their
retained owners join. -/
theorem Evaluation.regular_parent_connector_zero (evaluated : ChartBankRequest.Evaluation request)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (i j : Fin original.plans.length) (owners :
      EndpointJoin request i j) :
    Stokes.edgeArea (Evaluation.chartTrace (evaluated.entries.get i)).last
      (Evaluation.chartTrace (evaluated.entries.get j)).first = 0 := by
  rw [Evaluation.chartTrace_last (evaluated.entries.get i),
    Evaluation.chartTrace_first (evaluated.entries.get j)]
  exact Evaluation.regular_join_area
    (((evaluated.entries.get i).entries.get (PairedParentCharts.ChartParent original
      i).common.lastIndex).evaluated.chart.retained.area.evaluated.readings.get
    (Fin.last ((request.plans.get i).plans.get (PairedParentCharts.ChartParent original
      i).common.lastIndex).geometry.tail.length))
    (((evaluated.entries.get j).entries.get (PairedParentCharts.ChartParent original
      j).common.firstIndex).evaluated.chart.retained.area.evaluated.readings.get 0)
    owners ((evaluated.shared j).1.trans (evaluated.shared i).1.symm)
      ((evaluated.shared j).2.trans (evaluated.shared i).2.symm) unramified

/-- Construct the actual original last-to-first parent chart join from the retained physical closure and root return. -/
@[expose] def closingJoin (request : PairedParentCharts.ChartBankRequest original depth requested)
    (positive : 0 < original.plans.length)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents
      (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate)
    (returned : Gaussian.Equivalence.NamedEquivalent last first) :
    EndpointJoin request ⟨original.plans.length - 1,
      by omega0⟩ ⟨0, positive⟩ := by
  have present : 0 < (original.plans.map Plan.parent).length := by rw [Data.List.Map.length_map]; exact positive
  have same : ((original.plans.map Plan.parent)[(original.plans.map Plan.parent).length - 1]'(by omega0)).edge.point 1 =
      ((original.plans.map Plan.parent)[0]'present).edge.point 0 := by
    obtain ⟨chain⟩ := chain
    have retained : PreparedDirectDyadicRefinements.DirectPathChain (original.plans.map Plan.parent)
        (start := start) (finish := finish) := original.parents_eq.symm ▸ chain
    exact (PairedClosedBoundary.last_coordinate retained present).trans
      (closed.symm.trans (PairedClosedBoundary.first_coordinate retained present).symm)
  let retained : PreparedRefinementRootChains.RootChain
      (original.plans.map Plan.parent) first last := original.parents_eq.symm ▸ roots
  let link := (PairedClosedBoundary.rootLast retained present).trans
    (returned.trans (PairedClosedBoundary.rootFirst retained present))
  simp only [Data.List.Map.length_map, -eq_self, -iff_self] at same link
  have lastMapped := Data.List.Map.getElem_map Plan.parent original.plans (original.plans.length - 1)
    (PairedClosedBoundary.lastParent positive).isLt (by
        rw [Data.List.Map.length_map];
        exact (PairedClosedBoundary.lastParent positive).isLt)
  have firstMapped := Data.List.Map.getElem_map Plan.parent original.plans 0 positive present
  rw [lastMapped, firstMapped] at same link
  apply ReciprocalDiskArcOwners.sourceEndpointJoin _ _
    (ChartRequest.lastParameter_eq (request.plans.get ⟨original.plans.length - 1, by omega0⟩))
    (ChartRequest.firstParameter_eq (request.plans.get ⟨0, positive⟩))
  · dsimp only [PairedParentCharts.ChartParent]
    convert same using 1; rfl
  · dsimp only [PairedParentCharts.ChartParent]
    convert link using 1; rfl

/-- The complete original parent chart trace retaining every actual joining edge. -/
@[expose] def Evaluation.regularTrace (evaluated : ChartBankRequest.Evaluation request) : JoinedTrace.VertexTrace
  PrimitivePoint :=
  joinedTrace (fun i => (Evaluation.chartTrace
    (evaluated.entries.get i)))

/-- The original regular parent trace starts at the actual first retained parent chart endpoint. -/
theorem Evaluation.regularTrace_first (evaluated : ChartBankRequest.Evaluation request) (positive : 0 <
  original.plans.length) :
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated).first =
      (Evaluation.chartTrace (evaluated.entries.get ⟨0, positive⟩)).first :=
  joinedTrace_first _ positive

/-- The original regular parent trace ends at the actual last retained parent chart endpoint. -/
theorem Evaluation.regularTrace_last (evaluated : ChartBankRequest.Evaluation request) (positive : 0 <
  original.plans.length) :
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated).last =
      (Evaluation.chartTrace (evaluated.entries.get ⟨original.plans.length - 1, by omega0⟩)).last :=
  joinedTrace_last _ positive

/-- The unclosed increment list retains its actual endpoint difference. -/
theorem Evaluation.regularTrace_increment_total (evaluated : ChartBankRequest.Evaluation request) :
    PairedIncrementArea.total ((VertexTrace.increments
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated) id)) =
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated).last.sub
        (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated).first :=
        by
  let trace := (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated)
  have total := CenteredPathIncrements.increments_total (fun vertex => id (trace.indexed vertex))
  rw [VertexTrace.indexed_increments trace id] at total
  change PairedIncrementArea.total ((VertexTrace.increments trace id)) =
    (DyadicTrace.indexed trace.first trace.rest (Fin.last trace.rest.length)).sub trace.first at total
  rw [DyadicTrace.indexed_last] at total
  exact total

/-- Transport separate parent totals to the actual glued trace, retaining the error from every independently sampled
joining endpoint. -/
theorem Evaluation.regularTrace_total_insertion (evaluated : ChartBankRequest.Evaluation request)
    {error : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ error)
    (gaps : ∀ i : Fin (original.plans.length - 1),
      PrimitivePoint.Bounded
        ((Evaluation.chartTrace (evaluated.entries.get ⟨i.val + 1, by omega0⟩)).first.sub
        (Evaluation.chartTrace (evaluated.entries.get ⟨i.val, by omega0⟩)).last) error) :
    PrimitivePoint.Bounded
      ((PairedIncrementArea.total (List.ofFn (fun i : Fin original.plans.length =>
      VertexTrace.increments (Evaluation.chartTrace (evaluated.entries.get i)) id)).flatten).sub
      (PairedIncrementArea.total ((VertexTrace.increments
        (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated) id))))
      (((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^2 * error) :=
  joinedTrace_total_insertion _ nonnegative gaps

/-- The original separate-parent and joined trace areas satisfy the retained complete insertion error bound. -/
theorem Evaluation.regularTrace_area_insertion (evaluated : ChartBankRequest.Evaluation request)
    {error magnitude : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ error) (magnitudeNonnegative : 0 ≤
      magnitude)
    (small : error ≤ magnitude)
    (totals : ∀ i, PrimitivePoint.Bounded
      (PairedIncrementArea.total (VertexTrace.increments (Evaluation.chartTrace (evaluated.entries.get i)) id))
        magnitude)
    (gaps : ∀ i : Fin (original.plans.length - 1),
      PrimitivePoint.Bounded
        ((Evaluation.chartTrace (evaluated.entries.get ⟨i.val + 1, by omega0⟩)).first.sub
        (Evaluation.chartTrace (evaluated.entries.get ⟨i.val, by omega0⟩)).last) error) :
    Data.Gaussian.Norm.Basic.normSq (PairedIncrementArea.area (List.ofFn (fun i : Fin original.plans.length =>
      VertexTrace.increments (Evaluation.chartTrace (evaluated.entries.get i)) id)).flatten -
      PairedIncrementArea.area ((VertexTrace.increments
        (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated) id))) ≤
      32 * ((2 * original.plans.length - 1 : Nat) : InverseRootPolynomial.Coordinate)^4 * error * magnitude :=
  joinedTrace_area_insertion _ nonnegative
    magnitudeNonnegative small totals gaps

/-- Increment area already includes the closing-edge correction of the absolute vertex trace, even when its sampled
endpoints differ. -/
theorem Evaluation.regularTrace_increment_area (evaluated : ChartBankRequest.Evaluation request) :
    PairedIncrementArea.area ((VertexTrace.increments
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated) id)) =
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated).area id +
        Stokes.edgeArea (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace
        evaluated).last (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace
        evaluated).first := by
  let trace := (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated)
  have traced := CenteredPathIncrements.increments_trace (fun vertex => id (trace.indexed vertex))
  rw [VertexTrace.indexed_increments trace id, PairedIncrementArea.traceArea_eq,
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace_increment_total
      evaluated] at traced
  have same := traced.trans (trace.indexed_area id)
  change PairedIncrementArea.area ((VertexTrace.increments trace id)) +
    Stokes.edgeArea trace.first (trace.last.sub trace.first) = trace.area id at same
  have edge : Stokes.edgeArea trace.first (trace.last.sub trace.first) = -Stokes.edgeArea trace.last trace.first := by
    simp only [Stokes.edgeArea, PrimitivePoint.sub, -eq_self, -iff_self]
    ring1
  rw [edge] at same
  calc
    _ = (PairedIncrementArea.area ((VertexTrace.increments trace id)) + -Stokes.edgeArea trace.last trace.first) +
        Stokes.edgeArea trace.last trace.first := by ring1
    _ = _ := congrArg (fun area => area + Stokes.edgeArea trace.last trace.first) same

/-- The actual concatenated parent trace reads exactly the bank's cached area. The hypothesis supplies owner joins, not
numerical root equalities. -/
theorem Evaluation.regularTrace_area (evaluated : ChartBankRequest.Evaluation request)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (owners : ∀ i : Fin (original.plans.length - 1),
      EndpointJoin request ⟨i.val, by omega0⟩ ⟨i.val
        + 1, by omega0⟩) :
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated).area id =
      evaluated.chartArea := by
  rw [Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace,
    joinedTrace_area]
  have intervals := FiniteSum.Fin.sumFin_congr (fun i => ReciprocalRegularChartJoins.regular_chartTrace_area
    (evaluated.entries.get i) unramified)
  have connectors := FiniteSum.Fin.sumFin_congr (fun i =>
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regular_parent_connector_zero
    evaluated unramified _ _ (owners i))
  rw [intervals, connectors, FiniteSum.Fin.sumFin_zero, add_zero]
  exact evaluated.chartArea_eq.symm

/-- The complete original regular chart trace reads the cached parent-bank area using owner joins derived from its
retained physical and root chains. -/
theorem Evaluation.regularTrace_area_of_chain (evaluated : ChartBankRequest.Evaluation request)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents
      (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last) :
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated).area id =
      evaluated.chartArea :=
  Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace_area evaluated unramified
    (sourceJoins request chain roots)

/-- Closing the retained trace adds zero determinant area. This statement does not identify the two endpoint samples or
discard their increment. -/
theorem Evaluation.regularTrace_closed_area (evaluated : ChartBankRequest.Evaluation request)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (positive : 0 < original.plans.length)
    {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : Nonempty (PreparedDirectDyadicRefinements.DirectPathChain parents
      (start := start) (finish := finish)))
    {first last : Gaussian.Name.Basic.Named}
    (roots : PreparedRefinementRootChains.RootChain parents first last)
    (closed : start.coordinate = finish.coordinate)
    (returned : Gaussian.Equivalence.NamedEquivalent last first) :
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated).area id +
      Stokes.edgeArea (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace
        evaluated).last (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace
        evaluated).first = evaluated.chartArea := by
  have closing :=
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regular_parent_connector_zero
    evaluated unramified _ _
    (closingJoin request positive chain roots closed
      returned)
  have lastEq := joinedTrace_last (fun i =>
    (Evaluation.chartTrace (evaluated.entries.get i))) positive
  have firstEq := joinedTrace_first (fun i =>
    (Evaluation.chartTrace (evaluated.entries.get i))) positive
  change (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated).last =
    _ at lastEq
  change (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace evaluated).first =
    _ at firstEq
  rw [lastEq, firstEq, closing, add_zero]
  exact Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace.Evaluation.regularTrace_area_of_chain
    evaluated unramified chain roots

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
