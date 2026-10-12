module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalCapPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedCharts
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ConnectedSide
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularPathRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularSides
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideChartConnections
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SideRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RamifiedReciprocalAreaComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Data.Rat

open Purelib.Integration.Path

/-!
# Chart replacement of the original parity-selected surface request

The regular case retains its existing path. The ramified case acquires
charts and builds the original face reference from those same source
samples. Source, subdivision, and reading maxima precede their acquisitions.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh (SegmentComparison)
open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment
    curve.polynomial (Purelib.Curves.Hyperelliptic.Branches.Cuts.Ambient curve) start finish}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {piece :
    Purelib.Riemann.Paths.PreparedPathDecomposition.CoveredSegment segment owner}
  {placement : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace mesh segment} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {parentSheet : Fin 2}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {compared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
    placement piece differential parentSheet}
  {prepared :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapPreparation
    regular compared} {target areaTarget chartTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate}
    {floor : Nat}

/-- The chart request determined by the original cap parity case.

Regular requests retain their existing path; ramified requests carry an actual connected-chart replacement with its own
positive area allowance. -/
@[expose] def ChartRequest (request : SegmentComparison.CapRequest prepared target areaTarget floor) (chartTarget :
  InverseRootPolynomial.Coordinate) : Type 2 :=
  match request with
  | .regular _ => PUnit
  | .ramified _ original => ConnectedCharts.ChartRequest original.request chartTarget

namespace ChartRequest

variable {request :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.CapRequest prepared
  target areaTarget floor}

/-- Preserve the original regular request or prepare connected charts on the exact original ramified source request. -/
@[expose] def build (request : SegmentComparison.CapRequest prepared target areaTarget floor) (chartTarget :
  InverseRootPolynomial.Coordinate) (positive : 0 < chartTarget) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest request
  chartTarget :=
  match request with
  | .regular _ => ⟨⟩
  | .ramified _ original => ConnectedCharts.ChartRequest.build original.request chartTarget positive

/-- The common stage paying the retained original cap request and any actual ramified chart request. -/
@[expose] def index (charts :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest request
  chartTarget) : Nat :=
  match request, charts with
  | .regular original, _ => original.index
  | .ramified _ original, charts => max original.index (ConnectedCharts.ChartRequest.index charts)

/-- The actual ramified chart depth, with zero for an unchanged regular path. -/
@[expose] def depth (charts :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest request
  chartTarget) : Nat :=
  match request, charts with
  | .regular _, _ => 0
  | .ramified _ _, charts => ConnectedCharts.ChartRequest.depth charts

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- The retained chart stage also pays the original cap source request. -/
theorem source_le (charts :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest request
  chartTarget) : request.index ≤ charts.index := by
  cases request with
  | regular original => exact le_rfl
  | ramified degree original => exact Purelib.Data.Nat.Order.le_max_left _ _

variable {index : Nat} {box : Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- The parity-selected chart plan for the supplied exact original cap sample. -/
@[expose] def Plan (charts :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest request
  chartTarget) (sample : Primitives.Sample cap differential index box) : Type 2 :=
  match request, charts with
  | .regular _, _ => PUnit
  | .ramified _ _, charts => ConnectedCharts.ChartRequest.Plan charts sample

namespace Plan

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- Retain the regular case or prepare its actual ramified chart plan on the supplied cap sample. -/
@[expose] def build (charts :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest request
  chartTarget) (sample : Primitives.Sample cap differential index box) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan charts
  sample :=
  match request, charts with
  | .regular _, _ => ⟨⟩
  | .ramified _ _, charts => ConnectedCharts.ChartRequest.Plan.build charts sample

variable {charts :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest request
  chartTarget}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- The common retained reading stage paying the original comparison and any ramified chart plan. -/
@[expose] def stage (plan :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan charts
  sample) : Nat :=
  match request, charts, plan with
  | .regular original, _, _ => original.readingIndex
  | .ramified _ original, _, plan => max original.readingIndex (ConnectedCharts.ChartRequest.Plan.stage plan)

variable {depth readingIndex : Nat}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- The actual regular cap evaluation or ramified chart evaluation selected by the original request. -/
@[expose] def Data (plan :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan charts
  sample) (depth readingIndex : Nat) : Type 2 :=
  match request, charts, plan with
  | .regular original, _, _ => RegularCapRequest.Evaluation original sample depth readingIndex
  | .ramified _ _, _, plan => ConnectedCharts.ChartRequest.Plan.Evaluation plan depth readingIndex

namespace Data

variable {plan :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan
  charts sample}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest
  Plan.Data
  in
/-- Recover the original cap comparison from the same actual parity-selected evaluated data. -/
@[expose] def original (data :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data plan
  depth readingIndex) : CapRequest.Evaluation request sample depth readingIndex :=
  match request, charts, plan, data with
  | .regular _, _, _, data =>
      ⟨data, ((data.cap.original.parents.pairs.map Prod.fst).flatten, (data.cap.parents.pairs.map Prod.snd).flatten),
        rfl⟩
  | .ramified _ original, _, _, data =>
      let retained := ConnectedCharts.ChartRequest.Plan.Evaluation.original data
      let evaluated := original.evaluateWithCap retained
      ⟨evaluated, ((retained.separated.parents.pairs.map Prod.fst).flatten,
        (retained.blocks.map (fun block => block.1 :: block.2)).flatten), rfl⟩

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest
/-- Read the complete original regular path or retained ramified connected replacement path. -/
@[expose] def path (data :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data plan
  depth readingIndex) : List Gaussian :=
  match request, charts, plan, data with
  | .regular _, _, _, data => (data.cap.parents.pairs.map Prod.snd).flatten
  | .ramified _ _, _, _, data => data.connected.paths.flatten

/-- Read the cached summary of the exact retained parity-selected path. -/
@[expose] def summary (data :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data plan
  depth readingIndex) : IncrementArea.Summary data.path :=
  match request, charts, plan, data with
  | .regular _, _, _, data => data.cap.cap
  | .ramified _ _, _, _, data => data.connected.summary

end

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest
  Plan.Data
  in
/-- The actual replacement path preserves the original cap comparison total exactly. -/
theorem total_preserved (data :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data plan
  depth readingIndex) : data.summary.total = data.original.right.total := by
  cases request with
  | regular original => rfl
  | ramified degree original => exact data.total_eq

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest
  Plan.Data
  in
/-- The complete replacement area satisfies the independent positive chart allowance. -/
theorem area_error (data :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data plan
  depth readingIndex) (positive : 0 < chartTarget) :
    Data.Gaussian.Norm.Basic.normSq (data.summary.area - data.original.right.area) < chartTarget := by
  cases request with
  | regular original =>
      change Data.Gaussian.Norm.Basic.normSq (data.cap.cap.area - data.cap.cap.area) < chartTarget
      rw [Data.Gaussian.Basic.sub_self, Data.Gaussian.Norm.Basic.normSq_zero]
      exact positive
  | ramified degree original => exact data.area_error

end Data

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- Evaluate the original parity-selected request at the paid source, subdivision and reading stages. -/
@[expose] def evaluateData (plan :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan charts
  sample) (depth readingIndex : Nat)
    (later : charts.index ≤ index) (fineLater : charts.depth ≤ depth) (readingLater : plan.stage ≤ readingIndex) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data
      plan depth readingIndex := by
  cases request with
  | regular original => exact original.evaluate sample depth readingIndex later readingLater
  | ramified degree original =>
      exact ConnectedCharts.ChartRequest.Plan.evaluate plan depth readingIndex ((Purelib.Data.Nat.Order.le_max_right _
        _).trans later) fineLater ((Purelib.Data.Nat.Order.le_max_right _ _).trans readingLater)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
set_option genInjectivity false in
/-- The complete parity-selected chart replacement with its original cap comparison and exact total preservation.

The cached path and summary retain all actual increments and the independent chart-area discrepancy. -/
structure Evaluation (plan :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan charts
  sample) (depth readingIndex : Nat) where
  /-- The original parity-selected evaluated data retained by this cached comparison. -/ data :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Data
    plan depth readingIndex
  /-- The retained original cap comparison sharing the same actual evaluated data. -/ original : CapRequest.Evaluation
    request sample depth readingIndex
  /-- The retained original comparison is exactly the one read from the parity-selected data. -/ original_eq : original
    = data.original
  /-- The cached complete parity-selected replacement increment path. -/ path : List Data.Gaussian.Basic.Canonical
  /-- The cached replacement path is exactly that of the original parity-selected evaluation. -/ path_eq : path =
    data.path
  /-- The cached summary on that exact original replacement path. -/ summary : IncrementArea.Summary path
  /-- The cached replacement summary has exactly the original cap comparison total. -/ total_preserved : summary.total =
    original.right.total
  /-- The cached replacement area differs from the original cap area by less than the retained chart target. -/
    area_error : Data.Gaussian.Norm.Basic.normSq (summary.area - original.right.area) < chartTarget

constructive_injectivity Evaluation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest in
/-- Cache the actual parity-selected path, summary and original comparison with their exact total and area guarantees.
-/
@[expose] def evaluate (plan :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan charts
  sample) (positive : 0 < chartTarget) (depth readingIndex : Nat)
    (later : charts.index ≤ index) (fineLater : charts.depth ≤ depth) (readingLater : plan.stage ≤ readingIndex) :
      Evaluation
      plan depth readingIndex :=
  let data := plan.evaluateData depth readingIndex later fineLater readingLater
  let original := data.original
  ⟨data, original, rfl, data.path, rfl, data.summary, data.total_preserved, data.area_error positive⟩

namespace Evaluation

variable {plan :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan
  charts sample}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest
/-- The original source and complete replacement areas satisfy the combined original and chart error allowance. -/
theorem source_area_error (evaluated :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Evaluation
  plan depth readingIndex) :
    Data.Gaussian.Norm.Basic.normSq (evaluated.original.left.area - evaluated.summary.area) < 2 * (areaTarget +
      chartTarget) := by
  have reversed : Data.Gaussian.Norm.Basic.normSq (evaluated.original.right.area - evaluated.summary.area) <
    chartTarget := by
    rw [show evaluated.original.right.area - evaluated.summary.area = -(evaluated.summary.area -
      evaluated.original.right.area) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
    exact evaluated.area_error
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_via evaluated.original.left.area evaluated.original.right.area
    evaluated.summary.area).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct evaluated.original.area_close reversed))

/-- The original retained triangle-edge increment remains within the original integral target of the complete
replacement total. -/
theorem triangle_error (evaluated :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison.ChartRequest.Plan.Evaluation
  plan depth readingIndex)
    {domains : DomainBanks.FaceDomainBank frames faces.regulars} (aligned : compared.domains = domains.atRoute
      placement.location)
    {faceIndex : Nat} (later : request.budget.grid.index ≤ faceIndex) {shared : PrimitiveData.FacePrimitiveBank
      differential faceIndex domains}
    (readings : TrianglePrimitiveReadings.TriangleReadings shared mesh) :
    Data.Gaussian.Norm.Basic.normSq (placement.location.sourceEdge.increment readings.values -
      evaluated.summary.total) < target := by
  rw [evaluated.total_preserved]
  exact evaluated.original.triangle_error aligned later readings

end Evaluation
end Plan
end ChartRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison
