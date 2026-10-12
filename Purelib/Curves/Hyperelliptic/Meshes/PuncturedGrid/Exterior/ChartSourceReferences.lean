module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Riemann

open Purelib

@[expose] public section

/-! The actual paired chart bank supplies both shared-face references.
No regular-chart alignment or independently sampled source primitive is used. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target requested : Normalization.InverseRootPolynomial.Coordinate} {minimum depth :
    Nat}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}
  {request : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest plan.parents depth requested}
  (evaluated : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation request)

set_option genInjectivity false in
/-- Two shared-face primitive references retained by one actual paired chart evaluation.

Their original source budgets and values identify both components of the same joined chart path, whose area error is
paid by the chart request. -/
structure ChartSources where
  /-- The original paired source data retained by this evaluation. -/ retained :
    Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests.Sources evaluated
  /-- The first differential's reference on the original entered occurrence. -/ first :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference occurrence.compared.entered target
  /-- The recast second differential's reference on that same occurrence. -/ second :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference (occurrence.recastComparison other).entered
    target
  /-- The first reference uses exactly the source plan's retained first budget. -/ first_budget : first.budget =
    plan.first
  /-- The second reference uses exactly the source plan's retained second budget. -/ second_budget : second.budget =
    plan.second
  /-- The first reference equals the sum of the retained chart-source first increments. -/ first_value : first.value =
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests.firstIncrements
    evaluated retained.entries)
  /-- The second reference equals the sum of the same retained chart-source second increments. -/ second_value :
    second.value = Data.Gaussian.Norm.Sum.Basic.gaussianSum
    (Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests.secondIncrements evaluated retained.entries)
  /-- The joined chart replacement of the evaluation's actual flattened source paths. -/ joined :
    Normalization.ReciprocalDiskCommonSourceCharts.SourceComparisonRequest.PathReplacement evaluated.sourcePaths.flatten
  /-- The joined chart's first total is exactly the retained first reference value. -/ joined_first :
    joined.chart.totalValue.left = first.value
  /-- The joined chart's second total is exactly the retained second reference value. -/ joined_second :
    joined.chart.totalValue.right = second.value
  /-- The original source-path area and the joined chart area differ by less than the requested tolerance. -/
    joined_accurate : Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area evaluated.sourcePaths.flatten -
    joined.chart.areaValue) < requested

constructive_injectivity ChartSources

/-- Construct both original shared-face references and their joined chart from one retained paired evaluation. -/
def chartSources : Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences.ChartSources evaluated := by
  let retained := Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests.sources evaluated
  have firstLater : plan.first.minimumIndex ≤ retained.first.val.minimumIndex := by
    rw [retained.first.property.2, plan.floor_eq]
    exact (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)
  have secondLater : plan.second.minimumIndex ≤ retained.second.val.minimumIndex := by
    rw [retained.second.property.2, plan.floor_eq]
    exact (Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)
  let joined := Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts request
    evaluated
  have total := Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests.joinedCharts_total_readback evaluated
    retained.entries
  exact ⟨retained, Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference.ofRequest plan.first
    retained.first.val firstLater plan.positive,
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference.ofRequest plan.second retained.second.val
      secondLater plan.positive,
    rfl, rfl, retained.first.property.1, retained.second.property.1,
    joined, (congrArg Topology.Polygon.Stokes.PrimitivePoint.left total).trans retained.first.property.1.symm,
    (congrArg Topology.Polygon.Stokes.PrimitivePoint.right total).trans retained.second.property.1.symm,
    Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts.ChartBankRequest.Evaluation.joinedCharts_accurate request
      evaluated⟩

/-- The first shared-face edge increment approximates the first component of the retained joined chart.

The common late stage pays the original first source budget. -/
theorem ChartSources.joined_first_accurate (sources :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences.ChartSources evaluated) {faceIndex : Nat} (later :
  plan.index ≤ faceIndex)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement occurrence.placement.location -
      sources.joined.chart.totalValue.left) < target := by
  have after : sources.first.budget.grid.index ≤ faceIndex := by
    rw [sources.first_budget]
    exact ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)).trans later
  have accurate := Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences.reference_accurate occurrence.compared
    occurrence.aligned sources.first after shared
  rw [sources.joined_first]
  exact accurate

/-- The second shared-face edge increment approximates the second component of the same joined chart.

Recasting preserves the original occurrence and the common stage pays its second source budget. -/
theorem ChartSources.joined_second_accurate (sources :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences.ChartSources evaluated) {faceIndex : Nat} (later :
  plan.index ≤ faceIndex)
    (shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other faceIndex domains) :
    Data.Gaussian.Norm.Basic.normSq (shared.edgeIncrement occurrence.placement.location -
      sources.joined.chart.totalValue.right) < target := by
  have after : sources.second.budget.grid.index ≤ faceIndex := by
    rw [sources.second_budget]
    exact ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)).trans later
  have accurate := Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences.reference_accurate
    (occurrence.recastComparison other)
    (occurrence.recastComparison_aligned other) sources.second after shared
  rw [sources.joined_second]
  exact accurate

set_option genInjectivity false in
/-- The two original shared-face references for one retained paired boundary evaluation.

Both source budgets and component values are identified with that evaluation's cached path. -/
structure BoundaryReferences {request : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.BoundaryBankRequest
  plan.parents requested}
    (boundary : request.Evaluation) where
  /-- The original paired source data retained by this evaluation. -/ retained :
    Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.Sources boundary
  /-- The first differential's reference on the original entered occurrence. -/ first :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference occurrence.compared.entered target
  /-- The recast second differential's reference on that same occurrence. -/ second :
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference (occurrence.recastComparison other).entered
    target
  /-- The first reference uses exactly the source plan's retained first budget. -/ first_budget : first.budget =
    plan.first
  /-- The second reference uses exactly the source plan's retained second budget. -/ second_budget : second.budget =
    plan.second
  /-- The first reference is exactly the first total of the retained boundary path. -/ first_value : first.value =
    retained.path.totalValue.left
  /-- The second reference is exactly the second total of that same path. -/ second_value : second.value =
    retained.path.totalValue.right

constructive_injectivity BoundaryReferences

/-- Build both source references from one retained boundary evaluation and its original paired source plan. -/
def boundaryReferences {request : Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.BoundaryBankRequest
  plan.parents requested}
    (boundary : request.Evaluation) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences.BoundaryReferences (plan := plan) boundary := by
  let retained := Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.sources boundary
  have firstLater : plan.first.minimumIndex ≤ retained.first.val.minimumIndex := by
    rw [retained.first.property.2, plan.floor_eq]
    exact (Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)
  have secondLater : plan.second.minimumIndex ≤ retained.second.val.minimumIndex := by
    rw [retained.second.property.2, plan.floor_eq]
    exact (Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)
  have total := retained.path.total_eq.trans
    (Hyperelliptic.Charts.Reciprocal.Disk.BoundarySourceRequests.sourcePaths_total boundary retained.entries)
  exact ⟨retained, Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference.ofRequest plan.first
    retained.first.val firstLater plan.positive,
    Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences.Reference.ofRequest plan.second retained.second.val
      secondLater plan.positive, rfl, rfl,
    retained.first.property.1.trans (congrArg Topology.Polygon.Stokes.PrimitivePoint.left total).symm,
    retained.second.property.1.trans (congrArg Topology.Polygon.Stokes.PrimitivePoint.right total).symm⟩

/-- Both shared-face increments approximate the corresponding components of the same retained boundary path at the
common late stage. -/
theorem BoundaryReferences.shared_accurate {request :
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.BoundaryBankRequest plan.parents requested}
    {boundary : request.Evaluation} (references :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences.BoundaryReferences (plan := plan) boundary)
    {faceIndex : Nat} (later : plan.index ≤ faceIndex)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential faceIndex domains)
      (second : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other faceIndex domains) :
    Data.Gaussian.Norm.Basic.normSq (first.edgeIncrement occurrence.placement.location -
      references.retained.path.totalValue.left) < target ∧
      Data.Gaussian.Norm.Basic.normSq (second.edgeIncrement occurrence.placement.location -
        references.retained.path.totalValue.right) < target := by
  have firstLater : references.first.budget.grid.index ≤ faceIndex := by
    rw [references.first_budget]
    exact ((Nat.Order.le_max_left _ _).trans (Nat.Order.le_max_right _ _)).trans later
  have secondLater : references.second.budget.grid.index ≤ faceIndex := by
    rw [references.second_budget]
    exact ((Nat.Order.le_max_right _ _).trans (Nat.Order.le_max_right _ _)).trans later
  have firstBound := Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences.reference_accurate
    occurrence.compared occurrence.aligned references.first firstLater first
  have secondBound := Hyperelliptic.Meshes.PuncturedGrid.SegmentPrimitiveReferences.reference_accurate
    (occurrence.recastComparison other)
    (occurrence.recastComparison_aligned other) references.second secondLater second
  rw [references.first_value] at firstBound
  rw [references.second_value] at secondBound
  exact ⟨firstBound, secondBound⟩

set_option genInjectivity false in
/-- The physical occurrence's retained path supplies every cross-parent
sheet join. Only the path's two outer radial ends remain in this comparison. -/
structure BoundaryComparison (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  occurrence other target minimum) (requested : Normalization.InverseRootPolynomial.Coordinate) where
  /-- The quarter-target paired boundary request on the original parent plan. -/ request :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.BoundaryBankRequest plan.parents (requested / 4)
  /-- The quarter-target connector request linking those same retained boundary parents. -/ linked :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.LinkedRequest request (requested / 4)
  /-- The successful linked boundary certificate for this exact request. -/ certified : linked.Certificate
  /-- Both original shared-face references for the certified retained boundary. -/ references :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences.BoundaryReferences (plan := plan)
    certified.boundary
  /-- The certified linked boundary area meets the complete requested tolerance. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq certified.area < requested

constructive_injectivity BoundaryComparison

/-- Acquire a bounded linked paired boundary from the original occurrence's retained root chain.

Two quarter-target requests pay the combined boundary error while preserving both original shared-face references. -/
def boundaryComparison (plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan
  occurrence other target minimum)
    (requested : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < requested)
    (branch : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 1) :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences.BoundaryComparison plan requested := by
  have quarterPositive := Fraction.Order.Field.div_pos_direct positive (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)
  let request := Hyperelliptic.Charts.Reciprocal.Disk.PairedParentBoundaries.BoundaryBankRequest.build
    plan.parents (requested / 4) quarterPositive
  let linked := Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.LinkedRequest.build
    request (requested / 4) quarterPositive
    (Nonempty.map (fun chain => chain.toDirectPathChain) occurrence.compared.entered.cache.chain)
    (RootContinuation.PreparedCachedParentRoots.ParentCache.rootChain occurrence.compared.entered.cache)
  let certified := linked.acquire linked.index le_rfl branch
  have paid : 2 * (requested / 4 + requested / 4) = requested := by
    calc
      _ = (requested / 4) * 4 := by ring1
      _ = requested := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  exact ⟨request, linked, certified,
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences.boundaryReferences certified.boundary,
    certified.bounded.trans_eq paid⟩

/-- The bounded cap expression is written using the full source path area
from these exact shared-face references. Chords, parent polygon, origins and
the two remaining outer radial ends are retained with their signs. -/
theorem BoundaryComparison.path_bounded (comparison :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences.BoundaryComparison plan requested) :
    Data.Gaussian.Norm.Basic.normSq (comparison.references.retained.path.areaValue +
      comparison.references.retained.chords -
      comparison.references.retained.polygon.areaValue - comparison.certified.boundary.correction +
      Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.internalConnectors
        comparison.certified.boundary +
      FiniteSum.Fin.sumFin (Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.parentConnector
        comparison.certified.boundary) +
      Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.outerBoundary comparison.certified.boundary)
        < requested := by
  have equal : comparison.references.retained.path.areaValue + comparison.references.retained.chords -
      comparison.references.retained.polygon.areaValue - comparison.certified.boundary.correction +
      Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.internalConnectors
        comparison.certified.boundary +
      FiniteSum.Fin.sumFin (Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.parentConnector
        comparison.certified.boundary) +
      Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.outerBoundary comparison.certified.boundary
        = comparison.certified.area := by
    rw [comparison.references.retained.path_area, comparison.certified.boundary_eq]
    unfold Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryClosure.Evaluation.linkedBoundary
    ring1
  exact equal ▸ comparison.bounded

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ChartSourceReferences
