module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Energy.Polygon
import Purelib.Riemann.Branches.NewtonCutAnnulusProjection
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Topology.NewtonSewnExcision

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.List.Permutation
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Polygon.WitnessReadbacks

public import Purelib.Riemann.RootContinuation.NewtonOriginalLiftedBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

/-! Original enclosing-cell excision on actual cut triangles. Complete
projected cancellation retains cut jumps, endpoint defects and offsets. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Integration.Energy
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Branches.NewtonCutAnnulusProjection.BranchCellBank.NewtonGrid.AllHoleExcision
open Purelib.Riemann.Branches.NewtonCutPrimitiveArea
open Purelib.Riemann.Branches.NewtonCutPrimitiveArea.CutSourceWord
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.NewtonSewnExcision
open Purelib.Topology.Mesh
open Purelib.Topology.Mesh.TriangleSourceUniqueness
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
open Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation.ProjectedEdgePairing
open Purelib.Topology.Surface.Cut.PrimitiveJumps
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeListArea edgeArea
  edgeArea_reverse edgeListArea_append)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing (IncludedHoleSewing)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance (InnerOccurrences)
open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces (CutSourceWord)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.StemRequests (IncludedStemRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleRequests (IncludedHoleRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {target radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {current : LiftedPuncturedGrid grid.punctured}
  {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
    grid.faces.regulars} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {localValues : Fin current.mesh.triangles.length → Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
  {surface : Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample current.cutPolygon.patch localValues}

namespace OriginalCutBalance

/-- Every retained cut source edge projects to distinct endpoints on the actual lifted mesh. -/
theorem word_nonloop {sources : List (SewnPrimitiveContacts.SourceEdge current.mesh.triangles.length)}
    (word : CutSourceWord current.cutPolygon.patch.cut sources)
    (edge : OrientedEdge current.cutPolygon.patch.cut.count) (member : edge ∈ word.edges) :
    current.cutPolygon.patch.cut.vertexLabels edge.start ≠ current.cutPolygon.patch.cut.vertexLabels edge.finish := by
  rw [← word.sources.edges_eq] at member
  obtain ⟨route, _, same⟩ := Map.mem_map.mp member
  rw [← same]
  have nonloop := LiftedMesh.orientedEdges_nonloop current.mesh _ (SourceEdge.member
    (TriangleEdgeOwner.sourceEdge_positive route.owner))
  rw [TriangleEdgeOwner.sourceEdge_project route.owner] at nonloop
  rcases route with ⟨edge, owner, reversed⟩
  cases reversed
  · exact nonloop
  · exact Ne.symm nonloop

/-- The projected doubled original-cell cut word has exactly the retained two-sheet enclosing-boundary area. -/
theorem original_projected_area
    (geometry : IncludedHoleSewing bank grid.shrunk.included index domains differential)
    (primitive : Fin current.vertices.count → PrimitivePoint) :
    edgeListArea primitive (geometry.word.edges.map (OrientedEdge.map current.cutPolygon.patch.cut.vertexLabels)) =
      current.edges.twoSheetArea current.vertices primitive
        (grid.shrunk.included.resplit (CellBoundary.Cell.boundaryWalk (base.bank.cell index) (base.bank.cell_mem index))
          ((base.bank.cell index).anchor_mem (base.bank.cell_mem index))) := by
  rw [geometry.project]
  erw [HoleRequests.resplit_hole_double_indexed bank grid.shrunk.included (current := current) index,
    edgeListArea_append]
  change current.edges.twoSheetArea current.vertices primitive
    (grid.shrunk.included.resplit (bank.rows.get index).boundary _) = _
  rw [(bank.rows.get index).boundary_eq]

-- Preserve the original OriginalCutBalance.OriginalCutBalance nominal owner.

end OriginalCutBalance

set_option genInjectivity false in
/-- The complete original-cell excision balance on actual cut triangles.

The selected triangles, inner cut occurrences and doubled enclosing word retain a complete projected pairing, including
jumps and endpoint defects. -/
structure OriginalCutBalance (outer : OriginalAnnularFaces grid index)
    {annulus : Faces.AnnularFaces grid index} (region : LiftedBoundary.Lifted annulus current)
    (geometry : IncludedHoleSewing bank grid.shrunk.included index domains differential)
    (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch localValues) where
  /-- The actual sewn triangles whose source faces refine the original enclosing cell. -/ selected :
    CachedSample.FaceSelection surface (fun source => decide
    ((AllHoleExcision.sourceFace current source).cell.box.Refines (base.bank.cell index).box))
  /-- The retained inner-boundary cut occurrences on the lifted annulus. -/ inner : CutBalance.InnerOccurrences region
  /-- The cached ordered edge list for the complete original-cell balance. -/ edges : List (OrientedEdge
    current.cutPolygon.patch.cut.count)
  /-- The balance edges retain all selected triangle boundaries and both reversed boundary words. -/ edges_eq : edges =
    selected.triangles.flatMap OrientedTriangle.boundary ++
    (geometry.word.edges ++ inner.word.edges).map OrientedEdge.reverse
  /-- The complete projected pairing of the actual retained balance edges. -/ complete : ProjectedEdgePairing.Complete
    current.cutPolygon.patch.cut.vertexLabels edges

constructive_injectivity OriginalCutBalance

namespace OriginalCutBalance

/-- Select the original-cell cut triangles and construct their complete projected pairing with the retained outer and
inner cut words. -/
@[expose] def build (outer : OriginalAnnularFaces grid index) {annulus : Faces.AnnularFaces grid index}
    (region : LiftedBoundary.Lifted annulus current)
    (geometry : IncludedHoleSewing bank grid.shrunk.included index domains differential)
    (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch localValues) : OriginalCutBalance outer region
      geometry surface := by
  let keep := fun face : RegularFace grid.shrunk.prepared.toBranchCellBank => decide (face.cell.box.Refines
    (base.bank.cell index).box)
  let selected := FaceSelection.build surface (fun source => keep (AllHoleExcision.sourceFace current source))
  let inner := InnerOccurrences.build region
  let edges := selected.triangles.flatMap OrientedTriangle.boundary ++
    (geometry.word.edges ++ inner.word.edges).map OrientedEdge.reverse
  have nonloop : ∀ edge ∈ edges,
      current.cutPolygon.patch.cut.vertexLabels edge.start ≠ current.cutPolygon.patch.cut.vertexLabels edge.finish := by
    intro edge member
    rcases Data.List.Membership.mem_append.mp member with member | member
    · obtain ⟨triangle, triangleMember, edgeMember⟩ := Flatten.mem_flatMap.mp member
      rw [selected.triangles_eq] at triangleMember
      obtain ⟨trace, traceMember, same⟩ := Map.mem_map.mp triangleMember
      have projected : OrientedEdge.map current.cutPolygon.patch.cut.vertexLabels edge ∈
        (current.mesh.triangulation.faces trace.source).boundary := by
        rw [← selected.trace_projection trace traceMember, OrientedTriangle.boundary_map]
        exact Map.mem_map_of_mem (same.symm ▸ edgeMember)
      exact LiftedMesh.orientedEdges_nonloop current.mesh _ (Flatten.mem_flatMap.mpr
        ⟨_, Permutation.ofFn_mem current.mesh.triangulation.faces trace.source, projected⟩)
    · obtain ⟨original, member, same⟩ := Map.mem_map.mp member
      rw [← same]
      rcases Data.List.Membership.mem_append.mp member with member | member
      · exact Ne.symm (word_nonloop geometry.word original member)
      · exact Ne.symm (word_nonloop inner.word original member)
  have zero : ∀ primitive : Fin current.vertices.count → PrimitivePoint,
      edgeListArea primitive (edges.map (OrientedEdge.map current.cutPolygon.patch.cut.vertexLabels)) = 0 := by
    intro primitive
    rw [← WitnessReadbacks.mapped_area]
    change edgeListArea _ (selected.triangles.flatMap OrientedTriangle.boundary ++ _) = 0
    rw [edgeListArea_append, WitnessReadbacks.projected_triangles]
    erw [SewnAnnulus.selected_lifted_sum keep selected
      (fun triangle => edgeListArea primitive triangle.boundary),
      ← NewtonOriginalLiftedBoundary.allLifted_triangles outer current,
      ← Lifted.triangleEdges_sum, NewtonOriginalLiftedBoundary.triangleEdges_area outer region,
      WitnessReadbacks.reverse_area, edgeListArea_append, WitnessReadbacks.mapped_area _ primitive geometry.word.edges,
      WitnessReadbacks.mapped_area _ primitive inner.word.edges, inner.project, original_projected_area geometry]
    ring1
  exact ⟨selected, inner, edges, rfl, Complete.build _ edges nonloop zero⟩

variable {outer : OriginalAnnularFaces grid index} {annulus :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index}
  {region : Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus current}
  {geometry : IncludedHoleSewing bank grid.shrunk.included index domains differential}

/-- All actual cut corrections remain in the original-cell region balance. -/
theorem area_balance (balance : OriginalCutBalance outer region geometry surface)
    (sample : ProjectedEdgePairing.PrimitiveSample balance.complete.pairing surface.energyValues) :
    balance.selected.area = edgeListArea surface.energyValues geometry.word.edges +
      edgeListArea surface.energyValues balance.inner.word.edges + sample.jumpSum + sample.defectSum := by
  have equal := (congrArg (edgeListArea surface.energyValues) balance.edges_eq).symm.trans
    (balance.complete.area_eq_jumps_defects surface.energyValues sample)
  rw [edgeListArea_append, WitnessReadbacks.reverse_area, edgeListArea_append, ← balance.selected.area_eq] at equal
  calc
    _ = (balance.selected.area + -(edgeListArea surface.energyValues geometry.word.edges +
      edgeListArea surface.energyValues balance.inner.word.edges)) +
      (edgeListArea surface.energyValues geometry.word.edges + edgeListArea surface.energyValues
        balance.inner.word.edges) := by ring1
    _ = _ := by rw [equal]; ring1

/-- Subtracting the retained inner area, cut jumps, endpoint defects and occurrence correction gives the exact corrected
enclosing-word readback. -/
theorem corrected_area (balance : OriginalCutBalance outer region geometry surface)
    (sample : ProjectedEdgePairing.PrimitiveSample balance.complete.pairing surface.energyValues)
    (readback : CutSourceWord.AreaReadback geometry.word surface.sewn.values) :
    balance.selected.area - edgeListArea surface.energyValues balance.inner.word.edges -
      sample.jumpSum - sample.defectSum - readback.correction = readback.raw - readback.correction := by
  have raw : readback.raw = edgeListArea surface.energyValues geometry.word.edges := by
    rw [readback.raw_eq]
    have same (edges : List (OrientedEdge current.cutPolygon.patch.cut.count)) :
        edgeListArea (fun vertex => Polygon.energyPrimitivePoint (surface.sewn.values vertex)) edges =
          edgeListArea surface.energyValues edges := by
      induction edges with
      | nil => rfl
      | cons edge tail ih => rw [edgeListArea, edgeListArea, surface.energyValues_eq, surface.energyValues_eq, ih]
    exact same _
  rw [balance.area_balance sample, raw]
  ring1

/-- The full original-cell region now consumes the requested sewn-word comparison. Inner boundary, cut jumps, defects
and occurrence offsets all remain explicit; none is silently declared negligible. -/
theorem canonical_accurate {fixed : FaceMagnitudeBank domains differential} {error : Fraction.Rational} {floor : Nat}
    (request : IncludedHoleSewing.Request geometry fixed error floor)
    {stage : Nat} {shared : PrimitiveData.FacePrimitiveBank differential stage domains} (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
    (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values)
    (balance : OriginalCutBalance outer region geometry surface)
    (sample : ProjectedEdgePairing.PrimitiveSample balance.complete.pairing surface.energyValues)
    (readback : CutSourceWord.AreaReadback geometry.word surface.sewn.values)
    (later : request.index ≤ stage) :
    let walk := grid.shrunk.included.resplit (bank.rows.get index).boundary
      ((base.bank.cell index).anchor_mem (base.bank.cell_mem index))
    Data.Gaussian.Norm.Basic.normSq
      ((balance.selected.area - edgeListArea surface.energyValues balance.inner.word.edges -
        sample.jumpSum - sample.defectSum - readback.correction) -
        RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values)
          (current.edges.indexedEdges current.vertices (walk.append walk) 0)) ≤ error := by
  intro walk
  rw [balance.corrected_area sample readback]
  exact request.accurate readings surface readback later

end OriginalCutBalance

namespace OriginalCutBalance

/-- The actual original-cell cut triangles approximate twice the original based branch excursion. All requests are
computed from the existing banks; the inner boundary, jumps, endpoint defects and offsets remain explicit. -/
theorem original_branch_area_accurate
    (outer : OriginalAnnularFaces grid index) {annulus : Faces.AnnularFaces grid index}
    (region : LiftedBoundary.Lifted annulus current)
    (fixed : FaceMagnitudeBank domains differential) (sheet : Fin 2)
    (error : Fraction.Rational) (positive : 0 < error) (floor : Nat) :
    let part := error / 4
    let partPositive : 0 < part := Fraction.Order.Field.div_pos_direct positive (by decide)
    let innerPositive : 0 < part / 10 := Fraction.Order.Field.div_pos_direct partPositive (by decide)
    let stems := IncludedStemRequest.build bank grid.shrunk.included fixed index sheet (part / 10) innerPositive
    let holes := IncludedHoleRequest.build bank grid.shrunk.included fixed index (part / 10) innerPositive
    let geometry := IncludedHoleSewing.build bank grid.shrunk.included index domains differential
    let sewing := IncludedHoleSewing.Request.build geometry fixed part partPositive floor
    ∀ stage (shared : PrimitiveData.FacePrimitiveBank differential stage domains) (readings :
      TrianglePrimitiveReadings.TriangleReadings shared current.mesh)
      (surface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch readings.values),
      max (max stems.index holes.index) sewing.index ≤ stage →
      let balance := OriginalCutBalance.build outer region geometry surface
      let sample := PrimitiveSample.build balance.complete.pairing surface.energyValues
      let readback := AreaReadback.build geometry.word surface.sewn.values
      let loop := current.edges.indexedEdges current.vertices
        (grid.shrunk.included.resplit (bank.rows.get index).reference.walk (FramedBranchCellBank.baseMember base.bank))
          sheet
      Data.Gaussian.Norm.Basic.normSq
        ((balance.selected.area - edgeListArea surface.energyValues balance.inner.word.edges -
          sample.jumpSum - sample.defectSum - readback.correction) -
          (RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values) loop +
            RetracingWords.wordArea (CanonicalEdgeValues.edgeValuation current.mesh readings.values) loop)) ≤ error :=
              by
  intro part partPositive innerPositive stems holes geometry sewing stage shared readings surface later balance sample
    readback loop
  rw [balance.corrected_area sample readback]
  exact HoleSewing.included_branch_sewn_accurate bank grid.shrunk.included fixed index sheet error positive floor
    stage shared readings surface later

end OriginalCutBalance

end Purelib.Curves.Hyperelliptic.Meshes.Newton
