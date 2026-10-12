module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Data.List.Permutation
public import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Polygon.WitnessReadbacks

public import Purelib.Riemann.Branches.NewtonCutAnnulusProjection
import Purelib.Riemann.Branches.NewtonCutAreaRequests
public import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RetainedDetourRoutes
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

public section

/-!
# Newton annular excision with actual cut jumps and offsets

The selected cut triangles, the original two-lap hole boundary and the
prepared outer Newton tour form one projected zero chain. A complete finite
pairing retains its actual cut jumps and defects. Combining it with the
Newton request bounds the annular area after exactly these displayed terms
are subtracted; no projected closure is used to erase a cut contribution.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Riemann

open Purelib
open Purelib.Data.List

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {lifted :
    Meshes.LiftedPuncturedGrid grid.punctured}

namespace CutBalance

/-- The original routed triangle edge has distinct source corners. -/
private theorem route_distinct {edge : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count} (route :
  Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute lifted.mesh edge) :
    route.sourceEdge.first ≠ route.sourceEdge.last := by
  cases route with
  | forward location =>
      change Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.firstCorner location.kind ≠
        Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.lastCorner location.kind
      cases location.kind <;> decide
  | backward location =>
      change Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.lastCorner location.kind ≠
        Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners.firstCorner location.kind
      cases location.kind <;> decide

/-- Each source occurrence in the retained route spine has distinct corners.

Structural recursion retains the selected source occurrence. Each forward or
backward triangle route has distinct finite corner indices. -/
theorem sources_distinct : ∀ {word : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)} (routes :
  Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine lifted.mesh word),
    ∀ source ∈ routes.values (fun _ route => route.sourceEdge), source.first ≠ source.last
  | _, .nil, _, member => (List.not_mem_nil member).elim
  | _, .cons route tail, source, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · exact Hyperelliptic.Meshes.Newton.Annulus.CutBalance.route_distinct route
      · exact Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance.sources_distinct tail source member

set_option genInjectivity false in
/-- Retained inner-boundary routes, source occurrences and cut source word.

The sources reproduce the route spine in order, and the cut word retains
these same source occurrences on the original lifted hole boundary. -/
structure InnerOccurrences {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
  Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index}
    (region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) where
  /-- The actual original inner-boundary route spine. -/ routes :
    Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine lifted.mesh region.inner
  /-- The cached original source occurrences. -/ sources : List
    (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length)
  /-- The sources are exactly the original route-spine readback. -/ sources_eq : sources = routes.values (fun _ route =>
    route.sourceEdge)
  /-- The cut word on these exact retained sources. -/ word :
    Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces.CutSourceWord lifted.cutPolygon.patch.cut sources

constructive_injectivity InnerOccurrences

end CutBalance

namespace CutBalance.InnerOccurrences

variable {index : Hyperelliptic.Branches.BranchIsolation.Data.Index branches} {annulus :
  Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index} {region :
  Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}

/-- Reuse the actual lifted inner-boundary routes to retain their exact source list and cut word. -/
@[expose] def build (region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted) :
  Hyperelliptic.Meshes.Newton.Annulus.CutBalance.InnerOccurrences region :=
  let routes := Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.RouteSpine.build lifted.mesh region.inner (by
    rw [region.inner_eq]
    exact Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedWalk_supported lifted.mesh
      region.hole.doubleBoundary 0)
  let sources := routes.values (fun _ route => route.sourceEdge)
  let word := Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces.CutSourceWord.build lifted.cutPolygon.patch.cut
    sources (by
    intro source member
    exact ⟨(Permutation.mem_iff lifted.cutPolygon.coverage _).mpr
      (Data.List.Permutation.ofFn_mem (fun index => index) source.source),
        Hyperelliptic.Meshes.Newton.Annulus.CutBalance.sources_distinct routes source member⟩)
  ⟨routes, sources, rfl, word⟩

/-- The retained inner cut word projects to the exact original inner boundary. -/
theorem project (inner : Hyperelliptic.Meshes.Newton.Annulus.CutBalance.InnerOccurrences region) :
    inner.word.edges.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
      lifted.cutPolygon.patch.cut.vertexLabels) = region.inner :=
  inner.word.project.trans ((congrArg (List.map (fun source => source.project lifted.mesh.triangulation.faces))
    inner.sources_eq).trans
      (Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.sources_project inner.routes))

end CutBalance.InnerOccurrences

section AllHoleExcision.SewnAnnulus

variable {localValues : Fin lifted.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}
  {surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues}

namespace CutBalance.AllHoleExcision.SewnAnnulus

/-- Every selected triangle edge has distinct projected endpoints.

The retained triangle trace identifies its original source triangle, whose
checked boundary edges remain nonloops under the cut vertex projection. -/
theorem selected_nonloop (annulus : Topology.NewtonSewnExcision.AllHoleExcision.SewnAnnulus surface)
    (edge : Topology.Polygon.Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count)
    (member : edge ∈ annulus.selected.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary) :
    lifted.cutPolygon.patch.cut.vertexLabels edge.start ≠ lifted.cutPolygon.patch.cut.vertexLabels edge.finish := by
  obtain ⟨triangle, triangleMember, edgeMember⟩ := Data.List.Flatten.mem_flatMap.mp member
  rw [annulus.selected.triangles_eq] at triangleMember
  obtain ⟨trace, traceMember, same⟩ := Data.List.Map.mem_map.mp triangleMember
  have projected : Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels edge ∈
    (lifted.mesh.triangulation.faces trace.source).boundary := by
    rw [← annulus.selected.trace_projection trace traceMember,
      Topology.Surface.Sewing.VertexSewing.OrientedTriangle.boundary_map]
    exact Data.List.Map.mem_map_of_mem (same.symm ▸ edgeMember)
  exact Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
    lifted.mesh _ (Data.List.Flatten.mem_flatMap.mpr
    ⟨_, Data.List.Permutation.ofFn_mem lifted.mesh.triangulation.faces trace.source, projected⟩)

/-- Every edge of the retained source word has distinct projected endpoints.

The source owner certifies membership in the original triangle boundary;
reversing the retained route exchanges its two distinct endpoints. -/
theorem source_word_nonloop {sources : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge
  lifted.mesh.triangles.length)}
    (word : Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces.CutSourceWord lifted.cutPolygon.patch.cut sources)
    (edge : Topology.Polygon.Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count) (member : edge ∈ word.edges) :
    lifted.cutPolygon.patch.cut.vertexLabels edge.start ≠ lifted.cutPolygon.patch.cut.vertexLabels edge.finish := by
  rw [← word.sources.edges_eq] at member
  obtain ⟨route, _, same⟩ := Data.List.Map.mem_map.mp member
  rw [← same]
  have positive := Topology.Mesh.TriangleSourceUniqueness.TriangleEdgeOwner.sourceEdge_positive route.owner
  have nonloop :=
    Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
    lifted.mesh _ (Topology.Mesh.TriangleSourceUniqueness.SourceEdge.member positive)
  rw [Topology.Surface.Sewing.SewnPrimitiveContacts.TriangleEdgeOwner.sourceEdge_project route.owner] at nonloop
  rcases route with ⟨edge, owner, reversed⟩
  cases reversed
  · exact nonloop
  · exact Ne.symm nonloop

end CutBalance.AllHoleExcision.SewnAnnulus

set_option genInjectivity false in
/-- All three geometric contributions are retained with a complete pairing
of their projected cancellation. The outer word is the caller's already
prepared Newton word, not a fresh source lookup. -/
structure CutBalance (annulus : Topology.NewtonSewnExcision.AllHoleExcision.SewnAnnulus surface) (prepared :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation annulus.source.region)
    (outer : Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces.CutSourceWord lifted.cutPolygon.patch.cut
      prepared.sources) where
  /-- The actual retained inner-boundary occurrences. -/ inner :
    Hyperelliptic.Meshes.Newton.Annulus.CutBalance.InnerOccurrences annulus.source.region
  /-- The exact selected-triangle and reversed boundary edge list. -/ edges : List (Topology.Polygon.Stokes.OrientedEdge
    lifted.cutPolygon.patch.cut.count)
  /-- The list is literally the selected triangle boundaries followed by the reversed outer and inner words. -/ edges_eq
    : edges = annulus.selected.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary ++
    (outer.edges ++ inner.word.edges).map Topology.Polygon.Stokes.OrientedEdge.reverse
  /-- The complete pairing of the original projected edge cancellation. -/ complete :
    Topology.Surface.Boundary.ProjectedAreaCancellation.ProjectedEdgePairing.Complete
    lifted.cutPolygon.patch.cut.vertexLabels edges

constructive_injectivity CutBalance

namespace CutBalance

variable {annulus : Topology.NewtonSewnExcision.AllHoleExcision.SewnAnnulus surface} {prepared :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation annulus.source.region}
  {outer : Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces.CutSourceWord lifted.cutPolygon.patch.cut
    prepared.sources}

/-- Retain the original inner and prepared outer words, then build the complete projected cancellation pairing for their
exact selected-triangle difference. -/
@[expose] def build (annulus : Topology.NewtonSewnExcision.AllHoleExcision.SewnAnnulus surface) (prepared :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation annulus.source.region)
    (outer : Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces.CutSourceWord lifted.cutPolygon.patch.cut
      prepared.sources) : CutBalance annulus
      prepared outer := by
  let inner := Hyperelliptic.Meshes.Newton.Annulus.CutBalance.InnerOccurrences.build annulus.source.region
  let edges := annulus.selected.triangles.flatMap Topology.Polygon.Stokes.OrientedTriangle.boundary ++
    (outer.edges ++ inner.word.edges).map Topology.Polygon.Stokes.OrientedEdge.reverse
  have nonloop : ∀ edge ∈ edges,
      lifted.cutPolygon.patch.cut.vertexLabels edge.start ≠ lifted.cutPolygon.patch.cut.vertexLabels edge.finish := by
    intro edge member
    rcases Membership.mem_append.mp member with member | member
    · exact Hyperelliptic.Meshes.Newton.Annulus.CutBalance.AllHoleExcision.SewnAnnulus.selected_nonloop annulus edge
        member
    · obtain ⟨original, member, same⟩ := Data.List.Map.mem_map.mp member
      rw [← same]
      rcases Membership.mem_append.mp member with member | member
      · exact Ne.symm (Hyperelliptic.Meshes.Newton.Annulus.CutBalance.AllHoleExcision.SewnAnnulus.source_word_nonloop
          outer original member)
      · exact Ne.symm (Hyperelliptic.Meshes.Newton.Annulus.CutBalance.AllHoleExcision.SewnAnnulus.source_word_nonloop
          inner.word original member)
  have zero : ∀ primitive : Fin lifted.vertices.count → Topology.Polygon.Stokes.PrimitivePoint,
      Topology.Polygon.Stokes.edgeListArea primitive (edges.map (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
        lifted.cutPolygon.patch.cut.vertexLabels)) = 0 := by
    intro primitive
    rw [← Topology.Polygon.WitnessReadbacks.mapped_area]
    change Topology.Polygon.Stokes.edgeListArea _ (annulus.selected.triangles.flatMap
      Topology.Polygon.Stokes.OrientedTriangle.boundary ++ _) = 0
    rw [Topology.Polygon.Stokes.edgeListArea_append, Topology.Polygon.WitnessReadbacks.projected_triangles,
      Branches.NewtonCutAnnulusProjection.BranchCellBank.NewtonGrid.AllHoleExcision.SewnAnnulus.projected_sum annulus
        (fun triangle => Topology.Polygon.Stokes.edgeListArea primitive triangle.boundary),
      ← Topology.Polygon.WitnessReadbacks.triangles_area, annulus.source.region.triangleEdges_area,
        Topology.Polygon.WitnessReadbacks.reverse_area,
      Topology.Polygon.Stokes.edgeListArea_append,
      Topology.Polygon.WitnessReadbacks.mapped_area lifted.cutPolygon.patch.cut.vertexLabels primitive outer.edges,
      Topology.Polygon.WitnessReadbacks.mapped_area lifted.cutPolygon.patch.cut.vertexLabels primitive inner.word.edges,
        inner.project,
      outer.project, prepared.sources_project]
    ring1
  exact ⟨inner, edges, rfl, Topology.Surface.Boundary.ProjectedAreaCancellation.ProjectedEdgePairing.Complete.build _
    edges nonloop zero⟩

/-- Excision's actual selected area equals the two retained cut-boundary
areas plus every crossing jump and endpoint defect. -/
theorem area_balance (balance : CutBalance
  annulus prepared outer)
    (sample : Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing.PrimitiveSample balance.complete.pairing
      surface.energyValues) :
    annulus.selected.area = Topology.Polygon.Stokes.edgeListArea surface.energyValues outer.edges +
      Topology.Polygon.Stokes.edgeListArea surface.energyValues balance.inner.word.edges + sample.jumpSum +
        sample.defectSum := by
  have equal := (congrArg (Topology.Polygon.Stokes.edgeListArea surface.energyValues) balance.edges_eq).symm.trans
    (balance.complete.area_eq_jumps_defects surface.energyValues sample)
  rw [Topology.Polygon.Stokes.edgeListArea_append, Topology.Polygon.WitnessReadbacks.reverse_area,
    Topology.Polygon.Stokes.edgeListArea_append, ← annulus.selected.area_eq] at equal
  calc
    _ = (annulus.selected.area + -(Topology.Polygon.Stokes.edgeListArea surface.energyValues outer.edges +
      Topology.Polygon.Stokes.edgeListArea surface.energyValues balance.inner.word.edges)) +
      (Topology.Polygon.Stokes.edgeListArea surface.energyValues outer.edges + Topology.Polygon.Stokes.edgeListArea
        surface.energyValues balance.inner.word.edges) := by ring1
    _ = _ := by rw [equal]; ring1

end CutBalance
end AllHoleExcision.SewnAnnulus
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
