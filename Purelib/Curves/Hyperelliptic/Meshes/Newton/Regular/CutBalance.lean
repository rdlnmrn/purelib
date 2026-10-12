module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Integration.Energy.Polygon

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SignedSourceChartRequests
import Purelib.Data.List.Permutation
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
public import Purelib.Riemann.Branches.NewtonCutAnnulusProjection
public import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Topology.Polygon.WitnessReadbacks

public import Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Init.Core
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.Boundary.Values
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

public section

/-! Original regular-cell regions on the actual sewn cut surface. The two
closed sheet boundaries are retained separately, with all cut corrections. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences

open Purelib.Data.List

open Purelib.Integration.Energy

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann

open Purelib.Riemann.Branches.NewtonCutAnnulusProjection.BranchCellBank.NewtonGrid.AllHoleExcision

open Purelib.Riemann.Branches.NewtonCutPrimitiveArea

open Purelib.Riemann.Branches.NewtonCutPrimitiveSources

open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces

open Purelib.Riemann.Meshes

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology.NewtonSewnExcision

open Purelib.Topology.Mesh.TriangleSourceUniqueness

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation

open Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation.ProjectedEdgePairing

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle PrimitivePoint edgeListArea edgeArea
  edgeArea_reverse edgeListArea_append)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences (PairedWalk)
open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces (CutSourceWord)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces (OriginalRegularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
    {face : Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace original}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured}

namespace CutBalance

set_option genInjectivity false in
/-- The two retained closed sheet-boundary words of a regular cell.

Both words use the original paired placement of the resplit cell boundary,
retaining its source occurrences separately on sheet zero and sheet one. -/
structure BoundaryWords (face : PuncturedGridFaces.RegularFace original) (lifted : Meshes.LiftedPuncturedGrid
  grid.punctured) where
  /-- The actual paired source placement of the resplit original regular-cell boundary. -/ paired :
    WalkOccurrences.PairedWalk lifted.mesh
    (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member))
  /-- The retained sheet-zero cut source word. -/ zero : SewnPrimitiveFaces.CutSourceWord lifted.cutPolygon.patch.cut
    (paired.sources 0)
  /-- The retained sheet-one cut source word. -/ one : SewnPrimitiveFaces.CutSourceWord lifted.cutPolygon.patch.cut
    (paired.sources 1)

constructive_injectivity BoundaryWords

end CutBalance

namespace CutBalance.BoundaryWords

/-- Construct the actual paired boundary placement and its separate cut source words on both sheets. -/
@[expose] def build (face : PuncturedGridFaces.RegularFace original) (lifted : Meshes.LiftedPuncturedGrid
  grid.punctured) : Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted :=
  let paired := PairedWalk.build lifted.mesh
    (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member))
  let word (sheet : Fin 2) := CutSourceWord.build lifted.cutPolygon.patch.cut (paired.sources sheet) (by
    intro source member
    exact ⟨(Permutation.mem_iff lifted.cutPolygon.coverage _).mpr
      (Permutation.ofFn_mem (fun index => index) source.source),
      SignedSourceChartRequests.paired_sources_nonloop paired sheet source member⟩)
  ⟨paired, word 0, word 1⟩

/-- The ordered concatenation of the two retained sheet-boundary edge lists. -/
@[expose] def edges (words : Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted) : List
  (Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count) :=
  words.zero.edges ++ words.one.edges

section
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords
/-- The projected retained boundary words give exactly the two-sheet area of the original resplit regular-cell boundary.
-/
theorem projected_area (words : Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted)
  (primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint) :
    Stokes.edgeListArea (fun vertex => primitive (lifted.cutPolygon.patch.cut.vertexLabels vertex)) words.edges =
      lifted.edges.twoSheetArea lifted.vertices primitive
        (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) := by
  rw [edges, Stokes.edgeListArea_append,
    WitnessReadbacks.mapped_area _ primitive words.zero.edges, WitnessReadbacks.mapped_area _ primitive words.one.edges,
    words.zero.project, words.one.project, PairedWalk.sources_project words.paired, PairedWalk.sources_project
      words.paired]
  rfl

/-- Every retained cut source edge projects to distinct endpoints. -/
private theorem word_nonloop {sources : List (SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length)}
    (word : SewnPrimitiveFaces.CutSourceWord lifted.cutPolygon.patch.cut sources)
    (edge : Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count) (member : edge ∈ word.edges) :
    lifted.cutPolygon.patch.cut.vertexLabels edge.start ≠ lifted.cutPolygon.patch.cut.vertexLabels edge.finish := by
  rw [← word.sources.edges_eq] at member
  obtain ⟨route, _, same⟩ := Map.mem_map.mp member
  rw [← same]
  have nonloop := LiftedMesh.orientedEdges_nonloop lifted.mesh _ (SourceEdge.member
    (TriangleEdgeOwner.sourceEdge_positive route.owner))
  rw [TriangleEdgeOwner.sourceEdge_project route.owner] at nonloop
  rcases route with ⟨edge, owner, reversed⟩
  cases reversed
  · exact nonloop
  · exact Ne.symm nonloop

end

/-- Every edge in either retained boundary word has distinct projected endpoints. -/
theorem nonloop (words : Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted) (edge :
  Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count)
    (member : edge ∈ words.edges) :
    lifted.cutPolygon.patch.cut.vertexLabels edge.start ≠ lifted.cutPolygon.patch.cut.vertexLabels edge.finish := by
  rcases Membership.mem_append.mp member with first | last
  · exact Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords.word_nonloop words.zero edge first
  · exact Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords.word_nonloop words.one edge last

end CutBalance.BoundaryWords

variable {localValues : Fin lifted.mesh.triangles.length →
  Purelib.Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3}

set_option genInjectivity false in
/-- The original regular-cell region balance on the actual sewn cut surface.

A complete projected pairing retains both sheet boundaries alongside the selected cut triangles. -/
structure CutBalance (region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face) (words :
  Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted)
    (surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues) where
  /-- The actual sewn triangles whose source faces refine the original regular cell. -/ selected :
    CachedSample.FaceSelection surface (fun source => decide
    ((AllHoleExcision.sourceFace lifted source).cell.box.Refines face.cell.box))
  /-- The cached ordered edge list for the complete regular-cell region balance. -/ edges : List (Stokes.OrientedEdge
    lifted.cutPolygon.patch.cut.count)
  /-- The complete edge list retains all selected triangle boundaries and the reversed sheet-boundary words. -/ edges_eq
    : edges = selected.triangles.flatMap OrientedTriangle.boundary ++ words.edges.map OrientedEdge.reverse
  /-- The complete projected pairing on the actual balance edge list. -/ complete : ProjectedEdgePairing.Complete
    lifted.cutPolygon.patch.cut.vertexLabels edges

constructive_injectivity CutBalance

namespace CutBalance

/-- Select the retained regular-cell cut triangles and construct the complete projected pairing with both original
boundary words. -/
@[expose] def build (region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face) (words :
  Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted)
    (surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues) :
      CutBalance region words surface := by
  let keep := fun entry : PuncturedGridFaces.RegularFace grid.shrunk.prepared.toBranchCellBank => decide
    (entry.cell.box.Refines face.cell.box)
  let selected := FaceSelection.build surface (fun source => keep (AllHoleExcision.sourceFace lifted source))
  let edges := selected.triangles.flatMap OrientedTriangle.boundary ++ words.edges.map OrientedEdge.reverse
  have nonloop : ∀ edge ∈ edges,
      lifted.cutPolygon.patch.cut.vertexLabels edge.start ≠ lifted.cutPolygon.patch.cut.vertexLabels edge.finish := by
    intro edge member
    rcases Membership.mem_append.mp member with member | member
    · obtain ⟨triangle, triangleMember, edgeMember⟩ := Flatten.mem_flatMap.mp member
      rw [selected.triangles_eq] at triangleMember
      obtain ⟨trace, traceMember, same⟩ := Map.mem_map.mp triangleMember
      have projected : OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels edge ∈ (lifted.mesh.triangulation.faces
        trace.source).boundary := by
        rw [← selected.trace_projection trace traceMember, OrientedTriangle.boundary_map]
        exact Map.mem_map_of_mem (same.symm ▸ edgeMember)
      exact LiftedMesh.orientedEdges_nonloop lifted.mesh _ (Flatten.mem_flatMap.mpr
        ⟨_, Permutation.ofFn_mem lifted.mesh.triangulation.faces trace.source, projected⟩)
    · obtain ⟨original, present, same⟩ := Map.mem_map.mp member
      rw [← same]
      exact Ne.symm (words.nonloop original present)
  have zero : ∀ primitive : Fin lifted.vertices.count → Stokes.PrimitivePoint,
      Stokes.edgeListArea primitive (edges.map (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels)) = 0 := by
    intro primitive
    rw [← WitnessReadbacks.mapped_area]
    change Stokes.edgeListArea _ (selected.triangles.flatMap OrientedTriangle.boundary ++ _) = 0
    rw [Stokes.edgeListArea_append, WitnessReadbacks.reverse_area, words.projected_area]
    have projected : Stokes.edgeListArea (fun vertex => primitive (lifted.cutPolygon.patch.cut.vertexLabels vertex))
        (selected.triangles.flatMap OrientedTriangle.boundary) =
        CellBoundary.sumValues (fun triangle => Stokes.edgeListArea primitive (OrientedTriangle.map
          lifted.cutPolygon.patch.cut.vertexLabels triangle).boundary)
          selected.triangles := by
      exact WitnessReadbacks.projected_triangles _ primitive selected.triangles
    rw [projected]
    erw [SewnAnnulus.selected_lifted_sum keep selected
      (fun triangle => Stokes.edgeListArea primitive triangle.boundary), ← region.allLifted_triangles lifted,
      ← Lifted.triangleEdges_sum, region.triangleEdges_area lifted primitive]
    exact add_neg_cancel _
  exact ⟨selected, edges, rfl, Complete.build _ edges nonloop zero⟩

/-- The selected original regular-cell energy is the two boundary areas plus the actual sewn cut jumps and endpoint
defects. -/
theorem area_balance {region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face} {words :
  Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted}
    {surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues} (balance :
      CutBalance region words surface)
    (sample : ProjectedEdgePairing.PrimitiveSample balance.complete.pairing surface.energyValues) :
    balance.selected.area = Stokes.edgeListArea surface.energyValues words.zero.edges +
      Stokes.edgeListArea surface.energyValues words.one.edges + sample.jumpSum + sample.defectSum := by
  have equal := (congrArg (Stokes.edgeListArea surface.energyValues) balance.edges_eq).symm.trans
    (balance.complete.area_eq_jumps_defects surface.energyValues sample)
  rw [Stokes.edgeListArea_append, WitnessReadbacks.reverse_area,
    Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords.edges, Stokes.edgeListArea_append, ←
    balance.selected.area_eq] at equal
  calc
    _ = (balance.selected.area + -(Stokes.edgeListArea surface.energyValues words.zero.edges +
      Stokes.edgeListArea surface.energyValues words.one.edges)) +
      (Stokes.edgeListArea surface.energyValues words.zero.edges + Stokes.edgeListArea surface.energyValues
        words.one.edges) := by ring1
    _ = _ := by rw [equal]; ring1

/-- Both sheet occurrences keep their own primitive-offset corrections. Coordinate projection does not identify their
sewn primitive values. -/
theorem corrected_area {region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face} {words :
  Curves.Hyperelliptic.Meshes.Newton.Regular.CutBalance.BoundaryWords face lifted}
    {surface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch localValues} (balance :
      CutBalance region words surface)
    (sample : ProjectedEdgePairing.PrimitiveSample balance.complete.pairing surface.energyValues)
    (zero : CutSourceWord.AreaReadback words.zero surface.sewn.values)
    (one : CutSourceWord.AreaReadback words.one surface.sewn.values) :
    balance.selected.area - sample.jumpSum - sample.defectSum - zero.correction - one.correction =
      (zero.raw - zero.correction) + (one.raw - one.correction) := by
  have readback {sources : List (SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length)}
      (word : SewnPrimitiveFaces.CutSourceWord lifted.cutPolygon.patch.cut sources)
      (reading : CutSourceWord.AreaReadback word surface.sewn.values) :
      reading.raw = Stokes.edgeListArea surface.energyValues word.edges := by
    rw [reading.raw_eq]
    have same (edges : List (Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count)) :
        Stokes.edgeListArea (fun vertex => Polygon.energyPrimitivePoint (surface.sewn.values vertex)) edges =
          Stokes.edgeListArea surface.energyValues edges := by
      induction edges with
      | nil => rfl
      | cons edge tail ih =>
        rw [Stokes.edgeListArea, Stokes.edgeListArea, surface.energyValues_eq, surface.energyValues_eq, ih]
    exact same _
  rw [balance.area_balance sample, readback words.zero zero, readback words.one one]
  ring1

end CutBalance
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular
