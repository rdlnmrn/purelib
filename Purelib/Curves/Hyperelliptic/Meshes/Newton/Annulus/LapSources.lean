module
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.List.Prefix.Take
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes

public section

/-! Split the cached outer source occurrences at the actual one-lap length.
The projected halves are the two canonical sheet polygons of the Newton band. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LapSources

open Purelib.Curves
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {index :
    Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index} {lifted : Meshes.LiftedPuncturedGrid
    grid.punctured}
  {region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}

/-- Take the original cached source prefix of one actual annular boundary length. -/
@[expose] def firstLap (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region) := prepared.sources.take annulus.boundary.edgeCount

/-- Drop exactly one annular boundary length from the original cached sources. -/
@[expose] def secondLap (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region) := prepared.sources.drop annulus.boundary.edgeCount

/-- The original two-lap outer word is the concatenation of the canonical sheet-zero and sheet-one boundaries. -/
private theorem outer_split : region.outer =
    lifted.edges.indexedEdges lifted.vertices annulus.boundary 0 ++
      lifted.edges.indexedEdges lifted.vertices annulus.boundary 1 := by
  have split := region.outer_eq.trans
    (lifted.edges.indexedEdges_append lifted.vertices annulus.boundary annulus.boundary 0)
  exact split.trans (congrArg (fun tail =>
    lifted.edges.indexedEdges lifted.vertices annulus.boundary 0 ++ tail)
      (congrArg (lifted.edges.indexedEdges lifted.vertices annulus.boundary)
        (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.boundary_swap annulus lifted.edges 0)))

/-- The retained first-lap sources project to the original sheet-zero boundary. -/
theorem firstLap_project (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region) :
    (Hyperelliptic.Meshes.Newton.Annulus.LapSources.firstLap prepared).map (fun source => source.project
      lifted.mesh.triangulation.faces) =
      lifted.edges.indexedEdges lifted.vertices annulus.boundary 0 := by
  change (prepared.sources.take annulus.boundary.edgeCount).map _ = _
  rw [Data.List.Map.map_take, prepared.sources_project, Hyperelliptic.Meshes.Newton.Annulus.LapSources.outer_split]
  exact List.take_left' (lifted.edges.indexedEdges_length lifted.vertices annulus.boundary 0)

/-- The retained second-lap sources project to the original sheet-one boundary. -/
theorem secondLap_project (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region) :
    (Hyperelliptic.Meshes.Newton.Annulus.LapSources.secondLap prepared).map (fun source => source.project
      lifted.mesh.triangulation.faces) =
      lifted.edges.indexedEdges lifted.vertices annulus.boundary 1 := by
  change (prepared.sources.drop annulus.boundary.edgeCount).map _ = _
  rw [Data.List.Map.map_drop, prepared.sources_project, Hyperelliptic.Meshes.Newton.Annulus.LapSources.outer_split]
  exact List.drop_left' (lifted.edges.indexedEdges_length lifted.vertices annulus.boundary 0)

/-- Every retained first-lap occurrence belongs to the original source list. -/
theorem firstLap_member (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region)
    {source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length}
    (member : source ∈ Hyperelliptic.Meshes.Newton.Annulus.LapSources.firstLap prepared) : source ∈ prepared.sources :=
      List.mem_of_mem_take member

/-- Every retained second-lap occurrence belongs to the original source list. -/
theorem secondLap_member (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region)
    {source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length}
    (member : source ∈ Hyperelliptic.Meshes.Newton.Annulus.LapSources.secondLap prepared) : source ∈ prepared.sources :=
      Data.List.Membership.mem_of_mem_drop member

/-- The retained first lap has at most the original outer boundary length. -/
theorem firstLap_length_le (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region) :
    (Hyperelliptic.Meshes.Newton.Annulus.LapSources.firstLap prepared).length ≤ region.outer.length := by
  have count := congrArg List.length prepared.sources_project
  rw [Data.List.Map.length_map] at count
  change (prepared.sources.take _).length ≤ _
  rw [Data.List.Prefix.Take.length_take]
  have bounded : min annulus.boundary.edgeCount prepared.sources.length ≤ prepared.sources.length := by
    change (if annulus.boundary.edgeCount ≤ prepared.sources.length then annulus.boundary.edgeCount else
      prepared.sources.length) ≤ prepared.sources.length
    by_cases ordered : annulus.boundary.edgeCount ≤ prepared.sources.length
    · rewrite [if_pos ordered]
      exact ordered
    · rewrite [if_neg ordered]
      exact Nat.le_refl _
  exact bounded.trans_eq count

/-- The retained second lap has at most the original outer boundary length. -/
theorem secondLap_length_le (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region) :
    (Hyperelliptic.Meshes.Newton.Annulus.LapSources.secondLap prepared).length ≤ region.outer.length := by
  have count := congrArg List.length prepared.sources_project
  rw [Data.List.Map.length_map] at count
  change (prepared.sources.drop _).length ≤ _
  rw [List.length_drop]
  exact (Nat.sub_le _ _).trans_eq count

/-- Every cached original outer source has distinct triangle corners. -/
theorem sources_nonloop (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region)
    (source : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge lifted.mesh.triangles.length)
    (member : source ∈ prepared.sources) : source.first ≠ source.last := by
  have projected : source.project lifted.mesh.triangulation.faces ∈ region.outer :=
    prepared.sources_project ▸ Data.List.Map.mem_map_of_mem member
  rw [region.outer_eq] at projected
  have supported := Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedWalk_supported lifted.mesh
    (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.doubleBoundary annulus) 0 _ projected
  have nonloop : (source.project lifted.mesh.triangulation.faces).start ≠
      (source.project lifted.mesh.triangulation.faces).finish :=
    supported.elim
      (Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
      lifted.mesh _)
      (fun member same =>
        Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
        lifted.mesh _ member same.symm)
  intro equal
  exact nonloop (congrArg (Topology.Surface.Sewing.SewnPrimitiveFaces.corner (lifted.mesh.triangulation.faces
    source.source)) equal)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LapSources
