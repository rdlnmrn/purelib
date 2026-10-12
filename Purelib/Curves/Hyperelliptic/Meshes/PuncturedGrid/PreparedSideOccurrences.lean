module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison
public import Purelib.Polynomial.Geometry.Grid.Boundary.Segments
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

/-! One certified side occurrence for every original prepared grid segment.
The conversion preserves the literal source list, including repetitions,
reversals and both sheet laps; it does not locate or prepare another tour. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences
public section
open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh
open Purelib.Geometry
open Purelib.Polynomial.Geometry
open Purelib.Polynomial.Geometry.Grid.Boundary.Segments
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedPathDecomposition
open Purelib.Riemann.Topology
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Geometry.Rational (Box)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open Purelib.Polynomial.Geometry.Grid.Boundary.Segments.PreparedBoundarySegments (OnBoundary)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh (SideOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh.SegmentFace (sideOccurrence)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments (sourceEdges
  sourceEdges_project)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces} {ambient :
    Box}

namespace SideOccurrence

/-- The actual projected source edge has both endpoints in the box and on one common boundary side.

The point lies on one of the four retained coordinate sides of the same rectangle, including the endpoints of each side.
-/
@[expose]
def OnBoundary (occurrence : LiftedMesh.SideOccurrence mesh) (box : Rational.Box) : Prop :=
  let edge := occurrence.source.project mesh.triangulation.faces
  box.Contains (vertices.coordinate edge.start) ∧ box.Contains (vertices.coordinate edge.finish) ∧
    PreparedBoundarySegments.SameSide box (vertices.coordinate edge.start) (vertices.coordinate edge.finish)

end SideOccurrence

namespace AssignedSegments

/-- Retain one certified side occurrence per original prepared segment, preserving its list order and multiplicity.

The resulting list traverses the retained assigned side segments in order, carrying their source witnesses and
rectangle-boundary identities. -/
@[expose]
def sideOccurrences : ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial
  ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared},
    PreparedFaceSegments.AssignedSegments mesh pieces → List (LiftedMesh.SideOccurrence mesh)
  | _, _, _, _, _, _, .nil _ _ => []
  | _, _, _, _, _, _, .cons placement remaining =>
      (SegmentFace.sideOccurrence placement).val ::
        sideOccurrences
        remaining

/-- The retained side occurrences have exactly the original assigned source-edge list. -/
theorem sideOccurrences_sources : ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
    (assigned : PreparedFaceSegments.AssignedSegments mesh pieces),
      (sideOccurrences assigned).map
      SideOccurrence.source = AssignedSegments.sourceEdges assigned
  | _, _, _, _, _, _, .nil _ _ => rfl
  | _, _, _, _, _, _, .cons placement remaining =>
      congrArg₂ List.cons
        (SegmentFace.sideOccurrence placement).property

          (sideOccurrences_sources
          remaining)

/-- The retained side occurrences project to the original indexed prepared-segment list.

The two maps apply to the same retained entries in their original order; their composite changes neither the cached list
nor its input owners. -/
theorem sideOccurrences_project {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
    (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) :
    (sideOccurrences assigned).map
      (fun occurrence => occurrence.source.project mesh.triangulation.faces) = assigned.indexed := by
  calc
    _ = ((sideOccurrences
      assigned).map SideOccurrence.source).map
        (fun source => source.project mesh.triangulation.faces) := (Map.map_map ..).symm
    _ = _ := (congrArg (List.map (fun source => source.project mesh.triangulation.faces))
      (sideOccurrences_sources
        assigned)).trans (AssignedSegments.sourceEdges_project assigned)

/-- There is exactly one retained side occurrence per original indexed prepared segment.

Mapping the retained list preserves its exact length and order; the equality transports only the list readback. -/
theorem sideOccurrences_count {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
  curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
    (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) :
      (sideOccurrences
      assigned).length = assigned.indexed.length := by
  have count := congrArg List.length
    (sideOccurrences_project
    assigned)
  rw [Map.length_map] at count
  exact count

/-- Containment and common-side data are transported from the actual path spine to its retained source edges. No
containment-to-boundary inference.

The proof follows membership in the retained list through its original head, tail or concatenation, preserving the
supplied occurrence witness. -/
theorem sideOccurrences_onBoundary {box : Rational.Box} :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces), PreparedBoundarySegments.OnBoundary box path →
      ∀ occurrence ∈ sideOccurrences
        assigned, Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences.SideOccurrence.OnBoundary
        occurrence box
  | _, _, _, _, _, _, .nil _ _, _, _, member => (List.not_mem_nil member).elim
  | _, _, _, _, _, _, .cons placement remaining, bounded, occurrence, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · unfold Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences.SideOccurrence.OnBoundary
        rw [(SegmentFace.sideOccurrence placement).property,
          placement.location.sourceEdge_project]
        dsimp only
        rw [placement.start_eq, placement.finish_eq]
        exact ⟨bounded.1, bounded.2.1, bounded.2.2.1⟩
      · exact
          sideOccurrences_onBoundary
          remaining bounded.2.2.2 occurrence member

end AssignedSegments
end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedSideOccurrences
