module
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedOwnerAlignment
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedFaces

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Topology

open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

open Purelib.Topology.Polygon

@[expose] public section

/-!
# Local analytic entries from retained lifted-face occurrences

The shared grid transports reach all four corners on the selected face
sheet. An actual segment's proved owner alignment then supplies its local
entry directly. The executable result reads the retained sheet index only:
no return preparation, root classification, or proof trace is evaluated.
-/

section

open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached

/-- Equal physical points and an operational comparison of the original owners give a local reachability witness. -/
theorem ofEquivalentAt
  {polynomial : ClearPath.GaussianPolynomial} {box : Rational.Box} {start finish :
  Data.Gaussian.Basic.Canonical}
    {first : SquareRootContinuationChain.Owner (polynomial.eval start)} {last : SquareRootContinuationChain.Owner
      (polynomial.eval finish)}
    (equal : start = finish)
    (equivalent : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName first)
      (OwnerTraceReadings.ownerName last)) :
    PreparedFaceTracePrefixes.Reached box first last := by
  cases equal
  exact Reached.ofEquivalent equivalent

end Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached

end

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Geometry.Rectangle.Partition.RectangularEdgeUniqueness.RectangleEdge (Kind)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh LiftedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces (EdgeLocation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks (EdgeRoute)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    RootEdgeBank frames}
  {face : RegularFace bank} {sheet : Fin 2}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries.BranchCellBank

/-- The actual retained grid-edge root transport reaches its terminal owner inside the original clear face. -/
private theorem edge_reached (edge : Walks.Edge bank.grid start finish) (sheet : Fin 2)
    (first : face.cell.box.Contains start) (last : face.cell.box.Contains finish) :
    PreparedFaceTracePrefixes.Reached face.cell.box ((frames.frameAt start edge.vertices.1).owners sheet)
      ((frames.frameAt finish edge.vertices.2).owners ((edges.edge edge).forward.target sheet)) :=
  ⟨(edges.edge edge).trace sheet, ((edges.edge edge).trace_winding sheet).trans
    (ClearBoxPaths.segment_winding face.clearance (BranchIsolation.degreePositive curve) edge.segment first last)⟩

/-- Transport local reachability to the original vertex-bank owner using its exact coordinate and root-name identities.
-/
private theorem vertex_reached {base point : Data.Gaussian.Basic.Canonical} {source : SquareRootContinuationChain.Owner
  (curve.polynomial.eval base)}
    (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid point) (sheet : Fin 2) (index : Fin
      vertices.count)
    (reached : PreparedFaceTracePrefixes.Reached face.cell.box source ((frames.frameAt point member).owners sheet))
    (coordinate : vertices.coordinate index = point)
    (names : OwnerTraceReadings.ownerName (vertices.owner frames index) = OwnerTraceReadings.ownerName ((frames.frameAt
      point member).owners sheet)) :
    PreparedFaceTracePrefixes.Reached face.cell.box source (vertices.owner frames index) :=
  reached.append (Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached.ofEquivalentAt
    coordinate.symm (by rw [names]; exact NamedEquivalent.refl _))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries.BranchCellBank

namespace Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

/-- The actual continued corner owners, not just numerical sheet labels, are reached from the retained analytic face
frame. -/
theorem corners_reached (lifted :
  BranchCellBank.LiftedFace vertices edges face sheet) (models : BranchCellBank.FaceModels frames face) :
    PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet) (vertices.owner frames
      lifted.quad.first) ∧
      PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet) (vertices.owner frames
        lifted.quad.second) ∧
      PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet) (vertices.owner frames
        lifted.quad.third) ∧
      PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet) (vertices.owner frames
        lifted.quad.fourth) := by
  have first : PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet)
      ((frames.frameAt face.cell.box.anchor (face.cell.anchor_mem face.member)).owners sheet) := by
    rw [models.frame_eq]
    exact Reached.refl _
  have second : PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet)
      ((frames.frameAt _ (face.cell.bottomSide face.member).vertices.2).owners lifted.lowerRight) := by
    rw [lifted.bottom_eq]
    exact first.append (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries.BranchCellBank.edge_reached
      (face.cell.bottomSide face.member) sheet face.cell.box.contains_anchor
      ⟨face.cell.box.x_valid, le_rfl, le_rfl, face.cell.box.y_valid⟩)
  have third : PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet)
      ((frames.frameAt _ (face.cell.rightSide face.member).vertices.2).owners lifted.upperRight) := by
    rw [lifted.right_eq]
    exact second.append (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries.BranchCellBank.edge_reached
      (face.cell.rightSide face.member) lifted.lowerRight
      ⟨face.cell.box.x_valid, le_rfl, le_rfl, face.cell.box.y_valid⟩
      ⟨face.cell.box.x_valid, le_rfl, face.cell.box.y_valid, le_rfl⟩)
  have fourth : PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet)
      ((frames.frameAt _ (face.cell.topSide face.member).vertices.2).owners lifted.upperLeft) := by
    rw [lifted.top_eq]
    exact third.append (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries.BranchCellBank.edge_reached
      (face.cell.topSide face.member) lifted.upperRight
      ⟨face.cell.box.x_valid, le_rfl, face.cell.box.y_valid, le_rfl⟩
      ⟨le_rfl, face.cell.box.x_valid, face.cell.box.y_valid, le_rfl⟩)
  refine ⟨Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries.BranchCellBank.vertex_reached _ _ _ first
    lifted.coordinates.1 ?_,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries.BranchCellBank.vertex_reached _ _ _ second
      lifted.coordinates.2.1 ?_,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries.BranchCellBank.vertex_reached _ _ _ third
      lifted.coordinates.2.2.1 ?_,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries.BranchCellBank.vertex_reached _ _ _ fourth
      lifted.coordinates.2.2.2 ?_⟩
  · rw [lifted.first_eq, VertexBank.ownerName_index]
  · rw [lifted.second_eq, VertexBank.ownerName_index]
  · rw [lifted.third_eq, VertexBank.ownerName_index]
  · rw [lifted.fourth_eq, VertexBank.ownerName_index]

/-- Both actual owners of an original lifted face edge are reachable from its retained analytic face frame. -/
theorem edge_endpoints_reached (lifted :
  BranchCellBank.LiftedFace vertices edges face sheet)
    (models : BranchCellBank.FaceModels frames face) (kind : RectangleEdge.Kind) :
    PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet) (vertices.owner frames (lifted.quad.edge
      kind).start) ∧
      PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet) (vertices.owner frames
        (lifted.quad.edge kind).finish) := by
  obtain ⟨first, second, third, fourth⟩ := lifted.corners_reached models
  cases kind with
  | bottom => exact ⟨first, second⟩
  | right => exact ⟨second, third⟩
  | top => exact ⟨third, fourth⟩
  | left => exact ⟨fourth, first⟩
  | upDiagonal => exact ⟨first, third⟩
  | downDiagonal => exact ⟨third, first⟩

end Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

/-- The retained oriented edge location or route reaches both original endpoint owners from its actual selected face
frame. -/
theorem endpoints_reached {faces : List
  (PuncturedGridFaces.RegularFace bank)}
    {lifts : GridLiftedMesh.LiftedFaces vertices edges faces} {edge : Stokes.OrientedEdge vertices.count}
    (location : LiftedFaces.EdgeLocation lifts edge) (models : BranchCellBank.FaceModels frames location.face) :
    PreparedFaceTracePrefixes.Reached location.face.cell.box (models.frame.owners location.sheet) (vertices.owner frames
      edge.start) ∧
      PreparedFaceTracePrefixes.Reached location.face.cell.box (models.frame.owners location.sheet) (vertices.owner
        frames edge.finish) :=
  (congrArg (fun edge : Stokes.OrientedEdge vertices.count =>
    PreparedFaceTracePrefixes.Reached location.face.cell.box (models.frame.owners location.sheet) (vertices.owner frames
      edge.start) ∧
      PreparedFaceTracePrefixes.Reached location.face.cell.box (models.frame.owners location.sheet) (vertices.owner
        frames edge.finish)) location.edge_eq).mp
    (location.lifted.edge_endpoints_reached models location.kind)

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedFaces.EdgeLocation

section

variable {faces : PuncturedFaces bank} {mesh :
  LiftedMesh vertices edges faces}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute

/-- The retained oriented edge location or route reaches both original endpoint owners from its actual selected face
frame. -/
theorem endpoints_reached {edge :
  Stokes.OrientedEdge vertices.count}
    (route : MeshPathWalks.EdgeRoute mesh edge) (models : BranchCellBank.FaceModels frames route.face) :
    PreparedFaceTracePrefixes.Reached route.face.cell.box (models.frame.owners route.sheet) (vertices.owner frames
      edge.start) ∧
      PreparedFaceTracePrefixes.Reached route.face.cell.box (models.frame.owners route.sheet) (vertices.owner frames
        edge.finish) := by
  cases route with
  | forward location => exact location.endpoints_reached models
  | backward location => exact ⟨(location.endpoints_reached models).2, (location.endpoints_reached models).1⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace

/-- Reuse the selected lifted occurrence. Agreement with the incoming owner is erased proof data supplied automatically
by the retained path bank. -/
def entry {ambient : Rational.Box}
  {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient start finish} {owner : SquareRootContinuationChain.Owner
      (curve.polynomial.eval start)}
    (placement : LiftedMesh.SegmentFace mesh segment) (models : BranchCellBank.FaceModels frames placement.face)
    (aligned : Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName owner)
      (OwnerTraceReadings.ownerName (vertices.owner frames placement.indexed.start)))) :
    FaceModels.Entry models start owner :=
  ⟨placement.location.sheet, by
    obtain ⟨equivalent⟩ := aligned
    exact (placement.location.endpoints_reached models).1.append
      (Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes.Reached.ofEquivalentAt
        placement.start_eq
      equivalent.symm)⟩

/-- The analytic entry reads exactly the sheet of the original retained segment face placement. -/
theorem entry_sheet {ambient :
  Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    {segment : ClearPath.ClearSegment curve.polynomial ambient start finish} {owner : SquareRootContinuationChain.Owner
      (curve.polynomial.eval start)}
    (placement : LiftedMesh.SegmentFace mesh segment) (models : BranchCellBank.FaceModels frames placement.face)
    (aligned : Nonempty (Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName owner)
      (OwnerTraceReadings.ownerName (vertices.owner frames placement.indexed.start)))) :
    (placement.entry models aligned).sheet = placement.location.sheet := rfl

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh.SegmentFace

end
end
