module
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Segment
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Riemann.Paths.PreparedPathClosure
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Geometry

open Purelib.Polynomial.Dense.Gaussian.Path

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Winding

open Purelib.Riemann.Paths.OwnerLoopMonodromy

open Purelib.Riemann.Paths.PreparedPathClosure

open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels

open Purelib.Riemann.RootContinuation.RootPathTransport

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

@[expose] public section

/-!
# The retained preparation follows the shared grid-root transport

Compare the actual accepted segment with the stored reverse frame transport.
Their zero-winding loop identifies the terminal owner. All comparison traces
and operational witnesses remain inside propositions, so consuming the face
assignments cannot trigger a second executable continuation pass.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Polynomial.Geometry.Grid.Walks (Edge)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootFrames bank.grid} {start finish :
    Purelib.Data.Gaussian.Basic.Canonical} {owner : Owner (curve.polynomial.eval start)}

/-- Operational alignment is proved for the original cached terminal owner, not merely for a separately prepared path or
a displayed sheet number. -/
theorem coveredSegment_finish_aligned (edges :
  RootEdgeBank frames) (edge : Walks.Edge bank.grid start finish)
    (piece : CoveredSegment edge.segment owner) (sheet : Fin 2)
    (initial : Nonempty (Gaussian.Equivalence.NamedEquivalent (ownerName owner)
      (ownerName ((frames.frameAt start edge.vertices.1).owners sheet)))) :
    Nonempty (Gaussian.Equivalence.NamedEquivalent (ownerName piece.traced.finishOwner)
      (ownerName ((frames.frameAt finish edge.vertices.2).owners ((edges.edge edge).forward.target sheet)))) := by
  obtain ⟨equivalent⟩ := initial
  let connection := edges.edge edge
  have backEq : connection.reverse.forward.target (connection.forward.target sheet) = sheet :=
    (connection.bijection (BranchCellBank.referenceAt bank start edge.vertices.1).toLoop
      (BranchCellBank.referenceAt bank finish edge.vertices.2).toLoop).backward_forward sheet
  let backward := connection.reverse.trace (connection.forward.target sheet)
  have ready : Gaussian.Equivalence.NamedEquivalent
      (ownerName ((frames.frameAt start edge.vertices.1).owners (connection.reverse.forward.target
        (connection.forward.target sheet))))
      (ownerName owner) := by
    rw [backEq]
    exact equivalent.symm
  let join := OwnerPath.join curve.polynomial start _ owner ready
  let loop := backward.append (join.append piece.path.traced.trace.get)
  have winding : Polygon.Basic.chainRaw curve.polynomial finish loop.vertices = 8 * (0 : Int) := by
    rw [OwnerPath.append_winding, OwnerPath.append_winding,
      connection.reverse.trace_winding, OwnerPath.join_winding, TracedPath.winding_original piece.path.traced]
    have reverse := ClearSegment.rawWinding_reverse edge.segment
    change (Segment.segment curve.polynomial finish start).doubledWinding =
      -(Segment.segment curve.polynomial start finish).doubledWinding at reverse
    change (Segment.segment curve.polynomial finish start).doubledWinding +
      (0 + ((Segment.segment curve.polynomial start finish).doubledWinding + 0)) = _
    rw [reverse]
    omega
  exact ⟨OwnerPath.rootEquivalent_of_even_with_reference
    (BranchCellBank.referenceAt bank finish edge.vertices.2).toLoop loop 0 winding⟩

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}

/-- Every actual source owner agrees with the cached lifted index assigned to that occurrence. A numerical request need
not construct these witnesses. -/
def OwnersAligned
  {ambient : Rational.Box} :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : Owner (curve.polynomial.eval start)} {prepared : PreparedPath path owner} {pieces : CoveredSegments
        prepared},
      PreparedFaceSegments.AssignedSegments mesh pieces → Prop
  | _, _, _, _, _, _, .nil _ _ => True
  | _, _, _, owner, _, _, .cons placement tail =>
      Nonempty (Gaussian.Equivalence.NamedEquivalent (ownerName owner) (ownerName (vertices.owner frames
        placement.indexed.start))) ∧ tail.OwnersAligned

/-- The agreement proof consumes the semantic cached-index equation, not the internals of the assignment constructor.
Generated assignments satisfying that same equation have the identical owner guarantee. -/
theorem
  ownersAligned_of_indexed
  (mesh : LiftedMesh vertices edges faces) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} (walk : Walks.Walk bank.grid start finish) (sheet : Fin 2)
      (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid start) {owner : Owner
        (curve.polynomial.eval start)}
      {prepared : PreparedPath walk.path owner} {pieces : CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces),
      assigned.indexed = edges.indexedEdges vertices walk sheet →
      Nonempty (Gaussian.Equivalence.NamedEquivalent (ownerName owner) (ownerName ((frames.frameAt start member).owners
        sheet))) →
      assigned.OwnersAligned := by
  intro start finish walk
  induction walk with
  | nil point =>
      intro sheet member owner prepared pieces assigned equal initial
      cases assigned
      trivial
  | cons edge tail ih =>
      intro sheet member owner prepared pieces assigned equal initial
      cases assigned with
      | cons placement remaining =>
          have headEq : placement.indexed = edges.indexedEdge vertices edge sheet := (List.cons.inj equal).1
          constructor
          · rw [headEq]
            change Nonempty (Gaussian.Equivalence.NamedEquivalent (ownerName owner)
              (ownerName (vertices.owner frames (vertices.index _ edge.vertices.1 sheet))))
            rw [VertexBank.ownerName_index]
            exact initial
          · exact ih ((edges.edge edge).forward.target sheet) edge.vertices.2 remaining
              (List.cons.inj equal).2 (edges.coveredSegment_finish_aligned edge _ sheet initial)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments
