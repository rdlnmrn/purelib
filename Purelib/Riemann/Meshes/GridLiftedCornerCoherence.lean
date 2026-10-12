module
import Purelib.Data.Fin
import Purelib.Riemann.Integration.PuncturedVertexConnections
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Paths.OwnerLoopMonodromy

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.VertexLiftChoices
import Purelib.RootIsolation.SquareRoot.Grid.EdgeCoherence

public section

/-!
# Coherence of selected face lifts and actual endpoint transports

A requested corner sheet identifies the original face sheet uniquely. The
stored selection is tied to its actual mesh lookup, so changing corners can
be compared using exact triangle indices. Affine-edge endpoint coherence and
inverse laws are used only in erased proofs, never to repeat preparation.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Polynomial.Geometry.Grid.Walks (Edge)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Integration.PuncturedVertexConnections (RegularIncident)

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient} {frames : RootFrames grid}
  {start finish otherStart otherFinish : Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Riemann
open Purelib.Polynomial
open Purelib.RootIsolation
/-- Root edges with equal oriented endpoints induce the same retained sheet transport.

The comparison uses the supplied winding-one references at the original endpoints. -/
theorem target_eq_of_endpoints (edges : RootEdgeBank frames) (left :
  Geometry.Grid.Walks.Edge grid start finish)
    (right : Geometry.Grid.Walks.Edge grid otherStart otherFinish) (startEq : otherStart = start) (finishEq :
      otherFinish = finish)
    (firstReference : Paths.OwnerLoopMonodromy.WindingOneLoop polynomial start)
    (lastReference : Paths.OwnerLoopMonodromy.WindingOneLoop polynomial finish) (sheet : Fin 2) :
    (edges.edge right).forward.target sheet = (edges.edge left).forward.target sheet := by
  cases startEq
  cases finishEq
  exact (edges.edge right).forward_target_eq (edges.edge left) firstReference lastReference sheet

/-- Root edges with opposite endpoints induce inverse retained sheet transports.

The supplied endpoint references identify the actual forward and reversed transports. -/
theorem target_opposite_of_endpoints (edges : RootEdgeBank frames) (left :
  Geometry.Grid.Walks.Edge grid start finish)
    (right : Geometry.Grid.Walks.Edge grid otherStart otherFinish) (startEq : otherStart = finish) (finishEq :
      otherFinish = start)
    (firstReference : Paths.OwnerLoopMonodromy.WindingOneLoop polynomial start)
    (lastReference : Paths.OwnerLoopMonodromy.WindingOneLoop polynomial finish) (sheet : Fin 2) :
    (edges.edge right).forward.target ((edges.edge left).forward.target sheet) = sheet := by
  cases startEq
  cases finishEq
  exact ((edges.edge right).forward_target_eq (edges.edge (.reverse left)) lastReference firstReference _).trans
    (((edges.edge left).bijection firstReference lastReference).backward_forward sheet)

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

section

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}

namespace Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

/-- Equal requested start sheets at one side force equal original face sheets.

The original two-coordinate case certificate identifies both supplied sheet indices. Opposite-sheet corner transport
excludes the two unequal alternatives at the retained side. -/
theorem sheet_eq_of_startSheet_eq {face : RegularFace bank} {firstSheet lastSheet : Fin 2}
    (first : LiftedFace vertices edges face firstSheet) (last : LiftedFace vertices edges face lastSheet)
    (side : GridSide) (equal : first.sideStartSheet side = last.sideStartSheet side) : firstSheet = lastSheet := by
  have firstCases : firstSheet = 0 ∨ firstSheet = 1 :=
    Data.Fin.cases_induction (Or.inl rfl)
      (fun index => Data.Fin.cases_induction (Or.inr rfl)
        (fun empty => Fin.elim0 empty) index) firstSheet
  have lastCases : lastSheet = 0 ∨ lastSheet = 1 :=
    Data.Fin.cases_induction (Or.inl rfl)
      (fun index => Data.Fin.cases_induction (Or.inr rfl)
        (fun empty => Fin.elim0 empty) index) lastSheet
  rcases firstCases with firstEq | firstEq <;>
    rcases lastCases with lastEq | lastEq <;> subst firstSheet <;> subst lastSheet
  · rfl
  · exact (first.sideStartSheet_ne last side equal).elim
  · exact (last.sideStartSheet_ne first side equal.symm).elim
  · rfl

end Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

namespace Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

/-- A side-selected triangle is the original face lookup at its retained selected sheet.

The retained side lookup chooses an existing face occurrence and sheet. Both decision branches read that same cached
triangle without rebuilding the face or edge transport. -/
theorem locateAtSide_triangle_eq {faces : PuncturedFaces bank} (mesh : LiftedMesh vertices edges faces)
    (position : Fin faces.regulars.length) (side : GridSide) (requested : Fin 2) (upper : Bool) :
    (mesh.locateAtSide position side requested).located.occurrence.triangle upper =
      (mesh.locateFace position (mesh.locateAtSide position side requested).sheet).occurrence.triangle upper := by
  unfold LiftedMesh.locateAtSide LiftedMesh.selectSide
  by_cases equal : (mesh.locateFace position 0).lifted.sideStartSheet side = requested
  · rw [dif_pos equal]
  · rw [dif_neg equal]

end Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh

end

namespace Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident.Lifted

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {point : Purelib.Data.Gaussian.Basic.Canonical} {frames : RootIsolation.SquareRoot.Grid.RootFrames
    base.bank.grid} {vertices : VertexBank base.bank.grid}
  {edges : RootEdgeBank frames} {mesh :
    LiftedMesh vertices edges base.faces}
  {regular : RegularIncident base point} {requested : Fin 2}

/-- A lifted regular incident retains the exact triangle of its original face and selected sheet.

The stored selection equation identifies the actual side lookup. Its triangle readback retains the original regular-face
index and selected sheet of the supplied lifted incident. -/
theorem triangle_eq (lifted : regular.Lifted mesh requested) (upper : Bool) :
    lifted.value.located.occurrence.triangle upper =
      (mesh.locateFace regular.located.index lifted.value.sheet).occurrence.triangle upper := by
  rw [lifted.value_eq]
  exact mesh.locateAtSide_triangle_eq _ _ _ upper

end Purelib.Riemann.Integration.PuncturedVertexConnections.RegularIncident.Lifted

end
