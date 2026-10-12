module
import Purelib.Data.Nat.Multiplication
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Meshes.GridLiftedMesh
public import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Division
public import Purelib.Data.Nat.Remainder
import Mathlib.Order.Basic
import Purelib.Tactic.QuotientFreeOmega
public import Batteries.Data.List.Lemmas

public section

/-!
# Executable locations of the retained root-lifted faces

Lookup walks the existing lift spine and returns the actual cached lift and
its two triangle indices. It never reconstructs root owners, transports or
triangulations. The requested regular-face position and sheet are in the
result type, so a later dual step cannot silently use a different face.
-/

namespace Purelib.Riemann.Meshes.GridLiftedMesh

open scoped Purelib.Data.Nat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Topology.Mesh.QuadrilateralDual (QuadOccurrence)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

namespace LiftedFaces

open Purelib in
set_option genInjectivity false in
/-- A retained sheet lift at an original regular-face position with its exact triangle-list occurrence.

The bounded position indexes the original face list, and the quadrilateral occurrence identifies both triangles in the
retained lifted list. -/
structure Location {faces : List (RegularFace bank)} (lifts : LiftedFaces vertices edges faces)
    (position : Fin faces.length) (sheet : Fin 2) where
  /-- The exact original face lift at the retained position and sheet. -/ lifted : LiftedFace vertices edges
    faces[position.val] sheet
  /-- The exact two-triangle occurrence of the retained quadrilateral. -/ occurrence :
    Topology.Mesh.QuadrilateralDual.QuadOccurrence (fun index : Fin lifts.triangles.length =>
    lifts.triangles[index.val]) lifted.quad

constructive_injectivity Location

/-- Locate the requested sheet of the original first face in its four retained triangle positions.

Natural constructor cases select the original zero-sheet or one-sheet lift. The returned occurrence retains exactly the
first two or last two indices of the original four head triangles. -/
@[expose] def firstLocation {face : RegularFace bank} {faces : List (RegularFace bank)}
    (zero : LiftedFace vertices edges face 0) (one : LiftedFace vertices edges face 1)
    (tail : LiftedFaces vertices edges faces) (sheet : Fin 2) : Location (.cons zero one tail) 0 sheet := by
  rcases sheet with ⟨value, bound⟩
  cases value with
  | zero =>
      exact ⟨zero, ⟨⟨0, by change 0 < tail.triangles.length + 4; omega0⟩,
        ⟨1, by change 1 < tail.triangles.length + 4; omega0⟩, rfl, rfl⟩⟩
  | succ value =>
      cases value with
      | zero =>
          exact ⟨one, ⟨⟨2, by change 2 < tail.triangles.length + 4; omega0⟩,
            ⟨3, by change 3 < tail.triangles.length + 4; omega0⟩, rfl, rfl⟩⟩
      | succ value =>
          exact False.elim (Nat.not_lt_zero value
            (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))

/-- Locate an original face and sheet in the exact retained triangle list.

Each recursive tail step keeps the original lifted face and prepends the four original head triangles to its occurrence
certificate. -/
@[expose] def locate : {faces : List (RegularFace bank)} → (lifts : LiftedFaces vertices edges faces) →
    (position : Fin faces.length) → (sheet : Fin 2) → Location lifts position sheet
  | _, .nil, position, _ => Fin.elim0 position
  | _, .cons zero one tail, ⟨0, _⟩, sheet => firstLocation zero one tail sheet
  | _, .cons zero one tail, ⟨position + 1, bound⟩, sheet =>
      let found := tail.locate ⟨position, Nat.lt_of_succ_lt_succ bound⟩ sheet
      ⟨found.lifted, (((found.occurrence.prepend one.quad.secondTriangle).prepend one.quad.firstTriangle).prepend
        zero.quad.secondTriangle).prepend zero.quad.firstTriangle⟩

/-- The original face and sheet occupy triangle indices four times the face position plus twice the sheet, and its
successor.

Every recursive tail step adds the same four original head triangles. The retained sheet determines the two adjacent
indices within that unchanged four-triangle block. -/
theorem locate_indices : ∀ {faces : List (RegularFace bank)} (lifts : LiftedFaces vertices edges faces)
    (position : Fin faces.length) (sheet : Fin 2),
    (lifts.locate position sheet).occurrence.first.val = 4 * position.val + 2 * sheet.val ∧
      (lifts.locate position sheet).occurrence.second.val = 4 * position.val + 2 * sheet.val + 1
  | _, .nil, position, _ => Fin.elim0 position
  | _, .cons zero one tail, ⟨0, _⟩, sheet => by
      rcases sheet with ⟨value, bound⟩
      cases value with
      | zero => exact ⟨rfl, rfl⟩
      | succ value =>
          cases value with
          | zero => exact ⟨rfl, rfl⟩
          | succ value => exact False.elim (Nat.not_lt_zero value
              (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ bound)))
  | _, .cons zero one tail, ⟨position + 1, bound⟩, sheet => by
      have previous := tail.locate_indices ⟨position, Nat.lt_of_succ_lt_succ bound⟩ sheet
      change (tail.locate ⟨position, _⟩ sheet).occurrence.first.val + 1 + 1 + 1 + 1 = _ ∧
        (tail.locate ⟨position, _⟩ sheet).occurrence.second.val + 1 + 1 + 1 + 1 = _
      rw [previous.1, previous.2]
      dsimp only [Fin.val_mk]
      constructor <;> omega0

end LiftedFaces

namespace LiftedMesh

open Purelib.Data.Nat

variable {faces : PuncturedFaces bank}

open Purelib in
set_option genInjectivity false in
/-- A retained original sheet lift together with its exact occurrence in the mesh triangulation.

The retained quadrilateral is the lift selected from the original face list and sheet. Its occurrence uses the same
stored triangulation and preserves both original bounded triangle indices. -/
structure LocatedFace (mesh : LiftedMesh vertices edges faces) (position : Fin faces.regulars.length) (sheet : Fin 2)
  where
  /-- The exact original face lift at the retained position and sheet. -/ lifted : LiftedFace vertices edges
    faces.regulars[position.val] sheet
  /-- The exact two-triangle occurrence of the retained quadrilateral. -/ occurrence :
    Topology.Mesh.QuadrilateralDual.QuadOccurrence mesh.triangulation.faces lifted.quad

constructive_injectivity LocatedFace

/-- Locate an original face and sheet in the retained mesh's exact triangulation.

The cached triangle-list equation transports the original lift occurrence without changing its value indices or
quadrilateral. -/
@[expose] def locateFace (mesh : LiftedMesh vertices edges faces) (position : Fin faces.regulars.length) (sheet : Fin 2)
  :
    LocatedFace mesh position sheet :=
  let found := mesh.lifts.locate position sheet
  let reindex := fun index : Fin mesh.lifts.triangles.length =>
    (⟨index.val, by rw [mesh.triangles_eq]; exact index.isLt⟩ : Fin mesh.triangles.length)
  ⟨found.lifted, found.occurrence.map mesh.triangulation.faces reindex (fun index => by
    rw [mesh.faces_eq]
    exact getElem_congr mesh.triangles_eq (rfl : (reindex index).val = index.val) (reindex index).isLt)⟩

/-- The retained mesh location has the exact two original face/sheet triangle indices. -/
theorem locateFace_indices (mesh : LiftedMesh vertices edges faces) (position : Fin faces.regulars.length) (sheet : Fin
  2) :
    (mesh.locateFace position sheet).occurrence.first.val = 4 * position.val + 2 * sheet.val ∧
      (mesh.locateFace position sheet).occurrence.second.val = 4 * position.val + 2 * sheet.val + 1 :=
  mesh.lifts.locate_indices position sheet

set_option genInjectivity false in
/-- An original triangle index resolved to its retained face position, sheet and half-quadrilateral.

The stored located face and selector retain an exact equation identifying the requested original triangle index. -/
structure LocatedTriangle (mesh : LiftedMesh vertices edges faces) (index : Fin mesh.triangles.length) where
  /-- The retained bounded position in the original regular-face list. -/ position : Fin faces.regulars.length
  /-- The retained original two-element sheet index. -/ sheet : Fin 2
  /-- Whether the original requested triangle is the second half of its quadrilateral. -/ upper : Bool
  /-- The retained original face/sheet occurrence in the mesh. -/ located : mesh.LocatedFace position sheet
  /-- The selected triangle occurrence is exactly the original requested index. -/ index_eq :
    located.occurrence.triangle upper = index

constructive_injectivity LocatedTriangle

/-- A reconstructed four-triangle index gives a bounded original face position.

The remainder is nonnegative, so a quotient at least as large as the original
face count would put the index beyond the supplied fourfold list bound. -/
private theorem face_position_bound {value count quotient remainder : Nat}
    (reconstructed : remainder + 4 * quotient = value) (bound : value < 4 * count) :
    quotient < count := by omega0

/-- A reconstructed remainder below four gives a bounded two-sheet index.

The same natural quotient by two identifies the original sheet. The supplied
remainder ceiling excludes a third sheet without changing the quotient operation. -/
private theorem sheet_position_bound {value quotient remainder : Nat}
    (reconstructed : remainder + 2 * quotient = value) (bound : value < 4) :
    quotient < 2 := by omega0

open Purelib in
/-- Resolve the original triangle index into its exact regular-face position, sheet and triangle half.

Division and remainders by four and two select the original stored occurrence, whose index equation is retained
explicitly. -/
@[expose] def locateTriangle (mesh : LiftedMesh vertices edges faces) (index : Fin mesh.triangles.length) :
    mesh.LocatedTriangle index := by
  let position : Fin faces.regulars.length := ⟨index.val / 4, by
    exact face_position_bound (Division.mod_add_div index.val 4)
      (index.isLt.trans_eq mesh.faceCount)⟩
  let sheet : Fin 2 := ⟨index.val % 4 / 2, by
    exact sheet_position_bound (Division.mod_add_div (index.val % 4) 2)
      (Nat.mod_lt index.val (by decide))⟩
  let upper := decide (index.val % 2 = 1)
  let located := mesh.locateFace position sheet
  refine ⟨position, sheet, upper, located, ?_⟩
  apply Fin.ext
  have indices := mesh.locateFace_indices position sheet
  change (located.occurrence.triangle upper).val = index.val
  have outerEquation := Division.mod_add_div index.val 4
  have innerEquation := Division.mod_add_div (index.val % 4) 2
  have parityEquation : index.val % 2 = (index.val % 4) % 2 := by
    calc
      index.val % 2 = (4 * (index.val / 4) + index.val % 4) % 2 :=
        congrArg (fun item : Nat => item % 2) (outerEquation.symm.trans (Nat.add_comm _ _))
      _ = (2 * (2 * (index.val / 4)) + index.val % 4) % 2 := by rw [← Multiplication.mul_assoc]
      _ = (index.val % 4) % 2 := Remainder.mul_add_mod 2 _ _
  have reconstructed : 4 * (index.val / 4) + 2 * (index.val % 4 / 2) + index.val % 2 = index.val := by
    calc
      _ = ((index.val % 4) % 2 + 2 * (index.val % 4 / 2)) + 4 * (index.val / 4) := by
        rw [parityEquation, Nat.add_comm (4 * (index.val / 4) + 2 * (index.val % 4 / 2)),
          Nat.add_assoc, Nat.add_comm (4 * (index.val / 4)), ← Nat.add_assoc]
      _ = index.val % 4 + 4 * (index.val / 4) :=
        congrArg (fun item : Nat => item + 4 * (index.val / 4)) innerEquation
      _ = index.val := outerEquation
  by_cases high : index.val % 2 = 1
  · have upperTrue : upper = true := by
      change decide (index.val % 2 = 1) = true
      exact _root_.decide_eq_true high
    rw [Topology.Mesh.QuadrilateralDual.QuadOccurrence.triangle, upperTrue]
    change (mesh.locateFace position sheet).occurrence.second.val = _
    rw [indices.2]
    dsimp only [position, sheet]
    exact (congrArg (fun item : Nat => 4 * (index.val / 4) + 2 * (index.val % 4 / 2) + item) high).symm.trans
      reconstructed
  · have upperFalse : upper = false := by
      change decide (index.val % 2 = 1) = false
      exact _root_.decide_eq_false high
    rw [Topology.Mesh.QuadrilateralDual.QuadOccurrence.triangle, upperFalse]
    change (mesh.locateFace position sheet).occurrence.first.val = _
    rw [indices.1]
    dsimp only [position, sheet]
    have remainderZero : index.val % 2 = 0 := by
      exact Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ
        (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ (Nat.mod_lt index.val (by decide : 0 < (2 : Nat)))) high))
    rw [remainderZero, Nat.add_zero] at reconstructed
    exact reconstructed

end LiftedMesh

end Purelib.Riemann.Meshes.GridLiftedMesh
