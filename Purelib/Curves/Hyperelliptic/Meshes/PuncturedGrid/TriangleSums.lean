module
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

section

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

open Purelib.RootIsolation

public section

/-! The face-and-sheet traversal covers the actual mesh triangle index exactly. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums

/-- The original four-entry block index for a face position and triangle offset. -/
private def blockIndex {count : Nat} (position : Fin count) (offset : Fin 4) : Fin (4 * count) :=
  ⟨4 * position.val + offset.val, by have := position.isLt; have := offset.isLt; omega⟩

/-- The Gaussian sum over an empty finite index is zero. -/
private theorem sum_empty (values : Fin 0 → Gaussian.Basic.Canonical) : FiniteSum.Fin.sumFin values = 0 := rfl

/-- A Gaussian sum over four entries per position equals the sum of the original four-entry blocks. -/
private theorem sum_blocks : (count : Nat) → (values : Fin (4 * count) → Gaussian.Basic.Canonical) →
    FiniteSum.Fin.sumFin values = FiniteSum.Fin.sumFin (fun position =>
      values (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 0) + values
        (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 1) +
      values (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 2) + values
        (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 3)) := by
  intro count
  induction count with
  | zero => intro values; rfl
  | succ count ih =>
      intro values
      have tail := ih (fun index => values index.succ.succ.succ.succ)
      have shifted : FiniteSum.Fin.sumFin (fun position : Fin count =>
          values (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 0).succ.succ.succ.succ + values
            (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 1).succ.succ.succ.succ +
          values (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 2).succ.succ.succ.succ + values
            (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 3).succ.succ.succ.succ) =
          FiniteSum.Fin.sumFin (fun position : Fin count =>
          values (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position.succ 0) + values
            (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position.succ 1) +
          values (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position.succ 2) + values
            (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position.succ 3)) := by
        apply FiniteSum.Fin.sumFin_congr
        intro position
        have equal (offset : Fin 4) : (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position
          offset).succ.succ.succ.succ = Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position.succ offset
          := by
          apply Fin.ext
          simp only [Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex, Fin.val_succ]
          omega
        rw [equal, equal, equal, equal]
      have tailEq := tail.trans shifted
      conv_lhs => rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ,
        FiniteSum.Fin.sumFin_succ]
      conv_rhs => rw [FiniteSum.Fin.sumFin_succ]
      apply (congrArg (fun tail : Gaussian.Basic.Canonical => values 0 +
        (values (Fin.succ 0) + (values (Fin.succ 0).succ + (values (Fin.succ 0).succ.succ + tail)))) tailEq).trans
      have head0 : Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex (0 : Fin (count + 1)) 0 = (0 : Fin (4 *
        (count + 1))) := by
        apply Fin.ext
        rfl
      have head1 : Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex (0 : Fin (count + 1)) 1 = (Fin.succ 0 :
        Fin (4 * (count + 1))) := by
        apply Fin.ext
        rfl
      have head2 : Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex (0 : Fin (count + 1)) 2 = ((Fin.succ
        0).succ : Fin (4 * (count + 1))) := by
        apply Fin.ext
        rfl
      have head3 : Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex (0 : Fin (count + 1)) 3 = ((Fin.succ
        0).succ.succ : Fin (4 * (count + 1))) := by
        apply Fin.ext
        rfl
      rw [head0, head1, head2, head3]
      ring1

/-- The four-entry block decomposition transports along the retained exact index-size equality. -/
private theorem sum_blocks_cast {count size : Nat} (equal : size = 4 * count) (values : Fin size →
  Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin values = FiniteSum.Fin.sumFin (fun position =>
      values (Fin.cast equal.symm (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 0)) + values
        (Fin.cast equal.symm (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 1)) +
      values (Fin.cast equal.symm (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 2)) + values
        (Fin.cast equal.symm (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position 3))) := by
  subst size
  exact Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.sum_blocks count values

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {stage : Nat}
    {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {i j : Fin genus}

/-- The original mesh triangle sum equals the face-and-sheet traversal of both retained triangle orientations. -/
theorem LiftedMesh.triangle_sum (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces)
    (values : Fin mesh.triangles.length → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin values = FiniteSum.Fin.sumFin (fun position => FiniteSum.Fin.sumFin (fun sheet =>
      values (mesh.triangleIndex position sheet false) + values (mesh.triangleIndex position sheet true))) := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.sum_blocks_cast mesh.faceCount values]
  symm
  apply FiniteSum.Fin.sumFin_congr
  intro position
  have indexEq (sheet : Fin 2) (upper : Bool) (offset : Fin 4)
      (equal : 2 * sheet.val + (if upper then 1 else 0) = offset.val) :
      mesh.triangleIndex position sheet upper = Fin.cast mesh.faceCount.symm
        (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.blockIndex position offset) := by
    apply Fin.ext
    change 4 * position.val + 2 * sheet.val + (if upper then 1 else 0) = 4 * position.val + offset.val
    omega
  simp only [FiniteSum.Fin.sumFin_succ, Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.sum_empty]
  rw [indexEq 0 false 0 (by decide), indexEq 0 true 1 (by decide),
    indexEq (Fin.succ 0) false 2 (by decide), indexEq (Fin.succ 0) true 3 (by decide)]
  ring1

/-- The full original two-sheet triangle area is exactly the Gaussian sum over the retained mesh triangle index. -/
theorem RegularMeshes.TwoSheetRequest.fullTriangleArea_eq_sum
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) :
    Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.fullTriangleArea left right =
      FiniteSum.Fin.sumFin (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left
        right) :=
  (Hyperelliptic.Meshes.PuncturedGrid.TriangleSums.LiftedMesh.triangle_sum mesh
    (Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right)).symm

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums

end
