module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCornerBounds
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

public section

open Purelib
open Purelib.Algebra
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedCornerBounds
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.GridLiftedDualSteps
open Purelib.Riemann.Meshes.PuncturedGridFaces

/-! Exact partition of selected source triangles into internal crossings
and the original triangles left at physical or selection boundary sides. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (CrossingBank)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank (HorizontalOutcome
  VerticalOutcome)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_add sumFin_neg sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_zero)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed target}
  {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Rational} {floor stage :
    Nat}
  {retained : Matched.CrossingBank request mesh}
  {cache : Numerics domains stage}

/-- A selected scalar splits into the kept-neighbor and discarded-neighbor contributions. -/
private theorem value_split (first last : Bool) (area : Data.Gaussian.Basic.Canonical) :
    SelectedSides.value first area = SelectedSides.value (first && last) area +
      SelectedSides.value (first && !last) area := by
  cases first <;> cases last <;>
    simp only [SelectedSides.value, Bool.and, Bool.not, if_neg (by decide : ¬ false = true), if_pos (Eq.refl true),
      -eq_self, -iff_self] <;> ring1

/-- Every original triangle of a selected regular face, on both sheets. -/
@[expose] def selectedFullTriangleArea
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (keep : Fin faces.regulars.length → Bool) : Gaussian :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b =>
    SelectedSides.value (keep a) (TriangleReadings.bilinearArea left right (mesh.triangleIndex a b false)) +
    SelectedSides.value (keep a) (TriangleReadings.bilinearArea left right (mesh.triangleIndex a b true))))

/-- The physical right/top side triangles and outgoing right/top triangles whose next regular face is discarded. These
are actual source occurrences. -/
@[expose] def selectedBoundaryTriangleArea (neighbors : PuncturedFaces.NeighborBank faces)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (keep : Fin faces.regulars.length → Bool) : Gaussian :=
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b =>
    SideNeighbor.physicalValue (neighbors.entries.get a).right
      (SelectedSides.value (keep a) (TriangleReadings.bilinearArea left right (mesh.triangleIndex a b false))) +
    SideNeighbor.physicalValue (neighbors.entries.get a).top
      (SelectedSides.value (keep a) (TriangleReadings.bilinearArea left right (mesh.triangleIndex a b true))))) +
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    if GridSide.Matches .right (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars[c.val]'c.isLt).cell.box then
      SelectedSides.value (keep a && !keep c) (TriangleReadings.bilinearArea left right (mesh.triangleIndex a b false))
        else 0))) +
  FiniteSum.Fin.sumFin (fun a => FiniteSum.Fin.sumFin (fun b => FiniteSum.Fin.sumFin (fun c =>
    if GridSide.Matches .top (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars[c.val]'c.isLt).cell.box then
      SelectedSides.value (keep a && !keep c) (TriangleReadings.bilinearArea left right (mesh.triangleIndex a b true))
        else 0)))

/-- One selected side triangle partitions into internal, physical-boundary and discarded-neighbor terms. -/
private theorem side_partition (a : Fin faces.regulars.length) (side : GridLiftedDualSteps.GridSide)
    (neighbor : PuncturedFaces.SideNeighbor faces (faces.regulars[a.val]'a.isLt) side)
    (keep : Fin faces.regulars.length → Bool) (area : Data.Gaussian.Basic.Canonical) :
    SelectedSides.value (keep a) area =
      FiniteSum.Fin.sumFin (fun c => if side.Matches (faces.regulars[a.val]'a.isLt).cell.box
        (faces.regulars[c.val]'c.isLt).cell.box then
        SelectedSides.value (keep a && keep c) area else 0) +
      SideNeighbor.physicalValue neighbor (SelectedSides.value (keep a) area) +
      FiniteSum.Fin.sumFin (fun c => if side.Matches (faces.regulars[a.val]'a.isLt).cell.box
        (faces.regulars[c.val]'c.isLt).cell.box then
        SelectedSides.value (keep a && !keep c) area else 0) := by
  have split (c : Fin faces.regulars.length) :
      (if side.Matches (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars[c.val]'c.isLt).cell.box then
        SelectedSides.value (keep a) area else 0) =
      (if side.Matches (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars[c.val]'c.isLt).cell.box then
        SelectedSides.value (keep a && keep c) area else 0) +
      (if side.Matches (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars[c.val]'c.isLt).cell.box then
        SelectedSides.value (keep a && !keep c) area else 0) := by
    split
    · exact value_split (keep a) (keep c) area
    · exact (show (0 : Data.Gaussian.Basic.Canonical) = 0 + 0 by ring1)
  have regular := SideNeighbor.sum_matching neighbor (SelectedSides.value (keep a) area)
  have readback :
      (FiniteSum.Fin.sumFin (fun c => if side.Matches (faces.regulars[a.val]'a.isLt).cell.box (faces.regulars.get
        c).cell.box then
        SelectedSides.value (keep a) area else 0)) =
      FiniteSum.Fin.sumFin (fun c => if side.Matches (faces.regulars[a.val]'a.isLt).cell.box
        (faces.regulars[c.val]'c.isLt).cell.box then
        SelectedSides.value (keep a) area else 0) :=
    FiniteSum.Fin.sumFin_congr (fun c => by rw [List.get_eq_getElem])
  rw [readback, FiniteSum.Fin.sumFin_congr split, FiniteSum.Fin.sumFin_add] at regular
  calc
    _ = _ := SideNeighbor.value_split neighbor (SelectedSides.value (keep a) area)
    _ = _ := by rw [← regular]; ring1

/-- The complete selected triangle area splits into actual internal crossings and retained boundary triangles.

The identity preserves both sheets and the original right/top source occurrences at every selected face. -/
theorem CrossingBank.selected_triangle_partition (retained : Matched.CrossingBank request mesh)
    (neighbors : PuncturedFaces.NeighborBank faces)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (keep : Fin faces.regulars.length → Bool) :
    selectedFullTriangleArea left right keep
      = CrossingBank.selectedTriangleArea retained left right keep +
      selectedBoundaryTriangleArea neighbors left
        right keep := by
  have pointwise := FiniteSum.Fin.sumFin_congr (fun a => FiniteSum.Fin.sumFin_congr (fun b =>
    congrArg₂ (fun x y : Data.Gaussian.Basic.Canonical => x + y)
      (side_partition a .right
        (neighbors.entries.get a).right keep (TriangleReadings.bilinearArea left right (mesh.triangleIndex a b false)))
      (side_partition a .top (neighbors.entries.get
        a).top keep (TriangleReadings.bilinearArea left right (mesh.triangleIndex a b true)))))
  unfold SelectedTrianglePartition.selectedFullTriangleArea
  rw [pointwise]
  simp only [CrossingBank.selectedTriangleArea,
    selectedBoundaryTriangleArea,
    HorizontalOutcome.triangleArea_eq_if (left := left) (right := right),
    VerticalOutcome.triangleArea_eq_if (left := left) (right := right), -eq_self, -iff_self]
  have select_if (p : Prop) [Decidable p] (chosen : Bool) (area : Data.Gaussian.Basic.Canonical) :
      SelectedSides.value chosen (if p then area else 0) = if p then SelectedSides.value chosen area else 0 := by
    split
    · rfl
    · exact SelectedSides.value_zero chosen
  simp only [select_if, FiniteSum.Fin.sumFin_add, -eq_self, -iff_self]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
