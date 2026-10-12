module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Curves.Hyperelliptic.Meshes.Newton.BandConjugateWindowTriangles
import Purelib.Riemann.RootContinuation.NewtonBandWindowCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitSheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
public import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits

public section

/-! The two Newton-band boundary traversals account for every triangle of
the selected Newton annulus, with the actual cached face positions. -/
namespace Purelib.Riemann.RootContinuation.NewtonBandConjugateWindowSelectedTriangles

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits (fineOrder fineCompiler)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate (fineConjugateTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas (selectedConjugateFullTriangleArea)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_succ)
attribute [local congr] Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {preparation : NewtonPreparation original} {target radius : Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {index : Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index
    branches}
  {current : LiftedPuncturedGrid grid.punctured}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {stage : Nat} {cache : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
    stage}

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
/-- Both initial-sheet traversals account for every selected conjugate triangle area.

The identity uses the retained annular compiler's actual face positions, even when the two traversals transport their
sheets along different stems. -/
theorem fine_conjugate_triangles_selected (region : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
      :
    Geometry.Grid.CellBoundary.sumValues
      (Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate.fineConjugateTriangleArea left right)
      (fineCompiler (current := current) region 0).regulars +
      Geometry.Grid.CellBoundary.sumValues
        (Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate.fineConjugateTriangleArea left right)
        (fineCompiler (current := current) region 1).regulars =
      Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right (fun
        position =>
        decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index))) := by
  let value := fun position sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right
      (current.mesh.triangleIndex position sheet false) +
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right
        (current.mesh.triangleIndex position sheet true)
  have paired :=
    Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition.compileResplit_two_sheets
    (Geometry.Grid.Extension.CoordinateInclusion.refl grid.punctured.bank.grid) current.edges current.vertices
    (fun point member => (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
      grid.punctured.bank.toBranchCellBank point member).toLoop)
    (Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.anchor_onGrid region)
    (fineOrder (current := current) region 0).partition value 0 1 (by decide)
  have positions := Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces.fineCompiler_position_sum (current :=
    current) region 0
    (fun position => value position 0 + value position 1)
  refine paired.trans (positions.trans ?_)
  apply FiniteSum.Fin.sumFin_congr
  intro position
  dsimp only [Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas.selectedConjugateFullTriangleArea,
    Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value]
  have decisionReadback (sheet : Fin 2) :
      (if decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index)) then
        Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right
          (current.mesh.triangleIndex position sheet false) else 0) +
      (if decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index)) then
        Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right
          (current.mesh.triangleIndex position sheet true) else 0) =
      (if (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index) then
        Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right
          (current.mesh.triangleIndex position sheet false) else 0) +
      (if (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index) then
        Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right
          (current.mesh.triangleIndex position sheet true) else 0) := by
    by_cases selected : (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index)
    · rw [if_pos (decide_eq_true selected), if_pos (decide_eq_true selected), if_pos selected, if_pos selected]
    · have noDecision : decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box
        index)) ≠ true :=
        fun accepted => selected (of_decide_eq_true accepted)
      rw [if_neg noDecision, if_neg noDecision, if_neg selected, if_neg selected]
  refine Eq.trans ?_ (FiniteSum.Fin.sumFin_congr decisionReadback).symm
  change (if (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index)
    then value position 0 + value position 1 else 0) =
    FiniteSum.Fin.sumFin (fun sheet : Fin 2 =>
      (if (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index) then
        Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right
          (current.mesh.triangleIndex position sheet false) else 0) +
      (if (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index) then
        Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right
          (current.mesh.triangleIndex position sheet true) else 0))
  by_cases selected : (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index)
  · rw [if_pos selected]
    have each (sheet : Fin 2) :
        (if (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index) then
          Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right
            (current.mesh.triangleIndex position sheet false) else 0) +
        (if (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (grid.bands.box index) then
          Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings.conjugateArea left right
            (current.mesh.triangleIndex position sheet true) else 0) = value position sheet := by
      rw [if_pos selected, if_pos selected]
    rw [FiniteSum.Fin.sumFin_congr each]
    rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ]
    change value position 0 + value position 1 = value position 0 + (value position 1 + 0)
    rw [add_zero]
  · rw [if_neg selected]
    symm
    refine Eq.trans (b := FiniteSum.Fin.sumFin (fun _ : Fin 2 => (0 : Gaussian.Basic.Canonical))) ?_
      FiniteSum.Fin.sumFin_zero
    apply FiniteSum.Fin.sumFin_congr
    intro sheet
    rw [if_neg selected, if_neg selected, add_zero]

end Purelib.Riemann.RootContinuation.NewtonBandConjugateWindowSelectedTriangles
