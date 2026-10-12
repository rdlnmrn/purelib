module
import Purelib.Algebra.FiniteSum.Gaussian
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugateWindowTriangles
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCells
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitSheets
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FinePolygonAggregate
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CircuitAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.Extension

open Purelib.Riemann.RootContinuation

public section

/-! The two original boundary traversals account for every triangle of
the selected original annulus, with the actual cached face positions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugateWindowSelectedTriangles

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowCircuits (fineOrder fineCompiler)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.FineConjugatePolygonAggregate (fineConjugateTriangleArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas (selectedConjugateFullTriangleArea)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_succ)
attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
    {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {current : Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {stage : Nat} {cache : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
    domains stage}

/-- Both initial sheets together cover the retained face triangles, even when the compiler transports them along
different stems. -/
theorem fine_conjugate_triangles_selected (region : NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) :
    CellBoundary.sumValues (FineConjugatePolygonAggregate.fineConjugateTriangleArea left right)
      (WindowCircuits.fineCompiler (current := current) region 0).regulars +
      CellBoundary.sumValues (FineConjugatePolygonAggregate.fineConjugateTriangleArea left right)
        (WindowCircuits.fineCompiler (current := current) region 1).regulars =
      ConjugateTriangleAreas.selectedConjugateFullTriangleArea left right (fun position =>
        decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (original.cell index).box)) := by
  let value := fun position sheet =>
    TriangleReadings.conjugateArea left right (current.mesh.triangleIndex position sheet false) +
      TriangleReadings.conjugateArea left right (current.mesh.triangleIndex position sheet true)
  have paired := CircuitPartition.compileResplit_two_sheets
    (CoordinateInclusion.refl grid.punctured.bank.grid) current.edges current.vertices
    (fun point member => (BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank point member).toLoop)
    (grid.shrunk.included.vertex (ClearGrid.Cell.anchor_mem (original.cell index) (original.cell_mem index)))
    (WindowCircuits.fineOrder (current := current) region 0).partition value 0 1 (by decide)
  have positions := WindowCells.fineCompiler_position_sum (current := current) region 0
    (fun position => value position 0 + value position 1)
  refine paired.trans (positions.trans ?_)
  apply FiniteSum.Fin.sumFin_congr
  intro position
  dsimp only [ConjugateTriangleAreas.selectedConjugateFullTriangleArea, SelectedPerimeterIdentity.SelectedSides.value]
  by_cases selected : (grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (original.cell index).box
  · rewrite [if_pos selected]
    refine (FiniteSum.Gaussian.sumFin_two_gaussian (fun sheet => value position sheet)).symm.trans ?_
    apply FiniteSum.Fin.sumFin_congr
    intro sheet
    dsimp only [value]
    exact (congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b)
      (if_pos (decide_eq_true selected)) (if_pos (decide_eq_true selected))).symm
  · rewrite [if_neg selected]
    symm
    refine Eq.trans ?_ (FiniteSum.Fin.sumFin_zero (n := 2))
    apply FiniteSum.Fin.sumFin_congr
    intro sheet
    have rejected : ¬ decide _ = true := fun equal =>
      Bool.noConfusion ((decide_eq_false selected).symm.trans equal)
    exact (congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b)
      (if_neg rejected) (if_neg rejected)).trans (Data.Gaussian.Basic.add_zero 0)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugateWindowSelectedTriangles
