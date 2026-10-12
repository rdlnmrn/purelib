module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingSheetPermutation
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingSheetPermutation.LiftedMesh

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

@[expose] public section

/-! Paired-side sums include both destination sheets exactly once. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SheetSums

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}
  {faces : PuncturedFaces bank} {domains :
    FaceDomainBank frames faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
    {target : Rational}
  {mesh : LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : TwoSheetRequest (fun sheet
  => RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Rational} {floor
  stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub)
variable {cache : Numerics domains
  stage}

/-- Summing horizontal crossing discrepancies counts both destination-sheet bottom perimeters exactly once. -/
theorem HorizontalCrossing.sum_perimeters
    (source : (sheet : Fin 2) → mesh.LocatedFace firstPosition sheet)
    (crossings : (sheet : Fin 2) → LiftedSides.HorizontalCrossing request (source sheet) nextPosition false false)
    (perimeters : FacePerimeters (request := request) cache i j) :
    FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get firstPosition).get sheet).top -
      ((perimeters.perimeters.get nextPosition).get (crossings sheet).crossing.next.sheet).bottom) =
    FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get firstPosition).get sheet).top) -
      FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get nextPosition).get sheet).bottom) := by
  rw [FiniteSum.Fin.sumFin_sub]
  exact congrArg (fun value => FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get firstPosition).get
    sheet).top) - value)
    (Crossing.sum_destination source (fun sheet => (crossings sheet).crossing)
      (fun sheet => ((perimeters.perimeters.get nextPosition).get sheet).bottom))

/-- Summing vertical crossing discrepancies counts both destination-sheet left perimeters exactly once. -/
theorem VerticalCrossing.sum_perimeters
    (source : (sheet : Fin 2) → mesh.LocatedFace firstPosition sheet)
    (crossings : (sheet : Fin 2) → LiftedSides.VerticalCrossing request (source sheet) nextPosition false false)
    (perimeters : FacePerimeters (request := request) cache i j) :
    FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get firstPosition).get sheet).right -
      ((perimeters.perimeters.get nextPosition).get (crossings sheet).crossing.next.sheet).left) =
    FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get firstPosition).get sheet).right) -
      FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get nextPosition).get sheet).left) := by
  rw [FiniteSum.Fin.sumFin_sub]
  exact congrArg (fun value => FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get firstPosition).get
    sheet).right) - value)
    (Crossing.sum_destination source (fun sheet => (crossings sheet).crossing)
      (fun sheet => ((perimeters.perimeters.get nextPosition).get sheet).left))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SheetSums
