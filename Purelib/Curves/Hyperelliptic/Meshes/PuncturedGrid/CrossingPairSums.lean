module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SheetSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement
import Mathlib.Algebra.Ring.Defs
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
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Collapse the actual retained crossings over both sheets before pairing faces. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet} {target : Fraction.Rational}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
  Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
  target}

variable {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Fraction.Rational} {floor stage : Nat}
  {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}

variable {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

/-- Decide whether two original rational boxes match along the specified grid side. -/
instance (side : Meshes.GridLiftedDualSteps.GridSide) (first next : Rational.Box) : Decidable
  (side.Matches first next) := by
  cases side <;> unfold Meshes.GridLiftedDualSteps.GridSide.Matches <;> infer_instance

/-- Extract the actual retained horizontal crossing when the original boxes satisfy the matching side equations. -/
private def horizontalRetained (outcome : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.HorizontalOutcome
  request first nextPosition)
    (matching : Meshes.GridLiftedDualSteps.GridSide.Matches .top faces.regulars[firstPosition.val].cell.box
      faces.regulars[nextPosition.val].cell.box) :
    { joined : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides.HorizontalCrossing request first
      nextPosition false false // outcome = .matched joined } := by
  cases outcome with
  | matched joined => exact ⟨joined, rfl⟩
  | separated obstruction =>
      cases obstruction with
      | lower different => exact (different matching.1).elim
      | upper different => exact (different matching.2.1).elim
      | boundary different => exact (different matching.2.2).elim

/-- Summing the original horizontal crossings over both sheets gives the matched top-minus-bottom perimeters, or zero
when the boxes do not match. -/
theorem CrossingBank.horizontal_pair_sum (retained :
  Matched.CrossingBank request mesh)
    (perimeters : Matched.FacePerimeters (request := request) cache i
      j)
    (firstPosition nextPosition : Fin faces.regulars.length) :
    FiniteSum.Fin.sumFin (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.HorizontalOutcome.perimeterDifference perimeters
      (((retained.horizontal.get firstPosition).get sheet).get nextPosition)) =
    if Meshes.GridLiftedDualSteps.GridSide.Matches .top faces.regulars[firstPosition.val].cell.box
      faces.regulars[nextPosition.val].cell.box then
      FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get firstPosition).get sheet).top) -
        FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get nextPosition).get sheet).bottom)
    else 0 := by
  by_cases matching : Meshes.GridLiftedDualSteps.GridSide.Matches .top faces.regulars[firstPosition.val].cell.box
    faces.regulars[nextPosition.val].cell.box
  · rw [if_pos matching]
    let chosen := fun sheet => Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums.horizontalRetained
      (((retained.horizontal.get firstPosition).get sheet).get nextPosition) matching
    have readback : ∀ sheet,
      Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.HorizontalOutcome.perimeterDifference perimeters
        (((retained.horizontal.get firstPosition).get sheet).get nextPosition) =
        ((perimeters.perimeters.get firstPosition).get sheet).top -
          ((perimeters.perimeters.get nextPosition).get (chosen sheet).val.crossing.next.sheet).bottom := by
      intro sheet
      exact congrArg (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.HorizontalOutcome.perimeterDifference
        perimeters) (chosen sheet).property
    rw [FiniteSum.Fin.sumFin_congr readback]
    exact Hyperelliptic.Meshes.PuncturedGrid.Matched.SheetSums.HorizontalCrossing.sum_perimeters (fun sheet =>
      (retained.sources.get firstPosition).get sheet)
      (fun sheet => (chosen sheet).val) perimeters
  · rw [if_neg matching]
    have zero : ∀ sheet, Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.HorizontalOutcome.perimeterDifference
      perimeters
        (((retained.horizontal.get firstPosition).get sheet).get nextPosition) = 0 := by
      intro sheet
      cases ((retained.horizontal.get firstPosition).get sheet).get nextPosition with
      | matched joined =>
        exact (matching (Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.HorizontalCrossing.physical_match
          joined)).elim
      | separated obstruction => rfl
    rw [FiniteSum.Fin.sumFin_congr zero, FiniteSum.Fin.sumFin_zero]

/-- Extract the actual retained vertical crossing when the original boxes satisfy the matching side equations. -/
private def verticalRetained (outcome : Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank.VerticalOutcome request
  first nextPosition)
    (matching : Meshes.GridLiftedDualSteps.GridSide.Matches .right faces.regulars[firstPosition.val].cell.box
      faces.regulars[nextPosition.val].cell.box) :
    { joined : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides.VerticalCrossing request first
      nextPosition false false // outcome = .matched joined } := by
  cases outcome with
  | matched joined => exact ⟨joined, rfl⟩
  | separated obstruction =>
      cases obstruction with
      | lower different => exact (different matching.1).elim
      | upper different => exact (different matching.2.1).elim
      | boundary different => exact (different matching.2.2).elim

/-- Summing the original vertical crossings over both sheets gives the matched right-minus-left perimeters, or zero when
the boxes do not match. -/
theorem CrossingBank.vertical_pair_sum (retained : Matched.CrossingBank
  request mesh)
    (perimeters : Matched.FacePerimeters (request := request) cache i
      j)
    (firstPosition nextPosition : Fin faces.regulars.length) :
    FiniteSum.Fin.sumFin (fun sheet =>
      Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.VerticalOutcome.perimeterDifference perimeters
      (((retained.vertical.get firstPosition).get sheet).get nextPosition)) =
    if Meshes.GridLiftedDualSteps.GridSide.Matches .right faces.regulars[firstPosition.val].cell.box
      faces.regulars[nextPosition.val].cell.box then
      FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get firstPosition).get sheet).right) -
        FiniteSum.Fin.sumFin (fun sheet => ((perimeters.perimeters.get nextPosition).get sheet).left)
    else 0 := by
  by_cases matching : Meshes.GridLiftedDualSteps.GridSide.Matches .right faces.regulars[firstPosition.val].cell.box
    faces.regulars[nextPosition.val].cell.box
  · rw [if_pos matching]
    let chosen := fun sheet => Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums.verticalRetained
      (((retained.vertical.get firstPosition).get sheet).get nextPosition) matching
    have readback : ∀ sheet,
      Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.VerticalOutcome.perimeterDifference perimeters
        (((retained.vertical.get firstPosition).get sheet).get nextPosition) =
        ((perimeters.perimeters.get firstPosition).get sheet).right -
          ((perimeters.perimeters.get nextPosition).get (chosen sheet).val.crossing.next.sheet).left := by
      intro sheet
      exact congrArg (Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.VerticalOutcome.perimeterDifference
        perimeters) (chosen sheet).property
    rw [FiniteSum.Fin.sumFin_congr readback]
    exact Hyperelliptic.Meshes.PuncturedGrid.Matched.SheetSums.VerticalCrossing.sum_perimeters (fun sheet =>
      (retained.sources.get firstPosition).get sheet)
      (fun sheet => (chosen sheet).val) perimeters
  · rw [if_neg matching]
    have zero : ∀ sheet, Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters.VerticalOutcome.perimeterDifference
      perimeters
        (((retained.vertical.get firstPosition).get sheet).get nextPosition) = 0 := by
      intro sheet
      cases ((retained.vertical.get firstPosition).get sheet).get nextPosition with
      | matched joined =>
        exact (matching (Hyperelliptic.Meshes.PuncturedGrid.NeighborCrossingAgreement.VerticalCrossing.physical_match
          joined)).elim
      | separated obstruction => rfl
    rw [FiniteSum.Fin.sumFin_congr zero, FiniteSum.Fin.sumFin_zero]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
