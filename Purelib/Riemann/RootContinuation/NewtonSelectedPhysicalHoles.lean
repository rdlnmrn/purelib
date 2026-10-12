module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Riemann.RootContinuation.NewtonSelectedSideGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPhysicalComponents
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Tactic.Ring

@[expose] public section

/-! Selected Newton-annulus faces contribute only to retained hole components:
their strict ambient containment rules out every selected exterior side. -/
namespace Purelib.Riemann.RootContinuation.NewtonSelectedPhysicalHoles
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value)
open Purelib.Riemann.RootContinuation.NewtonSelectedPerimeters.AllHoleExcision (fineMask)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {lifted : LiftedPuncturedGrid grid.punctured}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
/-- An original selected regular face contributes zero to the physical exterior boundary.

The retained excision excludes selected exterior faces; the original neighbor classification handles all other physical
locations directly. -/
private theorem exterior_value_zero (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (position : Fin grid.faces.regulars.length) (side : GridSide)
    (neighbor : PuncturedFaces.SideNeighbor grid.faces (grid.faces.regulars[position.val]'position.isLt) side) (value :
      Basic.Canonical) :
    Meshes.PuncturedGrid.PhysicalComponentValues.SideNeighbor.componentValue neighbor .exterior
      (Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides.value (fineMask excision position) value) = 0 := by
  cases neighbor with
  | exterior equal =>
    by_cases selected : fineMask excision position = true
    · exact False.elim (excision.selected_not_exterior position side selected equal)
    · exact if_neg selected
  | neighbor cell member matching location => cases location <;> rfl

open Purelib.Algebra
open Purelib.Curves.Hyperelliptic
open Purelib.Data.Gaussian
/-- The original selected exterior component evaluation is zero on every retained side. -/
theorem exteriorEvaluation_zero (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (values : GridSide → Fin grid.faces.regulars.length → Basic.Canonical) :
    Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation neighbors (fineMask excision) values .exterior =
      0 := by
  unfold Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation
  rw [FiniteSum.Fin.sumFin_congr (fun p => exterior_value_zero excision p .right (neighbors.entries.get p).right (values
    .right p)),
    FiniteSum.Fin.sumFin_congr (fun p => exterior_value_zero excision p .left (neighbors.entries.get p).left (values
      .left p)),
    FiniteSum.Fin.sumFin_congr (fun p => exterior_value_zero excision p .top (neighbors.entries.get p).top (values .top
      p)),
    FiniteSum.Fin.sumFin_congr (fun p => exterior_value_zero excision p .bottom (neighbors.entries.get p).bottom (values
      .bottom p))]
  simp only [FiniteSum.Fin.sumFin_zero]
  ring1

/-- The original selected physical-boundary evaluation equals the finite sum of its physical-hole components.

The exact retained neighbor bank and excision mask identify the same physical components; the exterior term vanishes
because selected faces cannot touch it. -/
theorem physicalEvaluation_eq_holes (excision : Meshes.Newton.AllHoles.Excision.AllHoleExcision grid lifted)
    (neighbors : PuncturedFaces.NeighborBank grid.faces)
    (values : GridSide → Fin grid.faces.regulars.length → Basic.Canonical) :
    Meshes.PuncturedGrid.SelectedBoundaryDecomposition.SelectedSides.physicalEvaluation neighbors (fineMask excision)
      values =
      FiniteSum.Fin.sumFin (fun hole => Meshes.PuncturedGrid.SelectedPhysicalComponents.componentEvaluation neighbors
        (fineMask excision) values (.hole hole)) := by
  rw [Meshes.PuncturedGrid.SelectedPhysicalComponents.physicalEvaluation_components, exteriorEvaluation_zero excision
    neighbors values, zero_add]

end Purelib.Riemann.RootContinuation.NewtonSelectedPhysicalHoles
