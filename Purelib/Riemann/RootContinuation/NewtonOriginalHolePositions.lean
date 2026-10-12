module
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides

open Purelib.Data

public section

/-! Original-region side acquisitions enumerate exactly the physical holes. -/
namespace Purelib.Riemann.RootContinuation.NewtonOriginalHolePositions

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision AnnularEntry)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus (HoleSides)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {current : LiftedPuncturedGrid grid.punctured}

open Purelib.Curves in
open Purelib.Data in
/-- The retained original-region side receipts enumerate every physical hole position exactly once.

Their existing hole identities and the excision's enumeration equality determine the list directly, without reacquiring
sides or choosing a permutation. -/
theorem original_side_positions (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    (sides : (entry : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current) →
      Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides entry.region) :
    excision.entries.map (fun entry => (sides entry).position) =
      List.ofFn (fun position : Fin grid.faces.holes.length => position) := by
  apply (List.Map.map_inj_right (f := fun position : Fin grid.faces.holes.length =>
    grid.faces.holes[position.val]'position.isLt) (fun first last equal =>
      Hyperelliptic.Meshes.PuncturedGrid.HoleSideSelection.hole_position_eq_of_cell grid.faces first last (congrArg
        BranchHole.cell equal))).mp
  rw [List.Map.map_map, List.OfFn.Basic.map_ofFn]
  have equal : excision.entries.map (fun entry => grid.faces.holes[(sides entry).position.val]'(sides
    entry).position.isLt) =
      excision.entries.map AnnularEntry.hole := by
    apply List.Map.map_congr_left
    intro entry _
    exact (sides entry).hole_eq.trans entry.hole_eq
  exact equal.trans (excision.holes_eq.trans (List.OfFn.Basic.ofFn_getElem _).symm)

open Purelib.Algebra in
open Purelib.Curves in
open Purelib.Data in
/-- Summing values through retained original-region side receipts equals the full physical-hole sum. -/
theorem original_side_sum (excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision grid current)
    (sides : (entry : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current) →
      Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides entry.region)
    (value : Fin grid.faces.holes.length → Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (excision.entries.map (fun entry => value (sides entry).position)) =
      FiniteSum.Fin.sumFin value := by
  have positions := congrArg (List.map value) (original_side_positions excision sides)
  simp only [List.Map.map_map, Function.comp_def, List.OfFn.Basic.map_ofFn] at positions
  exact (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum positions).trans
    (Gaussian.Norm.Sum.Indexed.sumFin_eq_gaussianSum value).symm

end Purelib.Riemann.RootContinuation.NewtonOriginalHolePositions
