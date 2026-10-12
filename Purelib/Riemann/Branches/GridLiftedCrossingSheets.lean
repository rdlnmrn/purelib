module
import Purelib.Algebra.FiniteSum.Gaussian
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Data.Rat.Fraction.Field
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Polynomial.Dense.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Field
import Mathlib.Order.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Actual lifted crossings preserve the complete two-sheet sum. Sheet labels
may change; the retained side transports determine the permutation. -/
namespace Purelib.Riemann.Branches.GridLiftedCrossingSheets

open Purelib
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_succ)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

namespace LiftedFace

/-- Two retained lifts of the same original face and starting sheet have equal side-start sheets. -/
theorem sideStartSheet_same {face : RegularFace bank} {sheet : Fin 2}
    (first last : LiftedFace vertices edges face sheet) (side : GridSide) :
    first.sideStartSheet side = last.sideStartSheet side := by
  have bottom : first.lowerRight = last.lowerRight := first.bottom_eq.trans last.bottom_eq.symm
  have right : first.upperRight = last.upperRight := by rw [first.right_eq, last.right_eq, bottom]
  have top : first.upperLeft = last.upperLeft := by rw [first.top_eq, last.top_eq, right]
  cases side
  · rfl
  · exact bottom
  · exact right
  · exact top

/-- The two original sheet lifts have distinct finish sheets on every selected side. -/
theorem sideFinishSheet_ne {face : RegularFace bank}
    (zero : LiftedFace vertices edges face 0) (one : LiftedFace vertices edges face 1)
    (side : GridSide) : zero.sideFinishSheet side ≠ one.sideFinishSheet side := by
  cases side
  · exact zero.sideStartSheet_ne one .right
  · exact zero.sideStartSheet_ne one .top
  · exact zero.sideStartSheet_ne one .left
  · exact (by decide : (0 : Fin 2) ≠ 1)

end LiftedFace

namespace LiftedMesh

variable {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}
  {firstPosition nextPosition : Fin faces.regulars.length}
  {firstSide nextSide : GridSide}
  {first : (sheet : Fin 2) → mesh.LocatedFace firstPosition sheet}

/-- Crossing from both original sheet lifts selects distinct sheet indices at the next face. -/
theorem atSide_sheets_ne
    (next : (sheet : Fin 2) → mesh.AtSide nextPosition nextSide ((first sheet).lifted.sideFinishSheet firstSide)) :
    (next 0).sheet ≠ (next 1).sheet := by
  intro same
  have transport {a b : Fin 2} (left : mesh.LocatedFace nextPosition a)
      (right : mesh.LocatedFace nextPosition b) (equal : a = b) :
      left.lifted.sideStartSheet nextSide = right.lifted.sideStartSheet nextSide := by
    cases equal
    exact LiftedFace.sideStartSheet_same _ _ _
  have equal := transport (next 0).located (next 1).located same
  exact (LiftedFace.sideFinishSheet_ne (first 0).lifted (first 1).lifted firstSide)
    ((next 0).start_eq.symm.trans (equal.trans (next 1).start_eq))

open Purelib.Algebra in
open Purelib.Data.Gaussian in
/-- The exact two-sheet selection at an original crossing preserves a finite Gaussian sum.

The retained target sheets are distinct and therefore enumerate the same two original values, possibly in the opposite
order. -/
theorem atSide_sum
    (next : (sheet : Fin 2) → mesh.AtSide nextPosition nextSide ((first sheet).lifted.sideFinishSheet firstSide))
    (values : Fin 2 → Basic.Canonical) :
    FiniteSum.Fin.sumFin (fun sheet => values (next sheet).sheet) = FiniteSum.Fin.sumFin values := by
  rw [FiniteSum.Gaussian.sumFin_two_gaussian, FiniteSum.Gaussian.sumFin_two_gaussian]
  exact FiniteSum.Gaussian.two_sheets values (next 0).sheet (next 1).sheet (atSide_sheets_ne next)

open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The squared difference of original two-sheet sums is bounded by four times a common paired allowance.

The exact crossing sheet permutation pairs outgoing and incoming values before applying the finite Gaussian sum bound.
-/
theorem atSide_difference_bound
    (next : (sheet : Fin 2) → mesh.AtSide nextPosition nextSide ((first sheet).lifted.sideFinishSheet firstSide))
    (outgoing incoming : Fin 2 → Basic.Canonical) {allowance : Fraction.Rational}
    (bounded : ∀ sheet, Data.Gaussian.Norm.Basic.normSq
      (outgoing sheet - incoming (next sheet).sheet) ≤ allowance) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin outgoing - FiniteSum.Fin.sumFin incoming) ≤ 4 * allowance :=
      by
  rw [← atSide_sum next incoming, ← FiniteSum.Fin.sumFin_sub]
  exact (Norm.Sum.Indexed.normSq_sumFin_le _ allowance bounded).trans_eq (by
      change ((2 : Fraction.Rational) ^ 2) * allowance = 4 * allowance;
      rfl)

end LiftedMesh
end Purelib.Riemann.Branches.GridLiftedCrossingSheets
