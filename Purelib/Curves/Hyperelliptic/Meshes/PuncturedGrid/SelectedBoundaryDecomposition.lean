module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideNeighborConsistency
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingPairSums
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NeighborPerimeterSums.BranchCellBank.PuncturedFaces

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.TwoSheetRequest

open Purelib.Riemann.Meshes

open Purelib.Riemann.Meshes.GridLiftedDualSteps

open Purelib.Riemann.Meshes.PuncturedGridFaces

public section

/-! Separate selected physical sides from the regular selection interfaces.
Incoming interfaces are reindexed by the actual opposite-side geometry. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition
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
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (CrossingBank)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedPerimeterIdentity.SelectedSides (value transition)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSideRemainders.TwoSheetRequest.SelectedSides
  (boundaryEvaluation)
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
    VertexBank bank.grid} {edges :
    RootEdgeBank frames}
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

namespace SelectedSides

/-- The signed contribution of actual selected physical sides in the retained neighbor bank. -/
@[expose] def physicalEvaluation (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (neighbors.entries.get p).right (SelectedSides.value (keep
    p) (values .right p))) -
    FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (neighbors.entries.get p).left (SelectedSides.value (keep
      p) (values .left p))) -
    (FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (neighbors.entries.get p).top (SelectedSides.value (keep
      p) (values .top p))) -
      FiniteSum.Fin.sumFin (fun p => SideNeighbor.physicalValue (neighbors.entries.get p).bottom (SelectedSides.value
        (keep p) (values .bottom p))))

/-- The actual selected-to-discarded regular interface contributions on the specified geometric side. -/
@[expose] def outgoingSum (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) (side :
      GridLiftedDualSteps.GridSide) : Gaussian :=
  FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (fun next =>
    if side.Matches (faces.regulars[p.val]'p.isLt).cell.box (faces.regulars[next.val]'next.isLt).cell.box ∧
      keep p = true ∧ keep next = false then values side p else 0))

/-- The complete signed regular selection-interface contribution, retaining all four original side directions. -/
@[expose] def interfaceEvaluation (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) : Gaussian :=
  outgoingSum keep values .bottom
    + outgoingSum keep values
    .right - outgoingSum keep
    values .top - outgoingSum keep
    values .left

/-- An interface transition is its outgoing value minus the oppositely selected value.

The retained geometric predicate and two Boolean selections determine both
conditional contributions directly, including the absent-interface case. -/
private theorem transition_eq (p : Prop) [Decidable p] (a b : Bool) (x y : Data.Gaussian.Basic.Canonical) :
    (if p then SelectedSides.transition a b x y else 0) =
      (if p ∧ a = true ∧ b = false then x else 0) - (if p ∧ b = true ∧ a = false then y else 0) := by
  have falseTrue : ¬(false = true) := by intro equal; cases equal
  have trueFalse : ¬(true = false) := by intro equal; cases equal
  by_cases present : p
  · rw [if_pos present]
    cases a with
    | false =>
        cases b with
        | false =>
            rw [if_neg (fun h => falseTrue h.2.1), if_neg (fun h => falseTrue h.2.1)]
            dsimp only [SelectedSides.transition, SelectedSides.value, Bool.and, Bool.not]
            rw [if_neg falseTrue, if_neg falseTrue]
        | true =>
            rw [if_neg (fun h => falseTrue h.2.1), if_pos ⟨present, rfl, rfl⟩]
            rfl
    | true =>
        cases b with
        | false =>
            rw [if_pos ⟨present, rfl, rfl⟩, if_neg (fun h => falseTrue h.2.1)]
            rfl
        | true =>
            rw [if_neg (fun h => trueFalse h.2.2), if_neg (fun h => trueFalse h.2.2)]
            dsimp only [SelectedSides.transition, SelectedSides.value, Bool.and, Bool.not]
            rw [if_neg falseTrue, if_neg falseTrue]
  · rw [if_neg present, if_neg (fun h => present h.1), if_neg (fun h => present h.1)]
    ring1

/-- Taking the opposite geometric side twice restores the original side. -/
private theorem opposite_twice (side : GridLiftedDualSteps.GridSide) : side.opposite.opposite = side := by cases side
  <;> rfl

/-- Opposite-side matching splits the interface sum into two directed contributions.

Pointwise finite-sum transport preserves the selected values and their original
indices. Reversing the geometric match identifies the incoming contribution
with the outgoing sum on the opposite side. -/
private theorem transition_sum (keep : Fin faces.regulars.length → Bool)
    (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length → Data.Gaussian.Basic.Canonical) (side :
      GridLiftedDualSteps.GridSide) :
    FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (fun next =>
      if side.Matches (faces.regulars[p.val]'p.isLt).cell.box (faces.regulars[next.val]'next.isLt).cell.box then
        SelectedSides.transition (keep p) (keep next) (values side p) (values side.opposite next) else 0)) =
      outgoingSum keep values side
        - outgoingSum keep values
        side.opposite := by
  let outgoing (p next : Fin faces.regulars.length) : Gaussian :=
    if side.Matches (faces.regulars[p.val]'p.isLt).cell.box (faces.regulars[next.val]'next.isLt).cell.box ∧
      keep p = true ∧ keep next = false then values side p else 0
  let incoming (p next : Fin faces.regulars.length) : Gaussian :=
    if side.Matches (faces.regulars[p.val]'p.isLt).cell.box (faces.regulars[next.val]'next.isLt).cell.box ∧
      keep next = true ∧ keep p = false then values side.opposite next else 0
  have split : FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (fun next =>
      if side.Matches (faces.regulars[p.val]'p.isLt).cell.box (faces.regulars[next.val]'next.isLt).cell.box then
        SelectedSides.transition (keep p) (keep next) (values side p) (values side.opposite next) else 0)) =
      FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (outgoing p)) -
        FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (incoming p)) := by
    calc
      _ = FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (fun next => outgoing p next - incoming p next)) :=
        sumFin_congr (fun p => sumFin_congr (fun next => transition_eq _ _ _ _ _))
      _ = FiniteSum.Fin.sumFin (fun p =>
          FiniteSum.Fin.sumFin (outgoing p) - FiniteSum.Fin.sumFin (incoming p)) :=
        sumFin_congr (fun p => sumFin_sub (outgoing p) (incoming p))
      _ = _ := sumFin_sub _ _
  have reverseSum : FiniteSum.Fin.sumFin (fun p => FiniteSum.Fin.sumFin (incoming p)) =
      outgoingSum keep values side.opposite := by
    rw [FiniteSum.Fin.sumFin_swap]
    apply sumFin_congr
    intro p
    apply sumFin_congr
    intro next
    dsimp only [incoming]
    have matching : side.Matches (faces.regulars[next.val]'next.isLt).cell.box (faces.regulars[p.val]'p.isLt).cell.box ↔
        side.opposite.Matches (faces.regulars[p.val]'p.isLt).cell.box (faces.regulars[next.val]'next.isLt).cell.box :=
      ⟨fun h => h.reverse, fun h => (opposite_twice side) ▸ h.reverse⟩
    by_cases selected : side.Matches (faces.regulars[next.val]'next.isLt).cell.box
      (faces.regulars[p.val]'p.isLt).cell.box ∧
        keep p = true ∧ keep next = false
    · rw [if_pos selected, if_pos ⟨matching.mp selected.1, selected.2⟩]
    · rw [if_neg selected, if_neg (fun h => selected ⟨matching.mpr h.1, h.2⟩)]
  exact split.trans (congrArg (fun value => outgoingSum keep values side - value) reverseSum)

/-- The retained selected boundary splits into actual physical sides and regular selection interfaces. -/
theorem boundaryEvaluation_partition (neighbors : PuncturedFaces.NeighborBank faces)
    (keep : Fin faces.regulars.length → Bool) (values : GridLiftedDualSteps.GridSide → Fin faces.regulars.length →
      Data.Gaussian.Basic.Canonical) :

      SelectedSideRemainders.TwoSheetRequest.SelectedSides.boundaryEvaluation
      neighbors keep values =
      physicalEvaluation neighbors
      keep values +
      interfaceEvaluation keep
      values := by
  unfold SelectedSides.boundaryEvaluation
  have right := transition_sum
    keep values .right
  have top := transition_sum keep
    values .top
  dsimp only [GridSide.opposite] at right top
  rw [right, top]
  dsimp only [physicalEvaluation,
    interfaceEvaluation,
    GridSide.opposite]
  ring1

end SelectedSides
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedBoundaryDecomposition
