module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.OfFn.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CircuitTwoSheetCoverage
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CircuitRegularIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CircuitTwoSheetCoverage.BranchCellBank

open Purelib.Data.List

open Purelib.Polynomial.Geometry.Grid

@[expose] public section

/-! Complete regular-face sums on both sheets of the actual ordered window. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues sumValues_map)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
  (regularIndices)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)

/-- Permuting a finite list preserves the Gaussian sum of its actual entry readings. -/
private theorem OrderedRegularCoverage.sum_permutation {Item : Type} (value : Item → Data.Gaussian.Basic.Canonical)
  {first last : List Item}
    (order : List.Perm first last) : CellBoundary.sumValues value first = CellBoundary.sumValues value last := by
  induction order with
  | nil => rfl
  | cons head order ih => exact congrArg (value head + ·) ih
  | swap first last tail => change value _ + (value _ + _) = value _ + (value _ + _); ring1
  | trans first last ihFirst ihLast => exact ihFirst.trans ihLast

/-- Summing the explicit complete finite index list gives exactly the corresponding finite indexed sum. -/
private theorem OrderedRegularCoverage.sum_ofFn {count : Nat} (value : Fin count → Data.Gaussian.Basic.Canonical) :
    CellBoundary.sumValues value (List.ofFn (fun index : Fin count => index)) = FiniteSum.Fin.sumFin value := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [OfFn.Basic.ofFn_succ, FiniteSum.Fin.sumFin_succ]
      change value 0 + CellBoundary.sumValues value (List.ofFn (fun index : Fin count => index.succ)) = _
      have mapped := OfFn.Basic.map_ofFn (function := fun index : Fin count => index) (transform := Fin.succ)
      dsimp only [Function.comp_def] at mapped
      rw [← mapped, CellBoundary.sumValues_map]
      exact congrArg (value 0 + ·) (ih (fun index => value index.succ))

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Purelib.Riemann.Meshes.LiftedPuncturedGrid base} {bank :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
    {sheet : Fin 2}

namespace BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered
variable (ordered :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
  sheet)

/-- The full ambient window selects each retained regular position exactly once. -/
theorem
  regular_coverage
  : List.Perm ordered.prepared.partition.regularIndices
    (List.ofFn (fun index : Fin base.faces.regulars.length => index)) := by
  apply ordered.prepared.partition.regularIndices_coverage
  · rw [ordered.prepared.ordered.tree_eq]
    exact ordered.window.circuits_unique
  · intro index
    rw [ordered.prepared.ordered.tree_eq]
    exact (ordered.window.circuits_member).mpr
      ⟨(base.faces.regulars[index.val]'index.isLt).member, (base.faces.regulars[index.val]'index.isLt).cell.box_refines⟩

/-- The actual ordered regular occurrences sum to the complete finite regular-face sum. -/
theorem
  regular_sum
  (value : Fin base.faces.regulars.length → Data.Gaussian.Basic.Canonical) :
    CellBoundary.sumValues value ordered.prepared.partition.regularIndices = FiniteSum.Fin.sumFin value :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedRegularCoverage.sum_permutation value
    ordered.regular_coverage).trans (Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedRegularCoverage.sum_ofFn value)

/-- Local sheets are reached by the actual connector and prefix transports. -/
theorem
  twoSheet_regular_sum
  (value : Fin base.faces.regulars.length → Fin 2 → Data.Gaussian.Basic.Canonical) :
    CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet)
        (ordered.prepared.partition.compile lifted.edges lifted.vertices 0).regulars +
      CellBoundary.sumValues (fun occurrence => value occurrence.location.index occurrence.sheet)
        (ordered.prepared.partition.compile lifted.edges lifted.vertices 1).regulars =
      FiniteSum.Fin.sumFin (fun index => value index 0 + value index 1) :=
  (CircuitPartition.compile_twoSheet_sum lifted.edges lifted.vertices ordered.prepared.partition value).trans
    (ordered.regular_sum _)

end BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
