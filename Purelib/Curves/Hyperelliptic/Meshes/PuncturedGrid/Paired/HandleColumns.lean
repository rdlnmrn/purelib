module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.LinearAlgebra.Alternating.NormalForm.Intersection
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Pairing
import Purelib.LinearAlgebra.Vector.Unit
import Purelib.LinearAlgebra.Alternating.Handle.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.IntersectionResolution
import Purelib.LinearAlgebra.Alternating.Handle.UnitPairing
import Init.Prelude
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.LinearAlgebra.Alternating.Handle

open Purelib.LinearAlgebra.Vector

@[expose] public section

/-! Column symplectic identities on exactly the retained genus-many handles. -/
section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered (Paired)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms (Prepared)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates (CutBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleCoordinates.CutBank (HandleRows)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_neg)
open Purelib.LinearAlgebra.Alternating

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
    {sheet : Fin 2}
  {ordered :
    Ordered bank
    sheet} {paired : Paired ordered}
    {prepared : Prepared paired}
  (cut : CutBank prepared)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

/-- The original normal-form pivot at the retained genus index, using the exact handle-count equality. -/
def pivotAt
    (index : Fin genus) : Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count :=
  cut.normal.pivots[index.val]'(by rw [cut.handles_eq]; exact index.isLt)

/-- Every genus-indexed pivot belongs to the original retained normal-form pivot list. -/
theorem pivotAt_member
    (index : Fin genus) : cut.pivotAt index ∈ cut.normal.pivots :=
  List.getElem_mem (by rw [cut.handles_eq]; exact index.isLt)

/-- Distinct retained genus indices select distinct original normal-form pivots. -/
theorem pivotAt_injective
    {first last : Fin genus} (equal : cut.pivotAt first = cut.pivotAt last) : first = last := by
  apply Fin.ext
  exact congrArg (fun index : Fin cut.normal.pivots.length => index.val) (Handle.Basic.handleIndex_injective
    cut.normal.pivots cut.normal.normal.pivots_nodup
    ⟨first.val, by rw [cut.handles_eq]; exact first.isLt⟩
    ⟨last.val, by rw [cut.handles_eq]; exact last.isLt⟩ equal)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleColumns

/-- Equality of the selected original pivots gives exactly the Kronecker delta on their retained genus indices. -/
private theorem pivot_delta (first last : Fin genus) :
    (if cut.pivotAt first = cut.pivotAt last then (1 : Int) else 0) = if first = last then 1 else 0 := by
  by_cases same : first = last
  · rw [if_pos same, if_pos (congrArg cut.pivotAt same)]
  · rw [if_neg same, if_neg (fun equal => same (cut.pivotAt_injective equal))]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleColumns

variable (rows : HandleRows cut)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

/-- The complete wedge sum between two first pivot columns of the original handle rows is zero. -/
theorem first_column_wedges
    (first last : Fin genus) :
    FiniteSum.Fin.sumFin (fun index : Fin genus =>
      Data.Vector.get (rows.get index).a (cut.pivotAt first).1 * Data.Vector.get (rows.get index).b (cut.pivotAt last).1
        -
      Data.Vector.get (rows.get index).b (cut.pivotAt first).1 * Data.Vector.get (rows.get index).a (cut.pivotAt
        last).1) = 0 := by
  have equal := cut.handle_reconstruction rows (Unit.unitVector (cut.pivotAt first).2) (Unit.unitVector (cut.pivotAt
    last).2)
  have endpoint := UnitPairing.handlePairing_units_last_last cut.normal.normal.disjoint _ _ (cut.pivotAt_member first)
    (cut.pivotAt_member last)
  apply Eq.trans _ (equal.symm.trans endpoint)
  exact FiniteSum.Fin.sumFin_congr (fun index => by
    rw [(UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member first) (rows.get
      index).a).2,
      (UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member last) (rows.get
        index).b).2,
      (UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member first) (rows.get
        index).b).2,
      (UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member last) (rows.get
        index).a).2])

/-- The complete wedge sum between two last pivot columns of the original handle rows is zero. -/
theorem last_column_wedges
    (first last : Fin genus) :
    FiniteSum.Fin.sumFin (fun index : Fin genus =>
      Data.Vector.get (rows.get index).a (cut.pivotAt first).2 * Data.Vector.get (rows.get index).b (cut.pivotAt last).2
        -
      Data.Vector.get (rows.get index).b (cut.pivotAt first).2 * Data.Vector.get (rows.get index).a (cut.pivotAt
        last).2) = 0 := by
  have equal := cut.handle_reconstruction rows (Unit.unitVector (cut.pivotAt first).1) (Unit.unitVector (cut.pivotAt
    last).1)
  have endpoint := UnitPairing.handlePairing_units_first_first cut.normal.normal.disjoint _ _ (cut.pivotAt_member first)
    (cut.pivotAt_member last)
  apply Eq.trans _ (equal.symm.trans endpoint)
  apply FiniteSum.Fin.sumFin_congr
  intro index
  rw [(UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member first) (rows.get
    index).a).1,
    (UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member last) (rows.get
      index).b).1,
    (UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member first) (rows.get
      index).b).1,
    (UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member last) (rows.get
      index).a).1]
  ring1

/-- The complete mixed pivot-column wedge sum is the Kronecker delta on the exact original genus indices. -/
theorem mixed_column_wedges
    (first last : Fin genus) :
    FiniteSum.Fin.sumFin (fun index : Fin genus =>
      Data.Vector.get (rows.get index).a (cut.pivotAt first).1 * Data.Vector.get (rows.get index).b (cut.pivotAt last).2
        -
      Data.Vector.get (rows.get index).b (cut.pivotAt first).1 * Data.Vector.get (rows.get index).a (cut.pivotAt
        last).2) =
      if first = last then 1 else 0 := by
  have equal := cut.handle_reconstruction rows (Unit.unitVector (cut.pivotAt first).2) (Unit.unitVector (cut.pivotAt
    last).1)
  have endpoint := UnitPairing.handlePairing_units_last_first cut.normal.normal.disjoint _ _ (cut.pivotAt_member first)
    (cut.pivotAt_member last)
  rw [Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.HandleColumns.pivot_delta cut] at endpoint
  have terms : FiniteSum.Fin.sumFin (fun index : Fin genus =>
      Pairing.handlePairing cut.normal.pivots (rows.get index).a (Unit.unitVector (cut.pivotAt first).2) *
        Pairing.handlePairing cut.normal.pivots (rows.get index).b (Unit.unitVector (cut.pivotAt last).1) -
      Pairing.handlePairing cut.normal.pivots (rows.get index).b (Unit.unitVector (cut.pivotAt first).2) *
        Pairing.handlePairing cut.normal.pivots (rows.get index).a (Unit.unitVector (cut.pivotAt last).1)) =
      -FiniteSum.Fin.sumFin (fun index : Fin genus =>
        Data.Vector.get (rows.get index).a (cut.pivotAt first).1 * Data.Vector.get (rows.get index).b (cut.pivotAt
          last).2 -
        Data.Vector.get (rows.get index).b (cut.pivotAt first).1 * Data.Vector.get (rows.get index).a (cut.pivotAt
          last).2) := by
    apply Eq.trans (FiniteSum.Fin.sumFin_congr (fun index => ?_)) (FiniteSum.Fin.sumFin_neg _)
    rw [(UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member first) (rows.get
      index).a).2,
      (UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member last) (rows.get
        index).b).1,
      (UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member first) (rows.get
        index).b).2,
      (UnitPairing.handlePairing_right_unit_handle cut.normal.normal.disjoint _ (cut.pivotAt_member last) (rows.get
        index).a).1]
    ring1
  have negated := congrArg Neg.neg (terms.symm.trans (equal.symm.trans endpoint))
  exact (neg_neg _).symm.trans (negated.trans (neg_neg _))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

end
