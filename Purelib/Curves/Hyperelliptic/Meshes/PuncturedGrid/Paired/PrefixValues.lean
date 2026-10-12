module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Read the actual corrected B prefix as the finite sum of preceding A words. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PrefixValues

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {reference : Hyperelliptic.Branches.BranchIsolation.Data.Index branches}

namespace PairedRows

/-- The original prior word reads as the base prior value plus the finite sum of preceding A values. -/
theorem prior_value
    {labels : List (Hyperelliptic.Branches.BranchIsolation.Data.Index branches ×
      Hyperelliptic.Branches.BranchIsolation.Data.Index branches)}
    {prior : Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop lifted sheet} (rows :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows bank reference sheet labels prior)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (index : Fin
      labels.length) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value (rows.get index).prior.indexed =
      Topology.Surface.Sewing.SewingRetraction.wordValue value prior.indexed +
      FiniteSum.Fin.sumFin (fun earlier : Fin labels.length => if earlier.val < index.val then
        Topology.Surface.Sewing.SewingRetraction.wordValue value (rows.get earlier).row.a.closed.indexed else 0) := by
  induction rows with
  | nil => exact Fin.elim0 index
  | @cons labels rest prior row tail ih =>
      rcases index with ⟨position, bounded⟩
      cases position with
      | zero =>
        change Topology.Surface.Sewing.SewingRetraction.wordValue value prior.indexed =
          Topology.Surface.Sewing.SewingRetraction.wordValue value prior.indexed + _
        have zero : FiniteSum.Fin.sumFin (fun earlier : Fin (labels :: rest).length => if earlier.val < 0 then
            Topology.Surface.Sewing.SewingRetraction.wordValue value
              ((Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.PairedRows.cons row tail).get
              earlier).row.a.closed.indexed else 0) = 0 :=
          (FiniteSum.Fin.sumFin_congr (fun earlier => if_neg (Nat.not_lt_zero earlier.val))).trans
            FiniteSum.Fin.sumFin_zero
        exact (congrArg (Topology.Surface.Sewing.SewingRetraction.wordValue value prior.indexed + ·) zero).trans
          (Gaussian.Basic.add_zero _ ) |>.symm
      | succ position =>
        let index : Fin rest.length := ⟨position, Nat.lt_of_succ_lt_succ bounded⟩
        change Topology.Surface.Sewing.SewingRetraction.wordValue value (tail.get index).prior.indexed = _
        rw [ih index, FiniteSum.Fin.sumFin_succ]
        change Topology.Surface.Sewing.SewingRetraction.wordValue value (prior.indexed ++ row.a.closed.indexed) + _ =
          Topology.Surface.Sewing.SewingRetraction.wordValue value prior.indexed + ((if 0 < index.val + 1 then
            Topology.Surface.Sewing.SewingRetraction.wordValue value row.a.closed.indexed else 0) + _)
        rw [Topology.Surface.Sewing.SewingRetraction.wordValue_append, if_pos (Nat.zero_lt_succ _)]
        have equal := FiniteSum.Fin.sumFin_congr (fun earlier : Fin rest.length =>
          (show (if earlier.val < index.val then Topology.Surface.Sewing.SewingRetraction.wordValue value (tail.get
            earlier).row.a.closed.indexed else 0) =
              (if earlier.val + 1 < index.val + 1 then Topology.Surface.Sewing.SewingRetraction.wordValue value
                (tail.get earlier).row.a.closed.indexed else 0) from by
            by_cases before : earlier.val < index.val
            · rw [if_pos before, if_pos (Nat.add_lt_add_right before 1)]
            · rw [if_neg before, if_neg (fun later => before (Nat.lt_of_add_lt_add_right later))]))
        rw [equal, Gaussian.Basic.add_assoc]
        rfl
end PairedRows

section Ordered.Paired
variable {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank
  sheet} (paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered)

/-- Transporting the retained finite index preserves the exact Gaussian sum. -/
private theorem sum_cast {first last : Nat} (equal : first = last) (value : Fin first → Gaussian.Basic.Canonical) :
    FiniteSum.Fin.sumFin value = FiniteSum.Fin.sumFin (fun index : Fin last => value (Fin.cast equal.symm index)) := by
  cases equal
  rfl

/-- The original ordered prior word reads as the finite sum of preceding A values. -/
theorem prior_value (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
  (index : Fin genus) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.row index).prior.indexed =
      FiniteSum.Fin.sumFin (fun earlier : Fin genus => if earlier.val < index.val then
        Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.row earlier).row.a.closed.indexed else 0) := by
  have reading := Hyperelliptic.Meshes.PuncturedGrid.Paired.PrefixValues.PairedRows.prior_value paired.rows value
    (Fin.cast paired.split.count_eq.symm index)
  change Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.row index).prior.indexed = 0 + _ at reading
  rw [Gaussian.Basic.zero_add] at reading
  exact reading.trans (sum_cast
    paired.split.count_eq _)

/-- The original corrected B word reads as its B value plus the preceding A-prefix sum. -/
theorem corrected_value (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical)
  (index : Fin genus) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.row index).row.corrected.indexed =
      Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.row index).row.b.closed.indexed +
        FiniteSum.Fin.sumFin (fun earlier : Fin genus => if earlier.val < index.val then
          Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.row earlier).row.a.closed.indexed else 0) :=
            by
  rw [(paired.row index).row.corrected_eq]
  change Topology.Surface.Sewing.SewingRetraction.wordValue value ((paired.row index).row.b.closed.indexed ++
    (paired.row index).prior.indexed) = _
  rw [Topology.Surface.Sewing.SewingRetraction.wordValue_append,
    prior_value paired]

namespace Prepared
variable (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)

/-- The retained prepared B word reads as the original B value plus the exact preceding prepared A-prefix sum. -/
theorem bWord_prefix_value (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count →
  Gaussian.Basic.Canonical) (index : Fin genus) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index) =
      Topology.Surface.Sewing.SewingRetraction.wordValue value (paired.row index).row.b.closed.indexed +
      FiniteSum.Fin.sumFin (fun earlier : Fin genus => if earlier.val < index.val then
        Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord earlier) else 0) := by
  rw [prepared.bWord_eq, corrected_value paired]
  apply congrArg (_ + ·)
  apply FiniteSum.Fin.sumFin_congr
  intro earlier
  rw [prepared.aWord_eq]

end Prepared
end Ordered.Paired
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PrefixValues
