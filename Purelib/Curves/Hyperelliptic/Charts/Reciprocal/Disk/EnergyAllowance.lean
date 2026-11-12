module
import Purelib.Algebra.NatCast
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReplacementRequest
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathArea
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Riemann

public section

/-!
# Energy allowances for independent joined and replacement requests

No new source, root reader, or join request is prepared. The already retained
chart and endpoint budgets pay the complete energy comparison, independently
of the final chart and radial subdivision counts.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyAllowance

open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {regular : RegularBounds.Data cap} {cover :
    UniformReciprocalCover.Cover data}
  {prepared : ParentComparison.Preparation regular cover} {totalTarget areaTarget :
    Coordinate} {floor : Nat}

/-- The original joined request's quarter tolerance is at most one. -/
theorem JoinedRequest.energy_join_small (joined : JoinedParent.JoinedRequest
  prepared totalTarget areaTarget floor) : joined.budget.tolerance / 4 ≤ 1 := by
  have nonnegative := joined.budget.positive.le
  have quarter : joined.budget.tolerance / 4 ≤ joined.budget.tolerance := by
    apply (Field.div_le_iff_pos (by
        decide : (0 : Coordinate) < 4)).mpr
    exact (show joined.budget.tolerance = joined.budget.tolerance * 1 by ring1).trans_le
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide) nonnegative)
  exact quarter.trans (joined.budget.tolerance_eq.trans_le (Basic.min_le_left _ _))

/-- The original request already pays the full growing-count estimate.
Only original cell counts enter this calculation, not the final fine mesh. -/
theorem ChartReplacementRequest.energy_allowance
    {target : Coordinate} (replacement :
      ChartReplacementRequest prepared target floor)
    (joined : JoinedParent.JoinedRequest prepared totalTarget areaTarget floor) :
    ((2 * cover.mesh.edges.length : Nat) : Coordinate) ^ 2 *
      (replacement.localTarget + joined.budget.tolerance / 4) < 4 * target + totalTarget / 4 := by
  let n : Coordinate := (cover.mesh.edges.length : Coordinate)
  let localTarget := replacement.localTarget
  let tolerance := joined.budget.tolerance
  have localNonnegative : 0 ≤ localTarget := replacement.localPositive.le
  have quarterNonnegative : 0 ≤ localTarget / 4 := Field.div_nonneg_direct localNonnegative (by decide)
  have localLe : localTarget ≤ 2 * (localTarget + localTarget / 4) := by
    have first : localTarget ≤ localTarget + localTarget / 4 := le_add_of_nonneg_right quarterNonnegative
    have second : localTarget + localTarget / 4 ≤ 2 * (localTarget + localTarget / 4) := by
      exact (show localTarget + localTarget / 4 = 1 * (localTarget + localTarget / 4) by ring1).trans_le
        (Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) (add_nonneg localNonnegative
          quarterNonnegative))
    exact first.trans second
  have chartPaid : 4 * n ^ 2 * localTarget < 4 * target := by
    have bound := (Arithmetic.mul_le_mul_of_nonneg_left_direct localLe
      (Arithmetic.sq_nonneg_direct n)).trans_lt replacement.paid
    have scaled := Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Coordinate) < 4) bound
    exact (show 4 * n ^ 2 * localTarget = 4 * (n ^ 2 * localTarget) by ring1).trans_lt
      scaled
  have joinPaid : n ^ 2 * tolerance < totalTarget / 4 := by
    have nonnegative := Arithmetic.mul_nonneg_direct (Arithmetic.sq_nonneg_direct n)
      joined.budget.positive.le
    have bound : n ^ 2 * tolerance ≤ 4 * n ^ 2 * tolerance :=
      (show n ^ 2 * tolerance = 1 * (n ^ 2 * tolerance) by ring1).trans_le
        ((Arithmetic.mul_le_mul_of_nonneg_right_direct (by
            decide : (1 : Coordinate) ≤ 4) nonnegative).trans_eq (by ring1))
    exact bound.trans_lt joined.budget.total_paid
  have paid := Arithmetic.add_lt_add_direct chartPaid joinPaid
  refine (show ((2 * cover.mesh.edges.length : Nat) : Coordinate) ^ 2 *
    (replacement.localTarget + joined.budget.tolerance / 4) = 4 * n ^ 2 * localTarget + n ^ 2 * tolerance by
      calc
        _ = 4 * n ^ 2 * localTarget + n ^ 2 * ((tolerance / 4) * 4) := by
          simp only [Algebra.NatCast.mul, Nat.cast_ofNat]
          dsimp only [n, localTarget, tolerance]
          ring1
        _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]).trans_lt paid

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyAllowance
