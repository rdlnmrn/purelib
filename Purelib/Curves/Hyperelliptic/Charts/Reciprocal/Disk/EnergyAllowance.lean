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

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {cover :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data}
  {prepared : Hyperelliptic.Charts.Reciprocal.Disk.ParentComparison.Preparation regular cover} {totalTarget areaTarget :
    Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The original joined request's quarter tolerance is at most one. -/
theorem JoinedRequest.energy_join_small (joined : Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent.JoinedRequest
  prepared totalTarget areaTarget floor) : joined.budget.tolerance / 4 ≤ 1 := by
  have nonnegative := joined.budget.positive.le
  have quarter : joined.budget.tolerance / 4 ≤ joined.budget.tolerance := by
    apply (Fraction.Order.Field.div_le_iff_pos (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4)).mpr
    exact (show joined.budget.tolerance = joined.budget.tolerance * 1 by ring1).trans_le
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide) nonnegative)
  exact quarter.trans (joined.budget.tolerance_eq.trans_le (Fraction.Order.Basic.min_le_left _ _))

/-- The original request already pays the full growing-count estimate.
Only original cell counts enter this calculation, not the final fine mesh. -/
theorem ChartReplacementRequest.energy_allowance
    {target : Normalization.InverseRootPolynomial.Coordinate} (replacement :
      ChartReplacementRequest prepared target floor)
    (joined : Hyperelliptic.Charts.Reciprocal.Disk.JoinedParent.JoinedRequest prepared totalTarget areaTarget floor) :
    ((2 * cover.mesh.edges.length : Nat) : Normalization.InverseRootPolynomial.Coordinate) ^ 2 *
      (replacement.localTarget + joined.budget.tolerance / 4) < 4 * target + totalTarget / 4 := by
  let n : Coordinate := (cover.mesh.edges.length : Normalization.InverseRootPolynomial.Coordinate)
  let localTarget := replacement.localTarget
  let tolerance := joined.budget.tolerance
  have localNonnegative : 0 ≤ localTarget := replacement.localPositive.le
  have quarterNonnegative : 0 ≤ localTarget / 4 := Fraction.Order.Field.div_nonneg_direct localNonnegative (by decide)
  have localLe : localTarget ≤ 2 * (localTarget + localTarget / 4) := by
    have first : localTarget ≤ localTarget + localTarget / 4 := le_add_of_nonneg_right quarterNonnegative
    have second : localTarget + localTarget / 4 ≤ 2 * (localTarget + localTarget / 4) := by
      exact (show localTarget + localTarget / 4 = 1 * (localTarget + localTarget / 4) by ring1).trans_le
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) (add_nonneg localNonnegative
          quarterNonnegative))
    exact first.trans second
  have chartPaid : 4 * n ^ 2 * localTarget < 4 * target := by
    have bound := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localLe
      (Fraction.Order.Arithmetic.sq_nonneg_direct n)).trans_lt replacement.paid
    have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : Normalization.InverseRootPolynomial.Coordinate) < 4) bound
    exact (show 4 * n ^ 2 * localTarget = 4 * (n ^ 2 * localTarget) by ring1).trans_lt
      scaled
  have joinPaid : n ^ 2 * tolerance < totalTarget / 4 := by
    have nonnegative := Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct n)
      joined.budget.positive.le
    have bound : n ^ 2 * tolerance ≤ 4 * n ^ 2 * tolerance :=
      (show n ^ 2 * tolerance = 1 * (n ^ 2 * tolerance) by ring1).trans_le
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by
            decide : (1 : Normalization.InverseRootPolynomial.Coordinate) ≤ 4) nonnegative).trans_eq (by ring1))
    exact bound.trans_lt joined.budget.total_paid
  have paid := Fraction.Order.Arithmetic.add_lt_add_direct chartPaid joinPaid
  refine (show ((2 * cover.mesh.edges.length : Nat) : Normalization.InverseRootPolynomial.Coordinate) ^ 2 *
    (replacement.localTarget + joined.budget.tolerance / 4) = 4 * n ^ 2 * localTarget + n ^ 2 * tolerance by
      calc
        _ = 4 * n ^ 2 * localTarget + n ^ 2 * ((tolerance / 4) * 4) := by
          simp only [Algebra.NatCast.mul, Nat.cast_ofNat]
          dsimp only [n, localTarget, tolerance]
          ring1
        _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]).trans_lt paid

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EnergyAllowance
