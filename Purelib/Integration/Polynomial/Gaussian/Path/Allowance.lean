module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Data.List.Fold
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic
namespace PathModel

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Data.List

section
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Sum the displacement-weighted allowances of the original Gaussian cells in retained list order. -/
def totalWeightedAllowance (path : Basic.PathModel)
  : Fraction.Rational :=
  path.cells.foldr (fun cell total => cell.weightedAllowance + total) 0

/-- The exact original cell count times the sum of their weighted allowances.

This count-weighted allowance keeps every original cell occurrence, including repeated cells. -/
def aggregateAllowance (path : Basic.PathModel) :
  Fraction.Rational :=
  (path.cells.length : Fraction.Rational) * path.totalWeightedAllowance

end

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The sum of the original Gaussian cells' weighted allowances is nonnegative. -/
theorem totalWeightedAllowance_nonneg (path :
  Basic.PathModel) :
    0 <= path.totalWeightedAllowance := by
  unfold totalWeightedAllowance
  induction path.cells with
  | nil => exact le_rfl
  | cons cell remaining inductionHypothesis =>
      simp only [List.foldr_cons]
      exact add_nonneg cell.weightedAllowance_nonneg inductionHypothesis

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original path's count-weighted aggregate allowance is nonnegative. -/
theorem aggregateAllowance_nonneg (path :
  Basic.PathModel) :
    0 <= path.aggregateAllowance := by
  unfold aggregateAllowance
  exact Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le path.cells.length)) path.totalWeightedAllowance_nonneg

/-- Appending a retained last cell increases the actual finite list length by one. -/
private theorem length_last (last : CellModel) :
    ∀ cells : List CellModel, (cells ++ [last]).length = cells.length + 1
  | [] => rfl
  | _ :: remaining => by
    change (remaining ++ [last]).length + 1 = (remaining.length + 1) + 1
    rewrite [length_last last remaining]
    rfl

/-- The retained weighted allowances add on exact finite concatenation. -/
private theorem weighted_concat (first second : List CellModel) :
    (mk (first ++ second)).totalWeightedAllowance =
      (mk first).totalWeightedAllowance + (mk second).totalWeightedAllowance := by
  unfold totalWeightedAllowance
  rewrite [Fold.foldr_append]
  induction first with
  | nil => exact (Fraction.zero_add _).symm
  | cons cell remaining inductionHypothesis =>
    change cell.weightedAllowance + _ = (cell.weightedAllowance + _) + _
    rewrite [inductionHypothesis]
    exact (Fraction.add_assoc _ _ _).symm

/-- A cyclic head rotation preserves the original finite count and total weighted allowance. -/
theorem aggregateAllowance_rotateHead (path : PathModel) :
    path.rotateHead.aggregateAllowance = path.aggregateAllowance := by
  cases path with
  | mk cells =>
    cases cells with
    | nil => rfl
    | cons first remaining =>
      change ((remaining ++ [first]).length : Rational) * (mk (remaining ++ [first])).totalWeightedAllowance =
        ((remaining.length + 1 : Nat) : Rational) *
          (first.weightedAllowance + (mk remaining).totalWeightedAllowance)
      rewrite [length_last, weighted_concat]
      change ((remaining.length + 1 : Nat) : Rational) * ((mk remaining).totalWeightedAllowance +
        (first.weightedAllowance + 0)) =
          ((remaining.length + 1 : Nat) : Rational) * (first.weightedAllowance + (mk remaining).totalWeightedAllowance)
      have zero : first.weightedAllowance + 0 = first.weightedAllowance :=
        (Fraction.add_comm _ _).trans (Fraction.zero_add _)
      rewrite [zero]
      exact congrArg (fun total : Rational => ((remaining.length + 1 : Nat) : Rational) * total)
        (Fraction.add_comm _ _)
end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path.Basic

end
