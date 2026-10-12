module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
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
end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path.Basic

end
