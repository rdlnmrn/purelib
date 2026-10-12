module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Basic
namespace CellModel

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- The original displacement squared norm times the cell's retained local allowance. -/
def weightedAllowance (cell : Basic.CellModel) :
  Fraction.Rational :=
  Basic.Canonical.normSq cell.displacement * cell.localAllowance

section
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell
/-- Replace the local allowance with the supplied nonnegative allowance, retaining the original endpoints and
polynomial.

The constructed cell has an empty observation list rather than retaining observations indexed by the previous allowance.
-/
def withAllowance (cell : Basic.CellModel)
  (allowance : Fraction.Rational)
    (allowanceNonnegative : 0 <= allowance) : Basic.CellModel :=
  { start := cell.start
    finish := cell.finish
    polynomial := cell.polynomial
    localAllowance := allowance
    localAllowance_nonneg := allowanceNonnegative
    observations := [] }

/-- Replacing the local allowance preserves the original displacement. -/
@[simp] theorem withAllowance_displacement (cell :
  Basic.CellModel)
    (allowance : Fraction.Rational) (allowanceNonnegative : 0 <= allowance) :
    (cell.withAllowance allowance allowanceNonnegative).displacement =
      cell.displacement := rfl

/-- Replacing the local allowance preserves the exact original integral sample. -/
@[simp] theorem withAllowance_integralSample (cell :
  Basic.CellModel)
    (allowance : Fraction.Rational) (allowanceNonnegative : 0 <= allowance) :
    (cell.withAllowance allowance allowanceNonnegative).integralSample =
      cell.integralSample := rfl

end

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell
/-- Every Gaussian cell's displacement-weighted allowance is nonnegative. -/
theorem weightedAllowance_nonneg (cell :
  Basic.CellModel) :
    0 <= cell.weightedAllowance :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Basic.Canonical.normSq_nonneg cell.displacement) cell.localAllowance_nonneg

/-- A local squared-error bound becomes the retained weighted allowance after multiplication by the original cell
displacement. -/
theorem weighted_error_le (cell : Basic.CellModel)
  {error : Basic.Canonical}
    (bounded : Basic.Canonical.normSq error <= cell.localAllowance) :
    Basic.Canonical.normSq (cell.displacement * error) <= cell.weightedAllowance := by
  rw [Basic.Canonical.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
    (Basic.Canonical.normSq_nonneg cell.displacement)
end CellModel

end Purelib.Integration.Polynomial.Gaussian.Cell.Basic

end
