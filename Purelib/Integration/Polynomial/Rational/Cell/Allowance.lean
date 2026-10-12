module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Polynomial.Rational.Cell.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Polynomial.Rational.Cell.Basic
namespace CellModel

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial
/-- The retained displacement-weighted local allowance is nonnegative. -/
theorem weightedAllowance_nonneg (cell :
  Rational.Cell.Basic.CellModel) :
    0 ≤ cell.weightedAllowance :=
  Fraction.Order.Arithmetic.mul_nonneg_direct
    (Basic.Canonical.normSq_nonneg cell.displacement) cell.localAllowance_nonneg

/-- A local squared-error bound becomes the retained weighted allowance after multiplication by the exact cell
displacement. -/
theorem weighted_error_le (cell :
  Rational.Cell.Basic.CellModel) {error : Basic.Canonical}
    (bounded : Basic.Canonical.normSq error ≤ cell.localAllowance) :
    Basic.Canonical.normSq (cell.displacement * error) ≤ cell.weightedAllowance := by
  rw [Basic.Canonical.normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded
    (Basic.Canonical.normSq_nonneg cell.displacement)
end CellModel

end Purelib.Integration.Polynomial.Rational.Cell.Basic

end
