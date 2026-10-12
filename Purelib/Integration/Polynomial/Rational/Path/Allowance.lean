module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Polynomial.Rational.Path.Basic
import Purelib.Integration.Polynomial.Rational.Cell.Allowance
import Purelib.Integration.Polynomial.Rational.Cell.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
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

namespace Purelib.Integration.Polynomial.Rational.Path.Basic
namespace PathModel

open Purelib.Data.Rat
open Purelib.Integration.Polynomial
/-- Combine the ordered cell allowances by repeatedly doubling the next weighted allowance plus the tail budget.

The empty path has zero allowance, and the exact recurrence retains the original cell order. -/
def aggregateAllowance (path :
  Rational.Path.Basic.PathModel) : Fraction.Rational :=
  path.cells.foldr
    (fun cell total => 2 * (cell.weightedAllowance + total)) 0

/-- The recursively aggregated path allowance is nonnegative. -/
theorem aggregateAllowance_nonneg (path :
  Rational.Path.Basic.PathModel) :
    0 ≤ path.aggregateAllowance := by
  unfold aggregateAllowance
  induction path.cells with
  | nil => exact le_rfl
  | cons cell remaining induction =>
      simp only [List.foldr_cons]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg cell.weightedAllowance_nonneg induction)
end PathModel

end Purelib.Integration.Polynomial.Rational.Path.Basic

end
