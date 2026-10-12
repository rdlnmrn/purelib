module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Rational.Cell.Basic
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Integration.Polynomial.Rational.Path.Basic
public import Purelib.Integration.Program.Rational.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Rational.Path.Allowance
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

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

namespace Purelib.Integration.Program.Rational.Basic
namespace RefinementProgram

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Rational.Cell in
open Purelib.Integration.Polynomial.Rational.Path in
open Purelib.Integration.Program.Rational in
open Purelib.Polynomial.Ascending in
/-- Construct the constant refinement program for the exact original rational polynomial segment.

Every stage reuses the single original exact cell and its integral sample, with zero error scale and allowance and exact
sample magnitude bound. -/
def exactPolynomial (start finish : Basic.Canonical)
  (polynomial : Rational.Basic.CoefficientPolynomial) :
    Basic.RefinementProgram := by
  let cell := Basic.CellModel.exact start finish polynomial
  let path : Basic.PathModel := ⟨[cell]⟩
  let sample := path.integralSample
  exact
    { model := fun _ => path
      errorScale := 0
      errorScale_nonneg := le_rfl
      modelAllowance_le := by
        intro index
        change 2 * (Basic.Canonical.normSq cell.displacement * 0 + 0) ≤
          Geometric.Basic.quarterRadius 0 index
        rw [Fraction.Field.mul_zero_direct,
          Fraction.Field.zero_add,
          Fraction.Field.mul_zero_direct,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Fraction.Field.zero_mul_direct]
      later_close := by
        intro earlier later order
        change Basic.Canonical.normSq (sample - sample) ≤
          Geometric.Basic.quarterRadius 0 earlier
        rw [_root_.sub_self, Basic.Canonical.normSq_zero,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Fraction.Field.zero_mul_direct]
      centerBound := Basic.Canonical.normSq sample
      centerBound_nonneg := Basic.Canonical.normSq_nonneg sample
      sample_bounded := by intro index; exact le_rfl }
end RefinementProgram

end Purelib.Integration.Program.Rational.Basic

end
