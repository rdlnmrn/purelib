module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
public import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
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

namespace Purelib.Integration.Program.Gaussian.Basic
namespace RefinementProgram

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Integration.Program in
open Purelib.Polynomial.Ascending in
/-- Construct the constant refinement program for the exact original Gaussian polynomial segment.

Every stage reuses its single exact cell and path sample, with zero error scale and allowance and the exact sample
squared norm as center bound. -/
def exactPolynomial (start finish : Basic.Canonical)
  (polynomial : Polynomial.Ascending.Gaussian.CoefficientPolynomial) :
    Gaussian.Basic.RefinementProgram := by
  let cell := Basic.CellModel.exact start finish polynomial
  let path : Basic.PathModel := ⟨[cell]⟩
  let sample := path.integralSample
  exact
    { model := fun _ => path
      errorScale := 0
      errorScale_nonneg := le_rfl
      modelAllowance_le := by
        intro index
        change (1 : Fraction.Rational) * (Basic.Canonical.normSq cell.displacement * 0 + 0) <=
          Geometric.Basic.quarterRadius 0 index
        rw [Fraction.Field.mul_zero_direct,
          Fraction.Field.zero_add,
          Fraction.Field.mul_zero_direct,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Fraction.Field.zero_mul_direct]
      later_close := by
        intro earlier later order
        change Basic.Canonical.normSq (sample - sample) <=
          Geometric.Basic.quarterRadius 0 earlier
        rw [Basic.sub_self, Basic.Canonical.normSq_zero,
          Geometric.Basic.quarterRadius_eq_mul_pow,
          Fraction.Field.zero_mul_direct]
      centerBound := Basic.Canonical.normSq sample
      centerBound_nonneg := Basic.Canonical.normSq_nonneg sample
      sample_bounded := by intro index; exact le_rfl }
end RefinementProgram

end Purelib.Integration.Program.Gaussian.Basic

end
