module
public import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Checked replay of bounded Newton proposal traces

Saved integer grid coordinates are checked by multiplication and inequalities;
saved Newton updates are checked by multiplication.  Replay does not call the
floor or Newton proposal generators.  The starting proposal is explicit, so
diameter preparation can supply its checked warm-up result while ordinary
refinement supplies the box midpoint.  The existing finite candidate acceptance
check is retained, including its safe-side selection and winding.
All imports are already audited finite dependencies of checked shrinking.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Newton.Check.Product

/-- A candidate satisfying the Newton correction product is the exact normalized Newton center.

The derivative at the retained center must be nonzero; cancellation then identifies the candidate with the
quotient-defined update. -/
theorem newton_eq_of_product (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
    (center next : Gaussian.Basic.Canonical)
    (nonzero : (Dense.Derivative.derivative polynomial).eval center ≠ 0)
    (product : (center - next) * (Dense.Derivative.derivative polynomial).eval center =
      polynomial.eval center) :
    next = Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter polynomial center) := open
      Purelib.Algebra.Field in by
  rw [Dense.Gaussian.Newton.Basic.value_newtonCenter]
  have quotient : center - next = polynomial.eval center /
      (Dense.Derivative.derivative polynomial).eval center := by
    apply Gaussian.Basic.Canonical.mul_right_cancel_of_nonzero nonzero
    rw [ExplicitField.div_mul_cancel _ nonzero]
    exact product
  rw [← quotient]
  ring1

end Purelib.Polynomial.Dense.Gaussian.Newton.Check.Product

end
