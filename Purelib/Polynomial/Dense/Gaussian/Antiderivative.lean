module
import Purelib.Data.List.Reverse
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Antiderivative
import Purelib.Polynomial.Ascending.Gaussian.Dense.Antiderivative
public import Purelib.Polynomial.Ascending.Gaussian.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite antiderivatives of dense Gaussian polynomials

Connect the existing low-to-high polynomial integrator to the dense
high-to-low polynomial algebra.  The derivative identity is proved by finite
Horner induction.  The existing finite Taylor estimate then bounds local
primitive increments, without analytic limits or infinite series.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Antiderivative

/-- Reverse once into the existing coefficient integrator and once back
into dense form.  Downstream users can cache this polynomial directly. -/
def denseAntiderivative (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) : (Dense.Basic.DensePolynomial
    Gaussian.Basic.Canonical) :=
  Ascending.Gaussian.Dense.Evaluation.toDense (Ascending.Gaussian.Antiderivative.antiderivative
    ⟨polynomial.coeffs.reverse⟩)

open Purelib.Data.List in
/-- The formal derivative of the finite dense antiderivative evaluates to the original polynomial.

The original reversed coefficient list is integrated once and converted back to dense order. Its finite derivative
certificate and reversal identity recover the same polynomial evaluation. -/
theorem denseAntiderivative_derivative (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (point : Gaussian.Basic.Canonical) :
    (Dense.Gaussian.GCD.derivative (denseAntiderivative polynomial)).eval point =
      polynomial.eval point := by
  rw [denseAntiderivative,
    Ascending.Gaussian.Dense.Antiderivative.toDense_antiderivative_derivative, <-
    Ascending.Gaussian.Dense.Evaluation.toDense_eval]
  simp only [Ascending.Gaussian.Dense.Evaluation.toDense,
    Reverse.reverse_reverse, -eq_self, -iff_self]
  rfl

end Purelib.Polynomial.Dense.Gaussian.Antiderivative

end
