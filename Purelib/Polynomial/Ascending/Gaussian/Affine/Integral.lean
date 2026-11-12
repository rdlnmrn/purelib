module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Antiderivative
import Purelib.Polynomial.Ascending.Gaussian.Arithmetic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Derivative
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
public import Purelib.Polynomial.Ascending.Gaussian.Integral

public import Purelib.Polynomial.Ascending.Gaussian.Affine
import Purelib.Polynomial.Ascending.Gaussian.Affine.Derivative

open Purelib.Data

open Purelib.Polynomial

@[expose] public section

/-!
# Generated affine transport of finite Gaussian polynomials

Substitution is finite Horner coefficient arithmetic.  Its derivative and
integral laws are proved here, not supplied in a transport certificate.  The
integral law includes zero slope and reversed segments without dividing by
the path displacement.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Affine.Integral

open Purelib.Data.Gaussian.Basic.Canonical

/-- Finite substitution, including slope zero: no division by the affine
slope and no supplied change-of-variables certificate. -/
theorem definiteIntegral_affine (polynomial :
  CoefficientPolynomial)
    (offset slope start finish : Gaussian.Basic.Canonical) :
    slope * Integral.definiteIntegral (affine polynomial offset slope)
      start finish =
      Integral.definiteIntegral polynomial (offset + slope * start) (offset + slope * finish) := by
  have primitiveDerivative := Derivative.derivative_affine
    (Antiderivative.antiderivative polynomial) offset slope
  rw [Antiderivative.derivative_antiderivative] at primitiveDerivative
  calc
    slope * Integral.definiteIntegral (affine polynomial offset slope)
      start finish =
        Integral.definiteIntegral (Arithmetic.scale slope
          (affine polynomial offset slope)) start finish :=
      (Integral.definiteIntegral_scale slope _ start finish).symm
    _ = Integral.definiteIntegral (Derivative.derivative
      (affine (Antiderivative.antiderivative polynomial) offset slope))
        start finish :=
      (Integral.definiteIntegral_eq_of_coefficientwise primitiveDerivative start finish).symm
    _ = Evaluation.eval (affine
      (Antiderivative.antiderivative polynomial) offset slope) finish -
        Evaluation.eval (affine
          (Antiderivative.antiderivative polynomial) offset slope) start :=
      Integral.definiteIntegral_derivative _ start finish
    _ = Integral.definiteIntegral polynomial (offset + slope * start) (offset + slope * finish) := by
      rw [eval_affine, eval_affine]
      rfl
section
end

end Purelib.Polynomial.Ascending.Gaussian.Affine.Integral

end
