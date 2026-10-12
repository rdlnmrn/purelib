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
  Polynomial.Ascending.Gaussian.CoefficientPolynomial)
    (offset slope start finish : Gaussian.Basic.Canonical) :
    slope * Ascending.Gaussian.Integral.definiteIntegral (Ascending.Gaussian.Affine.affine polynomial offset slope)
      start finish =
      Ascending.Gaussian.Integral.definiteIntegral polynomial (offset + slope * start) (offset + slope * finish) := by
  have primitiveDerivative := Ascending.Gaussian.Affine.Derivative.derivative_affine
    (Ascending.Gaussian.Antiderivative.antiderivative polynomial) offset slope
  rw [Ascending.Gaussian.Antiderivative.derivative_antiderivative] at primitiveDerivative
  calc
    slope * Ascending.Gaussian.Integral.definiteIntegral (Ascending.Gaussian.Affine.affine polynomial offset slope)
      start finish =
        Ascending.Gaussian.Integral.definiteIntegral (Ascending.Gaussian.Arithmetic.scale slope
          (Ascending.Gaussian.Affine.affine polynomial offset slope)) start finish :=
      (Ascending.Gaussian.Integral.definiteIntegral_scale slope _ start finish).symm
    _ = Ascending.Gaussian.Integral.definiteIntegral (Ascending.Gaussian.Derivative.derivative
      (Ascending.Gaussian.Affine.affine (Ascending.Gaussian.Antiderivative.antiderivative polynomial) offset slope))
        start finish :=
      (Ascending.Gaussian.Integral.definiteIntegral_eq_of_coefficientwise primitiveDerivative start finish).symm
    _ = Ascending.Gaussian.Evaluation.eval (Ascending.Gaussian.Affine.affine
      (Ascending.Gaussian.Antiderivative.antiderivative polynomial) offset slope) finish -
        Ascending.Gaussian.Evaluation.eval (Ascending.Gaussian.Affine.affine
          (Ascending.Gaussian.Antiderivative.antiderivative polynomial) offset slope) start :=
      Ascending.Gaussian.Integral.definiteIntegral_derivative _ start finish
    _ = Ascending.Gaussian.Integral.definiteIntegral polynomial (offset + slope * start) (offset + slope * finish) := by
      rw [Ascending.Gaussian.Affine.eval_affine, Ascending.Gaussian.Affine.eval_affine]
      rfl
section
end

end Purelib.Polynomial.Ascending.Gaussian.Affine.Integral

end
