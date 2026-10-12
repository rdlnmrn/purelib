module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Constants
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Choice-free global winding on a finite constructive square

This module develops the coefficient-computed large-square theorem entirely
over the explicit constructive fraction and Gaussian representations.  Its
first layer computes the winding of the coordinate polynomial symbolically;
later layers transfer that value to a general positive-degree polynomial.
-/

namespace Purelib.RootIsolation.Winding.Global

end Purelib.RootIsolation.Winding.Global

section
namespace Purelib.Polynomial.Dense.Gaussian.Path.Constant

open _root_.Purelib.RootIsolation.Winding.Global
/-- Affine substitution preserves the normalized singleton representation of a nonzero Gaussian constant. -/
private theorem composeLine_gaussianConstant_of_ne
    (c origin direction : Gaussian.Basic.Canonical) (nonzero : c ≠ 0) :
    Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.composeLine (Dense.Gaussian.Constants.gaussianConstant c)
      origin direction = DensePolynomial.constant c := by
  rw [Dense.Gaussian.Substitution.Affine.composeLine, Dense.Gaussian.Substitution.Affine.composeLineCoeffs]
  simp only [Dense.Gaussian.Constants.gaussianConstant, DensePolynomial.constant_coeffs, List.foldl_cons,
    List.foldl_nil]
  rw [Dense.Gaussian.Substitution.Affine.mulLine_zero, DensePolynomial.zero_add_normalize,
    DensePolynomial.normalize_constant_of_ne nonzero]
/-- The real path component of a Gaussian constant is its constant rational coordinate polynomial. -/
public theorem gaussianConstant_pathReal
    (c origin direction : Gaussian.Basic.Canonical) (nonzero : c ≠ 0) :
    Dense.Gaussian.Path.Components.pathReal (Dense.Gaussian.Constants.gaussianConstant c) origin direction =
      DensePolynomial.constant c.re := by
  rw [Dense.Gaussian.Path.Components.pathReal,
    composeLine_gaussianConstant_of_ne c origin direction nonzero]
  rfl
/-- The imag path component of a Gaussian constant is its constant rational coordinate polynomial. -/
public theorem gaussianConstant_pathImag
    (c origin direction : Gaussian.Basic.Canonical) (nonzero : c ≠ 0) :
    Dense.Gaussian.Path.Components.pathImag (Dense.Gaussian.Constants.gaussianConstant c) origin direction =
      DensePolynomial.constant c.im := by
  rw [Dense.Gaussian.Path.Components.pathImag,
    composeLine_gaussianConstant_of_ne c origin direction nonzero]
  rfl
end Purelib.Polynomial.Dense.Gaussian.Path.Constant
end

namespace Purelib.RootIsolation.Winding.Global

end Purelib.RootIsolation.Winding.Global

end
