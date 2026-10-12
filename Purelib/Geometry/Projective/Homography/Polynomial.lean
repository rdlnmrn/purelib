module
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
public import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic

open Purelib

open Purelib.Geometry.Projective

open Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib.Polynomial

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense

section
@[expose] public section

/-!
# Bounded finite charts for CCL branch boundaries

Circle boundaries use the primary and reciprocal stereographic charts on the
fixed rational cell `[-1,1]`.  Coordinate-line boundaries use one symmetric
cell whose radius is computed from a coefficient majorant for the affine
numerator and an explicitly supplied positive lower bound for the affine
denominator.  Each chart is immediately sent through the finite cleared-gcd
and Sturm event classifier.
-/

namespace Purelib.Geometry.Projective.Homography

/-- The affine numerator `a*z+b` as a finite dense Gaussian polynomial. -/
def affineNumeratorPolynomial (matrix :
  GaussianMatrix) : Dense.Gaussian.Basic.GaussianPolynomial :=
  ⟨[matrix.a, matrix.b]⟩

/-- Evaluating the dense numerator polynomial gives the affine numerator.

The original two-coefficient Horner fold reads the same matrix entries and affine scalar used by the homography
numerator. -/
@[simp] theorem eval_affineNumeratorPolynomial
    (matrix : GaussianMatrix) (value : Data.Gaussian.Basic.Canonical) :
    (affineNumeratorPolynomial matrix).eval value =
      Homography.Basic.numerator matrix value := by
  simp only [affineNumeratorPolynomial,
    DensePolynomial.eval, DensePolynomial.evalCoeffs, Homography.Basic.numerator,
    List.foldl_cons, List.foldl_nil, Data.Gaussian.Basic.zero_mul, Data.Gaussian.Basic.zero_add, -eq_self, -iff_self]
  rfl
end Purelib.Geometry.Projective.Homography

end
