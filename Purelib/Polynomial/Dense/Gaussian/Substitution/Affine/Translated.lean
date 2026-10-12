module

-- Both public substitution inputs retain their original owner and exposed bodies.
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
public import Purelib.Polynomial.Dense.Gaussian.Substitution.Affine
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Multiplication

/-!
# Affine substitution of translated Gaussian coordinates

The retained affine substitution into `[1, -center]` normalizes to the original
direction and translated origin. A nonzero direction retains both slots.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.Translated

open Purelib.Data
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Substitution

/-- Substituting an affine line into a translated coordinate retains its direction and translated origin.

The nonzero direction preserves the exact two-coefficient normalized linear
representation, with the same supplied origin, direction and center. -/
public theorem composeLine_translatedCoordinate
    (c origin direction : Gaussian.Basic.Canonical) (directionNonzero : direction ≠ 0) :
    Affine.composeLine (Linear.Translated.translatedCoordinate c) origin direction =
      ⟨[direction, origin - c]⟩ := by
  have mulLineOne : Affine.mulLine origin direction (DensePolynomial.constant 1) =
      ⟨[direction, origin]⟩ := by
    rw [Affine.mulLine, DensePolynomial.scale_constant, DensePolynomial.scale_constant,
      Gaussian.Basic.mul_one,
      Gaussian.Basic.mul_one,
      DensePolynomial.normalize_constant_of_ne directionNonzero,
      DensePolynomial.shift_one_constant_of_ne directionNonzero]
    by_cases originZero : origin = 0
    · subst origin
      rw [DensePolynomial.normalize_constant_zero, DensePolynomial.zero_add_normalize,
        DensePolynomial.normalize_linear_of_leading_ne_zero directionNonzero]
    · rw [DensePolynomial.normalize_constant_of_ne originZero,
        DensePolynomial.constant_add_linear origin directionNonzero]
  rw [Affine.composeLine, Affine.composeLineCoeffs]
  simp only [Linear.Translated.translatedCoordinate, List.foldl_cons, List.foldl_nil]
  rw [Affine.mulLine_zero, DensePolynomial.zero_add_normalize,
    DensePolynomial.normalize_constant_of_ne (Ne.symm Gaussian.Basic.Canonical.zero_ne_one), mulLineOne,
    DensePolynomial.linear_add_constant origin (-c) directionNonzero]
  apply DensePolynomial.ext
  rewrite [Gaussian.Basic.Canonical.sub_eq_add_neg]
  exact Eq.refl _

end Purelib.Polynomial.Dense.Gaussian.Substitution.Affine.Translated
