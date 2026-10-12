module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.RationalEmbedding

import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Finite exponential Horner approximation

This is a finite operational exponential on Gaussian rationals in the closed
unit disk.  `sample x n` evaluates exactly one finite Horner program.  The
pairwise theorem compares any two displayed truncations and supplies an
explicit rational squared-error sidecar.  Nothing in this module defines a
completed exponential value or invokes an infinite series or a limit.
-/

namespace Purelib.Data.Gaussian.Scale

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Multiply both rational coordinates of a canonical Gaussian by the supplied rational scalar. -/
def scale (a : Fraction.Rational) (z : Basic.Canonical) : Basic.Canonical :=
  ⟨a * z.re, a * z.im⟩

/-- The real coordinate of rational Gaussian scaling is the scaled real coordinate. -/
@[simp] theorem scale_re (a : Fraction.Rational) (z : Basic.Canonical) :
    (scale a z).re = a * z.re := rfl

/-- The imaginary coordinate of rational Gaussian scaling is the scaled imaginary coordinate. -/
@[simp] theorem scale_im (a : Fraction.Rational) (z : Basic.Canonical) :
    (scale a z).im = a * z.im := rfl

/-- Rational coordinate scaling multiplies Gaussian squared norm by the square of the scalar. -/
theorem normSq_scale (a : Fraction.Rational) (z : Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (scale a z) = a ^ 2 * Data.Gaussian.Norm.Basic.normSq z := by
  simp only [Data.Gaussian.Norm.Basic.normSq, scale_re, scale_im]
  ring1
end Purelib.Data.Gaussian.Scale

end

section
@[expose] public section

/-!
# Finite divided differences and limit-free algebraic calculus

The derivative in this module is obtained by constructing a secant kernel
before putting its two displayed arguments equal.  No quotient by `x-y`,
limit, infinitesimal, or completed function graph is used.  Ordinary finite
polynomials, signed powers, and finite Laurent term lists are all evaluated by
structural recursion.
-/

namespace Purelib.Data.Gaussian.Scale

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Scaling a Gaussian product is the product with the left factor scaled. -/
public theorem scale_mul_product (factor : Fraction.Rational)
    (left right : Basic.Canonical) :
    scale factor (left * right) =
      scale factor left * right := by
  apply Basic.ext <;>
    simp only [scale_re,
      scale_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Rational coordinate scaling preserves Gaussian subtraction. -/
public theorem scale_sub (factor : Fraction.Rational) (left right : Basic.Canonical)
  :
    scale factor (left - right) =
      scale factor left -
        scale factor right := by
  apply Basic.ext <;>
    simp only [scale_re,
      scale_im, Basic.sub_re, Basic.sub_im] <;> ring1

/-- Scaling a Gaussian product is the product with its right factor scaled. -/
public theorem scale_mul_right (factor : Fraction.Rational)
    (left right : Basic.Canonical) :
    scale factor (left * right) =
      left * scale factor right := by
  apply Basic.ext <;>
    simp only [scale_re,
      scale_im, Basic.mul_re, Basic.mul_im] <;> ring1

end Purelib.Data.Gaussian.Scale

end

section
@[expose] public section

/-!
# Executable, limit-free differential laws for the logarithm

This module works with the finite local coordinate `log(1+u)`, on the
displayed rational disk `normSq u ≤ 1/4`.  Its relative forms and derivative
are finite alternating sums.  The reciprocal derivative law is expressed by
an exact finite geometric remainder and then by finite-request operational
equivalence.  No infinitesimal, limit, infinite series, or global logarithm
branch is introduced.
-/

namespace Purelib.Data.Gaussian.Scale

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Multiplying by a scaled right factor equals scaling the full Gaussian product. -/
public theorem mul_scale (u v : Basic.Canonical) (coefficient : Fraction.Rational) :
    u * scale coefficient v =
      scale coefficient (u * v) := by
  apply Basic.ext <;>
    simp only [scale_re,
      scale_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Two successive coordinate scalings combine by multiplying the rational scalars. -/
public theorem scale_scale (left right : Fraction.Rational) (u : Basic.Canonical) :
    scale left
        (scale right u) =
      scale (left * right) u := by
  apply Basic.ext <;>
    simp only [scale_re,
      scale_im] <;> ring1

end Purelib.Data.Gaussian.Scale

end

section
@[expose] public section

/-!
# Embedding finite rational coefficient tables in Gaussian polynomials

This is a structural map on finite lists, with evaluation, differentiation
and integration compatibility proved from the coefficient recursions.  It
does not identify polynomials by testing them on an infinite carrier.

The rational-side imports supply the existing finite coefficient calculus;
the Gaussian side supplies direct coefficient algebra.  No analytic
polynomial or completed scalar field is used.
-/

namespace Purelib.Data.Gaussian.Scale

section RationalEmbedding

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original rational coordinate embedding equals scaling Gaussian one. -/
theorem coordinate_scale_one (value : Fraction.Rational) :
    RationalEmbedding.PolynomialEmbedding.coordinate value = scale value 1 := by
  apply Basic.ext <;>
    simp only [RationalEmbedding.PolynomialEmbedding.coordinate, scale_re, scale_im,
      Basic.one_re,
      Basic.one_im] <;> ring1
end RationalEmbedding
end Purelib.Data.Gaussian.Scale

end

section
@[expose] public section

/-!
# Finite operational laws for transcendental CCL programs

This module begins the analytic identification layer without adjoining a
completed non-rational value.  Laws compare finite approximation programs:
from any current indices and any positive displayed rational tolerance they
compute synchronized later indices whose entire displayed tails agree to that
tolerance.

The exponential addition law will be proved here by a finite polynomial
Cauchy-product identity followed by explicit rational remainder bounds.  The
normalization law `exp(0) = 1` is already exact at every finite Horner depth.
-/

namespace Purelib.Data.Gaussian.Scale

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- The product of two scaled Gaussians is their product scaled by the product of the two scalars. -/
public theorem scale_mul_scale (left right : Fraction.Rational) (x y :
  Basic.Canonical) :
    scale left x *
        scale right y =
      scale (left * right) (x * y) := by
  apply Basic.ext <;>
    simp only [scale_re,
      scale_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- Multiplication by the retained real scalar embedding equals coordinate scaling. -/
public theorem scalar_mul_eq_scale (factor : Fraction.Rational) (value :
  Basic.Canonical) :
    RationalEmbedding.ComplexLog.scalar factor * value =
      scale factor value := by
  apply Basic.ext <;>
    simp only [RationalEmbedding.ComplexLog.scalar,
      scale_re,
      scale_im, Basic.mul_re, Basic.mul_im] <;> ring1

end Purelib.Data.Gaussian.Scale

end

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Data.Gaussian.Scale

open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Embedding a rational sum by scaling one is the sum of the two scaled copies of one. -/
public theorem scale_one_add (left right : Fraction.Rational) :
    scale (left + right) (1 : Basic.Canonical) =
      scale left 1 +
        scale right 1 := by
  apply Basic.ext <;>
    simp only [scale_re,
      scale_im, Basic.add_re, Basic.add_im, Basic.one_re, Basic.one_im] <;>
    ring1

/-- Scaling one by a rational product equals successive scaling by the two factors. -/
public theorem scale_one_mul (factor coefficient : Fraction.Rational) :
    scale (factor * coefficient) (1 : Basic.Canonical) =
      scale factor
        (scale coefficient 1) := by
  apply Basic.ext <;>
    simp only [scale_re,
      scale_im, Basic.one_re, Basic.one_im] <;> ring1

/-- Rational coordinate scaling preserves Gaussian addition. -/
private theorem scale_add (factor : Fraction.Rational) (left right : Basic.Canonical)
  :
    scale factor (left + right) =
      scale factor left +
        scale factor right := by
  apply Basic.ext <;>
    simp only [scale_re,
      scale_im, Basic.add_re, Basic.add_im] <;> ring1

/-- Scaling a Gaussian product agrees with scaling its left factor before multiplication. -/
private theorem scale_mul_left (factor : Fraction.Rational)
    (left right : Basic.Canonical) :
    scale factor (left * right) =
      scale factor left * right := by
  apply Basic.ext <;>
    simp only [scale_re,
      scale_im, Basic.mul_re, Basic.mul_im] <;> ring1
end Purelib.Data.Gaussian.Scale

end
