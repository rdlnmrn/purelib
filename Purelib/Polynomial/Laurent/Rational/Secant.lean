module
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Algebra.Power.Gaussian.Signed.Secant
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Polynomial.Laurent.Rational.Basic
public import Purelib.Polynomial.Laurent.Rational.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data
open Purelib.Data.Gaussian.Norm.Sum.Basic
open Purelib.Algebra.Power.Gaussian

section
public section

/-!
# Finite rational Laurent secant factorizations

The signed-power secant kernels extend through rational coefficient scaling
and finite Gaussian summation. At nonzero evaluation points they factor
Laurent value differences; on the diagonal they equal the original termwise
formal derivative evaluations.
-/

namespace Purelib.Polynomial.Laurent.Rational

namespace Basic.LaurentTerm

/-- Factor a Laurent term's value difference through its finite secant kernel.

Both evaluation points must be nonzero to support signed powers. -/
theorem eval_sub_factor (term : Basic.LaurentTerm) (x y : Gaussian.Basic.Canonical)
    (xNonzero : x ≠ 0) (yNonzero : y ≠ 0) :
    term.eval x - term.eval y = (x - y) * term.kernel x y := by
  simp only [Basic.LaurentTerm.eval, Basic.LaurentTerm.kernel]
  rw [← Gaussian.Scale.scale_sub]
  rw [Signed.Secant.signedPower_sub_factor x y xNonzero yNonzero term.exponent]
  exact Gaussian.Scale.scale_mul_right term.coefficient (x - y)
    (Signed.Secant.signedPowerKernel x y term.exponent)

/-- The Laurent term's kernel on the diagonal equals its derivative evaluation.

The evaluation point must be nonzero, including for negative exponents. -/
theorem kernel_diagonal (term : Basic.LaurentTerm) (x : Gaussian.Basic.Canonical)
    (xNonzero : x ≠ 0) :
    term.kernel x x = term.derivativeEval x := by
  rewrite [Basic.LaurentTerm.kernel, Basic.LaurentTerm.derivativeEval,
    Signed.Secant.signedPowerKernel_diagonal x xNonzero term.exponent]
  rfl

end Basic.LaurentTerm

namespace Secant

/-- Sum the secant factorization over a finite list of Laurent terms.

Both Gaussian-rational evaluation points are nonzero. -/
private theorem sumGaussian_sub_factor (x y : Gaussian.Basic.Canonical)
    (xNonzero : x ≠ 0) (yNonzero : y ≠ 0) :
    ∀ terms : List Basic.LaurentTerm,
      DividedDifference.sumGaussian (terms.map fun term => term.eval x) -
          DividedDifference.sumGaussian (terms.map fun term => term.eval y) =
        (x - y) *
          DividedDifference.sumGaussian (terms.map fun term => term.kernel x y)
  | [] => by
      change (0 : Gaussian.Basic.Canonical) - 0 = (x - y) * 0
      rewrite [Gaussian.Basic.sub_self, Gaussian.Basic.mul_zero]
      rfl
  | term :: remaining => by
      rw [List.map_cons, List.map_cons, List.map_cons,
        DividedDifference.sumGaussian, DividedDifference.sumGaussian, DividedDifference.sumGaussian]
      calc
        (term.eval x +
              DividedDifference.sumGaussian (remaining.map fun next => next.eval x)) -
            (term.eval y +
              DividedDifference.sumGaussian (remaining.map fun next => next.eval y)) =
            (term.eval x - term.eval y) +
              (DividedDifference.sumGaussian (remaining.map fun next => next.eval x) -
                DividedDifference.sumGaussian (remaining.map fun next => next.eval y)) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;>
            ring1
        _ = (x - y) * term.kernel x y +
            (x - y) *
              DividedDifference.sumGaussian (remaining.map fun next => next.kernel x y) := by
          rw [Basic.LaurentTerm.eval_sub_factor term x y xNonzero yNonzero,
            Purelib.Polynomial.Laurent.Rational.Secant.sumGaussian_sub_factor x y xNonzero yNonzero remaining]
        _ = (x - y) *
            (term.kernel x y +
              DividedDifference.sumGaussian (remaining.map fun next => next.kernel x y)) := by
          apply Gaussian.Basic.ext <;>
            simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
              Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;>
            ring1

end Secant

namespace Basic.LaurentPolynomial

/-- Linear extension of the signed-power factorization to every displayed
finite Laurent term list. -/
theorem eval_sub_factor
    (polynomial : Basic.LaurentPolynomial) (x y : Gaussian.Basic.Canonical)
    (xNonzero : x ≠ 0) (yNonzero : y ≠ 0) :
    polynomial.eval x - polynomial.eval y =
      (x - y) * polynomial.kernel x y :=
  Secant.sumGaussian_sub_factor x y xNonzero yNonzero polynomial.terms

end Basic.LaurentPolynomial

namespace Secant

/-- The summed diagonal kernel equals the summed derivative evaluations.

The identity follows the original finite term list at a nonzero point. -/
private theorem sumGaussian_kernel_diagonal (x : Gaussian.Basic.Canonical)
    (xNonzero : x ≠ 0) : ∀ terms : List Basic.LaurentTerm,
    DividedDifference.sumGaussian (terms.map fun term => term.kernel x x) =
      DividedDifference.sumGaussian (terms.map fun term => term.derivativeEval x)
  | [] => rfl
  | term :: remaining => by
      rw [List.map_cons, List.map_cons, DividedDifference.sumGaussian, DividedDifference.sumGaussian,
        Basic.LaurentTerm.kernel_diagonal term x xNonzero,
        Purelib.Polynomial.Laurent.Rational.Secant.sumGaussian_kernel_diagonal x xNonzero remaining]

end Secant

namespace Basic.LaurentPolynomial

/-- Diagonal evaluation of a finite Laurent secant kernel is its executable
termwise derivative, including all negative exponents. -/
theorem kernel_diagonal
    (polynomial : Basic.LaurentPolynomial) (x : Gaussian.Basic.Canonical) (xNonzero : x ≠ 0) :
    polynomial.kernel x x = polynomial.derivativeEval x :=
  Secant.sumGaussian_kernel_diagonal x xNonzero polynomial.terms

end Basic.LaurentPolynomial

end Purelib.Polynomial.Laurent.Rational

end
