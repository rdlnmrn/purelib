module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Polynomial.Ascending.Rational.Basic
public import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation
public import Purelib.Polynomial.Ascending.Rational.Truncation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Polynomial.Ascending.Rational.Basic (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Low-to-high finite polynomials for transcendental identities

This is a deliberately small, executable polynomial kernel.  A polynomial is
only a displayed finite list of rational coefficients, stored from constant
term upward.  It exists to prove finite Taylor identities without importing a
sparse-polynomial or formal-power-series API.
-/

namespace Purelib.Polynomial.Ascending.Rational.GaussianEvaluation.Truncation

/-! ## Low prefix and high tail decomposition -/

/-- Evaluate at most the first `count` rational coefficients at a Gaussian argument.

Horner recursion stops at the count or the end of the finite table, whichever comes first. -/
def prefixEvalCoefficients (z :
  Gaussian.Basic.Canonical) :
    List Fraction.Rational → Nat → Gaussian.Basic.Canonical
  | _, 0 => 0
  | [], _ + 1 => 0
  | coefficient :: remaining, count + 1 =>
      Gaussian.Scale.scale coefficient 1 +
        z * prefixEvalCoefficients z remaining count

/-- Evaluate the low-degree prefix of the retained polynomial at a Gaussian argument. -/
def prefixEval (z : Gaussian.Basic.Canonical)
  (polynomial : CoefficientPolynomial) (count : Nat) :
    Gaussian.Basic.Canonical := prefixEvalCoefficients z
      polynomial.coefficients count

/-- Every prefix evaluation of an empty table is zero. -/
@[simp] theorem prefixEvalCoefficients_nil (z
  : Gaussian.Basic.Canonical) : ∀ count,
    prefixEvalCoefficients z [] count = 0
  | 0 => rfl
  | _ + 1 => rfl

/-- Split a Gaussian Horner value into its low prefix and shifted high tail.

The tail is the table after `count` entries and is multiplied by the argument to that count; the identity also covers
counts beyond the table length. -/
theorem evalCoefficients_split (z :
  Gaussian.Basic.Canonical) : ∀ coefficients count,
    Ascending.Rational.GaussianEvaluation.evalCoefficients z coefficients =
      prefixEvalCoefficients z coefficients count +
        z ^ count * Ascending.Rational.GaussianEvaluation.evalCoefficients z (coefficients.drop count)
  | coefficients, 0 => by
      rw [prefixEvalCoefficients, pow_zero, List.drop_zero]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1
  | [], count + 1 => by
      rw [Ascending.Rational.GaussianEvaluation.evalCoefficients,
        prefixEvalCoefficients, List.drop_nil,
        Ascending.Rational.GaussianEvaluation.evalCoefficients]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;> ring1
  | coefficient :: remaining, count + 1 => by
      rw [Ascending.Rational.GaussianEvaluation.evalCoefficients,
        prefixEvalCoefficients, List.drop_succ_cons,
        evalCoefficients_split z remaining count,
          pow_succ]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Split a polynomial value into its prefix value plus the argument power times its dropped-tail value. -/
theorem eval_split (z :
  Gaussian.Basic.Canonical) (polynomial : CoefficientPolynomial) (count : Nat) :
    Ascending.Rational.GaussianEvaluation.eval polynomial z =
      prefixEval z polynomial count +
        z ^ count * Ascending.Rational.GaussianEvaluation.eval ⟨polynomial.coefficients.drop count⟩ z :=
  evalCoefficients_split z polynomial.coefficients count

/-- Matching coefficients below the count give equal Gaussian prefix values.

The two retained tables may have different lengths, since missing coefficients are zero. -/
theorem prefixEvalCoefficients_congr (z :
  Gaussian.Basic.Canonical) :
    ∀ {left right : List Fraction.Rational} count,
      (∀ degree, degree < count →
        Ascending.Rational.Basic.coefficientCoefficients left degree =
          Ascending.Rational.Basic.coefficientCoefficients right degree) →
      prefixEvalCoefficients z left count =
        prefixEvalCoefficients z right count
  | left, right, 0, equal => by
      cases left <;> cases right <;> rfl
  | [], [], count + 1, equal => rfl
  | [], right :: rightTail, count + 1, equal => by
      have headZero : right = 0 := by
        have atZero := equal 0 (by omega)
        change 0 = right at atZero
        exact atZero.symm
      have tailEqual : ∀ degree, degree < count →
          Ascending.Rational.Basic.coefficientCoefficients [] degree =
            Ascending.Rational.Basic.coefficientCoefficients rightTail degree := by
        intro degree below
        exact equal (degree + 1) (by omega)
      subst right
      change 0 = Gaussian.Scale.scale 0 1 +
        z * prefixEvalCoefficients z rightTail count
      rw [← prefixEvalCoefficients_congr z count
        tailEqual]
      rw [prefixEvalCoefficients_nil]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1
  | left :: leftTail, [], count + 1, equal => by
      have headZero : left = 0 := equal 0 (by omega)
      have tailEqual : ∀ degree, degree < count →
          Ascending.Rational.Basic.coefficientCoefficients leftTail degree =
            Ascending.Rational.Basic.coefficientCoefficients [] degree := by
        intro degree below
        exact equal (degree + 1) (by omega)
      subst left
      change Gaussian.Scale.scale 0 1 +
        z * prefixEvalCoefficients z leftTail count = 0
      rw [prefixEvalCoefficients_congr z count
        tailEqual]
      rw [prefixEvalCoefficients_nil]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1
  | left :: leftTail, right :: rightTail, count + 1, equal => by
      have headEqual : left = right := equal 0 (by omega)
      have tailEqual : ∀ degree, degree < count →
          Ascending.Rational.Basic.coefficientCoefficients leftTail degree =
            Ascending.Rational.Basic.coefficientCoefficients rightTail degree := by
        intro degree below
        exact equal (degree + 1) (by omega)
      rw [prefixEvalCoefficients,
        prefixEvalCoefficients, headEqual,
        prefixEvalCoefficients_congr z count
          tailEqual]

/-- Polynomials equal below a degree bound have equal prefix evaluations at that bound. -/
theorem prefixEval_congr {count : Nat} {left
  right : CoefficientPolynomial}
    (equal : Ascending.Rational.Truncation.EqualBelow count left right) (z : Gaussian.Basic.Canonical) :
    prefixEval z left count =
      prefixEval z right count :=
  prefixEvalCoefficients_congr z count equal
end Purelib.Polynomial.Ascending.Rational.GaussianEvaluation.Truncation

end
