module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.RationalEmbedding
public import Purelib.Data.Gaussian.Scale
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
public import Purelib.Polynomial.Ascending.Rational.Evaluation
import Purelib.Polynomial.Ascending.Rational.Monomial

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
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

namespace Purelib.Polynomial.Ascending.Rational.GaussianEvaluation

/-- Evaluate an ascending rational coefficient list at a Gaussian rational by Horner recursion.

Each coefficient is embedded on the real axis before adding the argument times the tail value. -/
def evalCoefficients (z : Gaussian.Basic.Canonical) :
  List Fraction.Rational → Gaussian.Basic.Canonical
  | [] => 0
  | coefficient :: remaining =>
      Gaussian.Scale.scale coefficient 1 +
        z * evalCoefficients z remaining

/-- Evaluate the retained rational polynomial at a Gaussian rational argument. -/
def eval (polynomial :
  CoefficientPolynomial) (z : Gaussian.Basic.Canonical) : Gaussian.Basic.Canonical :=
  evalCoefficients z polynomial.coefficients

/-- The empty coefficient table evaluates to Gaussian zero. -/
@[simp] theorem evalCoefficients_nil (z :
  Gaussian.Basic.Canonical) :
    evalCoefficients z [] = 0 := rfl

/-- A nonempty table evaluates as its embedded head plus the argument times the tail value. -/
@[simp] theorem evalCoefficients_cons (z :
  Gaussian.Basic.Canonical) (head : Fraction.Rational)
    (tail : List Fraction.Rational) :
    evalCoefficients z (head :: tail) =
      Gaussian.Scale.scale head 1 +
        z * evalCoefficients z tail := rfl

/-- Gaussian evaluation preserves padded addition of rational coefficient lists. -/
theorem eval_addCoefficients (z :
  Gaussian.Basic.Canonical) : ∀ left right,
    evalCoefficients z (Ascending.Rational.Basic.addCoefficients left right) =
      evalCoefficients z left +
        evalCoefficients z right
  | [], right => by
      apply Gaussian.Basic.ext <;>
        simp only [Ascending.Rational.Basic.addCoefficients, evalCoefficients,
          Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;> ring1
  | left, [] => by
      rw [Ascending.Rational.Basic.addCoefficients_nil_right]
      apply Gaussian.Basic.ext <;>
        simp only [evalCoefficients, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;> ring1
  | left :: leftTail, right :: rightTail => by
      rw [Ascending.Rational.Basic.addCoefficients, evalCoefficients,
        evalCoefficients,
        evalCoefficients, Gaussian.Scale.scale_one_add,
        eval_addCoefficients z leftTail rightTail]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

/-- Gaussian evaluation preserves polynomial addition. -/
@[simp] theorem eval_add (left right :
  CoefficientPolynomial) (z : Gaussian.Basic.Canonical) :
    eval (Ascending.Rational.Basic.add left right) z =
      eval left z + eval right z :=
  eval_addCoefficients z left.coefficients right.coefficients

/-- A table coefficientwise equal to the empty table evaluates to Gaussian zero.

Structural recursion eliminates its zero head and zero tail without identifying lists of different lengths. -/
private theorem
  evalCoefficients_eq_nil_of_coefficients_eq (z :
  Gaussian.Basic.Canonical) :
    ∀ (right : List Fraction.Rational),
      (∀ degree,
        Ascending.Rational.Basic.coefficientCoefficients [] degree =
          Ascending.Rational.Basic.coefficientCoefficients right degree) →
      evalCoefficients z [] =
        evalCoefficients z right
  | [], _ => rfl
  | right :: rightTail, equal => by
      have headZero : right = 0 := (equal 0).symm
      have tailEqual : ∀ degree,
          Ascending.Rational.Basic.coefficientCoefficients [] degree =
            Ascending.Rational.Basic.coefficientCoefficients rightTail degree := by
        intro degree
        exact equal (degree + 1)
      subst right
      have tailEval :=
        evalCoefficients_eq_nil_of_coefficients_eq z rightTail
          tailEqual
      rw [evalCoefficients,
        evalCoefficients, ← tailEval,
        evalCoefficients]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1

/-- Equal displayed coefficients give equal finite Horner evaluations.  The
proof follows the two finite coefficient lists directly; in particular, it
does not infer polynomial equality from values across Gaussian rationals. -/
theorem evalCoefficients_eq_of_coefficients_eq (z :
  Gaussian.Basic.Canonical) :
    ∀ (left right : List Fraction.Rational),
      (∀ degree,
        Ascending.Rational.Basic.coefficientCoefficients left degree =
          Ascending.Rational.Basic.coefficientCoefficients right degree) →
      evalCoefficients z left =
        evalCoefficients z right
  | [], right, equal =>
      evalCoefficients_eq_nil_of_coefficients_eq z right equal
  | left :: leftTail, [], equal => by
      have headZero : left = 0 := equal 0
      have tailEqual : ∀ degree,
          Ascending.Rational.Basic.coefficientCoefficients leftTail degree =
            Ascending.Rational.Basic.coefficientCoefficients [] degree := by
        intro degree
        exact equal (degree + 1)
      subst left
      have tailEval :=
        evalCoefficients_eq_of_coefficients_eq z leftTail []
          tailEqual
      rw [evalCoefficients,
        evalCoefficients, tailEval,
        evalCoefficients]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1
  | left :: leftTail, right :: rightTail, equal => by
      have headEqual : left = right := equal 0
      have tailEqual : ∀ degree,
          Ascending.Rational.Basic.coefficientCoefficients leftTail degree =
            Ascending.Rational.Basic.coefficientCoefficients rightTail degree := by
        intro degree
        exact equal (degree + 1)
      rw [evalCoefficients,
        evalCoefficients, headEqual,
        evalCoefficients_eq_of_coefficients_eq z leftTail
          rightTail tailEqual]

/-- Coefficientwise equal rational polynomials have equal Gaussian evaluations. -/
theorem eval_eq_of_coefficientwise {left right :
  CoefficientPolynomial}
    (equal : Ascending.Rational.Coefficientwise.CoefficientwiseEqual left right) (z : Gaussian.Basic.Canonical) :
    eval left z = eval right z :=
  evalCoefficients_eq_of_coefficients_eq z left.coefficients
    right.coefficients equal

/-- Scaling every rational coefficient scales the Gaussian Horner value. -/
theorem evalCoefficients_map_scale (factor :
  Fraction.Rational) (z : Gaussian.Basic.Canonical) :
    ∀ coefficients,
      evalCoefficients z (coefficients.map (factor * ·)) =
        Gaussian.Scale.scale factor
          (evalCoefficients z coefficients)
  | [] => by
      apply Gaussian.Basic.ext <;>
        simp only [List.map, evalCoefficients,
          Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;> ring1
  | coefficient :: remaining => by
      rw [List.map, evalCoefficients,
        evalCoefficients,
        Gaussian.Scale.scale_one_mul,
          evalCoefficients_map_scale factor z remaining]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
        ring1

/-- Gaussian evaluation commutes with rational scaling. -/
@[simp] theorem eval_scale (factor : Fraction.Rational)
  (polynomial : CoefficientPolynomial)
    (z : Gaussian.Basic.Canonical) :
    eval (Ascending.Rational.Basic.scale factor polynomial) z =
      Gaussian.Scale.scale factor (eval polynomial z) :=
  evalCoefficients_map_scale factor z polynomial.coefficients

/-- A prefixed zero block multiplies the Gaussian Horner value by the corresponding argument power. -/
theorem evalCoefficients_replicate_zero_append (z :
  Gaussian.Basic.Canonical) :
    ∀ count coefficients,
      evalCoefficients z (List.replicate count 0 ++ coefficients) =
        z ^ count * evalCoefficients z coefficients
  | 0, coefficients => by
      simp only [List.replicate_zero, List.nil_append, pow_zero]
      exact (Gaussian.Basic.one_mul _).symm
  | count + 1, coefficients => by
      rw [List.replicate_succ, List.cons_append, evalCoefficients,
        evalCoefficients_replicate_zero_append z count
          coefficients,
        pow_succ]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im] <;>
        ring1

/-- A polynomial shift multiplies its Gaussian value by the argument power. -/
@[simp] theorem eval_shift (count : Nat) (polynomial :
  CoefficientPolynomial)
    (z : Gaussian.Basic.Canonical) :
    eval (Ascending.Rational.Basic.shift count polynomial) z = z ^ count *
      eval polynomial z :=
  evalCoefficients_replicate_zero_append z count polynomial.coefficients

/-- Gaussian evaluation turns coefficient convolution into multiplication of the two values.

The finite recursion follows the scaled head contribution and shifted product of the tail. -/
theorem eval_mulCoefficients (z :
  Gaussian.Basic.Canonical) : ∀ left right,
    evalCoefficients z (Ascending.Rational.Basic.mulCoefficients left right) =
      evalCoefficients z left *
        evalCoefficients z right
  | [], right => by
      apply Gaussian.Basic.ext <;>
        simp only [Ascending.Rational.Basic.mulCoefficients, evalCoefficients,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im] <;> ring1
  | left :: leftTail, right => by
      rw [Ascending.Rational.Basic.mulCoefficients, eval_addCoefficients,
        evalCoefficients_map_scale,
          evalCoefficients,
        evalCoefficients,
          eval_mulCoefficients z leftTail right]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
          Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1

/-- Gaussian evaluation preserves polynomial multiplication. -/
@[simp] theorem eval_mul (left right :
  CoefficientPolynomial) (z : Gaussian.Basic.Canonical) :
    eval (Ascending.Rational.Basic.mul left right) z =
      eval left z * eval right z :=
  eval_mulCoefficients z left.coefficients right.coefficients

/-- Gaussian evaluation preserves natural powers of finite polynomials. -/
@[simp] theorem eval_pow (polynomial :
  CoefficientPolynomial) (z : Gaussian.Basic.Canonical) :
    ∀ exponent, eval (Ascending.Rational.Basic.pow polynomial exponent) z =
      eval polynomial z ^ exponent
  | 0 => by
      change Gaussian.Scale.scale 1 1 + z * 0 = _
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im, pow_zero] <;>
            ring1
  | exponent + 1 => by
      rw [Ascending.Rational.Basic.pow, eval_mul,
        eval_pow polynomial z exponent, pow_succ]

/-- A monomial evaluates to its rational coefficient scaling the Gaussian argument power. -/
theorem eval_monomial (degree : Nat) (coefficient :
  Fraction.Rational)
    (z : Gaussian.Basic.Canonical) :
    eval (Ascending.Rational.Monomial.monomial degree coefficient) z =
      Gaussian.Scale.scale coefficient (z ^ degree) := by
  rw [Ascending.Rational.Monomial.monomial, eval_shift]
  change z ^ degree *
      (Gaussian.Scale.scale coefficient 1 + z * 0) = _
  apply Gaussian.Basic.ext <;>
    simp only [Gaussian.Scale.scale_re,
      Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im,
      Gaussian.Basic.zero_re, Gaussian.Basic.zero_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1

/-- Gaussian Horner evaluation at an embedded rational equals the embedded scalar Horner value. -/
theorem evalCoefficients_scalar (radius :
  Fraction.Rational) : ∀ coefficients,
    evalCoefficients (Gaussian.RationalEmbedding.ComplexLog.scalar radius)
        coefficients =
      Gaussian.RationalEmbedding.ComplexLog.scalar
        (Ascending.Rational.Evaluation.scalarEvalCoefficients radius coefficients)
  | [] => rfl
  | coefficient :: remaining => by
      rw [evalCoefficients, Ascending.Rational.Evaluation.scalarEvalCoefficients,
        evalCoefficients_scalar radius remaining]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.RationalEmbedding.ComplexLog.scalar,
          Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im,
          Gaussian.Basic.mul_re, Gaussian.Basic.mul_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1

/-- Evaluation at an embedded rational agrees with the rational scalar evaluation. -/
theorem eval_scalar (radius : Fraction.Rational)
  (polynomial : CoefficientPolynomial) :
    eval polynomial (Gaussian.RationalEmbedding.ComplexLog.scalar radius) =
      Gaussian.RationalEmbedding.ComplexLog.scalar (Ascending.Rational.Evaluation.scalarEval radius polynomial) :=
  evalCoefficients_scalar radius polynomial.coefficients

/-- A table with all zero-extended coefficients zero has Gaussian value zero. -/
theorem evalCoefficients_zero_of_coefficients_zero (z :
  Gaussian.Basic.Canonical) :
    ∀ coefficients,
      (∀ degree, Ascending.Rational.Basic.coefficientCoefficients coefficients degree = 0) →
        evalCoefficients z coefficients = 0
  | [], allZero => rfl
  | coefficient :: remaining, allZero => by
      have headZero : coefficient = 0 := allZero 0
      have tailZero :
          ∀ degree, Ascending.Rational.Basic.coefficientCoefficients remaining degree = 0 := by
        intro degree
        exact allZero (degree + 1)
      subst coefficient
      rw [evalCoefficients,
        evalCoefficients_zero_of_coefficients_zero z remaining
          tailZero]
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Scale.scale_re,
          Gaussian.Scale.scale_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
            Gaussian.Basic.mul_im,
          Gaussian.Basic.zero_re, Gaussian.Basic.zero_im, Gaussian.Basic.one_re, Gaussian.Basic.one_im] <;> ring1
end Purelib.Polynomial.Ascending.Rational.GaussianEvaluation

end
