module
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Integer
import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
public import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
import Purelib.Polynomial.Dense.Rational.Extensionality

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Field

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Basic.Integer (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Executable integer certificates for finite dense rational polynomials

An integer polynomial is represented by an ascending `List Int`, converted
to the project's descending dense representation by a finite reversal and
canonical normalization.  This file proves that dense long division by a
monic integer polynomial preserves integer coefficients.  No factorization
domain, content normalization, or ambient polynomial hierarchy is used.
-/

namespace Purelib.Polynomial.Dense.Rational.IntegerCoefficients.Basic

/-- A dense polynomial has an executable ascending integer certificate. -/
def IsIntegralPolynomial (polynomial :
  CoefficientPolynomial) : Prop :=
  ∃ coefficients : List Int,
    polynomial.normalize = Dense.Rational.AscendingInteger.Basic.ofAscending coefficients

/-- The empty coefficient table certifies that the zero dense polynomial has integer coefficients. -/
theorem integral_zero :
  IsIntegralPolynomial (0 :
    CoefficientPolynomial) :=
  ⟨[], rfl⟩

/-- An integer-valued rational constant gives a dense polynomial with an explicit integer coefficient certificate. -/
theorem integral_constant {value : Fraction.Rational}
    (integral : Fraction.Integer.IsIntegralRational value) :
    IsIntegralPolynomial (DensePolynomial.constant value) := by
  rcases integral with ⟨integer, rfl⟩
  refine ⟨[integer], ?_⟩
  unfold Dense.Rational.AscendingInteger.Basic.ofAscending
  rfl

/-- A normalized integer coefficient certificate identifies dense evaluation with its ascending integer evaluator. -/
theorem eval_eq_integerCertificate {polynomial :
  CoefficientPolynomial}
    {coefficients : List Int}
    (certificate : polynomial.normalize =
      Dense.Rational.AscendingInteger.Basic.ofAscending coefficients)
    (point : Fraction.Rational) :
    polynomial.eval point =
      Ascending.Integer.Basic.eval coefficients point := by
  calc
    polynomial.eval point = polynomial.normalize.eval point :=
      (DensePolynomial.eval_normalize polynomial point).symm
    _ = (Dense.Rational.AscendingInteger.Basic.ofAscending coefficients).eval point := by
      rw [certificate]
    _ = Ascending.Integer.Basic.eval coefficients point :=
      Dense.Rational.AscendingInteger.Basic.eval_ofAscending coefficients point

/-- Normalization preserves the original ascending integer coefficient certificate. -/
theorem integral_normalize {polynomial :
  CoefficientPolynomial}
    (integral : IsIntegralPolynomial polynomial) :
    IsIntegralPolynomial polynomial.normalize := by
  rcases integral with ⟨coefficients, certificate⟩
  refine ⟨coefficients, ?_⟩
  rw [DensePolynomial.normalize_normalize, certificate]

/-- Adding dense polynomials with integer certificates produces an integer certificate by ascending coefficient
addition. -/
theorem integral_add {left right :
  CoefficientPolynomial}
    (leftIntegral : IsIntegralPolynomial left)
    (rightIntegral : IsIntegralPolynomial right) :
    IsIntegralPolynomial (left + right) := by
  rcases leftIntegral with ⟨leftCoefficients, leftCertificate⟩
  rcases rightIntegral with ⟨rightCoefficients, rightCertificate⟩
  refine ⟨Ascending.Integer.Basic.Certificate.add
    leftCoefficients rightCoefficients, ?_⟩
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_normalize _) (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
  intro point
  rw [DensePolynomial.eval_normalize, DensePolynomial.eval_add,
    eval_eq_integerCertificate leftCertificate,
    eval_eq_integerCertificate rightCertificate,
    ← Ascending.Integer.Basic.eval_add,
    Dense.Rational.AscendingInteger.Basic.eval_ofAscending]

/-- Negating a dense polynomial with an integer certificate negates its ascending coefficient witness. -/
theorem integral_neg {polynomial :
  CoefficientPolynomial}
    (integral : IsIntegralPolynomial polynomial) :
    IsIntegralPolynomial (-polynomial) := by
  rcases integral with ⟨coefficients, certificate⟩
  refine ⟨Ascending.Integer.Basic.neg coefficients, ?_⟩
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_normalize _) (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
  intro point
  rw [DensePolynomial.eval_normalize, DensePolynomial.eval_neg,
    eval_eq_integerCertificate certificate,
    ← Ascending.Integer.Basic.eval_neg,
    Dense.Rational.AscendingInteger.Basic.eval_ofAscending]

/-- Subtracting dense polynomials with integer certificates subtracts their ascending coefficient witnesses. -/
theorem integral_sub {left right :
  CoefficientPolynomial}
    (leftIntegral : IsIntegralPolynomial left)
    (rightIntegral : IsIntegralPolynomial right) :
    IsIntegralPolynomial (left - right) := by
  rcases leftIntegral with ⟨leftCoefficients, leftCertificate⟩
  rcases rightIntegral with ⟨rightCoefficients, rightCertificate⟩
  refine ⟨Ascending.Integer.Basic.sub
    leftCoefficients rightCoefficients, ?_⟩
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_normalize _) (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
  intro point
  rw [DensePolynomial.eval_normalize, DensePolynomial.eval_sub,
    eval_eq_integerCertificate leftCertificate,
    eval_eq_integerCertificate rightCertificate,
    ← Ascending.Integer.Basic.eval_sub,
    Dense.Rational.AscendingInteger.Basic.eval_ofAscending]

/-- Multiplying dense polynomials with integer certificates multiplies their ascending coefficient witnesses. -/
theorem integral_mul {left right :
  CoefficientPolynomial}
    (leftIntegral : IsIntegralPolynomial left)
    (rightIntegral : IsIntegralPolynomial right) :
    IsIntegralPolynomial (left * right) := by
  rcases leftIntegral with ⟨leftCoefficients, leftCertificate⟩
  rcases rightIntegral with ⟨rightCoefficients, rightCertificate⟩
  refine ⟨Ascending.Integer.Basic.Certificate.mul
    leftCoefficients rightCoefficients, ?_⟩
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_normalize _) (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
  intro point
  rw [DensePolynomial.eval_normalize, DensePolynomial.eval_mul,
    eval_eq_integerCertificate leftCertificate,
    eval_eq_integerCertificate rightCertificate,
    ← Ascending.Integer.Basic.eval_mul,
    Dense.Rational.AscendingInteger.Basic.eval_ofAscending]

/-- An integer-valued scalar preserves an integer coefficient certificate under dense scaling. -/
theorem integral_scale {factor : Fraction.Rational}
  {polynomial : CoefficientPolynomial}
    (factorIntegral : Fraction.Integer.IsIntegralRational factor)
    (polynomialIntegral : IsIntegralPolynomial polynomial) :
    IsIntegralPolynomial
      (DensePolynomial.scale factor polynomial) := by
  rcases factorIntegral with ⟨integer, rfl⟩
  rcases polynomialIntegral with ⟨coefficients, certificate⟩
  refine ⟨Ascending.Integer.Basic.Certificate.scale integer coefficients, ?_⟩
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_normalize _) (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
  intro point
  rw [DensePolynomial.eval_normalize,
    DensePolynomial.eval_scale,
    eval_eq_integerCertificate certificate,
    ← Ascending.Integer.Basic.eval_scale,
    Dense.Rational.AscendingInteger.Basic.eval_ofAscending]

/-- A displayed power-of-variable shift preserves an integer coefficient certificate through the corresponding ascending
shifts. -/
theorem integral_shift (exponent : Nat) {polynomial :
  CoefficientPolynomial}
    (integral : IsIntegralPolynomial polynomial) :
    IsIntegralPolynomial
      (DensePolynomial.shift exponent polynomial) := by
  rcases integral with ⟨coefficients, certificate⟩
  refine ⟨Dense.Rational.AscendingInteger.Basic.shiftN exponent coefficients, ?_⟩
  apply Dense.Rational.Extensionality.rational_normalized_eq_of_eval_eq
    (DensePolynomial.normalize_normalize _) (Dense.Rational.AscendingInteger.Basic.ofAscending_normalized _)
  intro point
  rw [DensePolynomial.eval_normalize,
    DensePolynomial.eval_shift,
    eval_eq_integerCertificate certificate,
    ← Dense.Rational.AscendingInteger.Basic.eval_shiftN,
    Dense.Rational.AscendingInteger.Basic.eval_ofAscending]
end Purelib.Polynomial.Dense.Rational.IntegerCoefficients.Basic

end
