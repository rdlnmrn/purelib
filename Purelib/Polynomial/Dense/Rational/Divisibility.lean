module

import Purelib.Data.Bool.Decide
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Extensionality
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

/-!
# Finite polynomial divisibility and Bezout certificates

A retained dense quotient certifies divisibility by scalar evaluation. Two
retained coefficient polynomials certify Bezout coprimality. Direct transports,
finite long division and the original derivative program relate those same
witnesses to normalized rational coefficient identities.
-/

namespace Purelib.Polynomial.Dense.Rational.Divisibility

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Rational
open Purelib.Data.Rat
open Purelib.Data.Bool
/-- The descending dense polynomial representation over constructive rationals. -/
public abbrev CoefficientPolynomial := Basic.DensePolynomial Fraction.Rational

/-- Pointwise equality is used only as an algebraic certificate.  Finite
coefficient extensionality converts it back to list equality whenever the
representation matters.

Each supplied rational point has its own scalar equality certificate. Finite coefficient extensionality can identify the
same normalized coefficient owners when their representations must coincide. -/
@[expose] public def EvalEq (left right : CoefficientPolynomial) : Prop :=
  ∀ point : Fraction.Rational, left.eval point = right.eval point

/-- Explicit polynomial divisibility, witnessed by one finite dense
quotient.

The witness is the original finite quotient polynomial. Its retained scalar identity compares the dividend with the
product of that same divisor and quotient. -/
@[expose] public def EvalDvd (divisor dividend : CoefficientPolynomial) : Prop :=
  ∃ quotient : CoefficientPolynomial, EvalEq dividend (divisor * quotient)

/-- Explicit Bezout coprimality.

The two retained finite coefficient polynomials multiply the original left and right inputs in order. Their scalar sum
is the rational unit at every supplied point. -/
@[expose] public def EvalCoprime (left right : CoefficientPolynomial) : Prop :=
  ∃ first second : CoefficientPolynomial, ∀ point : Fraction.Rational,
    1 = first.eval point * left.eval point +
      second.eval point * right.eval point

/-- Pointwise equality of polynomial evaluations is reflexive. -/
public theorem evalEq_refl (polynomial : CoefficientPolynomial) : EvalEq polynomial polynomial :=
  fun _ => rfl

/-- Reverse a pointwise equality of polynomial evaluations. -/
public theorem evalEq_symm {left right : CoefficientPolynomial} (equal : EvalEq left right) :
    EvalEq right left := fun point => (equal point).symm

/-- Compose two pointwise equalities of polynomial evaluations. -/
public theorem evalEq_trans {first second third : CoefficientPolynomial}
    (firstSecond : EvalEq first second) (secondThird : EvalEq second third) :
    EvalEq first third := fun point => (firstSecond point).trans (secondThird point)

/-- A polynomial divides itself with the explicit constant-one quotient.

The retained constant-one polynomial supplies the original quotient witness. Its scalar unit readback preserves the same
dividend value. -/
public theorem evalDvd_refl (polynomial : CoefficientPolynomial) : EvalDvd polynomial polynomial := by
  refine ⟨Basic.DensePolynomial.constant 1, ?_⟩
  intro point
  rw [Basic.DensePolynomial.eval_mul, Basic.DensePolynomial.eval_constant, mul_one]

/-- Compose two displayed polynomial divisibilities by multiplying their finite quotient witnesses.

The two original finite quotient witnesses are multiplied in their original order. Scalar evaluation transports their
retained divisibility identities through that same product. -/
public theorem evalDvd_trans {first second third : CoefficientPolynomial}
    (firstSecond : EvalDvd first second) (secondThird : EvalDvd second third) :
    EvalDvd first third := by
  rcases firstSecond with ⟨firstFactor, firstIdentity⟩
  rcases secondThird with ⟨secondFactor, secondIdentity⟩
  refine ⟨firstFactor * secondFactor, ?_⟩
  intro point
  calc
    third.eval point = second.eval point * secondFactor.eval point := by
      simpa only [Basic.DensePolynomial.eval_mul] using secondIdentity point
    _ = (first.eval point * firstFactor.eval point) *
        secondFactor.eval point := by
      exact congrArg (fun value => value * secondFactor.eval point)
        (by simpa only [Basic.DensePolynomial.eval_mul] using firstIdentity point)
    _ = (first * (firstFactor * secondFactor)).eval point := by
      simp only [Basic.DensePolynomial.eval_mul]
      ring0

/-- The left polynomial divides its product with the right polynomial, witnessed by that right factor.

The original right polynomial is the finite quotient witness. Its product with the same left divisor is retained without
rebuilding either input. -/
public theorem evalDvd_mul_right (left right : CoefficientPolynomial) :
    EvalDvd left (left * right) := ⟨right, evalEq_refl _⟩

/-- The right polynomial divides a displayed product, witnessed by the left factor.

The original left polynomial is the finite quotient witness. Scalar multiplication commutes the two same retained factor
values. -/
public theorem evalDvd_mul_left (left right : CoefficientPolynomial) :
    EvalDvd right (left * right) := by
  refine ⟨left, ?_⟩
  intro point
  simp only [Basic.DensePolynomial.eval_mul]
  ring0

/-- Swap the inputs and their two coefficients in a polynomial Bezout certificate.

The original two Bezout coefficient owners exchange positions together with their two inputs. Commuting their scalar
contributions retains the unit identity. -/
public theorem evalCoprime_symm {left right : CoefficientPolynomial}
    (coprime : EvalCoprime left right) : EvalCoprime right left := by
  rcases coprime with ⟨first, second, identity⟩
  refine ⟨second, first, ?_⟩
  intro point
  simpa only [add_comm] using identity point

/-- The constant-one polynomial is explicitly Bezout coprime to every polynomial.

The original constant-one and zero polynomials supply the two coefficient witnesses. Their scalar unit and zero values
retain the required sum. -/
public theorem evalCoprime_one_left (polynomial : CoefficientPolynomial) :
    EvalCoprime (Basic.DensePolynomial.constant 1) polynomial := by
  refine ⟨Basic.DensePolynomial.constant 1, 0, ?_⟩
  intro point
  simp only [Basic.DensePolynomial.eval_constant, Basic.DensePolynomial.eval_zero]
  ring0

/-- Every polynomial is explicitly Bezout coprime to the constant-one polynomial.

Swapping the retained constant-one-left certificate preserves its two coefficient polynomials and scalar unit identity.
-/
public theorem evalCoprime_one_right (polynomial : CoefficientPolynomial) :
    EvalCoprime polynomial (Basic.DensePolynomial.constant 1) :=
  evalCoprime_symm (evalCoprime_one_left polynomial)

/-- Two coprimality certificates multiply on the left.

The original two Bezout coefficient pairs determine the displayed product and three-term coefficient sum. Multiplying
their scalar unit identities verifies those same retained witnesses. -/
public theorem evalCoprime_mul_left {first second third : CoefficientPolynomial}
    (firstThird : EvalCoprime first third)
    (secondThird : EvalCoprime second third) :
    EvalCoprime (first * second) third := by
  rcases firstThird with ⟨a, b, firstIdentity⟩
  rcases secondThird with ⟨c, d, secondIdentity⟩
  refine ⟨a * c,
    a * d * first + b * c * second + b * d * third, ?_⟩
  intro point
  simp only [Basic.DensePolynomial.eval_mul, Basic.DensePolynomial.eval_add]
  calc
    1 = (a.eval point * first.eval point + b.eval point * third.eval point) *
          (c.eval point * second.eval point + d.eval point * third.eval point) := by
      rw [← firstIdentity point, ← secondIdentity point]
      ring0
    _ = (a.eval point * c.eval point) *
          (first.eval point * second.eval point) +
        (a.eval point * d.eval point * first.eval point +
            b.eval point * c.eval point * second.eval point +
            b.eval point * d.eval point * third.eval point) *
          third.eval point := by ring0

/-- Coprime divisors of the same polynomial may be multiplied.

The two original divisibility quotients and Bezout coefficients determine the displayed finite sum witness. Their
retained scalar identities factor the same dividend by both original coprime inputs. -/
public theorem evalDvd_mul_of_coprime {first second dividend : CoefficientPolynomial}
    (firstDivides : EvalDvd first dividend)
    (secondDivides : EvalDvd second dividend)
    (coprime : EvalCoprime first second) :
    EvalDvd (first * second) dividend := by
  rcases firstDivides with ⟨firstFactor, firstIdentity⟩
  rcases secondDivides with ⟨secondFactor, secondIdentity⟩
  rcases coprime with ⟨a, b, bezout⟩
  refine ⟨secondFactor * a + firstFactor * b, ?_⟩
  intro point
  simp only [Basic.DensePolynomial.eval_mul, Basic.DensePolynomial.eval_add]
  calc
    dividend.eval point = dividend.eval point * 1 := by ring0
    _ = dividend.eval point *
        (a.eval point * first.eval point +
          b.eval point * second.eval point) := by rw [← bezout point]
    _ = dividend.eval point * (a.eval point * first.eval point) +
        dividend.eval point * (b.eval point * second.eval point) := by ring0
    _ = (second.eval point * secondFactor.eval point) *
          (a.eval point * first.eval point) +
        (first.eval point * firstFactor.eval point) *
          (b.eval point * second.eval point) := by
      apply congrArg₂ (· + ·)
      · rw [secondIdentity point, Basic.DensePolynomial.eval_mul]
      · rw [firstIdentity point, Basic.DensePolynomial.eval_mul]
    _ = (first.eval point * second.eval point) *
        (secondFactor.eval point * a.eval point +
          firstFactor.eval point * b.eval point) := by ring0

/-- If one factor divides the left input of a Bezout certificate, it is also
coprime to the right input.

The retained factor quotient multiplies the original first Bezout coefficient. Its same scalar product identity
preserves coprimality with the unchanged right input. -/
public theorem evalCoprime_of_evalDvd_left {factor product right : CoefficientPolynomial}
    (factorDivides : EvalDvd factor product)
    (coprime : EvalCoprime product right) : EvalCoprime factor right := by
  rcases factorDivides with ⟨cofactor, factorIdentity⟩
  rcases coprime with ⟨first, second, bezout⟩
  refine ⟨first * cofactor, second, ?_⟩
  intro point
  simp only [Basic.DensePolynomial.eval_mul]
  calc
    1 = first.eval point * product.eval point +
        second.eval point * right.eval point := bezout point
    _ = (first.eval point * cofactor.eval point) * factor.eval point +
        second.eval point * right.eval point := by
      rw [factorIdentity point, Basic.DensePolynomial.eval_mul]
      ring0

/-- Exact pointwise divisibility forces the executable long-division
remainder to be the represented zero.

The original quotient witness and computed long-division quotient determine their retained coefficient difference. A
nonzero remainder would equal its product with the divisor, contradicting the same strict remainder degree bound. -/
public theorem divMod_remainder_isZero_of_evalDvd
    (dividend divisor : CoefficientPolynomial)
    (divisorNonzero : divisor.isZero = false)
    (divides : EvalDvd divisor dividend) :
    (Basic.DensePolynomial.divMod dividend divisor).remainder.isZero = true := by
  rcases divides with ⟨witness, witnessIdentity⟩
  let quotient := (Basic.DensePolynomial.divMod dividend divisor).quotient
  let remainder := (Basic.DensePolynomial.divMod dividend divisor).remainder
  let difference := witness - quotient
  have remainderIdentity : EvalEq remainder (divisor * difference) := by
    intro point
    have division := Basic.DensePolynomial.divMod_eval_equation dividend divisor point
    change remainder.eval point + divisor.eval point * quotient.eval point =
      dividend.eval point at division
    have witnessAt := witnessIdentity point
    rw [Basic.DensePolynomial.eval_mul] at witnessAt
    dsimp only [difference]
    rw [Basic.DensePolynomial.eval_mul, Basic.DensePolynomial.eval_sub]
    change remainder.eval point =
      divisor.eval point * (witness.eval point - quotient.eval point)
    calc
      remainder.eval point = dividend.eval point -
          divisor.eval point * quotient.eval point := by
        rw [← division]
        ring0
      _ = divisor.eval point * witness.eval point -
          divisor.eval point * quotient.eval point := by rw [witnessAt]
      _ = divisor.eval point *
          (witness.eval point - quotient.eval point) := by ring0
  have remainderNormalized : remainder.normalize = remainder := by
    exact Basic.DensePolynomial.divMod_remainder_normalize dividend divisor
  have productNormalized : (divisor * difference).normalize =
      divisor * difference := Basic.DensePolynomial.normalize_mul _ _
  have representedIdentity : remainder = divisor * difference :=
    Extensionality.rational_normalized_eq_of_eval_eq
      remainderNormalized productNormalized remainderIdentity
  by_cases remainderZero : remainder.isZero = true
  · exact remainderZero
  · have remainderNonzero : remainder.isZero = false := by
      exact Decide.bool_eq_false_of_not_eq_true _ remainderZero
    have differenceNonzero : difference.isZero = false := by
      by_cases differenceZero : difference.isZero = true
      · have productZero : divisor * difference = 0 :=
          Basic.DensePolynomial.mul_eq_zero_of_isZero_right (p := divisor) differenceZero
        have remainderIsZero : remainder.isZero = true := by
          rw [representedIdentity, productZero, Basic.DensePolynomial.isZero_zero]
        rw [remainderIsZero] at remainderNonzero
        exact Bool.noConfusion remainderNonzero
      · exact Decide.bool_eq_false_of_not_eq_true _ differenceZero
    have productDegree := Basic.DensePolynomial.natDegree_mul divisorNonzero differenceNonzero
    have remainderDegreeBelow :=
      Basic.DensePolynomial.divMod_remainder_degreeCount_lt dividend divisor divisorNonzero
    change remainder.degreeCount < divisor.degreeCount at remainderDegreeBelow
    have remainderCount := Basic.DensePolynomial.natDegree_add_one_eq_degreeCount remainderNonzero
    have divisorCount := Basic.DensePolynomial.natDegree_add_one_eq_degreeCount divisorNonzero
    have degreeIdentity := congrArg
      (fun polynomial : CoefficientPolynomial => polynomial.natDegree) representedIdentity
    rw [productDegree] at degreeIdentity
    omega0

/-- Two displayed factors of a square-free polynomial are explicitly
coprime.

The normalized factorization retains both original factors. The original derivative product rule transforms the same
squarefree Bezout coefficients into the displayed two factor coefficients. -/
public theorem evalCoprime_factors_of_squarefree
    {whole left right : CoefficientPolynomial}
    (wholeNormalized : whole.normalize = whole)
    (factorization : EvalEq whole (left * right))
    (squarefree : EvalCoprime whole
      (Derivative.derivative whole)) :
    EvalCoprime left right := by
  have representedFactorization : whole = left * right :=
    Extensionality.rational_normalized_eq_of_eval_eq
      wholeNormalized (Basic.DensePolynomial.normalize_mul _ _) factorization
  rcases squarefree with ⟨first, second, bezout⟩
  refine ⟨first * right + second *
      Derivative.derivative right,
    second * Derivative.derivative left, ?_⟩
  intro point
  simp only [Basic.DensePolynomial.eval_add, Basic.DensePolynomial.eval_mul]
  calc
    1 = first.eval point * whole.eval point + second.eval point *
        (Derivative.derivative whole).eval point := bezout point
    _ = first.eval point * (left.eval point * right.eval point) +
        second.eval point *
          ((Derivative.derivative left).eval point *
              right.eval point + left.eval point *
                (Derivative.derivative right).eval point) := by
      rw [representedFactorization,
        Derivative.eval_derivative_mul, Basic.DensePolynomial.eval_mul]
    _ = (first.eval point * right.eval point + second.eval point *
          (Derivative.derivative right).eval point) *
        left.eval point +
      (second.eval point *
          (Derivative.derivative left).eval point) *
        right.eval point := by ring0

/-- The constant-one polynomial divides every polynomial, with the polynomial itself as quotient.

The original dividend itself supplies the finite quotient witness. Its scalar value is preserved by the retained
constant-one divisor. -/
public theorem evalDvd_one (polynomial : CoefficientPolynomial) :
    EvalDvd (Basic.DensePolynomial.constant 1) polynomial := by
  refine ⟨polynomial, ?_⟩
  intro point
  rewrite [Basic.DensePolynomial.eval_mul,
    Basic.DensePolynomial.eval_constant, one_mul]
  exact Eq.refl _

/-- The dense constant-one polynomial has natural degree zero. -/
@[simp] public theorem natDegree_constant_one :
    (Basic.DensePolynomial.constant (1 : Fraction.Rational)).natDegree = 0 := by
  unfold Basic.DensePolynomial.natDegree Basic.DensePolynomial.degreeCount
  rw [Basic.DensePolynomial.normalize_constant_of_ne
    Fraction.Field.zero_ne_one.symm]
  rfl

/-- Pointwise replacement of the represented divisor preserves explicit
divisibility.

The original quotient witness is retained. Replacing only the divisor scalar readback transports its same dividend
product identity. -/
public theorem evalDvd_of_evalEq_divisor {first second dividend : CoefficientPolynomial}
    (equal : EvalEq first second) (divides : EvalDvd second dividend) :
    EvalDvd first dividend := by
  rcases divides with ⟨quotient, identity⟩
  refine ⟨quotient, ?_⟩
  intro point
  rw [Basic.DensePolynomial.eval_mul, equal point]
  simpa only [Basic.DensePolynomial.eval_mul] using identity point

/-- Extract the right-factor divisibility from a displayed pointwise factorization.

The original left factor supplies the finite quotient witness for the unchanged right divisor. Commuting their same
scalar product verifies the retained factorization. -/
public theorem evalDvd_right_of_factorization {whole left right : CoefficientPolynomial}
    (factorization : EvalEq whole (left * right)) : EvalDvd right whole := by
  refine ⟨left, ?_⟩
  intro point
  calc
    whole.eval point = (left * right).eval point := factorization point
    _ = right.eval point * left.eval point := by
      simp only [Basic.DensePolynomial.eval_mul]
      ring0
    _ = (right * left).eval point := by rw [Basic.DensePolynomial.eval_mul]

/-- Extract the left-factor divisibility from a displayed pointwise factorization.

The original right factor supplies the finite quotient witness. The retained factorization is exactly its required
scalar product identity. -/
public theorem evalDvd_left_of_factorization {whole left right : CoefficientPolynomial}
    (factorization : EvalEq whole (left * right)) : EvalDvd left whole := by
  refine ⟨right, factorization⟩
end Purelib.Polynomial.Dense.Rational.Divisibility
