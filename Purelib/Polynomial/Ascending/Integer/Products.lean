module
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Ascending.Integer.Basic
public import Purelib.Polynomial.Dense.Rational.FiniteProduct.Integer

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Polynomial

section
/-!
# Finite integer-polynomial certificates

Integer coefficient lists are stored in ascending degree order.  The
primitive-recursive operations below let a literal finite Bezout identity be
checked by kernel reduction over `Int`, then evaluated in any constructive
explicit field.  This is useful for prime-field exclusions without listing
or searching an ambient carrier.
-/

public section

namespace Purelib.Polynomial.Ascending.Integer.Products

/-- Add a displayed prefix of integer polynomials. -/
@[expose] def sum : Nat → (Nat → List Int) → List Int
  | 0, _ => []
  | count + 1, term =>
    Ascending.Integer.Basic.Certificate.add (Purelib.Polynomial.Ascending.Integer.Products.sum count term) (term count)

/-- The sum of an empty coefficient-table prefix is the empty zero table. -/
@[simp] theorem sum_zero (term : Nat → List Int) :
    Ascending.Integer.Products.sum 0 term = [] := rfl

/-- Extend a finite polynomial sum by adding its final indexed table. -/
@[simp] theorem sum_succ (count : Nat) (term : Nat → List Int) :
    Ascending.Integer.Products.sum (count + 1) term =
      Ascending.Integer.Basic.Certificate.add (Ascending.Integer.Products.sum count term) (term count) := rfl

/-- Evaluate a primitive-recursive sum directly in the target field. -/
@[expose] def valueSum {K : Type*} [ExplicitField K] :
    Nat → (Nat → K) → K
  | 0, _ => 0
  | count + 1, term => Purelib.Polynomial.Ascending.Integer.Products.valueSum count term + term count

/-- Evaluation of a finite coefficient-table sum equals the sum of the individual values. -/
theorem eval_sum {K : Type*} [ExplicitField K]
    (count : Nat) (term : Nat → List Int) (value : K) :
    Ascending.Integer.Basic.eval (Ascending.Integer.Products.sum count term) value =
      Ascending.Integer.Products.valueSum count (fun index => Ascending.Integer.Basic.eval (term index) value) := by
  induction count with
  | zero => rfl
  | succ count inductionHypothesis =>
      rw [Ascending.Integer.Products.sum_succ, Ascending.Integer.Basic.eval_add, inductionHypothesis,
        Ascending.Integer.Products.valueSum]

/-- Multiply a displayed prefix of integer polynomials. -/
@[expose] def product : Nat → (Nat → List Int) → List Int
  | 0, _ => [1]
  | count + 1, term =>
    Ascending.Integer.Basic.Certificate.mul (Purelib.Polynomial.Ascending.Integer.Products.product count term) (term
      count)

/-- The product of an empty coefficient-table prefix is the singleton one table. -/
@[simp] theorem product_zero (term : Nat → List Int) :
    Ascending.Integer.Products.product 0 term = [1] := rfl

/-- Extend a finite polynomial product by multiplying by its final indexed table. -/
@[simp] theorem product_succ (count : Nat)
    (term : Nat → List Int) :
    Ascending.Integer.Products.product (count + 1) term =
      Ascending.Integer.Basic.Certificate.mul (Ascending.Integer.Products.product count term) (term count) := rfl

/-- Evaluate the same primitive-recursive product directly in the target
field. -/
@[expose] def valueProduct {K : Type*} [ExplicitField K] :
    Nat → (Nat → K) → K
  | 0, _ => 1
  | count + 1, term => Purelib.Polynomial.Ascending.Integer.Products.valueProduct count term * term count

/-- Evaluation of a finite coefficient-table product equals the product of the individual values. -/
theorem eval_product {K : Type*} [ExplicitField K]
    (count : Nat) (term : Nat → List Int) (value : K) :
    Ascending.Integer.Basic.eval (Ascending.Integer.Products.product count term) value =
      Ascending.Integer.Products.valueProduct count (fun index => Ascending.Integer.Basic.eval (term index) value) := by
  induction count with
  | zero =>
      simp only [Ascending.Integer.Products.product_zero, Ascending.Integer.Basic.eval_cons,
        Ascending.Integer.Basic.eval_nil, Int.cast_one,
        mul_zero, add_zero, Ascending.Integer.Products.valueProduct, -eq_self, -iff_self] ; rfl
  | succ count inductionHypothesis =>
      rw [Ascending.Integer.Products.product_succ, Ascending.Integer.Basic.eval_mul, inductionHypothesis]
      rfl

/-- The finite list with one coefficient in the requested degree. -/
@[expose] def Certificate.monomial (degree : Nat) (coefficient :
  Int) : List Int :=
  List.replicate degree 0 ++ [coefficient]

/-- An integer monomial evaluates to its cast coefficient times the argument power. -/
theorem eval_monomial {K : Type*} [ExplicitField K]
    (degree : Nat) (coefficient : Int) (value : K) :
    Ascending.Integer.Basic.eval (Ascending.Integer.Products.Certificate.monomial degree coefficient) value =
      (coefficient : K) * value ^ degree := by
  induction degree with
  | zero =>
    simp [Ascending.Integer.Products.Certificate.monomial, Ascending.Integer.Basic.eval, -eq_self, -iff_self]; rfl
  | succ degree inductionHypothesis =>
      rw [Ascending.Integer.Products.Certificate.monomial, List.replicate_succ, List.cons_append,
        Ascending.Integer.Basic.eval_cons]
      rw [show List.replicate degree 0 ++ [coefficient] =
          Ascending.Integer.Products.Certificate.monomial degree coefficient by rfl]
      rw [inductionHypothesis, pow_succ]
      simp only [Purelib.Algebra.Ring.IntCast.cast_zero, zero_add]
      ring1

/-- Coefficients of `X^modulus-X`. -/
@[expose] def frobenius (modulus : Nat) : List Int :=
  Ascending.Integer.Basic.Certificate.add (Ascending.Integer.Products.Certificate.monomial modulus 1)
    (Ascending.Integer.Products.Certificate.monomial 1 (-1))

/-- The Frobenius coefficient table evaluates to `value^modulus - value`. -/
theorem eval_frobenius {K : Type*} [ExplicitField K]
    (modulus : Nat) (value : K) :
    Ascending.Integer.Basic.eval (Ascending.Integer.Products.frobenius modulus) value = value ^ modulus - value := by
  rw [Ascending.Integer.Products.frobenius, Ascending.Integer.Basic.eval_add, Ascending.Integer.Products.eval_monomial,
    Ascending.Integer.Products.eval_monomial]
  simp only [Int.cast_one, one_mul]
  ring1
end Purelib.Polynomial.Ascending.Integer.Products

end

end

section
@[expose] public section

/-!
# The finite Goh--Wildberger spread-cyclotomic factorization

This file completes Exercise 8.13 without roots, completed fields, or an
infinite polynomial family.  Ordinary cyclotomic factors are constructed by
finite monic long division over the constructive rationals.  Their integer
coefficients are reduced through the formal quadratic relation
`a^2 = t*a - 1`, and the resulting norm is evaluated at `t = 2 - 4s`.

The sole exceptional norm is `Phi_1`, whose norm is `4s`; this supplies the
one global factor `4` in the spread--Lucas identity.  Cancellation is done
only over the constructive rationals, after which the resulting integer
coefficient identity is transported to every explicitly supplied field,
including finite characteristic.
-/

namespace Purelib.Polynomial.Ascending.Integer.Products.ExerciseEightThirteen.IntegerPolynomial

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

/-- Evaluation of a `Fin`-indexed coefficient product respects pointwise
equality, even when its two sides are evaluated at different points. -/
theorem
  eval_coefficientProductFin_congr
  : ∀ (count : Nat)
    (left right : Fin count → List Int) (leftPoint rightPoint : K),
    (∀ index, Ascending.Integer.Basic.eval (left index) leftPoint =
      Ascending.Integer.Basic.eval (right index) rightPoint) →
    Ascending.Integer.Basic.eval (Dense.Rational.FiniteProduct.Integer.coefficientProductFin count left)
        leftPoint =
      Ascending.Integer.Basic.eval (Dense.Rational.FiniteProduct.Integer.coefficientProductFin count right)
        rightPoint
  | 0, left, right, leftPoint, rightPoint, pointwise => by
      simp only [Dense.Rational.FiniteProduct.Integer.coefficientProductFin_zero,
        Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil, Int.cast_one, mul_zero, add_zero, -eq_self,
          -iff_self] ; rfl
  | count + 1, left, right, leftPoint, rightPoint, pointwise => by
      rw [Dense.Rational.FiniteProduct.Integer.coefficientProductFin_succ,
        Dense.Rational.FiniteProduct.Integer.coefficientProductFin_succ,
        Ascending.Integer.Basic.eval_mul, Ascending.Integer.Basic.eval_mul,

          eval_coefficientProductFin_congr
          count
          (fun index => left index.castSucc)
          (fun index => right index.castSucc) leftPoint rightPoint
          (fun index => pointwise index.castSucc),
        pointwise (Fin.last count)]
end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.Polynomial.Ascending.Integer.Products.ExerciseEightThirteen.IntegerPolynomial

end

section
@[expose] public section

/-!
# Executable torus-knot genus and Alexander data

This file supplies finite integer-polynomial and positive-braid surface
certificates for the torus family.  Polynomial coefficients are stored in
low-to-high order.  Equality is coefficientwise over one explicit finite
bound, so concrete certificates reduce by kernel computation.

The Alexander candidate uses the numerical semigroup generated by `p` and
`q`: below the conductor `(p-1)(q-1)`, its coefficient at `n` is the change
in the semigroup-membership indicator from `n-1` to `n`.  A certificate checks
the familiar exact identity

`Delta(t) (1-t^p) (1-t^q) = (1-t^(pq)) (1-t)`.

No completed Laurent series or quotient field is constructed.
-/

namespace Purelib.Polynomial.Ascending.Integer.Products

/-! ## Finite integer polynomials -/

section IntPolynomial

/-- Place the integer coefficient at its requested degree after a finite zero prefix. -/
def TorusInvariants.monomial (degree : Nat) (coefficient : Int) :
  (List Int) :=
  List.replicate degree 0 ++ [coefficient]

/-- Construct the ascending integer table for `1 - X^exponent`. -/
def oneSubPower (exponent : Nat) : (List Int) :=
  Ascending.Integer.Basic.TorusInvariants.add [1] (Ascending.Integer.Products.TorusInvariants.monomial exponent (-1))
end IntPolynomial
end Purelib.Polynomial.Ascending.Integer.Products

end
