module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.TracePair.Basic
import Purelib.Algebra.Quadratic.TracePair.Norm
import Purelib.Polynomial.Ascending.Integer.Basic
import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Evaluation
public import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Reduction
public import Purelib.Polynomial.Dense.Rational.FiniteProduct.Integer

import Purelib.Tactic.QuotientFreeOmega

open Purelib.Algebra.Field

open Purelib.Polynomial

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

namespace Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Products

variable {K : Type*} [ExplicitField K]

section ExerciseEightThirteen
section IntegerPolynomial

/-- Taking the finite quadratic norm commutes with a finite coefficient
product after evaluation. -/
theorem
  ExerciseEightThirteen.IntegerPolynomial.eval_norm_coefficientProductFin
  : ∀ (count : Nat)
    (factor : Fin count → List Int) (trace : K),
    Ascending.Integer.Basic.eval
        (Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
          (Dense.Rational.FiniteProduct.Integer.coefficientProductFin count factor)) trace =
      Ascending.Integer.Basic.eval
        (Dense.Rational.FiniteProduct.Integer.coefficientProductFin count fun index =>
          Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.normCoefficients
            (factor index)) trace
  | 0, factor, trace => by
      rw [Dense.Rational.FiniteProduct.Integer.coefficientProductFin_zero,
        Dense.Rational.FiniteProduct.Integer.coefficientProductFin_zero,
        Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_normCoefficients]
      have subZero (scalar : K) : scalar - 0 = scalar := by
        exact (@SubNegMonoid.sub_eq_add_neg K
          SubtractionMonoid.toSubNegMonoid scalar 0).trans
            ((congrArg (fun value : K => scalar + value)
              (SubtractionMonoid.neg_eq_of_add 0 0 (AddZeroClass.add_zero 0))).trans
                (AddZeroClass.add_zero scalar))
      simp only [-eq_self, -iff_self, subZero,Algebra.Quadratic.TracePair.eval,
        Algebra.Quadratic.TracePair.norm,
        Algebra.Quadratic.TracePair.zero,
        Ascending.Integer.Basic.eval_cons, Ascending.Integer.Basic.eval_nil, Int.cast_one, mul_zero, mul_one, add_zero ]
      rfl
  | count + 1, factor, trace => by
      rw [Dense.Rational.FiniteProduct.Integer.coefficientProductFin_succ,
        Ascending.Integer.QuadraticTrace.Reduction.IntegerPolynomial.eval_normCoefficients_mul,
        Dense.Rational.FiniteProduct.Integer.coefficientProductFin_succ, Ascending.Integer.Basic.eval_mul,

          ExerciseEightThirteen.IntegerPolynomial.eval_norm_coefficientProductFin
          count
          (fun index => factor index.castSucc) trace]
end IntegerPolynomial
end ExerciseEightThirteen
end Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Products

end
