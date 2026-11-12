module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.Quadratic.TracePair.Basic
public import Purelib.Algebra.Quadratic.TracePair.Norm
import Purelib.Algebra.Quadratic.TracePair.Power
import Purelib.Polynomial.Ascending.Integer.Basic
public import Purelib.Polynomial.Ascending.Integer.PowerMinusOne
public import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Evaluation
import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Evaluation.PowerMinusOne
public import Purelib.Polynomial.Recurrence.Lucas.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Field

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# A finite quadratic trace norm on integer coefficient lists

For a displayed trace parameter `t`, let `a` satisfy
`a² = t*a - 1`.  Every integer polynomial in `a` reduces to a pair
`A(t) + B(t)*a`; its conjugate norm is
`A² + t*A*B + B²`.  All coefficient programs below are primitive
recursions on finite `List Int` values.
-/

namespace Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Reduction

section IntegerPolynomial

/-- Coefficient-level reduction to `A(t)+B(t)*a`. -/
def IntegerPolynomial.reduce : List Int → List Int
  × List Int
  | [] => ([], [])
  | coefficient :: remaining =>
      let recursive := IntegerPolynomial.reduce remaining
      (Basic.sub [coefficient] recursive.2,
        Basic.Certificate.add recursive.1 (Basic.Certificate.mul [0, 1]
          recursive.2))

/-- The empty polynomial reduces to two empty quadratic-coordinate tables. -/
@[simp] theorem IntegerPolynomial.reduce_nil :
  IntegerPolynomial.reduce [] = ([], []) := rfl

/-- Reduce a head and tail using the formal relation `a² = t*a - 1`.

The scalar table subtracts the tail generator part from the head, and the generator table adds the tail scalar part to
the trace times its generator part. -/
@[simp] theorem IntegerPolynomial.reduce_cons
  (coefficient : Int) (remaining : List Int) :
    IntegerPolynomial.reduce (coefficient :: remaining) =
      (Basic.sub [coefficient] (IntegerPolynomial.reduce
        remaining).2,
        Basic.Certificate.add (IntegerPolynomial.reduce
          remaining).1 (Basic.Certificate.mul [0, 1]
          (IntegerPolynomial.reduce remaining).2)) := rfl

/-- The two reduced integer polynomials evaluate to the formal quadratic scalar and generator coordinates.

This links the finite coefficient-level reduction with evaluation in every supplied explicit field at the displayed
trace. -/
theorem IntegerPolynomial.eval_reduce {K : Type*}
  [ExplicitField K] :
    ∀ coefficients : List Int, ∀ trace : K,
    Basic.eval (IntegerPolynomial.reduce coefficients).1
      trace =
        (TracePair.eval coefficients trace).scalar ∧
      Basic.eval (IntegerPolynomial.reduce coefficients).2
        trace =
        (TracePair.eval coefficients trace).generator
  | [], trace => by
      constructor <;> simp only [-eq_self, -iff_self,
        IntegerPolynomial.reduce,
        TracePair.eval, TracePair.zero,
        Basic.eval_nil] <;> rfl
  | coefficient :: remaining, trace => by
      have recursive := IntegerPolynomial.eval_reduce
        remaining trace
      rw [IntegerPolynomial.reduce_cons, Basic.eval_sub,
        Basic.eval_add, Basic.eval_mul,
        recursive.1, recursive.2, TracePair.eval_cons]
      constructor <;> simp only [-eq_self, -iff_self, Basic.eval_cons,
        Basic.eval_nil, Algebra.Ring.IntCast.cast_zero, Int.cast_one, mul_zero,
        add_zero, zero_add, mul_one] <;> rfl

/-- Integer trace-norm coefficients `A²+tAB+B²`. -/
def IntegerPolynomial.normCoefficients
  (coefficients : List Int) : List Int :=
  let reduced := IntegerPolynomial.reduce coefficients
  Basic.Certificate.add (Basic.Certificate.add
    (Basic.Certificate.mul reduced.1 reduced.1)
      (Basic.Certificate.mul [0, 1] (Basic.Certificate.mul reduced.1 reduced.2)))
    (Basic.Certificate.mul reduced.2 reduced.2)

/-- The reduced norm coefficient table evaluates to the quadratic norm of the formal polynomial value.

For coordinates `A` and `B` at trace `t`, both sides compute `A² + t*A*B + B²`. -/
theorem IntegerPolynomial.eval_normCoefficients {K
  : Type*} [ExplicitField K]
    (coefficients : List Int) (trace : K) :
    Basic.eval (IntegerPolynomial.normCoefficients
      coefficients) trace =
      TracePair.norm trace (TracePair.eval
        coefficients trace) := by
  unfold IntegerPolynomial.normCoefficients
  rw [Basic.eval_add, Basic.eval_add, Basic.eval_mul,
    Basic.eval_mul, Basic.eval_mul, Basic.eval_mul,
    (IntegerPolynomial.eval_reduce coefficients trace).1,
    (IntegerPolynomial.eval_reduce coefficients trace).2]
  simp only [Basic.eval_cons, Basic.eval_nil, Algebra.Ring.IntCast.cast_zero,
    Int.cast_one, mul_zero,
    add_zero, zero_add, mul_one, TracePair.norm]
  ring0

/-- The finite trace norm is multiplicative. -/
theorem IntegerPolynomial.eval_normCoefficients_mul
  {K : Type*} [ExplicitField K]
    (left right : List Int) (trace : K) :
    Basic.eval (IntegerPolynomial.normCoefficients
      (Basic.Certificate.mul left right)) trace =
      Basic.eval (IntegerPolynomial.normCoefficients left)
        trace *
        Basic.eval (IntegerPolynomial.normCoefficients
          right) trace := by
  rw [IntegerPolynomial.eval_normCoefficients,
    TracePair.eval_mul, TracePair.norm_mul,
    ← IntegerPolynomial.eval_normCoefficients, ←
      IntegerPolynomial.eval_normCoefficients]

/-- The quadratic norm of `X^degree - 1` evaluates to two minus the Lucas trace polynomial. -/
theorem
  IntegerPolynomial.eval_norm_powerMinusOneCoefficients
    {K : Type*} [ExplicitField K] (degree : Nat) (trace : K) :
    Basic.eval (IntegerPolynomial.normCoefficients
      (PowerMinusOne.IntegerPolynomial.powerMinusOneCoefficients degree)) trace =
      2 - TracePair.lucas degree trace := by
  rw [IntegerPolynomial.eval_normCoefficients,
    Evaluation.PowerMinusOne.IntegerPolynomial.eval_powerMinusOneCoefficients_pair,
    TracePair.norm_alphaPower_sub_one]

end IntegerPolynomial

end Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Reduction

end
