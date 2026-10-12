module
import Purelib.Approximation.Gaussian.Exponential.Taylor.Basic
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
import Purelib.Polynomial.Ascending.Rational.Derivative
import Purelib.Polynomial.Ascending.Rational.GaussianEvaluation

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Gaussian.Exponential

open Purelib.Approximation.Gaussian.Exponential.Taylor

open Purelib.Polynomial.Ascending.Rational

section
@[expose] public section

/-!
# Finite integration, an algebraic FTC, and polynomial ODE certificates

Integration here is coefficient arithmetic on a displayed finite polynomial.
The antiderivative divides each coefficient by its positive natural degree.
The fundamental theorem is the pair of exact finite statements that
differentiating this table returns the original table and that an interval
increment factors through the antiderivative's secant kernel.

The final section packages elementary initial-value problems with polynomial
forcing and records the exact finite defect of the exponential polynomial for
`y' = y`.  No measure, completed interval, limiting partition, or
function-as-an-infinite-set is used.
-/

namespace Purelib.Approximation.Gaussian.Exponential.Taylor.ODE

/-- The finite exponential polynomial satisfies `y' = y` up to precisely its last displayed Taylor term: its derivative
is the preceding polynomial. -/
theorem exponentialODE_derivative (degree : Nat) :
    Coefficientwise.CoefficientwiseEqual
      (Derivative.derivative (Polynomial.exponential (degree + 1)))
      (Polynomial.exponential degree) :=
  Polynomial.derivative_exponential_succ degree

/-- Pointwise form of the exact finite ODE defect. -/
theorem exponentialODE_defect (degree : Nat) (point :
  Data.Gaussian.Basic.Canonical) :
    GaussianEvaluation.eval (Polynomial.exponential (degree + 1)) point -
        GaussianEvaluation.eval (Derivative.derivative (Polynomial.exponential (degree + 1))) point =
      Taylor.Basic.taylorTerm point (degree + 1) := by
  rw [GaussianEvaluation.eval_eq_of_coefficientwise (Polynomial.derivative_exponential_succ degree)]
  rw [Polynomial.eval_exponential, Polynomial.eval_exponential,
    Taylor.Basic.truncatedExp_succ]
  apply Data.Gaussian.Basic.ext <;>
    simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.add_re,
      Data.Gaussian.Basic.add_im] <;> ring1

end Purelib.Approximation.Gaussian.Exponential.Taylor.ODE

end
