module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial
import Purelib.Approximation.Rat.Exponential.Taylor.Bounds
import Purelib.Data.Nat.Factorial.Basic
public import Purelib.Data.Rat.Geometric.TwoThird
import Purelib.Polynomial.Ascending.Rational.Evaluation

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Order.Arithmetic

section
public section

/-! Approximation Gaussian Exponential Taylor Polynomial Majorant and its finite structural certificates. -/

namespace Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial.Majorant

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Exponential.Taylor
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Data.Rat.Geometric
open Purelib.Polynomial.Ascending.Rational

/-- The finite exponential polynomial at a rational input in the interval from zero to four thirds is bounded by one
plus the matching two-thirds geometric sum. -/
theorem scalarEval_exponential_le {value : Fraction.Rational}
    (nonnegative : 0 ≤ value) (upper : value ≤ 4 / 3) : ∀ depth,
    Evaluation.scalarEval value (Polynomial.exponential depth) ≤ 1 + TwoThird.twoThirdSum depth
  | 0 => by rw [Polynomial.exponential, Evaluation.scalarEval_constant, TwoThird.twoThirdSum]; exact le_rfl
  | depth + 1 => by
      rw [Polynomial.exponential_succ, Evaluation.scalarEval_add, Evaluation.scalarEval_monomial, TwoThird.twoThirdSum]
      calc
        Evaluation.scalarEval value (Polynomial.exponential depth) +
            (1 / (Factorial.Basic.factorial
              (depth + 1) : Fraction.Rational)) * value ^ (depth + 1) ≤
          (1 + TwoThird.twoThirdSum depth) +
            2 * (2 / 3 : Fraction.Rational) ^ (depth + 1) :=
          add_le_add
            (Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial.Majorant.scalarEval_exponential_le nonnegative
              upper depth)
            (Rat.Exponential.Taylor.Bounds.scalarExponentialTerm_bound nonnegative upper depth)
        _ = 1 +
            (TwoThird.twoThirdSum depth +
              2 * (2 / 3 : Fraction.Rational) ^ (depth + 1)) := by ring1

/-- Every finite exponential polynomial at a rational input between zero and four thirds is at most five. -/
theorem scalarEval_exponential_le_five {value : Fraction.Rational}
    (nonnegative : 0 ≤ value) (upper : value ≤ 4 / 3) (depth : Nat) :
    Evaluation.scalarEval value (Polynomial.exponential depth) ≤ 5 :=
  (Approximation.Gaussian.Exponential.Taylor.Polynomial.Majorant.scalarEval_exponential_le nonnegative upper
    depth).trans (by
    have sumBound := TwoThird.twoThirdSum_le_four depth
    calc
      (1 : Fraction.Rational) + TwoThird.twoThirdSum depth ≤ 1 + 4 :=
        add_le_add le_rfl sumBound
      _ = 5 := by decide)
end Purelib.Approximation.Gaussian.Exponential.Taylor.Polynomial.Majorant

end
