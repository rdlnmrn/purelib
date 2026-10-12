module
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Coefficientwise
public import Purelib.Polynomial.Ascending.Rational.Monomial

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

section
public section

/-! Polynomial Ascending Rational Geometric and its finite structural certificates. -/

namespace Purelib.Polynomial.Ascending.Rational.Geometric

open Purelib.Polynomial

/-- Construct the finite polynomial `1 + 2x + … + 2x^degree`.

The recursive table retains a constant coefficient of one and adds a coefficient-two monomial at each positive degree.
-/
@[expose] public def geometricPrefix : Nat → Ascending.Rational.Basic.CoefficientPolynomial
  | 0 => Ascending.Rational.Basic.constant 1
  | degree + 1 => Ascending.Rational.Basic.add (Purelib.Polynomial.Ascending.Rational.Geometric.geometricPrefix degree)
    (Ascending.Rational.Monomial.monomial (degree + 1) 2)

/-- The geometric prefix has coefficient one at zero and two through its positive degree bound.

All coefficients above the displayed prefix degree vanish. -/
theorem geometricPrefix_coefficient : ∀ prefixDegree degree,
    Ascending.Rational.Basic.coefficient (Ascending.Rational.Geometric.geometricPrefix prefixDegree) degree =
      if degree = 0 then 1 else if degree ≤ prefixDegree then 2 else 0
  | 0, degree => by
      rw [Ascending.Rational.Geometric.geometricPrefix,
        Purelib.Polynomial.Ascending.Rational.Coefficientwise.coefficient_constant]
      by_cases zero : degree = 0
      · subst degree
        rewrite [if_pos (Eq.refl 0), if_pos (Eq.refl 0)]
        exact Eq.refl _
      · rewrite [if_neg zero, if_neg zero]
        rw [if_neg (fun degreeLeZero =>
          zero (Nat.eq_zero_of_le_zero degreeLeZero))]
  | prefixDegree + 1, degree => by
      rw [Ascending.Rational.Geometric.geometricPrefix, Ascending.Rational.Basic.coefficient_add,
        Purelib.Polynomial.Ascending.Rational.Geometric.geometricPrefix_coefficient prefixDegree degree,
        Ascending.Rational.Monomial.coefficient_monomial]
      by_cases zero : degree = 0
      · subst degree
        rewrite [if_pos (Eq.refl 0), if_pos (Eq.refl 0)]
        rw [if_neg ((fun impossible => Nat.noConfusion impossible))]
        ring1
      · rewrite [if_neg zero, if_neg zero]
        by_cases inside : degree ≤ prefixDegree
        · have notFinal : degree ≠ prefixDegree + 1 := by
            intro final
            subst degree
            exact (Nat.not_succ_le_self prefixDegree) inside
          rw [if_pos inside, if_neg notFinal,
            if_pos (inside.trans (Nat.le_succ prefixDegree))]
          ring1
        · by_cases final : degree = prefixDegree + 1
          · subst degree
            rw [if_neg inside, if_pos rfl,
              if_pos (Nat.le_refl _)]
            ring1
          · have beyond : ¬degree ≤ prefixDegree + 1 := by
              intro degreeLe
              exact inside (Nat.le_of_lt_succ
                (Nat.lt_of_le_of_ne degreeLe final))
            rw [if_neg inside, if_neg final, if_neg beyond]
            ring1
end Purelib.Polynomial.Ascending.Rational.Geometric

end
