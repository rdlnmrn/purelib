module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Arithmetic
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Pair.NoCommonZero

import Mathlib.Data.List.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Signed Euclidean chains over constructive fractions

This is the finite Sturm/Cauchy-index kernel for the constructive coordinate
model.  The chain terminates by the direct coefficient-list descent proved in
`Purelib.Algebra.Polynomial`; no sparse polynomial or root set is involved.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Evaluation

/-- Exact Horner identity for one signed remainder step. -/
theorem signedStep_eval_identity (p q :
  Dense.Rational.Basic.CoordinatePolynomial) (x : Fraction.Rational) :
    p.eval x = q.eval x * (DensePolynomial.divMod p q).quotient.eval x -
      (-((DensePolynomial.divMod p q).remainder)).eval x := by
  have h := DensePolynomial.divMod_eval_equation p q x
  rw [DensePolynomial.eval_neg]
  calc
    p.eval x = (DensePolynomial.divMod p q).remainder.eval x +
        q.eval x * (DensePolynomial.divMod p q).quotient.eval x := h.symm
    _ = q.eval x * (DensePolynomial.divMod p q).quotient.eval x -
        -((DensePolynomial.divMod p q).remainder.eval x) := by ring1

/-- No-common-zero data descends through one signed Euclidean step. -/
theorem noCommonZero_signedStep {p q :
  Dense.Rational.Basic.CoordinatePolynomial}
    (coprime : Polynomial.Dense.Rational.Pair.NoCommonZero p q) :
    Polynomial.Dense.Rational.Pair.NoCommonZero q (-((DensePolynomial.divMod p q).remainder)) := by
  intro x
  by_cases hq : q.eval x = 0
  · right
    intro hnext
    have hstep := signedStep_eval_identity p q x
    have hp : p.eval x = 0 := by
      rw [hq, hnext, zero_mul, zero_sub] at hstep
      exact hstep
    rcases coprime x with hpNe | hqNe
    · exact hpNe hp
    · exact hqNe hq
  · exact Or.inl hq
end Purelib.Polynomial.Dense.Rational.SignedRemainder.Evaluation

end
