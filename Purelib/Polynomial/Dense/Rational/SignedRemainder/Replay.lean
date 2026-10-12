module
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic

import Purelib.Data.Rat.Fraction.Field
public import Purelib.Polynomial.Dense.Rational.Division.Replay
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Polynomial

public section

/-!
# Replay of the original finite signed remainder chain

Saved quotients and remainders are untrusted witnesses. Coefficient identities
and strict degree descent identify each remainder with the original division
result, without executing long division during reload. The extra dependency
proves uniqueness on an explicit finite rational grid; it uses no infinite
root set or choice-derived witnesses.
-/

namespace Purelib.Polynomial.Dense.Rational

open Purelib.Polynomial.Dense.Basic.DensePolynomial

/-- The negated saved remainder has smaller degree count than a nonzero divisor. -/
theorem Division.Replay.Step.small {p q :
  CoordinatePolynomial}
  (step : Dense.Rational.Division.Replay.Step p q) (nonzero : q.isZero = false) :
    (-step.witness.remainder).degreeCount < q.degreeCount := by
  rw [Dense.Basic.DensePolynomial.degreeCount_neg, step.equation]
  exact Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt p q nonzero

/-- A zero second polynomial terminates the signed remainder chain at the first polynomial. -/
theorem SignedRemainder.Replay.terminal (p q :
  CoordinatePolynomial) (zero : q.isZero = true) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q = [p] := by
  rw [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain,
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq]
  rw [if_pos zero]

/-- A verified saved division step prepends the original dividend to its exact signed-chain tail. -/
theorem Division.Replay.Step.prepend {p q :
  CoordinatePolynomial}
  (step : Dense.Rational.Division.Replay.Step p q) (nonzero : q.isZero = false)
    (tail : List CoordinatePolynomial)
    (tail_eq : tail = Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain q (-step.witness.remainder)) :
    p :: tail = Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q := by
  rw [Dense.Rational.SignedRemainder.Basic.signedRemainderChain_step_of_second_nonzero p q nonzero,
    tail_eq, step.equation]

end Purelib.Polynomial.Dense.Rational

end
