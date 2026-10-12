module
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Reduced
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.Pair.NoCommonZero
import Mathlib.Algebra.Group.Even
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Data.Int.Arithmetic

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced.Parity

/-- At a clear endpoint of the original denominator, the reduced signed
chain has even doubled variation. -/
theorem endpointVariation2_reducedChain_even
    {numerator denominator : Dense.Rational.Basic.CoordinatePolynomial}
    {parameter : Fraction.Rational} (clear : denominator.eval parameter ≠ 0) :
    Even ((Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
      (Dense.Rational.SignedRemainder.Reduced.reducedChain numerator denominator)
      parameter : Nat) : Int) := by
  have reducedDenominatorNonzero :
      (Dense.Rational.Pair.Reduction.reducedDenominator numerator denominator).eval parameter ≠ 0 :=
    Dense.Rational.Pair.Reduction.reducedDenominator_eval_ne_zero clear
  have coprime := (Dense.Rational.Pair.Reduction.reducedPairCoprime numerator denominator).eval_ne_zero
  cases numeratorZero : (Dense.Rational.Pair.Reduction.reducedNumerator numerator denominator).isZero with
  | true =>
      have chain : Dense.Rational.SignedRemainder.Reduced.reducedChain numerator denominator =
          [Dense.Rational.Pair.Reduction.reducedDenominator numerator denominator] := by
        rewrite [Dense.Rational.SignedRemainder.Reduced.reducedChain]
        unfold Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain
        rw [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq]
        rewrite [if_pos numeratorZero]
        rfl
      rw [chain]
      exact ⟨0, rfl⟩
  | false =>
      have parity := Dense.Rational.SignedRemainder.Variation.endpointVariation2_sub_firstZeroFlag_even
        numeratorZero coprime parameter
      rewrite [if_neg reducedDenominatorNonzero, Data.Int.Arithmetic.sub_zero] at parity
      exact parity

/-- Clear rational endpoints make the doubled reduced count even. -/
theorem reducedCauchyIndex2_even
    {numerator denominator : Dense.Rational.Basic.CoordinatePolynomial}
    {lower upper : Fraction.Rational}
    (lowerClear : denominator.eval lower ≠ 0)
    (upperClear : denominator.eval upper ≠ 0) :
    Even (Dense.Rational.CauchyIndex.Reduced.reducedCauchyIndex2 numerator denominator lower upper) := by
  rcases endpointVariation2_reducedChain_even lowerClear with
    ⟨left, leftEven⟩
  rcases endpointVariation2_reducedChain_even upperClear with
    ⟨right, rightEven⟩
  refine ⟨left - right, ?_⟩
  unfold Dense.Rational.CauchyIndex.Reduced.reducedCauchyIndex2 Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
  change
    (Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
      (Dense.Rational.SignedRemainder.Reduced.reducedChain numerator denominator) lower : Int) -
        Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
          (Dense.Rational.SignedRemainder.Reduced.reducedChain numerator denominator) upper =
      (left - right) + (left - right)
  rw [leftEven, rightEven]
  ring1
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced.Parity

end
