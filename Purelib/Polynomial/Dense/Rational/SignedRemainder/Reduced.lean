module
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Pair.Reduction
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Mathlib.Data.List.Basic

/-!
# Gcd-reduced rational signed chains

The original executable pair reduction supplies the numerator and denominator
of a signed remainder chain. Pointwise nonzero certificates retain each member
of the same chain and the original nonzero-denominator hypothesis.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Reduced

open Purelib.Data.Rat
open Purelib.Polynomial

public section

/-- Compute the signed chain of the gcd-reduced rational pair.

The executable pair reduction retains the denominator as the first chain
polynomial and numerator as the second. Their same reduced representations
supply the signed Euclidean recursion and its coefficient-count fuel. -/
@[expose] def reducedChain (numerator denominator : Dense.Rational.Basic.CoordinatePolynomial) : List
  (Dense.Basic.DensePolynomial Fraction.Rational) :=
  Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain (Dense.Rational.Pair.Reduction.reducedDenominator
    numerator denominator)
    (Dense.Rational.Pair.Reduction.reducedNumerator numerator denominator)

/-- Every polynomial in the reduced signed remainder chain is nonzero when the original denominator is nonzero.

If the reduced numerator vanishes, the chain consists only of the retained nonzero reduced denominator. -/
theorem reducedChain_all_nonzero
    {numerator denominator : Dense.Rational.Basic.CoordinatePolynomial}
    (denominatorNonzero : denominator.isZero = false) :
    ∀ polynomial ∈ Dense.Rational.SignedRemainder.Reduced.reducedChain numerator denominator,
      polynomial.isZero = false := by
  have reducedDenominatorNonzero :=
    Dense.Rational.Pair.Reduction.reducedDenominator_isZero_false (numerator := numerator)
      denominatorNonzero
  cases numeratorZero : (Dense.Rational.Pair.Reduction.reducedNumerator numerator denominator).isZero with
  | false =>
      exact Dense.Rational.SignedRemainder.Basic.signedRemainderChain_all_nonzero
        reducedDenominatorNonzero numeratorZero
  | true =>
      have chain : Dense.Rational.SignedRemainder.Reduced.reducedChain numerator denominator =
          [Dense.Rational.Pair.Reduction.reducedDenominator numerator denominator] := by
        unfold Dense.Rational.SignedRemainder.Reduced.reducedChain
          Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain
        rw [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq]
        rewrite [if_pos numeratorZero]
        exact Eq.refl _
      intro polynomial member
      rewrite [chain] at member
      cases member with
      | head => exact reducedDenominatorNonzero
      | tail _ impossible => nomatch impossible
end

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Reduced
