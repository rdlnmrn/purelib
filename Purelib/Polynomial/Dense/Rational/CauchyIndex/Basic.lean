module

import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

/-!
# Doubled Cauchy indices of retained polynomial pairs

The difference of the two original finite endpoint variations determines
the doubled Cauchy index. Normalization, conjugation and endpoint composition
retain the same polynomial pairs and endpoint observations.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic

open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Basic renaming CoordinatePolynomial -> Dense
open Purelib.Polynomial.Dense.Rational
open Purelib.Algebra

/-- Compute the doubled Cauchy index from the two endpoint variations.

The signed remainder chain starts with the displayed denominator and numerator
polynomials. Its doubled variation at the second endpoint is subtracted from
its reading at the first, preserving both input polynomials and endpoint order. -/
@[expose] public def Sturm.cauchyIndex2 (p q : Dense) (a b : Fraction.Rational) : Int :=
  (SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain q p) a : Int) -
    SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain q p) b

/-- Normalizing both polynomials preserves their doubled Cauchy index.

Both endpoint variation certificates apply to the same reversed input pair.
Their exact natural readings therefore identify the retained integer difference
at the original two rational endpoints. -/
public theorem cauchyIndex2_normalize (p q : Dense) (a b : Fraction.Rational) :
    Sturm.cauchyIndex2 p.normalize q.normalize a b = Sturm.cauchyIndex2 p q a b := by
  unfold Sturm.cauchyIndex2
  rw [SignedRemainder.Variation.endpointVariation2_signedRemainderChain_normalize,
    SignedRemainder.Variation.endpointVariation2_signedRemainderChain_normalize]

/-- Negating the denominator negates the doubled Cauchy index.

The input pair must not vanish together at either displayed endpoint. The
endpoint-independent complementary variation sum and simultaneous-negation
certificates retain the same normalized polynomial pair and scalar readings. -/
public theorem cauchyIndex2_neg_denominator
    {p q : Dense} {a b : Fraction.Rational}
    (pairAtA : p.eval a ≠ 0 ∨ q.eval a ≠ 0)
    (pairAtB : p.eval b ≠ 0 ∨ q.eval b ≠ 0) :
    Sturm.cauchyIndex2 p (-q) a b = -Sturm.cauchyIndex2 p q a b := by
  rw [← cauchyIndex2_normalize p (-q) a b,
    ← cauchyIndex2_normalize p q a b]
  rw [DensePolynomial.normalize_neg, ← DensePolynomial.neg_normalize q]
  let P := p.normalize
  let Q := q.normalize
  have pNormalized : P.normalize = P := DensePolynomial.normalize_normalize p
  have normalizedAtA : Q.eval a ≠ 0 ∨ P.eval a ≠ 0 := by
    simpa only [P, Q, DensePolynomial.eval_normalize] using pairAtA.symm
  have normalizedAtB : Q.eval b ≠ 0 ∨ P.eval b ≠ 0 := by
    simpa only [P, Q, DensePolynomial.eval_normalize] using pairAtB.symm
  have variationSum := SignedRemainder.Variation.endpointVariation2_neg_second_sum_eq
    normalizedAtA normalizedAtB
  have negAtA := SignedRemainder.Variation.endpointVariation2_signedRemainderChain_neg Q (-P) a
  have negAtB := SignedRemainder.Variation.endpointVariation2_signedRemainderChain_neg Q (-P) b
  rw [DensePolynomial.neg_neg,
    pNormalized] at negAtA negAtB
  change Sturm.cauchyIndex2 P (-Q) a b = -Sturm.cauchyIndex2 P Q a b
  unfold Sturm.cauchyIndex2
  rw [negAtA, negAtB]
  have variationSumInt :=
    congrArg (fun value : Nat => (value : Int)) variationSum
  rewrite [NatCast.add, NatCast.add] at variationSumInt
  calc
    (SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q (-P)) a :
      Int) -
          SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q (-P)) b
            =
        ((SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q P) a :
          Int) +
            SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q (-P))
              a) -
          ((SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q P) a
            : Int) +
            SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q (-P))
              b) := by ring1
    _ = ((SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q P) b :
      Int) +
            SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q (-P))
              b) -
          ((SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q P) a
            : Int) +
            SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q (-P))
              b) := by
        rw [variationSumInt]
    _ = -((SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q P) a :
      Int) -
          SignedRemainder.Variation.Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain Q P) b)
            := by ring1

/-- Doubled Cauchy indices add across any intermediate endpoint.

The same chain supplies both occurrences of the intermediate variation. They
cancel in the exact integer difference, with no ordering assumption on the
three displayed rational endpoints. -/
public theorem cauchyIndex2_add (p q : Dense) (a b c : Fraction.Rational) :
    Sturm.cauchyIndex2 p q a c = Sturm.cauchyIndex2 p q a b + Sturm.cauchyIndex2 p q b c := by
  simp only [Sturm.cauchyIndex2]
  ring1

/-- Reversing the endpoints negates the doubled Cauchy index.

The same polynomial chain retains both endpoint variation readings. Reversing
their subtraction identifies the additive inverse of the original integer
reading without changing either polynomial or endpoint evaluation. -/
public theorem cauchyIndex2_reverse (p q : Dense) (a b : Fraction.Rational) :
    Sturm.cauchyIndex2 p q b a = -Sturm.cauchyIndex2 p q a b := by
  simp only [Sturm.cauchyIndex2]
  ring1

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
