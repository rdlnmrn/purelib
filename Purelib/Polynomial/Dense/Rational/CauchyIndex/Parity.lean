module
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Pair.NoCommonZero
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation

import Mathlib.Data.List.Basic
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Even
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring

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

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Parity

/-- A coprime displayed pair has Cauchy-index parity equal to the difference
of its denominator-coordinate endpoint-zero flags. -/
theorem cauchyIndex2_sub_secondZeroFlags_even
    {p q : Dense.Rational.Basic.CoordinatePolynomial} (coprime : Polynomial.Dense.Rational.Pair.NoCommonZero p q) (a b
      :
      Fraction.Rational) :
    Even (Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2 p q a b -
      ((if q.eval a = 0 then 1 else 0) -
        (if q.eval b = 0 then 1 else 0))) := by
  by_cases pZero : p.isZero = true
  · have pa := Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero pZero a
    have pb := Dense.Basic.DensePolynomial.eval_eq_zero_of_isZero pZero b
    have qa : q.eval a ≠ 0 := (coprime a).resolve_left (fun nonzero => nonzero pa)
    have qb : q.eval b ≠ 0 := (coprime b).resolve_left (fun nonzero => nonzero pb)
    have variationA : Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
        (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain q p) a = 0 := by
      unfold Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
      rewrite [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain,
        Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq, if_pos pZero]
      rfl
    have variationB : Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
        (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain q p) b = 0 := by
      unfold Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
      rewrite [Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain,
        Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq, if_pos pZero]
      rfl
    refine ⟨0, ?_⟩
    unfold Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
    rewrite [variationA, variationB, if_neg qa, if_neg qb]
    rfl
  · have pNonzero : p.isZero = false := by
      cases decision : p.isZero with
      | false => rfl
      | true => exact (pZero decision).elim
    have reverseCoprime : Polynomial.Dense.Rational.Pair.NoCommonZero q p := fun x => (coprime x).symm
    have atA := Dense.Rational.SignedRemainder.Variation.endpointVariation2_sub_firstZeroFlag_even
      pNonzero reverseCoprime a
    have atB := Dense.Rational.SignedRemainder.Variation.endpointVariation2_sub_firstZeroFlag_even
      pNonzero reverseCoprime b
    rcases atA with ⟨leftHalf, leftIdentity⟩
    rcases atB with ⟨rightHalf, rightIdentity⟩
    refine ⟨leftHalf - rightHalf, ?_⟩
    simp only [Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2]
    calc
      (Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
        (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain q p) a : Int) -
            Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
              (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain q p) b -
          ((if q.eval a = 0 then 1 else 0) -
            (if q.eval b = 0 then 1 else 0)) =
          ((Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
            (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain q p) a : Int) -
              (if q.eval a = 0 then 1 else 0)) -
            ((Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2
              (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain q p) b : Int) -
              (if q.eval b = 0 then 1 else 0)) := by ring1
      _ = (leftHalf + leftHalf) - (rightHalf + rightHalf) := by
        rw [leftIdentity, rightIdentity]
      _ = (leftHalf - rightHalf) + (leftHalf - rightHalf) := by ring1
end Purelib.Polynomial.Dense.Rational.CauchyIndex.Parity

end
