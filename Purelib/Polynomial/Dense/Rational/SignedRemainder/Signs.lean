module

import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Sign.Variation
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Pair.NoCommonZero
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Evaluation
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Bool.Decide

/-!
# Endpoint nonvanishing and adjacency of retained signed chains

The original signed division recursion retains each polynomial and its
coefficient-count descent. Pointwise non-common-zero certificates propagate
the same endpoint nonvanishing through its finite chain.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs

open Purelib.Data.Rat
open Purelib.Data.Bool
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Basic renaming CoordinatePolynomial -> Dense
open Purelib.Polynomial.Dense.Rational
open _root_.Purelib.Polynomial.Dense.Rational.Pair (NoCommonZero)

/-- The terminal evaluation of a non-common-zero signed polynomial pair is nonzero.

The second polynomial passes its retained nonzero test, and neither pair
vanishes together at the evaluation point. Each signed division step preserves
that pointwise condition while its remainder coefficient count strictly drops. -/
public theorem terminalValue_signedRemainderChain_eval_ne_zero
    {p q : Dense} (hq : q.isZero = false)
    (coprime : NoCommonZero p q) (x : Fraction.Rational) {tail : List Dense}
    (hchain : SignedRemainder.Basic.Sturm.signedRemainderChain p q = p :: tail) :
    Sign.Variation.terminalValue (p.eval x) (tail.map fun r => r.eval x) ≠ 0 := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q tail with
  | h n ih =>
      have qNotTrue : q.isZero ≠ true := by
        intro qTrue
        exact Bool.noConfusion (hq.symm.trans qTrue)
      rewrite [SignedRemainder.Basic.Sturm.signedRemainderChain,
        SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq,
        if_neg qNotTrue] at hchain
      dsimp only at hchain
      by_cases remainderTrue : (DensePolynomial.divMod p q).remainder.isZero = true
      · rewrite [if_pos remainderTrue] at hchain
        have htail : tail = [q] := by
          have tails := congrArg List.tail hchain
          change [q] = tail at tails
          exact tails.symm
        subst tail
        change q.eval x ≠ 0
        intro qZeroAtX
        have step := SignedRemainder.Evaluation.signedStep_eval_identity p q x
        have remainderZeroAtX := DensePolynomial.eval_eq_zero_of_isZero remainderTrue x
        rewrite [qZeroAtX, DensePolynomial.eval_neg, remainderZeroAtX,
          neg_zero, zero_mul, Fraction.Arithmetic.sub_eq_add_neg_direct,
          neg_zero, add_zero] at step
        rcases coprime x with pNonzeroAtX | qNonzeroAtX
        · exact pNonzeroAtX step
        · exact qNonzeroAtX qZeroAtX
      · rewrite [if_neg remainderTrue] at hchain
        let next := -((DensePolynomial.divMod p q).remainder)
        have remainderFalse := Decide.bool_eq_false_of_not_eq_true
          (DensePolynomial.divMod p q).remainder.isZero remainderTrue
        have nextFalse : next.isZero = false := by
          rewrite [DensePolynomial.isZero_neg]
          exact remainderFalse
        have nextCoprime : NoCommonZero q next :=
          SignedRemainder.Evaluation.noCommonZero_signedStep coprime
        have count : next.degreeCount < n := by
          dsimp only [next]
          rewrite [DensePolynomial.degreeCount_neg, ← hn]
          exact DensePolynomial.divMod_remainder_degreeCount_lt p q hq
        have htail : tail = SignedRemainder.Basic.Sturm.signedRemainderChain q next := by
          have tails := congrArg List.tail hchain
          change SignedRemainder.Basic.Sturm.signedRemainderChain q next = tail at tails
          exact tails.symm
        obtain ⟨recursiveTail, recursiveChain⟩ :=
          SignedRemainder.Basic.signedRemainderChain_eq_cons q next
        rewrite [htail, recursiveChain]
        change Sign.Variation.terminalValue (q.eval x)
          (recursiveTail.map fun r => r.eval x) ≠ 0
        exact ih next.degreeCount count nextFalse nextCoprime recursiveChain rfl

/-- The evaluated signed remainder chain has no adjacent zero entries.

The two initial polynomials must not vanish simultaneously at the evaluation
point. Signed division preserves this pointwise condition, and finite descent
propagates it along the same emitted polynomial chain. -/
public theorem noAdjacentZero_signedRemainderChain {p q : Dense}
    (coprime : NoCommonZero p q) (x : Fraction.Rational) :
    Sign.Variation.NoAdjacentZero ((SignedRemainder.Basic.Sturm.signedRemainderChain p q).map fun r => r.eval x) := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      rewrite [SignedRemainder.Basic.Sturm.signedRemainderChain,
        SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq]
      by_cases qTrue : q.isZero = true
      · rewrite [if_pos qTrue]
        exact True.intro
      · have qFalse := Decide.bool_eq_false_of_not_eq_true q.isZero qTrue
        rewrite [if_neg qTrue]
        dsimp only
        by_cases remainderTrue : (DensePolynomial.divMod p q).remainder.isZero = true
        · rewrite [if_pos remainderTrue]
          change (p.eval x ≠ 0 ∨ q.eval x ≠ 0) ∧ True
          exact ⟨coprime x, True.intro⟩
        · rewrite [if_neg remainderTrue]
          let next := -((DensePolynomial.divMod p q).remainder)
          have nextCoprime : NoCommonZero q next :=
            SignedRemainder.Evaluation.noCommonZero_signedStep coprime
          have count : next.degreeCount < n := by
            dsimp only [next]
            rewrite [DensePolynomial.degreeCount_neg, ← hn]
            exact DensePolynomial.divMod_remainder_degreeCount_lt p q qFalse
          have recursive := ih next.degreeCount count (p := q) (q := next) nextCoprime rfl
          obtain ⟨tail, chain⟩ := SignedRemainder.Basic.signedRemainderChain_eq_cons q next
          rewrite [chain] at recursive
          change Sign.Variation.NoAdjacentZero
            (p.eval x :: (SignedRemainder.Basic.Sturm.signedRemainderChain q next).map fun r => r.eval x)
          rewrite [chain]
          change (p.eval x ≠ 0 ∨ q.eval x ≠ 0) ∧
            Sign.Variation.NoAdjacentZero (q.eval x :: tail.map fun r => r.eval x)
          exact ⟨coprime x, recursive⟩

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs
