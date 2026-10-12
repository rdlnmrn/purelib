module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Sign.Basic
import Purelib.Data.Rat.Sign.Jump
public import Purelib.Data.Rat.Sign.Variation
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Pair.NoCommonZero
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Evaluation
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Even
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.Data.Bool.Decide

/-!
# Endpoint variation of retained signed Euclidean chains

The original chain and its endpoint evaluations determine doubled sign
variation. Direct finite branch readbacks compare normalization and negation,
while explicit integer witnesses retain endpoint parity.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation

open Purelib.Data.Rat
open Purelib.Data.Bool
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Rational.Basic renaming CoordinatePolynomial -> Dense
open Purelib.Polynomial.Dense.Rational
open _root_.Purelib.Polynomial.Dense.Rational.Pair (NoCommonZero)

/-- Measure doubled sign variation of a polynomial chain at one endpoint.

The displayed list retains its polynomial order. Evaluating each retained
polynomial at the same rational coordinate gives the finite list whose adjacent
integer-sign distances determine the natural variation reading. -/
@[expose] public def Sturm.endpointVariation2 (chain : List Dense) (x : Fraction.Rational) : Nat :=
  Sign.Variation.variation2 (chain.map fun p => p.eval x)

/-- A chain whose second polynomial is represented zero has zero endpoint variation.

The original zero test selects the singleton containing the first polynomial.
Its single retained evaluation has no adjacent sign change at any endpoint. -/
private theorem endpointVariation2_of_second_zero
    (p q : Dense) (qZero : q.isZero = true) (x : Fraction.Rational) :
    Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain p q) x = 0 := by
  unfold Sturm.endpointVariation2
  rewrite [SignedRemainder.Basic.Sturm.signedRemainderChain,
    SignedRemainder.Basic.Sturm.signedRemainderChainWF_eq, if_pos qZero]
  exact Eq.refl _

/-- An exposed signed division step contributes its first jump and its tail variation.

A represented nonzero second polynomial selects the same division step, including
the zero-remainder terminal case. The original next chain begins with that second
polynomial, so its first evaluation supplies the adjacent sign jump. -/
public theorem endpointVariation2_signedRemainderChain_step
    (p q : Dense) (qNonzero : q.isZero = false) (x : Fraction.Rational) :
    Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain p q) x =
      Sign.Jump.signJump (p.eval x) (q.eval x) +
        Sturm.endpointVariation2
          (SignedRemainder.Basic.Sturm.signedRemainderChain q (-((DensePolynomial.divMod p q).remainder))) x := by
  rw [Sturm.endpointVariation2,
    SignedRemainder.Basic.signedRemainderChain_step_of_second_nonzero p q qNonzero]
  obtain ⟨tail, chain⟩ :=
    SignedRemainder.Basic.signedRemainderChain_eq_cons q (-((DensePolynomial.divMod p q).remainder))
  rw [chain]
  rfl

/-- Normalizing both inputs preserves endpoint variation of the signed remainder chain.

Normalization preserves their evaluations and the retained division remainder.
Induction on the second polynomial's coefficient count compares the same finite
zero branch or transports the recursive tail equality through the initial jump. -/
public theorem endpointVariation2_signedRemainderChain_normalize
    (p q : Dense) (x : Fraction.Rational) :
    Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain p.normalize q.normalize) x =
      Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain p q) x := by
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q with
  | h degree inductionHypothesis =>
      by_cases qZero : q.isZero = true
      · have normalizedZero : q.normalize.isZero = true :=
          (DensePolynomial.isZero_normalize q).trans qZero
        exact (endpointVariation2_of_second_zero p.normalize q.normalize normalizedZero x).trans
          (endpointVariation2_of_second_zero p q qZero x).symm
      · have qNonzero := Decide.bool_eq_false_of_not_eq_true q.isZero qZero
        have normalizedNonzero : q.normalize.isZero = false :=
          (DensePolynomial.isZero_normalize q).trans qNonzero
        rw [endpointVariation2_signedRemainderChain_step
            p.normalize q.normalize normalizedNonzero x,
          endpointVariation2_signedRemainderChain_step
            p q qNonzero x]
        rw [DensePolynomial.eval_normalize, DensePolynomial.eval_normalize]
        have remainderEqual :
            (DensePolynomial.divMod p.normalize q.normalize).remainder =
              (DensePolynomial.divMod p q).remainder := by
          rw [DensePolynomial.divMod, DensePolynomial.divMod, DensePolynomial.degreeCount_normalize,
            DensePolynomial.normalize_normalize, DensePolynomial.normalize_normalize]
        rw [remainderEqual]
        let next := -((DensePolynomial.divMod p q).remainder)
        have nextNormalized : next.normalize = next := by
          exact DensePolynomial.normalize_neg _
        have nextCount : next.degreeCount < degree := by
          dsimp only [next]
          rw [DensePolynomial.degreeCount_neg, ← degreeEquation]
          exact DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero
        have recursive := inductionHypothesis next.degreeCount nextCount
          (p := q) (q := next) rfl
        rw [nextNormalized] at recursive
        rw [recursive]

/-- Simultaneous input negation preserves endpoint variation of the signed chain.

Negation preserves both zero tests and reverses both signs in each adjacent jump.
The exact division-remainder negation equation supplies the retained next pair;
its coefficient-count descent permits the same finite induction. -/
public theorem endpointVariation2_signedRemainderChain_neg
    (p q : Dense) (x : Fraction.Rational) :
    Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain (-p) (-q)) x =
      Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain p q) x := by
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q with
  | h degree inductionHypothesis =>
      by_cases qZero : q.isZero = true
      · have negZero : (-q).isZero = true := (DensePolynomial.isZero_neg q).trans qZero
        exact (endpointVariation2_of_second_zero (-p) (-q) negZero x).trans
          (endpointVariation2_of_second_zero p q qZero x).symm
      · have qNonzero := Decide.bool_eq_false_of_not_eq_true q.isZero qZero
        have negNonzero : (-q).isZero = false := (DensePolynomial.isZero_neg q).trans qNonzero
        rw [endpointVariation2_signedRemainderChain_step
            (-p) (-q) negNonzero x,
          endpointVariation2_signedRemainderChain_step
            p q qNonzero x]
        simp only [DensePolynomial.eval_neg, Sign.Jump.signJump_neg_neg,
          DensePolynomial.divMod_remainder_neg_both_direct]
        let next := -((DensePolynomial.divMod p q).remainder)
        have nextCount : next.degreeCount < degree := by
          dsimp only [next]
          rw [DensePolynomial.degreeCount_neg, ← degreeEquation]
          exact DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero
        rw [inductionHypothesis next.degreeCount nextCount
          (p := q) (q := next) rfl]

/-- Negating the second input gives an endpoint-independent sum of signed-chain variations.

At both displayed endpoints the input pair must not vanish together. Each
nonterminal division step retains that condition and contributes the same
complementary-jump sum, leaving the corresponding recursive tail equality. -/
public theorem endpointVariation2_neg_second_sum_eq
    {p q : Dense} {a b : Fraction.Rational}
    (pairAtA : p.eval a ≠ 0 ∨ q.eval a ≠ 0)
    (pairAtB : p.eval b ≠ 0 ∨ q.eval b ≠ 0) :
    Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain p q) a +
        Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain p (-q)) a =
      Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain p q) b +
        Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain p (-q)) b := by
  generalize degreeEquation : q.degreeCount = degree
  induction degree using Nat.strong_induction_on generalizing p q with
  | h degree inductionHypothesis =>
      by_cases qZero : q.isZero = true
      · have negZero : (-q).isZero = true := (DensePolynomial.isZero_neg q).trans qZero
        rewrite [endpointVariation2_of_second_zero p q qZero a,
          endpointVariation2_of_second_zero p (-q) negZero a,
          endpointVariation2_of_second_zero p q qZero b,
          endpointVariation2_of_second_zero p (-q) negZero b]
        exact Eq.refl _
      · have qNonzero := Decide.bool_eq_false_of_not_eq_true q.isZero qZero
        have negNonzero : (-q).isZero = false := (DensePolynomial.isZero_neg q).trans qNonzero
        let remainder := (DensePolynomial.divMod p q).remainder
        have nextPair (x : Fraction.Rational)
            (pair : p.eval x ≠ 0 ∨ q.eval x ≠ 0) :
            q.eval x ≠ 0 ∨ (-remainder).eval x ≠ 0 := by
          by_cases qZeroAtX : q.eval x = 0
          · right
            intro remainderZeroAtX
            have step := SignedRemainder.Evaluation.signedStep_eval_identity p q x
            have pZeroAtX : p.eval x = 0 := by
              rw [qZeroAtX] at step
              change p.eval x = 0 * (DensePolynomial.divMod p q).quotient.eval x -
                (-remainder).eval x at step
              rw [zero_mul, remainderZeroAtX, Fraction.Arithmetic.sub_eq_add_neg_direct, neg_zero, add_zero] at step
              exact step
            rcases pair with pNonzeroAtX | qNonzeroAtX
            · exact pNonzeroAtX pZeroAtX
            · exact qNonzeroAtX qZeroAtX
          · exact Or.inl qZeroAtX
        have nextAtA := nextPair a pairAtA
        have nextAtB := nextPair b pairAtB
        have nextCount : (-remainder).degreeCount < degree := by
          rw [DensePolynomial.degreeCount_neg, ← degreeEquation]
          exact DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero
        have recursive := inductionHypothesis (-remainder).degreeCount
          nextCount (p := q) (q := -remainder)
          nextAtA nextAtB rfl
        have atA := Sign.Jump.signJump_add_signJump_neg pairAtA.symm
        have atB := Sign.Jump.signJump_add_signJump_neg pairAtB.symm
        rw [Sign.Jump.signJump_comm (q.eval a) (p.eval a)] at atA
        rw [Sign.Jump.signJump_comm (q.eval b) (p.eval b)] at atB
        rw [endpointVariation2_signedRemainderChain_step
              p q qNonzero a,
            endpointVariation2_signedRemainderChain_step
              p (-q) negNonzero a,
            endpointVariation2_signedRemainderChain_step
              p q qNonzero b,
            endpointVariation2_signedRemainderChain_step
              p (-q) negNonzero b,
            DensePolynomial.divMod_remainder_neg_right p q qNonzero]
        simp only [DensePolynomial.eval_neg]
        rw [show (DensePolynomial.divMod p q).remainder = remainder by rfl]
        rw [endpointVariation2_signedRemainderChain_neg q remainder a,
          endpointVariation2_signedRemainderChain_neg q remainder b]
        have remainderNormalized : remainder.normalize = remainder := by
          exact DensePolynomial.divMod_remainder_normalize p q
        rw [DensePolynomial.neg_neg,
          remainderNormalized] at recursive
        calc
          Sign.Jump.signJump (p.eval a) (q.eval a) +
                Sturm.endpointVariation2
                  (SignedRemainder.Basic.Sturm.signedRemainderChain q (-remainder)) a +
              (Sign.Jump.signJump (p.eval a) (-q.eval a) +
                Sturm.endpointVariation2
                  (SignedRemainder.Basic.Sturm.signedRemainderChain q remainder) a) =
              (Sign.Jump.signJump (p.eval a) (q.eval a) +
                Sign.Jump.signJump (p.eval a) (-q.eval a)) +
                (Sturm.endpointVariation2
                    (SignedRemainder.Basic.Sturm.signedRemainderChain q (-remainder)) a +
                  Sturm.endpointVariation2
                    (SignedRemainder.Basic.Sturm.signedRemainderChain q remainder) a) := by ring1
          _ = 2 +
                (Sturm.endpointVariation2
                    (SignedRemainder.Basic.Sturm.signedRemainderChain q (-remainder)) b +
                  Sturm.endpointVariation2
                    (SignedRemainder.Basic.Sturm.signedRemainderChain q remainder) b) := by
              rw [atA, recursive]
          _ = (Sign.Jump.signJump (p.eval b) (q.eval b) +
                Sign.Jump.signJump (p.eval b) (-q.eval b)) +
                (Sturm.endpointVariation2
                    (SignedRemainder.Basic.Sturm.signedRemainderChain q (-remainder)) b +
                  Sturm.endpointVariation2
                    (SignedRemainder.Basic.Sturm.signedRemainderChain q remainder) b) := by
              rw [atB]
          _ = Sign.Jump.signJump (p.eval b) (q.eval b) +
                Sturm.endpointVariation2
                  (SignedRemainder.Basic.Sturm.signedRemainderChain q (-remainder)) b +
              (Sign.Jump.signJump (p.eval b) (-q.eval b) +
                Sturm.endpointVariation2
                  (SignedRemainder.Basic.Sturm.signedRemainderChain q remainder) b) := by ring1

/-- Endpoint variation differs evenly from the first-coordinate zero flag.

The represented second polynomial is nonzero, and the pair never vanishes
together at the displayed endpoint. The retained terminal evaluation is nonzero;
the two explicit parity witnesses add to the displayed integer difference. -/
public theorem endpointVariation2_sub_firstZeroFlag_even
    {p q : Dense} (hq : q.isZero = false)
    (coprime : NoCommonZero p q) (x : Fraction.Rational) :
    Even (((Sturm.endpointVariation2 (SignedRemainder.Basic.Sturm.signedRemainderChain p q) x : Nat) : Int) -
      (if p.eval x = 0 then 1 else 0)) := by
  obtain ⟨tail, chain⟩ := SignedRemainder.Basic.signedRemainderChain_eq_cons p q
  have terminal := SignedRemainder.Signs.terminalValue_signedRemainderChain_eval_ne_zero
    hq coprime x chain
  have variation := Sign.Variation.variation2_sub_signDifference_even
    (p.eval x) (tail.map fun r => r.eval x)
  have endpoint := Sign.Variation.sign_sub_terminal_sub_zeroFlag_even
    (x := p.eval x) terminal
  rcases variation with ⟨firstWitness, firstEquation⟩
  rcases endpoint with ⟨secondWitness, secondEquation⟩
  rw [Sturm.endpointVariation2, chain]
  simp only [List.map_cons]
  refine ⟨firstWitness + secondWitness, ?_⟩
  calc
    ((Sign.Variation.variation2 (p.eval x :: tail.map fun r => r.eval x) : Nat) : Int) -
          (if p.eval x = 0 then 1 else 0) =
        (((Sign.Variation.variation2 (p.eval x :: tail.map fun r => r.eval x) : Nat) : Int) -
          (Sign.Basic.sign (p.eval x) -
            Sign.Basic.sign (Sign.Variation.terminalValue (p.eval x) (tail.map fun r => r.eval x)))) +
        ((Sign.Basic.sign (p.eval x) -
            Sign.Basic.sign (Sign.Variation.terminalValue (p.eval x) (tail.map fun r => r.eval x))) -
          (if p.eval x = 0 then 1 else 0)) := by ring1
    _ = (firstWitness + firstWitness) + (secondWitness + secondWitness) := by
      rw [firstEquation, secondEquation]
    _ = (firstWitness + secondWitness) + (firstWitness + secondWitness) := by ring1

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
