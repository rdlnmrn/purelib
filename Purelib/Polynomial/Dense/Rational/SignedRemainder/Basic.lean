module
import Purelib.Data.Bool.Decide
import Purelib.Data.Nat.Subtraction
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Division.Basic
public import Purelib.Polynomial.Dense.Rational.Basic

import Mathlib.Data.List.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic

/-!
# Signed Euclidean chains over rational coefficient lists

The original signed Euclidean program uses the normalized coefficient count of
its second polynomial as fuel. Scalar Boolean branch certificates prove stable
readback, degree descent and nonzero membership without changing its recursion.
-/

namespace Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial

public section

/-- Compute a signed Euclidean chain with a supplied natural fuel.

Zero fuel returns the first polynomial. Each remaining step tests the retained
second polynomial and division remainder for zero; a nonterminal step keeps
the first polynomial and recurs on the divisor and negated remainder. -/
@[expose] def Sturm.signedRemainderChainFuel : Nat → Dense.Rational.Basic.CoordinatePolynomial →
  Dense.Rational.Basic.CoordinatePolynomial → List Dense.Rational.Basic.CoordinatePolynomial
  := Nat.rec
    (fun p _ => [p])
    (fun _ recursive p q =>
      if q.isZero then [p]
      else
        let dm := Dense.Basic.DensePolynomial.divMod p q
        if dm.remainder.isZero then [p, q]
        else p :: recursive q (-dm.remainder))

/-- Zero fuel returns the singleton containing the first polynomial. -/
@[simp] theorem Sturm.signedRemainderChainFuel_zero (p q : Dense.Rational.Basic.CoordinatePolynomial) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel 0 p q = [p] := rfl

/-- Unfold one fuelled signed Euclidean step.

A zero second polynomial ends the chain; a zero remainder ends it with the pair; otherwise the next pair is the divisor
and negated remainder. -/
theorem Sturm.signedRemainderChainFuel_succ
    (fuel : Nat) (p q : Dense.Rational.Basic.CoordinatePolynomial) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel (fuel + 1) p q =
      if q.isZero then [p]
      else
        let dm := Dense.Basic.DensePolynomial.divMod p q
        if dm.remainder.isZero then [p, q]
        else p :: Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel q (-dm.remainder) := rfl

/-- Once the fuel already covers the represented degree, one further step of
fuel leaves the calculated chain unchanged.

The retained second-polynomial coefficient count bounds every recursive
remainder count. The original Boolean decisions select identical terminal
branches or transport the induction equality through the same list constructor. -/
theorem Sturm.signedRemainderChainFuel_succ_of_degreeCount_le :
    ∀ (fuel : Nat) (p q : Dense.Rational.Basic.CoordinatePolynomial), q.degreeCount ≤ fuel →
      Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel (fuel + 1) p q =
        Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel p q := by
  intro fuel
  induction fuel with
  | zero =>
      intro p q enough
      have degreeZero : q.degreeCount = 0 := Nat.eq_zero_of_le_zero enough
      have qTrue := Dense.Basic.DensePolynomial.isZero_true_of_degreeCount_eq_zero degreeZero
      change (if q.isZero then [p]
          else
            let dm := Dense.Basic.DensePolynomial.divMod p q
            if dm.remainder.isZero then [p, q]
            else p :: Sturm.signedRemainderChainFuel 0 q (-dm.remainder)) = [p]
      rewrite [if_pos qTrue]
      exact Eq.refl _
  | succ fuel inductionHypothesis =>
      intro p q enough
      change (if q.isZero then [p]
          else
            let dm := Dense.Basic.DensePolynomial.divMod p q
            if dm.remainder.isZero then [p, q]
            else p :: Sturm.signedRemainderChainFuel (fuel + 1) q (-dm.remainder)) =
        if q.isZero then [p]
          else
            let dm := Dense.Basic.DensePolynomial.divMod p q
            if dm.remainder.isZero then [p, q]
            else p :: Sturm.signedRemainderChainFuel fuel q (-dm.remainder)
      by_cases qTrue : q.isZero = true
      · rewrite [if_pos qTrue, if_pos qTrue]
        exact Eq.refl _
      · have qFalse := Data.Bool.Decide.bool_eq_false_of_not_eq_true q.isZero qTrue
        rewrite [if_neg qTrue, if_neg qTrue]
        by_cases remainderTrue : (Dense.Basic.DensePolynomial.divMod p q).remainder.isZero = true
        · rewrite [if_pos remainderTrue, if_pos remainderTrue]
          exact Eq.refl _
        · rewrite [if_neg remainderTrue, if_neg remainderTrue]
          apply congrArg (List.cons p)
          apply inductionHypothesis q (-((Dense.Basic.DensePolynomial.divMod p q).remainder))
          have remainderDegree := Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt p q qFalse
          rw [Dense.Basic.DensePolynomial.degreeCount_neg]
          exact Nat.lt_succ_iff.mp (lt_of_lt_of_le remainderDegree enough)

/-- Adding surplus to sufficient fuel preserves the calculated signed chain.

The second polynomial's represented coefficient count must already be bounded
by the supplied fuel. Each added step uses the same zero tests and remainder,
and strict coefficient-count descent makes further fuel unnecessary. -/
theorem Sturm.signedRemainderChainFuel_add_of_degreeCount_le
    (extra fuel : Nat) (p q : Dense.Rational.Basic.CoordinatePolynomial) (enough : q.degreeCount ≤ fuel) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel (fuel + extra) p q =
      Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel p q := by
  induction extra with
  | zero => rw [Nat.add_zero]
  | succ extra inductionHypothesis =>
      rw [Nat.add_succ]
      calc
        Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel (fuel + extra + 1) p q =
            Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel (fuel + extra) p q :=
          Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel_succ_of_degreeCount_le
            (fuel + extra) p q
              (enough.trans (Nat.le_add_right fuel extra))
        _ = Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel p q := inductionHypothesis

/-- Extra fuel cannot change a signed chain once the fuel reaches the second
polynomial's coefficient count.

The surplus is the displayed natural subtraction from the retained count.
Adding it back recovers the original fuel, and fuel stability preserves the
original emitted chain. -/
theorem Sturm.signedRemainderChainFuel_stable
    (fuel : Nat) (p q : Dense.Rational.Basic.CoordinatePolynomial) (enough : q.degreeCount ≤ fuel) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel p q =
      Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel q.degreeCount p q := by
  have fuelEquation : q.degreeCount + (fuel - q.degreeCount) = fuel :=
    Data.Nat.Subtraction.add_sub_of_le enough
  rw [← fuelEquation]
  exact Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel_add_of_degreeCount_le
    (fuel - q.degreeCount) q.degreeCount p q le_rfl

/-- Compute the signed Euclidean chain with fuel from the second polynomial's coefficient count.

The original polynomial pair is passed to the same fuel-bounded recursion.
Strict descent of nonterminal remainder counts makes this represented count
sufficient for its terminal zero test. -/
@[expose] def Sturm.signedRemainderChainWF (p q : Dense.Rational.Basic.CoordinatePolynomial) : List
  (Dense.Basic.DensePolynomial
  Fraction.Rational) :=
  Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel q.degreeCount p q

/-- One executable unfolding of the fuelled signed Euclidean chain.

The same retained zero tests and division remainder determine each branch.
Degree descent supplies sufficient fuel for the unchanged recursive pair. -/
theorem Sturm.signedRemainderChainWF_eq (p q : Dense.Rational.Basic.CoordinatePolynomial) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF p q =
      if q.isZero then [p]
      else
        let dm := Dense.Basic.DensePolynomial.divMod p q
        if dm.remainder.isZero then [p, q]
        else p :: Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF q (-dm.remainder) := by
  change Sturm.signedRemainderChainFuel q.degreeCount p q =
    if q.isZero then [p]
    else
      let dm := Dense.Basic.DensePolynomial.divMod p q
      if dm.remainder.isZero then [p, q]
      else p :: Sturm.signedRemainderChainFuel (-dm.remainder).degreeCount q (-dm.remainder)
  by_cases qTrue : q.isZero = true
  · have degreeZero := Dense.Basic.DensePolynomial.degreeCount_eq_zero_of_isZero qTrue
    rewrite [degreeZero, Sturm.signedRemainderChainFuel_zero, if_pos qTrue]
    exact Eq.refl _
  · have qFalse := Data.Bool.Decide.bool_eq_false_of_not_eq_true q.isZero qTrue
    have degreePositive := Dense.Basic.DensePolynomial.degreeCount_pos_of_isZero_false qFalse
    obtain ⟨qDegree, degreeEq⟩ := Nat.exists_eq_succ_of_ne_zero degreePositive.ne'
    rewrite [degreeEq, Sturm.signedRemainderChainFuel_succ, if_neg qTrue, if_neg qTrue]
    by_cases remainderTrue : (Dense.Basic.DensePolynomial.divMod p q).remainder.isZero = true
    · rewrite [if_pos remainderTrue, if_pos remainderTrue]
      exact Eq.refl _
    · rewrite [if_neg remainderTrue, if_neg remainderTrue]
      apply congrArg (List.cons p)
      exact Sturm.signedRemainderChainFuel_stable qDegree q
        (-((Dense.Basic.DensePolynomial.divMod p q).remainder)) (by
          have remainderDegree := Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt p q qFalse
          rewrite [Dense.Basic.DensePolynomial.degreeCount_neg]
          omega0)

/-- The signed Euclidean remainder chain of two rational polynomials.

The existing finite recursion uses the normalized coefficient count of the second polynomial as sufficient fuel. -/
@[expose] def Sturm.signedRemainderChain (p q : Dense.Rational.Basic.CoordinatePolynomial) : List
  (Dense.Basic.DensePolynomial
  Fraction.Rational) :=
  Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF p q

/-- A chain computed with given fuel contains at most fuel plus one entries.

Zero fuel emits a singleton. A terminal positive-fuel step emits a singleton
or pair, while each nonterminal step contributes one retained polynomial and
consumes one unit of fuel. -/
theorem signedRemainderChainFuel_length_le
    (fuel : Nat) (p q : Dense.Rational.Basic.CoordinatePolynomial) :
    (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel p q).length ≤ fuel + 1 := by
  induction fuel generalizing p q with
  | zero =>
      change [p].length ≤ 1
      exact le_rfl
  | succ fuel inductionHypothesis =>
      change (if q.isZero then [p]
          else
            let dm := Dense.Basic.DensePolynomial.divMod p q
            if dm.remainder.isZero then [p, q]
            else p :: Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel q (-dm.remainder)).length
              ≤
        (fuel + 1) + 1
      split
      · simp only [List.length_cons, List.length_nil]
        omega
      · change (if (Dense.Basic.DensePolynomial.divMod p q).remainder.isZero then [p, q]
            else p :: Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainFuel fuel q
              (-((Dense.Basic.DensePolynomial.divMod p q).remainder))).length ≤
          fuel + 1 + 1
        split
        · simp only [List.length_cons, List.length_nil]
          omega
        · simp only [List.length_cons]
          have recursive := inductionHypothesis q (-((Dense.Basic.DensePolynomial.divMod p q).remainder))
          omega

/-- The degree-fuelled chain contains at most the second coefficient count plus one entries.

Its original second polynomial supplies the exact fuel used by the finite
recursion. The fuel-length certificate therefore bounds the emitted chain
without a separate nonzero hypothesis. -/
theorem Sturm.signedRemainderChainWF_length_le (p q : Dense.Rational.Basic.CoordinatePolynomial) :
    (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF p q).length ≤ q.degreeCount + 1 :=
  Dense.Rational.SignedRemainder.Basic.signedRemainderChainFuel_length_le q.degreeCount p q

/-- Bound the signed remainder chain length by the second coefficient count plus one.

The public chain retains the same degree-fuelled calculation. Its original
second polynomial determines the coefficient count in the bound, including
the terminal cases where either zero test succeeds. -/
theorem signedRemainderChain_length_le (p q : Dense.Rational.Basic.CoordinatePolynomial) :
    (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q).length ≤ q.degreeCount + 1 :=
  Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChainWF_length_le p q

/-- The signed remainder chain is nonempty and begins with its first input.

Each original terminal or recursive branch retains the first polynomial.
The displayed tail is the exact emitted remainder chain, pair tail or empty list. -/
theorem signedRemainderChain_eq_cons (p q : Dense.Rational.Basic.CoordinatePolynomial) :
    ∃ tail, Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q = p :: tail := by
  change ∃ tail, Sturm.signedRemainderChainWF p q = p :: tail
  have unfolded := Sturm.signedRemainderChainWF_eq p q
  by_cases qTrue : q.isZero = true
  · rewrite [if_pos qTrue] at unfolded
    exact ⟨[], unfolded⟩
  · rewrite [if_neg qTrue] at unfolded
    by_cases remainderTrue : (Dense.Basic.DensePolynomial.divMod p q).remainder.isZero = true
    · rewrite [if_pos remainderTrue] at unfolded
      exact ⟨[q], unfolded⟩
    · rewrite [if_neg remainderTrue] at unfolded
      exact ⟨Sturm.signedRemainderChainWF q (-((Dense.Basic.DensePolynomial.divMod p q).remainder)), unfolded⟩

/-- With a represented nonzero second member, the signed chain exposes its
first Euclidean step uniformly, including the terminal zero-remainder case.

The false second-polynomial zero test selects division. A zero remainder
makes the next retained chain a singleton; otherwise the original recursive
branch is already the displayed next chain. -/
theorem signedRemainderChain_step_of_second_nonzero
    (p q : Dense.Rational.Basic.CoordinatePolynomial) (qNonzero : q.isZero = false) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q =
      p :: Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain q (-((Dense.Basic.DensePolynomial.divMod p
        q).remainder)) := by
  have qNotTrue : q.isZero ≠ true := by
    intro qTrue
    exact Bool.noConfusion (qNonzero.symm.trans qTrue)
  rewrite [Sturm.signedRemainderChain, Sturm.signedRemainderChainWF_eq, if_neg qNotTrue]
  by_cases remainderTrue : (Dense.Basic.DensePolynomial.divMod p q).remainder.isZero = true
  · have nextTrue : (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).isZero = true := by
      rewrite [Dense.Basic.DensePolynomial.isZero_neg]
      exact remainderTrue
    rewrite [if_pos remainderTrue, Sturm.signedRemainderChain,
      Sturm.signedRemainderChainWF_eq, if_pos nextTrue]
    exact Eq.refl _
  · rewrite [if_neg remainderTrue]
    exact Eq.refl _

/-- A nonzero constant-degree second member ends the finite signed chain
after the displayed pair.

The strict remainder coefficient-count bound forces a zero remainder.
The original nonzero divisor branch therefore terminates with this exact pair. -/
theorem signedRemainderChain_eq_pair_of_second_degreeCount_one
    {p q : Dense.Rational.Basic.CoordinatePolynomial} (qNonzero : q.isZero = false)
    (qCount : q.degreeCount = 1) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q = [p, q] := by
  have qNotTrue : q.isZero ≠ true := by
    intro qTrue
    exact Bool.noConfusion (qNonzero.symm.trans qTrue)
  have remainderCount := Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt p q qNonzero
  rewrite [qCount] at remainderCount
  have countZero : (Dense.Basic.DensePolynomial.divMod p q).remainder.degreeCount = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ remainderCount)
  have remainderTrue := Dense.Basic.DensePolynomial.isZero_true_of_degreeCount_eq_zero countZero
  have unfolded := Sturm.signedRemainderChainWF_eq p q
  rewrite [if_neg qNotTrue, if_pos remainderTrue] at unfolded
  exact unfolded

/-- If the first member has smaller degree, its normalization is exactly the
first remainder and the executable signed chain takes that recursive step.

The retained degree inequality makes the normalized first polynomial the
original division remainder. Its nonzero certificate selects the same signed
recursive pair in the original program. -/
theorem signedRemainderChain_eq_cons_of_degree_lt
    {p q : Dense.Rational.Basic.CoordinatePolynomial} (pNonzero : p.isZero = false)
    (qNonzero : q.isZero = false) (degree : p.natDegree < q.natDegree) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q =
      p :: Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain q (-p.normalize) := by
  have division := Dense.Basic.DensePolynomial.divMod_of_natDegree_lt (p := p) (q := q) degree
  have normalizedNonzero : p.normalize.isZero = false := by
    rewrite [Dense.Basic.DensePolynomial.isZero_normalize]
    exact pNonzero
  have qNotTrue : q.isZero ≠ true := by
    intro qTrue
    exact Bool.noConfusion (qNonzero.symm.trans qTrue)
  have normalizedNotTrue : p.normalize.isZero ≠ true := by
    intro normalizedTrue
    exact Bool.noConfusion (normalizedNonzero.symm.trans normalizedTrue)
  rewrite [Sturm.signedRemainderChain, Sturm.signedRemainderChainWF_eq,
    if_neg qNotTrue]
  dsimp only
  rewrite [division.2, if_neg normalizedNotTrue]
  exact Eq.refl _

/-- Every emitted member is represented nonzero when the first two are.

This pointwise certificate concerns every member of the original emitted
list. Strict descent of the retained remainder coefficient count propagates
nonzero membership through each original recursive branch. -/
theorem signedRemainderChainWF_all_nonzero {p q : Dense.Rational.Basic.CoordinatePolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    ∀ polynomial ∈ Sturm.signedRemainderChainWF p q, polynomial.isZero = false := by
  generalize hn : q.degreeCount = n
  induction n using Nat.strong_induction_on generalizing p q with
  | h n ih =>
      intro polynomial member
      have qNotTrue : q.isZero ≠ true := by
        intro qTrue
        exact Bool.noConfusion (hq.symm.trans qTrue)
      rewrite [Sturm.signedRemainderChainWF_eq, if_neg qNotTrue] at member
      by_cases remainderTrue : (Dense.Basic.DensePolynomial.divMod p q).remainder.isZero = true
      · rewrite [if_pos remainderTrue] at member
        cases member with
        | head => exact hp
        | tail _ tailMember =>
            cases tailMember with
            | head => exact hq
            | tail _ impossible => nomatch impossible
      · rewrite [if_neg remainderTrue] at member
        cases member with
        | head => exact hp
        | tail _ tailMember =>
            have remainderFalse := Data.Bool.Decide.bool_eq_false_of_not_eq_true
              (Dense.Basic.DensePolynomial.divMod p q).remainder.isZero remainderTrue
            have hnext : (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).isZero = false := by
              rewrite [Dense.Basic.DensePolynomial.isZero_neg]
              exact remainderFalse
            have hcount : (-((Dense.Basic.DensePolynomial.divMod p q).remainder)).degreeCount < n := by
              rewrite [Dense.Basic.DensePolynomial.degreeCount_neg, ← hn]
              exact Dense.Basic.DensePolynomial.divMod_remainder_degreeCount_lt p q hq
            exact ih _ hcount hq hnext rfl polynomial tailMember

/-- Nonzero initial polynomials yield only nonzero members of the signed remainder chain.

The original degree-fuelled chain has the same list as its well-founded
readback. The certificate retains each member and proves its represented
zero test is false. -/
theorem signedRemainderChain_all_nonzero {p q : Dense.Rational.Basic.CoordinatePolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    ∀ polynomial ∈ Sturm.signedRemainderChain p q, polynomial.isZero = false :=
  Dense.Rational.SignedRemainder.Basic.signedRemainderChainWF_all_nonzero hp hq
/-- Identify the chain tail after a nonzero second polynomial.

It is exactly the signed remainder chain of that polynomial and the negated division remainder. -/
theorem signedRemainderChain_tail_eq_of_second_nonzero
    (p q : Dense.Rational.Basic.CoordinatePolynomial) (qNonzero : q.isZero = false) :
    (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q).tail =
      Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain q (-((Dense.Basic.DensePolynomial.divMod p
        q).remainder)) := by
  rw [Dense.Rational.SignedRemainder.Basic.signedRemainderChain_step_of_second_nonzero p q qNonzero]
  rfl

/-- Reconstruct the signed remainder chain from its first input and its list tail. -/
theorem signedRemainderChain_eq_head_cons_tail (p q : Dense.Rational.Basic.CoordinatePolynomial) :
    Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q =
      p :: (Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q).tail := by
  rcases Dense.Rational.SignedRemainder.Basic.signedRemainderChain_eq_cons p q with ⟨tail, chainEq⟩
  rw [chainEq]
  rfl
end

end Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
