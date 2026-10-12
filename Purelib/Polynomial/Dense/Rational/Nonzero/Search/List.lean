module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Roots.FiniteBound

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Evaluation

/-!
# First nonzero evaluation in a retained rational candidate list

The original finite scan returns its first candidate with nonzero polynomial
evaluation. Its certificates retain membership and the exact failed-scan
condition; enough distinct original candidates force a successful result.
-/

open Purelib.Data.Rat
open Purelib.Polynomial

namespace Purelib.Polynomial.Dense.Rational.Nonzero.Search.List

/-- Return the first displayed point where `p` is nonzero.

The original head is tested before its unchanged tail. A nonzero
evaluation returns that same rational candidate; zero evaluation
continues the original recursive scan and an empty list returns none. -/
@[expose] public def firstNonzero (p : Dense.Rational.Basic.CoordinatePolynomial) : List Fraction.Rational → Option
  Fraction.Rational
  | [] => none
  | x :: remaining =>
      if p.eval x = 0 then Purelib.Polynomial.Dense.Rational.Nonzero.Search.List.firstNonzero p remaining else some x

/-- A returned candidate belongs to the input list and has nonzero polynomial value.

The original Option result retains either the current nonzero head
or the result of the unchanged tail scan. Those same constructor
branches supply the displayed membership and nonzero evaluation. -/
public theorem firstNonzero_some_spec {p : Dense.Rational.Basic.CoordinatePolynomial} {points : List Fraction.Rational}
    {x : Fraction.Rational} (found : Dense.Rational.Nonzero.Search.List.firstNonzero p points = some x) :
    x ∈ points ∧ p.eval x ≠ 0 := by
  induction points with
  | nil =>
      change none = some x at found
      nomatch found
  | cons candidate remaining inductionHypothesis =>
      by_cases candidateZero : p.eval candidate = 0
      · rw [Dense.Rational.Nonzero.Search.List.firstNonzero, if_pos candidateZero] at found
        rcases inductionHypothesis found with ⟨member, nonzero⟩
        exact ⟨List.mem_cons_of_mem candidate member, nonzero⟩
      · rw [Dense.Rational.Nonzero.Search.List.firstNonzero, if_neg candidateZero] at found
        have equal : candidate = x := Option.some.inj found
        cases equal
        exact ⟨List.Mem.head remaining, candidateZero⟩

/-- The finite nonzero search fails exactly when every displayed candidate is a root.

Every original candidate is tested in list order. Failure of that
same scan supplies a zero evaluation at each actual occurrence,
and those retained zero evaluations force the original none result. -/
public theorem firstNonzero_eq_none_iff (p : Dense.Rational.Basic.CoordinatePolynomial)
    (points : List Fraction.Rational) :
    Dense.Rational.Nonzero.Search.List.firstNonzero p points = none ↔
      ∀ x ∈ points, p.eval x = 0 := by
  induction points with
  | nil =>
      constructor
      · intro _ x impossible
        nomatch impossible
      · intro _
        rfl
  | cons candidate remaining inductionHypothesis =>
      constructor
      · intro search x member
        by_cases candidateZero : p.eval candidate = 0
        · rw [Dense.Rational.Nonzero.Search.List.firstNonzero, if_pos candidateZero] at search
          cases member with
          | head => exact candidateZero
          | tail _ tailMember => exact inductionHypothesis.mp search x tailMember
        · rw [Dense.Rational.Nonzero.Search.List.firstNonzero, if_neg candidateZero] at search
          nomatch search
      · intro allZero
        have candidateZero : p.eval candidate = 0 :=
          allZero candidate List.mem_cons_self
        rw [Dense.Rational.Nonzero.Search.List.firstNonzero, if_pos candidateZero]
        apply inductionHypothesis.mpr
        intro x member
        exact allZero x (List.mem_cons_of_mem candidate member)

/-- Enough distinct displayed candidates guarantee a successful nonzero search.

The polynomial must be nonzero, the candidate list must have no duplicates, and its length must reach the polynomial
coefficient count. -/
public theorem firstNonzero_exists (p : Dense.Rational.Basic.CoordinatePolynomial) (points : List Fraction.Rational)
    (nonzero : p.isZero = false) (nodup : points.Nodup)
    (degreeBound : p.degreeCount ≤ points.length) :
    ∃ x, Dense.Rational.Nonzero.Search.List.firstNonzero p points = some x := by
  cases search : Dense.Rational.Nonzero.Search.List.firstNonzero p points with
  | none =>
      have allZero := (Dense.Rational.Nonzero.Search.List.firstNonzero_eq_none_iff p points).mp search
      have impossible := Dense.Rational.Roots.FiniteBound.nodup_zeros_length_lt_degreeCount p nonzero points
        nodup allZero
      exact (Nat.not_lt_of_ge degreeBound impossible).elim
  | some x => exact ⟨x, rfl⟩

end Purelib.Polynomial.Dense.Rational.Nonzero.Search.List
