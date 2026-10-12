module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.OfFn.Basic
public import Purelib.Approximation.Rational.Grid.Interior
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.Nonzero.Search.List

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Bounded nonzero search in a rational interval

The original finite grid supplies degree-bound-plus-one candidates in a proper
interval. The retained list scan and its successful Option projection select
the first nonzero evaluation with its original finite index and bounds.
-/

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Approximation.Rational
open Purelib.Data.List
open Purelib.Polynomial.Dense.Rational.Nonzero

namespace Purelib.Polynomial.Dense.Rational.Nonzero.Search.Interval

/-- Finite search through the `D+1` displayed interior candidates.

The original list contains exactly the supplied degree bound plus one
interior grid points. The unchanged list scan tests them in their original
order and returns its first nonzero evaluation, or none. -/
@[expose] public def interiorSearch (p : Dense.Rational.Basic.CoordinatePolynomial) (a b : Fraction.Rational)
    (degreeBound : Nat) : Option Fraction.Rational :=
  Search.List.firstNonzero p (Grid.Interior.interiorCandidates a b degreeBound)

/-- Scanning more distinct interior candidates than the polynomial degree finds a nonzero evaluation.

The interval is strictly ordered and the polynomial is nonzero with natural degree at most the supplied bound. -/
public theorem interiorSearch_succeeds (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    ∃ x, interiorSearch p a b degreeBound = some x := by
  apply Search.List.firstNonzero_exists p (Grid.Interior.interiorCandidates a b degreeBound) nonzero
    (Grid.Interior.interiorCandidates_nodup less degreeBound)
  rw [Grid.Interior.interiorCandidates_length]
  have count := Dense.Basic.DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
  rw [← count]
  exact Nat.add_le_add_right degree 1

/-- The bounded interior scan is populated under the nonzero polynomial and degree-bound hypotheses.

The successful scan certificate supplies a displayed Option constructor
under the original interval, nonzero polynomial and degree hypotheses.
Its isSome witness certifies that exact retained search result. -/
public theorem interiorSearch_isSome (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    (interiorSearch p a b degreeBound).isSome := by
  rcases interiorSearch_succeeds p degreeBound less nonzero degree with
    ⟨x, found⟩
  rw [found]
  rfl

/-- Total executable projection of the successful finite scan.

The original interior scan is projected with Option.get using its
success certificate. The same interval, polynomial and degree bound
determine both the scan and its selected rational value. -/
@[expose] public def interiorSearchValue (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) : Fraction.Rational :=
  (interiorSearch p a b degreeBound).get
    (interiorSearch_isSome p degreeBound less nonzero degree)

/-- The selected rational point lies strictly inside the interval and has nonzero polynomial value.

Membership in the original displayed candidate list supplies its finite
index and exact selected-value equality. The corresponding grid bounds
and nonzero evaluation certify that same retained rational value. -/
public theorem interiorSearchValue_spec (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    p.eval (interiorSearchValue p degreeBound less nonzero degree) ≠ 0 ∧
      a < interiorSearchValue p degreeBound less nonzero degree ∧
      interiorSearchValue p degreeBound less nonzero degree < b := by
  let search := interiorSearch p a b degreeBound
  have isSome : search.isSome :=
    interiorSearch_isSome p degreeBound less nonzero degree
  have found : search = some (search.get isSome) :=
    Option.eq_some_of_isSome isSome
  rcases Search.List.firstNonzero_some_spec found with ⟨member, valueNonzero⟩
  rw [Grid.Interior.interiorCandidates] at member
  rcases OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  have candidateNonzero :
      p.eval (Grid.Interior.interiorCandidate a b degreeBound index) ≠ 0 := by
    rw [equal]
    exact valueNonzero
  have selectedEqual :
      interiorSearchValue p degreeBound less nonzero degree =
        Grid.Interior.interiorCandidate a b degreeBound index := by
    change (interiorSearch p a b degreeBound).get _ = _
    change search.get _ = _
    exact equal.symm
  rw [selectedEqual]
  exact And.intro candidateNonzero
    (Grid.Interior.interiorCandidate_bounds less degreeBound index)

/-- The selected rational point belongs to the exact displayed candidate list.

The successful Option result retains its original occurrence in the
finite candidate list. The same scan and isSome witness determine the
selected value appearing in that membership certificate. -/
public theorem interiorSearchValue_mem (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    interiorSearchValue p degreeBound less nonzero degree ∈
      Grid.Interior.interiorCandidates a b degreeBound := by
  let search := interiorSearch p a b degreeBound
  have isSome : search.isSome :=
    interiorSearch_isSome p degreeBound less nonzero degree
  have found : search = some (search.get isSome) :=
    Option.eq_some_of_isSome isSome
  exact (Search.List.firstNonzero_some_spec found).1

/-- The selected point stays within the degree-scaled grid step of each interval endpoint.

The selected value keeps its original finite grid index. Both endpoint
displacements are bounded by the degree-scaled grid step for that same
proper interval and retained candidate. -/
public theorem interiorSearchValue_contraction (p : Dense.Rational.Basic.CoordinatePolynomial)
    {a b : Fraction.Rational} (degreeBound : Nat) (less : a < b)
    (nonzero : p.isZero = false) (degree : p.natDegree ≤ degreeBound) :
    interiorSearchValue p degreeBound less nonzero degree - a ≤
        ((degreeBound + 1 : Nat) : Fraction.Rational) *
          Grid.Interior.interiorStep a b degreeBound ∧
      b - interiorSearchValue p degreeBound less nonzero degree ≤
        ((degreeBound + 1 : Nat) : Fraction.Rational) *
          Grid.Interior.interiorStep a b degreeBound := by
  let search := interiorSearch p a b degreeBound
  have isSome : search.isSome :=
    interiorSearch_isSome p degreeBound less nonzero degree
  have found : search = some (search.get isSome) :=
    Option.eq_some_of_isSome isSome
  have member := (Search.List.firstNonzero_some_spec found).1
  rw [Grid.Interior.interiorCandidates] at member
  rcases OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  have selectedEqual :
      interiorSearchValue p degreeBound less nonzero degree =
        Grid.Interior.interiorCandidate a b degreeBound index := by
    change (interiorSearch p a b degreeBound).get _ = _
    change search.get _ = _
    exact equal.symm
  rw [selectedEqual]
  exact Grid.Interior.interiorCandidate_contraction less degreeBound index

end Purelib.Polynomial.Dense.Rational.Nonzero.Search.Interval
