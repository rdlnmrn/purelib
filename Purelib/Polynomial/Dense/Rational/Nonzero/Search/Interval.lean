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

/-- Certified finite search through the `D+1` displayed interior candidates.

The original spacing and prepared coefficient table are retained once.
The indexed scan constructs each original candidate only when visited, in the
same order. Its full-list receipt retains the same first nonzero member or
exact finite-list exhaustion and every actual candidate evaluation.
-/
@[expose] public def interiorSearch (p : Dense.Rational.Basic.CoordinatePolynomial) (a b : Fraction.Rational)
    (degreeBound : Nat) : Search.List.Scan p (Grid.Interior.interiorCandidates a b degreeBound) :=
  let spacing := Grid.Interior.interiorStep a b degreeBound
  let prepared := Dense.Rational.Evaluation.prepare p.coeffs
  Search.List.scanOfFn prepared
    (fun index : Fin (degreeBound + 1) => Grid.Interior.point a spacing index)

/-- The prepared interval producer retains the complete original scan and its exact ordered evaluations. -/
public theorem interiorSearch_eq (p : Dense.Rational.Basic.CoordinatePolynomial) (a b : Fraction.Rational)
    (degreeBound : Nat) :
    interiorSearch p a b degreeBound =
      Search.List.scan p (Grid.Interior.interiorCandidates a b degreeBound) :=
  (Search.List.scanOfFn_eq (Dense.Rational.Evaluation.prepare p.coeffs)
    (fun index : Fin (degreeBound + 1) =>
      Grid.Interior.point a (Grid.Interior.interiorStep a b degreeBound) index)).trans
    (Search.List.scanWithPrepared_eq (Dense.Rational.Evaluation.prepare p.coeffs)
      (Grid.Interior.interiorCandidates a b degreeBound))

/-- Select the first original interior nonroot without constructing unused rational values.

The same indexed scan and retained integer coefficient table determine the
result. Its point-only consumer needs no rational normalization; requesting
`interiorSearch` still retains every exact ordered evaluation.
-/
@[expose] public def interiorSearchResult (p : Dense.Rational.Basic.CoordinatePolynomial)
    (a b : Fraction.Rational) (degreeBound : Nat) : Option Fraction.Rational :=
  let spacing := Grid.Interior.interiorStep a b degreeBound
  let prepared := Dense.Rational.Evaluation.prepare p.coeffs
  Search.List.firstNonzeroOfFn prepared
    (fun index : Fin (degreeBound + 1) => Grid.Interior.point a spacing index)

/-- Projected interval selection has exactly the full scan's first result or finite exhaustion. -/
public theorem interiorSearchResult_eq (p : Dense.Rational.Basic.CoordinatePolynomial)
    (a b : Fraction.Rational) (degreeBound : Nat) :
    interiorSearchResult p a b degreeBound = (interiorSearch p a b degreeBound).result :=
  Search.List.firstNonzeroOfFn_eq (Dense.Rational.Evaluation.prepare p.coeffs)
    (fun index : Fin (degreeBound + 1) =>
      Grid.Interior.point a (Grid.Interior.interiorStep a b degreeBound) index)

/-- Scanning more distinct interior candidates than the polynomial degree finds a nonzero evaluation.

The interval is strictly ordered and the polynomial is nonzero with natural degree at most the supplied bound. -/
public theorem interiorSearch_succeeds (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    ∃ x, (interiorSearch p a b degreeBound).result = some x := by
  have enough : p.degreeCount ≤ (Grid.Interior.interiorCandidates a b degreeBound).length := by
    rw [Grid.Interior.interiorCandidates_length]
    have count := Dense.Basic.DensePolynomial.natDegree_add_one_eq_degreeCount nonzero
    rw [← count]
    exact Nat.add_le_add_right degree 1
  rcases Search.List.firstNonzero_exists p (Grid.Interior.interiorCandidates a b degreeBound) nonzero
    (Grid.Interior.interiorCandidates_nodup less degreeBound) enough with ⟨point, found⟩
  exact ⟨point, (congrArg Search.List.Scan.result (interiorSearch_eq p a b degreeBound)).trans found⟩

/-- The bounded interior scan is populated under the nonzero polynomial and degree-bound hypotheses.

The successful scan certificate supplies a displayed Option constructor
under the original interval, nonzero polynomial and degree hypotheses.
Its isSome witness certifies that exact retained search result. -/
public theorem interiorSearch_isSome (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    (interiorSearch p a b degreeBound).result.isSome := by
  rcases interiorSearch_succeeds p degreeBound less nonzero degree with
    ⟨x, found⟩
  rw [found]
  rfl

/-- Total executable projection of the successful finite scan.

The shared indexed scan's integer zero tests determine the selected point.
Its result agrees with the complete certified scan at the same polynomial,
interval and degree bound; unused rational evaluation values are not needed.
-/
@[expose] public def interiorSearchValue (p : Dense.Rational.Basic.CoordinatePolynomial) {a b : Fraction.Rational}
    (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) : Fraction.Rational :=
  (interiorSearchResult p a b degreeBound).get (by
    rewrite [interiorSearchResult_eq]
    exact interiorSearch_isSome p degreeBound less nonzero degree)

/-- The projected selected point equals the complete scan's original successful readback. -/
public theorem interiorSearchValue_eq_get (p : Dense.Rational.Basic.CoordinatePolynomial)
    {a b : Fraction.Rational} (degreeBound : Nat) (less : a < b) (nonzero : p.isZero = false)
    (degree : p.natDegree ≤ degreeBound) :
    interiorSearchValue p degreeBound less nonzero degree =
      (interiorSearch p a b degreeBound).result.get
        (interiorSearch_isSome p degreeBound less nonzero degree) := by
  have isSome : (interiorSearchResult p a b degreeBound).isSome := by
    rewrite [interiorSearchResult_eq]
    exact interiorSearch_isSome p degreeBound less nonzero degree
  have selected : interiorSearchResult p a b degreeBound =
      some (interiorSearchValue p degreeBound less nonzero degree) :=
    Option.eq_some_of_isSome isSome
  exact Option.some.inj (selected.symm.trans
    ((interiorSearchResult_eq p a b degreeBound).trans
      (Option.eq_some_of_isSome (interiorSearch_isSome p degreeBound less nonzero degree))))

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
  have isSome : search.result.isSome :=
    interiorSearch_isSome p degreeBound less nonzero degree
  have found : search.result = some (search.result.get isSome) :=
    Option.eq_some_of_isSome isSome
  rcases search.receipt.found_spec found with ⟨member, valueNonzero⟩
  change search.result.get isSome ∈ List.ofFn (Grid.Interior.interiorCandidate a b degreeBound) at member
  rcases OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  have candidateNonzero :
      p.eval (Grid.Interior.interiorCandidate a b degreeBound index) ≠ 0 := by
    rw [equal]
    exact valueNonzero
  have selectedEqual :
      interiorSearchValue p degreeBound less nonzero degree =
        Grid.Interior.interiorCandidate a b degreeBound index := by
    rewrite [interiorSearchValue_eq_get]
    change search.result.get _ = _
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
  rewrite [interiorSearchValue_eq_get]
  let search := interiorSearch p a b degreeBound
  have isSome : search.result.isSome :=
    interiorSearch_isSome p degreeBound less nonzero degree
  have found : search.result = some (search.result.get isSome) :=
    Option.eq_some_of_isSome isSome
  exact (search.receipt.found_spec found).1

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
  have isSome : search.result.isSome :=
    interiorSearch_isSome p degreeBound less nonzero degree
  have found : search.result = some (search.result.get isSome) :=
    Option.eq_some_of_isSome isSome
  have member := (search.receipt.found_spec found).1
  change search.result.get isSome ∈ List.ofFn (Grid.Interior.interiorCandidate a b degreeBound) at member
  rcases OfFn.Basic.mem_ofFn.mp member with ⟨index, equal⟩
  have selectedEqual :
      interiorSearchValue p degreeBound less nonzero degree =
        Grid.Interior.interiorCandidate a b degreeBound index := by
    rewrite [interiorSearchValue_eq_get]
    change search.result.get _ = _
    exact equal.symm
  rw [selectedEqual]
  exact Grid.Interior.interiorCandidate_contraction less degreeBound index

end Purelib.Polynomial.Dense.Rational.Nonzero.Search.Interval
