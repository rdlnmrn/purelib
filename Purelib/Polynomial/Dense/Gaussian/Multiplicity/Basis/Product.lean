module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
public import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.Tactic.Ring

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Multiplicity
open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive (PositiveEntry)

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Finite multiplicity basis for general polynomials

The recursive derivative-gcd preprocessing returns squarefree occurrences.
Different composite occurrences may overlap.  This module refines such
overlaps by finite pairwise gcd computations.  Every split retains explicit
squarefree and coprimality certificates, so later isolation can run once per
distinct positive-degree basis factor and attach its exact occurrence count.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product

/-- The displayed dense polynomial represented by a positive multiplicity
list. -/
def positivePolynomial : List
  PositiveEntry →
    Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  | [] => DensePolynomial.constant 1
  | entry :: entries =>
      Dense.Gaussian.Power.polynomialPower entry.part.polynomial entry.multiplicity *
        positivePolynomial entries

/-- Evaluating the multiplicity polynomial gives the product of the corresponding powered factor values.

Each original factor retains its natural multiplicity and its supplied evaluation point, and finite induction follows
the unchanged ordered product. -/
@[simp] theorem positivePolynomial_eval
    (entries : List PositiveEntry) (point : Gaussian.Basic.Canonical) :
    (positivePolynomial entries).eval point =
      Basis.Positive.positiveValue entries point := by
  induction entries with
  | nil =>
      simp only [positivePolynomial,
        Basis.Positive.positiveValue, DensePolynomial.eval_constant, -eq_self,
        -iff_self]
      rfl
  | cons entry entries inductionHypothesis =>
      simp only [positivePolynomial,
        Basis.Positive.positiveValue, DensePolynomial.eval_mul,
        Dense.Gaussian.Power.eval_polynomialPower, inductionHypothesis, -eq_self, -iff_self]
      rfl

/-- A finite product of the retained nonzero factors raised to their multiplicities is nonzero. -/
theorem positivePolynomial_nonzero : ∀ entries :
  List PositiveEntry,
    (positivePolynomial entries).isZero = false
  | [] => (Purelib.Polynomial.Dense.Leading.LeadingTerm.constant one_ne_zero).nonzero
  | entry :: entries =>
      DensePolynomial.isZero_mul_eq_false
        (Dense.Gaussian.Power.polynomialPower_nonzero entry.part.nonzero entry.multiplicity)
        (positivePolynomial_nonzero entries)

/-- Weighted degree of the positive-degree entries only. -/
def positiveDegree : List
  PositiveEntry → Nat
  | [] => 0
  | entry :: entries =>
      entry.multiplicity * entry.part.polynomial.natDegree +
        positiveDegree entries

/-- Removing degree-zero basis entries preserves the weighted degree. -/
theorem
  basisDegree_eq_positiveDegree_positiveEntries :
    ∀ source : List Dense.Gaussian.Multiplicity.Basis.Basic.BasisEntry,
      Basis.Basic.basisDegree source =
        positiveDegree
        (Basis.Positive.positiveEntries source)
  | [] => rfl
  | entry :: entries => by
      rw [Basis.Basic.basisDegree,
        Basis.Positive.positiveEntries]
      split
      · rename_i degreeZero
        rw [degreeZero, Nat.mul_zero, Nat.zero_add,
          basisDegree_eq_positiveDegree_positiveEntries
            entries]
      · simp only [positiveDegree]
        rw [basisDegree_eq_positiveDegree_positiveEntries
          entries]
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product

end

section
@[expose] public section

/-!
# Winding of finite weighted multiplicity products

This module connects the executable multiplicity polynomial from
`ConstructiveMultiplicity` to the finite box product formula.  Powers are
structural recursion over a displayed natural number; no root collection or
factor evaluation over a completed carrier is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product

/-- Concatenating multiplicity lists multiplies their polynomial values at every displayed point.

Both original lists retain their order and powered factors; evaluation of their concatenation separates into the two
original finite products. -/
theorem positivePolynomial_append_eval
    (left right : List PositiveEntry)
    (point : Gaussian.Basic.Canonical) :
    (positivePolynomial (left ++ right)).eval
        point =
      (positivePolynomial left).eval point *
        (positivePolynomial right).eval point := by
  induction left with
  | nil =>
      simp only [List.nil_append,
        positivePolynomial, DensePolynomial.eval_constant,
        one_mul, -eq_self, -iff_self]
      rfl
  | cons entry entries inductionHypothesis =>
      simp only [List.cons_append,
        positivePolynomial, DensePolynomial.eval_mul,
        inductionHypothesis, -eq_self, -iff_self]
      ring1

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product

end
