module

import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Build
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field

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

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition

/-- Refine the retained squarefree occurrences into a pairwise-coprime multiplicity basis.

The basis remains indexed by the decomposition's exact factor list and retains its value and degree identities. -/
def multiplicityBasis
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    Multiplicity.Basis decomposition.factors :=
  Dense.Gaussian.Multiplicity.Basis.Build.buildBasis decomposition.factors

/-- The original normalized polynomial is exactly the weighted product of
the pairwise-coprime squarefree basis at every displayed finite argument. -/
theorem eval_multiplicityBasis
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p)
    (point : Gaussian.Basic.Canonical) :
    p.eval point =
      Dense.Gaussian.Multiplicity.Basis.Basic.basisValue decomposition.multiplicityBasis.entries point := by
  rw [decomposition.evalIdentity point,
    decomposition.multiplicityBasis.valueIdentity point]

/-- Weighted multiplicity degrees sum to the original normalized degree. -/
theorem multiplicityDegree
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    Dense.Gaussian.Multiplicity.Basis.Basic.basisDegree decomposition.multiplicityBasis.entries = p.natDegree := by
  rw [decomposition.multiplicityBasis.degreeIdentity,
    Dense.Gaussian.Multiplicity.Basis.Build.occurrenceDegree_eq_sum, decomposition.degreeSum]

/-- Read the positive-degree entries of the decomposition's multiplicity basis.

Only degree-zero entries are removed; each retained entry keeps its squarefree factor and positive multiplicity. -/
def positiveMultiplicityEntries
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry :=
  Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries decomposition.multiplicityBasis.entries

/-- The retained positive multiplicity factors are pairwise coprime. -/
theorem
  positiveMultiplicityEntries_pairwise
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    decomposition.positiveMultiplicityEntries.Pairwise fun left right =>
      Multiplicity.CoprimeRelation left.part right.part :=
  Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries_pairwise decomposition.multiplicityBasis.pairwise

/-- Exact multiplicity factorization after deleting only a displayed nonzero
unit scalar. -/
theorem
  eval_positiveMultiplicityEntries
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p)
    (point : Gaussian.Basic.Canonical) :
    p.eval point =
      Dense.Gaussian.Multiplicity.Basis.Positive.unitValue decomposition.multiplicityBasis.entries *
        Dense.Gaussian.Multiplicity.Basis.Positive.positiveValue decomposition.positiveMultiplicityEntries point := by
  calc
    p.eval point = Dense.Gaussian.Multiplicity.Basis.Basic.basisValue decomposition.multiplicityBasis.entries point :=
      decomposition.eval_multiplicityBasis point
    _ = Dense.Gaussian.Multiplicity.Basis.Positive.unitValue decomposition.multiplicityBasis.entries *
        Dense.Gaussian.Multiplicity.Basis.Positive.positiveValue decomposition.positiveMultiplicityEntries point :=
      Dense.Gaussian.Multiplicity.Basis.Positive.basisValue_eq_unitValue_mul_positiveValue _ _

/-- The scalar contributed by degree-zero basis entries is nonzero. -/
theorem multiplicityUnit_ne_zero
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    Dense.Gaussian.Multiplicity.Basis.Positive.unitValue decomposition.multiplicityBasis.entries ≠ 0 :=
  Dense.Gaussian.Multiplicity.Basis.Positive.unitValue_ne_zero _

/-- A decomposition with a nonempty list of positive-degree occurrences has a nonempty positive multiplicity basis. -/
theorem
  positiveMultiplicityEntries_nonempty
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    decomposition.positiveMultiplicityEntries ≠ [] := by
  apply Dense.Gaussian.Multiplicity.Basis.Positive.positiveEntries_ne_nil_of_basisDegree_positive
  rw [decomposition.multiplicityDegree]
  cases factorsEquation : decomposition.factors with
  | nil => exact (decomposition.factorsNonempty factorsEquation).elim
  | cons factor factors =>
      rw [← decomposition.degreeSum, factorsEquation]
      simp only [List.map_cons, List.sum_cons]
      exact factor.degreePositive.trans_le (Nat.le_add_right _ _)

/-- The positive signed multiplicities, weighted by their squarefree factor
degrees, add exactly to the original positive-degree polynomial degree. -/
theorem positiveMultiplicityDegree
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    Dense.Gaussian.Multiplicity.Basis.Product.positiveDegree decomposition.positiveMultiplicityEntries = p.natDegree :=
      by
  calc
    Dense.Gaussian.Multiplicity.Basis.Product.positiveDegree decomposition.positiveMultiplicityEntries =
        Dense.Gaussian.Multiplicity.Basis.Basic.basisDegree decomposition.multiplicityBasis.entries :=
      (Dense.Gaussian.Multiplicity.Basis.Product.basisDegree_eq_positiveDegree_positiveEntries
        decomposition.multiplicityBasis.entries).symm
    _ = p.natDegree := decomposition.multiplicityDegree

/-- The normalized source evaluates as one explicit nonzero unit times the
displayed weighted positive polynomial. -/
theorem eval_positivePolynomial
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p)
    (point : Gaussian.Basic.Canonical) :
    p.eval point =
      Dense.Gaussian.Multiplicity.Basis.Positive.unitValue decomposition.multiplicityBasis.entries *
        (Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial
          decomposition.positiveMultiplicityEntries).eval point := by
  rw [decomposition.eval_positiveMultiplicityEntries point,
    Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial_eval]

/-- The multiplicity basis is an exact finite polynomial factorization:
the normalized coefficient difference between the source and the displayed
unit times the weighted positive polynomial is zero. -/
theorem
  positiveMultiplicityProductIdentity
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    Dense.Gaussian.Factorization.Identity.ProductIdentity p
      (Dense.Basic.DensePolynomial.constant (Dense.Gaussian.Multiplicity.Basis.Positive.unitValue
        decomposition.multiplicityBasis.entries))
      (Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial decomposition.positiveMultiplicityEntries) := by
  apply Dense.Gaussian.Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  rw [Dense.Basic.DensePolynomial.eval_constant]
  exact decomposition.eval_positivePolynomial point

end Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition

end
