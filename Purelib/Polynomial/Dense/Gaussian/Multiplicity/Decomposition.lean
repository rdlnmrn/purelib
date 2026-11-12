module
import Purelib.Polynomial.Dense.Gaussian.Extensionality

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

open Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis

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
  Build.buildBasis decomposition.factors

/-- The original normalized polynomial is exactly the weighted product of
the pairwise-coprime squarefree basis at every displayed finite argument. -/
theorem eval_multiplicityBasis
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p)
    (point : Gaussian.Basic.Canonical) :
    p.eval point =
      Basic.basisValue decomposition.multiplicityBasis.entries point := by
  rw [decomposition.evalIdentity point,
    decomposition.multiplicityBasis.valueIdentity point]

/-- Weighted multiplicity degrees sum to the original normalized degree. -/
theorem multiplicityDegree
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    Basic.basisDegree decomposition.multiplicityBasis.entries = p.natDegree := by
  rw [decomposition.multiplicityBasis.degreeIdentity,
    Build.occurrenceDegree_eq_sum, decomposition.degreeSum]

/-- Read the positive-degree entries of the decomposition's multiplicity basis.

Only degree-zero entries are removed; each retained entry keeps its squarefree factor and positive multiplicity. -/
def positiveMultiplicityEntries
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    List Positive.PositiveEntry :=
  Positive.positiveEntries decomposition.multiplicityBasis.entries

/-- The retained positive multiplicity factors are pairwise coprime. -/
theorem
  positiveMultiplicityEntries_pairwise
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    decomposition.positiveMultiplicityEntries.Pairwise fun left right =>
      Multiplicity.CoprimeRelation left.part right.part :=
  Positive.positiveEntries_pairwise decomposition.multiplicityBasis.pairwise

/-- Exact multiplicity factorization after deleting only a displayed nonzero
unit scalar. -/
theorem
  eval_positiveMultiplicityEntries
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p)
    (point : Gaussian.Basic.Canonical) :
    p.eval point =
      Positive.unitValue decomposition.multiplicityBasis.entries *
        Positive.positiveValue decomposition.positiveMultiplicityEntries point := by
  calc
    p.eval point = Basic.basisValue decomposition.multiplicityBasis.entries point :=
      decomposition.eval_multiplicityBasis point
    _ = Positive.unitValue decomposition.multiplicityBasis.entries *
        Positive.positiveValue decomposition.positiveMultiplicityEntries point :=
      Positive.basisValue_eq_unitValue_mul_positiveValue _ _

/-- The scalar contributed by degree-zero basis entries is nonzero. -/
theorem multiplicityUnit_ne_zero
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    Positive.unitValue decomposition.multiplicityBasis.entries ≠ 0 :=
  Positive.unitValue_ne_zero _

/-- A decomposition with a nonempty list of positive-degree occurrences has a nonempty positive multiplicity basis. -/
theorem
  positiveMultiplicityEntries_nonempty
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    decomposition.positiveMultiplicityEntries ≠ [] := by
  apply Positive.positiveEntries_ne_nil_of_basisDegree_positive
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
    Product.positiveDegree decomposition.positiveMultiplicityEntries = p.natDegree :=
      by
  calc
    Product.positiveDegree decomposition.positiveMultiplicityEntries =
        Basic.basisDegree decomposition.multiplicityBasis.entries :=
      (Product.basisDegree_eq_positiveDegree_positiveEntries
        decomposition.multiplicityBasis.entries).symm
    _ = p.natDegree := decomposition.multiplicityDegree

/-- The normalized source evaluates as one explicit nonzero unit times the
displayed weighted positive polynomial. -/
theorem eval_positivePolynomial
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p)
    (point : Gaussian.Basic.Canonical) :
    p.eval point =
      Positive.unitValue decomposition.multiplicityBasis.entries *
        (Product.positivePolynomial
          decomposition.positiveMultiplicityEntries).eval point := by
  rw [decomposition.eval_positiveMultiplicityEntries point,
    Product.positivePolynomial_eval]

/-- The multiplicity basis is an exact finite polynomial factorization:
the normalized coefficient difference between the source and the displayed
unit times the weighted positive polynomial is zero. -/
theorem
  positiveMultiplicityProductIdentity
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Decomposition p) :
    Factorization.Identity.ProductIdentity p
      (Basic.DensePolynomial.constant (Positive.unitValue
        decomposition.multiplicityBasis.entries))
      (Product.positivePolynomial decomposition.positiveMultiplicityEntries) := by
  apply Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  rw [Basic.DensePolynomial.eval_constant]
  exact decomposition.eval_positivePolynomial point

/-- The cached original multiplicity preprocessing gives the literal normalized source coefficient factorization. -/
theorem positiveMultiplicity_factorization
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (decomposition : Decomposition p) :
    p.normalize = Basic.DensePolynomial.scale (Positive.unitValue decomposition.multiplicityBasis.entries)
      (Product.positivePolynomial decomposition.positiveMultiplicityEntries) := by
  apply Extensionality.gaussian_normalized_eq_of_eval_eq
    (Basic.DensePolynomial.normalize_normalize p) (Basic.DensePolynomial.normalize_scale _ _)
  intro point
  rewrite [Basic.DensePolynomial.eval_normalize, Basic.DensePolynomial.eval_scale]
  exact decomposition.eval_positivePolynomial point

/-- The original discarded scalar and displayed powered factor heads reconstruct the same original source head. -/
theorem positiveMultiplicity_leadingCoeff
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial} (decomposition : Decomposition p) :
    p.leadingCoeff = Positive.unitValue decomposition.multiplicityBasis.entries *
      (decomposition.positiveMultiplicityEntries.foldr
        (fun entry total => entry.part.polynomial.leadingCoeff ^ entry.multiplicity * total) 1) := by
  have same := congrArg Basic.DensePolynomial.leadingCoeff decomposition.positiveMultiplicity_factorization
  have head : p.normalize.leadingCoeff = p.leadingCoeff := by
    change p.normalize.normalize.coeffs.headD 0 = p.normalize.coeffs.headD 0
    rewrite [Basic.DensePolynomial.normalize_normalize]
    rfl
  have weighted := Leading.LeadingTerm.ofNormalized
    (Product.positivePolynomial_nonzero decomposition.positiveMultiplicityEntries)
    (Product.positivePolynomial_normalized decomposition.positiveMultiplicityEntries)
  have scaled := Leading.LeadingTerm.scale decomposition.multiplicityUnit_ne_zero weighted
  exact head.symm.trans (same.trans (scaled.coefficient_eq.trans
    (congrArg (fun value => Positive.unitValue decomposition.multiplicityBasis.entries * value)
      (Product.positivePolynomial_leadingCoeff decomposition.positiveMultiplicityEntries))))

end Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition

end
