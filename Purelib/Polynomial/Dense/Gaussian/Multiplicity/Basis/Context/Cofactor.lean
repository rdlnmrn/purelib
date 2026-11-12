module
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Coprime
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
import Purelib.Polynomial.Dense.Gaussian.Power
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Polynomial.Dense.Leading
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Build
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Polynomial

section
public section

/-!
# Winding of finite weighted multiplicity products

This module connects the executable multiplicity polynomial from
`ConstructiveMultiplicity` to the finite box product formula.  Powers are
structural recursion over a displayed natural number; no root collection or
factor evaluation over a completed carrier is introduced.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
namespace PositiveContext

/-- The polynomial containing every positive factor except the focused
factor, together with the nonzero unit omitted by positive preprocessing. -/
@[expose] def otherPolynomial
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    {entries : List Positive.PositiveEntry} (context :
      PositiveContext entries) :
    (Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Basic.DensePolynomial.constant
      (Positive.unitValue
        decomposition.multiplicityBasis.entries) *
    (Product.positivePolynomial context.before *
      Product.positivePolynomial context.after)

/-- The cofactor formed from the retained prefix, suffix and nonzero unit is nonzero. -/
theorem otherPolynomial_nonzero
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    {entries : List Positive.PositiveEntry} (context :
      PositiveContext entries) :
    (context.otherPolynomial decomposition).isZero = false := by
  apply Basic.DensePolynomial.isZero_mul_eq_false
  · exact (Leading.LeadingTerm.constant
      decomposition.multiplicityUnit_ne_zero).nonzero
  · exact Basic.DensePolynomial.isZero_mul_eq_false
      (Product.positivePolynomial_nonzero context.before)
      (Product.positivePolynomial_nonzero context.after)

/-- Pairwise coprimality of the multiplicity basis supplies one finite
Bézout certificate between the focused factor and the product of every
other positive entry, including the omitted nonzero unit. -/
@[expose] def otherCoprime
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    {entries : List Positive.PositiveEntry} (context :
      PositiveContext entries)
    (pairwise : entries.Pairwise fun left right =>
      CoprimeRelation left.part right.part) :
    Coprime.Basic.CoprimeCertificate context.focus.part.polynomial
      (context.otherPolynomial decomposition) := by
  let unitCoprime :=
    Coprime.Operations.CoprimeCertificate.constantRightOfNe
      context.focus.part.nonzero
      (Positive.unitValue
        decomposition.multiplicityBasis.entries)
      decomposition.multiplicityUnit_ne_zero
  let splitCoprime :=
    Coprime.Operations.CoprimeCertificate.mulRight
      context.focus.part.nonzero
      (coprimePositivePolynomial context.focus
        context.before
        (fun other member => context.focus_coprime_other pairwise
          (List.mem_append_left context.after member)))
      (coprimePositivePolynomial context.focus
        context.after
        (fun other member => context.focus_coprime_other pairwise
          (List.mem_append_right context.before member)))
  exact Coprime.Operations.CoprimeCertificate.mulRight
    context.focus.part.nonzero unitCoprime splitCoprime

/-- Cofactor after removing one copy, rather than the complete
multiplicity, of the focused factor. -/
@[expose] def singleCofactor
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    {entries : List Positive.PositiveEntry} (context :
      PositiveContext entries) :
    (Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Power.polynomialPower
      context.focus.part.polynomial (context.focus.multiplicity - 1) *
    context.otherPolynomial decomposition

variable {entries : List Positive.PositiveEntry}

/-- The normalized source has the focused squarefree factor as an exact
finite coefficient divisor. -/
theorem focusFactorization
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    (entriesEq : entries = decomposition.positiveMultiplicityEntries)
    (context : PositiveContext entries) :
    Factorization.Identity.ProductIdentity p context.focus.part.polynomial
      (context.singleCofactor decomposition) := by
  apply Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  have exponentIdentity :
      context.focus.multiplicity - 1 + 1 = context.focus.multiplicity :=
    Data.Nat.Subtraction.sub_add_cancel context.focus.multiplicityPositive
  have powerIdentity :
      context.focus.part.polynomial.eval point ^ context.focus.multiplicity =
        context.focus.part.polynomial.eval point *
          context.focus.part.polynomial.eval point ^
            (context.focus.multiplicity - 1) := by
    rw [← exponentIdentity, pow_succ]
    exact Gaussian.Basic.mul_comm _ _
  rw [decomposition.eval_positivePolynomial point]
  have listSplit : decomposition.positiveMultiplicityEntries =
      context.before ++ context.focus :: context.after := by
    rw [← entriesEq]
    exact context.split
  rw [listSplit, Product.positivePolynomial_append_eval]
  simp only [Product.positivePolynomial,
    Power.eval_polynomialPower, Basic.DensePolynomial.eval_mul,
    Basic.DensePolynomial.eval_constant,
      singleCofactor,
      otherPolynomial]
  rw [powerIdentity]
  ring1

/-- The same normalized source factors as the full displayed multiplicity
power times the polynomial of all other positive entries. -/
theorem multiplicityFactorization
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    (entriesEq : entries = decomposition.positiveMultiplicityEntries)
    (context : PositiveContext entries) :
    Factorization.Identity.ProductIdentity p
      (Power.polynomialPower
        context.focus.part.polynomial context.focus.multiplicity)
      (context.otherPolynomial decomposition) := by
  apply Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  rw [decomposition.eval_positivePolynomial point]
  have listSplit : decomposition.positiveMultiplicityEntries =
      context.before ++ context.focus :: context.after := by
    rw [← entriesEq]
    exact context.split
  rw [listSplit, Product.positivePolynomial_append_eval]
  simp only [Product.positivePolynomial,
    Power.eval_polynomialPower, Basic.DensePolynomial.eval_mul,
    Basic.DensePolynomial.eval_constant,
      otherPolynomial]
  ring1

end PositiveContext

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic

end
