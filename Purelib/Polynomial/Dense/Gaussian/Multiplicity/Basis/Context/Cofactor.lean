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
    {entries : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry} (context :
      Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext entries) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Basic.DensePolynomial.constant
      (Dense.Gaussian.Multiplicity.Basis.Positive.unitValue
        decomposition.multiplicityBasis.entries) *
    (Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial context.before *
      Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial context.after)

/-- The cofactor formed from the retained prefix, suffix and nonzero unit is nonzero. -/
theorem otherPolynomial_nonzero
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    {entries : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry} (context :
      Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext entries) :
    (context.otherPolynomial decomposition).isZero = false := by
  apply Dense.Basic.DensePolynomial.isZero_mul_eq_false
  · exact (Dense.Leading.LeadingTerm.constant
      decomposition.multiplicityUnit_ne_zero).nonzero
  · exact Dense.Basic.DensePolynomial.isZero_mul_eq_false
      (Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial_nonzero context.before)
      (Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial_nonzero context.after)

/-- Pairwise coprimality of the multiplicity basis supplies one finite
Bézout certificate between the focused factor and the product of every
other positive entry, including the omitted nonzero unit. -/
@[expose] def otherCoprime
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    {entries : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry} (context :
      Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext entries)
    (pairwise : entries.Pairwise fun left right =>
      CoprimeRelation left.part right.part) :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate context.focus.part.polynomial
      (context.otherPolynomial decomposition) := by
  let unitCoprime :=
    Dense.Gaussian.Coprime.Operations.CoprimeCertificate.constantRightOfNe
      context.focus.part.nonzero
      (Dense.Gaussian.Multiplicity.Basis.Positive.unitValue
        decomposition.multiplicityBasis.entries)
      decomposition.multiplicityUnit_ne_zero
  let splitCoprime :=
    Dense.Gaussian.Coprime.Operations.CoprimeCertificate.mulRight
      context.focus.part.nonzero
      (Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext.coprimePositivePolynomial context.focus
        context.before
        (fun other member => context.focus_coprime_other pairwise
          (List.mem_append_left context.after member)))
      (Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext.coprimePositivePolynomial context.focus
        context.after
        (fun other member => context.focus_coprime_other pairwise
          (List.mem_append_right context.before member)))
  exact Dense.Gaussian.Coprime.Operations.CoprimeCertificate.mulRight
    context.focus.part.nonzero unitCoprime splitCoprime

/-- Cofactor after removing one copy, rather than the complete
multiplicity, of the focused factor. -/
@[expose] def singleCofactor
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    {entries : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry} (context :
      Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext entries) :
    (Dense.Basic.DensePolynomial Gaussian.Basic.Canonical) :=
  Dense.Gaussian.Power.polynomialPower
      context.focus.part.polynomial (context.focus.multiplicity - 1) *
    context.otherPolynomial decomposition

variable {entries : List Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry}

/-- The normalized source has the focused squarefree factor as an exact
finite coefficient divisor. -/
theorem focusFactorization
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    (entriesEq : entries = decomposition.positiveMultiplicityEntries)
    (context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext entries) :
    Dense.Gaussian.Factorization.Identity.ProductIdentity p context.focus.part.polynomial
      (context.singleCofactor decomposition) := by
  apply Dense.Gaussian.Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  have exponentIdentity :
      context.focus.multiplicity - 1 + 1 = context.focus.multiplicity :=
    Purelib.Data.Nat.Subtraction.sub_add_cancel context.focus.multiplicityPositive
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
  rw [listSplit, Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial_append_eval]
  simp only [Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial,
    Dense.Gaussian.Power.eval_polynomialPower, Dense.Basic.DensePolynomial.eval_mul,
    Dense.Basic.DensePolynomial.eval_constant,
      Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext.singleCofactor,
      Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext.otherPolynomial]
  rw [powerIdentity]
  ring1

/-- The same normalized source factors as the full displayed multiplicity
power times the polynomial of all other positive entries. -/
theorem multiplicityFactorization
    {p : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (decomposition : Squarefree.Decomposition p)
    (entriesEq : entries = decomposition.positiveMultiplicityEntries)
    (context : Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext entries) :
    Dense.Gaussian.Factorization.Identity.ProductIdentity p
      (Dense.Gaussian.Power.polynomialPower
        context.focus.part.polynomial context.focus.multiplicity)
      (context.otherPolynomial decomposition) := by
  apply Dense.Gaussian.Factorization.Identity.factorizationOfCandidateEvals
  intro point _
  rw [decomposition.eval_positivePolynomial point]
  have listSplit : decomposition.positiveMultiplicityEntries =
      context.before ++ context.focus :: context.after := by
    rw [← entriesEq]
    exact context.split
  rw [listSplit, Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial_append_eval]
  simp only [Dense.Gaussian.Multiplicity.Basis.Product.positivePolynomial,
    Dense.Gaussian.Power.eval_polynomialPower, Dense.Basic.DensePolynomial.eval_mul,
    Dense.Basic.DensePolynomial.eval_constant,
      Dense.Gaussian.Multiplicity.Basis.Context.Basic.PositiveContext.otherPolynomial]
  ring1

end PositiveContext

end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic

end
