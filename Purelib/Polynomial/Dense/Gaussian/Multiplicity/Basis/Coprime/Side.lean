module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Pairwise
public import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Cofactor
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Decomposition
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Factors
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Context.Coprime
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Product
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.CoprimeRelation
public import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Compute

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part

open Purelib.Polynomial

section
public section

/-!
# Total finite rational-function zero and pole sites

This module packages the signed multiplicity theorem over every finite
degree branch.  Linear factors return only exact displayed Gaussian-rational
zeros or poles.  Higher factors retain shrinking box tracks.  Constants have
no finite sites, and the identically-zero numerator has its own constructor.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

set_option genInjectivity false in
/-- Positive-degree side of a reduced rational function, together with its
complete finite multiplicity preprocessing and coprimality to the opposite
reduced cofactor. -/
structure PositiveSideInput
    (source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial) where
  /-- The source polynomial is already normalized. -/ sourceNormalized : source.normalize = source
  /-- The retained positive-degree preprocessing and squarefree occurrence decomposition of the source. -/ preprocessing
    : Dense.Gaussian.Squarefree.Decomposition.Compute.PositivePreprocessing source
  /-- The opposite reduced cofactor is nonzero. -/ oppositeNonzero : opposite.isZero = false
  /-- The source and opposite reduced cofactor carry an explicit Bézout certificate. -/ sourceOppositeCoprime :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate source opposite

constructive_injectivity PositiveSideInput

namespace PositiveSideInput

/-- Read the positive multiplicity entries from the retained preprocessing decomposition. -/
abbrev entries
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite) : List
      Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry :=
  input.preprocessing.decomposition.positiveMultiplicityEntries

/-- Enumerate the focused positions of the retained positive multiplicity list.

Each context keeps its original prefix, focused entry, suffix and exact split identity. -/
@[expose] def contexts
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite) :
    List (Context.Basic.PositiveContext input.entries) :=
  Dense.Gaussian.Multiplicity.Basis.Context.Basic.positiveContexts input.entries

/-- The focused-context list has the same length as the retained entry list. -/
theorem contexts_length
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite) :
    input.contexts.length = input.entries.length :=
  Dense.Gaussian.Multiplicity.Basis.Context.Basic.positiveContexts_length input.entries

/-- The weighted degrees of the retained entries sum to the original source degree. -/
theorem multiplicityDegree
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite) :
    Dense.Gaussian.Multiplicity.Basis.Product.positiveDegree input.entries =
      source.natDegree := by
  have degree := input.preprocessing.decomposition.positiveMultiplicityDegree
  simpa only [Dense.Basic.DensePolynomial.natDegree_normalize] using degree

/-- The retained positive-degree entries are pairwise coprime. -/
theorem entries_pairwise
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite) :
    input.entries.Pairwise fun left right =>
      CoprimeRelation
        left.part right.part :=
  input.preprocessing.decomposition.positiveMultiplicityEntries_pairwise

/-- The normalized source factors exactly through the selected factor and its single-copy cofactor. -/
theorem focusFactorization
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Context.Basic.PositiveContext input.entries) :
    Dense.Gaussian.Factorization.Identity.ProductIdentity source
      context.focus.part.polynomial
      (context.singleCofactor input.preprocessing.decomposition) := by
  have normalized := context.focusFactorization
    input.preprocessing.decomposition rfl
  simpa only [input.sourceNormalized] using normalized

/-- Every basis factor inherits a finite Bézout certificate against the
entire opposite reduced cofactor. -/
@[expose] def focusOppositeCoprime
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Context.Basic.PositiveContext input.entries) :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate context.focus.part.polynomial opposite :=
  Dense.Gaussian.Coprime.Factors.coprimeLeftFactor
    input.sourceOppositeCoprime context.focus.part.nonzero
    (input.focusFactorization context)

/-- A factor on this side and a factor on the opposite side inherit a
displayed finite Bézout certificate from reduced-cofactor coprimality. -/
@[expose] def focusFocusCoprime
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (left : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (leftContext : Context.Basic.PositiveContext left.entries)
    (right : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput opposite source)
    (rightContext : Context.Basic.PositiveContext
      right.entries) :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate leftContext.focus.part.polynomial
      rightContext.focus.part.polynomial := by
  let oppositeLeft :=
    Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
      (left.focusOppositeCoprime leftContext)
  let rightLeft := Dense.Gaussian.Coprime.Factors.coprimeLeftFactor
    oppositeLeft rightContext.focus.part.nonzero
      (right.focusFactorization rightContext)
  exact Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm rightLeft

/-- Same-side pairwise relations are converted back to the complete finite
Bézout data consumed by separation. -/
@[expose] def focusCoprimeOfRelation
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (left right : Context.Basic.PositiveContext input.entries)
    (relation : CoprimeRelation
      left.focus.part right.focus.part) :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate left.focus.part.polynomial
      right.focus.part.polynomial :=
  Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeCertificateOfRelation
    left.focus.part right.focus.part relation

/-- The focused contexts retain pairwise coprimality of their factors. -/
theorem contexts_pairwise
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite) :
    input.contexts.Pairwise fun left right =>
      CoprimeRelation
        left.focus.part right.focus.part :=
  Dense.Gaussian.Multiplicity.Basis.Context.Coprime.positiveContexts_pairwise
    input.entries_pairwise

/-- Finite lookup of the complete Bézout certificate between any two
distinct focused positions on the same side. -/
@[expose] def contextCoprime
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (left right : Fin input.contexts.length) (different : left ≠ right) :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate
      (input.contexts.get left).focus.part.polynomial
      (input.contexts.get right).focus.part.polynomial := open Purelib in by
  by_cases ordered : left.val < right.val
  · exact input.focusCoprimeOfRelation _ _
      (Data.List.Pairwise.pairwise_getElem input.contexts_pairwise
        left.val right.val left.isLt right.isLt ordered)
  · have valuesDifferent : left.val ≠ right.val := by
      intro equal
      exact different (Fin.ext equal)
    have reversed : right.val < left.val :=
      Nat.lt_of_le_of_ne (Nat.le_of_not_gt ordered) (Ne.symm valuesDifferent)
    exact input.focusCoprimeOfRelation _ _
      (Dense.Gaussian.Multiplicity.CoprimeRelation.coprimeRelation_symm
        (Data.List.Pairwise.pairwise_getElem input.contexts_pairwise
          right.val left.val right.isLt left.isLt reversed))

/-- An exact root of a focused factor is an exact root of the original source polynomial. -/
theorem exactSourceRoot
    {source opposite : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (input : Dense.Gaussian.Multiplicity.Basis.Coprime.Side.PositiveSideInput source opposite)
    (context : Context.Basic.PositiveContext input.entries)
    (root : Dense.Gaussian.Roots.Certificate.ExactRoot
      context.focus.part.polynomial) :
    source.eval root.point = 0 := by
  rw [Dense.Gaussian.Factorization.Identity.eval_factorization
    (input.focusFactorization context) root.point, root.root, zero_mul]
end PositiveSideInput
end Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Coprime.Side

end
