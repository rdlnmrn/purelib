module
meta import Purelib.Elab.ConstructiveInjectivity

import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Factors
import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Factors
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.GCD

open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.Polynomial.Dense.Gaussian.Factorization.Identity (ProductIdentity)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic (Factor)

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

namespace Purelib.Polynomial.Dense.Gaussian.Multiplicity

set_option genInjectivity false in
/-- One nonconstant gcd split of two squarefree factors.  The common factor,
both residual factors, and all three relevant coprimality certificates are
kept explicitly. -/
structure CommonSplit (left right :
  Factor) where
  /-- The retained nonconstant squarefree common factor. -/ common :
    Factor
  /-- The normalized nonzero squarefree residual factor of the left input. -/ leftRemainder :
    Squarefree.Part
  /-- The normalized nonzero squarefree residual factor of the right input. -/ rightRemainder :
    Squarefree.Part
  /-- The finite coefficient identity factoring the left input through the common factor and left residual. -/
    leftFactorization :
    ProductIdentity left.polynomial common.polynomial leftRemainder.polynomial
  /-- The finite coefficient identity factoring the right input through the common factor and right residual. -/
    rightFactorization :
    ProductIdentity right.polynomial common.polynomial rightRemainder.polynomial
  /-- The common factor and left residual have a retained coprimality certificate. -/ commonLeftCoprime :
    CoprimeCertificate common.polynomial leftRemainder.polynomial
  /-- The common factor and right residual have a retained coprimality certificate. -/ commonRightCoprime :
    CoprimeCertificate common.polynomial rightRemainder.polynomial
  /-- The two retained residual factors have a coprimality certificate. -/ remaindersCoprime :
    CoprimeCertificate leftRemainder.polynomial rightRemainder.polynomial
  /-- The degrees of the common factor and left residual sum to the original left degree. -/ leftDegreeSum :
    common.polynomial.natDegree + leftRemainder.polynomial.natDegree =
      left.polynomial.natDegree
  /-- The degrees of the common factor and right residual sum to the original right degree. -/ rightDegreeSum :
    common.polynomial.natDegree + rightRemainder.polynomial.natDegree =
      right.polynomial.natDegree

constructive_injectivity CommonSplit

namespace CommonSplit

/-- Turn the displayed nonconstant gcd of two squarefree factors into the
fully certified three-way split. -/
def commonSplit
    (left right : Factor)
    (common : Dense.Gaussian.Coprime.Decision.NonconstantCommonDivisor
      left.polynomial right.polynomial) :
    CommonSplit left right := by
  let divisor := common.divisor
  let leftRemainder := common.leftFactor
  let rightRemainder := common.rightFactor
  have leftFactorization :
      ProductIdentity left.polynomial divisor leftRemainder := by
    apply Dense.Gaussian.Factorization.Identity.factorizationOfCandidateEvals
    intro point _
    exact common.leftIdentity point
  have rightFactorization :
      ProductIdentity right.polynomial divisor rightRemainder := by
    apply Dense.Gaussian.Factorization.Identity.factorizationOfCandidateEvals
    intro point _
    exact common.rightIdentity point
  have leftRemainderNonzero : leftRemainder.isZero = false :=
    Dense.Gaussian.Factorization.Identity.right_isZero_false
      left.nonzero left.normalized leftFactorization
  have rightRemainderNonzero : rightRemainder.isZero = false :=
    Dense.Gaussian.Factorization.Identity.right_isZero_false
      right.nonzero right.normalized rightFactorization
  have divisorSquarefree : SquarefreeCertificate divisor :=
    Dense.Gaussian.Squarefree.Factors.leftFactorSquarefree
      left.squarefree common.nonzero leftFactorization
  have leftRemainderSquarefree : SquarefreeCertificate leftRemainder :=
    Dense.Gaussian.Squarefree.Factors.rightFactorSquarefree
      left.squarefree leftRemainderNonzero leftFactorization
  have rightRemainderSquarefree : SquarefreeCertificate rightRemainder :=
    Dense.Gaussian.Squarefree.Factors.rightFactorSquarefree
      right.squarefree rightRemainderNonzero rightFactorization
  let commonFactor : Factor :=
    { polynomial := divisor
      normalized := common.result.normalized
      nonzero := common.nonzero
      degreePositive := common.positiveDegree
      squarefree := divisorSquarefree }
  let leftPart : Squarefree.Part :=
    { polynomial := leftRemainder
      normalized := common.result.pFactorNormalized
      nonzero := leftRemainderNonzero
      squarefree := leftRemainderSquarefree }
  let rightPart : Squarefree.Part :=
    { polynomial := rightRemainder
      normalized := common.result.qFactorNormalized
      nonzero := rightRemainderNonzero
      squarefree := rightRemainderSquarefree }
  have commonLeftCoprime :
      CoprimeCertificate divisor leftRemainder :=
    Dense.Gaussian.Coprime.Factors.factorsCoprime
      left.squarefree common.nonzero leftFactorization
  have commonRightCoprime :
      CoprimeCertificate divisor rightRemainder :=
    Dense.Gaussian.Coprime.Factors.factorsCoprime
      right.squarefree common.nonzero rightFactorization
  have remaindersCoprime :
      CoprimeCertificate leftRemainder rightRemainder :=
    Dense.Gaussian.Coprime.Evaluation.coprimeCertificateOfIdentity
      leftRemainder rightRemainder (Or.inl leftRemainderNonzero)
        common.result.factorLeft common.result.factorRight
          common.result.factorIdentity
  exact
    { common := commonFactor
      leftRemainder := leftPart
      rightRemainder := rightPart
      leftFactorization := leftFactorization
      rightFactorization := rightFactorization
      commonLeftCoprime := commonLeftCoprime
      commonRightCoprime := commonRightCoprime
      remaindersCoprime := remaindersCoprime
      leftDegreeSum :=
        Dense.Gaussian.Factorization.Identity.factor_natDegree_add
          left.nonzero left.normalized common.nonzero leftRemainderNonzero
            leftFactorization
      rightDegreeSum :=
        Dense.Gaussian.Factorization.Identity.factor_natDegree_add
          right.nonzero right.normalized common.nonzero rightRemainderNonzero
            rightFactorization }

end CommonSplit

end Purelib.Polynomial.Dense.Gaussian.Multiplicity

end
