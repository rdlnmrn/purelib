module

public import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Product
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Factors
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Factors
import Purelib.Polynomial.Dense.Gaussian.Coprime.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# A squarefree common source for two original coefficient polynomials

One retained Euclidean result removes the duplicated common factor. The
original first polynomial times the actual right cofactor is squarefree and
factors through both original inputs with retained coprime complements.
-/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic (CoprimeCertificate)
open Purelib.Polynomial.Dense.Gaussian.Factorization.Identity (ProductIdentity)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

set_option genInjectivity false in
/-- A retained squarefree common source with exact factors and coprime complements for both original inputs.

The complete Euclidean result retains both original polynomial owners and
cofactors. Its original right cofactor forms the actual source with the first
input; both source factor identities, complement certificates and degree bound
refer to that same retained data.
-/
structure Union (first second : CoefficientPolynomial) where
  /-- The original completed Euclidean computation on the two ordered inputs. -/
  result : Dense.GCD.BezoutResult first second
  /-- The retained complete result is the original executable Euclidean result. -/
  result_eq : result = GCD.extendedGCD first second
  /-- The actual retained common source coefficient polynomial. -/
  polynomial : CoefficientPolynomial
  /-- The source is the original first input times the same retained right cofactor. -/
  polynomial_eq : polynomial = first * result.qFactor
  /-- The common source has a nonzero coefficient table. -/
  nonzero : polynomial.isZero = false
  /-- The original common source is squarefree. -/
  squarefree : SquarefreeCertificate polynomial
  /-- The source degree is at least the original first input degree. -/
  degree_ge_first : first.natDegree ≤ polynomial.natDegree
  /-- The same source degree is at least the original second input degree. -/
  degree_ge_second : second.natDegree ≤ polynomial.natDegree
  /-- The original first input factors the same source with the retained right cofactor. -/
  firstFactorization : ProductIdentity polynomial first result.qFactor
  /-- The original second input factors the same source with the retained left cofactor. -/
  secondFactorization : ProductIdentity polynomial second result.pFactor
  /-- The original first input and its same source complement are coprime. -/
  firstCoprime : CoprimeCertificate first result.qFactor
  /-- The original second input and its same source complement are coprime. -/
  secondCoprime : CoprimeCertificate second result.pFactor

constructive_injectivity Union

namespace Union

/-- Construct the common source from one already computed original Euclidean result.

Both inputs are nonzero and squarefree, with no normalization or irreducibility
hypothesis. Their retained factor identities prove nonzero complements and
coprimality. Coprime-product squarefreeness then certifies the original first
input times that same stored right complement.
-/
@[expose] def ofResult (first second : CoefficientPolynomial)
    (firstNonzero : first.isZero = false) (secondNonzero : second.isZero = false)
    (firstSquarefree : SquarefreeCertificate first) (secondSquarefree : SquarefreeCertificate second)
    (result : Dense.GCD.BezoutResult first second) (resultEq : result = GCD.extendedGCD first second) :
    Union first second := by
  have commonNonzero := result.nonzero (.inl firstNonzero)
  have firstFactorization : ProductIdentity first result.gcd result.pFactor :=
    Factorization.Identity.factorizationOfCandidateEvals first result.gcd result.pFactor
      (fun point _ => result.pIdentity point)
  have secondFactorization : ProductIdentity second result.gcd result.qFactor :=
    Factorization.Identity.factorizationOfCandidateEvals second result.gcd result.qFactor
      (fun point _ => result.qIdentity point)
  have normalizedFirst : ProductIdentity first.normalize result.gcd result.pFactor :=
    Factorization.Identity.factorizationOfCandidateEvals first.normalize result.gcd result.pFactor
      (fun point _ => (DensePolynomial.eval_normalize first point).trans (result.pIdentity point))
  have normalizedSecond : ProductIdentity second.normalize result.gcd result.qFactor :=
    Factorization.Identity.factorizationOfCandidateEvals second.normalize result.gcd result.qFactor
      (fun point _ => (DensePolynomial.eval_normalize second point).trans (result.qIdentity point))
  have leftNonzero := Factorization.Identity.right_isZero_false
    ((DensePolynomial.isZero_normalize first).trans firstNonzero)
    (DensePolynomial.normalize_normalize first) normalizedFirst
  have rightNonzero := Factorization.Identity.right_isZero_false
    ((DensePolynomial.isZero_normalize second).trans secondNonzero)
    (DensePolynomial.normalize_normalize second) normalizedSecond
  let commonLeft := Coprime.Factors.factorsCoprime firstSquarefree commonNonzero firstFactorization
  let commonRight := Coprime.Factors.factorsCoprime secondSquarefree commonNonzero secondFactorization
  let complements := Coprime.Evaluation.coprimeCertificateOfIdentity result.pFactor result.qFactor
    (.inl leftNonzero) result.factorLeft result.factorRight result.factorIdentity
  let rightFirstProduct := Coprime.Operations.CoprimeCertificate.mulRight rightNonzero
    (Coprime.Operations.CoprimeCertificate.symm commonRight)
    (Coprime.Operations.CoprimeCertificate.symm complements)
  let leftSecondProduct := Coprime.Operations.CoprimeCertificate.mulRight leftNonzero
    (Coprime.Operations.CoprimeCertificate.symm commonLeft) complements
  let firstCoprime : CoprimeCertificate first result.qFactor :=
    Coprime.Evaluation.coprimeCertificateOfIdentity first result.qFactor (.inl firstNonzero)
      rightFirstProduct.right rightFirstProduct.left (by
        intro point
        have identity := rightFirstProduct.identity point
        rewrite [DensePolynomial.eval_mul, ← result.pIdentity point] at identity
        exact identity.trans (Purelib.Data.Gaussian.Basic.add_comm _ _))
  let secondCoprime : CoprimeCertificate second result.pFactor :=
    Coprime.Evaluation.coprimeCertificateOfIdentity second result.pFactor (.inl secondNonzero)
      leftSecondProduct.right leftSecondProduct.left (by
        intro point
        have identity := leftSecondProduct.identity point
        rewrite [DensePolynomial.eval_mul, ← result.qIdentity point] at identity
        exact identity.trans (Purelib.Data.Gaussian.Basic.add_comm _ _))
  let polynomial := first * result.qFactor
  have rightSquarefree := Factors.rightFactorSquarefree secondSquarefree rightNonzero secondFactorization
  let squarefree := Product.product firstNonzero rightNonzero firstSquarefree rightSquarefree firstCoprime
  have throughFirst : ProductIdentity polynomial first result.qFactor :=
    Factorization.Identity.factorizationOfCandidateEvals polynomial first result.qFactor
      (fun point _ => DensePolynomial.eval_mul first result.qFactor point)
  have throughSecond : ProductIdentity polynomial second result.pFactor := by
    apply Factorization.Identity.factorizationOfCandidateEvals
    intro point _
    change (first * result.qFactor).eval point = _
    rewrite [DensePolynomial.eval_mul, result.pIdentity point, result.qIdentity point]
    exact (Purelib.Data.Gaussian.Basic.mul_assoc _ _ _).trans
      ((congrArg (fun value => result.gcd.eval point * value)
        (Purelib.Data.Gaussian.Basic.mul_comm _ _)).trans
        (Purelib.Data.Gaussian.Basic.mul_assoc _ _ _).symm)
  have degree : first.natDegree ≤ polynomial.natDegree := by
    change first.natDegree ≤ (first * result.qFactor).natDegree
    rewrite [DensePolynomial.natDegree_mul firstNonzero rightNonzero]
    exact Nat.le_add_right _ _
  have secondDegree : second.natDegree ≤ polynomial.natDegree := by
    have equality := Factorization.Identity.factor_natDegree_add
      (DensePolynomial.isZero_mul_eq_false firstNonzero rightNonzero)
      (DensePolynomial.normalize_mul first result.qFactor) secondNonzero leftNonzero throughSecond
    exact (Nat.le_add_right second.natDegree result.pFactor.natDegree).trans_eq equality
  exact
    { result := result
      result_eq := resultEq
      polynomial := polynomial
      polynomial_eq := rfl
      nonzero := DensePolynomial.isZero_mul_eq_false firstNonzero rightNonzero
      squarefree := squarefree
      degree_ge_first := degree
      degree_ge_second := secondDegree
      firstFactorization := throughFirst
      secondFactorization := throughSecond
      firstCoprime := firstCoprime
      secondCoprime := secondCoprime }

/-- Compute one original Euclidean result and retain its squarefree common source and both complement certificates. -/
@[expose] def ofInputs (first second : CoefficientPolynomial)
    (firstNonzero : first.isZero = false) (secondNonzero : second.isZero = false)
    (firstSquarefree : SquarefreeCertificate first) (secondSquarefree : SquarefreeCertificate second) :
    Union first second :=
  let result := GCD.extendedGCD first second
  ofResult first second firstNonzero secondNonzero firstSquarefree secondSquarefree result rfl

end Union

end Purelib.Polynomial.Dense.Gaussian.Squarefree

end
