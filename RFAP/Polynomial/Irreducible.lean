import mathlib.RFAP.ConstructiveFiniteRoots
import RFAP.Polynomial.Squarefree

/-!
# Finite irreducibility implies squarefreeness

Irreducibility is recorded in its constructive proper-divisor form: every
displayed nonzero divisor of degree strictly below the input degree is
constant.  Factorization is an exact zero test on a finite coefficient
difference.  The executable Euclidean gcd of a positive-degree polynomial and
its derivative is a proper divisor, so irreducibility turns it into the
constant gcd required by the numerical RFAP.
-/

namespace RFAP.Irreducible

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev SquarefreeCertificate :=
  RFAP.Squarefree.SquarefreeCertificate

open RFAP.ComputablePolynomial.DensePolynomial

/-- Finite proper-divisor formulation of irreducibility.  Every argument is a
displayed dense coefficient list, and `factorization` is a decidable zero test
on another finite coefficient list. -/
structure IrreducibleCertificate (p : GaussianPolynomial) where
  nonzero : p.isZero = false
  degreePositive : 0 < p.natDegree
  properDivisorConstant :
    ∀ (divisor cofactor : GaussianPolynomial),
      (p - divisor * cofactor).isZero = true →
      divisor.isZero = false →
      divisor.natDegree < p.natDegree →
      divisor.natDegree = 0

/-- The pointwise identity computed by extended Euclid certifies a finite
coefficient factorization after checking only the bounded candidate list of
the displayed difference. -/
theorem gcd_factorization
    (p q : GaussianPolynomial) :
    let result := RFAP.ConstructiveGCD.extendedGCD p q
    (p - result.gcd * result.pFactor).isZero = true := by
  let result := RFAP.ConstructiveGCD.extendedGCD p q
  apply RFAP.ConstructiveFiniteRoots.difference_isZero_of_candidate_evals
  intro point _
  rw [eval_mul]
  exact result.pIdentity point

/-- A positive-degree irreducible Gaussian-rational polynomial is squarefree.
The derivative descent and gcd bounds are proved directly from finite
coefficient scans; no root collection or infinite-carrier argument occurs. -/
def squarefreeOfIrreducible
    {p : GaussianPolynomial} (irreducible : IrreducibleCertificate p) :
    SquarefreeCertificate p := by
  let derivative := RFAP.ConstructiveGCD.derivative p
  let result := RFAP.ConstructiveGCD.extendedGCD p derivative
  have derivativeNonzero : derivative.isZero = false := by
    dsimp only [derivative]
    exact RFAP.ConstructiveDerivativeDegree.derivative_isZero_false
      irreducible.nonzero irreducible.degreePositive
  have derivativeDegree : derivative.natDegree < p.natDegree := by
    dsimp only [derivative]
    exact RFAP.ComputableDerivative.derivative_natDegree_lt
      irreducible.nonzero irreducible.degreePositive
  have gcdNonzero : result.gcd.isZero = false :=
    result.nonzero (Or.inl irreducible.nonzero)
  have gcdProper : result.gcd.natDegree < p.natDegree :=
    (result.degreeLeRight derivativeNonzero).trans_lt derivativeDegree
  have factorization :
      (p - result.gcd * result.pFactor).isZero = true := by
    simpa only [result, derivative] using gcd_factorization p derivative
  have gcdConstant := irreducible.properDivisorConstant result.gcd
    result.pFactor factorization gcdNonzero gcdProper
  exact RFAP.Squarefree.certificateOfConstantGCD p derivative
    gcdNonzero gcdConstant

end RFAP.Irreducible
