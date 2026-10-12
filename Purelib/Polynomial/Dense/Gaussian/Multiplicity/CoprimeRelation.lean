module

import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
import Purelib.Polynomial.Dense.Gaussian.Coprime.Factors
import Purelib.Polynomial.Dense.Gaussian.Coprime.Operations
public import Purelib.Polynomial.Dense.Gaussian.Factorization.Identity
import Purelib.Polynomial.Dense.Gaussian.GCD
public import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.Polynomial.Dense.Leading
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.GCD

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

/-- The finite Euclidean gcd has degree zero.  Both polynomials are supplied
as nonzero factors, so this proposition can always be converted back into
the full finite coprimality data. -/
def CoprimeRelation (left right :
  Squarefree.Part) : Prop :=
  (Dense.Gaussian.GCD.extendedGCD left.polynomial right.polynomial).gcd.natDegree =
    0

namespace CoprimeRelation

/-- Recover executable coprimality data from a constant-degree gcd relation.

Both retained squarefree parts are nonzero, so their displayed Euclidean gcd of degree zero supplies the full
coprimality certificate. -/
def coprimeCertificateOfRelation
    (left right : Squarefree.Part) (coprime :
      CoprimeRelation left right) :
    Dense.Gaussian.Coprime.Basic.CoprimeCertificate left.polynomial right.polynomial :=
  Dense.Gaussian.Coprime.Decision.certificateOfConstantGCD
    left.polynomial right.polynomial
      ((Dense.Gaussian.GCD.extendedGCD left.polynomial right.polynomial).nonzero
        (Or.inl left.nonzero)) coprime

end CoprimeRelation

namespace CoprimeRelation

/-- A coprimality certificate makes the retained Euclidean gcd have degree zero. -/
theorem coprimeRelationOfCertificate
    {left right : Squarefree.Part}
    (coprime : Dense.Gaussian.Coprime.Basic.CoprimeCertificate left.polynomial right.polynomial) :
    CoprimeRelation left right := by
  unfold CoprimeRelation
  rw [coprime.gcd_eq_constant]
  exact (Dense.Leading.LeadingTerm.constant coprime.unit_ne_zero).degree_eq

end CoprimeRelation

namespace CoprimeRelation

/-- The degree-zero gcd relation on retained squarefree parts is symmetric. -/
theorem coprimeRelation_symm
    {left right : Squarefree.Part} (coprime :
      CoprimeRelation left right) :
    CoprimeRelation right left :=
  coprimeRelationOfCertificate
    (Dense.Gaussian.Coprime.Operations.CoprimeCertificate.symm
      (coprimeCertificateOfRelation left right coprime))

end CoprimeRelation

namespace CoprimeRelation

/-- A nonzero displayed left divisor inherits the factor-level coprimality
relation with the other factor. -/
theorem coprimeRelation_leftFactor
    {parent other child : Squarefree.Part} {cofactor : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (coprime : CoprimeRelation parent other)
    (factorization : Dense.Gaussian.Factorization.Identity.ProductIdentity parent.polynomial
      child.polynomial cofactor) :
    CoprimeRelation child other :=
  coprimeRelationOfCertificate
    (Dense.Gaussian.Coprime.Factors.coprimeLeftFactor
      (coprimeCertificateOfRelation parent other coprime)
        child.nonzero factorization)

end CoprimeRelation

namespace CoprimeRelation

/-- A nonzero displayed right divisor inherits the factor-level coprimality
relation with the other factor. -/
theorem coprimeRelation_rightFactor
    {parent other child : Squarefree.Part} {cofactor : Basic.CanonicalCoefficients.CoefficientPolynomial}
    (coprime : CoprimeRelation parent other)
    (factorization : Dense.Gaussian.Factorization.Identity.ProductIdentity parent.polynomial
      cofactor child.polynomial) :
    CoprimeRelation child other :=
  coprimeRelationOfCertificate
    (Dense.Gaussian.Coprime.Factors.coprimeRightFactor
      (coprimeCertificateOfRelation parent other coprime)
        child.nonzero factorization)

end CoprimeRelation

end Purelib.Polynomial.Dense.Gaussian.Multiplicity

end
