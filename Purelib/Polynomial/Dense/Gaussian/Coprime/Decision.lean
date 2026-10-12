module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Coprime.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Exhaustive finite Gaussian coprimality decisions

The original completed Euclidean record has a nonzero common factor when one
input is nonzero. Its same degree decision either certifies a retained nonzero
constant or returns the original positive-degree divisor and both cofactors.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Coprime.Decision

open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Dense.Gaussian.Coprime.Basic

/-- Normalize a checked constant Euclidean gcd into the finite coprimality
certificate consumed by the numerical proof.

The original completed result supplies its leading coefficient and normalization certificate. Its same nonzero and
degree-zero witnesses identify that retained common factor with the displayed constant. -/
@[expose] public def certificateOfConstantGCD
    (p q : GCD.CoefficientPolynomial)
    (nonzero : (GCD.extendedGCD p q).gcd.isZero = false)
    (degreeZero :
      (GCD.extendedGCD p q).gcd.natDegree = 0) :
    CoprimeCertificate p q := by
  let result := GCD.extendedGCD p q
  exact
    { unit := result.gcd.leadingCoeff
      unit_ne_zero := DensePolynomial.leadingCoeff_ne_zero nonzero
      gcd_eq_constant := by
        calc
          result.gcd = result.gcd.normalize := result.normalized.symm
          _ = DensePolynomial.constant result.gcd.leadingCoeff :=
            DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero nonzero
              degreeZero }

set_option genInjectivity false in
/-- The negative branch of the same finite Euclidean decision: a displayed
nonconstant common divisor and both quotient identities.

The original completed Euclidean record supplies the common divisor and both retained cofactors. Its nonzero and
positive-degree witnesses certify the same divisor obstruction. -/
public structure NonconstantCommonDivisor (p q : GCD.CoefficientPolynomial) where
  /-- The original extended-Euclid result with both quotient and Bezout identities. -/ result :
    Purelib.Polynomial.Dense.GCD.BezoutResult p q
  /-- The retained gcd polynomial is nonzero. -/ nonzero : result.gcd.isZero = false
  /-- The retained gcd has positive natural degree. -/ positiveDegree : 0 < result.gcd.natDegree

constructive_injectivity NonconstantCommonDivisor

namespace NonconstantCommonDivisor

/-- Read the retained nonconstant common gcd polynomial. -/
@[expose] public def divisor {p q : GCD.CoefficientPolynomial}
    (common : NonconstantCommonDivisor p q) : (DensePolynomial GCD.Scalar) :=
  common.result.gcd

/-- Read the retained cofactor of the first polynomial. -/
@[expose] public def leftFactor {p q : GCD.CoefficientPolynomial}
    (common : NonconstantCommonDivisor p q) : (DensePolynomial GCD.Scalar) :=
  common.result.pFactor

/-- Read the retained cofactor of the second polynomial. -/
@[expose] public def rightFactor {p q : GCD.CoefficientPolynomial}
    (common : NonconstantCommonDivisor p q) : (DensePolynomial GCD.Scalar) :=
  common.result.qFactor

/-- The first polynomial evaluates as the retained common divisor times its left cofactor. -/
public theorem leftIdentity {p q : GCD.CoefficientPolynomial}
    (common : NonconstantCommonDivisor p q)
    (z : GCD.Scalar) :
    p.eval z = common.divisor.eval z * common.leftFactor.eval z :=
  common.result.pIdentity z

/-- The second polynomial evaluates as the retained common divisor times its right cofactor. -/
public theorem rightIdentity {p q : GCD.CoefficientPolynomial}
    (common : NonconstantCommonDivisor p q)
    (z : GCD.Scalar) :
    q.eval z = common.divisor.eval z * common.rightFactor.eval z :=
  common.result.qIdentity z

end NonconstantCommonDivisor

set_option genInjectivity false in
/-- Exhaustive result of one finite coprimality computation.

The original input indices remain attached to each branch. A constant result returns its nonzero unit certificate; a
positive-degree result retains the exact original divisor and cofactor identities. -/
public inductive CoprimeOutcome (p q : GCD.CoefficientPolynomial) where
  /-- A certified nonzero constant gcd proves the pair coprime. -/ | coprime (certificate : CoprimeCertificate p q)
  /-- A retained positive-degree gcd and cofactors witness a nonconstant common divisor. -/ | commonDivisor (certificate
    : NonconstantCommonDivisor p q)

constructive_injectivity CoprimeOutcome

/-- Decide coprimality by inspecting the executable Euclidean gcd.

The same original nonzero common factor and its exact natural-degree decision determine the result. Both branches
consume the completed original Euclidean record and preserve their original selected witnesses. -/
@[expose] public def coprimeOutcome
    (p q : GCD.CoefficientPolynomial)
    (someNonzero : p.isZero = false ∨ q.isZero = false) :
    CoprimeOutcome p q := by
  let result := GCD.extendedGCD p q
  have gcdNonzero : result.gcd.isZero = false := result.nonzero someNonzero
  if degreeZero : result.gcd.natDegree = 0 then
    exact .coprime (certificateOfConstantGCD p q gcdNonzero degreeZero)
  else
    exact .commonDivisor
      { result := result
        nonzero := gcdNonzero
        positiveDegree := Nat.pos_of_ne_zero degreeZero }
end Purelib.Polynomial.Dense.Gaussian.Coprime.Decision
