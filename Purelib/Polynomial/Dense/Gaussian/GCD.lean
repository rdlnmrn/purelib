module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Polynomial.Dense.Derivative
public import Purelib.Polynomial.Dense.GCD
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

/-!
# Euclidean and derivative operations over Gaussian coefficients

The original dense derivative and extended Euclidean programs specialize to
canonical Gaussian-rational coefficients. Their completed records retain the
same quotient, common factor and ordered Bezout coefficients with scalar
evaluation and strict remainder-degree certificates.
-/

namespace Purelib.Polynomial.Dense.Gaussian.GCD

open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Gaussian.Basic

/-- The canonical Gaussian-rational coefficient carrier. -/
public abbrev Scalar := Purelib.Data.Gaussian.Basic.Canonical
/-- Dense polynomials over canonical Gaussian rationals. -/
public abbrev CoefficientPolynomial := Basic.CanonicalCoefficients.CoefficientPolynomial

/-- The existing finite derivative algorithm specialized to Gaussian coefficients.

The same original coefficient derivative state runs over the retained descending Gaussian coefficient list. This
specialization retains its original selected field operations. -/
@[expose] public def derivative (p : CoefficientPolynomial) : CoefficientPolynomial :=
  Derivative.derivative p

/-- The existing finite extended Euclidean algorithm over Gaussian dense polynomials.

The result retains its computed gcd and both Bezout cofactors with their evaluation identity. -/
@[expose] public def extendedGCD (p q : CoefficientPolynomial) :
    Purelib.Polynomial.Dense.GCD.BezoutResult p q :=
  Purelib.Polynomial.Dense.GCD.extendedGCD p q

/-- The computed Gaussian gcd equals the Bezout combination at every displayed point.

The completed original Gaussian Euclidean record supplies both ordered coefficient polynomials. Its retained identity is
specialized at the same supplied Gaussian point. -/
public theorem bezout_identity (p q : CoefficientPolynomial) (z : Scalar) :
    (extendedGCD p q).gcd.eval z =
      (extendedGCD p q).left.eval z * p.eval z +
        (extendedGCD p q).right.eval z * q.eval z :=
  (extendedGCD p q).identity z

/-- Division by a nonzero Gaussian polynomial gives a remainder with strictly smaller coefficient count.

The original nonzero divisor and completed division state retain the generic strict coefficient-count certificate at the
same Gaussian scalar realization. -/
public theorem division_remainder_degree_decreases
    (p q : CoefficientPolynomial) (hq : q.isZero = false) :
    (p.divMod q).remainder.degreeCount < q.degreeCount :=
  Basic.DensePolynomial.divMod_remainder_degreeCount_lt p q hq

end Purelib.Polynomial.Dense.Gaussian.GCD
