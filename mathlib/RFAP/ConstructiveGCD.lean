import mathlib.RFAP.ComputableDerivative
import mathlib.RFAP.ComputableGCD
import mathlib.RFAP.ConstructivePolynomial

/-!
# Extended Euclid over constructive Gaussian coordinates

These wrappers are concrete audit points for the finite dense Euclidean
algorithm and automatic derivative.
-/

namespace RFAP.ConstructiveGCD

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial

open RFAP.ComputablePolynomial.DensePolynomial

def derivative (p : GaussianPolynomial) : GaussianPolynomial :=
  RFAP.ComputableDerivative.derivative p

def extendedGCD (p q : GaussianPolynomial) :
    RFAP.ComputableGCD.BezoutResult p q :=
  RFAP.ComputableGCD.extendedGCD p q

theorem bezout_identity (p q : GaussianPolynomial) (z : Gaussian) :
    (extendedGCD p q).gcd.eval z =
      (extendedGCD p q).left.eval z * p.eval z +
        (extendedGCD p q).right.eval z * q.eval z :=
  (extendedGCD p q).identity z

theorem division_remainder_degree_decreases
    (p q : GaussianPolynomial) (hq : q.isZero = false) :
    (p.divMod q).remainder.degreeCount < q.degreeCount :=
  divMod_remainder_degreeCount_lt p q hq

end RFAP.ConstructiveGCD
