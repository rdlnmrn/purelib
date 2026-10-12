module
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Rational.Squarefree.Decomposition
import Purelib.Polynomial.Dense.Rational.Squarefree.Locate
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
public import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation

public section

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

/-!
# Constructive root events on rationally parameterized curves

The constant-gcd branch of `CurveClear` excludes a polynomial
root everywhere on a rational curve.  This module handles the complementary
finite cases.  If both cleared coordinates vanish identically it records that
degeneracy explicitly.  Otherwise a nonconstant gcd is an ordinary nonzero
coordinate polynomial, so its derivative/gcd Sturm chain has the executable
event partition constructed in `ConstructiveSturmEventPartition`.
-/

namespace Purelib.RootIsolation.Curve.Event

/-- Repeated parameter factors are split by finite derivative-gcd recursion
before boundary ownership.  Every returned occurrence is squarefree and the
displayed product is exactly the normalized curve gcd. -/
@[expose] def eventDecomposition
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {curve : Curve.RationalCurve}
    (data : Curve.Event.Nontrivial p curve)
    (degreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p curve).natDegree) :
    Dense.Rational.Squarefree.Decomposition (Curve.Substitution.gcdPolynomial p curve) := by
  apply Dense.Rational.Squarefree.decomposeNormalized
  · exact (Dense.GCD.extendedGCD
      (Curve.Substitution.realPolynomial p curve)
      (Curve.Substitution.imaginaryPolynomial p curve)).normalized
  · exact data.gcdNonzero
  · exact degreePositive

/-- A displayed rational curve root is assigned by an executable finite scan
to its first squarefree parameter factor. -/
@[expose] def locateFactorRoot
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {curve : Curve.RationalCurve}
    (data : Curve.Event.Nontrivial p curve)
    (degreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p curve).natDegree)
    (parameter : Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0)
    (root : p.eval (curve.point parameter) = 0) :
    Dense.Rational.Squarefree.LocatedFactor (eventDecomposition data
      degreePositive).factors
      parameter :=
  (eventDecomposition data degreePositive).locateRoot parameter
    ((Curve.Event.gcd_eval_eq_zero_iff_curve_root p curve parameter
      denominatorNonzero).2 root)
end Purelib.RootIsolation.Curve.Event

end
