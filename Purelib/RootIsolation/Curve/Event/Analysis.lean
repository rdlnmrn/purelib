module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Substitution
import Purelib.RationalFunctions.Curve.Substitution.GCD
public import Purelib.RootIsolation.Curve.Clearance.Global
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Rat

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

public section

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

/-- At least one denominator-cleared coordinate is a represented nonzero
polynomial. -/
structure Nontrivial
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : Curve.RationalCurve) :
      Prop where
  /-- At least one of the original denominator-cleared coordinate polynomials is nonzero. -/ coordinateNonzero :
    (Curve.Substitution.realPolynomial p curve).isZero = false ∨
      (Curve.Substitution.imaginaryPolynomial p curve).isZero = false

namespace Nontrivial

/-- The gcd of a nontrivial cleared coordinate pair is nonzero. -/
theorem gcdNonzero
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {curve : Curve.RationalCurve}
    (data : Curve.Event.Nontrivial p curve) :
    (Curve.Substitution.gcdPolynomial p curve).isZero = false :=
  Dense.GCD.gcd_isZero_false data.coordinateNonzero

end Nontrivial

set_option genInjectivity false in
/-- Total finite outcome of the cleared-coordinate gcd calculation.

The three outcomes retain the original coordinate zero tests, constant-gcd exclusion certificate, or nontrivial
positive-degree event data. -/
inductive Analysis (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve :
  Curve.RationalCurve) where
  /-- Both denominator-cleared coordinate polynomials vanish identically, with both equations retained. -/ |
    identicallyZero
      (realZero :
        (Curve.Substitution.realPolynomial p curve).isZero = true)
      (imaginaryZero :
        (Curve.Substitution.imaginaryPolynomial p curve).isZero = true)
  /-- The retained constant-gcd certificate excludes roots on the non-pole curve. -/ | clear (certificate :
    Curve.Clearance.Global.GlobalClear p curve)
  /-- A nontrivial coordinate pair has a positive-degree gcd carrying its possible root events. -/ | events (data :
    Curve.Event.Nontrivial p curve)
      (gcdDegreePositive :
        0 < (Curve.Substitution.gcdPolynomial p curve).natDegree)

constructive_injectivity Analysis

/-- Execute the complete finite trichotomy: identically-zero restriction,
constant nonzero gcd, or nonconstant root-event polynomial.

The original coordinate and gcd-degree decisions select the same typed outcome, retaining both zero equations or the
same nontrivial coordinate witness. -/
@[expose] def analyze (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve :
  Curve.RationalCurve) :
    Curve.Event.Analysis p curve := by
  by_cases realNonzero :
      (Curve.Substitution.realPolynomial p curve).isZero = false
  · let data : Curve.Event.Nontrivial p curve := ⟨Or.inl realNonzero⟩
    by_cases degreeZero :
        (Curve.Substitution.gcdPolynomial p curve).natDegree = 0
    · exact .clear ⟨data.coordinateNonzero, degreeZero⟩
    · exact .events data (Nat.zero_lt_of_ne_zero degreeZero)
  · have realZero :
        (Curve.Substitution.realPolynomial p curve).isZero = true := by
      cases value : (Curve.Substitution.realPolynomial p curve).isZero with
      | false => exact (realNonzero value).elim
      | true => rfl
    by_cases imaginaryNonzero :
        (Curve.Substitution.imaginaryPolynomial p curve).isZero = false
    · let data : Curve.Event.Nontrivial p curve := ⟨Or.inr imaginaryNonzero⟩
      by_cases degreeZero :
          (Curve.Substitution.gcdPolynomial p curve).natDegree = 0
      · exact .clear ⟨data.coordinateNonzero, degreeZero⟩
      · exact .events data (Nat.zero_lt_of_ne_zero degreeZero)
    · have imaginaryZero :
          (Curve.Substitution.imaginaryPolynomial p curve).isZero =
            true := by
        cases value : (Curve.Substitution.imaginaryPolynomial p curve).isZero with
        | false => exact (imaginaryNonzero value).elim
        | true => rfl
      exact .identicallyZero realZero imaginaryZero

/-- The executable gcd vanishes at a displayed parameter exactly when both
cleared coordinate polynomials vanish there. -/
theorem gcd_eval_eq_zero_iff
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : Curve.RationalCurve)
    (parameter : Fraction.Rational) :
    (Curve.Substitution.gcdPolynomial p curve).eval parameter = 0 ↔
      (Curve.Substitution.realPolynomial p curve).eval parameter = 0 ∧
        (Curve.Substitution.imaginaryPolynomial p curve).eval
          parameter = 0 := by
  constructor
  · intro gcdZero
    constructor
    · have identity := Dense.GCD.leftFactor_eval_identity
          (Curve.Substitution.realPolynomial p curve)
          (Curve.Substitution.imaginaryPolynomial p curve) parameter
      change (Curve.Substitution.realPolynomial p curve).eval parameter =
        (Curve.Substitution.gcdPolynomial p curve).eval parameter * _
          at identity
      rw [gcdZero, Fraction.Field.zero_mul_direct] at identity
      exact identity
    · have identity := Dense.GCD.rightFactor_eval_identity
          (Curve.Substitution.realPolynomial p curve)
          (Curve.Substitution.imaginaryPolynomial p curve) parameter
      change
        (Curve.Substitution.imaginaryPolynomial p curve).eval parameter =
          (Curve.Substitution.gcdPolynomial p curve).eval parameter * _
            at identity
      rw [gcdZero, Fraction.Field.zero_mul_direct] at identity
      exact identity
  · rintro ⟨realZero, imaginaryZero⟩
    rw [Curve.Substitution.gcdPolynomial,
      Dense.GCD.gcd_eval_identity, realZero, imaginaryZero]
    rw [Fraction.Field.mul_zero_direct,
      Fraction.Field.mul_zero_direct,
      Fraction.Field.zero_add]

/-- Away from an explicitly excluded curve pole, the univariate gcd event is
exactly a zero of the original Gaussian polynomial on the curve. -/
theorem gcd_eval_eq_zero_iff_curve_root
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : Curve.RationalCurve)
    (parameter : Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    (Curve.Substitution.gcdPolynomial p curve).eval parameter = 0 ↔
      p.eval (curve.point parameter) = 0 :=
  (Curve.Event.gcd_eval_eq_zero_iff p curve parameter).trans
    (Curve.cleared_pair_zero_iff
      p curve parameter denominatorNonzero)
end Purelib.RootIsolation.Curve.Event

end
