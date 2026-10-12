module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Clearance.Pair.Bezout
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.GCD
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Substitution
public import Purelib.RationalFunctions.Curve.Substitution.GCD
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.RationalFunctions

section
@[expose] public section

/-!
# Finite global clearance for a rationally parameterized curve

The real and imaginary denominator-cleared substitutions are ordinary finite
dense coordinate polynomials.  Their executable extended gcd therefore
decides an important easy case: a nonzero constant gcd certifies that the
displayed polynomial has no root at any finite parameter of the curve.

Local root counts for a nonconstant gcd are left to the subsequent Sturm
layer; this module supplies the algebraic reduction and its proof.
-/

namespace Purelib.RootIsolation.Curve.Clearance.Global

/-- Proof-bearing result of the finite constant-gcd test. -/
structure GlobalClear (p :
  CoefficientPolynomial)
  (curve : Curve.RationalCurve) : Type where
  /-- At least one denominator-cleared coordinate polynomial is nonzero. -/ coordinateNonzero :
    (Curve.Substitution.realPolynomial p curve).isZero = false ∨
      (Curve.Substitution.imaginaryPolynomial p curve).isZero = false
  /-- The retained coordinate gcd has natural degree zero. -/ gcdDegreeZero : (Curve.Substitution.gcdPolynomial p
    curve).natDegree = 0

namespace GlobalClear

open Purelib.RootIsolation
/-- The normalized degree-zero gcd evaluates to its displayed nonzero leading
coefficient at every rational parameter. -/
theorem gcd_eval_eq_leadingCoeff
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
    (clear : Curve.Clearance.Global.GlobalClear p curve) (parameter : Fraction.Rational) :
    (Curve.Substitution.gcdPolynomial p curve).eval parameter =
      (Curve.Substitution.gcdPolynomial p curve).leadingCoeff := by
  have normalizedConstant :=
    DensePolynomial.normalize_eq_constant_leadingCoeff_of_degree_zero
      (Dense.GCD.gcd_isZero_false clear.coordinateNonzero)
      clear.gcdDegreeZero
  have gcdConstant : Curve.Substitution.gcdPolynomial p curve =
      DensePolynomial.constant (Curve.Substitution.gcdPolynomial p curve).leadingCoeff := by
    calc
      Curve.Substitution.gcdPolynomial p curve = (Curve.Substitution.gcdPolynomial p curve).normalize :=
        (Dense.GCD.extendedGCD
          (Curve.Substitution.realPolynomial p curve)
          (Curve.Substitution.imaginaryPolynomial p curve)).normalized.symm
      _ = DensePolynomial.constant (Curve.Substitution.gcdPolynomial p curve).leadingCoeff :=
        normalizedConstant
  have evaluated := congrArg
    (fun polynomial : Dense.Basic.RationalPolynomial => polynomial.eval parameter)
    gcdConstant
  simpa only [DensePolynomial.eval_constant] using evaluated

/-- The gcd of the cleared coordinate pair is nonzero. -/
theorem gcdNonzero
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
    (clear : Curve.Clearance.Global.GlobalClear p curve) :
    (Curve.Substitution.gcdPolynomial p curve).isZero = false :=
  Dense.GCD.gcd_isZero_false clear.coordinateNonzero

/-- The certified constant gcd is nonzero at every rational parameter. -/
theorem gcd_eval_ne_zero
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
    (clear : Curve.Clearance.Global.GlobalClear p curve) (parameter : Fraction.Rational) :
    (Curve.Substitution.gcdPolynomial p curve).eval parameter ≠ 0 := by
  rw [clear.gcd_eval_eq_leadingCoeff parameter]
  exact DensePolynomial.leadingCoeff_ne_zero clear.gcdNonzero

/-- Scale the executable extended-gcd coefficients by the nonzero constant
gcd.  The result is an explicit pointwise Bézout identity equal to one; no
polynomial extensionality or infinite carrier is used. -/
def coprime
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
    (clear : Curve.Clearance.Global.GlobalClear p curve) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate
      (Curve.Substitution.realPolynomial p curve) (Curve.Substitution.imaginaryPolynomial p curve) := by
  let real := Curve.Substitution.realPolynomial p curve
  let imaginary := Curve.Substitution.imaginaryPolynomial p curve
  let gcd := Curve.Substitution.gcdPolynomial p curve
  let leading := gcd.leadingCoeff
  let inverse := leading⁻¹
  let left := Dense.GCD.leftCoefficient real imaginary
  let right := Dense.GCD.rightCoefficient real imaginary
  have leadingNonzero : leading ≠ 0 := by
    exact DensePolynomial.leadingCoeff_ne_zero clear.gcdNonzero
  exact
    { left := DensePolynomial.scale inverse left
      right := DensePolynomial.scale inverse right
      identity := by
        intro parameter
        have bezout := Dense.GCD.gcd_eval_identity
          real imaginary parameter
        have gcdValue : gcd.eval parameter = leading := by
          exact clear.gcd_eval_eq_leadingCoeff parameter
        change 1 = (DensePolynomial.scale inverse left).eval parameter * real.eval parameter +
          (DensePolynomial.scale inverse right).eval parameter * imaginary.eval parameter
        simp only [DensePolynomial.eval_scale]
        calc
          1 = inverse * leading := by
            exact (Fraction.Field.inv_mul_cancel
              leading leadingNonzero).symm
          _ = inverse * gcd.eval parameter := by rw [gcdValue]
          _ = inverse * (Dense.GCD.gcd real imaginary).eval
              parameter := rfl
          _ = inverse *
              (left.eval parameter * real.eval parameter +
                right.eval parameter * imaginary.eval parameter) := by
            rw [bezout]
          _ = (inverse * left.eval parameter) * real.eval parameter +
              (inverse * right.eval parameter) * imaginary.eval parameter := by
            rw [Fraction.Field.left_distrib,
              ← Fraction.Field.mul_assoc,
              ← Fraction.Field.mul_assoc] }

/-- Coefficient-computed positive uniform clearance for the two cleared
polynomial coordinates on any displayed finite parameter interval. -/
def clearance
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
    (clear : Curve.Clearance.Global.GlobalClear p curve)
    (interval : Data.Rat.Interval.Bounds) :
    Clearance.Pair.Basic.Certificate
      (Curve.Substitution.realPolynomial p curve) (Curve.Substitution.imaginaryPolynomial p curve) interval :=
  Clearance.Pair.Bezout.certificateOfCoprime clear.coprime interval

/-- The two cleared coordinate polynomials have no common parameter zero. -/
theorem noCommonZero
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
    (clear : Curve.Clearance.Global.GlobalClear p curve) (parameter : Fraction.Rational) :
    (Curve.Substitution.realPolynomial p curve).eval parameter ≠ 0 ∨
      (Curve.Substitution.imaginaryPolynomial p curve).eval parameter ≠ 0 := by
  if realZero : (Curve.Substitution.realPolynomial p curve).eval parameter = 0 then
    right
    intro imaginaryZero
    apply clear.gcd_eval_ne_zero parameter
    change (Dense.GCD.gcd
      (Curve.Substitution.realPolynomial p curve) (Curve.Substitution.imaginaryPolynomial p curve)).eval
        parameter = 0
    rw [Dense.GCD.gcd_eval_identity]
    rewrite [realZero, imaginaryZero, Fraction.Field.mul_zero_direct,
      Fraction.Field.mul_zero_direct, Fraction.zero_add]
    rfl
  else
    exact Or.inl realZero

/-- At every finite non-pole parameter, constant-gcd clearance excludes a
polynomial root on the rational curve. -/
theorem eval_point_ne_zero
    {p : CoefficientPolynomial} {curve : Curve.RationalCurve}
    (clear : Curve.Clearance.Global.GlobalClear p curve) (parameter : Fraction.Rational)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    p.eval (curve.point parameter) ≠ 0 := by
  intro root
  have pair :=
    (Curve.cleared_pair_zero_iff
      p curve parameter denominatorNonzero).2 root
  rcases clear.noCommonZero parameter with realNonzero | imaginaryNonzero
  · exact realNonzero pair.1
  · exact imaginaryNonzero pair.2

end GlobalClear

open Purelib.RootIsolation in
/-- Execute the finite coordinate-nonzero and constant-gcd tests. -/
def globalClear?
    (p : CoefficientPolynomial) (curve : Curve.RationalCurve) :
    Option (GlobalClear p curve) :=
  if realNonzero : (Curve.Substitution.realPolynomial p curve).isZero = false then
    if degreeZero : (Curve.Substitution.gcdPolynomial p curve).natDegree = 0 then
      some ⟨Or.inl realNonzero, degreeZero⟩
    else
      none
  else if imaginaryNonzero :
      (Curve.Substitution.imaginaryPolynomial p curve).isZero = false then
    if degreeZero : (Curve.Substitution.gcdPolynomial p curve).natDegree = 0 then
      some ⟨Or.inr imaginaryNonzero, degreeZero⟩
    else
      none
  else
    none

end Purelib.RootIsolation.Curve.Clearance.Global

end
