import CCL.Boundary.Curve.Rational
import mathlib.RFAP.ComputableGCD
import RFAP.Geometry.PathClearance

/-!
# Finite global clearance for a rationally parameterized curve

The real and imaginary denominator-cleared substitutions are ordinary finite
dense coordinate polynomials.  Their executable extended gcd therefore
decides an important easy case: a nonzero constant gcd certifies that the
displayed polynomial has no root at any finite parameter of the curve.

Local root counts for a nonconstant gcd are left to the subsequent Sturm
layer; this module supplies the algebraic reduction and its proof.
-/

namespace CCL.CurveClear

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev CoordinatePolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Coordinate
abbrev RationalCurve := CCL.RationalCurve.RationalCurve

open RFAP.ComputablePolynomial.DensePolynomial

def realPolynomial
    (p : GaussianPolynomial) (curve : RationalCurve) : CoordinatePolynomial :=
  CCL.RationalCurve.clearedReal p curve

def imaginaryPolynomial
    (p : GaussianPolynomial) (curve : RationalCurve) : CoordinatePolynomial :=
  CCL.RationalCurve.clearedImag p curve

def gcdPolynomial
    (p : GaussianPolynomial) (curve : RationalCurve) : CoordinatePolynomial :=
  RFAP.ComputableGCD.gcd (realPolynomial p curve)
    (imaginaryPolynomial p curve)

/-- Proof-bearing result of the finite constant-gcd test. -/
structure GlobalClear (p : GaussianPolynomial) (curve : RationalCurve) : Type where
  coordinateNonzero :
    (realPolynomial p curve).isZero = false ∨
      (imaginaryPolynomial p curve).isZero = false
  gcdDegreeZero : (gcdPolynomial p curve).natDegree = 0

namespace GlobalClear

/-- The normalized degree-zero gcd evaluates to its displayed nonzero leading
coefficient at every rational parameter. -/
theorem gcd_eval_eq_leadingCoeff
    {p : GaussianPolynomial} {curve : RationalCurve}
    (clear : GlobalClear p curve) (parameter : Coordinate) :
    (gcdPolynomial p curve).eval parameter =
      (gcdPolynomial p curve).leadingCoeff := by
  have normalizedConstant :=
    normalize_eq_constant_leadingCoeff_of_degree_zero
      (RFAP.ComputableGCD.gcd_isZero_false clear.coordinateNonzero)
      clear.gcdDegreeZero
  have gcdConstant : gcdPolynomial p curve =
      constant (gcdPolynomial p curve).leadingCoeff := by
    calc
      gcdPolynomial p curve = (gcdPolynomial p curve).normalize :=
        (RFAP.ComputableGCD.extendedGCD
          (realPolynomial p curve)
          (imaginaryPolynomial p curve)).normalized.symm
      _ = constant (gcdPolynomial p curve).leadingCoeff :=
        normalizedConstant
  have evaluated := congrArg
    (fun polynomial : CoordinatePolynomial => polynomial.eval parameter)
    gcdConstant
  simpa only [eval_constant] using evaluated

theorem gcdNonzero
    {p : GaussianPolynomial} {curve : RationalCurve}
    (clear : GlobalClear p curve) :
    (gcdPolynomial p curve).isZero = false :=
  RFAP.ComputableGCD.gcd_isZero_false clear.coordinateNonzero

theorem gcd_eval_ne_zero
    {p : GaussianPolynomial} {curve : RationalCurve}
    (clear : GlobalClear p curve) (parameter : Coordinate) :
    (gcdPolynomial p curve).eval parameter ≠ 0 := by
  rw [clear.gcd_eval_eq_leadingCoeff parameter]
  exact leadingCoeff_ne_zero clear.gcdNonzero

/-- Scale the executable extended-gcd coefficients by the nonzero constant
gcd.  The result is an explicit pointwise Bézout identity equal to one; no
polynomial extensionality or infinite carrier is used. -/
def coprime
    {p : GaussianPolynomial} {curve : RationalCurve}
    (clear : GlobalClear p curve) :
    RFAP.PathClearance.CoprimeCertificate
      (realPolynomial p curve) (imaginaryPolynomial p curve) := by
  let real := realPolynomial p curve
  let imaginary := imaginaryPolynomial p curve
  let gcd := gcdPolynomial p curve
  let leading := gcd.leadingCoeff
  let inverse := leading⁻¹
  let left := RFAP.ComputableGCD.leftCoefficient real imaginary
  let right := RFAP.ComputableGCD.rightCoefficient real imaginary
  have leadingNonzero : leading ≠ 0 := by
    exact leadingCoeff_ne_zero clear.gcdNonzero
  exact
    { left := scale inverse left
      right := scale inverse right
      identity := by
        intro parameter
        have bezout := RFAP.ComputableGCD.gcd_eval_identity
          real imaginary parameter
        have gcdValue : gcd.eval parameter = leading := by
          exact clear.gcd_eval_eq_leadingCoeff parameter
        change 1 = (scale inverse left).eval parameter * real.eval parameter +
          (scale inverse right).eval parameter * imaginary.eval parameter
        simp only [eval_scale]
        calc
          1 = inverse * leading := by
            exact (RFAP.ConstructiveFraction.inv_mul_cancel
              leading leadingNonzero).symm
          _ = inverse * gcd.eval parameter := by rw [gcdValue]
          _ = inverse * (RFAP.ComputableGCD.gcd real imaginary).eval
              parameter := rfl
          _ = inverse *
              (left.eval parameter * real.eval parameter +
                right.eval parameter * imaginary.eval parameter) := by
            rw [bezout]
          _ = (inverse * left.eval parameter) * real.eval parameter +
              (inverse * right.eval parameter) * imaginary.eval parameter := by
            rw [RFAP.ConstructiveFraction.left_distrib,
              ← RFAP.ConstructiveFraction.mul_assoc,
              ← RFAP.ConstructiveFraction.mul_assoc] }

/-- Coefficient-computed positive uniform clearance for the two cleared
polynomial coordinates on any displayed finite parameter interval. -/
def clearance
    {p : GaussianPolynomial} {curve : RationalCurve}
    (clear : GlobalClear p curve)
    (interval : RFAP.PathClearance.Interval) :
    RFAP.PathClearance.Certificate
      (realPolynomial p curve) (imaginaryPolynomial p curve) interval :=
  RFAP.PathClearance.certificateOfCoprime clear.coprime interval

/-- The two cleared coordinate polynomials have no common parameter zero. -/
theorem noCommonZero
    {p : GaussianPolynomial} {curve : RationalCurve}
    (clear : GlobalClear p curve) (parameter : Coordinate) :
    (realPolynomial p curve).eval parameter ≠ 0 ∨
      (imaginaryPolynomial p curve).eval parameter ≠ 0 := by
  if realZero : (realPolynomial p curve).eval parameter = 0 then
    right
    intro imaginaryZero
    apply clear.gcd_eval_ne_zero parameter
    change (RFAP.ComputableGCD.gcd
      (realPolynomial p curve) (imaginaryPolynomial p curve)).eval
        parameter = 0
    rw [RFAP.ComputableGCD.gcd_eval_identity]
    simp only [realZero, imaginaryZero,
      RFAP.ConstructiveFraction.mul_zero_direct, zero_add]
  else
    exact Or.inl realZero

/-- At every finite non-pole parameter, constant-gcd clearance excludes a
polynomial root on the rational curve. -/
theorem eval_point_ne_zero
    {p : GaussianPolynomial} {curve : RationalCurve}
    (clear : GlobalClear p curve) (parameter : Coordinate)
    (denominatorNonzero : curve.denominatorAt parameter ≠ 0) :
    p.eval (curve.point parameter) ≠ 0 := by
  intro root
  have pair :=
    (CCL.RationalCurve.cleared_pair_zero_iff
      p curve parameter denominatorNonzero).2 root
  rcases clear.noCommonZero parameter with realNonzero | imaginaryNonzero
  · exact realNonzero pair.1
  · exact imaginaryNonzero pair.2

end GlobalClear

/-- Execute the finite coordinate-nonzero and constant-gcd tests. -/
def globalClear?
    (p : GaussianPolynomial) (curve : RationalCurve) :
    Option (GlobalClear p curve) :=
  if realNonzero : (realPolynomial p curve).isZero = false then
    if degreeZero : (gcdPolynomial p curve).natDegree = 0 then
      some ⟨Or.inl realNonzero, degreeZero⟩
    else
      none
  else if imaginaryNonzero :
      (imaginaryPolynomial p curve).isZero = false then
    if degreeZero : (gcdPolynomial p curve).natDegree = 0 then
      some ⟨Or.inr imaginaryNonzero, degreeZero⟩
    else
      none
  else
    none

end CCL.CurveClear
