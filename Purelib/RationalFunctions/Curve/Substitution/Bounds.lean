module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Components
public import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.RationalFunctions.Curve.Basic
public import Purelib.RationalFunctions.Curve.Substitution

open Purelib.Data
open Purelib.Polynomial
open Purelib.RationalFunctions

section
public section

/-!
# Uniform polynomial residual clearance on rational curve arcs

A constant cleared-coordinate gcd gives a positive coefficient-computed
lower bound for the denominator-cleared polynomial value on any displayed
finite parameter interval.  Dividing by a finite upper bound for the Horner
denominator power turns that into a positive lower bound for the original
polynomial residual at every non-pole point of the curve.

The final construction feeds that uniform residual directly to the
winding-one exclusion theorem.  One finite box refinement then excludes the
entire clear curve arc, rather than excluding only a selected rational point.
-/

namespace Purelib.RationalFunctions.Curve.Substitution

/-- Extract the real coordinate polynomial of the retained Horner denominator power.

The polynomial is read from the retained clearing state without recomputing its denominator power. -/
@[expose] def denominatorPowerReal
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : Curve.RationalCurve) :=
  Dense.Gaussian.Components.realPart
    (Curve.clearingState p curve).denominatorPower

/-- Extract the imaginary coordinate polynomial of the retained Horner denominator power.

The polynomial is read from the retained clearing state without recomputing its denominator power. -/
@[expose] def denominatorPowerImaginary
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : Curve.RationalCurve) :=
  Dense.Gaussian.Components.imagPart
    (Curve.clearingState p curve).denominatorPower

/-- Compute a positive quadrance majorant for the Horner denominator power on a rational interval.

Add the coefficient-derived squared evaluation bounds for its real and imaginary coordinate polynomials, then add one to
make the bound strictly positive. -/
@[expose] def denominatorPowerNormMajorant
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : Curve.RationalCurve)
    (interval : Data.Rat.Interval.Bounds) : Rat.Fraction.Rational :=
  Dense.Rational.Bounds.Horner.evalSqBound
      (denominatorPowerReal p curve) interval +
    Dense.Rational.Bounds.Horner.evalSqBound
      (denominatorPowerImaginary p curve) interval + 1

/-- The denominator-power quadrance majorant is strictly positive.

Each coordinate contribution is nonnegative, and the retained final unit contribution is strictly positive. -/
theorem denominatorPowerNormMajorant_pos
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : Curve.RationalCurve)
    (interval : Data.Rat.Interval.Bounds) :
    0 < denominatorPowerNormMajorant p curve interval := by
  apply Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
  · exact add_nonneg
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg _ _)
      (Dense.Rational.Bounds.Horner.evalSqBound_nonneg _ _)
  · decide

/-- The retained denominator-power evaluation has quadrance at most its interval majorant.

The rational parameter lies in the displayed interval. The two coordinate Horner bounds sum to the Gaussian quadrance
bound. -/
theorem normSq_denominatorPower_eval_le
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : Curve.RationalCurve)
    (interval : Data.Rat.Interval.Bounds) {parameter : Rat.Fraction.Rational}
    (inside : interval.Contains parameter) :
    Data.Gaussian.Norm.Basic.normSq
        ((Curve.clearingState p curve).denominatorPower.eval
          (Gaussian.Cast.Path.ofCoordinate parameter)) ≤
      denominatorPowerNormMajorant p curve interval := by
  have componentBound := add_le_add
    (Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
      (denominatorPowerReal p curve) interval inside)
    (Dense.Rational.Bounds.Horner.eval_sq_le_evalSqBound
      (denominatorPowerImaginary p curve) interval inside)
  have normComponentBound :
      Data.Gaussian.Norm.Basic.normSq
          ((Curve.clearingState p curve).denominatorPower.eval
            (Gaussian.Cast.Path.ofCoordinate parameter)) ≤
        Dense.Rational.Bounds.Horner.evalSqBound
            (denominatorPowerReal p curve) interval +
          Dense.Rational.Bounds.Horner.evalSqBound
            (denominatorPowerImaginary p curve) interval := by
    simpa only [denominatorPowerReal, denominatorPowerImaginary,
      Dense.Gaussian.Components.eval_realPart,
      Dense.Gaussian.Components.eval_imagPart, Data.Gaussian.Norm.Basic.normSq] using
        componentBound
  have majorantBound :
      Dense.Rational.Bounds.Horner.evalSqBound
            (denominatorPowerReal p curve) interval +
          Dense.Rational.Bounds.Horner.evalSqBound
            (denominatorPowerImaginary p curve) interval ≤
        denominatorPowerNormMajorant p curve interval := by
    unfold denominatorPowerNormMajorant
    exact le_add_of_nonneg_right (show (0 : Rat.Fraction.Rational) ≤ 1 by decide)
  exact normComponentBound.trans majorantBound

end Purelib.RationalFunctions.Curve.Substitution

end
