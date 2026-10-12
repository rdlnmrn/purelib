module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Substitution
public import Purelib.RationalFunctions.Curve.Substitution.Bounds
import Purelib.RationalFunctions.Curve.Substitution.GCD
public import Purelib.RootIsolation.Curve.Clearance.Global
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Clearance.Pair.Bezout
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

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

namespace Purelib.RootIsolation.Curve.Clearance.Residual

set_option genInjectivity false in
/-- A positive pointwise lower bound for the original polynomial residual on
the non-pole part of one displayed rational curve interval. -/
structure Certificate
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (curve : Curve.RationalCurve)
    (interval : Data.Rat.Interval.Bounds) where
  /-- The retained rational lower bound for squared polynomial residuals on the curve arc. -/ bound : Fraction.Rational
  /-- The retained residual lower bound is strictly positive. -/ positive : 0 < bound
  /-- Every interval parameter away from a curve pole satisfies the same residual lower bound. -/ lower : ∀ parameter :
    Fraction.Rational, interval.Contains parameter →
    curve.denominatorAt parameter ≠ 0 →
      bound ≤ Data.Gaussian.Norm.Basic.normSq (p.eval (curve.point parameter))

constructive_injectivity Certificate

/-- Convert constant-gcd curve clearance into a lower bound for the original
polynomial by an entirely finite denominator-power majorant. -/
@[expose] def certificate
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {curve : Curve.RationalCurve}
    (clear : Curve.Clearance.Global.GlobalClear p curve)
    (interval : Data.Rat.Interval.Bounds) : Certificate p curve interval := by
  let cleared := clear.clearance interval
  let majorant := Curve.Substitution.denominatorPowerNormMajorant p curve interval
  have majorantPositive : 0 < majorant :=
    Curve.Substitution.denominatorPowerNormMajorant_pos p curve interval
  exact
    { bound := cleared.bound / majorant
      positive := Fraction.Order.Field.div_pos_direct cleared.positive
        majorantPositive
      lower := by
        intro parameter inside denominatorNonzero
        have clearedLower : cleared.bound ≤
            Data.Gaussian.Norm.Basic.normSq ((Curve.clearedEval p curve).eval
              (Gaussian.Cast.Path.ofCoordinate parameter)) := by
          simpa only [cleared,
            Curve.Clearance.Global.GlobalClear.clearance,
            Curve.Substitution.realPolynomial,
            Curve.Substitution.imaginaryPolynomial,
            Curve.clearedReal,
            Curve.clearedImag,
            Dense.Gaussian.Components.eval_realPart,
            Dense.Gaussian.Components.eval_imagPart, Data.Gaussian.Norm.Basic.normSq] using
              (clear.clearance interval).lower parameter inside
        have semantics := Curve.eval_clearedEval
          p curve parameter denominatorNonzero
        rw [semantics, Gaussian.Norm.Basic.normSq_mul] at clearedLower
        have powerUpper := Curve.Substitution.normSq_denominatorPower_eval_le
          p curve interval inside
        have residualNonnegative :=
          Gaussian.Norm.Basic.normSq_nonneg (p.eval (curve.point parameter))
        have scaledUpper :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            powerUpper residualNonnegative
        apply (Fraction.Order.Field.div_le_iff_pos majorantPositive).2
        calc
          cleared.bound ≤
              Data.Gaussian.Norm.Basic.normSq
                  ((Curve.clearingState p curve).denominatorPower.eval
                    (Gaussian.Cast.Path.ofCoordinate parameter)) *
                Data.Gaussian.Norm.Basic.normSq (p.eval (curve.point parameter)) := clearedLower
          _ ≤ majorant * Data.Gaussian.Norm.Basic.normSq (p.eval (curve.point parameter)) :=
            scaledUpper
          _ = Data.Gaussian.Norm.Basic.normSq (p.eval (curve.point parameter)) * majorant :=
            Fraction.Field.mul_comm _ _ }

end Purelib.RootIsolation.Curve.Clearance.Residual

end
