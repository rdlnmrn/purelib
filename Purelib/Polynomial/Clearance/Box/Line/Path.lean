module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Cast.Imaginary
public import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Intervals
public import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Clearance.Pair.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Data.Gaussian.Cast
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Clearance.Box.Line.Basic (HorizontalLineClearance VerticalLineClearance)
open Purelib.Polynomial.Clearance.Pair.Basic (Certificate)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Quantitative clearance on constructive box boundaries

Path certificates on horizontal and vertical lines are converted to geometric
side certificates.  Four finite positive bounds combine by minimum into one
box-boundary certificate.
-/

namespace Purelib.Polynomial.Clearance.Box.Line

/-- Convert geometric vertical-line clearance back to the exact affine path
certificate used by the finite Cauchy construction. -/
def Basic.VerticalLineClearance.toPathCertificate
    {p : CoefficientPolynomial} {ambient : Box} {x : Fraction.Rational}
    (clearance : VerticalLineClearance p ambient x) :
    Certificate
      (Dense.Gaussian.Path.Components.pathReal p (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)
      (Dense.Gaussian.Path.Components.pathImag p (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)
      ⟨ambient.yLower, ambient.yUpper, ambient.y_valid⟩ where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro y inside
    have bound := clearance.lower y inside.1 inside.2
    simpa only [Data.Gaussian.Norm.Basic.normSq,
      Canonical.normSq, pow_two, Dense.Gaussian.Path.Components.eval_pathReal,
        Dense.Gaussian.Path.Components.eval_pathImag, Purelib.Geometry.Rational.Affine.Axis.line_vertical]
      using bound

/-- Conversion to the exact coordinate-path certificate retains the original bound. -/
@[simp] theorem Basic.VerticalLineClearance.toPathCertificate_bound
    {p : CoefficientPolynomial} {ambient : Box} {x : Fraction.Rational}
    (clearance : VerticalLineClearance p ambient x) :
    clearance.toPathCertificate.bound = clearance.bound := rfl

/-- Convert geometric horizontal-line clearance back to the exact affine
path certificate used by the finite Cauchy construction. -/
def Basic.HorizontalLineClearance.toPathCertificate
    {p : CoefficientPolynomial} {ambient : Box} {y : Fraction.Rational}
    (clearance : HorizontalLineClearance p ambient y) :
    Certificate
      (Dense.Gaussian.Path.Components.pathReal p (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection)
      (Dense.Gaussian.Path.Components.pathImag p (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection)
      ⟨ambient.xLower, ambient.xUpper, ambient.x_valid⟩ where
  bound := clearance.bound
  positive := clearance.positive
  lower := by
    intro x inside
    have bound := clearance.lower x inside.1 inside.2
    simpa only [Data.Gaussian.Norm.Basic.normSq,
      Canonical.normSq, pow_two, Dense.Gaussian.Path.Components.eval_pathReal,
        Dense.Gaussian.Path.Components.eval_pathImag, Purelib.Geometry.Rational.Affine.Axis.line_horizontal]
      using bound

/-- Conversion to the exact coordinate-path certificate retains the original bound. -/
@[simp] theorem Basic.HorizontalLineClearance.toPathCertificate_bound
    {p : CoefficientPolynomial} {ambient : Box} {y : Fraction.Rational}
    (clearance : HorizontalLineClearance p ambient y) :
    clearance.toPathCertificate.bound = clearance.bound := rfl

/-- Convert a finite coordinate-path certificate for `x + it` into geometric
vertical-line clearance. -/
def Path.verticalOfPathCertificate
    (p : CoefficientPolynomial) (ambient : Box) (x : Fraction.Rational)
    (certificate : Certificate
      (Dense.Gaussian.Path.Components.pathReal p (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)
      (Dense.Gaussian.Path.Components.pathImag p (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)
      (Box.Intervals.verticalInterval ambient)) : VerticalLineClearance p ambient x where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro y lower upper
    have bound := certificate.lower y ⟨lower, upper⟩
    simpa only [Data.Gaussian.Norm.Basic.normSq,
      Canonical.normSq, pow_two, Dense.Gaussian.Path.Components.eval_pathReal,
        Dense.Gaussian.Path.Components.eval_pathImag, Purelib.Geometry.Rational.Affine.Axis.line_vertical]
      using bound

/-- Conversion from the vertical coordinate-path certificate retains its exact clearance bound. -/
@[simp] theorem Path.verticalOfPathCertificate_bound
    (p : CoefficientPolynomial) (ambient : Box) (x : Fraction.Rational)
    (certificate : Certificate
      (Dense.Gaussian.Path.Components.pathReal p (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)
      (Dense.Gaussian.Path.Components.pathImag p (Gaussian.Cast.Winding.verticalBase x)
        Gaussian.Constants.imaginaryUnit)
      (Box.Intervals.verticalInterval ambient)) :
    (Clearance.Box.Line.Path.verticalOfPathCertificate p ambient x certificate).bound =
      certificate.bound := rfl

/-- Convert a finite coordinate-path certificate for `t + iy` into geometric
horizontal-line clearance. -/
def Path.horizontalOfPathCertificate
    (p : CoefficientPolynomial) (ambient : Box) (y : Fraction.Rational)
    (certificate : Certificate
      (Dense.Gaussian.Path.Components.pathReal p (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection)
      (Dense.Gaussian.Path.Components.pathImag p (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection)
      (Box.Intervals.horizontalInterval ambient)) : HorizontalLineClearance p ambient y where
  bound := certificate.bound
  positive := certificate.positive
  lower := by
    intro x lower upper
    have bound := certificate.lower x ⟨lower, upper⟩
    simpa only [Data.Gaussian.Norm.Basic.normSq,
      Canonical.normSq, pow_two, Dense.Gaussian.Path.Components.eval_pathReal,
        Dense.Gaussian.Path.Components.eval_pathImag, Purelib.Geometry.Rational.Affine.Axis.line_horizontal]
      using bound

/-- Conversion from the horizontal coordinate-path certificate retains its exact clearance bound. -/
@[simp] theorem Path.horizontalOfPathCertificate_bound
    (p : CoefficientPolynomial) (ambient : Box) (y : Fraction.Rational)
    (certificate : Certificate
      (Dense.Gaussian.Path.Components.pathReal p (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection)
      (Dense.Gaussian.Path.Components.pathImag p (Gaussian.Cast.Imaginary.horizontalBase y)
        Gaussian.Constants.horizontalDirection)
      (Box.Intervals.horizontalInterval ambient)) :
    (Clearance.Box.Line.Path.horizontalOfPathCertificate p ambient y certificate).bound =
      certificate.bound := rfl
end Purelib.Polynomial.Clearance.Box.Line

end
