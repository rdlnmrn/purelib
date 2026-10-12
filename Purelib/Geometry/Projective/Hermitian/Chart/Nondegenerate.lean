module
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
public import Purelib.Geometry.Projective.Hermitian.Chart.Coverage
import Purelib.Geometry.Projective.Hermitian.Chart.Source
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.RationalFunctions.Curve.Canonical.Circle.Basic
import Purelib.RationalFunctions.Curve.Canonical.Circle.Inverse
import Purelib.RationalFunctions.Curve.Canonical.Line
public import Purelib.RationalFunctions.Curve.Nondegenerate

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic

section

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Projective

open Purelib.Geometry.Projective.Hermitian

open Purelib.LinearAlgebra.Coordinates2.Matrix

open Purelib.RationalFunctions

open Purelib.RationalFunctions.Curve

open Purelib.RationalFunctions.Curve.Canonical

section
public section

/-!
# Nondegeneracy of the finite CCL boundary charts

Every active curve source is a genuine rational line or a nonzero-radius
circle transported by an invertible finite homography.  Consequently its
homogeneous denominator is a represented nonzero coordinate polynomial, and
its affine values are injective at non-pole parameters.

The final theorem uses only finitely many parameters: one denominator-safe
point in each of `natDegree + 1` disjoint unit intervals.  If both cleared
coordinates vanished identically, these points would give too many distinct
displayed roots of the original Gaussian-rational polynomial.
-/

namespace Purelib.Geometry.Projective.Hermitian.Chart

namespace BoundedChart

/-- The bounded chart has a nonzero denominator polynomial and is injective at non-pole parameters.

This is the nondegeneracy predicate of the retained rational curve, with no change to its coefficients or chart cell. -/
@[expose] def Nondegenerate {form : Hermitian.HermitianForm} (chart : Chart.BoundedChart form) : Prop :=
  RationalCurve.Nondegenerate chart.parameterization.curve

end BoundedChart

/-- Every chart emitted by the complete bounded source family is genuinely nondegenerate. Radius-zero norm comparisons
were classified as finite singleton boundaries before reaching this function. -/
theorem nondegenerate_of_mem_charts
    {reference : GaussianMatrix} {form : Hermitian.HermitianForm}
    (source : Chart.CurveSource reference form)
    (box : Rational.Box) (denominatorMargin : Fraction.Rational)
    (marginPositive : 0 < denominatorMargin)
    (chart : Chart.BoundedChart form)
    (member : chart ∈ Chart.charts source box
      denominatorMargin marginPositive) :
    chart.Nondegenerate := by
  cases source with
  | norm matrix determinantNonzero lowerRow base baseNonzero form_eq =>
      subst form
      change chart ∈ [_, _] at member
      rcases Purelib.Data.List.Membership.mem_cons.mp member with primary | remainder
      · subst chart
        exact Curve.transformed_nondegenerate matrix determinantNonzero
          (Circle.circle base) (Circle.circle_denominator_ne base)
          (Circle.circle_point_injective base baseNonzero)
      have reciprocal := Purelib.Data.List.Membership.mem_singleton.mp remainder
      subst chart
      exact Curve.transformed_nondegenerate matrix determinantNonzero
        (Circle.reciprocalCircle base) (Circle.reciprocalCircle_denominator_ne base)
        (Circle.reciprocalCircle_point_injective base baseNonzero)
  | real matrix determinantNonzero lowerRow threshold form_eq =>
      subst form
      change chart ∈ [_] at member
      have equal := Purelib.Data.List.Membership.mem_singleton.mp member
      subst chart
      exact Curve.transformed_nondegenerate matrix determinantNonzero
        (Line.realLine threshold)
        (Line.realLine_denominator_ne threshold)
        (Line.realLine_point_injective threshold)
  | imaginary matrix determinantNonzero lowerRow threshold form_eq =>
      subst form
      change chart ∈ [_] at member
      have equal := Purelib.Data.List.Membership.mem_singleton.mp member
      subst chart
      exact Curve.transformed_nondegenerate matrix determinantNonzero
        (Line.imaginaryLine threshold)
        (Line.imaginaryLine_denominator_ne threshold)
        (Line.imaginaryLine_point_injective threshold)
end Purelib.Geometry.Projective.Hermitian.Chart

end

end
