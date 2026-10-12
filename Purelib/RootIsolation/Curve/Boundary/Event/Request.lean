module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Data.Rat.Interval.Refinement
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
public import Purelib.RootIsolation.Curve.Boundary.Event.Basic
public import Purelib.RootIsolation.Curve.Event.Residual
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.RootIsolation.Sturm.Track.Request
import Purelib.Data.Rat.Interval.Width
import Purelib.RootIsolation.Curve.Event.Chordal
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Bounds
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Request

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Geometry.Projective.Hermitian (Atom)
open Purelib.LinearAlgebra.Coordinates2.Matrix (GaussianMatrix)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)
open Purelib.RootIsolation.Sturm.Track.Basic (State)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Complete finite event families for one CCL boundary

An unresolved Hermitian boundary can have two bounded rational charts.  The
owner calculation must therefore retain the nonzero events of every chart,
not merely the first nonconstant analysis.  This module flattens those
heterogeneous chart-local families into one finite boundary family.

The coverage theorem is pointwise and finite: any displayed rational
polynomial root on the unresolved boundary is located in one explicit member
of that computed family.  No root set or completed parameter is introduced.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Event.Basic
namespace BoundaryEventEntry

/-- Refine the nonzero Sturm event retained by one member of the complete
boundary family to an arbitrary requested rational parameter width. -/
def request
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary) (epsilon : Fraction.Rational) :=
  entry.event.2.request epsilon

/-- A positive parameter-width request bounds the retained boundary event's refined interval width. -/
theorem request_width_le
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    (Bounds.width (entry.request epsilon).cell.interval) ≤ epsilon :=
  entry.event.2.request_width_le epsilon positive

/-- Continue a boundary event from any already retained nonzero-count state.
This is used when a finite sample determines a second, data-dependent width. -/
def refineRequest
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary)
    (state : State
      entry.event.1.factor.polynomial)
    (epsilon : Fraction.Rational) :
    State
      entry.event.1.factor.polynomial :=
  Sturm.Track.Request.request
    entry.event.1.factor.polynomial entry.event.1.factor.nonzero state epsilon

/-- A later boundary-event request refines the exact supplied nonzero-count state. -/
theorem refineRequest_refines
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary)
    (state : State
      entry.event.1.factor.polynomial)
    (epsilon : Fraction.Rational) :
    (entry.refineRequest state epsilon).cell.interval.Refines
      state.cell.interval :=
  Sturm.Track.Request.request_refines
    entry.event.1.factor.polynomial entry.event.1.factor.nonzero state epsilon

/-- A positive later request bounds the width of the refinement of the supplied original event state. -/
theorem refineRequest_width_le
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary)
    (state : State
      entry.event.1.factor.polynomial)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon) :
    (Bounds.width (entry.refineRequest state epsilon).cell.interval) ≤ epsilon :=
  Sturm.Track.Request.request_width_le
    entry.event.1.factor.polynomial entry.event.1.factor.nonzero state epsilon
      positive

/-- Pole-safe squared-chordal shrinking after continuing from an arbitrary
retained event state. -/
theorem chordalSq_refineRequest_le
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary)
    (state : State
      entry.event.1.factor.polynomial)
    (stateRefinesChart : state.cell.interval.Refines
      entry.chart.cell.interval)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    {left right : Fraction.Rational}
    (leftInside :
      (entry.refineRequest state epsilon).cell.interval.Contains left)
    (rightInside :
      (entry.refineRequest state epsilon).cell.interval.Contains right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (entry.chart.projective left) (entry.chart.projective right) ≤
      entry.chart.uniformChordalVariationCoefficient * epsilon ^ 2 := by
  let requested := entry.refineRequest state epsilon
  have requestedRefinesChart : requested.cell.interval.Refines
      entry.chart.cell.interval :=
    Data.Rat.Interval.Refinement.intervalRefines_trans
      (entry.refineRequest_refines state epsilon) stateRefinesChart
  have leftChart : entry.chart.cell.interval.Contains left :=
    ⟨requestedRefinesChart.1.trans leftInside.1,
      leftInside.2.trans requestedRefinesChart.2⟩
  have rightChart : entry.chart.cell.interval.Contains right :=
    ⟨requestedRefinesChart.1.trans rightInside.1,
      rightInside.2.trans requestedRefinesChart.2⟩
  have parameterBound :=
    Data.Rat.Interval.parameter_sub_sq_le_width_sq
      requested.cell.interval leftInside rightInside
  have widthSquare : (Bounds.width requested.cell.interval) ^ 2 ≤ epsilon ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct
      (Bounds.width_nonneg requested.cell.interval)
      (entry.refineRequest_width_le state epsilon positive) 2
  exact (entry.chart.chordalSq_le_uniform leftChart rightChart).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (parameterBound.trans widthSquare)
      entry.chart.uniformChordalVariationCoefficient_nonneg)

/-- Pole-safe squared-chordal shrinking, lifted through the heterogeneous
complete-boundary event wrapper used by the dispatcher. -/
theorem chordalSq_request_le
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) {left right : Fraction.Rational}
    (leftInside : (entry.request epsilon).cell.interval.Contains left)
    (rightInside : (entry.request epsilon).cell.interval.Contains right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (entry.chart.projective left) (entry.chart.projective right) ≤
      entry.chart.uniformChordalVariationCoefficient * epsilon ^ 2 :=
  entry.event.2.chordalSq_request_le epsilon positive
    leftInside rightInside

/-- Coefficient-computable original-polynomial residual bound for portions of
this heterogeneous boundary event lying in a displayed affine box. -/
def affineResidualCoefficient
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary) (targetBox : Box) :
      Fraction.Rational :=
  Curve.Event.Basic.EventLeaf.affineEventResidualCoefficient
    (targetBox := targetBox) entry.event.1

/-- The original boundary event's coefficient for affine residuals in the supplied target box is nonnegative. -/
theorem affineResidualCoefficient_nonneg
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary) (targetBox : Box) :
    0 ≤ entry.affineResidualCoefficient targetBox :=
  Curve.Event.Basic.EventLeaf.affineEventResidualCoefficient_nonneg
    (targetBox := targetBox) entry.event.1

/-- Every affine meeting of a requested boundary event with `targetBox` has
the corresponding uniformly small original-polynomial residual. -/
theorem
  normSq_eval_point_request_le_of_inside
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    (entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary) (targetBox : Box)
    (epsilon : Fraction.Rational) (positive : 0 < epsilon)
    (parameter : Fraction.Rational)
    (parameterInside :
      (entry.request epsilon).cell.interval.Contains parameter)
    (denominatorNonzero :
      entry.chart.parameterization.curve.denominatorAt parameter ≠ 0)
    (pointInside : targetBox.Contains
      (entry.chart.parameterization.curve.point parameter)) :
    Data.Gaussian.Norm.Basic.normSq
        (p.eval (entry.chart.parameterization.curve.point parameter)) ≤
      entry.affineResidualCoefficient targetBox * epsilon ^ 2 := by
  simpa only [affineResidualCoefficient] using
    entry.event.2.normSq_eval_point_request_le_of_inside
      (targetBox := targetBox) epsilon positive parameter parameterInside
        denominatorNonzero pointInside

end BoundaryEventEntry
end Purelib.RootIsolation.Curve.Boundary.Event.Basic

end
