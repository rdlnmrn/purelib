module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Square
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Line.Hermitian
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Projective.Bounds
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.Data.Rat.Interval.Width
public import Purelib.RootIsolation.Curve.Event.Request
public import Purelib.Geometry.Projective.Hermitian.Chart.Bounds
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Sturm.Track.Basic
import Purelib.Data.Rat.Bounds.Square

open Purelib.Data.Rat.Interval (Bounds)

open Purelib.Data

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Persistent projective shrinking of nonzero CCL curve events

Every nonconstant curve analysis has already been split into squarefree
coordinate factors and an aligned finite partition.  This module extracts the
nonzero-count leaves as explicit finite event records.  Each record carries
the existing central-third Sturm transducer and, simultaneously, a homogeneous
projective image bound for its rational boundary chart.

The homogeneous estimate remains valid across an affine pole.  It is therefore
combined with each chart's positive homogeneous-weight lower bound to obtain
the genuine finite `chi^2` shrinking fact needed to couple a narrowing
parameter event to a narrowing winding box without choosing a completed
parameter or root.
-/

namespace Purelib.RootIsolation.Curve.Event.Basic
namespace EventLeaf

/-- The homogeneous image of a requested nonzero event cell has squared
cross diameter bounded by the original chart coefficient times the requested
parameter width squared.  No affine denominator clearance is required. -/
theorem normSq_cross_request_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) {left right : Fraction.Rational}
    (leftInside : (leaf.request epsilon).cell.interval.Contains left)
    (rightInside : (leaf.request epsilon).cell.interval.Contains right) :
    Data.Gaussian.Norm.Basic.normSq
        (Geometry.Projective.Line.Hermitian.Proj.cross
          (chart.projective left) (chart.projective right)) ≤
      Curve.Projective.crossVariationCoefficient
          chart.parameterization.curve chart.cell.interval * epsilon ^ 2 := by
  let requested := leaf.request epsilon
  have requestedRefines := leaf.request_refines_chart epsilon
  have leftChart : chart.cell.interval.Contains left :=
    ⟨requestedRefines.1.trans leftInside.1,
      leftInside.2.trans requestedRefines.2⟩
  have rightChart : chart.cell.interval.Contains right :=
    ⟨requestedRefines.1.trans rightInside.1,
      rightInside.2.trans requestedRefines.2⟩
  have crossBound := Curve.Projective.normSq_cross_le
    chart.parameterization.curve chart.cell.interval leftChart rightChart
  have parameterBound :=
    Data.Rat.Interval.parameter_sub_sq_le_width_sq
      requested.cell.interval leftInside rightInside
  have widthSquare : (Bounds.width requested.cell.interval) ^ 2 ≤ epsilon ^ 2 :=
    Purelib.Data.Rat.Bounds.Square.sq_le_sq_of_nonneg (leaf.request_width_le epsilon positive)
      (Bounds.width_nonneg requested.cell.interval) positive.le
  exact crossBound.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (parameterBound.trans widthSquare)
      (Curve.Projective.crossVariationCoefficient_nonneg
        chart.parameterization.curve chart.cell.interval))

/-- The genuine squared-chordal diameter of a requested nonzero event cell is
bounded by a coefficient fixed by the original finite chart times the square
of the requested width.  The full homogeneous-weight lower bound makes this
valid even when the event interval contains an affine pole. -/
theorem chordalSq_request_le
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
      Geometry.Projective.Hermitian.HermitianForm}
    {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
    {data : Curve.Event.Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : CCL.Boundary.Charts.SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) {left right : Fraction.Rational}
    (leftInside : (leaf.request epsilon).cell.interval.Contains left)
    (rightInside : (leaf.request epsilon).cell.interval.Contains right) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (chart.projective left) (chart.projective right) ≤
      chart.uniformChordalVariationCoefficient * epsilon ^ 2 := by
  let requested := leaf.request epsilon
  have requestedRefines := leaf.request_refines_chart epsilon
  have leftChart : chart.cell.interval.Contains left :=
    ⟨requestedRefines.1.trans leftInside.1,
      leftInside.2.trans requestedRefines.2⟩
  have rightChart : chart.cell.interval.Contains right :=
    ⟨requestedRefines.1.trans rightInside.1,
      rightInside.2.trans requestedRefines.2⟩
  have parameterBound :=
    Data.Rat.Interval.parameter_sub_sq_le_width_sq
      requested.cell.interval leftInside rightInside
  have widthSquare : (Bounds.width requested.cell.interval) ^ 2 ≤ epsilon ^ 2 :=
    Purelib.Data.Rat.Bounds.Square.sq_le_sq_of_nonneg (leaf.request_width_le epsilon positive)
      (Bounds.width_nonneg requested.cell.interval) positive.le
  exact (chart.chordalSq_le_uniform leftChart rightChart).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (parameterBound.trans widthSquare)
      chart.uniformChordalVariationCoefficient_nonneg)

end EventLeaf

end Purelib.RootIsolation.Curve.Event.Basic

end
