module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Interval.Refinement
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Reduction
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Event.Analysis
public import Purelib.RootIsolation.Curve.Event.Basic
import Purelib.RootIsolation.Curve.Event.Partition.Resolution
import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Resolution
import Purelib.RootIsolation.Sturm.Event.Resolution
import Purelib.RootIsolation.Sturm.Track.Basic
public import Purelib.RootIsolation.Sturm.Track.Request
import Purelib.Data.Rat.Interval.Width
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RootIsolation.Curve.Chart.Analysis

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Boundary.Charts (SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias)
open Purelib.RootIsolation.Curve.Event (Nontrivial)

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

/-- Refine the retained nonzero-count Sturm leaf to the requested accuracy.

The operation uses the original factor and state, preserving its chart ownership and count certificate. -/
def request
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational) :
    Sturm.Track.Basic.State factorAnalysis.factor.polynomial :=
  Sturm.Track.Request.request factorAnalysis.factor.polynomial
    factorAnalysis.factor.nonzero leaf.state epsilon

/-- The requested refinement remains inside the original chart interval. -/
theorem request_refines_chart
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational) :
    (leaf.request epsilon).cell.interval.Refines chart.cell.interval := by
  exact Data.Rat.Interval.Refinement.intervalRefines_trans
    (Sturm.Track.Request.request_refines
      factorAnalysis.factor.polynomial factorAnalysis.factor.nonzero
        leaf.state epsilon)
    (by simpa only [leaf.state_cell] using leaf.cell_refines_chart)

/-- A positive accuracy bounds the width of the requested original Sturm refinement. -/
theorem request_width_le
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    (Bounds.width (leaf.request epsilon).cell.interval) ≤ epsilon :=
  Sturm.Track.Request.request_width_le
    factorAnalysis.factor.polynomial factorAnalysis.factor.nonzero leaf.state
      epsilon positive

/-- Resolve the original Cauchy scan on the requested Sturm refinement.

The inherited nonzero count and original event width bound supply the retained finite separation certificate. -/
def requestResolution
    {p : CoefficientPolynomial} {box : Box} {form :
      HermitianForm}
    {chart : BoundedChart form}
    {data : Nontrivial p
      chart.parameterization.curve}
    {gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree}
    {factorAnalysis : SourcePersistentCurveEventsSquarefreeFactorAnalysisAlias p box chart data
      gcdDegreePositive}
    (leaf : Curve.Event.Basic.EventLeaf factorAnalysis) (epsilon : Fraction.Rational) :
    Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
      (Dense.Rational.Pair.Reduction.reducedNumerator
        (Dense.Derivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial)
      (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative factorAnalysis.factor.polynomial)
        factorAnalysis.factor.polynomial)
      (leaf.request epsilon).cell.interval := by
  apply Sturm.Event.polynomialEventResolutionOfBounds
    factorAnalysis.factor.polynomial chart.cell (leaf.request epsilon).cell
  · exact leaf.request_refines_chart epsilon
  · have refinesLeaf :
        (leaf.request epsilon).cell.interval.Refines leaf.cell.interval := by
      simpa only [request, leaf.state_cell] using
        Sturm.Track.Request.request_refines
          factorAnalysis.factor.polynomial factorAnalysis.factor.nonzero
            leaf.state epsilon
    have widthLe : (Bounds.width (leaf.request epsilon).cell.interval) ≤
        (Bounds.width leaf.cell.interval) :=
      Fraction.Order.Arithmetic.sub_le_sub_direct refinesLeaf.2 refinesLeaf.1
    have leafWidthSmall : (Bounds.width leaf.cell.interval) <
        Curve.Event.Partition.Squarefree.squarefreeLeafWidth
          factorAnalysis.factor.polynomial factorAnalysis.factor.squarefree
            chart.parameterization.curve box chart.cell := by
      simpa only [leaf.classification_cell] using
        leaf.classification.widthSmall
    exact widthLe.trans_lt
      (leafWidthSmall.trans_le
        ((Curve.Event.Partition.Squarefree.squarefreeLeafWidth_le_common
          factorAnalysis.factor.polynomial factorAnalysis.factor.squarefree
            chart.parameterization.curve box chart.cell).trans
          (Curve.Event.Partition.commonLeafWidth_le_event
            factorAnalysis.factor.polynomial chart.parameterization.curve box
              chart.cell)))
end EventLeaf

end Purelib.RootIsolation.Curve.Event.Basic

end
