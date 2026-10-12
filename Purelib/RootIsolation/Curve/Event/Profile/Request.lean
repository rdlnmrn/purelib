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
import Purelib.RootIsolation.Curve.Event.Partition.Resolution
import Purelib.RootIsolation.Curve.Event.Partition.Squarefree.Resolution
public import Purelib.RootIsolation.Curve.Event.Profile.Basic
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
import Purelib.Polynomial.Dense.Rational.Factorization.Condition.Profile
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Box.Conditions
import Purelib.RootIsolation.Curve.Chart.Analysis

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Boundary.Charts
  (SourcePersistentConditionProfilesProfileAnalysisAlias
   SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias)
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
# Persistent CCL events after exact box-condition splitting

Every original squarefree curve factor has been split by executable gcd
against all four cleared box-edge polynomials.  This module runs the aligned
Sturm-event construction on each final profile factor and exposes the same
finite residual estimate used by the unsplit event layer.

Each profile already records, for every edge, either exact equality ownership
or explicit Bezout coprimality.  The next owner layer can therefore stabilize
the signs of only the genuinely apart edges.
-/

namespace Purelib.RootIsolation.Curve.Event.Profile.Basic
namespace ProfileEventLeaf

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
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) (epsilon : Fraction.Rational) :
    Sturm.Track.Basic.State
      analysis.profile.factor.polynomial :=
  Sturm.Track.Request.request
    analysis.profile.factor.polynomial analysis.profile.factor.nonzero
      leaf.state epsilon

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
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) (epsilon : Fraction.Rational) :
    (leaf.request epsilon).cell.interval.Refines chart.cell.interval :=
  Data.Rat.Interval.Refinement.intervalRefines_trans
    (Sturm.Track.Request.request_refines
      analysis.profile.factor.polynomial analysis.profile.factor.nonzero
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
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) (epsilon : Fraction.Rational)
    (positive : 0 < epsilon) :
    (Bounds.width (leaf.request epsilon).cell.interval) ≤ epsilon :=
  Sturm.Track.Request.request_width_le
    analysis.profile.factor.polynomial analysis.profile.factor.nonzero
      leaf.state epsilon positive

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
    {factorAnalysis : SourcePersistentConditionProfilesSquarefreeFactorAnalysisAlias p box chart
      data
      gcdDegreePositive}
    {analysis : SourcePersistentConditionProfilesProfileAnalysisAlias factorAnalysis}
    (leaf : Curve.Event.Profile.Basic.ProfileEventLeaf analysis) (epsilon : Fraction.Rational) :
    Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
      (Dense.Rational.Pair.Reduction.reducedNumerator
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      (leaf.request epsilon).cell.interval := by
  apply Sturm.Event.polynomialEventResolutionOfBounds
    analysis.profile.factor.polynomial chart.cell (leaf.request epsilon).cell
  · exact leaf.request_refines_chart epsilon
  · have refinesLeaf :
        (leaf.request epsilon).cell.interval.Refines leaf.cell.interval := by
      simpa only [request, leaf.state_cell] using
        Sturm.Track.Request.request_refines
          analysis.profile.factor.polynomial analysis.profile.factor.nonzero
            leaf.state epsilon
    have widthLe : (Bounds.width (leaf.request epsilon).cell.interval) ≤
        (Bounds.width leaf.cell.interval) := Fraction.Order.Arithmetic.sub_le_sub_direct
          refinesLeaf.2 refinesLeaf.1
    have leafWidthSmall : (Bounds.width leaf.cell.interval) <
        Curve.Event.Partition.Squarefree.squarefreeLeafWidth
          analysis.profile.factor.polynomial analysis.profile.factor.squarefree
            chart.parameterization.curve box chart.cell := by
      simpa only [leaf.classification_cell] using
        leaf.classification.widthSmall
    exact widthLe.trans_lt
      (leafWidthSmall.trans_le
        ((Curve.Event.Partition.Squarefree.squarefreeLeafWidth_le_common
          analysis.profile.factor.polynomial analysis.profile.factor.squarefree
            chart.parameterization.curve box chart.cell).trans
          (Curve.Event.Partition.commonLeafWidth_le_event
            analysis.profile.factor.polynomial
              chart.parameterization.curve box chart.cell)))
end ProfileEventLeaf
end Purelib.RootIsolation.Curve.Event.Profile.Basic

end
