module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Interval.Refinement
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
import Purelib.RootIsolation.Curve.Event.Profile.Basic
public import Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
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
import Purelib.RootIsolation.Sturm.Count.Basic

open Purelib.Data.Rat.Interval (Bounds)
open Purelib.RootIsolation.Curve.Event.Profile.Basic (SourcePersistentProfileRequestFamilyProfileEventLeafAlias)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Complete finite refinement families for profile events

`SturmNonzeroEvent.request` deliberately follows one nonzero child.  That is
the right interface for one persistent algebraic event, but it is not a
complete refinement when the starting cell has several nonzero children.
This module builds the full finite binary refinement at a requested width,
filters all and only the nonzero-count children, and retains pointwise
coverage for every supplied displayed rational profile zero.

The construction uses only finite subdivision trees and integer event counts.
In particular, nonzero count is never converted into a root-existence claim.
-/

namespace Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic
section Profile

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {box : Box} {form :
  Geometry.Projective.Hermitian.HermitianForm}
variable {chart : Geometry.Projective.Hermitian.Chart.BoundedChart form}
variable {data : Curve.Event.Nontrivial p
  chart.parameterization.curve}
variable {gcdDegreePositive : 0 <
  (Curve.Substitution.gcdPolynomial p
    chart.parameterization.curve).natDegree}
variable {factorAnalysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilySquarefreeFactorAnalysisAlias p box
  chart data
  gcdDegreePositive}
variable {analysis : CCL.Boundary.Charts.SourcePersistentProfileRequestFamilyProfileAnalysisAlias factorAnalysis}
namespace CompleteRequestLeaf

/-- Follow this retained child itself, rather than restarting a later request
from its original profile parent.  This is the persistent finite event branch
used after an owner has been selected. -/
def request {leaf :
  SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
  Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational) :
    Sturm.Track.Basic.State
      analysis.profile.factor.polynomial :=
  Sturm.Track.Request.request
    analysis.profile.factor.polynomial analysis.profile.factor.nonzero
      entry.state target

/-- A later request refines this exact retained subdivision child. -/
theorem request_refines
    {leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational) :
    (entry.request target).cell.interval.Refines entry.cell.interval := by
  simpa only [request,
    Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.state] using
    Sturm.Track.Request.request_refines
      analysis.profile.factor.polynomial analysis.profile.factor.nonzero
        entry.state target

/-- A later request on the retained child stays inside its original chart. -/
theorem request_refines_chart
    {leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational) :
    (entry.request target).cell.interval.Refines chart.cell.interval :=
  Data.Rat.Interval.Refinement.intervalRefines_trans
    (entry.request_refines target) entry.refines_chart

/-- A positive later request bounds the width of the retained child's deterministic refinement. -/
theorem request_width_le
    {leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational)
    (positive : 0 < target) :
    (Bounds.width (entry.request target).cell.interval) ≤ target := by
  simpa only [request,
    Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf.state] using
    Sturm.Track.Request.request_width_le
      analysis.profile.factor.polynomial analysis.profile.factor.nonzero
        entry.state target positive

end CompleteRequestLeaf

/-- Finite Cauchy--Sturm resolution along the deterministic descendant path
of one already retained child.  The construction preserves only its explicit
nonzero integer count and rational interval refinements. -/
def CompleteRequestLeaf.requestResolution
    {leaf : SourcePersistentProfileRequestFamilyProfileEventLeafAlias analysis} {epsilon :
      Fraction.Rational}
    (entry : Curve.Event.Profile.Complete.Basic.CompleteRequestLeaf leaf epsilon) (target : Fraction.Rational) :
    Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
      (Dense.Rational.Pair.Reduction.reducedNumerator
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      (Dense.Rational.Pair.Reduction.reducedDenominator
        (Dense.Derivative.derivative
          analysis.profile.factor.polynomial)
        analysis.profile.factor.polynomial)
      (entry.request target).cell.interval := by
  apply
    Sturm.Event.polynomialEventResolutionOfBounds
      analysis.profile.factor.polynomial chart.cell
        (entry.request target).cell
  · exact entry.request_refines_chart target
  · have requestEntry :
        (entry.request target).cell.interval.Refines entry.cell.interval :=
      entry.request_refines target
    have requestLeaf :
        (entry.request target).cell.interval.Refines leaf.cell.interval :=
      Data.Rat.Interval.Refinement.intervalRefines_trans requestEntry
        entry.refines_leaf
    have requestWidth : (Bounds.width (entry.request target).cell.interval) ≤
        (Bounds.width leaf.cell.interval) :=
      Fraction.Order.Arithmetic.sub_le_sub_direct requestLeaf.2 requestLeaf.1
    have leafWidthSmall : (Bounds.width leaf.cell.interval) <
        Curve.Event.Partition.Squarefree.squarefreeLeafWidth
          analysis.profile.factor.polynomial analysis.profile.factor.squarefree
            chart.parameterization.curve box chart.cell := by
      simpa only [leaf.classification_cell] using
        leaf.classification.widthSmall
    exact requestWidth.trans_lt
      (leafWidthSmall.trans_le
        ((Curve.Event.Partition.Squarefree.squarefreeLeafWidth_le_common
          analysis.profile.factor.polynomial
            analysis.profile.factor.squarefree
              chart.parameterization.curve box chart.cell).trans
          (Curve.Event.Partition.commonLeafWidth_le_event
            analysis.profile.factor.polynomial chart.parameterization.curve
              box chart.cell)))

end Profile

/-! ## Complete requested families through a dispatched boundary -/

end Purelib.RootIsolation.Curve.Event.Profile.Complete.Basic

end
