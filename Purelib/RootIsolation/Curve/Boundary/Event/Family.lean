module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Attach
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Boundary.Analysis
public import Purelib.RootIsolation.Curve.Boundary.Event.Basic
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Family
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Curve.Clearance.Global
import Purelib.RootIsolation.Curve.Clearance.Residual

open Purelib.Geometry.Projective.Hermitian (Atom)
open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.LinearAlgebra.Coordinates2.Matrix (GaussianMatrix)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)
open Purelib.RootIsolation.Curve.Boundary.Event.Basic (BoundaryEventEntry)
open Purelib.RootIsolation.Curve.Chart (BoundedAnalysis)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

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

namespace Purelib.RootIsolation.Curve.Boundary.Event.Family

/-- Extract every nonzero event from one attached chart analysis. -/
def eventEntriesOfAnalysis
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (entry : Sigma fun chart : BoundedChart atom.form =>
      BoundedAnalysis p current chart)
    (member : entry ∈ boundary.analyses) :
    List (BoundaryEventEntry boundary) :=
  match entry with
  | ⟨_chart, .identicallyZero _realZero _imaginaryZero⟩ => []
  | ⟨_chart, .clear _certificate _residual⟩ => []
  | ⟨chart, .events data gcdDegreePositive factors factors_eq⟩ =>
      (Curve.Event.Family.eventFamily factors).attach.map
        fun attached =>
          { chart := chart
            data := data
            gcdDegreePositive := gcdDegreePositive
            factors := factors
            factors_eq := factors_eq
            analysisMember := member
            event := attached.1
            eventMember := attached.2 }

/-- Complete finite nonzero-event family of every bounded chart belonging to
one dispatched Hermitian boundary. -/
def boundaryEventFamily
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom) : List (BoundaryEventEntry boundary) :=
  boundary.analyses.attach.flatMap fun attached =>
    eventEntriesOfAnalysis boundary attached.1 attached.2

/-- Every retained event of an executed chart analysis belongs to that analysis's computed boundary-entry list. -/
theorem mem_eventEntriesOfAnalysis_events
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (chart : BoundedChart atom.form)
    (data : Curve.Event.Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (factors : List (CCL.Boundary.Charts.SourcePersistentBoundaryEventsSquarefreeFactorAnalysisAlias p current chart
      data
      gcdDegreePositive))
    (factors_eq : factors =
      Curve.Chart.analyzeSquarefreeFactors p current chart
        data gcdDegreePositive)
    (analysisMember :
      (⟨chart, BoundedAnalysis.events data
        gcdDegreePositive factors factors_eq⟩ :
        Sigma fun chart : BoundedChart atom.form =>
          BoundedAnalysis p current chart) ∈
        boundary.analyses)
    (event : Curve.Event.Family.SourcePersistentBoundaryEventsEventEntryAlias (p := p) (box := current) (form :=
      atom.form)
      (chart := chart) (data := data)
        (gcdDegreePositive := gcdDegreePositive))
    (eventMember : event ∈
      Curve.Event.Family.eventFamily factors) :
    ({ chart := chart
       data := data
       gcdDegreePositive := gcdDegreePositive
       factors := factors
       factors_eq := factors_eq
       analysisMember := analysisMember
       event := event
       eventMember := eventMember } : BoundaryEventEntry boundary) ∈
      eventEntriesOfAnalysis boundary
        ⟨chart, BoundedAnalysis.events data
          gcdDegreePositive factors factors_eq⟩ analysisMember := by
  rw [eventEntriesOfAnalysis]
  apply Data.List.Map.mem_map.mpr
  exact ⟨⟨event, eventMember⟩, Data.List.Attach.mem_attach _ _, rfl⟩

/-- An original event of a retained member chart analysis occurs in the complete dispatched boundary family. -/
theorem mem_boundaryEventFamily_of_event
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (chart : BoundedChart atom.form)
    (data : Curve.Event.Nontrivial p
      chart.parameterization.curve)
    (gcdDegreePositive : 0 <
      (Curve.Substitution.gcdPolynomial p
        chart.parameterization.curve).natDegree)
    (factors : List (CCL.Boundary.Charts.SourcePersistentBoundaryEventsSquarefreeFactorAnalysisAlias p current chart
      data
      gcdDegreePositive))
    (factors_eq : factors =
      Curve.Chart.analyzeSquarefreeFactors p current chart
        data gcdDegreePositive)
    (analysisMember :
      (⟨chart, BoundedAnalysis.events data
        gcdDegreePositive factors factors_eq⟩ :
        Sigma fun chart : BoundedChart atom.form =>
          BoundedAnalysis p current chart) ∈
        boundary.analyses)
    (event : Curve.Event.Family.SourcePersistentBoundaryEventsEventEntryAlias (p := p) (box := current) (form :=
      atom.form)
      (chart := chart) (data := data)
        (gcdDegreePositive := gcdDegreePositive))
    (eventMember : event ∈
      Curve.Event.Family.eventFamily factors) :
    ({ chart := chart
       data := data
       gcdDegreePositive := gcdDegreePositive
       factors := factors
       factors_eq := factors_eq
       analysisMember := analysisMember
       event := event
       eventMember := eventMember } : BoundaryEventEntry boundary) ∈
      boundaryEventFamily boundary := by
  rw [boundaryEventFamily]
  apply Data.List.Flatten.mem_flatMap.mpr
  refine ⟨⟨⟨chart,
    BoundedAnalysis.events data
      gcdDegreePositive factors factors_eq⟩, analysisMember⟩,
    Data.List.Attach.mem_attach _ _, ?_⟩
  exact mem_eventEntriesOfAnalysis_events boundary chart data
    gcdDegreePositive factors factors_eq analysisMember event eventMember
end Purelib.RootIsolation.Curve.Boundary.Event.Family

end
