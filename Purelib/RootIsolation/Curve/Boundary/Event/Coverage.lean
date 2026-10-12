module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.List.Map
import Purelib.Geometry.Projective.Chordal.Basic
import Purelib.Geometry.Projective.Chordal.Equivalence
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Coverage
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Projective.Line.Basic
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Projective.Basic
import Purelib.RootIsolation.Curve.Boundary.Analysis
public import Purelib.RootIsolation.Curve.Boundary.Event.Analysis
import Purelib.RootIsolation.Curve.Boundary.Event.Basic
public import Purelib.RootIsolation.Curve.Boundary.Event.Family
import Purelib.RootIsolation.Curve.Chart.Analysis
import Purelib.RootIsolation.Curve.Event.Family
public import Purelib.RootIsolation.Curve.Event.Located
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.Squarefree.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.CCL.Boundary.Charts
import Purelib.RootIsolation.Curve.Clearance.Global
import Purelib.RootIsolation.Curve.Clearance.Residual
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.Curve.Event.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Projective.Hermitian (Atom)
open Purelib.LinearAlgebra.Coordinates2.Matrix (GaussianMatrix)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.Curve.Boundary.Analysis (CurveBoundary)

open Purelib.Data

open Purelib

open Purelib.Data.Rat

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

namespace Purelib.RootIsolation.Curve.Boundary.Event.Coverage

set_option genInjectivity false in
/-- A displayed rational polynomial root on a boundary, located in one
specific member of the complete finite boundary-event family. -/
structure LocatedBoundaryEvent
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (value : Canonical) where
  /-- The actual boundary-family entry containing the displayed root. -/ entry :
    Curve.Boundary.Event.Basic.BoundaryEventEntry boundary
  /-- The retained entry belongs to the original complete boundary-event family. -/ member : entry ∈
    Curve.Boundary.Event.Family.boundaryEventFamily boundary
  /-- The displayed rational parameter of this boundary event. -/ parameter : Fraction.Rational
  /-- The retained parameter lies in the selected event interval. -/ parameterInside :
    entry.event.2.cell.interval.Contains parameter
  /-- The retained parameter is an exact zero of the selected event factor. -/ factorZero :
    entry.event.1.factor.polynomial.eval parameter = 0
  /-- The retained chart's denominator is nonzero at this parameter. -/ denominatorNonzero :
    entry.chart.parameterization.curve.denominatorAt parameter ≠ 0
  /-- The chart point at the retained parameter equals the displayed affine root. -/ point_eq :
    entry.chart.parameterization.curve.point parameter = value

constructive_injectivity LocatedBoundaryEvent

namespace LocatedBoundaryEvent

/-- The chart point retained by a located boundary event is exactly the
homogeneous representative of its displayed affine value. -/
theorem projective_equivalent_affine
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {value : Canonical} (located : Curve.Boundary.Event.Coverage.LocatedBoundaryEvent boundary value) :
    (located.entry.chart.projective located.parameter).Equivalent
      (Geometry.Projective.Line.Proj.affine value) := by
  have equivalent :=
    Curve.Projective.projective_equivalent_affine
      located.entry.chart.parameterization.curve located.parameter
        located.denominatorNonzero
  simpa only [Geometry.Projective.Hermitian.Chart.BoundedChart.projective,
    located.point_eq] using equivalent

/-- Any squared-chordal comparison can be transported without loss from the
located chart representation to the displayed affine boundary point. -/
theorem chordalSq_eq_affine
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    {boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom}
    {value : Canonical} (located : Curve.Boundary.Event.Coverage.LocatedBoundaryEvent boundary value)
    (other : Geometry.Projective.Line.GaussianLine) :
    Geometry.Projective.Chordal.Basic.chordalSq
        (located.entry.chart.projective located.parameter) other =
      Geometry.Projective.Chordal.Basic.chordalSq (Geometry.Projective.Line.Proj.affine value) other := by
  exact Geometry.Projective.Chordal.Equivalence.chordalSq_eq_of_equivalent_left
    (located.entry.chart.projective_valid located.parameter)
    (Geometry.Projective.Line.Gaussian.Proj.affine_hasNonzeroCoordinate value)
    located.projective_equivalent_affine other

end LocatedBoundaryEvent

/-- Pointwise completeness of the finite boundary-event family. -/
def locateBoundaryRoot
    {p : CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {reference : GaussianMatrix} {current : Box}
    {denominatorMargin : Fraction.Rational} {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p reference current denominatorMargin
      marginPositive atom)
    (value : Canonical) (inside : current.Contains value)
    (onBoundary : atom.form.eval value = 0)
    (root : p.eval value = 0)
    (denominatorLower : denominatorMargin ≤
      Data.Gaussian.Norm.Basic.normSq
        (Geometry.Projective.Homography.Basic.denominator reference value)) :
    LocatedBoundaryEvent boundary value := by
  let covered := Geometry.Projective.Hermitian.Chart.CurveSource.cover
    boundary.source current marginPositive value inside onBoundary
      denominatorLower
  rcases covered with
    ⟨chart, chartMember, parameter, parameterInside,
      curveDenominatorNonzero, pointEq⟩
  let analysis := Curve.Chart.analyzeChart p current chart
  let analysisEntry : Sigma fun chart : Geometry.Projective.Hermitian.Chart.BoundedChart atom.form =>
      Curve.Chart.BoundedAnalysis p current chart :=
    ⟨chart, analysis⟩
  have analysisMember : analysisEntry ∈ boundary.analyses := by
    rw [boundary.analyses_eq]
    exact Data.List.Map.mem_map.mpr ⟨chart, chartMember, rfl⟩
  dsimp only [analysisEntry, analysis] at analysisMember
  generalize analysisEq :
    Curve.Chart.analyzeChart p current chart = result
      at analysisMember
  cases result with
  | identicallyZero realZero imaginaryZero =>
      exact (Curve.Boundary.Event.Analysis.identicallyZero_absurd
        degreePositive boundary chart realZero imaginaryZero
          analysisMember).elim
  | clear certificate residual =>
      have lower := residual.lower parameter parameterInside
        curveDenominatorNonzero
      have curveRoot :
          p.eval (chart.parameterization.curve.point parameter) = 0 := by
        rw [pointEq]
        exact root
      rw [curveRoot, Gaussian.Norm.Basic.normSq_zero] at lower
      exact ((not_lt_of_ge lower) residual.positive).elim
  | events data gcdDegreePositive factors factors_eq =>
      have curveRoot :
          p.eval (chart.parameterization.curve.point parameter) = 0 := by
        rw [pointEq]
        exact root
      have curveInside :
          current.Contains (chart.parameterization.curve.point parameter) := by
        rw [pointEq]
        exact inside
      let located := Curve.Chart.locateSquarefreeCurveRoot
        p current chart data gcdDegreePositive parameter parameterInside
          curveDenominatorNonzero curveRoot curveInside
      let event : Curve.Event.Family.SourcePersistentBoundaryEventsEventEntryAlias (p := p) (box := current) (form :=
        atom.form)
          (chart := chart) (data := data)
          (gcdDegreePositive := gcdDegreePositive) :=
        ⟨Curve.Event.Located.LocatedSquarefreeCurveRoot.factorAnalysis
            located,
          Curve.Event.Located.LocatedSquarefreeCurveRoot.eventLeaf
            located⟩
      have eventMember : event ∈
          Curve.Event.Family.eventFamily factors := by
        exact Curve.Event.Located.LocatedSquarefreeCurveRoot.eventLeaf_mem_family_of_factors_eq
          factors_eq located
      let entry : Curve.Boundary.Event.Basic.BoundaryEventEntry boundary :=
        { chart := chart
          data := data
          gcdDegreePositive := gcdDegreePositive
          factors := factors
          factors_eq := factors_eq
          analysisMember := analysisMember
          event := event
          eventMember := eventMember }
      exact
        { entry := entry
          member := Curve.Boundary.Event.Family.mem_boundaryEventFamily_of_event boundary chart data
            gcdDegreePositive factors factors_eq analysisMember event eventMember
          parameter := parameter
          parameterInside := by
            exact located.location.contains
          factorZero := located.factorZero
          denominatorNonzero := curveDenominatorNonzero
          point_eq := pointEq }

end Purelib.RootIsolation.Curve.Boundary.Event.Coverage

end
