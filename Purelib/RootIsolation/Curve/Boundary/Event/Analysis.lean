module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Coverage
import Purelib.Geometry.Projective.Hermitian.Chart.Nondegenerate
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
public import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Chart.Analysis
public import Purelib.RootIsolation.Curve.Chart.Classification
import Purelib.RootIsolation.Curve.Chart.Nondegenerate
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
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
open Purelib.RootIsolation.Curve.Chart (BoundedAnalysis)

open Purelib.Data.Rat

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RationalFunctions

open Purelib.RootIsolation

section
public section

/-!
# Finite elimination of globally clear CCL boundary charts

The curve dispatcher returns a finite list of bounded rational charts.  A
constant-gcd chart now carries an original-polynomial residual lower bound.
This module folds the winding-one refinement from that bound over every clear
chart while preserving the current raw prefix.

If every chart in the returned boundary analysis is globally clear, finite
chart coverage then proves that the Hermitian boundary has no displayed point
in the final box.  Nonconstant curve-event charts are deliberately retained
for the subsequent owner calculation.  A radius-zero norm boundary is
classified upstream as a finite singleton; on every remaining line or circle
chart, a finite non-pole/root-count argument eliminates the identically-zero
outcome.
-/

namespace Purelib.RootIsolation.Curve.Boundary.Event.Analysis

/-- An analyzed entry in a dispatched curve boundary comes from the complete
finite chart family stored by that boundary. -/
theorem chart_mem_of_analysis_mem
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix}
    {current : Box} {denominatorMargin : Fraction.Rational}
    {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p
      reference current denominatorMargin marginPositive atom)
    {entry : Sigma fun chart : BoundedChart atom.form =>
      BoundedAnalysis p current chart}
    (member : entry ∈ boundary.analyses) :
    entry.1 ∈ Geometry.Projective.Hermitian.Chart.charts boundary.source current
      denominatorMargin marginPositive := by
  rw [boundary.analyses_eq] at member
  change entry ∈
    (Geometry.Projective.Hermitian.Chart.charts boundary.source current
      denominatorMargin marginPositive).map (fun chart =>
        ⟨chart,
          Curve.Chart.analyzeChart p current chart⟩) at member
  have member := Data.List.Map.mem_map.mp member
  rcases member with ⟨chart, chartMember, equal⟩
  have chartEqual := congrArg Sigma.fst equal
  rw [← chartEqual]
  exact chartMember

/-- No member of an active positive-degree curve boundary can have both
cleared coordinates identically zero. -/
theorem identicallyZero_absurd
    {p : CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {reference : GaussianMatrix}
    {current : Box} {denominatorMargin : Fraction.Rational}
    {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p
      reference current denominatorMargin marginPositive atom)
    (chart : BoundedChart atom.form)
    (realZero :
      (Curve.Substitution.realPolynomial p
        chart.parameterization.curve).isZero = true)
    (imaginaryZero :
      (Curve.Substitution.imaginaryPolynomial p
        chart.parameterization.curve).isZero = true)
    (member :
      (⟨chart, BoundedAnalysis.identicallyZero
          realZero imaginaryZero⟩ :
        Sigma fun chart : BoundedChart atom.form =>
          BoundedAnalysis p current chart) ∈ boundary.analyses) : False := by
  let entry : Sigma fun chart : BoundedChart atom.form =>
      BoundedAnalysis p current chart :=
    ⟨chart, BoundedAnalysis.identicallyZero
      realZero imaginaryZero⟩
  have chartMember := chart_mem_of_analysis_mem boundary (entry := entry) member
  have nondegenerate :=
    Geometry.Projective.Hermitian.Chart.nondegenerate_of_mem_charts
      boundary.source current denominatorMargin marginPositive chart chartMember
  exact Curve.Chart.not_identicallyZero
    degreePositive chart nondegenerate ⟨realZero, imaginaryZero⟩

set_option genInjectivity false in
/-- Boundary-aware classification: every chart is clear, or the retained
first unresolved entry is necessarily a genuine nonconstant curve event. -/
inductive BoundaryClassification
    {p : CoefficientPolynomial} {reference :
      GaussianMatrix}
    {current : Box} {denominatorMargin : Fraction.Rational}
    {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p
      reference current denominatorMargin marginPositive atom) where
  /-- Every original bounded chart entry has a retained clearance analysis. -/ | all (proof :
    Curve.Chart.Classification.AllClear boundary.analyses)
  /-- The original first unresolved chart retains its nonconstant event data, actual factor analyses and membership in
    the boundary's list. -/ | events
      (chart : BoundedChart atom.form)
      (data : Curve.Event.Nontrivial p
        chart.parameterization.curve)
      (gcdDegreePositive : 0 <
        (Curve.Substitution.gcdPolynomial p
          chart.parameterization.curve).natDegree)
      (factors : List
        (Curve.Chart.SquarefreeFactorAnalysis p current
          chart data gcdDegreePositive))
      (factors_eq : factors =
        Curve.Chart.analyzeSquarefreeFactors p current
          chart data gcdDegreePositive)
      (member :
        (⟨chart, BoundedAnalysis.events data
          gcdDegreePositive factors factors_eq⟩ :
          Sigma fun chart : BoundedChart atom.form =>
            BoundedAnalysis p current chart) ∈ boundary.analyses)

constructive_injectivity BoundaryClassification

/-- Classify the retained bounded boundary charts as all clear or retain their first genuine curve event.

Positive polynomial degree excludes the identically-zero chart case using the original finite chart coverage and
nondegeneracy certificates. -/
@[expose] def classifyBoundary
    {p : CoefficientPolynomial} (degreePositive : 0 < p.natDegree)
    {reference : GaussianMatrix}
    {current : Box} {denominatorMargin : Fraction.Rational}
    {marginPositive : 0 < denominatorMargin}
    {atom : Atom}
    (boundary : CurveBoundary p
      reference current denominatorMargin marginPositive atom) :
    BoundaryClassification boundary := by
  match Curve.Chart.Classification.classify boundary.analyses with
  | .all proof => exact .all proof
  | .unresolved entry member notClear =>
      rcases entry with ⟨chart, analysis⟩
      cases analysis with
      | identicallyZero realZero imaginaryZero =>
          exact (identicallyZero_absurd degreePositive boundary chart
            realZero imaginaryZero member).elim
      | clear certificate residual =>
          simp only [-eq_self, -iff_self, Curve.Chart.Classification.isClear] at notClear
          exact Bool.noConfusion notClear
      | events data gcdDegreePositive factors factorsEq =>
          exact .events chart data gcdDegreePositive factors factorsEq member
end Purelib.RootIsolation.Curve.Boundary.Event.Analysis

end
