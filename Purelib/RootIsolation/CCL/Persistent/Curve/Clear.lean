module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Projective.Hermitian.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Basic
import Purelib.Geometry.Projective.Hermitian.Chart.Coverage
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.RootIsolation.CCL.Persistent.State.Basic
public import Purelib.RootIsolation.Curve.Boundary.Analysis
import Purelib.RootIsolation.Curve.Chart.Analysis
public import Purelib.RootIsolation.Curve.Chart.Classification
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.Track.Exclusion.Curve
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Proper
import Purelib.Geometry.Projective.Hermitian.Atom
import Purelib.Geometry.Projective.Hermitian.Parametrization.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.RationalFunctions.Curve.Basic
import Purelib.RationalFunctions.Curve.Substitution.GCD
import Purelib.RootIsolation.Curve.Clearance.Global
import Purelib.RootIsolation.Curve.Clearance.Residual
import Purelib.RootIsolation.Curve.Event.Analysis
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Geometry.Projective.Hermitian.Chart (BoundedChart)
open Purelib.Geometry.Projective.Hermitian (HermitianForm)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RootIsolation.CCL.Persistent (State)
open Purelib.RootIsolation.Curve.Chart (BoundedAnalysis)
open Purelib.RootIsolation.Track.Basic (WindingOneTrack)

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

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

namespace Purelib.RootIsolation.CCL.Persistent.Curve.Clear

/-- Semantic result required from one analyzed chart after all clear-chart
refinements have run.  Event and identically-zero charts impose no claim at
this stage. -/
def ClearResolved
    {p : CoefficientPolynomial} {ambient analysisBox : Box}
    {form : HermitianForm} (final : State p ambient)
    (entry : Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p analysisBox chart) : Prop :=
  match entry with
  | ⟨chart, .clear _certificate _residual⟩ =>
      ∀ parameter,
        chart.cell.interval.Contains parameter →
        chart.parameterization.curve.denominatorAt parameter ≠ 0 →
        ¬final.numerical.box.Contains
          (chart.parameterization.curve.point parameter)
  | ⟨_chart, .identicallyZero _realZero _imaginaryZero⟩ => True
  | ⟨_chart, .events _data _degreePositive _factors _factorsEq⟩ => True

/-- Refine past every constant-gcd chart in one explicit finite analysis
list.  The other two chart outcomes are left untouched for later dispatch. -/
def refineClearAnalyses
    {p : CoefficientPolynomial} {ambient analysisBox : Box}
    {form : HermitianForm}
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p analysisBox chart) → State p ambient
  | [] => current
  | ⟨_chart, .identicallyZero _realZero _imaginaryZero⟩ :: remaining =>
      refineClearAnalyses track current remaining
  | ⟨_chart, .events _data _degreePositive _factors _factorsEq⟩ :: remaining =>
      refineClearAnalyses track current remaining
  | ⟨_chart, .clear _certificate residual⟩ :: remaining =>
      let numerical := residual.refinePast track current.numerical
      let next := current.refine numerical
        (residual.refinePast_refines track current.numerical)
      refineClearAnalyses track next remaining

/-- Processing the retained clear-chart analyses refines the original numerical box. -/
theorem refineClearAnalyses_refines
    {p : CoefficientPolynomial} {ambient analysisBox : Box}
    {form : HermitianForm}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p analysisBox chart)) :
    (refineClearAnalyses track current analyses).numerical.box.Refines
      current.numerical.box := by
  induction analyses generalizing current with
  | nil => exact Box.refines_refl _
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨chart, analysis⟩
      cases analysis with
      | identicallyZero realZero imaginaryZero =>
          exact inductionHypothesis current
      | events data degreePositive factors factorsEq =>
          exact inductionHypothesis current
      | clear certificate residual =>
          let numerical := residual.refinePast track current.numerical
          let next := current.refine numerical
            (residual.refinePast_refines track current.numerical)
          exact (inductionHypothesis next).trans
            (residual.refinePast_refines track current.numerical)

/-- Processing the retained clear-chart analyses preserves the exact original raw word. -/
theorem refineClearAnalyses_word
    {p : CoefficientPolynomial} {ambient analysisBox : Box}
    {form : HermitianForm}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p analysisBox chart)) :
    (refineClearAnalyses track current analyses).word = current.word := by
  induction analyses generalizing current with
  | nil => rfl
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨chart, analysis⟩
      cases analysis with
      | identicallyZero realZero imaginaryZero =>
          exact inductionHypothesis current
      | events data degreePositive factors factorsEq =>
          exact inductionHypothesis current
      | clear certificate residual =>
          let numerical := residual.refinePast track current.numerical
          let next := current.refine numerical
            (residual.refinePast_refines track current.numerical)
          exact (inductionHypothesis next).trans
            (State.refine_word
              current numerical
                (residual.refinePast_refines track current.numerical))

/-- Every constant-gcd entry occurring in the processed finite list is
excluded from the final box. -/
theorem refineClearAnalyses_resolves
    {p : CoefficientPolynomial} {ambient analysisBox : Box}
    {form : HermitianForm}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p analysisBox chart))
    {entry : Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p analysisBox chart}
    (member : entry ∈ analyses) :
    ClearResolved (refineClearAnalyses track current analyses)
      entry := by
  induction analyses generalizing current with
  | nil => exact (List.not_mem_nil member).elim
  | cons head remaining inductionHypothesis =>
      rcases Data.List.Membership.mem_cons.mp member with equal | tailMember
      · subst entry
        rcases head with ⟨chart, analysis⟩
        cases analysis with
        | identicallyZero realZero imaginaryZero => trivial
        | events data eventDegree factors factorsEq => trivial
        | clear certificate residual =>
            intro parameter inside denominatorNonzero contained
            let numerical := residual.refinePast track current.numerical
            let next := current.refine numerical
              (residual.refinePast_refines track current.numerical)
            have finalRefinesNext :
                (refineClearAnalyses track next remaining).numerical.box.Refines
                  next.numerical.box :=
              refineClearAnalyses_refines track next remaining
            exact residual.refinePast_excludes degreePositive track
              current.numerical parameter inside denominatorNonzero
                (finalRefinesNext.contains contained)
      · rcases head with ⟨chart, analysis⟩
        cases analysis with
        | identicallyZero realZero imaginaryZero =>
            exact inductionHypothesis current tailMember
        | events data eventDegree factors factorsEq =>
            exact inductionHypothesis current tailMember
        | clear certificate residual =>
            let numerical := residual.refinePast track current.numerical
            let next := current.refine numerical
              (residual.refinePast_refines track current.numerical)
            exact inductionHypothesis next tailMember

set_option genInjectivity false in
/-- Output of eliminating a boundary whose complete bounded chart family is
globally clear. -/
structure Resolution
    {p : CoefficientPolynomial} {ambient : Box}
    (current : State p ambient) (form : HermitianForm) where
  /-- The actual retained persistent state after all original clear-chart refinements. -/ state :
    State p ambient
  /-- The final numerical box refines the original current box. -/ boxRefines : state.numerical.box.Refines
    current.numerical.box
  /-- The final state retains the original raw word exactly. -/ word_eq : state.word = current.word
  /-- The original Hermitian boundary form is nonzero throughout the retained final box. -/ formNonzero : ∀ value :
    Gaussian.Basic.Canonical,
    state.numerical.box.Contains value → form.eval value ≠ 0

constructive_injectivity Resolution

/-- Refine past all clear charts and use finite chart coverage to exclude the
entire Hermitian boundary from the resulting box. -/
def resolve
    {p : CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient)
    {current : State p ambient}
    (boundary : Curve.Boundary.Analysis.CurveBoundary p
      (LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.adjugate
        (Data.CCL.Encoding.Parser.State.parse current.word).matrix)
      current.numerical.box
      (denominatorMargin : Fraction.Rational)
      (marginPositive : 0 < denominatorMargin)
      atom)
    (denominatorLower : ∀ {value : Gaussian.Basic.Canonical},
      current.numerical.box.Contains value →
        denominatorMargin ≤ Data.Gaussian.Norm.Basic.normSq
          (Geometry.Projective.Homography.Basic.denominator
            (LinearAlgebra.Coordinates2.Matrix.BoundaryAdjugate.adjugate
              (Data.CCL.Encoding.Parser.State.parse current.word).matrix)
            value))
    (allClear : Curve.Chart.Classification.AllClear boundary.analyses) :
    Resolution current atom.form := by
  let final := refineClearAnalyses track current boundary.analyses
  have finalRefines : final.numerical.box.Refines current.numerical.box :=
    refineClearAnalyses_refines track current boundary.analyses
  exact
    { state := final
      boxRefines := finalRefines
      word_eq := refineClearAnalyses_word track current boundary.analyses
      formNonzero := by
        intro value inside evaluatesZero
        have covered :=
          Geometry.Projective.Hermitian.Chart.CurveSource.covers
            boundary.source current.numerical.box marginPositive value
              (finalRefines.contains inside) evaluatesZero
              (denominatorLower (finalRefines.contains inside))
        rcases covered with
          ⟨chart, chartMember, parameter, parameterInside,
            curveDenominatorNonzero, pointEq⟩
        let entry : Sigma fun chart : BoundedChart atom.form =>
            BoundedAnalysis p current.numerical.box chart :=
          ⟨chart,
            Curve.Chart.analyzeChart p
              current.numerical.box chart⟩
        have entryMember : entry ∈ boundary.analyses := by
          rw [boundary.analyses_eq]
          exact Data.List.Map.mem_map.mpr ⟨chart, chartMember, rfl⟩
        have clearStatus := allClear entry entryMember
        have resolved := refineClearAnalyses_resolves degreePositive track
          current boundary.analyses entryMember
        dsimp only [entry] at clearStatus resolved
        generalize analysisEq :
            Curve.Chart.analyzeChart p
              current.numerical.box chart = analysis at clearStatus resolved
        cases analysis with
        | identicallyZero realZero imaginaryZero =>
            simp only [Curve.Chart.Classification.isClear] at clearStatus
            cases clearStatus
        | events data eventDegree factors factorsEq =>
            simp only [Curve.Chart.Classification.isClear] at clearStatus
            cases clearStatus
        | clear certificate residual =>
            exact (resolved parameter parameterInside
              curveDenominatorNonzero) (by simpa only [pointEq] using inside) }

end Purelib.RootIsolation.CCL.Persistent.Curve.Clear

end
