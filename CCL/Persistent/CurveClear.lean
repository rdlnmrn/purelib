import mathlib.Data.ConstructiveList
import CCL.Boundary.ChartNondegenerate
import CCL.Persistent.Dispatch

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

namespace CCL.PersistentCCLCurveClear

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box
abbrev State := CCL.PersistentCCL.State
abbrev WindingOneTrack := RFAP.ShrinkingTrack.WindingOneTrack
abbrev HermitianForm := CCL.CCLGeometry.HermitianForm
abbrev BoundedChart := CCL.CCLBoundaryCharts.BoundedChart
abbrev BoundedAnalysis := CCL.CCLBoundaryCharts.BoundedAnalysis

/-- Executable tag for the constant-gcd branch of one bounded chart. -/
def isClear
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    {chart : BoundedChart form} : BoundedAnalysis p box chart → Bool
  | .clear _certificate _residual => true
  | .identicallyZero _realZero _imaginaryZero => false
  | .events _data _degreePositive _factors _factorsEq => false

/-- Semantic result required from one analyzed chart after all clear-chart
refinements have run.  Event and identically-zero charts impose no claim at
this stage. -/
def ClearResolved
    {p : GaussianPolynomial} {ambient analysisBox : Box}
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
    {p : GaussianPolynomial} {ambient analysisBox : Box}
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

theorem refineClearAnalyses_refines
    {p : GaussianPolynomial} {ambient analysisBox : Box}
    {form : HermitianForm}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p analysisBox chart)) :
    (refineClearAnalyses track current analyses).numerical.box.Refines
      current.numerical.box := by
  induction analyses generalizing current with
  | nil => exact RFAP.Boxes.Box.refines_refl _
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

theorem refineClearAnalyses_word
    {p : GaussianPolynomial} {ambient analysisBox : Box}
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
            (CCL.PersistentCCL.State.refine_word
              current numerical
                (residual.refinePast_refines track current.numerical))

/-- Every constant-gcd entry occurring in the processed finite list is
excluded from the final box. -/
theorem refineClearAnalyses_resolves
    {p : GaussianPolynomial} {ambient analysisBox : Box}
    {form : HermitianForm}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p analysisBox chart))
    {entry : Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p analysisBox chart}
    (member : entry ∈ analyses) :
    ClearResolved (refineClearAnalyses track current analyses) entry := by
  induction analyses generalizing current with
  | nil => simp at member
  | cons head remaining inductionHypothesis =>
      rcases List.mem_cons.mp member with equal | tailMember
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

/-- Every member of the finite chart list is a constant-gcd clear analysis. -/
def AllClear
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p box chart)) : Prop :=
  ∀ entry, entry ∈ analyses → isClear entry.2 = true

/-- Executable finite classification of a chart list: either every entry is
constant-gcd clear, or the first identically-zero/event entry is retained. -/
inductive Classification
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm}
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p box chart)) where
  | all (proof : AllClear analyses)
  | unresolved
      (entry : Sigma fun chart : BoundedChart form =>
        BoundedAnalysis p box chart)
      (member : entry ∈ analyses)
      (notClear : isClear entry.2 = false)

def classify
    {p : GaussianPolynomial} {box : Box} {form : HermitianForm} :
    (analyses : List (Sigma fun chart : BoundedChart form =>
      BoundedAnalysis p box chart)) → Classification analyses
  | [] => .all (by intro entry member; simp at member)
  | ⟨chart, .identicallyZero realZero imaginaryZero⟩ :: _remaining =>
      .unresolved
        ⟨chart, .identicallyZero realZero imaginaryZero⟩
        List.mem_cons_self rfl
  | ⟨chart, .events data degreePositive factors factorsEq⟩ :: _remaining =>
      .unresolved ⟨chart, .events data degreePositive factors factorsEq⟩
        List.mem_cons_self rfl
  | ⟨chart, .clear certificate residual⟩ :: remaining => by
      match classify remaining with
      | .unresolved entry member notClear =>
          exact .unresolved entry
            (List.mem_cons_of_mem
              ⟨chart, .clear certificate residual⟩ member) notClear
      | .all proof =>
          exact .all (by
            intro entry member
            rcases List.mem_cons.mp member with equal | tailMember
            · subst entry
              rfl
            · exact proof entry tailMember)

/-- An analyzed entry in a dispatched curve boundary comes from the complete
finite chart family stored by that boundary. -/
theorem chart_mem_of_analysis_mem
    {p : GaussianPolynomial} {reference : CCL.GaussianProjective.Mat2}
    {current : Box} {denominatorMargin : RFAP.ConstructiveFraction.Rational}
    {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CCL.PersistentCCLDispatch.CurveBoundary p
      reference current denominatorMargin marginPositive atom)
    {entry : Sigma fun chart : BoundedChart atom.form =>
      BoundedAnalysis p current chart}
    (member : entry ∈ boundary.analyses) :
    entry.1 ∈ CCL.CCLBoundaryCharts.charts boundary.source current
      denominatorMargin marginPositive := by
  rw [boundary.analyses_eq] at member
  change entry ∈
    (CCL.CCLBoundaryCharts.charts boundary.source current
      denominatorMargin marginPositive).map (fun chart =>
        ⟨chart,
          CCL.CCLBoundaryCharts.analyzeChart p current chart⟩) at member
  rw [QuotientFreeList.mem_map] at member
  rcases member with ⟨chart, chartMember, equal⟩
  have chartEqual := congrArg Sigma.fst equal
  rw [← chartEqual]
  exact chartMember

/-- No member of an active positive-degree curve boundary can have both
cleared coordinates identically zero. -/
theorem identicallyZero_absurd
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {reference : CCL.GaussianProjective.Mat2}
    {current : Box} {denominatorMargin : RFAP.ConstructiveFraction.Rational}
    {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CCL.PersistentCCLDispatch.CurveBoundary p
      reference current denominatorMargin marginPositive atom)
    (chart : BoundedChart atom.form)
    (realZero :
      (CCL.CurveClear.realPolynomial p
        chart.parameterization.curve).isZero = true)
    (imaginaryZero :
      (CCL.CurveClear.imaginaryPolynomial p
        chart.parameterization.curve).isZero = true)
    (member :
      (⟨chart, CCL.CCLBoundaryCharts.BoundedAnalysis.identicallyZero
          realZero imaginaryZero⟩ :
        Sigma fun chart : BoundedChart atom.form =>
          BoundedAnalysis p current chart) ∈ boundary.analyses) : False := by
  let entry : Sigma fun chart : BoundedChart atom.form =>
      BoundedAnalysis p current chart :=
    ⟨chart, CCL.CCLBoundaryCharts.BoundedAnalysis.identicallyZero
      realZero imaginaryZero⟩
  have chartMember := chart_mem_of_analysis_mem boundary (entry := entry) member
  have nondegenerate :=
    CCL.CCLChartNondegenerate.nondegenerate_of_mem_charts
      boundary.source current denominatorMargin marginPositive chart chartMember
  exact CCL.CCLChartNondegenerate.not_identicallyZero
    degreePositive chart nondegenerate ⟨realZero, imaginaryZero⟩

/-- Boundary-aware classification: every chart is clear, or the retained
first unresolved entry is necessarily a genuine nonconstant curve event. -/
inductive BoundaryClassification
    {p : GaussianPolynomial} {reference : CCL.GaussianProjective.Mat2}
    {current : Box} {denominatorMargin : RFAP.ConstructiveFraction.Rational}
    {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CCL.PersistentCCLDispatch.CurveBoundary p
      reference current denominatorMargin marginPositive atom) where
  | all (proof : AllClear boundary.analyses)
  | events
      (chart : BoundedChart atom.form)
      (data : CCL.CurveEvents.Nontrivial p
        chart.parameterization.curve)
      (gcdDegreePositive : 0 <
        (CCL.CurveClear.gcdPolynomial p
          chart.parameterization.curve).natDegree)
      (factors : List
        (CCL.CCLBoundaryCharts.SquarefreeFactorAnalysis p current
          chart data gcdDegreePositive))
      (factors_eq : factors =
        CCL.CCLBoundaryCharts.analyzeSquarefreeFactors p current
          chart data gcdDegreePositive)
      (member :
        (⟨chart, CCL.CCLBoundaryCharts.BoundedAnalysis.events data
          gcdDegreePositive factors factors_eq⟩ :
          Sigma fun chart : BoundedChart atom.form =>
            BoundedAnalysis p current chart) ∈ boundary.analyses)

def classifyBoundary
    {p : GaussianPolynomial} (degreePositive : 0 < p.natDegree)
    {reference : CCL.GaussianProjective.Mat2}
    {current : Box} {denominatorMargin : RFAP.ConstructiveFraction.Rational}
    {marginPositive : 0 < denominatorMargin}
    {atom : CCL.CCLFormula.Atom}
    (boundary : CCL.PersistentCCLDispatch.CurveBoundary p
      reference current denominatorMargin marginPositive atom) :
    BoundaryClassification boundary := by
  match classify boundary.analyses with
  | .all proof => exact .all proof
  | .unresolved entry member notClear =>
      rcases entry with ⟨chart, analysis⟩
      cases analysis with
      | identicallyZero realZero imaginaryZero =>
          exact (identicallyZero_absurd degreePositive boundary chart
            realZero imaginaryZero member).elim
      | clear certificate residual =>
          simp only [isClear] at notClear
          exact Bool.noConfusion notClear
      | events data gcdDegreePositive factors factorsEq =>
          exact .events chart data gcdDegreePositive factors factorsEq member

/-- Output of eliminating a boundary whose complete bounded chart family is
globally clear. -/
structure Resolution
    {p : GaussianPolynomial} {ambient : Box}
    (current : State p ambient) (form : HermitianForm) where
  state : State p ambient
  boxRefines : state.numerical.box.Refines current.numerical.box
  word_eq : state.word = current.word
  formNonzero : ∀ value : Gaussian,
    state.numerical.box.Contains value → form.eval value ≠ 0

/-- Refine past all clear charts and use finite chart coverage to exclude the
entire Hermitian boundary from the resulting box. -/
def resolve
    {p : GaussianPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (track : WindingOneTrack p ambient)
    {current : State p ambient}
    (boundary : CCL.PersistentCCLDispatch.CurveBoundary p
      (CCL.CCLPullback.adjugate
        (CCL.RawParser.parse current.word).matrix)
      current.numerical.box
      (denominatorMargin : RFAP.ConstructiveFraction.Rational)
      (marginPositive : 0 < denominatorMargin)
      atom)
    (denominatorLower : ∀ {value : Gaussian},
      current.numerical.box.Contains value →
        denominatorMargin ≤ RFAP.ConstructiveGaussian.Gaussian.normSq
          (CCL.RawParser.denominator
            (CCL.CCLPullback.adjugate
              (CCL.RawParser.parse current.word).matrix)
            value))
    (allClear : AllClear boundary.analyses) :
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
          CCL.CCLBoundaryCharts.CurveSource.covers
            boundary.source current.numerical.box marginPositive value
              (finalRefines.contains inside) evaluatesZero
              (denominatorLower (finalRefines.contains inside))
        rcases covered with
          ⟨chart, chartMember, parameter, parameterInside,
            curveDenominatorNonzero, pointEq⟩
        let entry : Sigma fun chart : BoundedChart atom.form =>
            BoundedAnalysis p current.numerical.box chart :=
          ⟨chart,
            CCL.CCLBoundaryCharts.analyzeChart p
              current.numerical.box chart⟩
        have entryMember : entry ∈ boundary.analyses := by
          rw [boundary.analyses_eq]
          exact QuotientFreeList.mem_map.mpr ⟨chart, chartMember, rfl⟩
        have clearStatus := allClear entry entryMember
        have resolved := refineClearAnalyses_resolves degreePositive track
          current boundary.analyses entryMember
        dsimp only [entry] at clearStatus resolved
        generalize analysisEq :
            CCL.CCLBoundaryCharts.analyzeChart p
              current.numerical.box chart = analysis at clearStatus resolved
        cases analysis with
        | identicallyZero realZero imaginaryZero =>
            simp only [isClear] at clearStatus
            cases clearStatus
        | events data eventDegree factors factorsEq =>
            simp only [isClear] at clearStatus
            cases clearStatus
        | clear certificate residual =>
            exact (resolved parameter parameterInside
              curveDenominatorNonzero) (by simpa only [pointEq] using inside) }

end CCL.PersistentCCLCurveClear
