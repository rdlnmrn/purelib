import FTA.CCLEventTangentSigns
import FTA.CCLCompleteOwnerCompatibility

/-!
# Complete-child tangent signs for a selected positive event

The incremental tangent classifier deliberately omits historical parser
constraints because the existing grid transports them from a represented
sample.  This module classifies the larger finite list of active faces in the
complete selected child formula.  It is the algebraic interface needed by a
direct event-point sampler whose accuracy is fixed before any rational point
is selected.
-/

namespace FTA
namespace CCLCompleteEventTangentSigns

open CCL CCL.GaussianRat
open FTA.CCLBranchController
open FTA.CCLBoundaryPath
open FTA.CCLBranchCharts
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLCountOneClassification
open FTA.CCLCompleteOwnerCompatibility
open FTA.CCLCompleteOwnerShapes
open FTA.CCLEventTangentSigns
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLIntersectionSharedFactors
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLPathIntersection
open FTA.CCLPathTangent
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventApproximation
open FTA.CCLSectorTangent
open FTA.ComputablePolynomial
open FTA.ProjectivePath
open FTA.RationalPolynomialBounds
open FTA.RootCountDivisibility
open FTA.RootTrackSeparation
open FTA.SturmTransducer

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI
abbrev RatPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial ℚ

/-- Complete-payload path projection kept syntactically independent of the
history-free payload adapter. -/
abbrev selectedCompletePath
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ProjectivePath.Path :=
  selected.candidate.sourceEvent.partition.entry.chart.path

/-- Four nonpositive canonical direction products cannot coexist when their
angle-gap identity is congruent, modulo the event factor, to a polynomial
that is uniformly positive on the isolated event cell.  Canonically zero
slopes are handled by divisibility; strictly negative pairs retain their
sign throughout the common cell. -/
theorem ConditionRelations.not_four_direction_products_nonpositive
    {event : RatPolynomial} {input : SquarefreeInput event}
    {conditions : List RatPolynomial}
    (relations : ConditionRelations event conditions)
    (parent : CountOneInterval event)
    (result : FTA.CCLIntersectionEventSigns.CommonEventSigns input
      relations.coprimeConditions parent)
    {base a b c d e f g h : RatPolynomial}
    (aMember : a ∈ conditions) (bMember : b ∈ conditions)
    (cMember : c ∈ conditions) (dMember : d ∈ conditions)
    (eMember : e ∈ conditions) (fMember : f ∈ conditions)
    (gMember : g ∈ conditions) (hMember : h ∈ conditions)
    (axisScale diagonalScale : ℚ) (axisScalePositive : 0 < axisScale)
    (diagonalScalePositive : 0 < diagonalScale)
    (basePositive : ∀ t : ℚ,
      result.refined.interval.lower ≤ t →
      t ≤ result.refined.interval.upper → 0 < base.eval t)
    (baseLower : FTA.PositiveLowerBound.Certificate base
      result.refined.interval)
    (divides : event.toPolynomial ∣
      (base + (DensePolynomial.scale axisScale ((a * b) * (c * d)) +
        DensePolynomial.scale diagonalScale ((e * f) * (g * h)))).toPolynomial)
    (abNonpositive :
      canonicalEventValue input a result.refined.interval.lower *
        canonicalEventValue input b result.refined.interval.lower ≤ 0)
    (cdNonpositive :
      canonicalEventValue input c result.refined.interval.lower *
        canonicalEventValue input d result.refined.interval.lower ≤ 0)
    (efNonpositive :
      canonicalEventValue input e result.refined.interval.lower *
        canonicalEventValue input f result.refined.interval.lower ≤ 0)
    (ghNonpositive :
      canonicalEventValue input g result.refined.interval.lower *
        canonicalEventValue input h result.refined.interval.lower ≤ 0) :
    False := by
  have classifyProduct {q r : RatPolynomial}
      (qMember : q ∈ conditions) (rMember : r ∈ conditions)
      (nonpositive :
        canonicalEventValue input q result.refined.interval.lower *
          canonicalEventValue input r result.refined.interval.lower ≤ 0) :
      event.toPolynomial ∣ (q * r).toPolynomial ∨
        ∀ t : ℚ, result.refined.interval.lower ≤ t →
          t ≤ result.refined.interval.upper → (q * r).eval t < 0 := by
    rcases lt_or_eq_of_le nonpositive with negative | zero
    · right
      intro t lower upper
      have qNonzero : canonicalEventValue input q
          result.refined.interval.lower ≠ 0 := by
        intro qZero
        simp [qZero] at negative
      have rNonzero : canonicalEventValue input r
          result.refined.interval.lower ≠ 0 := by
        intro rZero
        simp [rZero] at negative
      have qSign :=
        FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
          relations parent result qMember qNonzero lower upper
      have rSign :=
        FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_mul_eval_pos
          relations parent result rMember rNonzero lower upper
      simp only [DensePolynomial.eval_mul]
      nlinarith [mul_pos qSign rSign]
    · left
      rcases mul_eq_zero.mp zero with qZero | rZero
      · have qDivides :=
          FTA.CCLBranchEventOwner.ConditionRelations.dvd_of_canonicalEventValue_eq_zero
            relations parent result qMember qZero
        simpa only [DensePolynomial.toPolynomial_mul] using
          dvd_mul_of_dvd_left qDivides r.toPolynomial
      · have rDivides :=
          FTA.CCLBranchEventOwner.ConditionRelations.dvd_of_canonicalEventValue_eq_zero
            relations parent result rMember rZero
        simpa only [DensePolynomial.toPolynomial_mul] using
          dvd_mul_of_dvd_right rDivides q.toPolynomial
  have combineProducts {q r s t : RatPolynomial}
      (first : event.toPolynomial ∣ (q * r).toPolynomial ∨
        ∀ x : ℚ, result.refined.interval.lower ≤ x →
          x ≤ result.refined.interval.upper → (q * r).eval x < 0)
      (second : event.toPolynomial ∣ (s * t).toPolynomial ∨
        ∀ x : ℚ, result.refined.interval.lower ≤ x →
          x ≤ result.refined.interval.upper → (s * t).eval x < 0) :
      event.toPolynomial ∣ ((q * r) * (s * t)).toPolynomial ∨
        ∀ x : ℚ, result.refined.interval.lower ≤ x →
          x ≤ result.refined.interval.upper →
            0 ≤ ((q * r) * (s * t)).eval x := by
    rcases first with firstDivides | firstNegative
    · left
      simpa only [DensePolynomial.toPolynomial_mul] using
        dvd_mul_of_dvd_left firstDivides (s * t).toPolynomial
    · rcases second with secondDivides | secondNegative
      · left
        simpa only [DensePolynomial.toPolynomial_mul] using
          dvd_mul_of_dvd_right secondDivides (q * r).toPolynomial
      · right
        intro x lower upper
        have firstNegative' := firstNegative x lower upper
        have secondNegative' := secondNegative x lower upper
        simp only [DensePolynomial.eval_mul] at firstNegative' secondNegative' ⊢
        exact mul_nonneg_of_nonpos_of_nonpos
          firstNegative'.le secondNegative'.le
  have axisOutcome := combineProducts
    (classifyProduct aMember bMember abNonpositive)
    (classifyProduct cMember dMember cdNonpositive)
  have diagonalOutcome := combineProducts
    (classifyProduct eMember fMember efNonpositive)
    (classifyProduct gMember hMember ghNonpositive)
  let axisTerm := (a * b) * (c * d)
  let diagonalTerm := (e * f) * (g * h)
  change event.toPolynomial ∣ axisTerm.toPolynomial ∨
      (∀ x : ℚ, result.refined.interval.lower ≤ x →
        x ≤ result.refined.interval.upper → 0 ≤ axisTerm.eval x) at axisOutcome
  change event.toPolynomial ∣ diagonalTerm.toPolynomial ∨
      (∀ x : ℚ, result.refined.interval.lower ≤ x →
        x ≤ result.refined.interval.upper →
          0 ≤ diagonalTerm.eval x) at diagonalOutcome
  change event.toPolynomial ∣
    (base + (DensePolynomial.scale axisScale axisTerm +
      DensePolynomial.scale diagonalScale diagonalTerm)).toPolynomial at divides
  have removeDiagonal :
      (base + (DensePolynomial.scale axisScale axisTerm +
          DensePolynomial.scale diagonalScale diagonalTerm)).toPolynomial -
        (DensePolynomial.scale diagonalScale diagonalTerm).toPolynomial =
      (base + DensePolynomial.scale axisScale axisTerm).toPolynomial := by
    simp only [DensePolynomial.toPolynomial_add,
      DensePolynomial.toPolynomial_scale]
    ring
  have extendBase (extra : RatPolynomial)
      (extraNonnegative : ∀ x : ℚ,
        result.refined.interval.lower ≤ x →
        x ≤ result.refined.interval.upper → 0 ≤ extra.eval x) :
      FTA.PositiveLowerBound.Certificate (base + extra)
        result.refined.interval :=
    { bound := baseLower.bound
      positive := baseLower.positive
      lower := by
        intro x lower upper
        have baseBound := baseLower.lower x lower upper
        have basePos := basePositive x lower upper
        have extraNonneg := extraNonnegative x lower upper
        simp only [DensePolynomial.eval_add]
        nlinarith [sq_nonneg (extra.eval x)] }
  rcases axisOutcome with axisDivides | axisNonnegative
  · have axisScaledDivides : event.toPolynomial ∣
        (DensePolynomial.scale axisScale axisTerm).toPolynomial := by
      simp only [axisTerm, DensePolynomial.toPolynomial_scale]
      exact dvd_mul_of_dvd_right axisDivides _
    rcases diagonalOutcome with diagonalDivides | diagonalNonnegative
    · have diagonalScaledDivides : event.toPolynomial ∣
          (DensePolynomial.scale diagonalScale diagonalTerm).toPolynomial := by
        simp only [diagonalTerm, DensePolynomial.toPolynomial_scale]
        exact dvd_mul_of_dvd_right diagonalDivides _
      have withoutDiagonal := dvd_sub divides diagonalScaledDivides
      have baseAndAxis : event.toPolynomial ∣
          (base + DensePolynomial.scale axisScale axisTerm).toPolynomial := by
        rw [removeDiagonal] at withoutDiagonal
        exact withoutDiagonal
      have withoutAxis := dvd_sub baseAndAxis axisScaledDivides
      have baseDivides : event.toPolynomial ∣ base.toPolynomial := by
        simpa only [DensePolynomial.toPolynomial_add,
          DensePolynomial.toPolynomial_scale, add_sub_cancel_right] using
            withoutAxis
      exact CountOneInterval.no_positiveLowerBound_of_dvd input result.refined
        baseDivides baseLower
    · have diagonalNonnegative' : ∀ x : ℚ,
          result.refined.interval.lower ≤ x →
          x ≤ result.refined.interval.upper →
          0 ≤ (DensePolynomial.scale diagonalScale diagonalTerm).eval x := by
        intro x lower upper
        simp only [diagonalTerm, DensePolynomial.eval_scale]
        exact mul_nonneg diagonalScalePositive.le
          (diagonalNonnegative x lower upper)
      have withoutAxis := dvd_sub divides axisScaledDivides
      have rearranged :
          (base + (DensePolynomial.scale axisScale axisTerm +
              DensePolynomial.scale diagonalScale diagonalTerm)).toPolynomial -
            (DensePolynomial.scale axisScale axisTerm).toPolynomial =
          (base + DensePolynomial.scale diagonalScale diagonalTerm).toPolynomial := by
        simp only [DensePolynomial.toPolynomial_add,
          DensePolynomial.toPolynomial_scale]
        ring
      have remaining : event.toPolynomial ∣
          (base + DensePolynomial.scale diagonalScale diagonalTerm).toPolynomial := by
        rw [rearranged] at withoutAxis
        exact withoutAxis
      exact CountOneInterval.no_positiveLowerBound_of_dvd input result.refined
        remaining (extendBase _ diagonalNonnegative')
  · have axisNonnegative' : ∀ x : ℚ,
        result.refined.interval.lower ≤ x →
        x ≤ result.refined.interval.upper →
        0 ≤ (DensePolynomial.scale axisScale axisTerm).eval x := by
      intro x lower upper
      simp only [axisTerm, DensePolynomial.eval_scale]
      exact mul_nonneg axisScalePositive.le (axisNonnegative x lower upper)
    rcases diagonalOutcome with diagonalDivides | diagonalNonnegative
    · have diagonalScaledDivides : event.toPolynomial ∣
          (DensePolynomial.scale diagonalScale diagonalTerm).toPolynomial := by
        simp only [diagonalTerm, DensePolynomial.toPolynomial_scale]
        exact dvd_mul_of_dvd_right diagonalDivides _
      have remaining := dvd_sub divides diagonalScaledDivides
      have remaining' : event.toPolynomial ∣
          (base + DensePolynomial.scale axisScale axisTerm).toPolynomial := by
        rw [removeDiagonal] at remaining
        exact remaining
      exact CountOneInterval.no_positiveLowerBound_of_dvd input result.refined
        remaining' (extendBase _ axisNonnegative')
    · have diagonalNonnegative' : ∀ x : ℚ,
          result.refined.interval.lower ≤ x →
          x ≤ result.refined.interval.upper →
          0 ≤ (DensePolynomial.scale diagonalScale diagonalTerm).eval x := by
        intro x lower upper
        simp only [diagonalTerm, DensePolynomial.eval_scale]
        exact mul_nonneg diagonalScalePositive.le
          (diagonalNonnegative x lower upper)
      have extrasNonnegative : ∀ x : ℚ,
          result.refined.interval.lower ≤ x →
          x ≤ result.refined.interval.upper →
          0 ≤ (DensePolynomial.scale axisScale axisTerm +
            DensePolynomial.scale diagonalScale diagonalTerm).eval x := by
        intro x lower upper
        simp only [DensePolynomial.eval_add]
        exact add_nonneg (axisNonnegative' x lower upper)
          (diagonalNonnegative' x lower upper)
      apply CountOneInterval.no_positiveLowerBound_of_dvd input result.refined
        divides
      exact extendBase
        (DensePolynomial.scale axisScale axisTerm +
          DensePolynomial.scale diagonalScale diagonalTerm)
        extrasNonnegative

/-- Cleared slopes for every active face of the complete selected child,
grouped by the fixed eight-direction table. -/
def selectedCompleteSlopeConditions
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : List RatPolynomial :=
  coordinateDirections.flatMap fun direction =>
    (eventPayloadActiveOwnerForms selected).map fun form =>
      clearedDirectionalSlope form (selectedCompletePath selected) direction

theorem clearedDirectionalSlope_mem_selectedCompleteSlopeConditions
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {direction : QI}
    (directionMember : direction ∈ coordinateDirections)
    {form : HermitianForm}
    (formMember : form ∈ eventPayloadActiveOwnerForms selected) :
    clearedDirectionalSlope form (selectedCompletePath selected) direction ∈
      selectedCompleteSlopeConditions selected := by
  rw [selectedCompleteSlopeConditions, List.mem_flatMap]
  exact ⟨direction, directionMember,
    List.mem_map.mpr ⟨form, formMember, rfl⟩⟩

/-- Unique count-one descendant after classifying all complete-child slope
polynomials simultaneously. -/
def selectedCompleteSlopeClassification
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :=
  followCountOneConditions selected.candidate.inputCell.branch.factor
    (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined
    (selectedCompleteSlopeConditions selected)

def selectedCompleteSlopeSigns
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :=
  (selectedCompleteSlopeClassification selected).branch.computeEventSigns
    (selectedCompleteSlopeClassification selected).parent

theorem selectedCompleteSlopeSigns_refines_inputCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    (selectedCompleteSlopeSigns selected).refined.interval.Refines
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined.interval :=
  (selectedCompleteSlopeClassification selected).signRefines

/-- A chart obtained by applying an inverse source matrix has a uniformly
positive cleared forward denominator.  Homogeneous adjugate cancellation
reduces it to the source determinant norm times a standard circle/line
denominator, whose norm is at least one. -/
theorem sourceChart_clearedLowerRow_eval_ge
    (source : CCLBranchPlan.BoundarySource)
    (chart : BoundedChart source) (parameter : ℚ) :
    normSq (determinant source.matrix) ≤
      (clearedForm (affineNormForm source.matrix.c source.matrix.d)
        chart.path).eval parameter := by
  cases source with
  | norm matrix scaleValue =>
      have pathMember := chart.pathMember
      simp [CCLBranchPlan.BoundarySource.paths] at pathMember
      rcases pathMember with pathPrimary | pathReciprocal
      · rw [pathPrimary]
        change normSq (determinant matrix) ≤
          (clearedForm (affineNormForm matrix.c matrix.d)
            (actPath (adjugate matrix)
              (scaledCirclePath scaleValue))).eval parameter
        rw [eval_clearedForm_lowerRow_actPath_adjugate,
          eval_denominatorNorm]
        change normSq (determinant matrix) ≤
          normSq (determinant matrix) *
            normSq (unitCirclePath.denominator.eval
              (PathPolynomial.ofRat parameter))
        rw [unitCirclePath_denominator]
        change normSq (determinant matrix) ≤
          normSq (determinant matrix) * ((1 + parameter ^ 2) ^ 2 + 0 ^ 2)
        calc
          normSq (determinant matrix) = normSq (determinant matrix) * 1 := by ring
          _ ≤ normSq (determinant matrix) *
              ((1 + parameter ^ 2) ^ 2 + 0 ^ 2) := by
            apply mul_le_mul_of_nonneg_left _
              (normSq_nonneg (determinant matrix))
            nlinarith [sq_nonneg parameter]
      · rw [pathReciprocal]
        change normSq (determinant matrix) ≤
          (clearedForm (affineNormForm matrix.c matrix.d)
            (actPath (adjugate matrix)
              (reciprocalScaledCirclePath scaleValue))).eval parameter
        rw [eval_clearedForm_lowerRow_actPath_adjugate,
          eval_denominatorNorm]
        change normSq (determinant matrix) ≤
          normSq (determinant matrix) *
            normSq (reciprocalUnitCirclePath.denominator.eval
              (PathPolynomial.ofRat parameter))
        rw [reciprocalUnitCirclePath_denominator]
        change normSq (determinant matrix) ≤
          normSq (determinant matrix) * ((1 + parameter ^ 2) ^ 2 + 0 ^ 2)
        calc
          normSq (determinant matrix) = normSq (determinant matrix) * 1 := by ring
          _ ≤ normSq (determinant matrix) *
              ((1 + parameter ^ 2) ^ 2 + 0 ^ 2) := by
            apply mul_le_mul_of_nonneg_left _
              (normSq_nonneg (determinant matrix))
            nlinarith [sq_nonneg parameter]
  | real matrix threshold =>
      have pathMember := chart.pathMember
      simp only [CCLBranchPlan.BoundarySource.paths, List.mem_singleton] at pathMember
      rw [pathMember]
      change normSq (determinant matrix) ≤
        (clearedForm (affineNormForm matrix.c matrix.d)
          (actPath (adjugate matrix)
            (linePath ⟨threshold, 0⟩ ⟨0, 1⟩))).eval parameter
      rw [eval_clearedForm_lowerRow_actPath_adjugate,
        eval_denominatorNorm, linePath_denominator]
      simp [normSq]
  | imag matrix threshold =>
      have pathMember := chart.pathMember
      simp only [CCLBranchPlan.BoundarySource.paths, List.mem_singleton] at pathMember
      rw [pathMember]
      change normSq (determinant matrix) ≤
        (clearedForm (affineNormForm matrix.c matrix.d)
          (actPath (adjugate matrix)
            (linePath ⟨0, threshold⟩ ⟨1, 0⟩))).eval parameter
      rw [eval_clearedForm_lowerRow_actPath_adjugate,
        eval_denominatorNorm, linePath_denominator]
      simp [normSq]

/-- The selected source chart therefore supplies a positive lower bound for
the inverse-decoder denominator appearing in every pulled-back completed
block formula. -/
def selectedCompleteDecoderDenominatorPositiveLowerBound
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (stateDeterminant : determinant state.matrix ≠ 0) :
    FTA.PositiveLowerBound.Certificate
      (clearedForm
        (affineNormForm (adjugate state.matrix).c (adjugate state.matrix).d)
        (selectedCompletePath selected))
      (selectedCompleteSlopeSigns selected).refined.interval := by
  let source := selected.candidate.sourceEvent.partition.entry.source
  have sourceDeterminantPositive : 0 < normSq (determinant source.matrix) :=
    normSq_pos (CCLBranchPlan.inputPlan_determinant_ne state
      selected.sourceMember stateDeterminant)
  exact
    { bound := normSq (determinant source.matrix) ^ 2
      positive := sq_pos_of_pos sourceDeterminantPositive
      lower := by
        intro parameter _lower _upper
        have sourceMember := selected.sourceMember
        have lowerRow := CCLBranchPlan.inputPlan_lowerRow state sourceMember
        have sourceLower := sourceChart_clearedLowerRow_eval_ge source
          selected.candidate.sourceEvent.partition.entry.chart parameter
        rw [lowerRow.1, lowerRow.2] at sourceLower
        have squaredLower := mul_self_le_mul_self
          sourceDeterminantPositive.le sourceLower
        simpa only [source, selectedPath, pow_two] using squaredLower }

/-- The denominator certificate already carried by the selected event yields
a positive squared-value lower bound on the final complete-slope interval. -/
def selectedCompleteDenominatorPositiveLowerBound
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    FTA.PositiveLowerBound.Certificate
      (denominatorNorm (selectedCompletePath selected))
      (selectedCompleteSlopeSigns selected).refined.interval := by
  let denominator := RelevantCurveEvent.ownerDenominatorCertificate
    selected.candidate.sourceEvent.event
  exact
    { bound := denominator.bound ^ 2
      positive := sq_pos_of_pos denominator.positive
      lower := by
        intro t lower upper
        have rootLower := selected.candidate.inputCell.signRefines.1.trans
          ((selectedCompleteSlopeSigns_refines_inputCell selected).1.trans lower)
        have rootUpper :=
          (upper.trans
              (selectedCompleteSlopeSigns_refines_inputCell selected).2).trans
            selected.candidate.inputCell.signRefines.2
        have denominatorLower : denominator.bound ≤
            (denominatorNorm (selectedCompletePath selected)).eval t :=
          denominator.lower rootLower rootUpper
        simpa only [pow_two] using
          mul_self_le_mul_self denominator.positive.le denominatorLower }

/-- Multiplying the denominator certificate four times and rescaling by a
strictly positive invariant angle gap gives the positive obstruction used by
the finite compass search. -/
def selectedCompleteAngleGapPositiveLowerBound
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (left right : HermitianForm)
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    FTA.PositiveLowerBound.Certificate
      (DensePolynomial.scale
        (boundaryDiscriminant left * boundaryDiscriminant right -
          2 * gradientPairingConstant left right ^ 2)
        ((denominatorNorm (selectedCompletePath selected) *
            denominatorNorm (selectedCompletePath selected)) *
          (denominatorNorm (selectedCompletePath selected) *
            denominatorNorm (selectedCompletePath selected))))
      (selectedCompleteSlopeSigns selected).refined.interval := by
  let denominatorCertificate :=
    selectedCompleteDenominatorPositiveLowerBound selected
  let denominatorSquared := FTA.PositiveLowerBound.Certificate.mul
    denominatorCertificate denominatorCertificate
  let denominatorFourth := FTA.PositiveLowerBound.Certificate.mul
    denominatorSquared denominatorSquared
  exact FTA.PositiveLowerBound.Certificate.ofScalarProduct
    (boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2)
    angleGapPositive.ne' denominatorFourth (by
      intro t
      simp only [DensePolynomial.eval_scale, DensePolynomial.eval_mul])

/-- Canonical value of one complete-child slope on the common classified
count-one descendant. -/
def selectedCompleteSlopeValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (form : HermitianForm) (direction : QI) : ℚ :=
  canonicalEventValue
    (selectedCompleteSlopeClassification selected).branch.factor.input
    (clearedDirectionalSlope form (selectedCompletePath selected) direction)
    (selectedCompleteSlopeSigns selected).refined.interval.lower

def classifiedCompleteSlopesPositive?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (direction : QI) : Bool :=
  (eventPayloadActiveOwnerForms selected).all fun form =>
    decide (0 < selectedCompleteSlopeValue selected form direction)

theorem classifiedCompleteSlopesPositive?_eq_true_iff
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (direction : QI) :
    classifiedCompleteSlopesPositive? selected direction = true ↔
      ∀ form ∈ eventPayloadActiveOwnerForms selected,
        0 < selectedCompleteSlopeValue selected form direction := by
  simp [classifiedCompleteSlopesPositive?]

/-- Executable eight-direction tangent-cone search for every active face of
the complete selected child formula. -/
def classifiedCompleteTangentDirection?
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : Option QI :=
  coordinateDirections.find? fun direction =>
    classifiedCompleteSlopesPositive? selected direction

theorem classifiedCompleteTangentDirection?_some_mem
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : classifiedCompleteTangentDirection? selected = some direction) :
    direction ∈ coordinateDirections :=
  List.mem_of_find?_eq_some search

theorem classifiedCompleteTangentDirection?_some_slopes
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : classifiedCompleteTangentDirection? selected = some direction) :
    ∀ form ∈ eventPayloadActiveOwnerForms selected,
      0 < selectedCompleteSlopeValue selected form direction := by
  apply (classifiedCompleteSlopesPositive?_eq_true_iff selected direction).mp
  exact List.find?_some search

/-- A successful complete-child search has positive cleared slopes at every
rational parameter in its final common-sign interval. -/
theorem classifiedCompleteTangentDirection?_some_clearedSlopes
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : classifiedCompleteTangentDirection? selected = some direction)
    {t : ℚ}
    (lower : (selectedCompleteSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (selectedCompleteSlopeSigns selected).refined.interval.upper) :
    ∀ form ∈ eventPayloadActiveOwnerForms selected,
      0 < (clearedDirectionalSlope form (selectedCompletePath selected)
        direction).eval t := by
  intro form formMember
  let classification := selectedCompleteSlopeClassification selected
  let signs := selectedCompleteSlopeSigns selected
  let polynomial :=
    clearedDirectionalSlope form (selectedCompletePath selected) direction
  have polynomialMember : polynomial ∈
      selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      (classifiedCompleteTangentDirection?_some_mem search) formMember
  have canonicalPositive :=
    classifiedCompleteTangentDirection?_some_slopes search form formMember
  have productPositive :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      classification.branch.relations classification.parent signs
      polynomialMember canonicalPositive.ne' lower upper
  change 0 < polynomial.eval t
  change 0 < selectedCompleteSlopeValue selected form direction at canonicalPositive
  change 0 < selectedCompleteSlopeValue selected form direction *
    polynomial.eval t at productPositive
  nlinarith

/-- Repackage the complete slope-classified divisor as an ordinary input
event cell for the existing rational extraction and localization pipeline. -/
def selectedCompleteSlopeInputCell
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    InputEventCell state selected.candidate.sourceEvent.event :=
  { branch :=
      { factor := (selectedCompleteSlopeClassification selected).branch.factor
        relations := selected.candidate.inputCell.branch.relations.ofDvd
          (selectedCompleteSlopeClassification selected).branch.factor.input
          (selectedCompleteSlopeClassification selected).divides }
    divides := (selectedCompleteSlopeClassification selected).divides.trans
      selected.candidate.inputCell.divides
    parent := (selectedCompleteSlopeSigns selected).refined
    refines := RationalInterval.refines_trans
      (selectedCompleteSlopeSigns_refines_inputCell selected)
      selected.candidate.inputCell.signRefines }

def selectedCompleteSlopeInputSigns
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :=
  (selectedCompleteSlopeInputCell selected).branch.computeEventSigns
    (selectedCompleteSlopeInputCell selected).parent

/-- Proof-bearing tangent vector at any rational path point retained by the
complete slope-sign cell. -/
def completeClassifiedTangentDirectionAt
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : classifiedCompleteTangentDirection? selected = some direction)
    (t : ℚ)
    (lower : (selectedCompleteSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (selectedCompleteSlopeSigns selected).refined.interval.upper) :
    TangentDirection (eventPayloadActiveOwnerForms selected)
      ((selectedCompletePath selected).value t) :=
  { vector := direction
    normSqLeOne := coordinateDirection_normSq_le_one
      (classifiedCompleteTangentDirection?_some_mem search)
    slopes := by
      intro form member
      have rootLower :=
        (selectedCompleteSlopeSigns_refines_inputCell selected).1.trans lower
      have rootUpper := upper.trans
        (selectedCompleteSlopeSigns_refines_inputCell selected).2
      have denominator :=
        selected.candidate.inputCell.path_denominator_ne_on_cell
          rootLower rootUpper
      apply (eval_clearedDirectionalSlope_pos_iff form
        (selectedCompletePath selected) direction t denominator).1
      exact classifiedCompleteTangentDirection?_some_clearedSlopes search
        lower upper form member }

/-- One computed positive margin lower-bounds every complete classified slope
condition throughout the final common event cell. -/
def selectedCompleteSlopeStrictMargin
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  ConditionRelations.strictMargin
    (selectedCompleteSlopeClassification selected).branch.relations
    (selectedCompleteSlopeClassification selected).parent
    (selectedCompleteSlopeSigns selected)

theorem selectedCompleteSlopeStrictMargin_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < selectedCompleteSlopeStrictMargin selected :=
  ConditionRelations.strictMargin_pos
    (selectedCompleteSlopeClassification selected).branch.relations
    (selectedCompleteSlopeClassification selected).parent
    (selectedCompleteSlopeSigns selected)

theorem selectedCompleteSlopeStrictMargin_le_clearedSlope
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : classifiedCompleteTangentDirection? selected = some direction)
    {t : ℚ}
    (lower : (selectedCompleteSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (selectedCompleteSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (formMember : form ∈ eventPayloadActiveOwnerForms selected) :
    selectedCompleteSlopeStrictMargin selected ≤
      (clearedDirectionalSlope form (selectedCompletePath selected) direction).eval
        t := by
  let polynomial :=
    clearedDirectionalSlope form (selectedCompletePath selected) direction
  have polynomialMember : polynomial ∈
      selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      (classifiedCompleteTangentDirection?_some_mem search) formMember
  have canonicalPositive :=
    classifiedCompleteTangentDirection?_some_slopes search form formMember
  have marginLeAbs :=
    ConditionRelations.strictMargin_le_abs_eval
      (selectedCompleteSlopeClassification selected).branch.relations
      (selectedCompleteSlopeClassification selected).parent
      (selectedCompleteSlopeSigns selected) polynomialMember
      canonicalPositive.ne' lower upper
  have positive := classifiedCompleteTangentDirection?_some_clearedSlopes
    search lower upper form formMember
  simpa only [polynomial, selectedCompleteSlopeStrictMargin,
    abs_of_pos positive] using marginLeAbs

/-- Positive whole-cell upper bound for the projective denominator norm on
the complete classified slope interval. -/
def selectedCompleteSlopeDenominatorUpper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  denseEvalAbsBound (denominatorNorm (selectedCompletePath selected))
      (intervalMagnitude
        (selectedCompleteSlopeSigns selected).refined.interval.lower
        (selectedCompleteSlopeSigns selected).refined.interval.upper) + 1

theorem selectedCompleteSlopeDenominatorUpper_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < selectedCompleteSlopeDenominatorUpper selected := by
  unfold selectedCompleteSlopeDenominatorUpper
  have nonnegative := (denseHornerBounds_nonneg
    (denominatorNorm (selectedCompletePath selected))
    (intervalMagnitude_pos
      (selectedCompleteSlopeSigns selected).refined.interval.lower
      (selectedCompleteSlopeSigns selected).refined.interval.upper).le).1
  linarith

theorem denominatorNorm_le_selectedCompleteSlopeDenominatorUpper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {t : ℚ}
    (lower : (selectedCompleteSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (selectedCompleteSlopeSigns selected).refined.interval.upper) :
    (denominatorNorm (selectedCompletePath selected)).eval t ≤
      selectedCompleteSlopeDenominatorUpper selected := by
  let magnitude := intervalMagnitude
    (selectedCompleteSlopeSigns selected).refined.interval.lower
    (selectedCompleteSlopeSigns selected).refined.interval.upper
  have magnitudeNonnegative : 0 ≤ magnitude :=
    (intervalMagnitude_pos _ _).le
  have tMagnitude : |t| ≤ magnitude :=
    abs_le_intervalMagnitude lower upper
  have absoluteBound := abs_dense_eval_le_denseEvalAbsBound
    (denominatorNorm (selectedCompletePath selected)) magnitudeNonnegative tMagnitude
  exact (le_abs_self _).trans absoluteBound |>.trans (by
    unfold selectedCompleteSlopeDenominatorUpper
    dsimp only [magnitude]
    linarith)

/-- Uniform positive lower bound for every complete selected directional
derivative using the fixed classified compass vector. -/
def selectedCompleteSlopeDirectionalLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  selectedCompleteSlopeStrictMargin selected /
    selectedCompleteSlopeDenominatorUpper selected

theorem selectedCompleteSlopeDirectionalLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < selectedCompleteSlopeDirectionalLower selected :=
  div_pos (selectedCompleteSlopeStrictMargin_pos selected)
    (selectedCompleteSlopeDenominatorUpper_pos selected)

theorem selectedCompleteSlopeDirectionalLower_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : classifiedCompleteTangentDirection? selected = some direction)
    {t : ℚ}
    (lower : (selectedCompleteSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (selectedCompleteSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (formMember : form ∈ eventPayloadActiveOwnerForms selected) :
    selectedCompleteSlopeDirectionalLower selected ≤
      directionalSlope form ((selectedCompletePath selected).value t) direction := by
  have rootLower :=
    (selectedCompleteSlopeSigns_refines_inputCell selected).1.trans lower
  have rootUpper := upper.trans
    (selectedCompleteSlopeSigns_refines_inputCell selected).2
  have pathDenominator :=
    selected.candidate.inputCell.path_denominator_ne_on_cell rootLower rootUpper
  have denominatorPositive := eval_denominatorNorm_pos
    (selectedCompletePath selected) t pathDenominator
  have denominatorLe :=
    denominatorNorm_le_selectedCompleteSlopeDenominatorUpper selected lower
      upper
  have marginLe := selectedCompleteSlopeStrictMargin_le_clearedSlope search
    lower upper formMember
  have scaled : selectedCompleteSlopeDirectionalLower selected *
      (denominatorNorm (selectedCompletePath selected)).eval t ≤
      selectedCompleteSlopeStrictMargin selected := by
    unfold selectedCompleteSlopeDirectionalLower
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀
      (selectedCompleteSlopeDenominatorUpper_pos selected)).2
    exact mul_le_mul_of_nonneg_left denominatorLe
      (selectedCompleteSlopeStrictMargin_pos selected).le
  rw [eval_clearedDirectionalSlope form (selectedCompletePath selected) direction t
    pathDenominator] at marginLe
  apply (mul_le_mul_iff_of_pos_right denominatorPositive).mp
  calc
    selectedCompleteSlopeDirectionalLower selected *
        (denominatorNorm (selectedCompletePath selected)).eval t ≤
      selectedCompleteSlopeStrictMargin selected := scaled
    _ ≤ (denominatorNorm (selectedCompletePath selected)).eval t *
        directionalSlope form ((selectedCompletePath selected).value t) direction :=
      marginLe
    _ = directionalSlope form ((selectedCompletePath selected).value t) direction *
        (denominatorNorm (selectedCompletePath selected)).eval t := by ring

/-- Uniform finite lower bound for every complete active-face entry radius on
the classified event cell. -/
def selectedCompleteBoundaryRadiusLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  FTA.Maximality.positiveMinimum
    ((eventPayloadActiveOwnerForms selected).map fun form =>
      selectedCompleteSlopeDirectionalLower selected /
        (|form.radial| + 1))

theorem selectedCompleteBoundaryRadiusLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < selectedCompleteBoundaryRadiusLower selected := by
  apply FTA.Maximality.positiveMinimum_pos
  intro radius member
  rw [List.mem_map] at member
  rcases member with ⟨form, _formMember, rfl⟩
  exact div_pos (selectedCompleteSlopeDirectionalLower_pos selected)
    (by positivity)

theorem selectedCompleteBoundaryRadiusLower_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    selectedCompleteBoundaryRadiusLower selected ≤ 1 :=
  FTA.Maximality.positiveMinimum_le_one _

theorem selectedCompleteBoundaryRadiusLower_le_entryRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : classifiedCompleteTangentDirection? selected = some direction)
    {t : ℚ}
    (lower : (selectedCompleteSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (selectedCompleteSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (formMember : form ∈ eventPayloadActiveOwnerForms selected) :
    selectedCompleteBoundaryRadiusLower selected ≤
      entryRadius form ((selectedCompletePath selected).value t) direction := by
  apply (FTA.Maximality.positiveMinimum_le_of_mem
    (List.mem_map.mpr ⟨form, formMember, rfl⟩)).trans
  unfold entryRadius
  exact div_le_div_of_nonneg_right
    (selectedCompleteSlopeDirectionalLower_le search lower upper formMember)
    (by positivity)

/-- Complete active boundaries remain multiples of the final complete-slope
event factor. -/
theorem selectedCompleteSlopeActivePolynomial_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedForm form (selectedCompletePath selected)).toPolynomial :=
  (selectedCompleteSlopeClassification selected).divides.trans
    (selectedCompleteActivePolynomial_dvd selected member)

/-- A count-one selected event cannot lie simultaneously on a normalized
radial boundary and both coordinate sides of a sector corner when the corner
radius differs from the radial radius.  The proof eliminates their common
event factor from the homogeneous norm/coordinate identity. -/
theorem selectedComplete_scaled_norm_real_imag_not_all_active
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (matrix : Mat2 QI)
    (radius realThreshold imagThreshold : ℚ)
    (radialScale realScale imagScale : ℚ)
    (radialScaleNonzero : radialScale ≠ 0)
    (realScaleNonzero : realScale ≠ 0)
    (imagScaleNonzero : imagScale ≠ 0)
    (radiusGapNonzero :
      realThreshold ^ 2 + imagThreshold ^ 2 - radius ≠ 0)
    (denominatorLower : FTA.PositiveLowerBound.Certificate
      (clearedForm (affineNormForm matrix.c matrix.d)
        (selectedCompletePath selected))
      (selectedCompleteSlopeSigns selected).refined.interval)
    (radialMember : HermitianForm.scale radialScale
        (normComparisonForm matrix radius) ∈
      eventPayloadActiveOwnerForms selected)
    (realMember : HermitianForm.scale realScale
        (realComparisonForm matrix realThreshold) ∈
      eventPayloadActiveOwnerForms selected)
    (imagMember : HermitianForm.scale imagScale
        (imagComparisonForm matrix imagThreshold) ∈
      eventPayloadActiveOwnerForms selected) :
    False := by
  let classification := selectedCompleteSlopeClassification selected
  let path := selectedCompletePath selected
  let factor := classification.branch.factor.polynomial.toPolynomial
  let normPolynomial :=
    (clearedForm (normComparisonForm matrix radius) path).toPolynomial
  let realPolynomial :=
    (clearedForm (realComparisonForm matrix realThreshold) path).toPolynomial
  let imagPolynomial :=
    (clearedForm (imagComparisonForm matrix imagThreshold) path).toPolynomial
  have radialScaledDivides :=
    selectedCompleteSlopeActivePolynomial_dvd selected radialMember
  have realScaledDivides :=
    selectedCompleteSlopeActivePolynomial_dvd selected realMember
  have imagScaledDivides :=
    selectedCompleteSlopeActivePolynomial_dvd selected imagMember
  have normDivides : factor ∣ normPolynomial := by
    apply dvd_clearedForm_of_dvd_scale radialScale
      (normComparisonForm matrix radius) path radialScaleNonzero
    simpa only [factor, classification, path] using radialScaledDivides
  have realDivides : factor ∣ realPolynomial := by
    apply dvd_clearedForm_of_dvd_scale realScale
      (realComparisonForm matrix realThreshold) path realScaleNonzero
    simpa only [factor, classification, path] using realScaledDivides
  have imagDivides : factor ∣ imagPolynomial := by
    apply dvd_clearedForm_of_dvd_scale imagScale
      (imagComparisonForm matrix imagThreshold) path imagScaleNonzero
    simpa only [factor, classification, path] using imagScaledDivides
  have denominatorSquareDivides : factor ∣
      (clearedForm (affineNormForm matrix.c matrix.d) path *
        clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial := by
    apply dvd_clearedDenominator_square_of_norm_real_imag factor matrix radius
      realThreshold imagThreshold path radiusGapNonzero
    · simpa only [normPolynomial] using normDivides
    · simpa only [realPolynomial] using realDivides
    · simpa only [imagPolynomial] using imagDivides
  have denominatorProductLower : FTA.PositiveLowerBound.Certificate
      (clearedForm (affineNormForm matrix.c matrix.d) path *
        clearedForm (affineNormForm matrix.c matrix.d) path)
      (selectedCompleteSlopeSigns selected).refined.interval :=
    FTA.PositiveLowerBound.Certificate.mul denominatorLower denominatorLower
  apply CountOneInterval.no_positiveLowerBound_of_dvd
    classification.branch.factor.input
    (selectedCompleteSlopeSigns selected).refined
    denominatorSquareDivides
  simpa only [path] using denominatorProductLower

/-- A nondegenerate complete-child active boundary cannot have both cleared
gradient coordinates vanish on the final complete-slope event factor. -/
theorem selectedCompleteActive_clearedGradient_not_both_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadActiveOwnerForms selected)
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    ¬((selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedGradientX form (selectedCompletePath selected)).toPolynomial ∧
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedGradientY form (selectedCompletePath selected)).toPolynomial) := by
  intro bothDivides
  let classification := selectedCompleteSlopeClassification selected
  let path := selectedCompletePath selected
  let factor := classification.branch.factor.polynomial.toPolynomial
  let denominator := (denominatorNorm path).toPolynomial
  have factorDividesSelected :
      factor ∣ selected.candidate.inputCell.branch.factor.polynomial.toPolynomial :=
    classification.divides
  have factorDividesEvent :
      factor ∣ selected.candidate.sourceEvent.event.branch.factor.polynomial.toPolynomial :=
    factorDividesSelected.trans selected.candidate.inputCell.divides
  let denominatorCondition := denominatorCoprimeCondition
    selected.candidate.sourceEvent.event.branch
    selected.candidate.sourceEvent.event.denominatorNonEquality
  have eventCoprimeDenominator : IsCoprime
      selected.candidate.sourceEvent.event.branch.factor.polynomial.toPolynomial
      denominator := by
    have certificate := denominatorCondition.coprime.isCoprime
    simpa [denominatorCondition, denominator, path, selectedPath,
      denominatorCoprimeCondition_polynomial] using certificate
  have factorCoprimeDenominator : IsCoprime factor denominator :=
    eventCoprimeDenominator.of_isCoprime_of_dvd_left factorDividesEvent
  have factorCoprimeDenominatorSq :
      IsCoprime factor (denominator * denominator) :=
    factorCoprimeDenominator.mul_right factorCoprimeDenominator
  have factorDividesForm :
      factor ∣ (clearedForm form path).toPolynomial := by
    simpa [factor, path, classification] using
      selectedCompleteSlopeActivePolynomial_dvd selected formMember
  have factorDividesLeft : factor ∣
      (DensePolynomial.scale (4 * form.radial)
        (clearedForm form path * denominatorNorm path)).toPolynomial := by
    simp only [DensePolynomial.toPolynomial_scale,
      DensePolynomial.toPolynomial_mul]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left factorDividesForm denominator) _
  rw [clearedGradient_discriminant_identity] at factorDividesLeft
  simp only [DensePolynomial.toPolynomial_add,
    DensePolynomial.toPolynomial_mul, DensePolynomial.toPolynomial_scale]
      at factorDividesLeft
  have factorDividesGradientSum : factor ∣
      (clearedGradientX form path).toPolynomial *
          (clearedGradientX form path).toPolynomial +
        (clearedGradientY form path).toPolynomial *
          (clearedGradientY form path).toPolynomial :=
    dvd_add (dvd_mul_of_dvd_left bothDivides.1 _)
      (dvd_mul_of_dvd_left bothDivides.2 _)
  have factorDividesDiscriminant : factor ∣
      Polynomial.C (boundaryDiscriminant form) *
        (denominator * denominator) := by
    have difference := dvd_sub factorDividesLeft factorDividesGradientSum
    simpa [denominator] using difference
  have discriminantUnit :
      IsUnit (Polynomial.C (boundaryDiscriminant form)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr discriminantNonzero)
  have factorCoprimeDiscriminant : IsCoprime factor
      (Polynomial.C (boundaryDiscriminant form) *
        (denominator * denominator)) :=
    (isCoprime_mul_unit_left_right discriminantUnit factor
      (denominator * denominator)).2 factorCoprimeDenominatorSq
  have factorUnit :=
    factorCoprimeDiscriminant.isUnit_of_dvd factorDividesDiscriminant
  have degree := Polynomial.natDegree_eq_zero_of_isUnit factorUnit
  rw [DensePolynomial.natDegree_toPolynomial
    classification.branch.factor.input.nonzero] at degree
  exact classification.branch.factor.input.nonconstant degree

/-- Canonical zero is exactly divisibility by the final complete-slope factor
for every slope in the common classification table. -/
theorem selectedCompleteSlopeValue_eq_zero_iff_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadActiveOwnerForms selected)
    {direction : QI} (directionMember : direction ∈ coordinateDirections) :
    selectedCompleteSlopeValue selected form direction = 0 ↔
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedDirectionalSlope form (selectedCompletePath selected)
          direction).toPolynomial := by
  let classification := selectedCompleteSlopeClassification selected
  let signs := selectedCompleteSlopeSigns selected
  have polynomialMember :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      directionMember formMember
  constructor
  · intro zero
    exact ConditionRelations.dvd_of_canonicalEventValue_eq_zero
      classification.branch.relations classification.parent signs
      polynomialMember (by
        simpa [selectedCompleteSlopeValue, classification, signs] using zero)
  · intro divides
    exact canonicalEventValue_eq_zero_of_dvd
      classification.branch.factor.input _ _ divides

/-- A nondegenerate complete active face has a nonzero classified horizontal
or vertical slope coordinate. -/
theorem selectedCompleteActive_axis_values_not_both_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadActiveOwnerForms selected)
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    selectedCompleteSlopeValue selected form ⟨1, 0⟩ ≠ 0 ∨
      selectedCompleteSlopeValue selected form ⟨0, 1⟩ ≠ 0 := by
  by_contra neither
  push Not at neither
  apply selectedCompleteActive_clearedGradient_not_both_dvd selected
    formMember discriminantNonzero
  constructor
  · simpa using (selectedCompleteSlopeValue_eq_zero_iff_dvd selected formMember
      (direction := ⟨1, 0⟩) (by simp [coordinateDirections])).1 neither.1
  · simpa using (selectedCompleteSlopeValue_eq_zero_iff_dvd selected formMember
      (direction := ⟨0, 1⟩) (by simp [coordinateDirections])).1 neither.2

/-- Opposite table directions have opposite complete classified signs. -/
theorem selectedCompleteSlopeValue_opposite_pos_of_neg
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadActiveOwnerForms selected)
    {direction opposite : QI}
    (directionMember : direction ∈ coordinateDirections)
    (oppositeMember : opposite ∈ coordinateDirections)
    (polynomialOpposite :
      (clearedDirectionalSlope form (selectedCompletePath selected)
          opposite).toPolynomial =
        -(clearedDirectionalSlope form (selectedCompletePath selected)
          direction).toPolynomial)
    (negative : selectedCompleteSlopeValue selected form direction < 0) :
    0 < selectedCompleteSlopeValue selected form opposite := by
  let classification := selectedCompleteSlopeClassification selected
  let signs := selectedCompleteSlopeSigns selected
  have directionPolynomialMember :
      clearedDirectionalSlope form (selectedCompletePath selected) direction ∈
        selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      directionMember formMember
  have oppositePolynomialMember :
      clearedDirectionalSlope form (selectedCompletePath selected) opposite ∈
        selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      oppositeMember formMember
  have positive :=
    ConditionRelations.canonicalEventValue_pos_of_polynomial_neg
      classification.branch.relations classification.parent signs
      directionPolynomialMember oppositePolynomialMember polynomialOpposite
      (by simpa [selectedCompleteSlopeValue, classification, signs] using
        negative)
  simpa [selectedCompleteSlopeValue, classification, signs] using positive

/-- A nonzero complete classified slope can be cancelled from a product
which is divisible by the final complete-slope factor. -/
theorem selectedCompleteSlopeValue_eq_zero_of_mul_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    {leftForm rightForm : HermitianForm}
    (leftFormMember : leftForm ∈ eventPayloadActiveOwnerForms selected)
    {leftDirection rightDirection : QI}
    (leftDirectionMember : leftDirection ∈ coordinateDirections)
    (leftNonzero :
      selectedCompleteSlopeValue selected leftForm leftDirection ≠ 0)
    (divides :
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedDirectionalSlope leftForm (selectedCompletePath selected)
            leftDirection).toPolynomial *
          (clearedDirectionalSlope rightForm (selectedCompletePath selected)
            rightDirection).toPolynomial) :
    selectedCompleteSlopeValue selected rightForm rightDirection = 0 := by
  let classification := selectedCompleteSlopeClassification selected
  let signs := selectedCompleteSlopeSigns selected
  let leftPolynomial :=
    clearedDirectionalSlope leftForm (selectedCompletePath selected) leftDirection
  let rightPolynomial :=
    clearedDirectionalSlope rightForm (selectedCompletePath selected) rightDirection
  have leftMember : leftPolynomial ∈ selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      leftDirectionMember leftFormMember
  have zero :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_eq_zero_of_dvd_mul_left
      classification.branch.relations signs.refined.interval.lower leftMember
      (by simpa [selectedCompleteSlopeValue, classification, signs,
        leftPolynomial] using leftNonzero)
      (by simpa [classification, leftPolynomial, rightPolynomial] using divides)
  simpa [selectedCompleteSlopeValue, classification, signs, rightPolynomial]
    using zero

/-- Right-factor version of complete classified slope cancellation. -/
theorem selectedCompleteSlopeValue_eq_zero_of_mul_dvd_right
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    {leftForm rightForm : HermitianForm}
    (rightFormMember : rightForm ∈ eventPayloadActiveOwnerForms selected)
    {leftDirection rightDirection : QI}
    (rightDirectionMember : rightDirection ∈ coordinateDirections)
    (rightNonzero :
      selectedCompleteSlopeValue selected rightForm rightDirection ≠ 0)
    (divides :
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (clearedDirectionalSlope leftForm (selectedCompletePath selected)
            leftDirection).toPolynomial *
          (clearedDirectionalSlope rightForm (selectedCompletePath selected)
            rightDirection).toPolynomial) :
    selectedCompleteSlopeValue selected leftForm leftDirection = 0 := by
  let classification := selectedCompleteSlopeClassification selected
  let signs := selectedCompleteSlopeSigns selected
  let leftPolynomial :=
    clearedDirectionalSlope leftForm (selectedCompletePath selected) leftDirection
  let rightPolynomial :=
    clearedDirectionalSlope rightForm (selectedCompletePath selected) rightDirection
  have rightMember : rightPolynomial ∈
      selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      rightDirectionMember rightFormMember
  have zero :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_eq_zero_of_dvd_mul_right
      classification.branch.relations signs.refined.interval.lower rightMember
      (by simpa [selectedCompleteSlopeValue, classification, signs,
        rightPolynomial] using rightNonzero)
      (by simpa [classification, leftPolynomial, rightPolynomial] using divides)
  simpa [selectedCompleteSlopeValue, classification, signs, leftPolynomial]
    using zero

/-- Positive complete classified slopes survive positive rescaling and the
addition of a direction whose slope vanishes on the event factor. -/
theorem selectedCompleteSlopeValue_pos_of_direction_combination
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadActiveOwnerForms selected)
    {source target zeroDirection : QI}
    (sourceMember : source ∈ coordinateDirections)
    (targetMember : target ∈ coordinateDirections)
    (zeroMember : zeroDirection ∈ coordinateDirections)
    (scale errorScale : ℚ) (scalePositive : 0 < scale)
    (realCombination :
      target.re = scale * source.re + errorScale * zeroDirection.re)
    (imagCombination :
      target.im = scale * source.im + errorScale * zeroDirection.im)
    (zeroValue :
      selectedCompleteSlopeValue selected form zeroDirection = 0)
    (sourcePositive :
      0 < selectedCompleteSlopeValue selected form source) :
    0 < selectedCompleteSlopeValue selected form target := by
  let classification := selectedCompleteSlopeClassification selected
  let signs := selectedCompleteSlopeSigns selected
  let sourcePolynomial :=
    clearedDirectionalSlope form (selectedCompletePath selected) source
  let targetPolynomial :=
    clearedDirectionalSlope form (selectedCompletePath selected) target
  let zeroPolynomial :=
    clearedDirectionalSlope form (selectedCompletePath selected) zeroDirection
  let errorPolynomial := DensePolynomial.scale errorScale zeroPolynomial
  have sourcePolynomialMember : sourcePolynomial ∈
      selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      sourceMember formMember
  have targetPolynomialMember : targetPolynomial ∈
      selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      targetMember formMember
  have zeroDivides : classification.branch.factor.polynomial.toPolynomial ∣
      zeroPolynomial.toPolynomial := by
    exact (selectedCompleteSlopeValue_eq_zero_iff_dvd selected formMember
      zeroMember).1 zeroValue
  have errorDivides : classification.branch.factor.polynomial.toPolynomial ∣
      errorPolynomial.toPolynomial := by
    simp only [errorPolynomial, DensePolynomial.toPolynomial_scale]
    exact dvd_mul_of_dvd_right zeroDivides _
  have polynomialIdentity : targetPolynomial.toPolynomial =
      Polynomial.C scale * sourcePolynomial.toPolynomial +
        errorPolynomial.toPolynomial := by
    simp only [targetPolynomial, sourcePolynomial, zeroPolynomial,
      errorPolynomial, clearedDirectionalSlope,
      DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_scale]
    rw [realCombination, imagCombination]
    simp only [map_add, map_mul]
    ring
  have positive :=
    FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_pos_of_positive_scale_mod
      classification.branch.relations classification.parent signs
      sourcePolynomialMember targetPolynomialMember scale scalePositive
      polynomialIdentity errorDivides
      (by simpa [selectedCompleteSlopeValue, classification, signs,
        sourcePolynomial] using sourcePositive)
  simpa [selectedCompleteSlopeValue, classification, signs, targetPolynomial]
    using positive

/-- If one complete active gradient is vertical on the event and another is
horizontal, one of the four half-diagonals is positive for both. -/
theorem exists_classifiedComplete_diagonal_direction_of_axis_zeros
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    {vertical horizontal : HermitianForm}
    (verticalMember : vertical ∈ eventPayloadActiveOwnerForms selected)
    (horizontalMember : horizontal ∈ eventPayloadActiveOwnerForms selected)
    (verticalEastZero :
      selectedCompleteSlopeValue selected vertical ⟨1, 0⟩ = 0)
    (horizontalNorthZero :
      selectedCompleteSlopeValue selected horizontal ⟨0, 1⟩ = 0)
    (verticalNorthNonzero :
      selectedCompleteSlopeValue selected vertical ⟨0, 1⟩ ≠ 0)
    (horizontalEastNonzero :
      selectedCompleteSlopeValue selected horizontal ⟨1, 0⟩ ≠ 0) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedCompleteSlopeValue selected vertical direction ∧
        0 < selectedCompleteSlopeValue selected horizontal direction := by
  have verticalSouthPositive
      (northNegative :
        selectedCompleteSlopeValue selected vertical ⟨0, 1⟩ < 0) :
      0 < selectedCompleteSlopeValue selected vertical ⟨0, -1⟩ :=
    selectedCompleteSlopeValue_opposite_pos_of_neg selected verticalMember
      (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
      (by simp [coordinateDirections]) (by simp [coordinateDirections])
      (by simp) northNegative
  have horizontalWestPositive
      (eastNegative :
        selectedCompleteSlopeValue selected horizontal ⟨1, 0⟩ < 0) :
      0 < selectedCompleteSlopeValue selected horizontal ⟨-1, 0⟩ :=
    selectedCompleteSlopeValue_opposite_pos_of_neg selected horizontalMember
      (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
      (by simp [coordinateDirections]) (by simp [coordinateDirections])
      (by simp) eastNegative
  rcases lt_or_gt_of_ne verticalNorthNonzero with
      verticalNorthNegative | verticalNorthPositive
  · have verticalSouth := verticalSouthPositive verticalNorthNegative
    rcases lt_or_gt_of_ne horizontalEastNonzero with
        horizontalEastNegative | horizontalEastPositive
    · have horizontalWest := horizontalWestPositive horizontalEastNegative
      refine ⟨⟨-1 / 2, -1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
      · exact selectedCompleteSlopeValue_pos_of_direction_combination selected
          verticalMember (source := ⟨0, -1⟩) (target := ⟨-1 / 2, -1 / 2⟩)
          (zeroDirection := ⟨1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (-1 / 2) (by norm_num)
          (by norm_num) (by norm_num) verticalEastZero verticalSouth
      · exact selectedCompleteSlopeValue_pos_of_direction_combination selected
          horizontalMember (source := ⟨-1, 0⟩)
          (target := ⟨-1 / 2, -1 / 2⟩) (zeroDirection := ⟨0, 1⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (-1 / 2) (by norm_num)
          (by norm_num) (by norm_num) horizontalNorthZero horizontalWest
    · refine ⟨⟨1 / 2, -1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
      · exact selectedCompleteSlopeValue_pos_of_direction_combination selected
          verticalMember (source := ⟨0, -1⟩) (target := ⟨1 / 2, -1 / 2⟩)
          (zeroDirection := ⟨1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (1 / 2) (by norm_num)
          (by norm_num) (by norm_num) verticalEastZero verticalSouth
      · exact selectedCompleteSlopeValue_pos_of_direction_combination selected
          horizontalMember (source := ⟨1, 0⟩)
          (target := ⟨1 / 2, -1 / 2⟩) (zeroDirection := ⟨0, 1⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (-1 / 2) (by norm_num)
          (by norm_num) (by norm_num) horizontalNorthZero
          horizontalEastPositive
  · rcases lt_or_gt_of_ne horizontalEastNonzero with
        horizontalEastNegative | horizontalEastPositive
    · have horizontalWest := horizontalWestPositive horizontalEastNegative
      refine ⟨⟨-1 / 2, 1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
      · exact selectedCompleteSlopeValue_pos_of_direction_combination selected
          verticalMember (source := ⟨0, 1⟩) (target := ⟨-1 / 2, 1 / 2⟩)
          (zeroDirection := ⟨1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (-1 / 2) (by norm_num)
          (by norm_num) (by norm_num) verticalEastZero verticalNorthPositive
      · exact selectedCompleteSlopeValue_pos_of_direction_combination selected
          horizontalMember (source := ⟨-1, 0⟩)
          (target := ⟨-1 / 2, 1 / 2⟩) (zeroDirection := ⟨0, 1⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (1 / 2) (by norm_num)
          (by norm_num) (by norm_num) horizontalNorthZero horizontalWest
    · refine ⟨⟨1 / 2, 1 / 2⟩, by simp [coordinateDirections], ?_, ?_⟩
      · exact selectedCompleteSlopeValue_pos_of_direction_combination selected
          verticalMember (source := ⟨0, 1⟩) (target := ⟨1 / 2, 1 / 2⟩)
          (zeroDirection := ⟨1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (1 / 2) (by norm_num)
          (by norm_num) (by norm_num) verticalEastZero verticalNorthPositive
      · exact selectedCompleteSlopeValue_pos_of_direction_combination selected
          horizontalMember (source := ⟨1, 0⟩)
          (target := ⟨1 / 2, 1 / 2⟩) (zeroDirection := ⟨0, 1⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp [coordinateDirections]) (1 / 2) (1 / 2) (by norm_num)
          (by norm_num) (by norm_num) horizontalNorthZero
          horizontalEastPositive

/-- Orthogonality of a compatible pair remains divisible after the complete
slope classifier refines the original selected event factor. -/
def selectedCompleteGradientDotPolynomial
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (left right : HermitianForm) :
    RatPolynomial :=
  clearedDirectionalSlope left (selectedCompletePath selected) ⟨1, 0⟩ *
      clearedDirectionalSlope right (selectedCompletePath selected) ⟨1, 0⟩ +
    clearedDirectionalSlope left (selectedCompletePath selected) ⟨0, 1⟩ *
      clearedDirectionalSlope right (selectedCompletePath selected) ⟨0, 1⟩

theorem selectedCompleteGradientDotPolynomial_dvd_of_pairingConstant_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadActiveOwnerForms selected)
    (rightMember : right ∈ eventPayloadActiveOwnerForms selected)
    (constantZero : gradientPairingConstant left right = 0) :
    (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (selectedCompleteGradientDotPolynomial selected left right).toPolynomial := by
  apply dvd_trans (selectedCompleteSlopeClassification selected).divides
  have originalDivides := dvd_clearedGradient_pairing_of_constant_zero
    left right (selectedCompletePath selected)
    selected.candidate.inputCell.branch.factor.polynomial.toPolynomial
    constantZero (selectedCompleteActivePolynomial_dvd selected leftMember)
    (selectedCompleteActivePolynomial_dvd selected rightMember)
  simpa only [selectedCompleteGradientDotPolynomial,
    DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
    toPolynomial_clearedDirectionalSlope_east,
    toPolynomial_clearedDirectionalSlope_north] using originalDivides

theorem selectedCompleteGradientY_product_dvd_of_leftEast_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadActiveOwnerForms selected)
    (dotDivides :
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedCompleteGradientDotPolynomial selected left right).toPolynomial)
    (leftEastZero :
      selectedCompleteSlopeValue selected left ⟨1, 0⟩ = 0) :
    (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedDirectionalSlope left (selectedCompletePath selected) ⟨0, 1⟩).toPolynomial *
        (clearedDirectionalSlope right (selectedCompletePath selected) ⟨0, 1⟩).toPolynomial := by
  have leftEastDivides :=
    (selectedCompleteSlopeValue_eq_zero_iff_dvd selected leftMember
      (direction := ⟨1, 0⟩) (by simp [coordinateDirections])).1 leftEastZero
  have xProductDivides := dvd_mul_of_dvd_left leftEastDivides
    (clearedDirectionalSlope right (selectedCompletePath selected) ⟨1, 0⟩).toPolynomial
  have difference := dvd_sub dotDivides xProductDivides
  simpa only [selectedCompleteGradientDotPolynomial,
    DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
    add_sub_cancel_left] using difference

theorem selectedCompleteGradientY_product_dvd_of_rightEast_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (rightMember : right ∈ eventPayloadActiveOwnerForms selected)
    (dotDivides :
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedCompleteGradientDotPolynomial selected left right).toPolynomial)
    (rightEastZero :
      selectedCompleteSlopeValue selected right ⟨1, 0⟩ = 0) :
    (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedDirectionalSlope left (selectedCompletePath selected) ⟨0, 1⟩).toPolynomial *
        (clearedDirectionalSlope right (selectedCompletePath selected) ⟨0, 1⟩).toPolynomial := by
  have rightEastDivides :=
    (selectedCompleteSlopeValue_eq_zero_iff_dvd selected rightMember
      (direction := ⟨1, 0⟩) (by simp [coordinateDirections])).1 rightEastZero
  have xProductDivides := dvd_mul_of_dvd_right rightEastDivides
    (clearedDirectionalSlope left (selectedCompletePath selected) ⟨1, 0⟩).toPolynomial
  have difference := dvd_sub dotDivides xProductDivides
  simpa only [selectedCompleteGradientDotPolynomial,
    DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
    add_sub_cancel_left] using difference

theorem selectedCompleteGradientX_product_dvd_of_leftNorth_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadActiveOwnerForms selected)
    (dotDivides :
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedCompleteGradientDotPolynomial selected left right).toPolynomial)
    (leftNorthZero :
      selectedCompleteSlopeValue selected left ⟨0, 1⟩ = 0) :
    (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedDirectionalSlope left (selectedCompletePath selected) ⟨1, 0⟩).toPolynomial *
        (clearedDirectionalSlope right (selectedCompletePath selected) ⟨1, 0⟩).toPolynomial := by
  have leftNorthDivides :=
    (selectedCompleteSlopeValue_eq_zero_iff_dvd selected leftMember
      (direction := ⟨0, 1⟩) (by simp [coordinateDirections])).1 leftNorthZero
  have yProductDivides := dvd_mul_of_dvd_left leftNorthDivides
    (clearedDirectionalSlope right (selectedCompletePath selected) ⟨0, 1⟩).toPolynomial
  have difference := dvd_sub dotDivides yProductDivides
  simpa only [selectedCompleteGradientDotPolynomial,
    DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
    add_sub_cancel_right] using difference

theorem selectedCompleteGradientX_product_dvd_of_rightNorth_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (rightMember : right ∈ eventPayloadActiveOwnerForms selected)
    (dotDivides :
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedCompleteGradientDotPolynomial selected left right).toPolynomial)
    (rightNorthZero :
      selectedCompleteSlopeValue selected right ⟨0, 1⟩ = 0) :
    (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
      (clearedDirectionalSlope left (selectedCompletePath selected) ⟨1, 0⟩).toPolynomial *
        (clearedDirectionalSlope right (selectedCompletePath selected) ⟨1, 0⟩).toPolynomial := by
  have rightNorthDivides :=
    (selectedCompleteSlopeValue_eq_zero_iff_dvd selected rightMember
      (direction := ⟨0, 1⟩) (by simp [coordinateDirections])).1 rightNorthZero
  have yProductDivides := dvd_mul_of_dvd_right rightNorthDivides
    (clearedDirectionalSlope left (selectedCompletePath selected) ⟨0, 1⟩).toPolynomial
  have difference := dvd_sub dotDivides yProductDivides
  simpa only [selectedCompleteGradientDotPolynomial,
    DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
    add_sub_cancel_right] using difference

/-- When all four complete classified axis slopes are nonzero, one axis is
common-positive; the divisible dot sum excludes opposing signs on both axes. -/
theorem exists_classifiedComplete_axis_direction_pair_of_nonzero_axes
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadActiveOwnerForms selected)
    (rightMember : right ∈ eventPayloadActiveOwnerForms selected)
    (leftEastNonzero :
      selectedCompleteSlopeValue selected left ⟨1, 0⟩ ≠ 0)
    (rightEastNonzero :
      selectedCompleteSlopeValue selected right ⟨1, 0⟩ ≠ 0)
    (leftNorthNonzero :
      selectedCompleteSlopeValue selected left ⟨0, 1⟩ ≠ 0)
    (rightNorthNonzero :
      selectedCompleteSlopeValue selected right ⟨0, 1⟩ ≠ 0)
    (dotDivides :
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedCompleteGradientDotPolynomial selected left right).toPolynomial) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedCompleteSlopeValue selected left direction ∧
        0 < selectedCompleteSlopeValue selected right direction := by
  by_cases eastProductPositive : 0 <
      selectedCompleteSlopeValue selected left ⟨1, 0⟩ *
        selectedCompleteSlopeValue selected right ⟨1, 0⟩
  · rcases mul_pos_iff.mp eastProductPositive with
      ⟨leftPositive, rightPositive⟩ | ⟨leftNegative, rightNegative⟩
    · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], leftPositive,
        rightPositive⟩
    · have leftWestPositive :=
        selectedCompleteSlopeValue_opposite_pos_of_neg selected leftMember
          (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp) leftNegative
      have rightWestPositive :=
        selectedCompleteSlopeValue_opposite_pos_of_neg selected rightMember
          (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp) rightNegative
      exact ⟨⟨-1, 0⟩, by simp [coordinateDirections], leftWestPositive,
        rightWestPositive⟩
  · have eastProductNegative :
        selectedCompleteSlopeValue selected left ⟨1, 0⟩ *
            selectedCompleteSlopeValue selected right ⟨1, 0⟩ < 0 :=
      lt_of_le_of_ne (le_of_not_gt eastProductPositive)
        (mul_ne_zero leftEastNonzero rightEastNonzero)
    by_cases northProductPositive : 0 <
        selectedCompleteSlopeValue selected left ⟨0, 1⟩ *
          selectedCompleteSlopeValue selected right ⟨0, 1⟩
    · rcases mul_pos_iff.mp northProductPositive with
        ⟨leftPositive, rightPositive⟩ | ⟨leftNegative, rightNegative⟩
      · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], leftPositive,
          rightPositive⟩
      · have leftSouthPositive :=
          selectedCompleteSlopeValue_opposite_pos_of_neg selected leftMember
            (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
            (by simp [coordinateDirections]) (by simp [coordinateDirections])
            (by simp) leftNegative
        have rightSouthPositive :=
          selectedCompleteSlopeValue_opposite_pos_of_neg selected rightMember
            (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
            (by simp [coordinateDirections]) (by simp [coordinateDirections])
            (by simp) rightNegative
        exact ⟨⟨0, -1⟩, by simp [coordinateDirections],
          leftSouthPositive, rightSouthPositive⟩
    · have northProductNegative :
          selectedCompleteSlopeValue selected left ⟨0, 1⟩ *
              selectedCompleteSlopeValue selected right ⟨0, 1⟩ < 0 :=
        lt_of_le_of_ne (le_of_not_gt northProductPositive)
          (mul_ne_zero leftNorthNonzero rightNorthNonzero)
      let classification := selectedCompleteSlopeClassification selected
      let signs := selectedCompleteSlopeSigns selected
      exact (FTA.CCLBranchEventOwner.ConditionRelations.not_both_canonical_products_neg_of_dvd_sum
        classification.branch.relations classification.parent signs
        (clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
          (direction := ⟨1, 0⟩) (by simp [coordinateDirections]) leftMember)
        (clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
          (direction := ⟨1, 0⟩) (by simp [coordinateDirections]) rightMember)
        (clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
          (direction := ⟨0, 1⟩) (by simp [coordinateDirections]) leftMember)
        (clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
          (direction := ⟨0, 1⟩) (by simp [coordinateDirections]) rightMember)
        (by simpa only [selectedCompleteGradientDotPolynomial,
          DensePolynomial.toPolynomial_add, DensePolynomial.toPolynomial_mul,
          classification] using dotDivides)
        (by simpa [selectedCompleteSlopeValue, classification, signs] using
          eastProductNegative)
        (by simpa [selectedCompleteSlopeValue, classification, signs] using
          northProductNegative)).elim

/-- Two nondegenerate complete active faces with event-divisible gradient dot
product admit a common-positive entry of the exact eight-direction table. -/
theorem exists_classifiedComplete_direction_pair_of_gradientDot_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadActiveOwnerForms selected)
    (rightMember : right ∈ eventPayloadActiveOwnerForms selected)
    (leftNondegenerate : boundaryDiscriminant left ≠ 0)
    (rightNondegenerate : boundaryDiscriminant right ≠ 0)
    (dotDivides :
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedCompleteGradientDotPolynomial selected left right).toPolynomial) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedCompleteSlopeValue selected left direction ∧
        0 < selectedCompleteSlopeValue selected right direction := by
  have leftAxes := selectedCompleteActive_axis_values_not_both_zero selected
    leftMember leftNondegenerate
  have rightAxes := selectedCompleteActive_axis_values_not_both_zero selected
    rightMember rightNondegenerate
  by_cases leftEastZero :
      selectedCompleteSlopeValue selected left ⟨1, 0⟩ = 0
  · have leftNorthNonzero :
        selectedCompleteSlopeValue selected left ⟨0, 1⟩ ≠ 0 := by
      rcases leftAxes with leftEastNonzero | leftNorthNonzero
      · exact (leftEastNonzero leftEastZero).elim
      · exact leftNorthNonzero
    have yProductDivides :=
      selectedCompleteGradientY_product_dvd_of_leftEast_zero selected
        leftMember dotDivides leftEastZero
    have rightNorthZero := selectedCompleteSlopeValue_eq_zero_of_mul_dvd
      selected leftMember (rightForm := right) (leftDirection := ⟨0, 1⟩)
      (rightDirection := ⟨0, 1⟩) (by simp [coordinateDirections])
      leftNorthNonzero yProductDivides
    have rightEastNonzero :
        selectedCompleteSlopeValue selected right ⟨1, 0⟩ ≠ 0 := by
      rcases rightAxes with rightEastNonzero | rightNorthNonzero
      · exact rightEastNonzero
      · exact (rightNorthNonzero rightNorthZero).elim
    exact exists_classifiedComplete_diagonal_direction_of_axis_zeros selected
      leftMember rightMember leftEastZero rightNorthZero leftNorthNonzero
      rightEastNonzero
  · by_cases rightEastZero :
        selectedCompleteSlopeValue selected right ⟨1, 0⟩ = 0
    · have rightNorthNonzero :
          selectedCompleteSlopeValue selected right ⟨0, 1⟩ ≠ 0 := by
        rcases rightAxes with rightEastNonzero | rightNorthNonzero
        · exact (rightEastNonzero rightEastZero).elim
        · exact rightNorthNonzero
      have yProductDivides :=
        selectedCompleteGradientY_product_dvd_of_rightEast_zero selected
          rightMember dotDivides rightEastZero
      have leftNorthZero :=
        selectedCompleteSlopeValue_eq_zero_of_mul_dvd_right selected
          rightMember (leftForm := left) (leftDirection := ⟨0, 1⟩)
          (rightDirection := ⟨0, 1⟩) (by simp [coordinateDirections])
          rightNorthNonzero yProductDivides
      rcases exists_classifiedComplete_diagonal_direction_of_axis_zeros
          selected rightMember leftMember rightEastZero leftNorthZero
          rightNorthNonzero leftEastZero with
        ⟨direction, directionMember, rightPositive, leftPositive⟩
      exact ⟨direction, directionMember, leftPositive, rightPositive⟩
    · have leftNorthNonzero :
          selectedCompleteSlopeValue selected left ⟨0, 1⟩ ≠ 0 := by
        intro leftNorthZero
        have xProductDivides :=
          selectedCompleteGradientX_product_dvd_of_leftNorth_zero selected
            leftMember dotDivides leftNorthZero
        exact rightEastZero
          (selectedCompleteSlopeValue_eq_zero_of_mul_dvd selected leftMember
            (rightForm := right) (leftDirection := ⟨1, 0⟩)
            (rightDirection := ⟨1, 0⟩) (by simp [coordinateDirections])
            leftEastZero xProductDivides)
      have rightNorthNonzero :
          selectedCompleteSlopeValue selected right ⟨0, 1⟩ ≠ 0 := by
        intro rightNorthZero
        have xProductDivides :=
          selectedCompleteGradientX_product_dvd_of_rightNorth_zero selected
            rightMember dotDivides rightNorthZero
        exact rightEastZero
          (selectedCompleteSlopeValue_eq_zero_of_mul_dvd selected leftMember
            (rightForm := right) (leftDirection := ⟨1, 0⟩)
            (rightDirection := ⟨1, 0⟩) (by simp [coordinateDirections])
            leftEastZero xProductDivides)
      exact exists_classifiedComplete_axis_direction_pair_of_nonzero_axes
        selected leftMember rightMember leftEastZero rightEastZero
        leftNorthNonzero rightNorthNonzero dotDivides

/-- Every nondegenerate complete active face has a strictly positive axis
direction in the executable table. -/
theorem exists_classifiedComplete_axis_direction_single
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (formMember : form ∈ eventPayloadActiveOwnerForms selected)
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedCompleteSlopeValue selected form direction := by
  rcases selectedCompleteActive_axis_values_not_both_zero selected formMember
      discriminantNonzero with eastNonzero | northNonzero
  · rcases lt_or_gt_of_ne eastNonzero with eastNegative | eastPositive
    · refine ⟨⟨-1, 0⟩, by simp [coordinateDirections], ?_⟩
      exact selectedCompleteSlopeValue_opposite_pos_of_neg selected formMember
        (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
        (by simp [coordinateDirections]) (by simp [coordinateDirections])
        (by simp) eastNegative
    · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], eastPositive⟩
  · rcases lt_or_gt_of_ne northNonzero with northNegative | northPositive
    · refine ⟨⟨0, -1⟩, by simp [coordinateDirections], ?_⟩
      exact selectedCompleteSlopeValue_opposite_pos_of_neg selected formMember
        (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
        (by simp [coordinateDirections]) (by simp [coordinateDirections])
        (by simp) northNegative
    · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], northPositive⟩

/-- Any common-positive entry makes the executable complete search succeed. -/
theorem classifiedCompleteTangentDirection?_isSome_of_exists
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (existsDirection :
      ∃ direction ∈ coordinateDirections,
        ∀ form ∈ eventPayloadActiveOwnerForms selected,
          0 < selectedCompleteSlopeValue selected form direction) :
    (classifiedCompleteTangentDirection? selected).isSome := by
  rw [classifiedCompleteTangentDirection?, List.find?_isSome]
  rcases existsDirection with ⟨direction, directionMember, slopes⟩
  exact ⟨direction, directionMember,
    (classifiedCompleteSlopesPositive?_eq_true_iff selected direction).2 slopes⟩

/-- A strictly positive invariant angle gap rules out simultaneous failure of
the four antipodal direction pairs in the complete classified compass table. -/
theorem not_four_selectedComplete_direction_products_nonpositive_of_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadActiveOwnerForms selected)
    (rightMember : right ∈ eventPayloadActiveOwnerForms selected)
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2)
    (eastNonpositive :
      selectedCompleteSlopeValue selected left ⟨1, 0⟩ *
        selectedCompleteSlopeValue selected right ⟨1, 0⟩ ≤ 0)
    (northNonpositive :
      selectedCompleteSlopeValue selected left ⟨0, 1⟩ *
        selectedCompleteSlopeValue selected right ⟨0, 1⟩ ≤ 0)
    (northEastNonpositive :
      selectedCompleteSlopeValue selected left ⟨1 / 2, 1 / 2⟩ *
        selectedCompleteSlopeValue selected right ⟨1 / 2, 1 / 2⟩ ≤ 0)
    (southEastNonpositive :
      selectedCompleteSlopeValue selected left ⟨1 / 2, -1 / 2⟩ *
        selectedCompleteSlopeValue selected right ⟨1 / 2, -1 / 2⟩ ≤ 0) :
    False := by
  let classification := selectedCompleteSlopeClassification selected
  let signs := selectedCompleteSlopeSigns selected
  let path := selectedCompletePath selected
  let gap := boundaryDiscriminant left * boundaryDiscriminant right -
    2 * gradientPairingConstant left right ^ 2
  let base := DensePolynomial.scale gap
    ((denominatorNorm path * denominatorNorm path) *
      (denominatorNorm path * denominatorNorm path))
  let leftEast := clearedDirectionalSlope left path ⟨1, 0⟩
  let rightEast := clearedDirectionalSlope right path ⟨1, 0⟩
  let leftNorth := clearedDirectionalSlope left path ⟨0, 1⟩
  let rightNorth := clearedDirectionalSlope right path ⟨0, 1⟩
  let leftNorthEast := clearedDirectionalSlope left path ⟨1 / 2, 1 / 2⟩
  let rightNorthEast := clearedDirectionalSlope right path ⟨1 / 2, 1 / 2⟩
  let leftSouthEast := clearedDirectionalSlope left path ⟨1 / 2, -1 / 2⟩
  let rightSouthEast := clearedDirectionalSlope right path ⟨1 / 2, -1 / 2⟩
  have leftEastMember : leftEast ∈ selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightEastMember : rightEast ∈ selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have leftNorthMember : leftNorth ∈ selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightNorthMember : rightNorth ∈ selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have leftNorthEastMember : leftNorthEast ∈
      selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightNorthEastMember : rightNorthEast ∈
      selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have leftSouthEastMember : leftSouthEast ∈
      selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightSouthEastMember : rightSouthEast ∈
      selectedCompleteSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedCompleteSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have basePositive : ∀ t : ℚ,
      signs.refined.interval.lower ≤ t →
      t ≤ signs.refined.interval.upper → 0 < base.eval t := by
    intro t lower upper
    let denominator := RelevantCurveEvent.ownerDenominatorCertificate
      selected.candidate.sourceEvent.event
    have rootLower := selected.candidate.inputCell.signRefines.1.trans
      ((selectedCompleteSlopeSigns_refines_inputCell selected).1.trans lower)
    have rootUpper :=
      (upper.trans
          (selectedCompleteSlopeSigns_refines_inputCell selected).2).trans
        selected.candidate.inputCell.signRefines.2
    have denominatorLower : denominator.bound ≤
        (denominatorNorm path).eval t := by
      simpa only [path, selectedPath] using
        denominator.lower rootLower rootUpper
    have denominatorPositive : 0 < (denominatorNorm path).eval t :=
      denominator.positive.trans_le denominatorLower
    simp only [base, DensePolynomial.eval_scale, DensePolynomial.eval_mul]
    exact mul_pos angleGapPositive
      (mul_pos (mul_pos denominatorPositive denominatorPositive)
        (mul_pos denominatorPositive denominatorPositive))
  have baseLower : FTA.PositiveLowerBound.Certificate base
      signs.refined.interval := by
    simpa only [base, gap, path, signs] using
      selectedCompleteAngleGapPositiveLowerBound selected left right
        angleGapPositive
  have obstructionDivides :
      classification.branch.factor.polynomial.toPolynomial ∣
        (base +
          (DensePolynomial.scale 4
              ((leftEast * rightEast) * (leftNorth * rightNorth)) +
            DensePolynomial.scale 16
              ((leftNorthEast * rightNorthEast) *
                (leftSouthEast * rightSouthEast)))).toPolynomial := by
    have identity := dvd_compass_angleGap_identity left right path
      classification.branch.factor.polynomial.toPolynomial
      (by
        simpa only [classification, path] using
          selectedCompleteSlopeActivePolynomial_dvd selected leftMember)
      (by
        simpa only [classification, path] using
          selectedCompleteSlopeActivePolynomial_dvd selected rightMember)
    simpa only [base, gap, leftEast, rightEast, leftNorth, rightNorth,
      leftNorthEast, rightNorthEast, leftSouthEast, rightSouthEast] using
        identity
  exact ConditionRelations.not_four_direction_products_nonpositive
    classification.branch.relations classification.parent signs
    leftEastMember rightEastMember leftNorthMember rightNorthMember
    leftNorthEastMember rightNorthEastMember leftSouthEastMember
    rightSouthEastMember 4 16 (by norm_num) (by norm_num) basePositive
    baseLower obstructionDivides
    (by simpa [selectedCompleteSlopeValue, classification, signs, path,
      leftEast, rightEast] using eastNonpositive)
    (by simpa [selectedCompleteSlopeValue, classification, signs, path,
      leftNorth, rightNorth] using northNonpositive)
    (by simpa [selectedCompleteSlopeValue, classification, signs, path,
      leftNorthEast, rightNorthEast] using northEastNonpositive)
    (by simpa [selectedCompleteSlopeValue, classification, signs, path,
      leftSouthEast, rightSouthEast] using southEastNonpositive)

/-- A positive invariant angle gap forces one of the eight classified compass
directions to have strictly positive slopes for both active faces. -/
theorem exists_classifiedComplete_direction_pair_of_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadActiveOwnerForms selected)
    (rightMember : right ∈ eventPayloadActiveOwnerForms selected)
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedCompleteSlopeValue selected left direction ∧
        0 < selectedCompleteSlopeValue selected right direction := by
  have negNorthEast : (-⟨1 / 2, 1 / 2⟩ : QI) =
      ⟨-1 / 2, -1 / 2⟩ := by
    ext <;> norm_num
  have negSouthEast : (-⟨1 / 2, -1 / 2⟩ : QI) =
      ⟨-1 / 2, 1 / 2⟩ := by
    ext <;> norm_num
  by_cases eastProduct : 0 <
      selectedCompleteSlopeValue selected left ⟨1, 0⟩ *
        selectedCompleteSlopeValue selected right ⟨1, 0⟩
  · rcases mul_pos_iff.mp eastProduct with positive | negative
    · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], positive⟩
    · have leftWestPositive :=
        selectedCompleteSlopeValue_opposite_pos_of_neg selected leftMember
          (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp) negative.1
      have rightWestPositive :=
        selectedCompleteSlopeValue_opposite_pos_of_neg selected rightMember
          (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp) negative.2
      exact ⟨⟨-1, 0⟩, by simp [coordinateDirections], leftWestPositive,
        rightWestPositive⟩
  · by_cases northProduct : 0 <
        selectedCompleteSlopeValue selected left ⟨0, 1⟩ *
          selectedCompleteSlopeValue selected right ⟨0, 1⟩
    · rcases mul_pos_iff.mp northProduct with positive | negative
      · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], positive⟩
      · have leftSouthPositive :=
          selectedCompleteSlopeValue_opposite_pos_of_neg selected leftMember
            (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
            (by simp [coordinateDirections]) (by simp [coordinateDirections])
            (by simp) negative.1
        have rightSouthPositive :=
          selectedCompleteSlopeValue_opposite_pos_of_neg selected rightMember
            (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
            (by simp [coordinateDirections]) (by simp [coordinateDirections])
            (by simp) negative.2
        exact ⟨⟨0, -1⟩, by simp [coordinateDirections], leftSouthPositive,
          rightSouthPositive⟩
    · by_cases northEastProduct : 0 <
          selectedCompleteSlopeValue selected left ⟨1 / 2, 1 / 2⟩ *
            selectedCompleteSlopeValue selected right ⟨1 / 2, 1 / 2⟩
      · rcases mul_pos_iff.mp northEastProduct with positive | negative
        · exact ⟨⟨1 / 2, 1 / 2⟩, by simp [coordinateDirections], positive⟩
        · have leftSouthWestPositive :=
            selectedCompleteSlopeValue_opposite_pos_of_neg selected leftMember
              (direction := ⟨1 / 2, 1 / 2⟩)
              (opposite := (-⟨1 / 2, 1 / 2⟩ : QI))
              (by simp [coordinateDirections])
              (by rw [negNorthEast]; simp [coordinateDirections])
              (toPolynomial_clearedDirectionalSlope_neg left
                (selectedCompletePath selected) ⟨1 / 2, 1 / 2⟩) negative.1
          have rightSouthWestPositive :=
            selectedCompleteSlopeValue_opposite_pos_of_neg selected rightMember
              (direction := ⟨1 / 2, 1 / 2⟩)
              (opposite := (-⟨1 / 2, 1 / 2⟩ : QI))
              (by simp [coordinateDirections])
              (by rw [negNorthEast]; simp [coordinateDirections])
              (toPolynomial_clearedDirectionalSlope_neg right
                (selectedCompletePath selected) ⟨1 / 2, 1 / 2⟩) negative.2
          rw [negNorthEast] at leftSouthWestPositive rightSouthWestPositive
          exact ⟨⟨-1 / 2, -1 / 2⟩, by simp [coordinateDirections],
            leftSouthWestPositive, rightSouthWestPositive⟩
      · by_cases southEastProduct : 0 <
            selectedCompleteSlopeValue selected left ⟨1 / 2, -1 / 2⟩ *
              selectedCompleteSlopeValue selected right ⟨1 / 2, -1 / 2⟩
        · rcases mul_pos_iff.mp southEastProduct with positive | negative
          · exact ⟨⟨1 / 2, -1 / 2⟩, by simp [coordinateDirections],
              positive⟩
          · have leftNorthWestPositive :=
              selectedCompleteSlopeValue_opposite_pos_of_neg selected leftMember
                (direction := ⟨1 / 2, -1 / 2⟩)
                (opposite := (-⟨1 / 2, -1 / 2⟩ : QI))
                (by simp [coordinateDirections])
                (by rw [negSouthEast]; simp [coordinateDirections])
                (toPolynomial_clearedDirectionalSlope_neg left
                  (selectedCompletePath selected) ⟨1 / 2, -1 / 2⟩) negative.1
            have rightNorthWestPositive :=
              selectedCompleteSlopeValue_opposite_pos_of_neg selected rightMember
                (direction := ⟨1 / 2, -1 / 2⟩)
                (opposite := (-⟨1 / 2, -1 / 2⟩ : QI))
                (by simp [coordinateDirections])
                (by rw [negSouthEast]; simp [coordinateDirections])
                (toPolynomial_clearedDirectionalSlope_neg right
                  (selectedCompletePath selected) ⟨1 / 2, -1 / 2⟩) negative.2
            rw [negSouthEast] at leftNorthWestPositive rightNorthWestPositive
            exact ⟨⟨-1 / 2, 1 / 2⟩, by simp [coordinateDirections],
              leftNorthWestPositive, rightNorthWestPositive⟩
        · exact
            (not_four_selectedComplete_direction_products_nonpositive_of_angleGap
              selected leftMember rightMember angleGapPositive
              (le_of_not_gt eastProduct) (le_of_not_gt northProduct)
              (le_of_not_gt northEastProduct)
              (le_of_not_gt southEastProduct)).elim

/-- A displayed two-face cone with positive invariant angle gap closes the
executable complete tangent search. -/
theorem classifiedCompleteTangentDirection?_isSome_of_pair_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (forms : eventPayloadActiveOwnerForms selected = [left, right])
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    (classifiedCompleteTangentDirection? selected).isSome := by
  have leftMember : left ∈ eventPayloadActiveOwnerForms selected := by
    simp [forms]
  have rightMember : right ∈ eventPayloadActiveOwnerForms selected := by
    simp [forms]
  rcases exists_classifiedComplete_direction_pair_of_angleGap selected
      leftMember rightMember angleGapPositive with
    ⟨direction, directionMember, leftPositive, rightPositive⟩
  apply classifiedCompleteTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using And.intro leftPositive rightPositive

/-- A compatible nondegenerate pair closes the executable complete search as
soon as its cleared gradient dot product vanishes on the selected factor. -/
theorem classifiedCompleteTangentDirection?_isSome_of_pair
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (forms : eventPayloadActiveOwnerForms selected = [left, right])
    (leftNondegenerate : boundaryDiscriminant left ≠ 0)
    (rightNondegenerate : boundaryDiscriminant right ≠ 0)
    (dotDivides :
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial.toPolynomial ∣
        (selectedCompleteGradientDotPolynomial selected left right).toPolynomial) :
    (classifiedCompleteTangentDirection? selected).isSome := by
  have leftMember : left ∈ eventPayloadActiveOwnerForms selected := by
    simp [forms]
  have rightMember : right ∈ eventPayloadActiveOwnerForms selected := by
    simp [forms]
  rcases exists_classifiedComplete_direction_pair_of_gradientDot_dvd selected
      leftMember rightMember leftNondegenerate rightNondegenerate dotDivides with
    ⟨direction, directionMember, leftSlope, rightSlope⟩
  apply classifiedCompleteTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using And.intro leftSlope rightSlope

/-- For a parsed prefix, nondegeneracy is automatic; vanishing of the exact
Hermitian gradient-pairing constant is the only pair compatibility premise. -/
theorem classifiedCompleteTangentDirection?_isSome_of_parsed_pairingConstant_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {word : Prefix.Word}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (forms : eventPayloadActiveOwnerForms selected = [left, right])
    (constantZero : gradientPairingConstant left right = 0) :
    (classifiedCompleteTangentDirection? selected).isSome := by
  have leftMember : left ∈ eventPayloadActiveOwnerForms selected := by
    simp [forms]
  have rightMember : right ∈ eventPayloadActiveOwnerForms selected := by
    simp [forms]
  apply classifiedCompleteTangentDirection?_isSome_of_pair selected forms
  · exact selectedParsedCompleteActiveOwner_boundaryDiscriminant_ne selected
      leftMember
  · exact selectedParsedCompleteActiveOwner_boundaryDiscriminant_ne selected
      rightMember
  · exact selectedCompleteGradientDotPolynomial_dvd_of_pairingConstant_zero
      selected leftMember rightMember constantZero

/-- The selected canonical owner list inherits the exact completed-block pair
classification after the current decoder pullback. -/
theorem selectedCompletedSector_activeOwnerForms_pair_shape
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : SelectedEventPayload output) {left right : HermitianForm}
    (forms : eventPayloadActiveOwnerForms
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      |gradientPairingConstant left right| = normSq (determinant matrix) := by
  apply completedSectorInputAdvance_activeOwnerForms_pair_shape kind exponent
    first second selected.bit matrix history
    (eventPayloadCanonicalValue
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected.toIncrementalPayload)
  · exact eventPayloadCanonical_holds
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected
  · simpa only [eventPayloadActiveOwnerForms] using forms

/-- For an invertible completed parser state, the selected pair is either
orthogonal or has the strict rational angle gap used by the compass table. -/
theorem selectedCompletedSector_activeOwnerForms_pair_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : SelectedEventPayload output)
    (matrixDeterminantNonzero : determinant matrix ≠ 0)
    {left right : HermitianForm}
    (forms : eventPayloadActiveOwnerForms
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected = [left, right]) :
    gradientPairingConstant left right = 0 ∨
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2 := by
  apply completedSectorInputAdvance_activeOwnerForms_pair_angleGap kind
    exponent first second selected.bit matrix matrixDeterminantNonzero history
    (eventPayloadCanonicalValue
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected.toIncrementalPayload)
  · exact eventPayloadCanonical_holds
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected
  · simpa only [eventPayloadActiveOwnerForms] using forms

/-- The selected completed-block active cone contains at most the radial face
and the two weak faces of one sector corner. -/
theorem selectedCompletedSector_activeOwnerForms_length_le_three
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : SelectedEventPayload output) :
    (eventPayloadActiveOwnerForms
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected).length ≤ 3 := by
  apply completedSectorInputAdvance_activeOwnerForms_length_le_three kind
    exponent first second selected.bit matrix history
    (eventPayloadCanonicalValue
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected.toIncrementalPayload)
  exact eventPayloadCanonical_holds
    (state :=
      ⟨.sector kind exponent (.two first second), matrix, history⟩)
    selected

/-- The structural upper bound cannot be attained: a radial boundary and the
two coordinate faces of a normalized sector corner have incompatible squared
radii on every denominator-separated selected chart. -/
theorem selectedCompletedSector_activeOwnerForms_ne_triple
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {firstBit secondBit : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : SelectedEventPayload output)
    (matrixDeterminantNonzero : determinant matrix ≠ 0)
    {first second third : HermitianForm}
    (forms : eventPayloadActiveOwnerForms
      (state :=
        ⟨.sector kind exponent (.two firstBit secondBit), matrix, history⟩)
      selected = [first, second, third]) :
    False := by
  let state : RawParser.State :=
    ⟨.sector kind exponent (.two firstBit secondBit), matrix, history⟩
  let normalized := normalizedMatrix kind exponent (adjugate matrix)
  have shape :=
    completedSectorInputAdvance_activeOwnerForms_triple_exact kind exponent
      firstBit secondBit selected.bit matrix history
      (eventPayloadCanonicalValue (state := state) selected)
      (eventPayloadCanonical_holds (state := state) selected) (by
        simpa only [state, eventPayloadActiveOwnerForms] using forms)
  rcases shape with ⟨rfl, corner⟩
  have radialMember :
      HermitianForm.scale (normalizedRadialOwnerScale kind exponent)
          (normComparisonForm normalized (normalizedRadialRadius kind)) ∈
        eventPayloadActiveOwnerForms (state := state) selected := by
    rw [← radialOwnerForm_eq_scale_normalized]
    simpa only [state] using (show
      radialOwnerForm kind exponent (adjugate matrix) ∈
        eventPayloadActiveOwnerForms (state := state) selected by simp [forms])
  let decoderLower :=
    selectedCompleteDecoderDenominatorPositiveLowerBound
      (state := state) selected matrixDeterminantNonzero
  have normalizedLower : FTA.PositiveLowerBound.Certificate
      (clearedForm (affineNormForm normalized.c normalized.d)
        (selectedCompletePath selected))
      (selectedCompleteSlopeSigns selected).refined.interval := by
    have lowerRow := normalizedMatrix_lowerRow kind exponent (adjugate matrix)
    dsimp only [normalized]
    rw [lowerRow.1, lowerRow.2]
    exact decoderLower
  rcases corner with northEast | northWest | southWest | southEast
  · rcases northEast with ⟨_sector, rfl, rfl⟩
    apply selectedComplete_scaled_norm_real_imag_not_all_active selected
      normalized (normalizedRadialRadius kind) (1 / 2) (1 / 2)
      (normalizedRadialOwnerScale kind exponent) 1 1
    · exact normalizedRadialOwnerScale_ne kind exponent
    · norm_num
    · norm_num
    · exact normalizedCorner_radius_gap_ne kind
    · exact normalizedLower
    · exact radialMember
    · simp [normalized, forms, positiveRealOwner]
    · simp [normalized, forms, positiveImagOwner]
  · rcases northWest with ⟨_sector, rfl, rfl⟩
    apply selectedComplete_scaled_norm_real_imag_not_all_active selected
      normalized (normalizedRadialRadius kind) (-1 / 2) (1 / 2)
      (normalizedRadialOwnerScale kind exponent) (-1) 1
    · exact normalizedRadialOwnerScale_ne kind exponent
    · norm_num
    · norm_num
    · have gap := normalizedCorner_radius_gap_ne kind
      norm_num at gap ⊢
      exact gap
    · exact normalizedLower
    · exact radialMember
    · simp [normalized, forms, negativeRealOwner]
    · simp [normalized, forms, positiveImagOwner]
  · rcases southWest with ⟨_sector, rfl, rfl⟩
    apply selectedComplete_scaled_norm_real_imag_not_all_active selected
      normalized (normalizedRadialRadius kind) (-1 / 2) (-1 / 2)
      (normalizedRadialOwnerScale kind exponent) (-1) (-1)
    · exact normalizedRadialOwnerScale_ne kind exponent
    · norm_num
    · norm_num
    · have gap := normalizedCorner_radius_gap_ne kind
      norm_num at gap ⊢
      exact gap
    · exact normalizedLower
    · exact radialMember
    · simp [normalized, forms, negativeRealOwner]
    · simp [normalized, forms, negativeImagOwner]
  · rcases southEast with ⟨_sector, rfl, rfl⟩
    apply selectedComplete_scaled_norm_real_imag_not_all_active selected
      normalized (normalizedRadialRadius kind) (1 / 2) (-1 / 2)
      (normalizedRadialOwnerScale kind exponent) 1 (-1)
    · exact normalizedRadialOwnerScale_ne kind exponent
    · norm_num
    · norm_num
    · have gap := normalizedCorner_radius_gap_ne kind
      norm_num at gap ⊢
      exact gap
    · exact normalizedLower
    · exact radialMember
    · simp [normalized, forms, positiveRealOwner]
    · simp [normalized, forms, negativeImagOwner]

/-- Consequently every selected completed-block owner cone has length at most
two; the former structural upper bound of three is never attained. -/
theorem selectedCompletedSector_activeOwnerForms_length_le_two
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {firstBit secondBit : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : SelectedEventPayload output)
    (matrixDeterminantNonzero : determinant matrix ≠ 0) :
    (eventPayloadActiveOwnerForms
      (state :=
        ⟨.sector kind exponent (.two firstBit secondBit), matrix, history⟩)
      selected).length ≤ 2 := by
  let state : RawParser.State :=
    ⟨.sector kind exponent (.two firstBit secondBit), matrix, history⟩
  have lengthLeThree :=
    selectedCompletedSector_activeOwnerForms_length_le_three
      (kind := kind) (exponent := exponent) (first := firstBit)
      (second := secondBit) (matrix := matrix) (history := history) selected
  cases forms : eventPayloadActiveOwnerForms (state := state) selected with
  | nil => simp
  | cons first tail =>
      cases tail with
      | nil => simp
      | cons second rest =>
          cases rest with
          | nil => simp
          | cons third remaining =>
              cases remaining with
              | nil =>
                  exact (selectedCompletedSector_activeOwnerForms_ne_triple
                    (kind := kind) (exponent := exponent)
                    (firstBit := firstBit) (secondBit := secondBit)
                    (matrix := matrix) (history := history)
                    selected matrixDeterminantNonzero
                    (by simpa only [state] using forms)).elim
              | cons fourth remaining =>
                  simp [forms] at lengthLeThree
                  omega

/-- Every two-face cone selected immediately after a completed sector block
passes the executable compass search when the decoder and retained history
are invertible. -/
theorem classifiedCompleteTangentDirection?_isSome_of_completedSector_pair
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : SelectedEventPayload output)
    (matrixDeterminantNonzero : determinant matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible
      ⟨.sector kind exponent (.two first second), matrix, history⟩)
    {left right : HermitianForm}
    (forms : eventPayloadActiveOwnerForms
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected = [left, right]) :
    (classifiedCompleteTangentDirection?
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected).isSome := by
  let state : RawParser.State :=
    ⟨.sector kind exponent (.two first second), matrix, history⟩
  have leftMember : left ∈ eventPayloadActiveOwnerForms (state := state) selected := by
    dsimp only [state]
    simp [forms]
  have rightMember : right ∈ eventPayloadActiveOwnerForms (state := state) selected := by
    dsimp only [state]
    simp [forms]
  rcases selectedCompletedSector_activeOwnerForms_pair_angleGap selected
      matrixDeterminantNonzero forms with constantZero | angleGapPositive
  · apply classifiedCompleteTangentDirection?_isSome_of_pair
      (state := state) selected (by simpa only [state] using forms)
    · exact selectedCompleteActiveOwner_boundaryDiscriminant_ne
        (state := state) selected matrixDeterminantNonzero
          (by simpa only [state] using historyValid) leftMember
    · exact selectedCompleteActiveOwner_boundaryDiscriminant_ne
        (state := state) selected matrixDeterminantNonzero
          (by simpa only [state] using historyValid) rightMember
    · exact selectedCompleteGradientDotPolynomial_dvd_of_pairingConstant_zero
        (state := state) selected leftMember rightMember constantZero
  · exact classifiedCompleteTangentDirection?_isSome_of_pair_angleGap
      (state := state) selected (by simpa only [state] using forms)
        angleGapPositive

/-- The complete classified search succeeds vacuously for an empty cone. -/
theorem classifiedCompleteTangentDirection?_isSome_of_nil
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (forms : eventPayloadActiveOwnerForms selected = []) :
    (classifiedCompleteTangentDirection? selected).isSome := by
  apply classifiedCompleteTangentDirection?_isSome_of_exists selected
  refine ⟨⟨1, 0⟩, by simp [coordinateDirections], ?_⟩
  simp [forms]

/-- Nondegeneracy closes the complete executable search for a singleton
active cone, including a singleton inherited from parser history. -/
theorem classifiedCompleteTangentDirection?_isSome_of_singleton
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (forms : eventPayloadActiveOwnerForms selected = [form])
    (discriminantNonzero : boundaryDiscriminant form ≠ 0) :
    (classifiedCompleteTangentDirection? selected).isSome := by
  have formMember : form ∈ eventPayloadActiveOwnerForms selected := by
    simp [forms]
  rcases exists_classifiedComplete_axis_direction_single selected formMember
      discriminantNonzero with ⟨direction, directionMember, slope⟩
  apply classifiedCompleteTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using slope

/-- Every completed-block cone of length at most two is closed by the finite
search. -/
theorem classifiedCompleteTangentDirection?_isSome_of_completedSector_length_le_two
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : SelectedEventPayload output)
    (matrixDeterminantNonzero : determinant matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible
      ⟨.sector kind exponent (.two first second), matrix, history⟩)
    (lengthLe : (eventPayloadActiveOwnerForms
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected).length ≤ 2) :
    (classifiedCompleteTangentDirection?
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected).isSome := by
  let state : RawParser.State :=
    ⟨.sector kind exponent (.two first second), matrix, history⟩
  cases forms : eventPayloadActiveOwnerForms (state := state) selected with
  | nil =>
      exact classifiedCompleteTangentDirection?_isSome_of_nil
        (state := state) selected forms
  | cons form tail =>
      cases tail with
      | nil =>
          apply classifiedCompleteTangentDirection?_isSome_of_singleton
            (state := state) selected forms
          exact selectedCompleteActiveOwner_boundaryDiscriminant_ne
            (state := state) selected matrixDeterminantNonzero
              (by simpa only [state] using historyValid) (by simp [forms])
      | cons second rest =>
          cases rest with
          | nil =>
              exact
                classifiedCompleteTangentDirection?_isSome_of_completedSector_pair
                  selected matrixDeterminantNonzero historyValid
                    (by simpa only [state] using forms)
          | cons third remaining =>
              simp [state, forms] at lengthLe

/-- Unconditional completed-block tangent-search success: the incompatible
three-face corner has been eliminated, and all lists of length at most two
are handled by the finite compass search. -/
theorem classifiedCompleteTangentDirection?_isSome_of_completedSector
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : SelectedEventPayload output)
    (matrixDeterminantNonzero : determinant matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible
      ⟨.sector kind exponent (.two first second), matrix, history⟩) :
    (classifiedCompleteTangentDirection?
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      selected).isSome := by
  apply
    classifiedCompleteTangentDirection?_isSome_of_completedSector_length_le_two
      selected matrixDeterminantNonzero historyValid
  exact selectedCompletedSector_activeOwnerForms_length_le_two selected
    matrixDeterminantNonzero

/-- State-field form of completed-sector search totality.  This avoids
transporting controller states to a freshly written structure literal. -/
theorem classifiedCompleteTangentDirection?_isSome_of_completedPhase
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second))
    (matrixDeterminantNonzero : determinant state.matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible state) :
    (classifiedCompleteTangentDirection? selected).isSome := by
  rcases state with ⟨statePhase, matrix, history⟩
  dsimp only at phase
  subst statePhase
  exact classifiedCompleteTangentDirection?_isSome_of_completedSector
    selected matrixDeterminantNonzero historyValid

/-- Executable complete compass direction for any state whose phase field is
a completed two-bit sector. -/
def completedPhaseClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second))
    (matrixDeterminantNonzero : determinant state.matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible state) : QI :=
  (classifiedCompleteTangentDirection? selected).get
    (classifiedCompleteTangentDirection?_isSome_of_completedPhase selected
      phase matrixDeterminantNonzero historyValid)

theorem completedPhaseClassifiedTangentDirection_spec
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : state.phase = .sector kind exponent (.two first second))
    (matrixDeterminantNonzero : determinant state.matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible state) :
    classifiedCompleteTangentDirection? selected =
      some (completedPhaseClassifiedTangentDirection selected phase
        matrixDeterminantNonzero historyValid) :=
  Option.eq_some_of_isSome
    (classifiedCompleteTangentDirection?_isSome_of_completedPhase selected
      phase matrixDeterminantNonzero historyValid)

/-- Executable direction returned by the complete classified compass search
after a completed sector block.  The proof arguments certify totality of the
same finite search and are erased from the extracted program. -/
def completedSectorClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : SelectedEventPayload
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      output)
    (matrixDeterminantNonzero : determinant matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible
      ⟨.sector kind exponent (.two first second), matrix, history⟩) : QI :=
  (classifiedCompleteTangentDirection?
    (state :=
      ⟨.sector kind exponent (.two first second), matrix, history⟩)
    selected).get
      (classifiedCompleteTangentDirection?_isSome_of_completedSector
        selected matrixDeterminantNonzero historyValid)

/-- The total completed-sector direction is exactly the value returned by the
finite classified search. -/
theorem completedSectorClassifiedTangentDirection_spec
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    {matrix : Mat2 QI} {history : List RawParser.Constraint}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate matrix)}
    (selected : SelectedEventPayload
      (state :=
        ⟨.sector kind exponent (.two first second), matrix, history⟩)
      output)
    (matrixDeterminantNonzero : determinant matrix ≠ 0)
    (historyValid : HistoryMatricesInvertible
      ⟨.sector kind exponent (.two first second), matrix, history⟩) :
    classifiedCompleteTangentDirection?
        (state :=
          ⟨.sector kind exponent (.two first second), matrix, history⟩)
        selected =
      some (completedSectorClassifiedTangentDirection selected
        matrixDeterminantNonzero historyValid) := by
  exact Option.eq_some_of_isSome
    (classifiedCompleteTangentDirection?_isSome_of_completedSector selected
      matrixDeterminantNonzero historyValid)

/-- Every nondegenerate complete cone of length at most one is decided by the
finite search. -/
theorem classifiedCompleteTangentDirection?_isSome_of_length_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (nondegenerate : ∀ form ∈ eventPayloadActiveOwnerForms selected,
      boundaryDiscriminant form ≠ 0)
    (lengthLe : (eventPayloadActiveOwnerForms selected).length ≤ 1) :
    (classifiedCompleteTangentDirection? selected).isSome := by
  cases forms : eventPayloadActiveOwnerForms selected with
  | nil => exact classifiedCompleteTangentDirection?_isSome_of_nil selected forms
  | cons form tail =>
      cases tail with
      | nil =>
          apply classifiedCompleteTangentDirection?_isSome_of_singleton selected
            forms
          exact nondegenerate form (by simp [forms])
      | cons next rest => simp [forms] at lengthLe

/-- For an actual parsed prefix, invertibility of the decoder and every
historical constraint discharges the nondegeneracy premise automatically. -/
theorem classifiedCompleteTangentDirection?_isSome_of_parsed_length_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {word : Prefix.Word}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix)}
    (selected : SelectedEventPayload output)
    (lengthLe : (eventPayloadActiveOwnerForms selected).length ≤ 1) :
    (classifiedCompleteTangentDirection? selected).isSome := by
  apply classifiedCompleteTangentDirection?_isSome_of_length_le_one selected
  · intro form member
    exact selectedParsedCompleteActiveOwner_boundaryDiscriminant_ne selected
      member
  · exact lengthLe

/-- Every complete-child strict atom retains its canonical event sign after
the ordinary final narrowing used by event extraction. -/
theorem selectedCompleteStrictAtCompleteSlopeInputCellApproximation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon) :
    ∀ form ∈ eventPayloadStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected.toIncrementalPayload form *
        form.eval ((selectedCompletePath selected).value
          ((selectedCompleteSlopeInputCell selected).clearedApproximation
            epsilon epsilonPositive).refined.interval.lower) := by
  intro form member
  let path := selectedCompletePath selected
  let originalSigns := selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent
  let cell := selectedCompleteSlopeInputCell selected
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let t := approximation.refined.interval.lower
  have completeLower :
      (selectedCompleteSlopeSigns selected).refined.interval.lower ≤ t :=
    (selectedCompleteSlopeInputSigns selected).refines.1.trans
      approximation.refines.1
  have completeUpper : t ≤
      (selectedCompleteSlopeSigns selected).refined.interval.upper :=
    (approximation.refined.proper.le.trans approximation.refines.2).trans
      (selectedCompleteSlopeInputSigns selected).refines.2
  have lower : originalSigns.refined.interval.lower ≤ t :=
    (selectedCompleteSlopeSigns_refines_inputCell selected).1.trans
      completeLower
  have upper : t ≤ originalSigns.refined.interval.upper :=
    completeUpper.trans
      (selectedCompleteSlopeSigns_refines_inputCell selected).2
  have canonicalNonzero := strictPriorForms_value_ne
    (inputAdvanceFormula state selected.bit)
    (eventPayloadCanonicalValue selected.toIncrementalPayload) member
  change canonicalEventValue
    selected.candidate.inputCell.branch.factor.input
    (clearedForm form selected.candidate.sourceEvent.partition.entry.chart.path)
    originalSigns.refined.interval.lower ≠ 0 at canonicalNonzero
  have polynomialSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent originalSigns
      (selectedCompleteStrictPolynomial_mem selected member)
      (by simpa only [eventPayloadCanonicalValue] using canonicalNonzero)
      lower upper
  have pathDenominator := cell.path_denominator_ne_on_cell
    approximation.refines.1
    (approximation.refined.proper.le.trans approximation.refines.2)
  have denominatorPositive := eval_denominatorNorm_pos path t pathDenominator
  change 0 < eventPayloadCanonicalValue selected.toIncrementalPayload form *
    (clearedForm form path).eval t at polynomialSign
  rw [eval_clearedForm form path t pathDenominator] at polynomialSign
  have rearranged : 0 < (denominatorNorm path).eval t *
      (eventPayloadCanonicalValue selected.toIncrementalPayload form *
        form.eval ((selectedCompletePath selected).value t)) := by
    dsimp only [path, cell, approximation, t] at polynomialSign ⊢
    convert polynomialSign using 1
    all_goals ring
  rcases mul_pos_iff.mp rearranged with positive | negative
  · exact positive.2
  · exact (not_lt_of_ge denominatorPositive.le negative.1).elim

/-- Every complete active face is explicitly small at the ordinary final
narrowing of the complete slope-classified input cell. -/
theorem selectedCompleteActiveAtCompleteSlopeInputCellApproximation_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {epsilon : ℚ}
    (epsilonPositive : 0 < epsilon) {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    |form.eval ((selectedCompletePath selected).value
      ((selectedCompleteSlopeInputCell selected).clearedApproximation epsilon
        epsilonPositive).refined.interval.lower)| ≤
      approximationBound (clearedForm form (selectedCompletePath selected))
          (selectedCompleteSlopeClassification selected).branch.factor.polynomial
          (selectedCompleteSlopeInputSigns selected).refined epsilon /
        (RelevantCurveEvent.ownerDenominatorCertificate
          selected.candidate.sourceEvent.event).bound := by
  let cell := selectedCompleteSlopeInputCell selected
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let t := approximation.refined.interval.lower
  let denominator := RelevantCurveEvent.ownerDenominatorCertificate
    selected.candidate.sourceEvent.event
  have small := approximation.multipleSmall
    (selectedCompleteSlopeActivePolynomial_dvd selected member)
    epsilonPositive.le
  have pathDenominator := cell.path_denominator_ne_on_cell
    approximation.refines.1
    (approximation.refined.proper.le.trans approximation.refines.2)
  have denominatorLower : denominator.bound ≤
      (denominatorNorm (selectedCompletePath selected)).eval t := by
    apply denominator.lower
    · exact cell.signRefines.1.trans approximation.refines.1
    · exact (approximation.refined.proper.le.trans
        approximation.refines.2).trans cell.signRefines.2
  apply (le_div_iff₀ denominator.positive).2
  calc
    |form.eval ((selectedCompletePath selected).value t)| * denominator.bound =
        denominator.bound * |form.eval ((selectedCompletePath selected).value t)| := by
      ring
    _ ≤ (denominatorNorm (selectedCompletePath selected)).eval t *
          |form.eval ((selectedCompletePath selected).value t)| :=
      mul_le_mul_of_nonneg_right denominatorLower (abs_nonneg _)
    _ = |(clearedForm form (selectedCompletePath selected)).eval t| := by
      rw [eval_clearedForm form (selectedCompletePath selected) t pathDenominator,
        abs_mul, abs_of_pos (eval_denominatorNorm_pos
          (selectedCompletePath selected) t pathDenominator)]
    _ ≤ approximationBound (clearedForm form (selectedCompletePath selected))
          (selectedCompleteSlopeClassification selected).branch.factor.polynomial
          (selectedCompleteSlopeInputSigns selected).refined epsilon := by
      exact small

end CCLCompleteEventTangentSigns
end FTA
