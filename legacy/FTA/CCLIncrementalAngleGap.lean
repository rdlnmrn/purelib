import FTA.CCLCompleteEventTangentSigns

/-!
# Incremental tangent search from a positive angle gap

The complete-child tangent classifier already proves that two active faces
with positive invariant angle gap admit a common direction in the finite
eight-point compass.  Incremental parsing classifies a smaller, history-free
list of slope polynomials, so it needs the same obstruction argument on its
own final count-one descendant.  This module supplies that reusable pair
theorem without changing the executable classifier.
-/

namespace FTA
namespace CCLIncrementalAngleGap

open CCL CCL.GaussianRat
open FTA.CCLBranchController
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLCompleteEventTangentSigns
open FTA.CCLCountOneClassification
open FTA.CCLEventTangentSigns
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLIntersectionSharedFactors
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLPathIntersection
open FTA.CCLPathTangent
open FTA.CCLPositiveEventSemantics
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

/-- The selected source chart supplies a positive lower bound for the pulled-
back decoder denominator on the incremental slope-refined event interval. -/
def selectedSlopeDecoderDenominatorPositiveLowerBound
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (stateDeterminant : determinant state.matrix ≠ 0) :
    FTA.PositiveLowerBound.Certificate
      (clearedForm
        (affineNormForm (adjugate state.matrix).c (adjugate state.matrix).d)
        (selectedPath selected))
      (selectedSlopeSigns selected).refined.interval := by
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

/-- The selected event's denominator certificate remains valid after the
incremental slope-condition refinement. -/
def selectedSlopeDenominatorPositiveLowerBound
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    FTA.PositiveLowerBound.Certificate
      (denominatorNorm (selectedPath selected))
      (selectedSlopeSigns selected).refined.interval := by
  let denominator := RelevantCurveEvent.ownerDenominatorCertificate
    selected.candidate.sourceEvent.event
  exact
    { bound := denominator.bound ^ 2
      positive := sq_pos_of_pos denominator.positive
      lower := by
        intro t lower upper
        have rootLower := selected.candidate.inputCell.signRefines.1.trans
          ((selectedSlopeSigns_refines_inputCell selected).1.trans lower)
        have rootUpper :=
          (upper.trans (selectedSlopeSigns_refines_inputCell selected).2).trans
            selected.candidate.inputCell.signRefines.2
        have denominatorLower : denominator.bound ≤
            (denominatorNorm (selectedPath selected)).eval t :=
          denominator.lower rootLower rootUpper
        simpa only [pow_two] using
          mul_self_le_mul_self denominator.positive.le denominatorLower }

/-- Four denominator factors turn a positive invariant angle gap into the
strictly positive polynomial obstruction used by the compass identity. -/
def selectedSlopeAngleGapPositiveLowerBound
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (left right : HermitianForm)
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    FTA.PositiveLowerBound.Certificate
      (DensePolynomial.scale
        (boundaryDiscriminant left * boundaryDiscriminant right -
          2 * gradientPairingConstant left right ^ 2)
        ((denominatorNorm (selectedPath selected) *
            denominatorNorm (selectedPath selected)) *
          (denominatorNorm (selectedPath selected) *
            denominatorNorm (selectedPath selected))))
      (selectedSlopeSigns selected).refined.interval := by
  let denominatorCertificate :=
    selectedSlopeDenominatorPositiveLowerBound selected
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

/-- A count-one incremental event cannot lie on a normalized radial boundary
and both coordinate sides of a corner whose squared radius is different. -/
theorem selectedSlope_scaled_norm_real_imag_not_all_active
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (matrix : Mat2 QI)
    (radius realThreshold imagThreshold : ℚ)
    (radialScale realScale imagScale : ℚ)
    (radialScaleNonzero : radialScale ≠ 0)
    (realScaleNonzero : realScale ≠ 0)
    (imagScaleNonzero : imagScale ≠ 0)
    (radiusGapNonzero :
      realThreshold ^ 2 + imagThreshold ^ 2 - radius ≠ 0)
    (denominatorLower : FTA.PositiveLowerBound.Certificate
      (clearedForm (affineNormForm matrix.c matrix.d)
        (selectedPath selected))
      (selectedSlopeSigns selected).refined.interval)
    (radialMember : HermitianForm.scale radialScale
        (normComparisonForm matrix radius) ∈
      eventPayloadIncrementalActiveOwnerForms selected)
    (realMember : HermitianForm.scale realScale
        (realComparisonForm matrix realThreshold) ∈
      eventPayloadIncrementalActiveOwnerForms selected)
    (imagMember : HermitianForm.scale imagScale
        (imagComparisonForm matrix imagThreshold) ∈
      eventPayloadIncrementalActiveOwnerForms selected) :
    False := by
  let classification := selectedSlopeClassification selected
  let path := selectedPath selected
  let factor := classification.branch.factor.polynomial.toPolynomial
  let normPolynomial :=
    (clearedForm (normComparisonForm matrix radius) path).toPolynomial
  let realPolynomial :=
    (clearedForm (realComparisonForm matrix realThreshold) path).toPolynomial
  let imagPolynomial :=
    (clearedForm (imagComparisonForm matrix imagThreshold) path).toPolynomial
  have radialScaledDivides :=
    selectedSlopeActivePolynomial_dvd selected radialMember
  have realScaledDivides :=
    selectedSlopeActivePolynomial_dvd selected realMember
  have imagScaledDivides :=
    selectedSlopeActivePolynomial_dvd selected imagMember
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
      (selectedSlopeSigns selected).refined.interval :=
    FTA.PositiveLowerBound.Certificate.mul denominatorLower denominatorLower
  apply CountOneInterval.no_positiveLowerBound_of_dvd
    classification.branch.factor.input
    (selectedSlopeSigns selected).refined
    denominatorSquareDivides
  simpa only [path] using denominatorProductLower

/-- A positive invariant angle gap rules out nonpositive products in all four
antipodal compass pairs on the incremental slope-classified event cell. -/
theorem not_four_selectedSlope_direction_products_nonpositive_of_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (rightMember : right ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2)
    (eastNonpositive :
      selectedSlopeValue selected left ⟨1, 0⟩ *
        selectedSlopeValue selected right ⟨1, 0⟩ ≤ 0)
    (northNonpositive :
      selectedSlopeValue selected left ⟨0, 1⟩ *
        selectedSlopeValue selected right ⟨0, 1⟩ ≤ 0)
    (northEastNonpositive :
      selectedSlopeValue selected left ⟨1 / 2, 1 / 2⟩ *
        selectedSlopeValue selected right ⟨1 / 2, 1 / 2⟩ ≤ 0)
    (southEastNonpositive :
      selectedSlopeValue selected left ⟨1 / 2, -1 / 2⟩ *
        selectedSlopeValue selected right ⟨1 / 2, -1 / 2⟩ ≤ 0) :
    False := by
  let classification := selectedSlopeClassification selected
  let signs := selectedSlopeSigns selected
  let path := selectedPath selected
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
  have leftEastMember : leftEast ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightEastMember : rightEast ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have leftNorthMember : leftNorth ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightNorthMember : rightNorth ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have leftNorthEastMember : leftNorthEast ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightNorthEastMember : rightNorthEast ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have leftSouthEastMember : leftSouthEast ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      (by simp [coordinateDirections]) leftMember
  have rightSouthEastMember : rightSouthEast ∈ selectedSlopeConditions selected :=
    clearedDirectionalSlope_mem_selectedSlopeConditions selected
      (by simp [coordinateDirections]) rightMember
  have basePositive : ∀ t : ℚ,
      signs.refined.interval.lower ≤ t →
      t ≤ signs.refined.interval.upper → 0 < base.eval t := by
    intro t lower upper
    let denominator := RelevantCurveEvent.ownerDenominatorCertificate
      selected.candidate.sourceEvent.event
    have rootLower := selected.candidate.inputCell.signRefines.1.trans
      ((selectedSlopeSigns_refines_inputCell selected).1.trans lower)
    have rootUpper :=
      (upper.trans (selectedSlopeSigns_refines_inputCell selected).2).trans
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
      selectedSlopeAngleGapPositiveLowerBound selected left right
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
          selectedSlopeActivePolynomial_dvd selected leftMember)
      (by
        simpa only [classification, path] using
          selectedSlopeActivePolynomial_dvd selected rightMember)
    simpa only [base, gap, leftEast, rightEast, leftNorth, rightNorth,
      leftNorthEast, rightNorthEast, leftSouthEast, rightSouthEast] using
        identity
  exact
    (CCLCompleteEventTangentSigns.ConditionRelations.not_four_direction_products_nonpositive
      classification.branch.relations classification.parent signs
      leftEastMember rightEastMember leftNorthMember rightNorthMember
      leftNorthEastMember rightNorthEastMember leftSouthEastMember
      rightSouthEastMember 4 16 (by norm_num) (by norm_num) basePositive
      baseLower obstructionDivides
      (by simpa [selectedSlopeValue, classification, signs, path,
        leftEast, rightEast] using eastNonpositive)
      (by simpa [selectedSlopeValue, classification, signs, path,
        leftNorth, rightNorth] using northNonpositive)
      (by simpa [selectedSlopeValue, classification, signs, path,
        leftNorthEast, rightNorthEast] using northEastNonpositive)
      (by simpa [selectedSlopeValue, classification, signs, path,
        leftSouthEast, rightSouthEast] using southEastNonpositive)).elim

/-- A positive invariant angle gap forces one of the eight incremental
classified compass directions to point strictly into both active faces. -/
theorem exists_classified_direction_pair_of_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (leftMember : left ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (rightMember : right ∈ eventPayloadIncrementalActiveOwnerForms selected)
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    ∃ direction ∈ coordinateDirections,
      0 < selectedSlopeValue selected left direction ∧
        0 < selectedSlopeValue selected right direction := by
  have negNorthEast : (-⟨1 / 2, 1 / 2⟩ : QI) =
      ⟨-1 / 2, -1 / 2⟩ := by
    ext <;> norm_num
  have negSouthEast : (-⟨1 / 2, -1 / 2⟩ : QI) =
      ⟨-1 / 2, 1 / 2⟩ := by
    ext <;> norm_num
  by_cases eastProduct : 0 <
      selectedSlopeValue selected left ⟨1, 0⟩ *
        selectedSlopeValue selected right ⟨1, 0⟩
  · rcases mul_pos_iff.mp eastProduct with positive | negative
    · exact ⟨⟨1, 0⟩, by simp [coordinateDirections], positive⟩
    · have leftWestPositive :=
        selectedSlopeValue_opposite_pos_of_neg selected leftMember
          (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp) negative.1
      have rightWestPositive :=
        selectedSlopeValue_opposite_pos_of_neg selected rightMember
          (direction := ⟨1, 0⟩) (opposite := ⟨-1, 0⟩)
          (by simp [coordinateDirections]) (by simp [coordinateDirections])
          (by simp) negative.2
      exact ⟨⟨-1, 0⟩, by simp [coordinateDirections], leftWestPositive,
        rightWestPositive⟩
  · by_cases northProduct : 0 <
        selectedSlopeValue selected left ⟨0, 1⟩ *
          selectedSlopeValue selected right ⟨0, 1⟩
    · rcases mul_pos_iff.mp northProduct with positive | negative
      · exact ⟨⟨0, 1⟩, by simp [coordinateDirections], positive⟩
      · have leftSouthPositive :=
          selectedSlopeValue_opposite_pos_of_neg selected leftMember
            (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
            (by simp [coordinateDirections]) (by simp [coordinateDirections])
            (by simp) negative.1
        have rightSouthPositive :=
          selectedSlopeValue_opposite_pos_of_neg selected rightMember
            (direction := ⟨0, 1⟩) (opposite := ⟨0, -1⟩)
            (by simp [coordinateDirections]) (by simp [coordinateDirections])
            (by simp) negative.2
        exact ⟨⟨0, -1⟩, by simp [coordinateDirections], leftSouthPositive,
          rightSouthPositive⟩
    · by_cases northEastProduct : 0 <
          selectedSlopeValue selected left ⟨1 / 2, 1 / 2⟩ *
            selectedSlopeValue selected right ⟨1 / 2, 1 / 2⟩
      · rcases mul_pos_iff.mp northEastProduct with positive | negative
        · exact ⟨⟨1 / 2, 1 / 2⟩, by simp [coordinateDirections],
            positive⟩
        · have leftSouthWestPositive :=
            selectedSlopeValue_opposite_pos_of_neg selected leftMember
              (direction := ⟨1 / 2, 1 / 2⟩)
              (opposite := (-⟨1 / 2, 1 / 2⟩ : QI))
              (by simp [coordinateDirections])
              (by rw [negNorthEast]; simp [coordinateDirections])
              (toPolynomial_clearedDirectionalSlope_neg left
                (selectedPath selected) ⟨1 / 2, 1 / 2⟩) negative.1
          have rightSouthWestPositive :=
            selectedSlopeValue_opposite_pos_of_neg selected rightMember
              (direction := ⟨1 / 2, 1 / 2⟩)
              (opposite := (-⟨1 / 2, 1 / 2⟩ : QI))
              (by simp [coordinateDirections])
              (by rw [negNorthEast]; simp [coordinateDirections])
              (toPolynomial_clearedDirectionalSlope_neg right
                (selectedPath selected) ⟨1 / 2, 1 / 2⟩) negative.2
          rw [negNorthEast] at leftSouthWestPositive rightSouthWestPositive
          exact ⟨⟨-1 / 2, -1 / 2⟩, by simp [coordinateDirections],
            leftSouthWestPositive, rightSouthWestPositive⟩
      · by_cases southEastProduct : 0 <
            selectedSlopeValue selected left ⟨1 / 2, -1 / 2⟩ *
              selectedSlopeValue selected right ⟨1 / 2, -1 / 2⟩
        · rcases mul_pos_iff.mp southEastProduct with positive | negative
          · exact ⟨⟨1 / 2, -1 / 2⟩, by simp [coordinateDirections],
              positive⟩
          · have leftNorthWestPositive :=
              selectedSlopeValue_opposite_pos_of_neg selected leftMember
                (direction := ⟨1 / 2, -1 / 2⟩)
                (opposite := (-⟨1 / 2, -1 / 2⟩ : QI))
                (by simp [coordinateDirections])
                (by rw [negSouthEast]; simp [coordinateDirections])
                (toPolynomial_clearedDirectionalSlope_neg left
                  (selectedPath selected) ⟨1 / 2, -1 / 2⟩) negative.1
            have rightNorthWestPositive :=
              selectedSlopeValue_opposite_pos_of_neg selected rightMember
                (direction := ⟨1 / 2, -1 / 2⟩)
                (opposite := (-⟨1 / 2, -1 / 2⟩ : QI))
                (by simp [coordinateDirections])
                (by rw [negSouthEast]; simp [coordinateDirections])
                (toPolynomial_clearedDirectionalSlope_neg right
                  (selectedPath selected) ⟨1 / 2, -1 / 2⟩) negative.2
            rw [negSouthEast] at leftNorthWestPositive rightNorthWestPositive
            exact ⟨⟨-1 / 2, 1 / 2⟩, by simp [coordinateDirections],
              leftNorthWestPositive, rightNorthWestPositive⟩
        · exact
            (not_four_selectedSlope_direction_products_nonpositive_of_angleGap
              selected leftMember rightMember angleGapPositive
              (le_of_not_gt eastProduct) (le_of_not_gt northProduct)
              (le_of_not_gt northEastProduct)
              (le_of_not_gt southEastProduct)).elim

/-- A displayed incremental two-face cone with positive invariant angle gap
therefore closes the executable tangent search. -/
theorem classifiedTangentDirection?_isSome_of_pair_angleGap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {left right : HermitianForm}
    (forms : eventPayloadIncrementalActiveOwnerForms selected = [left, right])
    (angleGapPositive :
      0 < boundaryDiscriminant left * boundaryDiscriminant right -
        2 * gradientPairingConstant left right ^ 2) :
    (classifiedTangentDirection? selected).isSome := by
  have leftMember : left ∈ eventPayloadIncrementalActiveOwnerForms selected := by
    simp [forms]
  have rightMember : right ∈ eventPayloadIncrementalActiveOwnerForms selected := by
    simp [forms]
  rcases exists_classified_direction_pair_of_angleGap selected leftMember
      rightMember angleGapPositive with
    ⟨direction, directionMember, leftPositive, rightPositive⟩
  apply classifiedTangentDirection?_isSome_of_exists selected
  refine ⟨direction, directionMember, ?_⟩
  simpa [forms] using And.intro leftPositive rightPositive

end CCLIncrementalAngleGap
end FTA
