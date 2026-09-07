import FTA.CCLActiveBoundaryEvent
import FTA.CCLFormulaClosure
import FTA.CCLSectorBoundaryConvergence

/-!
# Closed sector data at a residual active boundary

Persistent active samples approach the same isolated algebraic event as the
owner-independent Sturm approximation.  Consequently the event's canonical
sign table satisfies the closed current radial/sector predicate.  This is the
finite bridge that selects a compatible successor sector before the rational
residual cone is entered.
-/

namespace FTA
namespace CCLActiveMetricTrack

open CCL CCL.GaussianRat
open CCL.EncoderParserBridge
open FTA.AxisSafeCuts
open FTA.CCLActiveBoxCoupling
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchPlan
open FTA.CCLCanonicalEvent
open FTA.CCLCompleteEventTangentSigns
open FTA.CCLCompleteOwnerCompatibility
open FTA.CCLFormulaClosure
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLFormulaStability
open FTA.CCLGeometry
open FTA.CCLMultiOwnerGrid
open FTA.CCLNextBitFormula
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventConvergence
open FTA.CCLSectorBoundaryConvergence
open FTA.CCLSectorInteriorCone
open FTA.CCLSectorInteriorSelection
open FTA.ConstructiveTrack
open FTA.LocalExtraction
open FTA.RootTrackSeparation

/-- The retained source chart supplies a uniform positive lower bound for
the current inverse-decoder denominator on the boundary event cell.  This is
the unfinished-sector analogue of the completed-event decoder certificate. -/
def ActivePositiveGuardData.boundaryDecoderDenominatorPositiveLowerBound
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    FTA.PositiveLowerBound.Certificate
      (clearedForm
        (affineNormForm
          (adjugate (RawParser.parse current.core.word).matrix).c
          (adjugate (RawParser.parse current.core.word).matrix).d)
        data.boundaryPathCylinder.path)
      data.boundaryOrientedInputCell.parent.interval := by
  let state := RawParser.parse current.core.word
  let source := data.sourceCell.partition.entry.source
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have sourceDeterminantPositive : 0 < normSq (determinant source.matrix) :=
    normSq_pos (data.source_determinant_ne stateDeterminant)
  exact
    { bound := normSq (determinant source.matrix) ^ 2
      positive := sq_pos_of_pos sourceDeterminantPositive
      lower := by
        intro parameter _lower _upper
        have lowerRow := CCLBranchPlan.inputPlan_lowerRow state
          data.source_mem_inputPlan
        have sourceLower := sourceChart_clearedLowerRow_eval_ge source
          data.sourceCell.partition.entry.chart parameter
        rw [lowerRow.1, lowerRow.2] at sourceLower
        have squaredLower := mul_self_le_mul_self
          sourceDeterminantPositive.le sourceLower
        simpa only [source, state, data.boundaryPathCylinder_path,
          pow_two] using squaredLower }

/-- The same decoder lower bound stated directly on the path indexed by the
selected boundary candidate.  Keeping this dependent path explicit avoids
rewriting the event index in later canonical-divisibility arguments. -/
def ActivePositiveGuardData.boundaryCandidateDecoderPositiveLowerBound
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    FTA.PositiveLowerBound.Certificate
      (clearedForm
        (affineNormForm
          (adjugate (RawParser.parse current.core.word).matrix).c
          (adjugate (RawParser.parse current.core.word).matrix).d)
        data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path)
      data.boundaryOrientedInputCell.parent.interval := by
  let state := RawParser.parse current.core.word
  let source := data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.source
  have sourceMember : source ∈ inputPlan state := by
    dsimp only [source, state]
    rw [data.boundaryCandidate_sourceEvent]
    exact data.source_mem_inputPlan
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have sourceDeterminantPositive : 0 < normSq (determinant source.matrix) :=
    normSq_pos (CCLBranchPlan.inputPlan_determinant_ne state sourceMember
      stateDeterminant)
  exact
    { bound := normSq (determinant source.matrix) ^ 2
      positive := sq_pos_of_pos sourceDeterminantPositive
      lower := by
        intro parameter _lower _upper
        have lowerRow := CCLBranchPlan.inputPlan_lowerRow state sourceMember
        have sourceLower := sourceChart_clearedLowerRow_eval_ge source
          data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart
            parameter
        rw [lowerRow.1, lowerRow.2] at sourceLower
        have squaredLower := mul_self_le_mul_self
          sourceDeterminantPositive.le sourceLower
        simpa only [source, state, pow_two] using squaredLower }

private theorem ActivePositiveGuardData.boundaryCandidateEventFactor_not_dvd_decoder
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    ¬data.boundaryOrientedInputCell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
        (affineNormForm
          (adjugate (RawParser.parse current.core.word).matrix).c
          (adjugate (RawParser.parse current.core.word).matrix).d)
        data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path
      ).toPolynomial := by
  intro divides
  exact FTA.RootCountDivisibility.CountOneInterval.no_positiveLowerBound_of_dvd
    data.boundaryOrientedInputCell.branch.factor.input
    data.boundaryOrientedInputCell.parent divides
    data.boundaryCandidateDecoderPositiveLowerBound

private theorem ActivePositiveGuardData.boundaryCandidateEventFactor_not_dvd_decoderSq
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    ¬data.boundaryOrientedInputCell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
          (affineNormForm
            (adjugate (RawParser.parse current.core.word).matrix).c
            (adjugate (RawParser.parse current.core.word).matrix).d)
          data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path *
        clearedForm
          (affineNormForm
            (adjugate (RawParser.parse current.core.word).matrix).c
            (adjugate (RawParser.parse current.core.word).matrix).d)
          data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path
      ).toPolynomial := by
  intro divides
  let lower := data.boundaryCandidateDecoderPositiveLowerBound
  exact FTA.RootCountDivisibility.CountOneInterval.no_positiveLowerBound_of_dvd
    data.boundaryOrientedInputCell.branch.factor.input
    data.boundaryOrientedInputCell.parent divides
    (FTA.PositiveLowerBound.Certificate.mul lower lower)

private theorem inputEventCanonicalZero_dvd_clearedForm
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (form : HermitianForm)
    (member : clearedForm form path ∈ inputEventPolynomials state path)
    (zero : inputEventCanonicalValue cell form = 0) :
    cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form path).toPolynomial := by
  apply ConditionRelations.dvd_of_canonicalEventValue_eq_zero
    cell.branch.relations cell.parent
    (cell.branch.computeEventSigns cell.parent) member
  simpa only [inputEventCanonicalValue] using zero

private theorem ActivePositiveGuardData.boundaryEventFactor_not_dvd_decoder
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    ¬data.boundaryOrientedInputCell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
        (affineNormForm
          (adjugate (RawParser.parse current.core.word).matrix).c
          (adjugate (RawParser.parse current.core.word).matrix).d)
        data.boundaryPathCylinder.path).toPolynomial := by
  intro divides
  exact FTA.RootCountDivisibility.CountOneInterval.no_positiveLowerBound_of_dvd
    data.boundaryOrientedInputCell.branch.factor.input
    data.boundaryOrientedInputCell.parent divides
    data.boundaryDecoderDenominatorPositiveLowerBound

private theorem ActivePositiveGuardData.boundaryEventFactor_not_dvd_decoderSq
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current) :
    ¬data.boundaryOrientedInputCell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
          (affineNormForm
            (adjugate (RawParser.parse current.core.word).matrix).c
            (adjugate (RawParser.parse current.core.word).matrix).d)
          data.boundaryPathCylinder.path *
        clearedForm
          (affineNormForm
            (adjugate (RawParser.parse current.core.word).matrix).c
            (adjugate (RawParser.parse current.core.word).matrix).d)
          data.boundaryPathCylinder.path).toPolynomial := by
  intro divides
  let lower := data.boundaryDecoderDenominatorPositiveLowerBound
  exact FTA.RootCountDivisibility.CountOneInterval.no_positiveLowerBound_of_dvd
    data.boundaryOrientedInputCell.branch.factor.input
    data.boundaryOrientedInputCell.parent divides
    (FTA.PositiveLowerBound.Certificate.mul lower lower)

private theorem ActivePositiveGuardData.inputEventPolynomial_of_boundaryPath
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (form : HermitianForm)
    (member : clearedForm form data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path) :
    clearedForm form
        data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path := by
  rw [data.boundaryCandidate_sourceEvent]
  simpa only [data.boundaryPathCylinder_path,
    ActivePositiveGuardData.sourceEvent] using member

private theorem inputEvent_normComparison_not_both_canonicalZero
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (matrix : Mat2 QI)
    (leftRadius rightRadius : ℚ) (radiiDistinct : leftRadius ≠ rightRadius)
    (leftMember : clearedForm (normComparisonForm matrix leftRadius) path ∈
      inputEventPolynomials state path)
    (rightMember : clearedForm (normComparisonForm matrix rightRadius) path ∈
      inputEventPolynomials state path)
    (denominatorNotDivides :
      ¬cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial) :
    ¬(inputEventCanonicalValue cell
          (normComparisonForm matrix leftRadius) = 0 ∧
        inputEventCanonicalValue cell
          (normComparisonForm matrix rightRadius) = 0) := by
  rintro ⟨leftZero, rightZero⟩
  have leftDivides := inputEventCanonicalZero_dvd_clearedForm cell
    (normComparisonForm matrix leftRadius) leftMember leftZero
  have rightDivides := inputEventCanonicalZero_dvd_clearedForm cell
    (normComparisonForm matrix rightRadius) rightMember rightZero
  have difference := dvd_sub leftDivides rightDivides
  have scaled : cell.branch.factor.polynomial.toPolynomial ∣
      Polynomial.C (rightRadius - leftRadius) *
        (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial := by
    rw [toPolynomial_clearedForm_normComparison,
      toPolynomial_clearedForm_normComparison] at difference
    convert difference using 1
    simp only [Polynomial.C_sub]
    ring
  apply denominatorNotDivides
  apply dvd_of_dvd_C_mul (rightRadius - leftRadius)
  · exact sub_ne_zero.mpr (Ne.symm radiiDistinct)
  · exact scaled

private theorem inputEvent_realComparison_not_both_canonicalZero
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (matrix : Mat2 QI)
    (leftThreshold rightThreshold : ℚ)
    (thresholdsDistinct : leftThreshold ≠ rightThreshold)
    (leftMember : clearedForm (realComparisonForm matrix leftThreshold) path ∈
      inputEventPolynomials state path)
    (rightMember : clearedForm (realComparisonForm matrix rightThreshold) path ∈
      inputEventPolynomials state path)
    (denominatorNotDivides :
      ¬cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial) :
    ¬(inputEventCanonicalValue cell
          (realComparisonForm matrix leftThreshold) = 0 ∧
        inputEventCanonicalValue cell
          (realComparisonForm matrix rightThreshold) = 0) := by
  rintro ⟨leftZero, rightZero⟩
  have leftDivides := inputEventCanonicalZero_dvd_clearedForm cell
    (realComparisonForm matrix leftThreshold) leftMember leftZero
  have rightDivides := inputEventCanonicalZero_dvd_clearedForm cell
    (realComparisonForm matrix rightThreshold) rightMember rightZero
  have difference := dvd_sub leftDivides rightDivides
  have scaled : cell.branch.factor.polynomial.toPolynomial ∣
      Polynomial.C (rightThreshold - leftThreshold) *
        (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial := by
    rw [toPolynomial_clearedForm_realComparison,
      toPolynomial_clearedForm_realComparison] at difference
    convert difference using 1
    simp only [Polynomial.C_sub]
    ring
  apply denominatorNotDivides
  apply dvd_of_dvd_C_mul (rightThreshold - leftThreshold)
  · exact sub_ne_zero.mpr (Ne.symm thresholdsDistinct)
  · exact scaled

private theorem inputEvent_imagComparison_not_both_canonicalZero
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (matrix : Mat2 QI)
    (lowerThreshold upperThreshold : ℚ)
    (thresholdsDistinct : lowerThreshold ≠ upperThreshold)
    (lowerMember : clearedForm (imagComparisonForm matrix lowerThreshold) path ∈
      inputEventPolynomials state path)
    (upperMember : clearedForm (imagComparisonForm matrix upperThreshold) path ∈
      inputEventPolynomials state path)
    (denominatorNotDivides :
      ¬cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial) :
    ¬(inputEventCanonicalValue cell
          (imagComparisonForm matrix lowerThreshold) = 0 ∧
        inputEventCanonicalValue cell
          (imagComparisonForm matrix upperThreshold) = 0) := by
  rintro ⟨lowerZero, upperZero⟩
  have lowerDivides := inputEventCanonicalZero_dvd_clearedForm cell
    (imagComparisonForm matrix lowerThreshold) lowerMember lowerZero
  have upperDivides := inputEventCanonicalZero_dvd_clearedForm cell
    (imagComparisonForm matrix upperThreshold) upperMember upperZero
  have difference := dvd_sub lowerDivides upperDivides
  have scaled : cell.branch.factor.polynomial.toPolynomial ∣
      Polynomial.C (upperThreshold - lowerThreshold) *
        (clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial := by
    rw [toPolynomial_clearedForm_imagComparison,
      toPolynomial_clearedForm_imagComparison] at difference
    convert difference using 1
    simp only [Polynomial.C_sub]
    ring
  apply denominatorNotDivides
  apply dvd_of_dvd_C_mul (upperThreshold - lowerThreshold)
  · exact sub_ne_zero.mpr (Ne.symm thresholdsDistinct)
  · exact scaled

private theorem inputEvent_scaled_norm_real_imag_not_all_canonicalZero
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (matrix : Mat2 QI)
    (radius realThreshold imagThreshold : ℚ)
    (radialScale realScale imagScale : ℚ)
    (radialScaleNonzero : radialScale ≠ 0)
    (realScaleNonzero : realScale ≠ 0)
    (imagScaleNonzero : imagScale ≠ 0)
    (radiusGapNonzero :
      realThreshold ^ 2 + imagThreshold ^ 2 - radius ≠ 0)
    (radialMember : clearedForm
      (HermitianForm.scale radialScale
        (normComparisonForm matrix radius)) path ∈
      inputEventPolynomials state path)
    (realMember : clearedForm
      (HermitianForm.scale realScale
        (realComparisonForm matrix realThreshold)) path ∈
      inputEventPolynomials state path)
    (imagMember : clearedForm
      (HermitianForm.scale imagScale
        (imagComparisonForm matrix imagThreshold)) path ∈
      inputEventPolynomials state path)
    (denominatorSqNotDivides :
      ¬cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm (affineNormForm matrix.c matrix.d) path *
          clearedForm (affineNormForm matrix.c matrix.d) path).toPolynomial) :
    ¬(inputEventCanonicalValue cell
          (HermitianForm.scale radialScale
            (normComparisonForm matrix radius)) = 0 ∧
        inputEventCanonicalValue cell
          (HermitianForm.scale realScale
            (realComparisonForm matrix realThreshold)) = 0 ∧
        inputEventCanonicalValue cell
          (HermitianForm.scale imagScale
            (imagComparisonForm matrix imagThreshold)) = 0) := by
  rintro ⟨radialZero, realZero, imagZero⟩
  have radialScaledDivides := inputEventCanonicalZero_dvd_clearedForm cell
    _ radialMember radialZero
  have realScaledDivides := inputEventCanonicalZero_dvd_clearedForm cell
    _ realMember realZero
  have imagScaledDivides := inputEventCanonicalZero_dvd_clearedForm cell
    _ imagMember imagZero
  have radialDivides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm (normComparisonForm matrix radius) path).toPolynomial := by
    exact dvd_clearedForm_of_dvd_scale radialScale _ path radialScaleNonzero
      radialScaledDivides
  have realDivides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
        (realComparisonForm matrix realThreshold) path).toPolynomial := by
    exact dvd_clearedForm_of_dvd_scale realScale _ path realScaleNonzero
      realScaledDivides
  have imagDivides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
        (imagComparisonForm matrix imagThreshold) path).toPolynomial := by
    exact dvd_clearedForm_of_dvd_scale imagScale _ path imagScaleNonzero
      imagScaledDivides
  apply denominatorSqNotDivides
  exact dvd_clearedDenominator_square_of_norm_real_imag
    cell.branch.factor.polynomial.toPolynomial matrix radius realThreshold
      imagThreshold path radiusGapNonzero radialDivides realDivides imagDivides

/-- Every source annulus wall becomes a positive rational multiple of the
radius-one or radius-two wall after the parser's sector normalization. -/
private theorem radialEventFace_source_normalized
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI)
    (face : EventOrientedFace)
    (member : face ∈ radialEventFaces kind exponent matrix) :
    ∃ scale radius : ℚ, 0 < scale ∧
      (radius = 1 ∨ radius = 2) ∧
      face.source = HermitianForm.scale scale
        (normComparisonForm (normalizedMatrix kind exponent matrix) radius) := by
  cases kind with
  | initialHigh =>
      simp only [radialEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl
      · refine ⟨(2 : ℚ) ^ exponent, 1, by positivity, Or.inl rfl, ?_⟩
        simpa only [eventNormFace, radialOwnerForm, normalizedRadialOwnerScale,
          normalizedRadialRadius] using
          (radialOwnerForm_eq_scale_normalized .initialHigh exponent matrix)
      · refine ⟨(2 : ℚ) ^ exponent, 2, by positivity, Or.inr rfl, ?_⟩
        rw [normalizedMatrix, normalizationMatrix,
          normComparisonForm_scaleMatrix]
        apply HermitianForm.ext <;>
          simp only [eventNormFace, normComparisonForm, HermitianForm.sub,
            HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
            normSq_inv _ (RawParser.natPow_gamma_ne exponent),
            normSq_natPow, normSq_gamma, pow_succ] <;>
          field_simp

  | initialLow =>
      simp only [radialEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl
      · refine ⟨1 / (2 : ℚ) ^ exponent, 1, by positivity, Or.inl rfl, ?_⟩
        simpa only [eventNormFace, radialOwnerForm, normalizedRadialOwnerScale,
          normalizedRadialRadius, inv_eq_one_div] using
          (radialOwnerForm_eq_scale_normalized .initialLow exponent matrix)
      · refine ⟨1 / (2 : ℚ) ^ exponent, 2, by positivity, Or.inr rfl, ?_⟩
        rw [normalizedMatrix, normalizationMatrix,
          normComparisonForm_scaleMatrix]
        apply HermitianForm.ext <;>
          simp only [eventNormFace, normComparisonForm, HermitianForm.sub,
            HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
            normSq_natPow, normSq_gamma] <;>
          field_simp
  | loop =>
      simp only [radialEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl
      · refine ⟨(2 : ℚ) ^ exponent, 1, by positivity, Or.inl rfl, ?_⟩
        simpa only [eventNormFace, radialOwnerForm, normalizedRadialOwnerScale,
          normalizedRadialRadius, normalizedMatrix, normalizationMatrix] using
          (radialOwnerForm_eq_scale_normalized .initialHigh exponent matrix)
      · refine ⟨(2 : ℚ) ^ exponent, 2, by positivity, Or.inr rfl, ?_⟩
        rw [normalizedMatrix, normalizationMatrix,
          normComparisonForm_scaleMatrix]
        apply HermitianForm.ext <;>
          simp only [eventNormFace, normComparisonForm, HermitianForm.sub,
            HermitianForm.add, HermitianForm.neg, HermitianForm.scale,
            normSq_inv _ (RawParser.natPow_gamma_ne exponent),
            normSq_natPow, normSq_gamma, pow_succ] <;>
          field_simp

private theorem activeRadialEventForms_length_le_one
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (classified : ∀ face ∈ radialEventFaces kind exponent
      (adjugate (RawParser.parse current.core.word).matrix),
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials (RawParser.parse current.core.word)
          data.boundaryPathCylinder.path) :
    (activeOrientedFaceForms data.boundaryOrientedInputCell
      (radialEventFaces kind exponent
        (adjugate (RawParser.parse current.core.word).matrix))).length ≤ 1 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  change (activeOrientedFaceForms cell
    (radialEventFaces kind exponent matrix)).length ≤ 1
  have denominatorNotDivides :
      ¬cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm (affineNormForm matrix.c matrix.d)
          data.boundaryPathCylinder.path).toPolynomial := by
    simpa only [cell, matrix, state] using
      data.boundaryEventFactor_not_dvd_decoder
  cases kind with
  | initialHigh =>
      have notBoth := inputEvent_normComparison_not_both_canonicalZero cell
        matrix ((2 : ℚ) ^ exponent) ((2 : ℚ) ^ (exponent + 1))
        (by
          have positive : 0 < (2 : ℚ) ^ exponent := by positivity
          rw [pow_succ]
          nlinarith)
        (classified (eventNormFace true matrix ((2 : ℚ) ^ exponent))
          (by simp [radialEventFaces, matrix, state]))
        (classified (eventNormFace false matrix ((2 : ℚ) ^ (exponent + 1)))
          (by simp [radialEventFaces, matrix, state])) denominatorNotDivides
      by_cases lowerZero : inputEventCanonicalValue cell
          (normComparisonForm matrix ((2 : ℚ) ^ exponent)) = 0
      · by_cases upperZero : inputEventCanonicalValue cell
            (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))) = 0
        · exact (notBoth ⟨lowerZero, upperZero⟩).elim
        · simp [activeOrientedFaceForms, radialEventFaces,
            EventOrientedFace.canonicalValue, eventNormFace, lowerZero,
            upperZero]
      · by_cases upperZero : inputEventCanonicalValue cell
            (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))) = 0 <;>
          simp [activeOrientedFaceForms, radialEventFaces,
            EventOrientedFace.canonicalValue, eventNormFace, lowerZero,
            upperZero]

  | initialLow =>
      have powerPositive : 0 < (2 : ℚ) ^ exponent := by positivity
      have radiiDistinct : ((2 : ℚ) ^ exponent)⁻¹ ≠
          2 / (2 : ℚ) ^ exponent := by
        rw [← one_div]
        exact ne_of_lt
          (div_lt_div_of_pos_right (by norm_num) powerPositive)
      have lowerClassified :=
        classified (eventNormFace true matrix (1 / (2 : ℚ) ^ exponent))
          (by simp [radialEventFaces, matrix, state])
      change clearedForm
          (normComparisonForm matrix (1 / (2 : ℚ) ^ exponent))
            data.boundaryPathCylinder.path ∈
        inputEventPolynomials (RawParser.parse current.core.word)
          data.boundaryPathCylinder.path at lowerClassified
      have notBoth := inputEvent_normComparison_not_both_canonicalZero cell
        matrix (((2 : ℚ) ^ exponent)⁻¹) (2 / (2 : ℚ) ^ exponent)
        radiiDistinct (by
          rw [data.boundaryCandidate_sourceEvent]
          simpa only [data.boundaryPathCylinder_path,
            ActivePositiveGuardData.sourceEvent, one_div] using
            lowerClassified)
        (classified (eventNormFace false matrix (2 / (2 : ℚ) ^ exponent))
          (by simp [radialEventFaces, matrix, state])) denominatorNotDivides
      by_cases lowerZero : inputEventCanonicalValue cell
          (normComparisonForm matrix (((2 : ℚ) ^ exponent)⁻¹)) = 0
      · by_cases upperZero : inputEventCanonicalValue cell
            (normComparisonForm matrix (2 / (2 : ℚ) ^ exponent)) = 0
        · exact (notBoth ⟨lowerZero, upperZero⟩).elim
        · simp [activeOrientedFaceForms, radialEventFaces,
            EventOrientedFace.canonicalValue, eventNormFace,
            lowerZero, upperZero]
      · by_cases upperZero : inputEventCanonicalValue cell
            (normComparisonForm matrix (2 / (2 : ℚ) ^ exponent)) = 0 <;>
          simp [activeOrientedFaceForms, radialEventFaces,
            EventOrientedFace.canonicalValue, eventNormFace,
            lowerZero, upperZero]
  | loop =>
      have notBoth := inputEvent_normComparison_not_both_canonicalZero cell
        matrix ((2 : ℚ) ^ exponent) ((2 : ℚ) ^ (exponent + 1))
        (by
          have positive : 0 < (2 : ℚ) ^ exponent := by positivity
          rw [pow_succ]
          nlinarith)
        (classified (eventNormFace true matrix ((2 : ℚ) ^ exponent))
          (by simp [radialEventFaces, matrix, state]))
        (classified (eventNormFace false matrix ((2 : ℚ) ^ (exponent + 1)))
          (by simp [radialEventFaces, matrix, state])) denominatorNotDivides
      by_cases lowerZero : inputEventCanonicalValue cell
          (normComparisonForm matrix ((2 : ℚ) ^ exponent)) = 0
      · by_cases upperZero : inputEventCanonicalValue cell
            (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))) = 0
        · exact (notBoth ⟨lowerZero, upperZero⟩).elim
        · simp [activeOrientedFaceForms, radialEventFaces,
            EventOrientedFace.canonicalValue, eventNormFace, lowerZero,
            upperZero]
      · by_cases upperZero : inputEventCanonicalValue cell
            (normComparisonForm matrix ((2 : ℚ) ^ (exponent + 1))) = 0 <;>
          simp [activeOrientedFaceForms, radialEventFaces,
            EventOrientedFace.canonicalValue, eventNormFace, lowerZero,
            upperZero]

private theorem filter_three_length_le_two_of_not_both
    {α : Type} (check : α → Bool) (first second third : α)
    (notBoth : ¬(check second = true ∧ check third = true)) :
    ([first, second, third].filter check).length ≤ 2 := by
  cases firstCheck : check first <;>
    cases secondCheck : check second <;>
    cases thirdCheck : check third <;>
    simp_all

private theorem filter_pair_length_le_one_of_not_both
    {α : Type} (check : α → Bool) (first second : α)
    (notBoth : ¬(check first = true ∧ check second = true)) :
    ([first, second].filter check).length ≤ 1 := by
  cases firstCheck : check first <;>
    cases secondCheck : check second <;>
    simp_all

private theorem map_filter_pair_eq_pair
    {α β : Type} (check : α → Bool) (map : α → β)
    (first second : α) (left right : β)
    (pair : (([first, second].filter check).map map) = [left, right]) :
    left = map first ∧ right = map second := by
  cases firstCheck : check first <;>
    cases secondCheck : check second <;>
    simp_all

private theorem map_filter_three_eq_pair_of_not_both
    {α β : Type} (check : α → Bool) (map : α → β)
    (first second third : α) (left right : β)
    (notBoth : ¬(check second = true ∧ check third = true))
    (pair : (([first, second, third].filter check).map map) =
      [left, right]) :
    (left = map first ∧ right = map second) ∨
      (left = map first ∧ right = map third) := by
  cases firstCheck : check first <;>
    cases secondCheck : check second <;>
    cases thirdCheck : check third <;>
    simp_all

private theorem not_both_comm {left right : Prop}
    (notBoth : ¬(left ∧ right)) : ¬(right ∧ left) := by
  rintro ⟨rightHolds, leftHolds⟩
  exact notBoth ⟨leftHolds, rightHolds⟩

private theorem filter_three_length_le_one_of_pairwise
    {α : Type} (check : α → Bool) (first second third : α)
    (firstSecond : ¬(check first = true ∧ check second = true))
    (firstThird : ¬(check first = true ∧ check third = true))
    (secondThird : ¬(check second = true ∧ check third = true)) :
    ([first, second, third].filter check).length ≤ 1 := by
  cases firstCheck : check first <;>
    cases secondCheck : check second <;>
    cases thirdCheck : check third <;>
    simp_all

private theorem sourceCanonicalZero_of_orientedCheck
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (face : EventOrientedFace)
    (checked : decide (face.canonicalValue cell = 0) = true) :
    inputEventCanonicalValue cell face.source = 0 := by
  have zero := of_decide_eq_true checked
  cases increasingEq : face.increasing
  · simpa [EventOrientedFace.canonicalValue, increasingEq] using zero
  · simpa [EventOrientedFace.canonicalValue, increasingEq] using zero

private theorem activeSectorEventForms_length_le_two
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (classified : ∀ face ∈ sectorEventFaces sector
      (normalizedMatrix kind exponent
        (adjugate (RawParser.parse current.core.word).matrix)),
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials (RawParser.parse current.core.word)
          data.boundaryPathCylinder.path) :
    (activeOrientedFaceForms data.boundaryOrientedInputCell
      (sectorEventFaces sector
        (normalizedMatrix kind exponent
          (adjugate (RawParser.parse current.core.word).matrix)))).length ≤ 2 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  let path :=
    data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path
  change (activeOrientedFaceForms cell
    (sectorEventFaces sector normalized)).length ≤ 2
  have normalizedDenominatorNotDivides :
      ¬cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm (affineNormForm normalized.c normalized.d) path
          ).toPolynomial := by
    have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
    dsimp only [normalized]
    rw [lowerRow.1, lowerRow.2]
    simpa only [cell, matrix, state, path] using
      data.boundaryCandidateEventFactor_not_dvd_decoder
  cases sector with
  | east =>
      have lowerMember := data.inputEventPolynomial_of_boundaryPath _
        (classified (eventImagFace true normalized (-1 / 2))
          (by simp [sectorEventFaces, normalized, matrix, state]))
      have upperMember := data.inputEventPolynomial_of_boundaryPath _
        (classified (eventImagFace false normalized (1 / 2))
          (by simp [sectorEventFaces, normalized, matrix, state]))
      have notBoth := inputEvent_imagComparison_not_both_canonicalZero cell
        normalized (-1 / 2) (1 / 2) (by norm_num) lowerMember upperMember
          normalizedDenominatorNotDivides
      rw [activeOrientedFaceForms, List.length_map]
      apply filter_three_length_le_two_of_not_both
      intro both
      apply notBoth
      constructor
      · simpa [EventOrientedFace.canonicalValue, eventImagFace] using
          (of_decide_eq_true both.1)
      · simpa [EventOrientedFace.canonicalValue, eventImagFace] using
          (of_decide_eq_true both.2)
  | northEast =>
      rw [activeOrientedFaceForms, List.length_map]
      simpa [sectorEventFaces] using
        List.length_filter_le
          (fun face : EventOrientedFace =>
            decide (face.canonicalValue cell = 0))
          (sectorEventFaces .northEast normalized)
  | north =>
      have lowerMember := data.inputEventPolynomial_of_boundaryPath _
        (classified (eventRealFace true normalized (-1 / 2))
          (by simp [sectorEventFaces, normalized, matrix, state]))
      have upperMember := data.inputEventPolynomial_of_boundaryPath _
        (classified (eventRealFace false normalized (1 / 2))
          (by simp [sectorEventFaces, normalized, matrix, state]))
      have notBoth := inputEvent_realComparison_not_both_canonicalZero cell
        normalized (-1 / 2) (1 / 2) (by norm_num) lowerMember upperMember
          normalizedDenominatorNotDivides
      rw [activeOrientedFaceForms, List.length_map]
      apply filter_three_length_le_two_of_not_both
      intro both
      apply notBoth
      constructor
      · simpa [EventOrientedFace.canonicalValue, eventRealFace] using
          (of_decide_eq_true both.1)
      · simpa [EventOrientedFace.canonicalValue, eventRealFace] using
          (of_decide_eq_true both.2)
  | northWest =>
      rw [activeOrientedFaceForms, List.length_map]
      simpa [sectorEventFaces] using
        List.length_filter_le
          (fun face : EventOrientedFace =>
            decide (face.canonicalValue cell = 0))
          (sectorEventFaces .northWest normalized)
  | west =>
      have lowerMember := data.inputEventPolynomial_of_boundaryPath _
        (classified (eventImagFace true normalized (-1 / 2))
          (by simp [sectorEventFaces, normalized, matrix, state]))
      have upperMember := data.inputEventPolynomial_of_boundaryPath _
        (classified (eventImagFace false normalized (1 / 2))
          (by simp [sectorEventFaces, normalized, matrix, state]))
      have notBoth := inputEvent_imagComparison_not_both_canonicalZero cell
        normalized (-1 / 2) (1 / 2) (by norm_num) lowerMember upperMember
          normalizedDenominatorNotDivides
      rw [activeOrientedFaceForms, List.length_map]
      apply filter_three_length_le_two_of_not_both
      intro both
      apply notBoth
      constructor
      · simpa [EventOrientedFace.canonicalValue, eventImagFace] using
          (of_decide_eq_true both.1)
      · simpa [EventOrientedFace.canonicalValue, eventImagFace] using
          (of_decide_eq_true both.2)
  | southWest =>
      rw [activeOrientedFaceForms, List.length_map]
      simpa [sectorEventFaces] using
        List.length_filter_le
          (fun face : EventOrientedFace =>
            decide (face.canonicalValue cell = 0))
          (sectorEventFaces .southWest normalized)
  | south =>
      have lowerMember := data.inputEventPolynomial_of_boundaryPath _
        (classified (eventRealFace true normalized (-1 / 2))
          (by simp [sectorEventFaces, normalized, matrix, state]))
      have upperMember := data.inputEventPolynomial_of_boundaryPath _
        (classified (eventRealFace false normalized (1 / 2))
          (by simp [sectorEventFaces, normalized, matrix, state]))
      have notBoth := inputEvent_realComparison_not_both_canonicalZero cell
        normalized (-1 / 2) (1 / 2) (by norm_num) lowerMember upperMember
          normalizedDenominatorNotDivides
      rw [activeOrientedFaceForms, List.length_map]
      apply filter_three_length_le_two_of_not_both
      intro both
      apply notBoth
      constructor
      · simpa [EventOrientedFace.canonicalValue, eventRealFace] using
          (of_decide_eq_true both.1)
      · simpa [EventOrientedFace.canonicalValue, eventRealFace] using
          (of_decide_eq_true both.2)
  | southEast =>
      rw [activeOrientedFaceForms, List.length_map]
      simpa [sectorEventFaces] using
        List.length_filter_le
          (fun face : EventOrientedFace =>
            decide (face.canonicalValue cell = 0))
          (sectorEventFaces .southEast normalized)

private theorem radialEventFace_sectorCorner_not_all_canonicalZero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (radialFace : EventOrientedFace)
    (radialMember : radialFace ∈ radialEventFaces kind exponent
      (adjugate (RawParser.parse current.core.word).matrix))
    (realThreshold imagThreshold : ℚ)
    (cornerRadiusGap : ∀ radius : ℚ, radius = 1 ∨ radius = 2 →
      realThreshold ^ 2 + imagThreshold ^ 2 - radius ≠ 0)
    (radialClassified : clearedForm radialFace.source
        data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path)
    (realClassified : clearedForm
        (realComparisonForm
          (normalizedMatrix kind exponent
            (adjugate (RawParser.parse current.core.word).matrix))
          realThreshold) data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path)
    (imagClassified : clearedForm
        (imagComparisonForm
          (normalizedMatrix kind exponent
            (adjugate (RawParser.parse current.core.word).matrix))
          imagThreshold) data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path) :
    ¬(inputEventCanonicalValue data.boundaryOrientedInputCell
          radialFace.source = 0 ∧
        inputEventCanonicalValue data.boundaryOrientedInputCell
          (realComparisonForm
            (normalizedMatrix kind exponent
              (adjugate (RawParser.parse current.core.word).matrix))
            realThreshold) = 0 ∧
        inputEventCanonicalValue data.boundaryOrientedInputCell
          (imagComparisonForm
            (normalizedMatrix kind exponent
              (adjugate (RawParser.parse current.core.word).matrix))
            imagThreshold) = 0) := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  let path :=
    data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path
  rcases radialEventFace_source_normalized kind exponent matrix radialFace
      (by simpa only [matrix, state] using radialMember) with
    ⟨scale, radius, scalePositive, radiusCase, sourceEquality⟩
  have radialMember' := data.inputEventPolynomial_of_boundaryPath _
    radialClassified
  have realMember' := data.inputEventPolynomial_of_boundaryPath _
    realClassified
  have imagMember' := data.inputEventPolynomial_of_boundaryPath _
    imagClassified
  have denominatorSqNotDivides :
      ¬cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm (affineNormForm normalized.c normalized.d) path *
          clearedForm (affineNormForm normalized.c normalized.d) path
        ).toPolynomial := by
    have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
    dsimp only [normalized]
    rw [lowerRow.1, lowerRow.2]
    simpa only [cell, matrix, state, path] using
      data.boundaryCandidateEventFactor_not_dvd_decoderSq
  intro zeros
  apply inputEvent_scaled_norm_real_imag_not_all_canonicalZero cell normalized
    radius realThreshold imagThreshold scale 1 1 scalePositive.ne'
      (by norm_num) (by norm_num) (cornerRadiusGap radius radiusCase)
  · rw [← sourceEquality]
    simpa only [cell, normalized, matrix, state, path] using radialMember'
  · simpa only [HermitianForm.scale_one, cell, normalized, matrix, state,
      path] using realMember'
  · simpa only [HermitianForm.scale_one, cell, normalized, matrix, state,
      path] using imagMember'
  · exact denominatorSqNotDivides
  · simpa only [sourceEquality, HermitianForm.scale_one, cell, normalized,
      matrix, state] using zeros

private theorem radialEventFace_sectorCorner_checks_not_both
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (radialFace : EventOrientedFace)
    (radialMember : radialFace ∈ radialEventFaces kind exponent
      (adjugate (RawParser.parse current.core.word).matrix))
    (radialChecked : decide
      (radialFace.canonicalValue data.boundaryOrientedInputCell = 0) = true)
    (realIncreasing imagIncreasing : Bool)
    (realThreshold imagThreshold : ℚ)
    (cornerRadiusGap : ∀ radius : ℚ, radius = 1 ∨ radius = 2 →
      realThreshold ^ 2 + imagThreshold ^ 2 - radius ≠ 0)
    (radialClassified : clearedForm radialFace.source
        data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path)
    (realClassified : clearedForm
        (realComparisonForm
          (normalizedMatrix kind exponent
            (adjugate (RawParser.parse current.core.word).matrix))
          realThreshold) data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path)
    (imagClassified : clearedForm
        (imagComparisonForm
          (normalizedMatrix kind exponent
            (adjugate (RawParser.parse current.core.word).matrix))
          imagThreshold) data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path) :
    ¬(decide
          ((eventRealFace realIncreasing
            (normalizedMatrix kind exponent
              (adjugate (RawParser.parse current.core.word).matrix))
            realThreshold).canonicalValue data.boundaryOrientedInputCell = 0) =
          true ∧
        decide
          ((eventImagFace imagIncreasing
            (normalizedMatrix kind exponent
              (adjugate (RawParser.parse current.core.word).matrix))
            imagThreshold).canonicalValue data.boundaryOrientedInputCell = 0) =
          true) := by
  intro checked
  apply radialEventFace_sectorCorner_not_all_canonicalZero data kind exponent
    radialFace radialMember realThreshold imagThreshold cornerRadiusGap
      radialClassified realClassified imagClassified
  exact
    ⟨sourceCanonicalZero_of_orientedCheck data.boundaryOrientedInputCell
        radialFace radialChecked,
      sourceCanonicalZero_of_orientedCheck data.boundaryOrientedInputCell
        (eventRealFace realIncreasing
          (normalizedMatrix kind exponent
            (adjugate (RawParser.parse current.core.word).matrix))
          realThreshold) checked.1,
      sourceCanonicalZero_of_orientedCheck data.boundaryOrientedInputCell
        (eventImagFace imagIncreasing
          (normalizedMatrix kind exponent
            (adjugate (RawParser.parse current.core.word).matrix))
          imagThreshold) checked.2⟩

private theorem sectorRealFaces_checks_not_both
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (leftIncreasing rightIncreasing : Bool)
    (leftThreshold rightThreshold : ℚ)
    (thresholdsDistinct : leftThreshold ≠ rightThreshold)
    (leftClassified : clearedForm
        (realComparisonForm
          (normalizedMatrix kind exponent
            (adjugate (RawParser.parse current.core.word).matrix))
          leftThreshold) data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path)
    (rightClassified : clearedForm
        (realComparisonForm
          (normalizedMatrix kind exponent
            (adjugate (RawParser.parse current.core.word).matrix))
          rightThreshold) data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path) :
    ¬(decide
          ((eventRealFace leftIncreasing
            (normalizedMatrix kind exponent
              (adjugate (RawParser.parse current.core.word).matrix))
            leftThreshold).canonicalValue data.boundaryOrientedInputCell = 0) =
          true ∧
        decide
          ((eventRealFace rightIncreasing
            (normalizedMatrix kind exponent
              (adjugate (RawParser.parse current.core.word).matrix))
            rightThreshold).canonicalValue data.boundaryOrientedInputCell = 0) =
          true) := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  let path :=
    data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path
  have leftMember := data.inputEventPolynomial_of_boundaryPath _ leftClassified
  have rightMember := data.inputEventPolynomial_of_boundaryPath _
    rightClassified
  have denominatorNotDivides :
      ¬cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm (affineNormForm normalized.c normalized.d) path
          ).toPolynomial := by
    have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
    dsimp only [normalized]
    rw [lowerRow.1, lowerRow.2]
    simpa only [cell, matrix, state, path] using
      data.boundaryCandidateEventFactor_not_dvd_decoder
  have notBoth := inputEvent_realComparison_not_both_canonicalZero cell
    normalized leftThreshold rightThreshold thresholdsDistinct leftMember
      rightMember denominatorNotDivides
  intro checked
  apply notBoth
  exact
    ⟨sourceCanonicalZero_of_orientedCheck cell
        (eventRealFace leftIncreasing normalized leftThreshold) checked.1,
      sourceCanonicalZero_of_orientedCheck cell
        (eventRealFace rightIncreasing normalized rightThreshold) checked.2⟩

private theorem sectorImagFaces_checks_not_both
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (lowerIncreasing upperIncreasing : Bool)
    (lowerThreshold upperThreshold : ℚ)
    (thresholdsDistinct : lowerThreshold ≠ upperThreshold)
    (lowerClassified : clearedForm
        (imagComparisonForm
          (normalizedMatrix kind exponent
            (adjugate (RawParser.parse current.core.word).matrix))
          lowerThreshold) data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path)
    (upperClassified : clearedForm
        (imagComparisonForm
          (normalizedMatrix kind exponent
            (adjugate (RawParser.parse current.core.word).matrix))
          upperThreshold) data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path) :
    ¬(decide
          ((eventImagFace lowerIncreasing
            (normalizedMatrix kind exponent
              (adjugate (RawParser.parse current.core.word).matrix))
            lowerThreshold).canonicalValue data.boundaryOrientedInputCell = 0) =
          true ∧
        decide
          ((eventImagFace upperIncreasing
            (normalizedMatrix kind exponent
              (adjugate (RawParser.parse current.core.word).matrix))
            upperThreshold).canonicalValue data.boundaryOrientedInputCell = 0) =
          true) := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  let path :=
    data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path
  have lowerMember := data.inputEventPolynomial_of_boundaryPath _
    lowerClassified
  have upperMember := data.inputEventPolynomial_of_boundaryPath _
    upperClassified
  have denominatorNotDivides :
      ¬cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm (affineNormForm normalized.c normalized.d) path
          ).toPolynomial := by
    have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
    dsimp only [normalized]
    rw [lowerRow.1, lowerRow.2]
    simpa only [cell, matrix, state, path] using
      data.boundaryCandidateEventFactor_not_dvd_decoder
  have notBoth := inputEvent_imagComparison_not_both_canonicalZero cell
    normalized lowerThreshold upperThreshold thresholdsDistinct lowerMember
      upperMember denominatorNotDivides
  intro checked
  apply notBoth
  exact
    ⟨sourceCanonicalZero_of_orientedCheck cell
        (eventImagFace lowerIncreasing normalized lowerThreshold) checked.1,
      sourceCanonicalZero_of_orientedCheck cell
        (eventImagFace upperIncreasing normalized upperThreshold) checked.2⟩

private theorem activeSectorEventForms_pair_angleGap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (classified : ∀ face ∈ sectorEventFaces sector
      (normalizedMatrix kind exponent
        (adjugate (RawParser.parse current.core.word).matrix)),
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials (RawParser.parse current.core.word)
          data.boundaryPathCylinder.path)
    {left right : HermitianForm}
    (pair : activeOrientedFaceForms data.boundaryOrientedInputCell
      (sectorEventFaces sector
        (normalizedMatrix kind exponent
          (adjugate (RawParser.parse current.core.word).matrix))) =
        [left, right]) :
    0 < boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  let check := fun face : EventOrientedFace =>
    decide (face.canonicalValue cell = 0)
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have matrixDeterminant : determinant matrix ≠ 0 := by
    dsimp only [matrix]
    rw [determinant_adjugate]
    exact stateDeterminant
  have normalizedDeterminant : determinant normalized ≠ 0 :=
    FTA.CCLCompleteOwnerShapes.normalizedMatrix_determinant_ne_of kind
      exponent matrix matrixDeterminant
  change (((sectorEventFaces sector normalized).filter check).map
    EventOrientedFace.form) = [left, right] at pair
  cases sector with
  | east =>
      have lowerClassified := classified
        (eventImagFace true normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have upperClassified := classified
        (eventImagFace false normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have notBoth := sectorImagFaces_checks_not_both data kind exponent true
        false (-1 / 2) (1 / 2) (by norm_num) lowerClassified
          upperClassified
      have shape := map_filter_three_eq_pair_of_not_both check
        EventOrientedFace.form
        (eventRealFace true normalized (1 / 2))
        (eventImagFace true normalized (-1 / 2))
        (eventImagFace false normalized (1 / 2)) left right notBoth
        (by simpa [sectorEventFaces] using pair)
      rcases shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
          orientedRealForm, orientedImagForm] using
          orientedReal_orientedImag_angleGap_pos true true normalized
            (1 / 2) (-1 / 2) normalizedDeterminant
      · simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
          orientedRealForm, orientedImagForm] using
          orientedReal_orientedImag_angleGap_pos true false normalized
            (1 / 2) (1 / 2) normalizedDeterminant
  | northEast =>
      have shape := map_filter_pair_eq_pair check EventOrientedFace.form
        (eventRealFace true normalized (1 / 2))
        (eventImagFace true normalized (1 / 2)) left right
        (by simpa [sectorEventFaces] using pair)
      rcases shape with ⟨rfl, rfl⟩
      simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
        orientedRealForm, orientedImagForm] using
        orientedReal_orientedImag_angleGap_pos true true normalized
          (1 / 2) (1 / 2) normalizedDeterminant
  | north =>
      have lowerClassified := classified
        (eventRealFace true normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have upperClassified := classified
        (eventRealFace false normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have notBoth := sectorRealFaces_checks_not_both data kind exponent true
        false (-1 / 2) (1 / 2) (by norm_num) lowerClassified
          upperClassified
      have shape := map_filter_three_eq_pair_of_not_both check
        EventOrientedFace.form
        (eventImagFace true normalized (1 / 2))
        (eventRealFace true normalized (-1 / 2))
        (eventRealFace false normalized (1 / 2)) left right notBoth
        (by simpa [sectorEventFaces] using pair)
      rcases shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
          orientedRealForm, orientedImagForm] using
          orientedImag_orientedReal_angleGap_pos true true normalized
            (1 / 2) (-1 / 2) normalizedDeterminant
      · simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
          orientedRealForm, orientedImagForm] using
          orientedImag_orientedReal_angleGap_pos true false normalized
            (1 / 2) (1 / 2) normalizedDeterminant
  | northWest =>
      have shape := map_filter_pair_eq_pair check EventOrientedFace.form
        (eventRealFace false normalized (-1 / 2))
        (eventImagFace true normalized (1 / 2)) left right
        (by simpa [sectorEventFaces] using pair)
      rcases shape with ⟨rfl, rfl⟩
      simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
        orientedRealForm, orientedImagForm] using
        orientedReal_orientedImag_angleGap_pos false true normalized
          (-1 / 2) (1 / 2) normalizedDeterminant
  | west =>
      have lowerClassified := classified
        (eventImagFace true normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have upperClassified := classified
        (eventImagFace false normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have notBoth := sectorImagFaces_checks_not_both data kind exponent true
        false (-1 / 2) (1 / 2) (by norm_num) lowerClassified
          upperClassified
      have shape := map_filter_three_eq_pair_of_not_both check
        EventOrientedFace.form
        (eventRealFace false normalized (-1 / 2))
        (eventImagFace true normalized (-1 / 2))
        (eventImagFace false normalized (1 / 2)) left right notBoth
        (by simpa [sectorEventFaces] using pair)
      rcases shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
          orientedRealForm, orientedImagForm] using
          orientedReal_orientedImag_angleGap_pos false true normalized
            (-1 / 2) (-1 / 2) normalizedDeterminant
      · simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
          orientedRealForm, orientedImagForm] using
          orientedReal_orientedImag_angleGap_pos false false normalized
            (-1 / 2) (1 / 2) normalizedDeterminant
  | southWest =>
      have shape := map_filter_pair_eq_pair check EventOrientedFace.form
        (eventRealFace false normalized (-1 / 2))
        (eventImagFace false normalized (-1 / 2)) left right
        (by simpa [sectorEventFaces] using pair)
      rcases shape with ⟨rfl, rfl⟩
      simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
        orientedRealForm, orientedImagForm] using
        orientedReal_orientedImag_angleGap_pos false false normalized
          (-1 / 2) (-1 / 2) normalizedDeterminant
  | south =>
      have lowerClassified := classified
        (eventRealFace true normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have upperClassified := classified
        (eventRealFace false normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have notBoth := sectorRealFaces_checks_not_both data kind exponent true
        false (-1 / 2) (1 / 2) (by norm_num) lowerClassified
          upperClassified
      have shape := map_filter_three_eq_pair_of_not_both check
        EventOrientedFace.form
        (eventImagFace false normalized (-1 / 2))
        (eventRealFace true normalized (-1 / 2))
        (eventRealFace false normalized (1 / 2)) left right notBoth
        (by simpa [sectorEventFaces] using pair)
      rcases shape with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
          orientedRealForm, orientedImagForm] using
          orientedImag_orientedReal_angleGap_pos false true normalized
            (-1 / 2) (-1 / 2) normalizedDeterminant
      · simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
          orientedRealForm, orientedImagForm] using
          orientedImag_orientedReal_angleGap_pos false false normalized
            (-1 / 2) (1 / 2) normalizedDeterminant
  | southEast =>
      have shape := map_filter_pair_eq_pair check EventOrientedFace.form
        (eventRealFace true normalized (1 / 2))
        (eventImagFace false normalized (-1 / 2)) left right
        (by simpa [sectorEventFaces] using pair)
      rcases shape with ⟨rfl, rfl⟩
      simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
        orientedRealForm, orientedImagForm] using
        orientedReal_orientedImag_angleGap_pos true false normalized
          (1 / 2) (-1 / 2) normalizedDeterminant

private theorem activeSectorTwoEventForms_pair_angleGap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    {left right : HermitianForm}
    (pair : activeOrientedFaceForms data.boundaryOrientedInputCell
      (sectorTwoEventFaces first second
        (normalizedMatrix kind exponent
          (adjugate (RawParser.parse current.core.word).matrix))) =
        [left, right]) :
    0 < boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  let check := fun face : EventOrientedFace =>
    decide (face.canonicalValue cell = 0)
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have matrixDeterminant : determinant matrix ≠ 0 := by
    dsimp only [matrix]
    rw [determinant_adjugate]
    exact stateDeterminant
  have normalizedDeterminant : determinant normalized ≠ 0 :=
    FTA.CCLCompleteOwnerShapes.normalizedMatrix_determinant_ne_of kind
      exponent matrix matrixDeterminant
  change (((sectorTwoEventFaces first second normalized).filter check).map
    EventOrientedFace.form) = [left, right] at pair
  cases first <;> cases second
  · have shape := map_filter_pair_eq_pair check EventOrientedFace.form
      (eventRealFace true normalized (1 / 2))
      (eventImagFace true normalized (-1 / 2)) left right
      (by simpa [sectorTwoEventFaces] using pair)
    rcases shape with ⟨rfl, rfl⟩
    simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
      orientedRealForm, orientedImagForm] using
      orientedReal_orientedImag_angleGap_pos true true normalized
        (1 / 2) (-1 / 2) normalizedDeterminant
  · have shape := map_filter_pair_eq_pair check EventOrientedFace.form
      (eventRealFace false normalized (1 / 2))
      (eventImagFace true normalized (1 / 2)) left right
      (by simpa [sectorTwoEventFaces] using pair)
    rcases shape with ⟨rfl, rfl⟩
    simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
      orientedRealForm, orientedImagForm] using
      orientedReal_orientedImag_angleGap_pos false true normalized
        (1 / 2) (1 / 2) normalizedDeterminant
  · have shape := map_filter_pair_eq_pair check EventOrientedFace.form
      (eventRealFace false normalized (-1 / 2))
      (eventImagFace false normalized (1 / 2)) left right
      (by simpa [sectorTwoEventFaces] using pair)
    rcases shape with ⟨rfl, rfl⟩
    simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
      orientedRealForm, orientedImagForm] using
      orientedReal_orientedImag_angleGap_pos false false normalized
        (-1 / 2) (1 / 2) normalizedDeterminant
  · have shape := map_filter_pair_eq_pair check EventOrientedFace.form
      (eventRealFace true normalized (-1 / 2))
      (eventImagFace false normalized (-1 / 2)) left right
      (by simpa [sectorTwoEventFaces] using pair)
    rcases shape with ⟨rfl, rfl⟩
    simpa [eventRealFace, eventImagFace, EventOrientedFace.form,
      orientedRealForm, orientedImagForm] using
      orientedReal_orientedImag_angleGap_pos true false normalized
        (-1 / 2) (-1 / 2) normalizedDeterminant

private def sectorTwoAxis : Bool → Bool → Sector
  | false, false => .east
  | false, true => .north
  | true, false => .west
  | true, true => .south

private theorem sectorTwoEventForm_mem_axisInterior
    (first second : Bool) (matrix : Mat2 QI) {form : HermitianForm}
    (member : form ∈
      (sectorTwoEventFaces first second matrix).map EventOrientedFace.form) :
    form ∈ sectorInteriorForms (sectorTwoAxis first second) matrix := by
  cases first <;> cases second <;>
    simp only [sectorTwoEventFaces, List.map_cons, List.map_nil,
      List.mem_cons, List.not_mem_nil, or_false] at member <;>
    rcases member with rfl | rfl <;>
    simp [sectorTwoAxis, sectorInteriorForms, eventRealFace, eventImagFace,
      EventOrientedFace.form, orientedRealForm, orientedImagForm]

private theorem activeSectorEventForms_length_le_one_of_radialChecked
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (radialFace : EventOrientedFace)
    (radialMember : radialFace ∈ radialEventFaces kind exponent
      (adjugate (RawParser.parse current.core.word).matrix))
    (radialChecked : decide
      (radialFace.canonicalValue data.boundaryOrientedInputCell = 0) = true)
    (radialClassified : clearedForm radialFace.source
        data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path)
    (sectorClassified : ∀ face ∈ sectorEventFaces sector
      (normalizedMatrix kind exponent
        (adjugate (RawParser.parse current.core.word).matrix)),
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials (RawParser.parse current.core.word)
          data.boundaryPathCylinder.path) :
    (activeOrientedFaceForms data.boundaryOrientedInputCell
      (sectorEventFaces sector
        (normalizedMatrix kind exponent
          (adjugate (RawParser.parse current.core.word).matrix)))).length ≤ 1 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  change (activeOrientedFaceForms cell
    (sectorEventFaces sector normalized)).length ≤ 1
  cases sector with
  | east =>
      have realClassified := sectorClassified
        (eventRealFace true normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have lowerClassified := sectorClassified
        (eventImagFace true normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have upperClassified := sectorClassified
        (eventImagFace false normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have realLower := radialEventFace_sectorCorner_checks_not_both data
        kind exponent radialFace radialMember radialChecked true true
        (1 / 2) (-1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified realClassified lowerClassified
      have realUpper := radialEventFace_sectorCorner_checks_not_both data
        kind exponent radialFace radialMember radialChecked true false
        (1 / 2) (1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified realClassified upperClassified
      have lowerUpper := sectorImagFaces_checks_not_both data kind exponent
        true false (-1 / 2) (1 / 2) (by norm_num) lowerClassified
          upperClassified
      rw [activeOrientedFaceForms, List.length_map]
      exact filter_three_length_le_one_of_pairwise _ _ _ _ realLower
        realUpper lowerUpper
  | northEast =>
      have realClassified := sectorClassified
        (eventRealFace true normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have imagClassified := sectorClassified
        (eventImagFace true normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have notBoth := radialEventFace_sectorCorner_checks_not_both data kind
        exponent radialFace radialMember radialChecked true true (1 / 2)
          (1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified realClassified imagClassified
      rw [activeOrientedFaceForms, List.length_map]
      exact filter_pair_length_le_one_of_not_both _ _ _ notBoth
  | north =>
      have imagClassified := sectorClassified
        (eventImagFace true normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have lowerClassified := sectorClassified
        (eventRealFace true normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have upperClassified := sectorClassified
        (eventRealFace false normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have lowerImag := radialEventFace_sectorCorner_checks_not_both data
        kind exponent radialFace radialMember radialChecked true true
        (-1 / 2) (1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified lowerClassified imagClassified
      have upperImag := radialEventFace_sectorCorner_checks_not_both data
        kind exponent radialFace radialMember radialChecked false true
        (1 / 2) (1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified upperClassified imagClassified
      have lowerUpper := sectorRealFaces_checks_not_both data kind exponent
        true false (-1 / 2) (1 / 2) (by norm_num) lowerClassified
          upperClassified
      rw [activeOrientedFaceForms, List.length_map]
      exact filter_three_length_le_one_of_pairwise _ _ _ _
        (not_both_comm lowerImag) (not_both_comm upperImag) lowerUpper
  | northWest =>
      have realClassified := sectorClassified
        (eventRealFace false normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have imagClassified := sectorClassified
        (eventImagFace true normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have notBoth := radialEventFace_sectorCorner_checks_not_both data kind
        exponent radialFace radialMember radialChecked false true (-1 / 2)
          (1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified realClassified imagClassified
      rw [activeOrientedFaceForms, List.length_map]
      exact filter_pair_length_le_one_of_not_both _ _ _ notBoth
  | west =>
      have realClassified := sectorClassified
        (eventRealFace false normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have lowerClassified := sectorClassified
        (eventImagFace true normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have upperClassified := sectorClassified
        (eventImagFace false normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have realLower := radialEventFace_sectorCorner_checks_not_both data
        kind exponent radialFace radialMember radialChecked false true
        (-1 / 2) (-1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified realClassified lowerClassified
      have realUpper := radialEventFace_sectorCorner_checks_not_both data
        kind exponent radialFace radialMember radialChecked false false
        (-1 / 2) (1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified realClassified upperClassified
      have lowerUpper := sectorImagFaces_checks_not_both data kind exponent
        true false (-1 / 2) (1 / 2) (by norm_num) lowerClassified
          upperClassified
      rw [activeOrientedFaceForms, List.length_map]
      exact filter_three_length_le_one_of_pairwise _ _ _ _ realLower
        realUpper lowerUpper
  | southWest =>
      have realClassified := sectorClassified
        (eventRealFace false normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have imagClassified := sectorClassified
        (eventImagFace false normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have notBoth := radialEventFace_sectorCorner_checks_not_both data kind
        exponent radialFace radialMember radialChecked false false (-1 / 2)
          (-1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified realClassified imagClassified
      rw [activeOrientedFaceForms, List.length_map]
      exact filter_pair_length_le_one_of_not_both _ _ _ notBoth
  | south =>
      have imagClassified := sectorClassified
        (eventImagFace false normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have lowerClassified := sectorClassified
        (eventRealFace true normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have upperClassified := sectorClassified
        (eventRealFace false normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have lowerImag := radialEventFace_sectorCorner_checks_not_both data
        kind exponent radialFace radialMember radialChecked true false
        (-1 / 2) (-1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified lowerClassified imagClassified
      have upperImag := radialEventFace_sectorCorner_checks_not_both data
        kind exponent radialFace radialMember radialChecked false false
        (1 / 2) (-1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified upperClassified imagClassified
      have lowerUpper := sectorRealFaces_checks_not_both data kind exponent
        true false (-1 / 2) (1 / 2) (by norm_num) lowerClassified
          upperClassified
      rw [activeOrientedFaceForms, List.length_map]
      exact filter_three_length_le_one_of_pairwise _ _ _ _
        (not_both_comm lowerImag) (not_both_comm upperImag) lowerUpper
  | southEast =>
      have realClassified := sectorClassified
        (eventRealFace true normalized (1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have imagClassified := sectorClassified
        (eventImagFace false normalized (-1 / 2))
        (by simp [sectorEventFaces, normalized, matrix, state])
      have notBoth := radialEventFace_sectorCorner_checks_not_both data kind
        exponent radialFace radialMember radialChecked true false (1 / 2)
          (-1 / 2)
        (by intro radius radiusCase
            rcases radiusCase with rfl | rfl <;> norm_num)
        radialClassified realClassified imagClassified
      rw [activeOrientedFaceForms, List.length_map]
      exact filter_pair_length_le_one_of_not_both _ _ _ notBoth

theorem activeBlockEventForms_length_le_two
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
      sector (adjugate (RawParser.parse current.core.word).matrix)) :
    (activeBlockEventForms data.boundaryOrientedInputCell kind exponent sector
      (adjugate (RawParser.parse current.core.word).matrix)).length ≤ 2 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  let check := fun face : EventOrientedFace =>
    decide (face.canonicalValue cell = 0)
  let radialFaces := radialEventFaces kind exponent matrix
  let sectorFaces := sectorEventFaces sector normalized
  have radialClassified : ∀ face ∈ radialFaces,
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials state data.boundaryPathCylinder.path := by
    intro face member
    exact target.classified face
      (by
        apply List.mem_append_left
        simpa only [radialFaces, sectorFaces, blockEventFaces, normalized,
          matrix, state] using member)
  have sectorClassified : ∀ face ∈ sectorFaces,
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials state data.boundaryPathCylinder.path := by
    intro face member
    exact target.classified face
      (by
        apply List.mem_append_right
        simpa only [radialFaces, sectorFaces, blockEventFaces, normalized,
          matrix, state] using member)
  have radialLength : (radialFaces.filter check).length ≤ 1 := by
    have bound := activeRadialEventForms_length_le_one data kind exponent
      (by simpa only [radialFaces, matrix, state] using radialClassified)
    simpa only [activeOrientedFaceForms, List.length_map, radialFaces, check,
      cell, matrix, state] using bound
  have sectorLength : (sectorFaces.filter check).length ≤ 2 := by
    have bound := activeSectorEventForms_length_le_two data kind exponent
      sector (by simpa only [sectorFaces, normalized, matrix, state] using
        sectorClassified)
    simpa only [activeOrientedFaceForms, List.length_map, sectorFaces, check,
      cell, normalized, matrix, state] using bound
  change (((radialFaces ++ sectorFaces).filter check).map
    EventOrientedFace.form).length ≤ 2
  rw [List.filter_append, List.map_append, List.length_append,
    List.length_map, List.length_map]
  generalize radialEquality : radialFaces.filter check = radialActive
  cases radialActive with
  | nil =>
      simpa using sectorLength
  | cons radialFace tail =>
      have tailNil : tail = [] := by
        rw [radialEquality] at radialLength
        cases tail with
        | nil => rfl
        | cons next rest => simp at radialLength
      subst tail
      have radialFiltered : radialFace ∈ radialFaces.filter check := by
        rw [radialEquality]
        simp
      rcases List.mem_filter.mp radialFiltered with
        ⟨radialMember, radialChecked⟩
      have sectorOne :=
        activeSectorEventForms_length_le_one_of_radialChecked data kind
          exponent sector radialFace
          (by simpa only [radialFaces, matrix, state] using radialMember)
          (by simpa only [check, cell] using radialChecked)
          (radialClassified radialFace radialMember)
          (by simpa only [sectorFaces, normalized, matrix, state] using
            sectorClassified)
      have sectorFilteredLength : (sectorFaces.filter check).length ≤ 1 := by
        simpa only [activeOrientedFaceForms, List.length_map, sectorFaces,
          check, cell, normalized, matrix, state] using sectorOne
      simp only [List.length_cons, List.length_nil]
      omega

theorem activeBlockEventForms_pair_angleGap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
      sector (adjugate (RawParser.parse current.core.word).matrix))
    {left right : HermitianForm}
    (pair : activeBlockEventForms data.boundaryOrientedInputCell kind exponent
      sector (adjugate (RawParser.parse current.core.word).matrix) =
        [left, right]) :
    0 < boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  let radialFaces := radialEventFaces kind exponent matrix
  let sectorFaces := sectorEventFaces sector normalized
  let radialActive := activeOrientedFaceForms cell radialFaces
  let sectorActive := activeOrientedFaceForms cell sectorFaces
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have matrixDeterminant : determinant matrix ≠ 0 := by
    dsimp only [matrix]
    rw [determinant_adjugate]
    exact stateDeterminant
  have radialClassified : ∀ face ∈ radialFaces,
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials state data.boundaryPathCylinder.path := by
    intro face member
    exact target.classified face
      (by
        apply List.mem_append_left
        simpa only [radialFaces, sectorFaces, blockEventFaces, normalized,
          matrix, state] using member)
  have sectorClassified : ∀ face ∈ sectorFaces,
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials state data.boundaryPathCylinder.path := by
    intro face member
    exact target.classified face
      (by
        apply List.mem_append_right
        simpa only [radialFaces, sectorFaces, blockEventFaces, normalized,
          matrix, state] using member)
  have radialLength : radialActive.length ≤ 1 := by
    have bound := activeRadialEventForms_length_le_one data kind exponent
      (by simpa only [radialFaces, matrix, state] using radialClassified)
    simpa only [radialActive, radialFaces, cell, matrix, state] using bound
  have appendPair : radialActive ++ sectorActive = [left, right] := by
    simpa only [activeBlockEventForms, blockEventFaces,
      activeOrientedFaceForms, List.filter_append, List.map_append,
      radialActive, sectorActive, radialFaces, sectorFaces, normalized, cell,
      matrix, state] using pair
  generalize radialEquality : radialActive = actualRadial at appendPair radialLength
  cases actualRadial with
  | nil =>
      have sectorPair : sectorActive = [left, right] := by
        simpa using appendPair
      apply activeSectorEventForms_pair_angleGap data kind exponent sector
        (by simpa only [sectorFaces, normalized, matrix, state] using
          sectorClassified)
      simpa only [sectorActive, sectorFaces, normalized, cell, matrix, state]
        using sectorPair
  | cons radial tail =>
      have tailNil : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest => simp at radialLength
      subst tail
      simp only [List.cons_append] at appendPair
      injection appendPair with radialEq sectorPair
      subst left
      simp only [List.nil_append] at sectorPair
      have radialMember : radial ∈ radialActive := by
        rw [radialEquality]
        simp
      rcases List.mem_map.mp radialMember with
        ⟨radialFace, radialFiltered, radialForm⟩
      rcases List.mem_filter.mp radialFiltered with
        ⟨radialFaceMember, _radialChecked⟩
      have radialInteriorMember : radial ∈
          radialInteriorForms kind exponent matrix := by
        rw [← radialEventFaces_map_form]
        exact List.mem_map.mpr
          ⟨radialFace, radialFaceMember, radialForm⟩
      have rightMember : right ∈ sectorActive := by
        rw [sectorPair]
        simp
      rcases List.mem_map.mp rightMember with
        ⟨sectorFace, sectorFiltered, sectorForm⟩
      rcases List.mem_filter.mp sectorFiltered with
        ⟨sectorFaceMember, _sectorChecked⟩
      have sectorInteriorMember : right ∈
          sectorInteriorForms sector normalized := by
        rw [← sectorEventFaces_map_form]
        exact List.mem_map.mpr
          ⟨sectorFace, sectorFaceMember, sectorForm⟩
      exact radialInterior_sectorInterior_angleGap_pos kind exponent sector
        matrix matrixDeterminant radialInteriorMember sectorInteriorMember

theorem activeBlockEventForms_boundaryDiscriminant_neg
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    {form : HermitianForm}
    (member : form ∈ activeBlockEventForms data.boundaryOrientedInputCell
      kind exponent sector
        (adjugate (RawParser.parse current.core.word).matrix)) :
    boundaryDiscriminant form < 0 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have matrixDeterminant : determinant matrix ≠ 0 := by
    dsimp only [matrix]
    rw [determinant_adjugate]
    exact stateDeterminant
  have normalizedDeterminant : determinant normalized ≠ 0 :=
    FTA.CCLCompleteOwnerShapes.normalizedMatrix_determinant_ne_of kind
      exponent matrix matrixDeterminant
  rcases List.mem_map.mp member with ⟨face, filtered, rfl⟩
  rcases List.mem_filter.mp filtered with ⟨faceMember, _checked⟩
  rcases List.mem_append.mp faceMember with radialMember | sectorMember
  · apply radialInteriorForm_boundaryDiscriminant_neg kind exponent matrix
      matrixDeterminant
    rw [← radialEventFaces_map_form]
    exact List.mem_map.mpr ⟨face, radialMember, rfl⟩
  · apply sectorInteriorForm_boundaryDiscriminant_neg sector normalized
      normalizedDeterminant
    rw [← sectorEventFaces_map_form]
    exact List.mem_map.mpr ⟨face, sectorMember, rfl⟩

private theorem
    activeSectorTwoEventForms_length_le_one_of_radialChecked
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (radialFace : EventOrientedFace)
    (radialMember : radialFace ∈ radialEventFaces kind exponent
      (adjugate (RawParser.parse current.core.word).matrix))
    (radialChecked : decide
      (radialFace.canonicalValue data.boundaryOrientedInputCell = 0) = true)
    (radialClassified : clearedForm radialFace.source
        data.boundaryPathCylinder.path ∈
      inputEventPolynomials (RawParser.parse current.core.word)
        data.boundaryPathCylinder.path)
    (sectorClassified : ∀ face ∈ sectorTwoEventFaces first second
      (normalizedMatrix kind exponent
        (adjugate (RawParser.parse current.core.word).matrix)),
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials (RawParser.parse current.core.word)
          data.boundaryPathCylinder.path) :
    (activeOrientedFaceForms data.boundaryOrientedInputCell
      (sectorTwoEventFaces first second
        (normalizedMatrix kind exponent
          (adjugate (RawParser.parse current.core.word).matrix)))).length ≤ 1 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  change (activeOrientedFaceForms cell
    (sectorTwoEventFaces first second normalized)).length ≤ 1
  cases first <;> cases second
  · have realClassified := sectorClassified
      (eventRealFace true normalized (1 / 2))
      (by simp [sectorTwoEventFaces, normalized, matrix, state])
    have imagClassified := sectorClassified
      (eventImagFace true normalized (-1 / 2))
      (by simp [sectorTwoEventFaces, normalized, matrix, state])
    have notBoth := radialEventFace_sectorCorner_checks_not_both data kind
      exponent radialFace radialMember radialChecked true true (1 / 2)
        (-1 / 2)
      (by intro radius radiusCase
          rcases radiusCase with rfl | rfl <;> norm_num)
      radialClassified realClassified imagClassified
    rw [activeOrientedFaceForms, List.length_map]
    exact filter_pair_length_le_one_of_not_both _ _ _ notBoth
  · have realClassified := sectorClassified
      (eventRealFace false normalized (1 / 2))
      (by simp [sectorTwoEventFaces, normalized, matrix, state])
    have imagClassified := sectorClassified
      (eventImagFace true normalized (1 / 2))
      (by simp [sectorTwoEventFaces, normalized, matrix, state])
    have notBoth := radialEventFace_sectorCorner_checks_not_both data kind
      exponent radialFace radialMember radialChecked false true (1 / 2)
        (1 / 2)
      (by intro radius radiusCase
          rcases radiusCase with rfl | rfl <;> norm_num)
      radialClassified realClassified imagClassified
    rw [activeOrientedFaceForms, List.length_map]
    exact filter_pair_length_le_one_of_not_both _ _ _ notBoth
  · have realClassified := sectorClassified
      (eventRealFace false normalized (-1 / 2))
      (by simp [sectorTwoEventFaces, normalized, matrix, state])
    have imagClassified := sectorClassified
      (eventImagFace false normalized (1 / 2))
      (by simp [sectorTwoEventFaces, normalized, matrix, state])
    have notBoth := radialEventFace_sectorCorner_checks_not_both data kind
      exponent radialFace radialMember radialChecked false false (-1 / 2)
        (1 / 2)
      (by intro radius radiusCase
          rcases radiusCase with rfl | rfl <;> norm_num)
      radialClassified realClassified imagClassified
    rw [activeOrientedFaceForms, List.length_map]
    exact filter_pair_length_le_one_of_not_both _ _ _ notBoth
  · have realClassified := sectorClassified
      (eventRealFace true normalized (-1 / 2))
      (by simp [sectorTwoEventFaces, normalized, matrix, state])
    have imagClassified := sectorClassified
      (eventImagFace false normalized (-1 / 2))
      (by simp [sectorTwoEventFaces, normalized, matrix, state])
    have notBoth := radialEventFace_sectorCorner_checks_not_both data kind
      exponent radialFace radialMember radialChecked true false (-1 / 2)
        (-1 / 2)
      (by intro radius radiusCase
          rcases radiusCase with rfl | rfl <;> norm_num)
      radialClassified realClassified imagClassified
    rw [activeOrientedFaceForms, List.length_map]
    exact filter_pair_length_le_one_of_not_both _ _ _ notBoth

theorem activeBlockSectorTwoEventForms_length_le_two
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (target : CanonicalOrientedTarget data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix))) :
    (activeOrientedFaceForms data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix))).length ≤ 2 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  let check := fun face : EventOrientedFace =>
    decide (face.canonicalValue cell = 0)
  let radialFaces := radialEventFaces kind exponent matrix
  let sectorFaces := sectorTwoEventFaces first second normalized
  have radialClassified : ∀ face ∈ radialFaces,
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials state data.boundaryPathCylinder.path := by
    intro face member
    exact target.classified face
      (by
        apply List.mem_append_left
        simpa only [radialFaces, sectorFaces, blockSectorTwoEventFaces,
          normalized, matrix, state] using member)
  have sectorClassified : ∀ face ∈ sectorFaces,
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials state data.boundaryPathCylinder.path := by
    intro face member
    exact target.classified face
      (by
        apply List.mem_append_right
        simpa only [radialFaces, sectorFaces, blockSectorTwoEventFaces,
          normalized, matrix, state] using member)
  have radialLength : (radialFaces.filter check).length ≤ 1 := by
    have bound := activeRadialEventForms_length_le_one data kind exponent
      (by simpa only [radialFaces, matrix, state] using radialClassified)
    simpa only [activeOrientedFaceForms, List.length_map, radialFaces, check,
      cell, matrix, state] using bound
  have sectorLength : (sectorFaces.filter check).length ≤ 2 := by
    have bound := List.length_filter_le check sectorFaces
    cases first <;> cases second <;>
      simpa [sectorFaces, sectorTwoEventFaces] using bound
  change (((radialFaces ++ sectorFaces).filter check).map
    EventOrientedFace.form).length ≤ 2
  rw [List.filter_append, List.map_append, List.length_append,
    List.length_map, List.length_map]
  generalize radialEquality : radialFaces.filter check = radialActive
  cases radialActive with
  | nil =>
      simpa using sectorLength
  | cons radialFace tail =>
      have tailNil : tail = [] := by
        rw [radialEquality] at radialLength
        cases tail with
        | nil => rfl
        | cons next rest => simp at radialLength
      subst tail
      have radialFiltered : radialFace ∈ radialFaces.filter check := by
        rw [radialEquality]
        simp
      rcases List.mem_filter.mp radialFiltered with
        ⟨radialMember, radialChecked⟩
      have sectorOne :=
        activeSectorTwoEventForms_length_le_one_of_radialChecked data kind
          exponent first second radialFace
          (by simpa only [radialFaces, matrix, state] using radialMember)
          (by simpa only [check, cell] using radialChecked)
          (radialClassified radialFace radialMember)
          (by simpa only [sectorFaces, normalized, matrix, state] using
            sectorClassified)
      have sectorFilteredLength : (sectorFaces.filter check).length ≤ 1 := by
        simpa only [activeOrientedFaceForms, List.length_map, sectorFaces,
          check, cell, normalized, matrix, state] using sectorOne
      simp only [List.length_cons, List.length_nil]
      omega

theorem activeBlockSectorTwoEventForms_pair_angleGap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (target : CanonicalOrientedTarget data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix)))
    {left right : HermitianForm}
    (pair : activeOrientedFaceForms data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix)) =
        [left, right]) :
    0 < boundaryDiscriminant left * boundaryDiscriminant right -
      2 * gradientPairingConstant left right ^ 2 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  let cell := data.boundaryOrientedInputCell
  let radialFaces := radialEventFaces kind exponent matrix
  let sectorFaces := sectorTwoEventFaces first second normalized
  let radialActive := activeOrientedFaceForms cell radialFaces
  let sectorActive := activeOrientedFaceForms cell sectorFaces
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have matrixDeterminant : determinant matrix ≠ 0 := by
    dsimp only [matrix]
    rw [determinant_adjugate]
    exact stateDeterminant
  have radialClassified : ∀ face ∈ radialFaces,
      clearedForm face.source data.boundaryPathCylinder.path ∈
        inputEventPolynomials state data.boundaryPathCylinder.path := by
    intro face member
    exact target.classified face
      (by
        apply List.mem_append_left
        simpa only [radialFaces, sectorFaces, blockSectorTwoEventFaces,
          normalized, matrix, state] using member)
  have radialLength : radialActive.length ≤ 1 := by
    have bound := activeRadialEventForms_length_le_one data kind exponent
      (by simpa only [radialFaces, matrix, state] using radialClassified)
    simpa only [radialActive, radialFaces, cell, matrix, state] using bound
  have appendPair : radialActive ++ sectorActive = [left, right] := by
    simpa only [activeOrientedFaceForms, blockSectorTwoEventFaces,
      List.filter_append, List.map_append, radialActive, sectorActive,
      radialFaces, sectorFaces, normalized, cell, matrix, state] using pair
  generalize radialEquality : radialActive = actualRadial at appendPair radialLength
  cases actualRadial with
  | nil =>
      have sectorPair : sectorActive = [left, right] := by
        simpa using appendPair
      apply activeSectorTwoEventForms_pair_angleGap data kind exponent first
        second
      simpa only [sectorActive, sectorFaces, normalized, cell, matrix, state]
        using sectorPair
  | cons radial tail =>
      have tailNil : tail = [] := by
        cases tail with
        | nil => rfl
        | cons next rest => simp at radialLength
      subst tail
      simp only [List.cons_append] at appendPair
      injection appendPair with radialEq sectorPair
      subst left
      simp only [List.nil_append] at sectorPair
      have radialMember : radial ∈ radialActive := by
        rw [radialEquality]
        simp
      rcases List.mem_map.mp radialMember with
        ⟨radialFace, radialFiltered, radialForm⟩
      rcases List.mem_filter.mp radialFiltered with
        ⟨radialFaceMember, _radialChecked⟩
      have radialInteriorMember : radial ∈
          radialInteriorForms kind exponent matrix := by
        rw [← radialEventFaces_map_form]
        exact List.mem_map.mpr
          ⟨radialFace, radialFaceMember, radialForm⟩
      have rightMember : right ∈ sectorActive := by
        rw [sectorPair]
        simp
      rcases List.mem_map.mp rightMember with
        ⟨sectorFace, sectorFiltered, sectorForm⟩
      rcases List.mem_filter.mp sectorFiltered with
        ⟨sectorFaceMember, _sectorChecked⟩
      have sectorInteriorMember : right ∈
          (sectorTwoEventFaces first second normalized).map
            EventOrientedFace.form :=
        List.mem_map.mpr ⟨sectorFace, sectorFaceMember, sectorForm⟩
      exact radialInterior_sectorInterior_angleGap_pos kind exponent
        (sectorTwoAxis first second) matrix matrixDeterminant
          radialInteriorMember
          (sectorTwoEventForm_mem_axisInterior first second normalized
            sectorInteriorMember)

theorem activeBlockSectorTwoEventForms_boundaryDiscriminant_neg
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    {form : HermitianForm}
    (member : form ∈ activeOrientedFaceForms
      data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix))) :
    boundaryDiscriminant form < 0 := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let normalized := normalizedMatrix kind exponent matrix
  have stateDeterminant : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have matrixDeterminant : determinant matrix ≠ 0 := by
    dsimp only [matrix]
    rw [determinant_adjugate]
    exact stateDeterminant
  have normalizedDeterminant : determinant normalized ≠ 0 :=
    FTA.CCLCompleteOwnerShapes.normalizedMatrix_determinant_ne_of kind
      exponent matrix matrixDeterminant
  rcases List.mem_map.mp member with ⟨face, filtered, rfl⟩
  rcases List.mem_filter.mp filtered with ⟨faceMember, _checked⟩
  rcases List.mem_append.mp faceMember with radialMember | sectorMember
  · apply radialInteriorForm_boundaryDiscriminant_neg kind exponent matrix
      matrixDeterminant
    rw [← radialEventFaces_map_form]
    exact List.mem_map.mpr ⟨face, radialMember, rfl⟩
  · apply sectorInteriorForm_boundaryDiscriminant_neg
      (sectorTwoAxis first second) normalized normalizedDeterminant
    apply sectorTwoEventForm_mem_axisInterior first second normalized
    exact List.mem_map.mpr ⟨face, sectorMember, rfl⟩

private theorem clearedForm_mem_inputEventPolynomials_of_sectorZeroRadialFace
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (path : ProjectivePath.Path) (face : EventOrientedFace)
    (member : face ∈ radialEventFaces kind exponent
      (adjugate matrix)) :
    clearedForm face.source path ∈ inputEventPolynomials
      ⟨.sector kind exponent .zero, matrix, history⟩ path := by
  cases kind with
  | initialHigh =>
      simp only [radialEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl <;>
        simp [eventNormFace, inputEventPolynomials, eventFormulaPolynomials,
          inputAdvanceFormula, advanceFormula, stateFormula, activeFormula,
          sectorBitsFormula, radialFormula, Formula.pullback, formulaAtoms,
          RawParser.step, pullbackForm_normComparison, RawParser.identityMatrix,
          Mat2.mul, adjugate]
  | initialLow =>
      simp only [radialEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl <;>
        simp [eventNormFace, inputEventPolynomials, eventFormulaPolynomials,
          inputAdvanceFormula, advanceFormula, stateFormula, activeFormula,
          sectorBitsFormula, radialFormula, Formula.pullback, formulaAtoms,
          RawParser.step, pullbackForm_normComparison, RawParser.identityMatrix,
          Mat2.mul, adjugate]
  | loop =>
      simp only [radialEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl <;>
        simp [eventNormFace, inputEventPolynomials, eventFormulaPolynomials,
          inputAdvanceFormula, advanceFormula, stateFormula, activeFormula,
          sectorBitsFormula, radialFormula, Formula.pullback, formulaAtoms,
          RawParser.step, pullbackForm_normComparison, RawParser.identityMatrix,
          Mat2.mul, adjugate]

private theorem clearedForm_mem_inputEventPolynomials_of_sectorZeroSectorFace
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (path : ProjectivePath.Path) (face : EventOrientedFace)
    (member : face ∈ sectorEventFaces sector
      (normalizedMatrix kind exponent (adjugate matrix))) :
    clearedForm face.source path ∈ inputEventPolynomials
      ⟨.sector kind exponent .zero, matrix, history⟩ path := by
  cases sector with
  | east =>
      simp only [sectorEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl | rfl <;>
        simp [eventRealFace, eventImagFace, inputEventPolynomials,
          eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
          stateFormula, activeFormula, sectorBitsFormula, radialFormula,
          Formula.pullback, formulaAtoms, RawParser.step,
          pullbackForm_realComparison,
          pullbackForm_imagComparison, normalizedMatrix, normalizationMatrix,
          RawParser.identityMatrix, Mat2.mul, adjugate]
  | northEast =>
      simp only [sectorEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl <;>
        simp [eventRealFace, eventImagFace, inputEventPolynomials,
          eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
          stateFormula, activeFormula, sectorBitsFormula, radialFormula,
          Formula.pullback, formulaAtoms, RawParser.step,
          pullbackForm_realComparison,
          pullbackForm_imagComparison, normalizedMatrix, normalizationMatrix,
          RawParser.identityMatrix, Mat2.mul, adjugate]
  | north =>
      simp only [sectorEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl | rfl <;>
        simp [eventRealFace, eventImagFace, inputEventPolynomials,
          eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
          stateFormula, activeFormula, sectorBitsFormula, radialFormula,
          Formula.pullback, formulaAtoms, RawParser.step,
          pullbackForm_realComparison,
          pullbackForm_imagComparison, normalizedMatrix, normalizationMatrix,
          RawParser.identityMatrix, Mat2.mul, adjugate]
  | northWest =>
      simp only [sectorEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl <;>
        simp [eventRealFace, eventImagFace, inputEventPolynomials,
          eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
          stateFormula, activeFormula, sectorBitsFormula, radialFormula,
          Formula.pullback, formulaAtoms, RawParser.step,
          pullbackForm_realComparison,
          pullbackForm_imagComparison, normalizedMatrix, normalizationMatrix,
          RawParser.identityMatrix, Mat2.mul, adjugate]
  | west =>
      simp only [sectorEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl | rfl <;>
        simp [eventRealFace, eventImagFace, inputEventPolynomials,
          eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
          stateFormula, activeFormula, sectorBitsFormula, radialFormula,
          Formula.pullback, formulaAtoms, RawParser.step,
          pullbackForm_realComparison,
          pullbackForm_imagComparison, normalizedMatrix, normalizationMatrix,
          RawParser.identityMatrix, Mat2.mul, adjugate]
  | southWest =>
      simp only [sectorEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl <;>
        simp [eventRealFace, eventImagFace, inputEventPolynomials,
          eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
          stateFormula, activeFormula, sectorBitsFormula, radialFormula,
          Formula.pullback, formulaAtoms, RawParser.step,
          pullbackForm_realComparison,
          pullbackForm_imagComparison, normalizedMatrix, normalizationMatrix,
          RawParser.identityMatrix, Mat2.mul, adjugate]
  | south =>
      simp only [sectorEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl | rfl <;>
        simp [eventRealFace, eventImagFace, inputEventPolynomials,
          eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
          stateFormula, activeFormula, sectorBitsFormula, radialFormula,
          Formula.pullback, formulaAtoms, RawParser.step,
          pullbackForm_realComparison,
          pullbackForm_imagComparison, normalizedMatrix, normalizationMatrix,
          RawParser.identityMatrix, Mat2.mul, adjugate]
  | southEast =>
      simp only [sectorEventFaces, List.mem_cons, List.not_mem_nil, or_false]
        at member
      rcases member with rfl | rfl <;>
        simp [eventRealFace, eventImagFace, inputEventPolynomials,
          eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
          stateFormula, activeFormula, sectorBitsFormula, radialFormula,
          Formula.pullback, formulaAtoms, RawParser.step,
          pullbackForm_realComparison,
          pullbackForm_imagComparison, normalizedMatrix, normalizationMatrix,
          RawParser.identityMatrix, Mat2.mul, adjugate]

/-- At the zero-bit sector phase, the pair of child formulas classifies every
source comparison used by every possible full successor row.  This proof is
row-local: it never expands the eight-way current formula. -/
theorem clearedForm_mem_inputEventPolynomials_of_sectorZeroBlockFace
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (path : ProjectivePath.Path) (face : EventOrientedFace)
    (member : face ∈ blockEventFaces kind exponent sector
      (adjugate matrix)) :
    clearedForm face.source path ∈ inputEventPolynomials
      ⟨.sector kind exponent .zero, matrix, history⟩ path := by
  rcases List.mem_append.mp member with radial | angular
  · exact
      clearedForm_mem_inputEventPolynomials_of_sectorZeroRadialFace kind
        exponent matrix history path face radial
  · exact
      clearedForm_mem_inputEventPolynomials_of_sectorZeroSectorFace kind
        exponent sector matrix history path face angular

theorem clearedForm_mem_inputEventPolynomials_of_sectorZeroBlockFace_of_phase
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (sector : Sector) (path : ProjectivePath.Path)
    (phase : state.phase = .sector kind exponent .zero)
    (face : EventOrientedFace)
    (member : face ∈ blockEventFaces kind exponent sector
      (adjugate state.matrix)) :
    clearedForm face.source path ∈ inputEventPolynomials state path := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  exact clearedForm_mem_inputEventPolynomials_of_sectorZeroBlockFace kind
    exponent sector matrix history path face member

/-- Uniform source list used before the compatible zero-prefix sector row is
known.  Repetition is harmless and keeps membership proofs structural. -/
def sectorZeroEventSourceForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    List HermitianForm :=
  (RawParser.sectorCandidates .zero).flatMap fun sector =>
    blockEventSourceForms kind exponent sector matrix

theorem blockEventFace_source_mem_sectorZeroEventSourceForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) (face : EventOrientedFace)
    (member : face ∈ blockEventFaces kind exponent sector matrix) :
    face.source ∈ sectorZeroEventSourceForms kind exponent matrix := by
  apply List.mem_flatMap.mpr
  refine ⟨sector, ?_, ?_⟩
  · cases sector <;> native_decide
  · exact List.mem_map.mpr ⟨face, member, rfl⟩

/-- A sufficiently close persistent active sample supplies one full sector
row whose entire exact event orientation is weakly inward.  The row is a
finite witness to the later canonical-table search; it is not itself retained
as the controller's bit choice. -/
theorem exists_canonicalBlockTarget_of_sectorZero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent .zero) :
    ∃ sector ∈ RawParser.sectorCandidates .zero,
      CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent sector
        (adjugate (RawParser.parse current.core.word).matrix) := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let forms := sectorZeroEventSourceForms kind exponent matrix
  let strictRadius := convergentStrictRadius cell forms
  let radius := strictRadius / 2
  have strictRadiusPositive : 0 < strictRadius :=
    convergentStrictRadius_pos cell forms
  have radiusPositive : 0 < radius := by
    dsimp only [radius]
    linarith
  have radiusSmall : radius < convergentStrictRadius cell forms := by
    dsimp only [radius, strictRadius]
    linarith
  let inner := refineState squarefree elimination data.output.state radius
    radiusPositive
  have innerRefinesCurrent : inner.box.Refines current.core.numerical.box := by
    apply (refineState_refines squarefree elimination data.output.state radius
      radiusPositive).trans
    exact data.output_refines_separation.trans data.separation.refines
  let sample := current.samples.sample inner innerRefinesCurrent
  have active := sample.tail_active
  rw [phase] at active
  rcases active with ⟨radial, sector, sectorMember, sectorHolds⟩
  refine ⟨sector, sectorMember, ?_⟩
  let tail := RatBox.homographic matrix sample.point
  have radialClosure : RadialClosureHolds kind exponent tail :=
    radialClosureHolds_of_radialBracket kind exponent tail radial
  have sectorClosure : SectorClosureHolds sector
      (RawParser.normalizedValue kind exponent tail) :=
    sectorClosureHolds_of_holds sector _ sectorHolds
  have denominator : matrix.c * sample.point + matrix.d ≠ 0 := by
    simpa only [matrix, state] using sample.inverseDenominator
  have inward : ∀ form ∈
      blockSectorInteriorForms kind exponent sector matrix,
      0 ≤ form.eval sample.point := by
    intro form member
    rcases List.mem_append.mp member with radialMember | sectorMember
    · exact radialInteriorForms_nonneg_of_closure kind exponent matrix
        sample.point denominator radialClosure form radialMember
    · let normalized := normalizedMatrix kind exponent matrix
      have normalizedDenominator :
          normalized.c * sample.point + normalized.d ≠ 0 := by
        have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
        simpa only [normalized, lowerRow.1, lowerRow.2] using denominator
      have closureAt : SectorClosureHolds sector
          (RatBox.homographic normalized sample.point) := by
        simpa only [normalized, tail, homographic_normalizedMatrix] using
          sectorClosure
      exact sectorInteriorForms_nonneg_of_closure sector normalized
        sample.point normalizedDenominator closureAt form sectorMember
  change CanonicalBlockTarget cell kind exponent sector matrix
  apply canonicalBlockTargetOfInnerSample cell kind exponent sector matrix forms
    squarefree degreeNonzero elimination data.output.state
    data.output_refines_separation radius radiusPositive radiusSmall
    sample.point
  · simpa only [inner] using sample.inside
  · intro face faceMember
    exact blockEventFace_source_mem_sectorZeroEventSourceForms kind exponent
      sector matrix face faceMember
  · intro face faceMember
    exact
      clearedForm_mem_inputEventPolynomials_of_sectorZeroBlockFace_of_phase
        state kind exponent sector _ phase face faceMember
  · exact inward

/-- Executable test that every oriented face of one full block row is weakly
inward in the exact event's canonical sign table. -/
def canonicalBlockTargetCheck
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) : Bool :=
  (blockEventFaces kind exponent sector matrix).all fun face =>
    decide (0 ≤ face.canonicalValue cell)

theorem canonicalBlockTargetCheck_eq_true_iff
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (matrix : Mat2 QI) :
    canonicalBlockTargetCheck cell kind exponent sector matrix = true ↔
      ∀ face ∈ blockEventFaces kind exponent sector matrix,
        0 ≤ face.canonicalValue cell := by
  simp [canonicalBlockTargetCheck]

def canonicalSectorZeroCandidates
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (matrix : Mat2 QI) :
    List Sector :=
  (RawParser.sectorCandidates .zero).filter fun sector =>
    canonicalBlockTargetCheck cell kind exponent sector matrix

structure SectorZeroCanonicalSelection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) where
  sector : Sector
  candidate : sector ∈ RawParser.sectorCandidates .zero
  target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
    sector (adjugate (RawParser.parse current.core.word).matrix)

/-- Choose the first compatible row using only the exact event's finite
canonical table.  The analytical arguments occur solely in the proof that
the filtered list is nonempty. -/
def sectorZeroCanonicalSelection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent .zero) :
    SectorZeroCanonicalSelection data kind exponent := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let candidates := canonicalSectorZeroCandidates cell kind exponent matrix
  have candidatesNonempty : candidates ≠ [] := by
    rcases exists_canonicalBlockTarget_of_sectorZero data squarefree
        degreeNonzero elimination kind exponent phase with
      ⟨sector, sectorMember, target⟩
    intro empty
    have member : sector ∈ candidates := by
      apply List.mem_filter.mpr
      exact ⟨sectorMember,
        (canonicalBlockTargetCheck_eq_true_iff cell kind exponent sector
          matrix).2 target.canonicalNonnegative⟩
    rw [empty] at member
    simp at member
  let sector := candidates.head candidatesNonempty
  have selected := List.head_mem candidatesNonempty
  have selectedParts := List.mem_filter.mp selected
  refine
    { sector := sector
      candidate := selectedParts.1
      target := ?_ }
  refine
    { classified := ?_
      canonicalNonnegative :=
        (canonicalBlockTargetCheck_eq_true_iff cell kind exponent sector
          matrix).1 selectedParts.2 }
  intro face faceMember
  exact clearedForm_mem_inputEventPolynomials_of_sectorZeroBlockFace_of_phase
    state kind exponent sector _ phase face faceMember

private theorem clearedForm_mem_inputEventPolynomials_of_sectorOneRadialFace
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (path : ProjectivePath.Path) (face : EventOrientedFace)
    (member : face ∈ radialEventFaces kind exponent (adjugate matrix)) :
    clearedForm face.source path ∈ inputEventPolynomials
      ⟨.sector kind exponent (.one first), matrix, history⟩ path := by
  cases first <;> cases kind <;>
    simp only [radialEventFaces, List.mem_cons, List.not_mem_nil, or_false]
      at member <;>
    rcases member with rfl | rfl <;>
    simp [eventNormFace, inputEventPolynomials, eventFormulaPolynomials,
      inputAdvanceFormula, advanceFormula, stateFormula, activeFormula,
      sectorBitsFormula, radialFormula, Formula.pullback, formulaAtoms,
      RawParser.step, pullbackForm_normComparison, RawParser.identityMatrix,
      Mat2.mul, adjugate]

private theorem clearedForm_mem_inputEventPolynomials_of_sectorOneTwoFace
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (path : ProjectivePath.Path) (face : EventOrientedFace)
    (member : face ∈ sectorTwoEventFaces first second
      (normalizedMatrix kind exponent (adjugate matrix))) :
    clearedForm face.source path ∈ inputEventPolynomials
      ⟨.sector kind exponent (.one first), matrix, history⟩ path := by
  cases first <;> cases second <;>
    simp only [sectorTwoEventFaces, List.mem_cons, List.not_mem_nil, or_false]
      at member <;>
    rcases member with rfl | rfl <;>
    simp [eventRealFace, eventImagFace, inputEventPolynomials,
      eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
      stateFormula, activeFormula, sectorBitsFormula, radialFormula,
      Formula.pullback, formulaAtoms, RawParser.step,
      pullbackForm_realComparison, pullbackForm_imagComparison,
      normalizedMatrix, normalizationMatrix, RawParser.identityMatrix,
      Mat2.mul, adjugate]

theorem clearedForm_mem_inputEventPolynomials_of_sectorOneBlockTwoFace
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (matrix : Mat2 QI) (history : List RawParser.Constraint)
    (path : ProjectivePath.Path) (face : EventOrientedFace)
    (member : face ∈ blockSectorTwoEventFaces kind exponent first second
      (adjugate matrix)) :
    clearedForm face.source path ∈ inputEventPolynomials
      ⟨.sector kind exponent (.one first), matrix, history⟩ path := by
  rcases List.mem_append.mp member with radial | angular
  · exact clearedForm_mem_inputEventPolynomials_of_sectorOneRadialFace kind
      exponent first matrix history path face radial
  · exact clearedForm_mem_inputEventPolynomials_of_sectorOneTwoFace kind
      exponent first second matrix history path face angular

theorem
    clearedForm_mem_inputEventPolynomials_of_sectorOneBlockTwoFace_of_phase
    (state : RawParser.State) (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second : Bool) (path : ProjectivePath.Path)
    (phase : state.phase = .sector kind exponent (.one first))
    (face : EventOrientedFace)
    (member : face ∈ blockSectorTwoEventFaces kind exponent first second
      (adjugate state.matrix)) :
    clearedForm face.source path ∈ inputEventPolynomials state path := by
  rcases state with ⟨statePhase, matrix, history⟩
  simp only at phase
  subst statePhase
  exact clearedForm_mem_inputEventPolynomials_of_sectorOneBlockTwoFace kind
    exponent first second matrix history path face member

private theorem sector_mem_two_secondProjection
    (first : Bool) (sector : Sector)
    (member : sector ∈ RawParser.sectorCandidates (.one first)) :
    sector ∈ RawParser.sectorCandidates
      (.two first (sectorSecondBit sector)) := by
  cases first <;> cases sector <;> simp_all [sectorSecondBit]

private def SectorTwoClosureHolds : Bool → Bool → QI → Prop
  | false, false, z => 1 / 2 ≤ z.re ∧ -1 / 2 ≤ z.im
  | false, true, z => z.re ≤ 1 / 2 ∧ 1 / 2 ≤ z.im
  | true, false, z => z.re ≤ -1 / 2 ∧ z.im ≤ 1 / 2
  | true, true, z => -1 / 2 ≤ z.re ∧ z.im ≤ -1 / 2

private theorem sectorTwoClosureHolds_of_sectorClosure
    (first second : Bool) (sector : Sector) (z : QI)
    (sectorMember : sector ∈
      RawParser.sectorCandidates (.two first second))
    (closure : SectorClosureHolds sector z) :
    SectorTwoClosureHolds first second z := by
  cases first <;> cases second <;> cases sector <;>
    simp_all [SectorTwoClosureHolds, SectorClosureHolds] <;> linarith

private theorem sectorTwoEventFaces_nonneg_of_closure
    (first second : Bool) (sector : Sector) (matrix : Mat2 QI)
    (point : QI) (denominator : matrix.c * point + matrix.d ≠ 0)
    (sectorMember : sector ∈
      RawParser.sectorCandidates (.two first second))
    (closure : SectorClosureHolds sector
      (RatBox.homographic matrix point))
    (face : EventOrientedFace)
    (faceMember : face ∈ sectorTwoEventFaces first second matrix) :
    0 ≤ face.form.eval point := by
  have bounds := sectorTwoClosureHolds_of_sectorClosure first second sector
    (RatBox.homographic matrix point) sectorMember closure
  cases first <;> cases second <;>
    simp only [sectorTwoEventFaces, List.mem_cons, List.not_mem_nil, or_false]
      at faceMember <;>
    rcases faceMember with rfl | rfl
  · exact (orientedRealForm_eval_nonneg_iff true matrix (1 / 2) point
      denominator).2 bounds.1
  · exact (orientedImagForm_eval_nonneg_iff true matrix (-1 / 2) point
      denominator).2 bounds.2
  · exact (orientedRealForm_eval_nonneg_iff false matrix (1 / 2) point
      denominator).2 bounds.1
  · exact (orientedImagForm_eval_nonneg_iff true matrix (1 / 2) point
      denominator).2 bounds.2
  · exact (orientedRealForm_eval_nonneg_iff false matrix (-1 / 2) point
      denominator).2 bounds.1
  · exact (orientedImagForm_eval_nonneg_iff false matrix (1 / 2) point
      denominator).2 bounds.2
  · exact (orientedRealForm_eval_nonneg_iff true matrix (-1 / 2) point
      denominator).2 bounds.1
  · exact (orientedImagForm_eval_nonneg_iff false matrix (-1 / 2) point
      denominator).2 bounds.2

def sectorOneEventSourceForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (matrix : Mat2 QI) : List HermitianForm :=
  [false, true].flatMap fun second =>
    orientedFaceSourceForms
      (blockSectorTwoEventFaces kind exponent first second matrix)

theorem blockSectorTwoEventFace_source_mem_sectorOneEventSourceForms
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (matrix : Mat2 QI) (face : EventOrientedFace)
    (member : face ∈
      blockSectorTwoEventFaces kind exponent first second matrix) :
    face.source ∈ sectorOneEventSourceForms kind exponent first matrix := by
  apply List.mem_flatMap.mpr
  refine ⟨second, ?_, ?_⟩
  · cases second <;> simp
  · exact List.mem_map.mpr ⟨face, member, rfl⟩

/-- One-prefix analogue of `exists_canonicalBlockTarget_of_sectorZero`.
Only the radial faces and the two walls of the resulting two-bit prefix are
retained; the future third-bit wall is deliberately absent. -/
theorem exists_canonicalOrientedTarget_of_sectorOne
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.one first)) :
    ∃ second,
      CanonicalOrientedTarget data.boundaryOrientedInputCell
        (blockSectorTwoEventFaces kind exponent first second
          (adjugate (RawParser.parse current.core.word).matrix)) := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let forms := sectorOneEventSourceForms kind exponent first matrix
  let strictRadius := convergentStrictRadius cell forms
  let radius := strictRadius / 2
  have strictRadiusPositive : 0 < strictRadius :=
    convergentStrictRadius_pos cell forms
  have radiusPositive : 0 < radius := by
    dsimp only [radius]
    linarith
  have radiusSmall : radius < convergentStrictRadius cell forms := by
    dsimp only [radius, strictRadius]
    linarith
  let inner := refineState squarefree elimination data.output.state radius
    radiusPositive
  have innerRefinesCurrent : inner.box.Refines current.core.numerical.box := by
    apply (refineState_refines squarefree elimination data.output.state radius
      radiusPositive).trans
    exact data.output_refines_separation.trans data.separation.refines
  let sample := current.samples.sample inner innerRefinesCurrent
  have active := sample.tail_active
  rw [phase] at active
  rcases active with ⟨radial, sector, sectorMember, sectorHolds⟩
  let second := sectorSecondBit sector
  have sectorTwoMember : sector ∈
      RawParser.sectorCandidates (.two first second) :=
    sector_mem_two_secondProjection first sector sectorMember
  refine ⟨second, ?_⟩
  let faces := blockSectorTwoEventFaces kind exponent first second matrix
  let tail := RatBox.homographic matrix sample.point
  have radialClosure : RadialClosureHolds kind exponent tail :=
    radialClosureHolds_of_radialBracket kind exponent tail radial
  have sectorClosure : SectorClosureHolds sector
      (RawParser.normalizedValue kind exponent tail) :=
    sectorClosureHolds_of_holds sector _ sectorHolds
  have denominator : matrix.c * sample.point + matrix.d ≠ 0 := by
    simpa only [matrix, state] using sample.inverseDenominator
  let normalized := normalizedMatrix kind exponent matrix
  have normalizedDenominator :
      normalized.c * sample.point + normalized.d ≠ 0 := by
    have lowerRow := normalizedMatrix_lowerRow kind exponent matrix
    simpa only [normalized, lowerRow.1, lowerRow.2] using denominator
  have closureAt : SectorClosureHolds sector
      (RatBox.homographic normalized sample.point) := by
    simpa only [normalized, tail, homographic_normalizedMatrix] using
      sectorClosure
  have fullInward : ∀ form ∈
      blockSectorInteriorForms kind exponent sector matrix,
      0 ≤ form.eval sample.point := by
    intro form member
    rcases List.mem_append.mp member with radialMember | sectorFormMember
    · exact radialInteriorForms_nonneg_of_closure kind exponent matrix
        sample.point denominator radialClosure form radialMember
    · exact sectorInteriorForms_nonneg_of_closure sector normalized
        sample.point normalizedDenominator closureAt form sectorFormMember
  change CanonicalOrientedTarget cell faces
  apply canonicalOrientedTargetOfInnerSample cell faces forms squarefree
    degreeNonzero elimination data.output.state data.output_refines_separation
    radius radiusPositive radiusSmall sample.point
  · simpa only [inner] using sample.inside
  · intro face faceMember
    exact blockSectorTwoEventFace_source_mem_sectorOneEventSourceForms kind
      exponent first second matrix face faceMember
  · intro face faceMember
    exact
      clearedForm_mem_inputEventPolynomials_of_sectorOneBlockTwoFace_of_phase
        state kind exponent first second _ phase face faceMember
  · intro face faceMember
    rcases List.mem_append.mp faceMember with radialFace | sectorFace
    · apply fullInward face.form
      apply List.mem_append_left
      rw [← radialEventFaces_map_form]
      exact List.mem_map.mpr ⟨face, radialFace, rfl⟩
    · exact sectorTwoEventFaces_nonneg_of_closure first second sector normalized
        sample.point normalizedDenominator sectorTwoMember closureAt face
          sectorFace

def canonicalOrientedTargetCheck
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (faces : List EventOrientedFace) : Bool :=
  faces.all fun face => decide (0 ≤ face.canonicalValue cell)

theorem canonicalOrientedTargetCheck_eq_true_iff
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (faces : List EventOrientedFace) :
    canonicalOrientedTargetCheck cell faces = true ↔
      ∀ face ∈ faces, 0 ≤ face.canonicalValue cell := by
  simp [canonicalOrientedTargetCheck]

def canonicalSectorOneSecondCandidates
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (matrix : Mat2 QI) : List Bool :=
  [false, true].filter fun second =>
    canonicalOrientedTargetCheck cell
      (blockSectorTwoEventFaces kind exponent first second matrix)

structure SectorOneCanonicalSelection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool) where
  second : Bool
  target : CanonicalOrientedTarget data.boundaryOrientedInputCell
    (blockSectorTwoEventFaces kind exponent first second
      (adjugate (RawParser.parse current.core.word).matrix))

def sectorOneCanonicalSelection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first : Bool)
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.one first)) :
    SectorOneCanonicalSelection data kind exponent first := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let candidates := canonicalSectorOneSecondCandidates cell kind exponent first
    matrix
  have candidatesNonempty : candidates ≠ [] := by
    rcases exists_canonicalOrientedTarget_of_sectorOne data squarefree
        degreeNonzero elimination kind exponent first phase with
      ⟨second, target⟩
    intro empty
    have member : second ∈ candidates := by
      apply List.mem_filter.mpr
      refine ⟨?_, ?_⟩
      · cases second <;> simp
      · exact (canonicalOrientedTargetCheck_eq_true_iff cell _).2
          target.canonicalNonnegative
    rw [empty] at member
    simp at member
  let second := candidates.head candidatesNonempty
  have selected := List.head_mem candidatesNonempty
  have selectedParts := List.mem_filter.mp selected
  refine
    { second := second
      target := ?_ }
  refine
    { classified := ?_
      canonicalNonnegative :=
        (canonicalOrientedTargetCheck_eq_true_iff cell _).1 selectedParts.2 }
  intro face faceMember
  exact
    clearedForm_mem_inputEventPolynomials_of_sectorOneBlockTwoFace_of_phase
      state kind exponent first second _ phase face faceMember

theorem activeBlockTangentResidualBudget_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
      sector (adjugate (RawParser.parse current.core.word).matrix)) :
    0 < tangentResidualBudget
      (activeBlockEventForms data.boundaryOrientedInputCell kind exponent sector
        (adjugate (RawParser.parse current.core.word).matrix)) := by
  let active := activeBlockEventForms data.boundaryOrientedInputCell kind
    exponent sector (adjugate (RawParser.parse current.core.word).matrix)
  apply tangentResidualBudget_pos_of_length_le_two active
  · exact activeBlockEventForms_length_le_two data kind exponent sector target
  · intro form member
    exact activeBlockEventForms_boundaryDiscriminant_neg data kind exponent
      sector member
  · intro left right pair
    exact activeBlockEventForms_pair_angleGap data kind exponent sector target
      pair

def activeBlockConvergentTangentRadius
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector) : ℚ :=
  convergentTangentRadius data.boundaryOrientedInputCell
    (blockEventSourceForms kind exponent sector
      (adjugate (RawParser.parse current.core.word).matrix))
    (activeBlockEventForms data.boundaryOrientedInputCell kind exponent sector
      (adjugate (RawParser.parse current.core.word).matrix))

theorem activeBlockConvergentTangentRadius_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
      sector (adjugate (RawParser.parse current.core.word).matrix)) :
    0 < activeBlockConvergentTangentRadius data kind exponent sector := by
  unfold activeBlockConvergentTangentRadius
  exact convergentTangentRadius_pos _ _ _
    (activeBlockTangentResidualBudget_pos data kind exponent sector target)

theorem activeBlockConvergentTangentDirection?_isSome
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
      sector (adjugate (RawParser.parse current.core.word).matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.separation.state.box) :
    (tangentDirectionCertificate?
      (activeBlockEventForms data.boundaryOrientedInputCell kind exponent sector
        (adjugate (RawParser.parse current.core.word).matrix))
      (convergentBoxCenter squarefree elimination next
        (activeBlockConvergentTangentRadius data kind exponent sector)
        (activeBlockConvergentTangentRadius_pos data kind exponent sector
          target))).isSome := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let sources := blockEventSourceForms kind exponent sector matrix
  let active := activeBlockEventForms cell kind exponent sector matrix
  let radius := activeBlockConvergentTangentRadius data kind exponent sector
  have budgetPositive : 0 < tangentResidualBudget active := by
    simpa only [active, cell, matrix, state] using
      activeBlockTangentResidualBudget_pos data kind exponent sector target
  have radiusPositive : 0 < radius := by
    simpa only [radius] using activeBlockConvergentTangentRadius_pos data kind
      exponent sector target
  have epsilonPositive :
      0 < convergentCoefficientSum cell sources * radius :=
    mul_pos (convergentCoefficientSum_pos cell sources) radiusPositive
  have epsilonSmall :
      convergentCoefficientSum cell sources * radius <
        tangentResidualBudget active := by
    simpa only [radius, activeBlockConvergentTangentRadius, sources, active,
      cell, matrix, state] using
      convergentCoefficientSum_mul_tangentRadius_lt_budget cell sources active
        budgetPositive
  have search : (tangentDirectionCertificate? active
      (convergentBoxCenter squarefree elimination next radius
        radiusPositive)).isSome := by
    apply tangentDirectionCertificate?_isSome_of_residual_lt_budget active
      (convergentBoxCenter squarefree elimination next radius radiusPositive)
      (convergentCoefficientSum cell sources * radius)
      (by
        simpa only [active, cell, matrix, state] using
          activeBlockEventForms_length_le_two data kind exponent sector target)
      epsilonPositive epsilonSmall
    · intro form formMember
      rcases List.mem_map.mp formMember with ⟨face, filtered, faceForm⟩
      rcases List.mem_filter.mp filtered with ⟨faceMember, checked⟩
      have sourceMember : face.source ∈ sources := by
        exact List.mem_map.mpr ⟨face, faceMember, rfl⟩
      have canonicalZero := sourceCanonicalZero_of_orientedCheck cell face
        checked
      have sourceResidual :=
        convergentBoxCenter_abs_eval_lt_sum_of_canonicalZero cell sources
          squarefree degreeNonzero elimination next nextRefines radius
          radiusPositive face.source sourceMember
          (by
            simpa only [state, matrix, data.boundaryPathCylinder_path] using
              target.classified face faceMember)
          canonicalZero
      subst form
      cases increasing : face.increasing <;>
        simp [EventOrientedFace.form, increasing] <;>
        exact sourceResidual
    · intro form formMember
      exact activeBlockEventForms_boundaryDiscriminant_neg data kind exponent
        sector (by simpa only [active, cell, matrix, state] using formMember)
    · intro left right pair
      exact activeBlockEventForms_pair_angleGap data kind exponent sector target
        (by simpa only [active, cell, matrix, state] using pair)
  simpa only [active, radius, cell, matrix, state] using search

theorem activeBlockTangentSlopeBudget_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
      sector (adjugate (RawParser.parse current.core.word).matrix))
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    0 < tangentSlopeBudget next.box
      (activeBlockEventForms data.boundaryOrientedInputCell kind exponent sector
        (adjugate (RawParser.parse current.core.word).matrix)) := by
  let active := activeBlockEventForms data.boundaryOrientedInputCell kind
    exponent sector (adjugate (RawParser.parse current.core.word).matrix)
  apply tangentSlopeBudget_pos_of_length_le_two next.box active
  · exact activeBlockEventForms_length_le_two data kind exponent sector target
  · intro form member
    exact activeBlockEventForms_boundaryDiscriminant_neg data kind exponent
      sector member
  · intro left right pair
    exact activeBlockEventForms_pair_angleGap data kind exponent sector target
      pair

def activeBlockConvergentSampleRadius
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (next : WindingOneState p (RatBox.symmetric R hR)) : ℚ :=
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let sources := blockEventSourceForms kind exponent sector matrix
  let active := activeBlockEventForms cell kind exponent sector matrix
  let priors := approximateBlockSectorBoxPriors active kind exponent sector
    matrix next.box
  convergentSampleRadius cell sources active priors next

theorem activeBlockConvergentSampleRadius_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
      sector (adjugate (RawParser.parse current.core.word).matrix))
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    0 < activeBlockConvergentSampleRadius data kind exponent sector next := by
  unfold activeBlockConvergentSampleRadius
  exact convergentSampleRadius_pos _ _ _ _ _
    (activeBlockTangentResidualBudget_pos data kind exponent sector target)
    (activeBlockTangentSlopeBudget_pos data kind exponent sector target next)

theorem activeBlockConvergentDirectionAbove?_isSome
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
      sector (adjugate (RawParser.parse current.core.word).matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.separation.state.box) :
    let state := RawParser.parse current.core.word
    let matrix := adjugate state.matrix
    let cell := data.boundaryOrientedInputCell
    let active := activeBlockEventForms cell kind exponent sector matrix
    let radius := activeBlockConvergentSampleRadius data kind exponent sector
      next
    let base := convergentBoxCenter squarefree elimination next radius
      (activeBlockConvergentSampleRadius_pos data kind exponent sector target
        next)
    (tangentDirectionAboveCertificate? active base
      (tangentSlopeBudget next.box active)).isSome := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let sources := blockEventSourceForms kind exponent sector matrix
  let active := activeBlockEventForms cell kind exponent sector matrix
  let priors := approximateBlockSectorBoxPriors active kind exponent sector
    matrix next.box
  let radius := activeBlockConvergentSampleRadius data kind exponent sector next
  have residualBudgetPositive : 0 < tangentResidualBudget active := by
    simpa only [active, cell, matrix, state] using
      activeBlockTangentResidualBudget_pos data kind exponent sector target
  have slopeBudgetPositive : 0 < tangentSlopeBudget next.box active := by
    simpa only [active, cell, matrix, state] using
      activeBlockTangentSlopeBudget_pos data kind exponent sector target next
  have radiusPositive : 0 < radius := by
    simpa only [radius] using activeBlockConvergentSampleRadius_pos data kind
      exponent sector target next
  let base := convergentBoxCenter squarefree elimination next radius
    radiusPositive
  have baseInside : next.box.Contains base := by
    have strict := convergentBoxCenter_strictContains squarefree elimination
      next radius radiusPositive
    exact ⟨strict.1.le, strict.2.1.le, strict.2.2.1.le,
      strict.2.2.2.le⟩
  have radiusLtTangent : radius <
      convergentTangentRadius cell sources active := by
    simpa only [radius, activeBlockConvergentSampleRadius, sources, active,
      priors, cell, matrix, state] using
      convergentSampleRadius_lt_tangentRadius cell sources active priors next
        residualBudgetPositive slopeBudgetPositive
  have epsilonPositive :
      0 < convergentCoefficientSum cell sources * radius :=
    mul_pos (convergentCoefficientSum_pos cell sources) radiusPositive
  have epsilonSmall : convergentCoefficientSum cell sources * radius <
      tangentResidualBudget active := by
    calc
      convergentCoefficientSum cell sources * radius <
          convergentCoefficientSum cell sources *
            convergentTangentRadius cell sources active :=
        mul_lt_mul_of_pos_left radiusLtTangent
          (convergentCoefficientSum_pos cell sources)
      _ < tangentResidualBudget active :=
        convergentCoefficientSum_mul_tangentRadius_lt_budget cell sources
          active residualBudgetPositive
  have search := tangentDirectionAboveCertificate?_isSome_of_residual_lt_budget
    next.box active base (convergentCoefficientSum cell sources * radius)
    (activeBlockEventForms_length_le_two data kind exponent sector target)
    baseInside epsilonPositive epsilonSmall
  apply search
  · intro form formMember
    rcases List.mem_map.mp formMember with ⟨face, filtered, faceForm⟩
    rcases List.mem_filter.mp filtered with ⟨faceMember, checked⟩
    have sourceMember : face.source ∈ sources :=
      List.mem_map.mpr ⟨face, faceMember, rfl⟩
    have canonicalZero := sourceCanonicalZero_of_orientedCheck cell face
      checked
    have sourceResidual :=
      convergentBoxCenter_abs_eval_lt_sum_of_canonicalZero cell sources
        squarefree degreeNonzero elimination next nextRefines radius
        radiusPositive face.source sourceMember
        (by
          simpa only [state, matrix, data.boundaryPathCylinder_path] using
            target.classified face faceMember)
        canonicalZero
    subst form
    cases increasing : face.increasing <;>
      simp [EventOrientedFace.form, increasing] <;> exact sourceResidual
  · intro form formMember
    exact activeBlockEventForms_boundaryDiscriminant_neg data kind exponent
      sector (by simpa only [active, cell, matrix, state] using formMember)
  · intro left right pair
    exact activeBlockEventForms_pair_angleGap data kind exponent sector target
      (by simpa only [active, cell, matrix, state] using pair)

/-- Fully static zero-prefix sector entry.  The radius, thresholded compass
direction, strict-prior margin, and residual step budget are all computed
from rational data; no safeguarding hypothesis remains. -/
def activeBlockConvergentSample
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (sector : Sector)
    (target : CanonicalBlockTarget data.boundaryOrientedInputCell kind exponent
      sector (adjugate (RawParser.parse current.core.word).matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.separation.state.box) :
    BlockSectorBoxSample kind exponent sector
      (adjugate (RawParser.parse current.core.word).matrix) next.box := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let sources := blockEventSourceForms kind exponent sector matrix
  let active := activeBlockEventForms cell kind exponent sector matrix
  let priors := approximateBlockSectorBoxPriors active kind exponent sector
    matrix next.box
  let radius := activeBlockConvergentSampleRadius data kind exponent sector next
  have residualBudgetPositive : 0 < tangentResidualBudget active := by
    simpa only [active, cell, matrix, state] using
      activeBlockTangentResidualBudget_pos data kind exponent sector target
  have slopeBudgetPositive : 0 < tangentSlopeBudget next.box active := by
    simpa only [active, cell, matrix, state] using
      activeBlockTangentSlopeBudget_pos data kind exponent sector target next
  have radiusPositive : 0 < radius := by
    simpa only [radius] using activeBlockConvergentSampleRadius_pos data kind
      exponent sector target next
  let base := convergentBoxCenter squarefree elimination next radius
    radiusPositive
  have search : (tangentDirectionAboveCertificate? active base
      (tangentSlopeBudget next.box active)).isSome := by
    simpa only [state, matrix, cell, active, radius, base] using
      activeBlockConvergentDirectionAbove?_isSome data kind exponent sector
        target squarefree degreeNonzero elimination next nextRefines
  let above := (tangentDirectionAboveCertificate? active base
    (tangentSlopeBudget next.box active)).get search
  let direction := above.toTangentDirection slopeBudgetPositive.le
  have radiusLtTangent : radius <
      convergentTangentRadius cell sources active := by
    simpa only [radius, activeBlockConvergentSampleRadius, sources, active,
      priors, cell, matrix, state] using
      convergentSampleRadius_lt_tangentRadius cell sources active priors next
        residualBudgetPositive slopeBudgetPositive
  have radiusStrict : radius < convergentStrictRadius cell sources :=
    radiusLtTangent.trans (convergentTangentRadius_lt_strictRadius cell sources
      active residualBudgetPositive)
  have radiusClear : radius < convergentClearanceRadius p next := by
    simpa only [radius, activeBlockConvergentSampleRadius, sources, active,
      priors, cell, matrix, state] using
      convergentSampleRadius_lt_clearanceRadius cell sources active priors next
        residualBudgetPositive slopeBudgetPositive
  have baseInside : next.box.Contains base := by
    have strict := convergentBoxCenter_strictContains squarefree elimination
      next radius radiusPositive
    exact ⟨strict.1.le, strict.2.1.le, strict.2.2.1.le,
      strict.2.2.2.le⟩
  have priorLower : ∀ form ∈ priors,
      convergentPriorEvaluationLower cell next ≤ |form.eval base| := by
    simpa only [priors, active, sources, base, cell, matrix, state] using
      convergentBlockPriorEvaluationLower_le cell kind exponent sector matrix
        target squarefree degreeNonzero elimination next nextRefines radius
        radiusPositive radiusStrict radiusClear
  have uniformLe :
      convergentUniformBoundaryBudgetLower next.box active priors
          (convergentPriorEvaluationLower cell next) ≤
        approximateBoundaryBudget direction priors := by
    simpa only [direction] using
      convergentUniformBoundaryBudgetLower_le above slopeBudgetPositive
        baseInside (convergentPriorEvaluationLower_pos cell next) priorLower
  have residualLtUniform : convergentCoefficientSum cell sources * radius <
      convergentUniformBoundaryBudgetLower next.box active priors
        (convergentPriorEvaluationLower cell next) := by
    simpa only [radius, activeBlockConvergentSampleRadius, sources, active,
      priors, cell, matrix, state] using
      convergentCoefficientSum_mul_sampleRadius_lt_uniformBudget cell sources
        active priors next residualBudgetPositive slopeBudgetPositive
  have residualBudget : convergentCoefficientSum cell sources * radius <
      approximateBoundaryBudget direction priors :=
    residualLtUniform.trans_le uniformLe
  simpa only [matrix, state, active, priors, sources, cell] using
    convergentBlockSample cell kind exponent sector matrix target squarefree
      degreeNonzero elimination next nextRefines radius radiusPositive
        radiusStrict direction residualBudget

theorem activeBlockSectorTwoTangentResidualBudget_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (target : CanonicalOrientedTarget data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix))) :
    0 < tangentResidualBudget
      (activeOrientedFaceForms data.boundaryOrientedInputCell
        (blockSectorTwoEventFaces kind exponent first second
          (adjugate (RawParser.parse current.core.word).matrix))) := by
  let active := activeOrientedFaceForms data.boundaryOrientedInputCell
    (blockSectorTwoEventFaces kind exponent first second
      (adjugate (RawParser.parse current.core.word).matrix))
  apply tangentResidualBudget_pos_of_length_le_two active
  · exact activeBlockSectorTwoEventForms_length_le_two data kind exponent
      first second target
  · intro form member
    exact activeBlockSectorTwoEventForms_boundaryDiscriminant_neg data kind
      exponent first second member
  · intro left right pair
    exact activeBlockSectorTwoEventForms_pair_angleGap data kind exponent first
      second target pair

def activeBlockSectorTwoConvergentTangentRadius
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ)
    (first second : Bool) : ℚ :=
  let faces := blockSectorTwoEventFaces kind exponent first second
    (adjugate (RawParser.parse current.core.word).matrix)
  convergentTangentRadius data.boundaryOrientedInputCell
    (orientedFaceSourceForms faces)
    (activeOrientedFaceForms data.boundaryOrientedInputCell faces)

theorem activeBlockSectorTwoConvergentTangentRadius_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (target : CanonicalOrientedTarget data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix))) :
    0 < activeBlockSectorTwoConvergentTangentRadius data kind exponent first
      second := by
  unfold activeBlockSectorTwoConvergentTangentRadius
  exact convergentTangentRadius_pos _ _ _
    (activeBlockSectorTwoTangentResidualBudget_pos data kind exponent first
      second target)

theorem activeBlockSectorTwoConvergentTangentDirection?_isSome
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (target : CanonicalOrientedTarget data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix)))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.separation.state.box) :
    let faces := blockSectorTwoEventFaces kind exponent first second
      (adjugate (RawParser.parse current.core.word).matrix)
    (tangentDirectionCertificate?
      (activeOrientedFaceForms data.boundaryOrientedInputCell faces)
      (convergentBoxCenter squarefree elimination next
        (activeBlockSectorTwoConvergentTangentRadius data kind exponent first
          second)
        (activeBlockSectorTwoConvergentTangentRadius_pos data kind exponent
          first second target))).isSome := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let faces := blockSectorTwoEventFaces kind exponent first second matrix
  let sources := orientedFaceSourceForms faces
  let active := activeOrientedFaceForms cell faces
  let radius := activeBlockSectorTwoConvergentTangentRadius data kind exponent
    first second
  have budgetPositive : 0 < tangentResidualBudget active := by
    simpa only [active, faces, cell, matrix, state] using
      activeBlockSectorTwoTangentResidualBudget_pos data kind exponent first
        second target
  have radiusPositive : 0 < radius := by
    simpa only [radius] using
      activeBlockSectorTwoConvergentTangentRadius_pos data kind exponent first
        second target
  have epsilonPositive :
      0 < convergentCoefficientSum cell sources * radius :=
    mul_pos (convergentCoefficientSum_pos cell sources) radiusPositive
  have epsilonSmall :
      convergentCoefficientSum cell sources * radius <
        tangentResidualBudget active := by
    simpa only [radius, activeBlockSectorTwoConvergentTangentRadius, sources,
      active, faces, cell, matrix, state] using
      convergentCoefficientSum_mul_tangentRadius_lt_budget cell sources active
        budgetPositive
  have search : (tangentDirectionCertificate? active
      (convergentBoxCenter squarefree elimination next radius
        radiusPositive)).isSome := by
    apply tangentDirectionCertificate?_isSome_of_residual_lt_budget active
      (convergentBoxCenter squarefree elimination next radius radiusPositive)
      (convergentCoefficientSum cell sources * radius)
      (by
        simpa only [active, faces, cell, matrix, state] using
          activeBlockSectorTwoEventForms_length_le_two data kind exponent first
            second target)
      epsilonPositive epsilonSmall
    · intro form formMember
      rcases List.mem_map.mp formMember with ⟨face, filtered, faceForm⟩
      rcases List.mem_filter.mp filtered with ⟨faceMember, checked⟩
      have sourceMember : face.source ∈ sources :=
        List.mem_map.mpr ⟨face, faceMember, rfl⟩
      have canonicalZero := sourceCanonicalZero_of_orientedCheck cell face
        checked
      have sourceResidual :=
        convergentBoxCenter_abs_eval_lt_sum_of_canonicalZero cell sources
          squarefree degreeNonzero elimination next nextRefines radius
          radiusPositive face.source sourceMember
          (by
            simpa only [state, matrix, data.boundaryPathCylinder_path] using
              target.classified face faceMember)
          canonicalZero
      subst form
      cases increasing : face.increasing <;>
        simp [EventOrientedFace.form, increasing] <;>
        exact sourceResidual
    · intro form formMember
      exact activeBlockSectorTwoEventForms_boundaryDiscriminant_neg data kind
        exponent first second
          (by simpa only [active, faces, cell, matrix, state] using formMember)
    · intro left right pair
      exact activeBlockSectorTwoEventForms_pair_angleGap data kind exponent first
        second target
          (by simpa only [active, faces, cell, matrix, state] using pair)
  simpa only [active, faces, radius, cell, matrix, state] using search

theorem activeBlockSectorTwoTangentSlopeBudget_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (target : CanonicalOrientedTarget data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix)))
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    let faces := blockSectorTwoEventFaces kind exponent first second
      (adjugate (RawParser.parse current.core.word).matrix)
    0 < tangentSlopeBudget next.box
      (activeOrientedFaceForms data.boundaryOrientedInputCell faces) := by
  let faces := blockSectorTwoEventFaces kind exponent first second
    (adjugate (RawParser.parse current.core.word).matrix)
  let active := activeOrientedFaceForms data.boundaryOrientedInputCell faces
  apply tangentSlopeBudget_pos_of_length_le_two next.box active
  · exact activeBlockSectorTwoEventForms_length_le_two data kind exponent first
      second target
  · intro form member
    exact activeBlockSectorTwoEventForms_boundaryDiscriminant_neg data kind
      exponent first second member
  · intro left right pair
    exact activeBlockSectorTwoEventForms_pair_angleGap data kind exponent first
      second target pair

def activeBlockSectorTwoConvergentSampleRadius
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (next : WindingOneState p (RatBox.symmetric R hR)) : ℚ :=
  let matrix := adjugate (RawParser.parse current.core.word).matrix
  let cell := data.boundaryOrientedInputCell
  let faces := blockSectorTwoEventFaces kind exponent first second matrix
  let sources := orientedFaceSourceForms faces
  let active := activeOrientedFaceForms cell faces
  let priors := approximateOrientedBoxPriors active
    (orientedFaceForms faces) next.box
  convergentSampleRadius cell sources active priors next

theorem activeBlockSectorTwoConvergentSampleRadius_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (target : CanonicalOrientedTarget data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix)))
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    0 < activeBlockSectorTwoConvergentSampleRadius data kind exponent first
      second next := by
  unfold activeBlockSectorTwoConvergentSampleRadius
  exact convergentSampleRadius_pos _ _ _ _ _
    (activeBlockSectorTwoTangentResidualBudget_pos data kind exponent first
      second target)
    (activeBlockSectorTwoTangentSlopeBudget_pos data kind exponent first second
      target next)

theorem activeBlockSectorTwoConvergentDirectionAbove?_isSome
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (target : CanonicalOrientedTarget data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix)))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.separation.state.box) :
    let matrix := adjugate (RawParser.parse current.core.word).matrix
    let cell := data.boundaryOrientedInputCell
    let faces := blockSectorTwoEventFaces kind exponent first second matrix
    let active := activeOrientedFaceForms cell faces
    let radius := activeBlockSectorTwoConvergentSampleRadius data kind exponent
      first second next
    let base := convergentBoxCenter squarefree elimination next radius
      (activeBlockSectorTwoConvergentSampleRadius_pos data kind exponent first
        second target next)
    (tangentDirectionAboveCertificate? active base
      (tangentSlopeBudget next.box active)).isSome := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let faces := blockSectorTwoEventFaces kind exponent first second matrix
  let sources := orientedFaceSourceForms faces
  let active := activeOrientedFaceForms cell faces
  let priors := approximateOrientedBoxPriors active
    (orientedFaceForms faces) next.box
  let radius := activeBlockSectorTwoConvergentSampleRadius data kind exponent
    first second next
  have residualBudgetPositive : 0 < tangentResidualBudget active := by
    simpa only [active, faces, cell, matrix, state] using
      activeBlockSectorTwoTangentResidualBudget_pos data kind exponent first
        second target
  have slopeBudgetPositive : 0 < tangentSlopeBudget next.box active := by
    simpa only [active, faces, cell, matrix, state] using
      activeBlockSectorTwoTangentSlopeBudget_pos data kind exponent first second
        target next
  have radiusPositive : 0 < radius := by
    simpa only [radius] using
      activeBlockSectorTwoConvergentSampleRadius_pos data kind exponent first
        second target next
  let base := convergentBoxCenter squarefree elimination next radius
    radiusPositive
  have baseInside : next.box.Contains base := by
    have strict := convergentBoxCenter_strictContains squarefree elimination
      next radius radiusPositive
    exact ⟨strict.1.le, strict.2.1.le, strict.2.2.1.le,
      strict.2.2.2.le⟩
  have radiusLtTangent : radius <
      convergentTangentRadius cell sources active := by
    simpa only [radius, activeBlockSectorTwoConvergentSampleRadius, sources,
      active, priors, faces, cell, matrix, state] using
      convergentSampleRadius_lt_tangentRadius cell sources active priors next
        residualBudgetPositive slopeBudgetPositive
  have epsilonPositive :
      0 < convergentCoefficientSum cell sources * radius :=
    mul_pos (convergentCoefficientSum_pos cell sources) radiusPositive
  have epsilonSmall : convergentCoefficientSum cell sources * radius <
      tangentResidualBudget active := by
    calc
      convergentCoefficientSum cell sources * radius <
          convergentCoefficientSum cell sources *
            convergentTangentRadius cell sources active :=
        mul_lt_mul_of_pos_left radiusLtTangent
          (convergentCoefficientSum_pos cell sources)
      _ < tangentResidualBudget active :=
        convergentCoefficientSum_mul_tangentRadius_lt_budget cell sources
          active residualBudgetPositive
  have search := tangentDirectionAboveCertificate?_isSome_of_residual_lt_budget
    next.box active base (convergentCoefficientSum cell sources * radius)
    (activeBlockSectorTwoEventForms_length_le_two data kind exponent first
      second target) baseInside epsilonPositive epsilonSmall
  apply search
  · intro form formMember
    rcases List.mem_map.mp formMember with ⟨face, filtered, faceForm⟩
    rcases List.mem_filter.mp filtered with ⟨faceMember, checked⟩
    have sourceMember : face.source ∈ sources :=
      List.mem_map.mpr ⟨face, faceMember, rfl⟩
    have canonicalZero := sourceCanonicalZero_of_orientedCheck cell face checked
    have sourceResidual :=
      convergentBoxCenter_abs_eval_lt_sum_of_canonicalZero cell sources
        squarefree degreeNonzero elimination next nextRefines radius
        radiusPositive face.source sourceMember
        (by
          simpa only [state, matrix, data.boundaryPathCylinder_path] using
            target.classified face faceMember)
        canonicalZero
    subst form
    cases increasing : face.increasing <;>
      simp [EventOrientedFace.form, increasing] <;> exact sourceResidual
  · intro form formMember
    exact activeBlockSectorTwoEventForms_boundaryDiscriminant_neg data kind
      exponent first second
        (by simpa only [active, faces, cell, matrix, state] using formMember)
  · intro left right pair
    exact activeBlockSectorTwoEventForms_pair_angleGap data kind exponent first
      second target
        (by simpa only [active, faces, cell, matrix, state] using pair)

/-- Fully static one-prefix sector entry, parallel to
`activeBlockConvergentSample`. -/
def activeBlockSectorTwoConvergentSample
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (target : CanonicalOrientedTarget data.boundaryOrientedInputCell
      (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix)))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.separation.state.box) :
    OrientedBoxSample
      (orientedFaceForms (blockSectorTwoEventFaces kind exponent first second
        (adjugate (RawParser.parse current.core.word).matrix))) next.box := by
  let state := RawParser.parse current.core.word
  let matrix := adjugate state.matrix
  let cell := data.boundaryOrientedInputCell
  let faces := blockSectorTwoEventFaces kind exponent first second matrix
  let sources := orientedFaceSourceForms faces
  let active := activeOrientedFaceForms cell faces
  let priors := approximateOrientedBoxPriors active
    (orientedFaceForms faces) next.box
  let radius := activeBlockSectorTwoConvergentSampleRadius data kind exponent
    first second next
  have residualBudgetPositive : 0 < tangentResidualBudget active := by
    simpa only [active, faces, cell, matrix, state] using
      activeBlockSectorTwoTangentResidualBudget_pos data kind exponent first
        second target
  have slopeBudgetPositive : 0 < tangentSlopeBudget next.box active := by
    simpa only [active, faces, cell, matrix, state] using
      activeBlockSectorTwoTangentSlopeBudget_pos data kind exponent first second
        target next
  have radiusPositive : 0 < radius := by
    simpa only [radius] using
      activeBlockSectorTwoConvergentSampleRadius_pos data kind exponent first
        second target next
  let base := convergentBoxCenter squarefree elimination next radius
    radiusPositive
  have search : (tangentDirectionAboveCertificate? active base
      (tangentSlopeBudget next.box active)).isSome := by
    simpa only [state, matrix, cell, faces, active, radius, base] using
      activeBlockSectorTwoConvergentDirectionAbove?_isSome data kind exponent
        first second target squarefree degreeNonzero elimination next
          nextRefines
  let above := (tangentDirectionAboveCertificate? active base
    (tangentSlopeBudget next.box active)).get search
  let direction := above.toTangentDirection slopeBudgetPositive.le
  have radiusLtTangent : radius <
      convergentTangentRadius cell sources active := by
    simpa only [radius, activeBlockSectorTwoConvergentSampleRadius, sources,
      active, priors, faces, cell, matrix, state] using
      convergentSampleRadius_lt_tangentRadius cell sources active priors next
        residualBudgetPositive slopeBudgetPositive
  have radiusStrict : radius < convergentStrictRadius cell sources :=
    radiusLtTangent.trans (convergentTangentRadius_lt_strictRadius cell sources
      active residualBudgetPositive)
  have radiusClear : radius < convergentClearanceRadius p next := by
    simpa only [radius, activeBlockSectorTwoConvergentSampleRadius, sources,
      active, priors, faces, cell, matrix, state] using
      convergentSampleRadius_lt_clearanceRadius cell sources active priors next
        residualBudgetPositive slopeBudgetPositive
  have baseInside : next.box.Contains base := by
    have strict := convergentBoxCenter_strictContains squarefree elimination
      next radius radiusPositive
    exact ⟨strict.1.le, strict.2.1.le, strict.2.2.1.le,
      strict.2.2.2.le⟩
  have priorLower : ∀ form ∈ priors,
      convergentPriorEvaluationLower cell next ≤ |form.eval base| := by
    simpa only [priors, active, sources, base, faces, cell, matrix, state] using
      convergentOrientedPriorEvaluationLower_le cell faces target squarefree
        degreeNonzero elimination next nextRefines radius radiusPositive
          radiusStrict radiusClear
  have uniformLe :
      convergentUniformBoundaryBudgetLower next.box active priors
          (convergentPriorEvaluationLower cell next) ≤
        approximateBoundaryBudget direction priors := by
    simpa only [direction] using
      convergentUniformBoundaryBudgetLower_le above slopeBudgetPositive
        baseInside (convergentPriorEvaluationLower_pos cell next) priorLower
  have residualLtUniform : convergentCoefficientSum cell sources * radius <
      convergentUniformBoundaryBudgetLower next.box active priors
        (convergentPriorEvaluationLower cell next) := by
    simpa only [radius, activeBlockSectorTwoConvergentSampleRadius, sources,
      active, priors, faces, cell, matrix, state] using
      convergentCoefficientSum_mul_sampleRadius_lt_uniformBudget cell sources
        active priors next residualBudgetPositive slopeBudgetPositive
  have residualBudget : convergentCoefficientSum cell sources * radius <
      approximateBoundaryBudget direction priors :=
    residualLtUniform.trans_le uniformLe
  simpa only [matrix, state, faces, active, priors, sources, cell] using
    convergentOrientedBoxSample cell faces target squarefree degreeNonzero
      elimination next nextRefines radius radiusPositive radiusStrict direction
        residualBudget

end CCLActiveMetricTrack
end FTA
