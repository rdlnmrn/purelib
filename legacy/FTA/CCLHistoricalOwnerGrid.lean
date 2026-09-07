import FTA.CCLBoundaryPreservingOwner
import FTA.CCLPositiveEventGrid
import FTA.CCLPositiveEventConvergence

/-!
# Complete historical owner grids

This module packages a simultaneous owner perturbation for every active face
of the old parser predicate together with the selected child.  In contrast to
the earlier incremental grid, inherited equality faces are entered or
preserved explicitly rather than hidden behind a strict-prior stability
assumption.

The base point, exact rational tangent certificate, and residual estimates
remain separate finite inputs.  From them the grid computes one rational
point inside the later winding box, proves the complete historical formula,
and reconstructs the extended raw word.
-/

namespace FTA
namespace CCLHistoricalOwnerGrid

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBoundaryPreservingOwner
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLCanonicalEvent
open FTA.CCLCompleteEventTangentSigns
open FTA.CCLEventTangentSigns
open FTA.CCLCoupledController
open FTA.CCLFormulaPullback
open FTA.CCLFormulaPath
open FTA.CCLGeometry
open FTA.CCLHistoricalEventOwner
open FTA.CCLHistoricalEventTangentSigns
open FTA.CCLHermitianBox
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLPathIntersection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventGrid
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventSemantics
open FTA.CCLRationalTangentCone
open FTA.LocalExtraction
open FTA.RationalPolynomialBounds
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Complete-payload specialization of the common denominator upper bound. -/
private abbrev selectedEventDenominatorUpper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  FTA.CCLPositiveEventConvergence.selectedEventDenominatorUpper
    selected.toIncrementalPayload

private theorem selectedEventDenominatorUpper_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < selectedEventDenominatorUpper selected :=
  FTA.CCLPositiveEventConvergence.selectedEventDenominatorUpper_pos
    selected.toIncrementalPayload

/-- Strict forms protected while all historical equality owners are entered:
the canonically strict branch, the later box, and the nonzero norm test. -/
def historicalGridPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (_base : QI) (box : RatBox) :
    List HermitianForm :=
  historicalStrictPriorForms selected ++ boxForms box ++
    [affineNormForm 1 0]

/-- A localized rational base for the complete historical owner list. -/
structure HistoricalGridBase
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (next : WindingOneState p (RatBox.symmetric R hR)) where
  point : QI
  strict : next.box.StrictContains point
  nonzero : point ≠ 0
  historicalStrict :
    ∀ form ∈ historicalStrictPriorForms selected,
      0 < historicalCanonicalValue selected form * form.eval point

/-- Linear residual coefficient for one complete historical active face at
the represented coupled-track base. -/
def historicalActiveBaseCoefficient
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) (form : HermitianForm) : ℚ :=
  inputEventFormCoefficient (historicalSlopeInputCell selected) form +
    10 * variationMajorant form separation.state.box

theorem historicalActiveBaseCoefficient_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) (form : HermitianForm) :
    0 < historicalActiveBaseCoefficient selected form := by
  exact add_pos_of_nonneg_of_pos
    (inputEventFormCoefficient_nonneg (historicalSlopeInputCell selected) form)
    (mul_pos (by norm_num)
      (variationMajorant_pos form separation.state.box))

/-- The complete historical active list has one executable positive residual
coefficient bound. -/
def historicalActiveCoefficientSum
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) : ℚ :=
  1 + ((historicalActiveOwnerForms selected).map fun form =>
    historicalActiveBaseCoefficient selected form).sum

theorem historicalActiveCoefficientSum_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) :
    0 < historicalActiveCoefficientSum selected := by
  have sumNonnegative : 0 ≤
      ((historicalActiveOwnerForms selected).map fun form =>
        historicalActiveBaseCoefficient selected form).sum := by
    apply List.sum_nonneg
    intro coefficient coefficientMember
    rw [List.mem_map] at coefficientMember
    rcases coefficientMember with ⟨form, _formMember, rfl⟩
    exact (historicalActiveBaseCoefficient_pos selected form).le
  unfold historicalActiveCoefficientSum
  linarith

theorem historicalActiveBaseCoefficient_lt_sum
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    historicalActiveBaseCoefficient selected form <
      historicalActiveCoefficientSum selected := by
  have coefficientLeSum : historicalActiveBaseCoefficient selected form ≤
      ((historicalActiveOwnerForms selected).map fun item =>
        historicalActiveBaseCoefficient selected item).sum := by
    apply List.single_le_sum
    · intro coefficient coefficientMember
      rw [List.mem_map] at coefficientMember
      rcases coefficientMember with ⟨item, _itemMember, rfl⟩
      exact (historicalActiveBaseCoefficient_pos selected item).le
    · exact List.mem_map.mpr ⟨form, member, rfl⟩
  unfold historicalActiveCoefficientSum
  linarith

/-- Every historical active face is linearly small at the exact rational
boundary approximation from the final historical classification. -/
theorem historicalBoundaryPoint_active_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    |form.eval (historicalBoundaryPoint selected squarefree radius
      radiusPositive)| ≤
        inputEventFormCoefficient (historicalSlopeInputCell selected) form *
          radius := by
  have divides := historicalSlopeActivePolynomial_dvd selected member
  rw [historicalBoundaryPoint_eq_shrinkingInputEventPoint]
  exact shrinkingInputEventForm_le_of_dvd
    (historicalSlopeInputCell selected) squarefree radius radiusPositive
    form divides

/-- Transfer the historical event residual to the represented base selected
inside an arbitrary later winding-one box. -/
theorem historicalConvergentGridBase_active_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    |form.eval base.point| ≤
      historicalActiveBaseCoefficient selected form * radius := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventPoint := historicalBoundaryPoint selected squarefree radius
    radiusPositive
  have baseInside : separation.state.box.Contains base.point :=
    nextRefines.contains base.strict.contains
  have eventInside : separation.state.box.Contains eventPoint :=
    (historicalBoundaryState_refines_separation selected squarefree
      elimination radius radiusPositive).contains
        (historicalBoundaryState_contains_point selected squarefree
          elimination radius radiusPositive)
  have variation := abs_eval_sub_eval_le form baseInside eventInside
  have distance := convergentGridBase_inputEvent_distance current separation
    (historicalSlopeInputCell selected) squarefree degreeNonzero elimination
    next nextRefines radius radiusPositive
  have variationLe :
      |form.eval base.point - form.eval eventPoint| ≤
        10 * variationMajorant form separation.state.box * radius := by
    apply variation.trans
    exact mul_le_mul_of_nonneg_left distance
      (variationMajorant_pos form separation.state.box).le |>.trans_eq (by ring)
  have eventLe := historicalBoundaryPoint_active_le selected squarefree
    radius radiusPositive member
  have triangle : |form.eval base.point| ≤
      |form.eval base.point - form.eval eventPoint| +
        |form.eval eventPoint| := by
    have bound := abs_add_le
      (form.eval base.point - form.eval eventPoint) (form.eval eventPoint)
    simpa only [sub_add_cancel] using bound
  exact triangle.trans (by
    dsimp only [historicalActiveBaseCoefficient]
    calc
      |form.eval base.point - form.eval eventPoint| +
          |form.eval eventPoint| ≤
        10 * variationMajorant form separation.state.box * radius +
          inputEventFormCoefficient (historicalSlopeInputCell selected) form *
            radius := add_le_add variationLe eventLe
      _ = (inputEventFormCoefficient (historicalSlopeInputCell selected) form +
          10 * variationMajorant form separation.state.box) * radius := by ring)

theorem historicalConvergentGridBase_active_lt_sum
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    |form.eval base.point| <
      historicalActiveCoefficientSum selected * radius := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  have individual := historicalConvergentGridBase_active_le current separation
    selected squarefree degreeNonzero elimination next nextRefines radius
    radiusPositive member
  exact individual.trans_lt (mul_lt_mul_of_pos_right
    (historicalActiveBaseCoefficient_lt_sum selected member) radiusPositive)

/-- One computable positive margin simultaneously lower-bounds all cleared
directional slopes in the final historical classification cell. -/
def historicalSlopeStrictMargin
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  ConditionRelations.strictMargin
    (historicalSlopeClassification selected).branch.relations
    (historicalSlopeClassification selected).parent
    (historicalSlopeSigns selected)

theorem historicalSlopeStrictMargin_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < historicalSlopeStrictMargin selected :=
  ConditionRelations.strictMargin_pos
    (historicalSlopeClassification selected).branch.relations
    (historicalSlopeClassification selected).parent
    (historicalSlopeSigns selected)

theorem historicalSlopeStrictMargin_le_clearedSlope
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    {t : ℚ}
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    historicalSlopeStrictMargin selected ≤
      (clearedDirectionalSlope form (selectedCompletePath selected) direction).eval t := by
  let polynomial :=
    clearedDirectionalSlope form (selectedCompletePath selected) direction
  have polynomialMember : polynomial ∈ historicalSlopeConditions selected :=
    clearedDirectionalSlope_mem_historicalSlopeConditions selected
      (historicalClassifiedTangentDirection?_some_mem search) member
  have canonicalPositive :=
    historicalClassifiedTangentDirection?_some_slopes search form member
  have marginLeAbs := ConditionRelations.strictMargin_le_abs_eval
    (historicalSlopeClassification selected).branch.relations
    (historicalSlopeClassification selected).parent
    (historicalSlopeSigns selected) polynomialMember canonicalPositive.ne'
    lower upper
  have positive := historicalClassifiedTangentDirection?_some_clearedSlopes
    search lower upper form member
  simpa only [polynomial, historicalSlopeStrictMargin,
    abs_of_pos positive] using marginLeAbs

/-- Positive whole-cell upper bound for the projective denominator on the
final historical slope interval. -/
def historicalSlopeDenominatorUpper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  denseEvalAbsBound (denominatorNorm (selectedCompletePath selected))
      (intervalMagnitude
        (historicalSlopeSigns selected).refined.interval.lower
        (historicalSlopeSigns selected).refined.interval.upper) + 1

theorem historicalSlopeDenominatorUpper_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < historicalSlopeDenominatorUpper selected := by
  unfold historicalSlopeDenominatorUpper
  have nonnegative := (denseHornerBounds_nonneg
    (denominatorNorm (selectedCompletePath selected))
    (intervalMagnitude_pos
      (historicalSlopeSigns selected).refined.interval.lower
      (historicalSlopeSigns selected).refined.interval.upper).le).1
  linarith

theorem denominatorNorm_le_historicalSlopeDenominatorUpper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {t : ℚ}
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper) :
    (denominatorNorm (selectedCompletePath selected)).eval t ≤
      historicalSlopeDenominatorUpper selected := by
  let magnitude := intervalMagnitude
    (historicalSlopeSigns selected).refined.interval.lower
    (historicalSlopeSigns selected).refined.interval.upper
  have magnitudeNonnegative : 0 ≤ magnitude :=
    (intervalMagnitude_pos _ _).le
  have tMagnitude : |t| ≤ magnitude :=
    abs_le_intervalMagnitude lower upper
  have absoluteBound := abs_dense_eval_le_denseEvalAbsBound
    (denominatorNorm (selectedCompletePath selected)) magnitudeNonnegative tMagnitude
  exact (le_abs_self _).trans absoluteBound |>.trans (by
    unfold historicalSlopeDenominatorUpper
    dsimp only [magnitude]
    linarith)

/-- Uniform positive lower bound for every historical active directional
derivative under the fixed classified vector. -/
def historicalSlopeDirectionalLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  historicalSlopeStrictMargin selected /
    historicalSlopeDenominatorUpper selected

theorem historicalSlopeDirectionalLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < historicalSlopeDirectionalLower selected :=
  div_pos (historicalSlopeStrictMargin_pos selected)
    (historicalSlopeDenominatorUpper_pos selected)

theorem historicalSlopeDirectionalLower_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    {t : ℚ}
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    historicalSlopeDirectionalLower selected ≤
      directionalSlope form ((selectedCompletePath selected).value t) direction := by
  have rootLower :=
    (historicalSlopeSigns_refines_inputCell selected).1.trans lower
  have rootUpper := upper.trans
    (historicalSlopeSigns_refines_inputCell selected).2
  have denominator :=
    (historicalInputCell selected).path_denominator_ne_on_cell
      rootLower rootUpper
  have denominatorPositive := eval_denominatorNorm_pos
    (selectedCompletePath selected) t denominator
  have denominatorLe := denominatorNorm_le_historicalSlopeDenominatorUpper
    selected lower upper
  have marginLe := historicalSlopeStrictMargin_le_clearedSlope search lower
    upper member
  have scaled : historicalSlopeDirectionalLower selected *
      (denominatorNorm (selectedCompletePath selected)).eval t ≤
      historicalSlopeStrictMargin selected := by
    unfold historicalSlopeDirectionalLower
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (historicalSlopeDenominatorUpper_pos selected)).2
    exact mul_le_mul_of_nonneg_left denominatorLe
      (historicalSlopeStrictMargin_pos selected).le
  rw [eval_clearedDirectionalSlope form (selectedCompletePath selected) direction t
    denominator] at marginLe
  apply (mul_le_mul_iff_of_pos_right denominatorPositive).mp
  calc
    historicalSlopeDirectionalLower selected *
        (denominatorNorm (selectedCompletePath selected)).eval t ≤
      historicalSlopeStrictMargin selected := scaled
    _ ≤ (denominatorNorm (selectedCompletePath selected)).eval t *
        directionalSlope form ((selectedCompletePath selected).value t) direction :=
      marginLe
    _ = directionalSlope form ((selectedCompletePath selected).value t) direction *
        (denominatorNorm (selectedCompletePath selected)).eval t := by ring

/-- Uniform absolute-value margin for canonically strict current-history
forms on the final historical event interval. -/
def historicalCurrentStrictFormMargin
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) : ℚ :=
  let classification :=
    CCLCanonicalEvent.currentFormulaClassification selected.candidate.inputCell
  let signs := classification.branch.computeEventSigns classification.parent
  FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
      classification.branch.relations classification.parent signs /
    selectedEventDenominatorUpper selected

theorem historicalCurrentStrictFormMargin_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) :
    0 < historicalCurrentStrictFormMargin selected := by
  apply div_pos
  · exact FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_pos
      (CCLCanonicalEvent.currentFormulaClassification
        selected.candidate.inputCell).branch.relations
      (CCLCanonicalEvent.currentFormulaClassification
        selected.candidate.inputCell).parent
      ((CCLCanonicalEvent.currentFormulaClassification
        selected.candidate.inputCell).branch.computeEventSigns
          (CCLCanonicalEvent.currentFormulaClassification
            selected.candidate.inputCell).parent)
  · exact selectedEventDenominatorUpper_pos selected

/-- Uniform absolute-value margin for canonically strict selected-child forms
on the final historical event interval. -/
def historicalChildStrictFormMargin
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) : ℚ :=
  let cell := historicalInputCell selected
  let signs := cell.branch.computeEventSigns cell.parent
  FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
      cell.branch.relations cell.parent signs /
    selectedEventDenominatorUpper selected

theorem historicalChildStrictFormMargin_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) :
    0 < historicalChildStrictFormMargin selected := by
  apply div_pos
  · exact FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_pos
      (historicalInputCell selected).branch.relations
      (historicalInputCell selected).parent
      ((historicalInputCell selected).branch.computeEventSigns
        (historicalInputCell selected).parent)
  · exact selectedEventDenominatorUpper_pos selected

/-- One positive margin works for either origin of a strict historical form. -/
def historicalStrictFormMargin
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) : ℚ :=
  min (historicalCurrentStrictFormMargin selected)
    (historicalChildStrictFormMargin selected)

theorem historicalStrictFormMargin_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) :
    0 < historicalStrictFormMargin selected := by
  exact lt_min (historicalCurrentStrictFormMargin_pos selected)
    (historicalChildStrictFormMargin_pos selected)

private theorem historicalBoundaryParameter_candidate_bounds
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined.interval.lower ≤
        historicalBoundaryParameter selected squarefree radius radiusPositive ∧
      historicalBoundaryParameter selected squarefree radius radiusPositive ≤
        (selected.candidate.inputCell.branch.computeEventSigns
          selected.candidate.inputCell.parent).refined.interval.upper := by
  have bounds := historicalBoundaryParameter_bounds selected squarefree radius
    radiusPositive
  let classification := currentFormulaClassification
    selected.candidate.inputCell
  let currentSigns := classification.branch.computeEventSigns
    classification.parent
  let cell := historicalInputCell selected
  let finalSigns := cell.branch.computeEventSigns cell.parent
  have finalLower : finalSigns.refined.interval.lower ≤
      historicalBoundaryParameter selected squarefree radius radiusPositive :=
    (historicalSlopeSigns_refines_inputCell selected).1.trans bounds.1
  have finalUpper : historicalBoundaryParameter selected squarefree radius
      radiusPositive ≤ finalSigns.refined.interval.upper :=
    bounds.2.trans (historicalSlopeSigns_refines_inputCell selected).2
  have currentLower : currentSigns.refined.interval.lower ≤
      historicalBoundaryParameter selected squarefree radius radiusPositive :=
    finalSigns.refines.1.trans finalLower
  have currentUpper : historicalBoundaryParameter selected squarefree radius
      radiusPositive ≤ currentSigns.refined.interval.upper :=
    finalUpper.trans finalSigns.refines.2
  exact ⟨classification.signRefines.1.trans currentLower,
    currentUpper.trans classification.signRefines.2⟩

/-- The current-history strict margin holds at every rational parameter in
the final historical slope cell, independently of how that point was
localized. -/
theorem historicalCurrentStrictFormMargin_le_pathValue
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) {t : ℚ}
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (member : form ∈ strictPriorForms
      (inputStateFormula (RawParser.parse current.word))
      (historicalCanonicalValue selected)) :
    historicalCurrentStrictFormMargin selected ≤
      |form.eval ((selectedCompletePath selected).value t)| := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  let classification := CCLCanonicalEvent.currentFormulaClassification
    selected.candidate.inputCell
  let currentSigns := classification.branch.computeEventSigns
    classification.parent
  let cell := historicalInputCell selected
  let finalSigns := cell.branch.computeEventSigns cell.parent
  have finalLower : finalSigns.refined.interval.lower ≤ t :=
    (historicalSlopeSigns_refines_inputCell selected).1.trans lower
  have finalUpper : t ≤ finalSigns.refined.interval.upper :=
    upper.trans (historicalSlopeSigns_refines_inputCell selected).2
  have currentLower : currentSigns.refined.interval.lower ≤ t :=
    finalSigns.refines.1.trans finalLower
  have currentUpper : t ≤ currentSigns.refined.interval.upper :=
    finalUpper.trans finalSigns.refines.2
  have candidateLower :
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined.interval.lower ≤ t :=
    classification.signRefines.1.trans currentLower
  have candidateUpper : t ≤
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined.interval.upper :=
    currentUpper.trans classification.signRefines.2
  have polynomialMember : clearedForm atom.form (selectedCompletePath selected) ∈
      eventFormulaPolynomials
        (inputStateFormula (RawParser.parse current.word))
        (selectedCompletePath selected) :=
    List.mem_map.mpr
      ⟨atom, satisfyingAtoms_mem_formulaAtoms _ _
        (strictSatisfyingAtoms_source atomMember), rfl⟩
  have historicalNonzero :
      historicalCanonicalValue selected atom.form ≠ 0 :=
    strictPriorForms_value_ne _ _ member
  let currentCanonical := canonicalEventValue
    classification.branch.factor.input
    (clearedForm atom.form (selectedCompletePath selected))
    currentSigns.refined.interval.lower
  have currentNonzero : currentCanonical ≠ 0 := by
    have sampleLower : currentSigns.refined.interval.lower ≤
        finalSigns.refined.interval.lower := finalSigns.refines.1
    have sampleUpper : finalSigns.refined.interval.lower ≤
        currentSigns.refined.interval.upper :=
      finalSigns.refined.proper.le.trans finalSigns.refines.2
    have agreement (test : SignTest) :
        test.Holds currentCanonical ↔
          test.Holds (historicalCanonicalValue selected atom.form) := by
      have same := ConditionRelations.canonicalEventValue_holds_iff_between
        classification.branch.relations classification.parent currentSigns
        polynomialMember test sampleLower sampleUpper
      simpa only [currentCanonical, historicalCanonicalValue,
        inputEventCanonicalValue, historicalInputCell,
        CCLCanonicalEvent.currentFormulaInputCell, classification,
        currentSigns, cell, finalSigns, selectedCompletePath] using same
    rcases lt_or_gt_of_ne historicalNonzero with negative | positive
    · exact ne_of_lt ((agreement .negative).2 negative)
    · exact ne_of_gt ((agreement .positive).2 positive)
  have clearedLower := ConditionRelations.strictMargin_le_abs_eval
    classification.branch.relations classification.parent currentSigns
    polynomialMember currentNonzero currentLower currentUpper
  have denominator := cell.path_denominator_ne_on_cell finalLower finalUpper
  have denominatorLe := selectedEventDenominator_le
    selected.toIncrementalPayload candidateLower candidateUpper
  have clearedIdentity :
      |(clearedForm atom.form (selectedCompletePath selected)).eval t| =
        |(denominatorNorm (selectedCompletePath selected)).eval t| *
          |atom.form.eval ((selectedCompletePath selected).value t)| := by
    rw [eval_clearedForm atom.form (selectedCompletePath selected) t denominator,
      abs_mul]
  unfold historicalCurrentStrictFormMargin
  apply (div_le_iff₀ (selectedEventDenominatorUpper_pos selected)).2
  calc
    ConditionRelations.strictMargin classification.branch.relations
        classification.parent currentSigns ≤
      |(clearedForm atom.form (selectedCompletePath selected)).eval t| := clearedLower
    _ = |(denominatorNorm (selectedCompletePath selected)).eval t| *
        |atom.form.eval ((selectedCompletePath selected).value t)| := clearedIdentity
    _ ≤ selectedEventDenominatorUpper selected *
        |atom.form.eval ((selectedCompletePath selected).value t)| :=
      mul_le_mul_of_nonneg_right denominatorLe (abs_nonneg _)
    _ = |atom.form.eval ((selectedCompletePath selected).value t)| *
        selectedEventDenominatorUpper selected := by ring

theorem historicalCurrentStrictFormMargin_le_boundaryPoint
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {form : HermitianForm}
    (member : form ∈ strictPriorForms
      (inputStateFormula (RawParser.parse current.word))
      (historicalCanonicalValue selected)) :
    historicalCurrentStrictFormMargin selected ≤
      |form.eval (historicalBoundaryPoint selected squarefree radius
        radiusPositive)| := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  let classification := CCLCanonicalEvent.currentFormulaClassification
    selected.candidate.inputCell
  let currentSigns := classification.branch.computeEventSigns
    classification.parent
  let cell := historicalInputCell selected
  let finalSigns := cell.branch.computeEventSigns cell.parent
  let t := historicalBoundaryParameter selected squarefree radius radiusPositive
  have slopeBounds := historicalBoundaryParameter_bounds selected squarefree
    radius radiusPositive
  have finalLower : finalSigns.refined.interval.lower ≤ t :=
    (historicalSlopeSigns_refines_inputCell selected).1.trans slopeBounds.1
  have finalUpper : t ≤ finalSigns.refined.interval.upper :=
    slopeBounds.2.trans (historicalSlopeSigns_refines_inputCell selected).2
  have currentLower : currentSigns.refined.interval.lower ≤ t :=
    finalSigns.refines.1.trans finalLower
  have currentUpper : t ≤ currentSigns.refined.interval.upper :=
    finalUpper.trans finalSigns.refines.2
  have polynomialMember : clearedForm atom.form (selectedCompletePath selected) ∈
      eventFormulaPolynomials
        (inputStateFormula (RawParser.parse current.word))
        (selectedCompletePath selected) :=
    List.mem_map.mpr
      ⟨atom, satisfyingAtoms_mem_formulaAtoms _ _
        (strictSatisfyingAtoms_source atomMember), rfl⟩
  have historicalNonzero :
      historicalCanonicalValue selected atom.form ≠ 0 :=
    strictPriorForms_value_ne _ _ member
  let currentCanonical := canonicalEventValue classification.branch.factor.input
    (clearedForm atom.form (selectedCompletePath selected))
    currentSigns.refined.interval.lower
  have currentNonzero : currentCanonical ≠ 0 := by
    have sampleLower : currentSigns.refined.interval.lower ≤
        finalSigns.refined.interval.lower := finalSigns.refines.1
    have sampleUpper : finalSigns.refined.interval.lower ≤
        currentSigns.refined.interval.upper :=
      finalSigns.refined.proper.le.trans finalSigns.refines.2
    have agreement (test : SignTest) :
        test.Holds currentCanonical ↔
          test.Holds (historicalCanonicalValue selected atom.form) := by
      have same :=
        FTA.CCLBranchEventOwner.ConditionRelations.canonicalEventValue_holds_iff_between
          classification.branch.relations classification.parent currentSigns
          polynomialMember test sampleLower sampleUpper
      simpa only [currentCanonical, historicalCanonicalValue,
        inputEventCanonicalValue, historicalInputCell,
        CCLCanonicalEvent.currentFormulaInputCell, classification,
        currentSigns, cell, finalSigns, selectedCompletePath] using same
    rcases lt_or_gt_of_ne historicalNonzero with negative | positive
    · exact ne_of_lt ((agreement .negative).2 negative)
    · exact ne_of_gt ((agreement .positive).2 positive)
  have clearedLower :=
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
      classification.branch.relations classification.parent currentSigns
      polynomialMember currentNonzero currentLower currentUpper
  have denominator := historicalBoundaryParameter_denominator_ne selected
    squarefree radius radiusPositive
  have denominatorBounds := historicalBoundaryParameter_candidate_bounds
    selected squarefree radius radiusPositive
  have denominatorLe := selectedEventDenominator_le
    selected.toIncrementalPayload denominatorBounds.1 denominatorBounds.2
  have clearedIdentity :
      |(clearedForm atom.form (selectedCompletePath selected)).eval t| =
        |(denominatorNorm (selectedCompletePath selected)).eval t| *
          |atom.form.eval ((selectedCompletePath selected).value t)| := by
    rw [eval_clearedForm atom.form (selectedCompletePath selected) t denominator,
      abs_mul]
  unfold historicalCurrentStrictFormMargin
  apply (div_le_iff₀ (selectedEventDenominatorUpper_pos selected)).2
  calc
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
        classification.branch.relations classification.parent currentSigns ≤
      |(clearedForm atom.form (selectedCompletePath selected)).eval t| := clearedLower
    _ = |(denominatorNorm (selectedCompletePath selected)).eval t| *
        |atom.form.eval ((selectedCompletePath selected).value t)| := clearedIdentity
    _ ≤ selectedEventDenominatorUpper selected *
        |atom.form.eval ((selectedCompletePath selected).value t)| :=
      mul_le_mul_of_nonneg_right denominatorLe (abs_nonneg _)
    _ = |atom.form.eval ((selectedCompletePath selected).value t)| *
        selectedEventDenominatorUpper selected := by ring

/-- The selected-child strict margin likewise holds throughout the final
historical slope cell. -/
theorem historicalChildStrictFormMargin_le_pathValue
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) {t : ℚ}
    (lower : (historicalSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤
      (historicalSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (member : form ∈ strictPriorForms
      (inputAdvanceFormula (RawParser.parse current.word) selected.bit)
      (historicalCanonicalValue selected)) :
    historicalChildStrictFormMargin selected ≤
      |form.eval ((selectedCompletePath selected).value t)| := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  let classification := CCLCanonicalEvent.currentFormulaClassification
    selected.candidate.inputCell
  let currentSigns := classification.branch.computeEventSigns
    classification.parent
  let cell := historicalInputCell selected
  let signs := cell.branch.computeEventSigns cell.parent
  have cellLower : signs.refined.interval.lower ≤ t :=
    (historicalSlopeSigns_refines_inputCell selected).1.trans lower
  have cellUpper : t ≤ signs.refined.interval.upper :=
    upper.trans (historicalSlopeSigns_refines_inputCell selected).2
  have currentLower : currentSigns.refined.interval.lower ≤ t :=
    signs.refines.1.trans cellLower
  have currentUpper : t ≤ currentSigns.refined.interval.upper :=
    cellUpper.trans signs.refines.2
  have candidateLower :
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined.interval.lower ≤ t :=
    classification.signRefines.1.trans currentLower
  have candidateUpper : t ≤
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined.interval.upper :=
    currentUpper.trans classification.signRefines.2
  have polynomialMember : clearedForm atom.form (selectedCompletePath selected) ∈
      inputEventPolynomials (RawParser.parse current.word)
        (selectedCompletePath selected) :=
    clearedForm_mem_inputEventPolynomials_of_advance_atom
      (RawParser.parse current.word) (selectedCompletePath selected) selected.bit atom
      (satisfyingAtoms_mem_formulaAtoms _ _
        (strictSatisfyingAtoms_source atomMember))
  have canonicalNonzero :
      historicalCanonicalValue selected atom.form ≠ 0 :=
    strictPriorForms_value_ne _ _ member
  have clearedLower := ConditionRelations.strictMargin_le_abs_eval
    cell.branch.relations cell.parent signs polynomialMember
    (by simpa only [historicalCanonicalValue, inputEventCanonicalValue,
      cell, signs, selectedCompletePath] using canonicalNonzero)
    cellLower cellUpper
  have denominator := cell.path_denominator_ne_on_cell cellLower cellUpper
  have denominatorLe := selectedEventDenominator_le
    selected.toIncrementalPayload candidateLower candidateUpper
  have clearedIdentity :
      |(clearedForm atom.form (selectedCompletePath selected)).eval t| =
        |(denominatorNorm (selectedCompletePath selected)).eval t| *
          |atom.form.eval ((selectedCompletePath selected).value t)| := by
    rw [eval_clearedForm atom.form (selectedCompletePath selected) t denominator,
      abs_mul]
  unfold historicalChildStrictFormMargin
  apply (div_le_iff₀ (selectedEventDenominatorUpper_pos selected)).2
  calc
    ConditionRelations.strictMargin cell.branch.relations cell.parent signs ≤
      |(clearedForm atom.form (selectedCompletePath selected)).eval t| := clearedLower
    _ = |(denominatorNorm (selectedCompletePath selected)).eval t| *
        |atom.form.eval ((selectedCompletePath selected).value t)| := clearedIdentity
    _ ≤ selectedEventDenominatorUpper selected *
        |atom.form.eval ((selectedCompletePath selected).value t)| :=
      mul_le_mul_of_nonneg_right denominatorLe (abs_nonneg _)
    _ = |atom.form.eval ((selectedCompletePath selected).value t)| *
        selectedEventDenominatorUpper selected := by ring

theorem historicalChildStrictFormMargin_le_boundaryPoint
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {form : HermitianForm}
    (member : form ∈ strictPriorForms
      (inputAdvanceFormula (RawParser.parse current.word) selected.bit)
      (historicalCanonicalValue selected)) :
    historicalChildStrictFormMargin selected ≤
      |form.eval (historicalBoundaryPoint selected squarefree radius
        radiusPositive)| := by
  rcases List.mem_map.mp member with ⟨atom, atomMember, rfl⟩
  let cell := historicalInputCell selected
  let signs := cell.branch.computeEventSigns cell.parent
  let t := historicalBoundaryParameter selected squarefree radius radiusPositive
  have slopeBounds := historicalBoundaryParameter_bounds selected squarefree
    radius radiusPositive
  have cellLower : signs.refined.interval.lower ≤ t :=
    (historicalSlopeSigns_refines_inputCell selected).1.trans slopeBounds.1
  have cellUpper : t ≤ signs.refined.interval.upper :=
    slopeBounds.2.trans (historicalSlopeSigns_refines_inputCell selected).2
  have polynomialMember : clearedForm atom.form (selectedCompletePath selected) ∈
      inputEventPolynomials (RawParser.parse current.word)
        (selectedCompletePath selected) :=
    clearedForm_mem_inputEventPolynomials_of_advance_atom
      (RawParser.parse current.word) (selectedCompletePath selected) selected.bit atom
      (satisfyingAtoms_mem_formulaAtoms _ _
        (strictSatisfyingAtoms_source atomMember))
  have canonicalNonzero :
      historicalCanonicalValue selected atom.form ≠ 0 :=
    strictPriorForms_value_ne _ _ member
  have clearedLower :=
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
      cell.branch.relations cell.parent signs polynomialMember
      (by simpa only [historicalCanonicalValue, inputEventCanonicalValue,
        cell, signs, selectedCompletePath] using canonicalNonzero)
      cellLower cellUpper
  have denominator := historicalBoundaryParameter_denominator_ne selected
    squarefree radius radiusPositive
  have denominatorBounds := historicalBoundaryParameter_candidate_bounds
    selected squarefree radius radiusPositive
  have denominatorLe := selectedEventDenominator_le
    selected.toIncrementalPayload denominatorBounds.1 denominatorBounds.2
  have clearedIdentity :
      |(clearedForm atom.form (selectedCompletePath selected)).eval t| =
        |(denominatorNorm (selectedCompletePath selected)).eval t| *
          |atom.form.eval ((selectedCompletePath selected).value t)| := by
    rw [eval_clearedForm atom.form (selectedCompletePath selected) t denominator,
      abs_mul]
  unfold historicalChildStrictFormMargin
  apply (div_le_iff₀ (selectedEventDenominatorUpper_pos selected)).2
  calc
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
        cell.branch.relations cell.parent signs ≤
      |(clearedForm atom.form (selectedCompletePath selected)).eval t| := clearedLower
    _ = |(denominatorNorm (selectedCompletePath selected)).eval t| *
        |atom.form.eval ((selectedCompletePath selected).value t)| := clearedIdentity
    _ ≤ selectedEventDenominatorUpper selected *
        |atom.form.eval ((selectedCompletePath selected).value t)| :=
      mul_le_mul_of_nonneg_right denominatorLe (abs_nonneg _)
    _ = |atom.form.eval ((selectedCompletePath selected).value t)| *
        selectedEventDenominatorUpper selected := by ring

theorem historicalStrictFormMargin_le_boundaryPoint
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {form : HermitianForm}
    (member : form ∈ historicalStrictPriorForms selected) :
    historicalStrictFormMargin selected ≤
      |form.eval (historicalBoundaryPoint selected squarefree radius
        radiusPositive)| := by
  rw [historicalStrictPriorForms_eq_append] at member
  rcases List.mem_append.mp member with currentMember | childMember
  · exact (min_le_left _ _).trans
      (historicalCurrentStrictFormMargin_le_boundaryPoint selected squarefree
        radius radiusPositive currentMember)
  · exact (min_le_right _ _).trans
      (historicalChildStrictFormMargin_le_boundaryPoint selected squarefree
        radius radiusPositive childMember)

/-- One computable positive radius transfers every historical strict sign
from the rational boundary approximation to the represented base. -/
def historicalStrictRadius
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) : ℚ :=
  FTA.Maximality.positiveMinimum
    ((historicalStrictPriorForms selected).map fun form =>
      historicalStrictFormMargin selected /
        (20 * variationMajorant form separation.state.box))

theorem historicalStrictRadius_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) :
    0 < historicalStrictRadius selected := by
  apply FTA.Maximality.positiveMinimum_pos
  intro value valueMember
  rw [List.mem_map] at valueMember
  rcases valueMember with ⟨form, _formMember, rfl⟩
  exact div_pos (historicalStrictFormMargin_pos selected)
    (mul_pos (by norm_num)
      (variationMajorant_pos form separation.state.box))

theorem historicalStrictRadius_le_form
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) {form : HermitianForm}
    (member : form ∈ historicalStrictPriorForms selected) :
    historicalStrictRadius selected ≤ historicalStrictFormMargin selected /
      (20 * variationMajorant form separation.state.box) := by
  apply FTA.Maximality.positiveMinimum_le_of_mem
  exact List.mem_map.mpr ⟨form, member, rfl⟩

theorem historicalConvergentGridBase_strict
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < historicalStrictRadius selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    ∀ form ∈ historicalStrictPriorForms selected,
      0 < historicalCanonicalValue selected form * form.eval base.point := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventPoint := historicalBoundaryPoint selected squarefree radius
    radiusPositive
  change ∀ form ∈ historicalStrictPriorForms selected,
    0 < historicalCanonicalValue selected form * form.eval base.point
  intro form member
  have radiusForm : radius < historicalStrictFormMargin selected /
      (20 * variationMajorant form separation.state.box) :=
    radiusSmall.trans_le (historicalStrictRadius_le_form selected member)
  have coefficientPositive :
      0 < 20 * variationMajorant form separation.state.box :=
    mul_pos (by norm_num)
      (variationMajorant_pos form separation.state.box)
  have variationSmall :
      10 * variationMajorant form separation.state.box * radius <
        historicalStrictFormMargin selected := by
    have scaled := (lt_div_iff₀ coefficientPositive).mp radiusForm
    have variationPositive := variationMajorant_pos form separation.state.box
    nlinarith
  have baseInside : separation.state.box.Contains base.point :=
    nextRefines.contains base.strict.contains
  have eventInside : separation.state.box.Contains eventPoint :=
    (historicalBoundaryState_refines_separation selected squarefree
      elimination radius radiusPositive).contains
        (historicalBoundaryState_contains_point selected squarefree
          elimination radius radiusPositive)
  have variation := abs_eval_sub_eval_le form baseInside eventInside
  have distance := convergentGridBase_inputEvent_distance current separation
    (historicalSlopeInputCell selected) squarefree degreeNonzero elimination
    next nextRefines radius radiusPositive
  have variationLe :
      |form.eval base.point - form.eval eventPoint| ≤
        10 * variationMajorant form separation.state.box * radius := by
    apply variation.trans
    exact mul_le_mul_of_nonneg_left distance
      (variationMajorant_pos form separation.state.box).le |>.trans_eq (by ring)
  have eventMargin := historicalStrictFormMargin_le_boundaryPoint selected
    squarefree radius radiusPositive member
  have close : |form.eval eventPoint - form.eval base.point| <
      |form.eval eventPoint| := by
    rw [abs_sub_comm]
    exact variationLe.trans_lt (variationSmall.trans_le eventMargin)
  have eventBaseSame :
      0 < form.eval eventPoint * form.eval base.point :=
    mul_pos_of_abs_sub_lt_abs_left close
  have bounds := historicalBoundaryParameter_bounds selected squarefree radius
    radiusPositive
  have eventSign := historicalStrictPriorForms_mul_eval_pos selected
    bounds.1 bounds.2 form member
  exact mul_pos_trans (by
    simpa only [eventPoint, historicalBoundaryPoint] using eventSign)
    eventBaseSame

/-- Canonical localized historical base in any later winding-one box. -/
def historicalConvergentGridBase
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < historicalStrictRadius selected) :
    HistoricalGridBase current separation selected next :=
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  { point := base.point
    strict := base.strict
    nonzero := base.nonzero
    historicalStrict := by
      simpa only [base] using historicalConvergentGridBase_strict current
        separation selected squarefree degreeNonzero elimination next
        nextRefines radius radiusPositive radiusSmall }

/-- The successful historical classifier supplies a tangent certificate at
the rational boundary approximation used for any requested radius. -/
def historicalBoundaryClassifiedTangentDirection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    TangentDirection (historicalActiveOwnerForms selected)
      (historicalBoundaryPoint selected squarefree radius radiusPositive) :=
  historicalClassifiedTangentDirectionAt search
    (historicalBoundaryParameter selected squarefree radius radiusPositive)
    (historicalBoundaryParameter_bounds selected squarefree radius
      radiusPositive).1
    (historicalBoundaryParameter_bounds selected squarefree radius
      radiusPositive).2

/-- A fixed positive lower bound for the tangent-stability radius of every
historical boundary approximation using the classified vector. -/
def historicalSlopeTangentRadiusLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  FTA.Maximality.positiveMinimum
    ((historicalActiveOwnerForms selected).map fun form =>
      historicalSlopeDirectionalLower selected /
        (2 * FTA.CCLTangentStability.slopeVariationCoefficient form))

theorem historicalSlopeTangentRadiusLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < historicalSlopeTangentRadiusLower selected := by
  apply FTA.Maximality.positiveMinimum_pos
  intro value member
  rw [List.mem_map] at member
  rcases member with ⟨form, _formMember, rfl⟩
  exact div_pos (historicalSlopeDirectionalLower_pos selected)
    (mul_pos (by norm_num)
      (FTA.CCLTangentStability.slopeVariationCoefficient_pos form))

theorem historicalSlopeTangentRadiusLower_le_stabilityRadius
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    historicalSlopeTangentRadiusLower selected ≤
      FTA.CCLTangentStability.tangentStabilityRadius
        (historicalBoundaryClassifiedTangentDirection search squarefree
          radius radiusPositive) := by
  unfold FTA.CCLTangentStability.tangentStabilityRadius
  apply FTA.Maximality.le_positiveMinimum
    (FTA.Maximality.positiveMinimum_le_one _)
  intro value valueMember
  rw [List.mem_map] at valueMember
  rcases valueMember with ⟨form, formMember, rfl⟩
  have lowerMember : historicalSlopeDirectionalLower selected /
        (2 * FTA.CCLTangentStability.slopeVariationCoefficient form) ∈
      (historicalActiveOwnerForms selected).map fun item =>
        historicalSlopeDirectionalLower selected /
          (2 * FTA.CCLTangentStability.slopeVariationCoefficient item) :=
    List.mem_map.mpr ⟨form, formMember, rfl⟩
  apply (FTA.Maximality.positiveMinimum_le_of_mem lowerMember).trans
  have slopeLe := historicalSlopeDirectionalLower_le search
    (historicalBoundaryParameter_bounds selected squarefree radius
      radiusPositive).1
    (historicalBoundaryParameter_bounds selected squarefree radius
      radiusPositive).2 formMember
  change historicalSlopeDirectionalLower selected /
      (2 * FTA.CCLTangentStability.slopeVariationCoefficient form) ≤
    directionalSlope form
        (historicalBoundaryPoint selected squarefree radius radiusPositive)
        direction /
      (2 * FTA.CCLTangentStability.slopeVariationCoefficient form)
  exact (div_le_div_iff_of_pos_right (mul_pos (by norm_num)
    (FTA.CCLTangentStability.slopeVariationCoefficient_pos form))).2 slopeLe

/-- Fixed request-radius cap retaining half of the historical tangent
stability margin after the `10 * radius` convergence estimate. -/
def historicalSlopeEventRadiusCap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  historicalSlopeTangentRadiusLower selected / 20

theorem historicalSlopeEventRadiusCap_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < historicalSlopeEventRadiusCap selected :=
  div_pos (historicalSlopeTangentRadiusLower_pos selected) (by norm_num)

theorem historicalSlopeEventRadiusCap_le_eventTangentRadiusCap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    historicalSlopeEventRadiusCap selected ≤ eventTangentRadiusCap
      (historicalBoundaryClassifiedTangentDirection search squarefree radius
        radiusPositive) := by
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 20)).2
  exact historicalSlopeTangentRadiusLower_le_stabilityRadius search squarefree
    radius radiusPositive

/-- Transfer the fixed classified historical vector from the rational event
point to the represented base in any later winding-one box. -/
def historicalConvergentGridBase_classifiedTangentDirection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusLe : radius ≤ historicalSlopeEventRadiusCap selected) :
    TangentDirection (historicalActiveOwnerForms selected)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point := by
  let tangent := historicalBoundaryClassifiedTangentDirection search
    squarefree radius radiusPositive
  apply FTA.CCLTangentStability.TangentDirection.atNearby tangent
  unfold FTA.CCLTangentStability.coordinateDistance
  have distance :
      |(convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point.re -
          (historicalBoundaryPoint selected squarefree radius
            radiusPositive).re| +
        |(convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point.im -
          (historicalBoundaryPoint selected squarefree radius
            radiusPositive).im| ≤ 10 * radius := by
    rw [historicalBoundaryPoint_eq_shrinkingInputEventPoint]
    exact convergentGridBase_inputEvent_distance current separation
      (historicalSlopeInputCell selected) squarefree degreeNonzero elimination
      next nextRefines radius radiusPositive
  apply distance.trans_lt
  have radiusLePoint : radius ≤ eventTangentRadiusCap tangent :=
    radiusLe.trans
      (historicalSlopeEventRadiusCap_le_eventTangentRadiusCap search
        squarefree radius radiusPositive)
  exact (mul_le_mul_of_nonneg_left radiusLePoint (by norm_num)).trans_lt
    (ten_mul_eventTangentRadiusCap_lt_stabilityRadius tangent)

/-- Under the same static cap, the exhaustive rational cone solver succeeds
at the represented historical base. -/
theorem rationalTangentDirectionCertificate?_isSome_at_historicalConvergentGridBase
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusLe : radius ≤ historicalSlopeEventRadiusCap selected) :
    (rationalTangentDirectionCertificate?
      (historicalActiveOwnerForms selected)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point).isSome := by
  let tangent := historicalConvergentGridBase_classifiedTangentDirection
    current separation selected squarefree degreeNonzero elimination next
    nextRefines search radius radiusPositive radiusLe
  apply rationalTangentDirectionCertificate?_isSome_of_exists
  exact ⟨tangent.vector, tangent.slopes⟩

/-- Finite data sufficient for one complete historical owner perturbation. -/
structure HistoricalGridData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (_nextRefines : next.box.Refines separation.state.box) where
  base : QI
  baseStrict : next.box.StrictContains base
  baseNonzero : base ≠ 0
  direction : TangentDirection (historicalActiveOwnerForms selected) base
  strictAtBase :
    ∀ form ∈ historicalStrictPriorForms selected,
      0 < historicalCanonicalValue selected form * form.eval base
  activeResidual :
    ∀ form ∈ historicalActiveOwnerForms selected,
      |form.eval base| < approximateBoundaryBudget direction
        (historicalGridPriorForms selected base next.box)

/-- Executable complete historical-grid attempt.  The exact rational cone
solver chooses the direction; the only subsequent decision is the displayed
finite residual bound at the localized base. -/
def historicalGridData?
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (base : HistoricalGridBase current separation selected next) :
    Option (HistoricalGridData current separation selected next nextRefines) :=
  match rationalTangentDirectionCertificate?
      (historicalActiveOwnerForms selected) base.point with
  | none => none
  | some direction =>
      if residualCheck :
          ∀ form ∈ historicalActiveOwnerForms selected,
            |form.eval base.point| < approximateBoundaryBudget direction
              (historicalGridPriorForms selected base.point next.box)
      then some
        { base := base.point
          baseStrict := base.strict
          baseNonzero := base.nonzero
          direction := direction
          strictAtBase := base.historicalStrict
          activeResidual := residualCheck }
      else none

theorem historicalGridData?_isSome_of_direction
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (base : HistoricalGridBase current separation selected next)
    (direction : TangentDirection (historicalActiveOwnerForms selected)
      base.point)
    (directionSearch : rationalTangentDirectionCertificate?
      (historicalActiveOwnerForms selected) base.point = some direction)
    (residual : ∀ form ∈ historicalActiveOwnerForms selected,
      |form.eval base.point| < approximateBoundaryBudget direction
        (historicalGridPriorForms selected base.point next.box)) :
    (historicalGridData? current separation selected next nextRefines
      base).isSome := by
  unfold historicalGridData?
  rw [directionSearch]
  simp only
  rw [dif_pos residual]
  rfl

def historicalGridDataOfIsSome
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (base : HistoricalGridBase current separation selected next)
    (success : (historicalGridData? current separation selected next
      nextRefines base).isSome) :
    HistoricalGridData current separation selected next nextRefines :=
  (historicalGridData? current separation selected next nextRefines base).get
    success

/-- The exact rational cone certificate selected at a convergent historical
base once the fixed classified direction proves that the solver succeeds. -/
def historicalConvergentRationalDirection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusLe : radius ≤ historicalSlopeEventRadiusCap selected) :
    TangentDirection (historicalActiveOwnerForms selected)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point :=
  (rationalTangentDirectionCertificate?
    (historicalActiveOwnerForms selected)
    (convergentGridBase current separation squarefree elimination next
      nextRefines radius radiusPositive).point).get
      (rationalTangentDirectionCertificate?_isSome_at_historicalConvergentGridBase
        current separation selected squarefree degreeNonzero elimination next
        nextRefines search radius radiusPositive radiusLe)

theorem historicalConvergentRationalDirection_search
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusLe : radius ≤ historicalSlopeEventRadiusCap selected) :
    rationalTangentDirectionCertificate?
      (historicalActiveOwnerForms selected)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point =
      some (historicalConvergentRationalDirection current separation selected
        squarefree degreeNonzero elimination next nextRefines search radius
        radiusPositive radiusLe) := by
  unfold historicalConvergentRationalDirection
  exact (Option.some_get _).symm

/-- All finite checks in the complete historical-grid program succeed once
the convergence radius obeys the strict/tangent caps and its common linear
residual fits below the displayed perturbation budget. -/
theorem historicalConvergentGridData?_isSome
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusStrict : radius < historicalStrictRadius selected)
    (radiusTangent : radius ≤ historicalSlopeEventRadiusCap selected)
    (residualBudget :
      let base := convergentGridBase current separation squarefree elimination
        next nextRefines radius radiusPositive
      let direction := historicalConvergentRationalDirection current
        separation selected squarefree degreeNonzero elimination next
        nextRefines search radius radiusPositive radiusTangent
      historicalActiveCoefficientSum selected * radius <
        approximateBoundaryBudget direction
          (historicalGridPriorForms selected base.point next.box)) :
    (historicalGridData? current separation selected next nextRefines
      (historicalConvergentGridBase current separation selected squarefree
        degreeNonzero elimination next nextRefines radius radiusPositive
        radiusStrict)).isSome := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let gridBase := historicalConvergentGridBase current separation selected
    squarefree degreeNonzero elimination next nextRefines radius radiusPositive
    radiusStrict
  let direction := historicalConvergentRationalDirection current separation
    selected squarefree degreeNonzero elimination next nextRefines search radius
    radiusPositive radiusTangent
  apply historicalGridData?_isSome_of_direction current separation selected
    next nextRefines gridBase direction
  · change rationalTangentDirectionCertificate?
        (historicalActiveOwnerForms selected) base.point = some direction
    simpa only [direction, base] using
      historicalConvergentRationalDirection_search current separation selected
        squarefree degreeNonzero elimination next nextRefines search radius
        radiusPositive radiusTangent
  · intro form member
    change |form.eval base.point| < approximateBoundaryBudget direction
      (historicalGridPriorForms selected base.point next.box)
    have activeSmall := historicalConvergentGridBase_active_lt_sum current
      separation selected squarefree degreeNonzero elimination next nextRefines
      radius radiusPositive member
    have budget : historicalActiveCoefficientSum selected * radius <
        approximateBoundaryBudget direction
          (historicalGridPriorForms selected base.point next.box) := by
      simpa only [base, direction] using residualBudget
    exact activeSmall.trans budget

namespace HistoricalGridData

theorem priors_nonzero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines) :
    ∀ form ∈ historicalGridPriorForms selected data.base next.box,
      form.eval data.base ≠ 0 := by
  intro form member
  simp only [historicalGridPriorForms, List.mem_append,
    List.mem_singleton] at member
  rcases member with (historicalStrict | boxForm) | normForm
  · intro zero
    have positive := data.strictAtBase form historicalStrict
    rw [zero] at positive
    norm_num at positive
  · exact (boxForms_pos_of_strictContains data.baseStrict form boxForm).ne'
  · subst form
    simpa [eval_affineNormForm] using (normSq_pos data.baseNonzero).ne'

/-- Computed rational owner-grid point. -/
def point
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines) :
    QI :=
  step data.base
    (multiOwnerEpsilon data.direction
      (historicalGridPriorForms selected data.base next.box))
    data.direction.vector

theorem entered
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines) :
    ∀ form ∈ historicalActiveOwnerForms selected,
      0 < form.eval data.point := by
  simpa only [point] using
    enters_all_boundaries_of_residual data.direction
      (historicalGridPriorForms selected data.base next.box)
      data.priors_nonzero data.activeResidual

theorem preserved
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines) :
    ∀ form ∈ historicalGridPriorForms selected data.base next.box,
      0 < form.eval data.base * form.eval data.point := by
  simpa only [point] using
    preserves_all_priors data.direction
      (historicalGridPriorForms selected data.base next.box)
      data.priors_nonzero

theorem point_inside
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines) :
    next.box.Contains data.point := by
  change next.box.Contains (step data.base
    (multiOwnerEpsilon data.direction
      (historicalGridPriorForms selected data.base next.box))
    data.direction.vector)
  apply multiOwner_step_mem_box_of_strict_priors data.direction
    data.priors_nonzero next.box
    (boxForms_pos_of_strictContains data.baseStrict)
  intro form member
  simp [historicalGridPriorForms, member]

theorem point_nonzero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines) :
    data.point ≠ 0 := by
  let normForm := affineNormForm 1 0
  have normMember : normForm ∈
      historicalGridPriorForms selected data.base next.box := by
    simp [historicalGridPriorForms, normForm]
  have product := data.preserved normForm normMember
  have basePositive : 0 < normForm.eval data.base := by
    simpa [normForm, eval_affineNormForm] using normSq_pos data.baseNonzero
  have pointPositive : 0 < normForm.eval data.point := by
    rcases mul_pos_iff.mp product with signs | signs
    · exact signs.2
    · exact (not_lt_of_ge basePositive.le signs.1).elim
  intro zero
  rw [zero] at pointPositive
  norm_num [normForm, eval_affineNormForm, normSq] at pointPositive

theorem strict_same_sign
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines) :
    ∀ form ∈ historicalStrictPriorForms selected,
      0 < historicalCanonicalValue selected form * form.eval data.point := by
  intro form member
  apply mul_pos_trans (data.strictAtBase form member)
  apply data.preserved form
  simp [historicalGridPriorForms, member]

theorem formula_holds
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected) :
    (historicalOwnerFormula (RawParser.parse current.word) selected.bit).Holds
      data.point := by
  apply formula_holds_of_owner_form_lists_nonnegative
    (historicalOwnerFormula (RawParser.parse current.word) selected.bit)
    (historicalCanonicalValue selected) data.point
    (historicalOwnerFormula_canonical_holds current separation selected
      squarefree degreeNonzero elimination valid)
    (historicalOwnerFormula_noZeroTests
      (RawParser.parse current.word) selected.bit)
  · intro form member
    exact (data.entered form (by
      simpa only [historicalActiveOwnerForms] using member)).le
  · intro form member
    exact data.strict_same_sign form (by
      simpa only [historicalStrictPriorForms] using member)

theorem represented_append
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected) :
    RawParserSemantics.Represented (current.word ++ [selected.bit])
      data.point := by
  have complete := data.formula_holds squarefree degreeNonzero elimination valid
  have components :
      (inputStateFormula (RawParser.parse current.word)).Holds data.point ∧
        (inputAdvanceFormula (RawParser.parse current.word)
          selected.bit).Holds data.point := by
    simpa only [historicalOwnerFormula, Formula.Holds] using complete
  have insideSeparation : separation.state.box.Contains data.point :=
    nextRefines.contains data.point_inside
  have inverseDenominator :=
    CCLBranchEvidence.separation_denominator_ne separation insideSeparation
  have representedCurrent : RawParserSemantics.Represented current.word
      data.point :=
    represented_of_inputStateFormula current.word data.point
      inverseDenominator components.1
  exact CCLBranchSampling.represented_append_of_inputFormula current.word
    data.point selected.bit inverseDenominator representedCurrent components.2

/-- Forms whose strict orientation makes the complete historical formula
stable after the grid point has entered every formerly active owner face. -/
def stableForms
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload separation) : List HermitianForm :=
  historicalActiveOwnerForms selected ++ historicalStrictPriorForms selected

theorem stableForms_nonzero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines) :
    ∀ form ∈ stableForms selected, form.eval data.point ≠ 0 := by
  intro form member
  rcases List.mem_append.mp member with active | strict
  · exact (data.entered form active).ne'
  · intro zero
    have positive := data.strict_same_sign form strict
    rw [zero] at positive
    norm_num at positive

theorem represented_append_of_stableForms
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    {nextPoint : QI} (inside : separation.state.box.Contains nextPoint)
    (sameSigns : ∀ form ∈ stableForms selected,
      0 < form.eval data.point * form.eval nextPoint) :
    RawParserSemantics.Represented (current.word ++ [selected.bit])
      nextPoint := by
  have activeNonnegative : ∀ form ∈ historicalActiveOwnerForms selected,
      0 ≤ form.eval nextPoint := by
    intro form member
    have entered := data.entered form member
    have preserved := sameSigns form
      (List.mem_append_left _ member)
    have positive : 0 < form.eval nextPoint := by
      nlinarith
    exact positive.le
  have strictSameSign : ∀ form ∈ historicalStrictPriorForms selected,
      0 < historicalCanonicalValue selected form * form.eval nextPoint := by
    intro form member
    apply mul_pos_trans (data.strict_same_sign form member)
    apply sameSigns form
    exact List.mem_append_right _ member
  have complete :
      (historicalOwnerFormula (RawParser.parse current.word)
        selected.bit).Holds nextPoint := by
    apply formula_holds_of_owner_form_lists_nonnegative
      (historicalOwnerFormula (RawParser.parse current.word) selected.bit)
      (historicalCanonicalValue selected) nextPoint
      (historicalOwnerFormula_canonical_holds current separation selected
        squarefree degreeNonzero elimination valid)
      (historicalOwnerFormula_noZeroTests
        (RawParser.parse current.word) selected.bit)
    · simpa only [historicalActiveOwnerForms] using activeNonnegative
    · simpa only [historicalStrictPriorForms] using strictSameSign
  have components :
      (inputStateFormula (RawParser.parse current.word)).Holds nextPoint ∧
        (inputAdvanceFormula (RawParser.parse current.word)
          selected.bit).Holds nextPoint := by
    simpa only [historicalOwnerFormula, Formula.Holds] using complete
  have inverseDenominator :=
    CCLBranchEvidence.separation_denominator_ne separation inside
  have representedCurrent : RawParserSemantics.Represented current.word
      nextPoint :=
    represented_of_inputStateFormula current.word nextPoint
      inverseDenominator components.1
  exact CCLBranchSampling.represented_append_of_inputFormula current.word
    nextPoint selected.bit inverseDenominator representedCurrent components.2

/-- One complete historical grid record supplies the persistent local
semantic certificate expected by the coupled-state controller. -/
def stableOutcome
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected) :
    CCLCoupledTrack.StableRepresentedOutcome
      (current.word ++ [selected.bit]) next.box separation.state.box where
  point := data.point
  inside := data.point_inside
  nonzero := data.point_nonzero
  semantics := data.represented_append squarefree degreeNonzero elimination valid
  priors := stableForms selected
  priorsNonzero := data.stableForms_nonzero
  stable := by
    intro nextPoint inside sameSigns
    exact data.represented_append_of_stableForms squarefree degreeNonzero
      elimination valid inside sameSigns

def ownerSample
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {next : WindingOneState p (RatBox.symmetric R hR)}
    {nextRefines : next.box.Refines separation.state.box}
    (data : HistoricalGridData current separation selected next nextRefines)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected) :
    OwnerInputSample current selected.bit next separation.state.box where
  outcome := data.stableOutcome squarefree degreeNonzero elimination valid

end HistoricalGridData

/-- The sole remaining geometric input: complete historical grid data in
every later nested winding-one box. -/
structure HistoricalGridDataFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation) where
  data : (next : WindingOneState p (RatBox.symmetric R hR)) →
    (nextRefines : next.box.Refines separation.state.box) →
      HistoricalGridData current separation selected next nextRefines

/-- Fully executable presentation of the remaining family obligation: choose
a localized base in every later box and prove that its finite grid search
succeeds. -/
structure HistoricalGridSearchFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation) where
  base : (next : WindingOneState p (RatBox.symmetric R hR)) →
    next.box.Refines separation.state.box →
      HistoricalGridBase current separation selected next
  success : ∀ next nextRefines,
    (historicalGridData? current separation selected next nextRefines
      (base next nextRefines)).isSome

/-- Quantitative presentation of the remaining per-refinement choice.  Its
radius fields are entirely rational and its only non-cap field is the finite
residual-budget inequality for the exact cone direction chosen at that base. -/
structure HistoricalConvergentGridSuccessFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection) where
  radius : (next : WindingOneState p (RatBox.symmetric R hR)) →
    next.box.Refines separation.state.box → ℚ
  radiusPositive : ∀ next nextRefines, 0 < radius next nextRefines
  radiusStrict : ∀ next nextRefines,
    radius next nextRefines < historicalStrictRadius selected
  radiusTangent : ∀ next nextRefines,
    radius next nextRefines ≤ historicalSlopeEventRadiusCap selected
  residualBudget : ∀ next nextRefines,
    let request := radius next nextRefines
    let positive := radiusPositive next nextRefines
    let tangent := radiusTangent next nextRefines
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines request positive
    let direction := historicalConvergentRationalDirection current separation
      selected squarefree degreeNonzero elimination next nextRefines search
      request positive tangent
    historicalActiveCoefficientSum selected * request <
      approximateBoundaryBudget direction
        (historicalGridPriorForms selected base.point next.box)

/-- A quantitative convergent family is exactly the executable historical
grid family required by the persistent semantic package. -/
def HistoricalConvergentGridSuccessFamily.searchFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    {squarefree : GaussianSquarefreeCertificate p}
    {degreeNonzero : p.toPolynomial.natDegree ≠ 0}
    {D : ℕ} {elimination : AxisEliminationCertificate p D}
    {classifiedDirection : QI}
    {search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection}
    (family : HistoricalConvergentGridSuccessFamily current separation selected
      squarefree degreeNonzero elimination search) :
    HistoricalGridSearchFamily current separation selected where
  base next nextRefines := historicalConvergentGridBase current separation
    selected squarefree degreeNonzero elimination next nextRefines
    (family.radius next nextRefines)
    (family.radiusPositive next nextRefines)
    (family.radiusStrict next nextRefines)
  success next nextRefines :=
    historicalConvergentGridData?_isSome current separation selected squarefree
      degreeNonzero elimination next nextRefines search
      (family.radius next nextRefines)
      (family.radiusPositive next nextRefines)
      (family.radiusStrict next nextRefines)
      (family.radiusTangent next nextRefines)
      (family.residualBudget next nextRefines)

def HistoricalGridSearchFamily.dataFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    (family : HistoricalGridSearchFamily current separation selected) :
    HistoricalGridDataFamily current separation selected where
  data next nextRefines := historicalGridDataOfIsSome current separation
    selected next nextRefines (family.base next nextRefines)
      (family.success next nextRefines)

/-- A uniform family of complete historical grids discharges all persistent
sample coherence fields automatically. -/
def HistoricalGridDataFamily.persistentSamples
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    (family : HistoricalGridDataFamily current separation selected)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected) :
    PersistentEventOwnerSamples current separation selected where
  sample next nextRefines :=
    (family.data next nextRefines).ownerSample squarefree degreeNonzero
      elimination valid
  sample_priors := by
    intro next nextRefines
    rfl
  sample_sameSigns := by
    intro next nextRefines form member
    let baseData := family.data separation.state
      (RatBox.refines_refl separation.state.box)
    let nextData := family.data next nextRefines
    change form ∈ HistoricalGridData.stableForms selected at member
    change 0 < form.eval baseData.point * form.eval nextData.point
    rcases List.mem_append.mp member with active | strict
    · exact mul_pos (baseData.entered form active)
        (nextData.entered form active)
    · exact CCLCoupledTrack.sameSign_of_common_anchor
        (baseData.strict_same_sign form strict)
        (nextData.strict_same_sign form strict)

/-- Close an equality-owned event all the way to a concrete machine step once
the uniform historical grid family has been constructed. -/
def HistoricalGridDataFamily.step
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    (family : HistoricalGridDataFamily current separation selected)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected) :
    CCLCoupledTrack.StepResult current :=
  nextOfPersistentEventPayload current separation selected
    (family.persistentSamples squarefree degreeNonzero elimination valid)

def HistoricalGridSearchFamily.step
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload separation}
    (family : HistoricalGridSearchFamily current separation selected)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected) :
    CCLCoupledTrack.StepResult current :=
  family.dataFamily.step squarefree degreeNonzero elimination valid

end CCLHistoricalOwnerGrid
end FTA
