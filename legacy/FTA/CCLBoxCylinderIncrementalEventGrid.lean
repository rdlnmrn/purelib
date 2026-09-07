import FTA.CCLBoxCylinderCheckpoint
import FTA.CCLBoundaryPreservingOwner
import FTA.CCLCompletedMetricContraction
import FTA.CCLEventTangentSigns
import FTA.CCLGuardedEventGrid
import FTA.CCLIncrementalCanonicalOwner
import FTA.CCLIncrementalPhaseCompatibility
import FTA.CCLMetricTrack
import FTA.CCLPersistentController
import FTA.CCLPositiveAllNeither
import FTA.CCLPositiveEventConvergence
import FTA.CCLStrictChildSemantics

/-!
# Incremental event grids at whole-box cylinder checkpoints

Universal wrapping makes every rational point in the retained box a valid
old-prefix representative.  The positive event grid can therefore protect
only the genuinely new incremental child predicate.  This module derives a
cap-independent rational lower bound for its tangent and prior margins,
computes a static localization cap, and packages the resulting grid points
as a persistent coupled-controller successor.
-/

namespace FTA
namespace CCLBoxCylinderIncrementalEventGrid

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBoxCylinderCheckpoint
open FTA.CCLBranchController
open FTA.CCLBranchEvidence
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchPartition
open FTA.CCLBranchPlan
open FTA.CCLBoundaryPreservingOwner
open FTA.CCLClearanceExclusion
open FTA.CCLCanonicalEvent
open FTA.CCLCompletedBlockContraction
open FTA.CCLCompletedMetricContraction
open FTA.CCLCoupledController
open FTA.CCLCoupledTrack
open FTA.CCLDirectTrack
open FTA.CCLEventExtraction
open FTA.CCLEventTangentSigns
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLGuardedEventGrid
open FTA.CCLGuardCellClearance
open FTA.CCLHermitianBox
open FTA.CCLIncrementalCanonicalOwner
open FTA.CCLIncrementalPhaseCompatibility
open FTA.CCLIntersectionEventSigns
open FTA.CCLMultiOwnerGrid
open FTA.CCLMetricTrack
open FTA.CCLOwnerDirection
open FTA.CCLPathIntersection
open FTA.CCLPersistentController
open FTA.CCLPositiveAllNeither
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventApproximation
open FTA.CCLPositiveEventLocalization
open FTA.CCLPositiveEventGrid
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventTrack
open FTA.CCLRawCylinderEnvelope
open FTA.CCLStrictChildSemantics
open FTA.CCLTangentStability
open FTA.CCLTerminalSeparation
open FTA.ConstructiveTrack
open FTA.CentralBandGrid
open FTA.DenseDerivative
open FTA.GaussianPolynomialBounds
open FTA.LocalExtraction
open FTA.RationalPolynomialBounds
open FTA.RootCountDivisibility
open FTA.RootTrackSeparation

abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial CCL.GaussianRat

/-- Forget the checkpoint's universal wrapping field only at the boundary
where an already-certified event step enters the persistent metric pipeline.
The numerical box, raw word, and current cylinder are unchanged. -/
def checkpointMetricState
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLBoxCylinderCheckpoint.State p ambient) :
    CCLMetricTrack.State p ambient where
  core := current.asCoupled.toPersistentState
  cylinder := current.cylinder
  cylinder_word := current.cylinder_word

theorem checkpointMetricState_componentError
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLBoxCylinderCheckpoint.State p ambient) :
    (checkpointMetricState current).componentError = current.componentError :=
  rfl

theorem checkpointMetricState_refines
    {p : GaussianPolynomial} {ambient : RatBox}
    {new old : CCLBoxCylinderCheckpoint.State p ambient}
    (refines : new.Refines old) :
    (checkpointMetricState new).Refines (checkpointMetricState old) :=
  refines

/-- The strict finite plan retained by an all-clear bit supplies exactly the
phase-indexed controller support needed if that bit enters a completed sector.
The preceding plan already included the remaining third-bit wall, so every
target candidate contradicts one of its interval-strict signs. -/
theorem plannedBit_completedSectorControllerCanonicalData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLDirectTrack.State p (RatBox.symmetric R hR)}
    (planned : CCLDirectTrack.PlannedBit current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CompletedSectorControllerCanonicalData planned.numerical
      (current.word ++ [planned.decision.bit]) := by
  intro completed
  exact controllerCanonicalOnInputEvents_of_completed_strictPriorPlan
    planned.numerical current.word planned.decision.bit planned.strictSigns
      completed squarefree degreeNonzero elimination

/-- A direct all-clear plan already proves whole-box wrapping for its appended
bit.  Install that wrapped successor in the metric state while restricting
the inherited cylinder. -/
def metricStepOfCheckpointPlannedBit
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLBoxCylinderCheckpoint.State p ambient)
    (planned : CCLDirectTrack.PlannedBit current.core) :
    CCLMetricTrack.StepResult (checkpointMetricState current) := by
  let core : CCLDirectTrack.State p ambient :=
    { numerical := planned.numerical
      word := current.core.word ++ [planned.decision.bit] }
  let wraps : CCLBoxCylinderCheckpoint.Wraps core.word core.numerical.box := by
    change CCLBoxCylinderCheckpoint.Wraps
      (current.core.word ++ [planned.decision.bit]) planned.numerical.box
    exact current.wraps_append_of_plannedBit planned
  let next := CCLBoxCylinderCheckpoint.State.next current planned.decision.bit
    core (by rfl) wraps
  have nextRefines : next.Refines current :=
    CCLBoxCylinderCheckpoint.State.next_refines current planned.decision.bit
      core planned.refines (by rfl) wraps
  exact .next planned.decision.bit (checkpointMetricState next)
    (checkpointMetricState_refines nextRefines) rfl

def selectedSlopeBoundaryRadiusLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  FTA.Maximality.positiveMinimum
    ((eventPayloadIncrementalActiveOwnerForms selected).map fun form =>
      selectedSlopeDirectionalLower selected / (|form.radial| + 1))

theorem selectedSlopeBoundaryRadiusLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedSlopeBoundaryRadiusLower selected := by
  apply FTA.Maximality.positiveMinimum_pos
  intro radius member
  rw [List.mem_map] at member
  rcases member with ⟨form, _formMember, rfl⟩
  exact div_pos (selectedSlopeDirectionalLower_pos selected) (by positivity)

theorem selectedSlopeBoundaryRadiusLower_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    selectedSlopeBoundaryRadiusLower selected ≤ 1 :=
  FTA.Maximality.positiveMinimum_le_one _

theorem selectedSlopeBoundaryRadiusLower_le_entryRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some direction)
    {t : ℚ} (lower : (selectedSlopeSigns selected).refined.interval.lower ≤ t)
    (upper : t ≤ (selectedSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    selectedSlopeBoundaryRadiusLower selected ≤
      entryRadius form ((selectedPath selected).value t) direction := by
  apply (FTA.Maximality.positiveMinimum_le_of_mem
    (List.mem_map.mpr ⟨form, member, rfl⟩)).trans
  unfold entryRadius
  exact div_le_div_of_nonneg_right
    (selectedSlopeDirectionalLower_le search lower upper member) (by positivity)

theorem selectedSlopeBoundaryRadiusLower_le_cappedEntryRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    selectedSlopeBoundaryRadiusLower selected ≤
      entryRadius form
        (slopeCappedLocalizedEventPoint selected squarefree next cap capPositive)
        (slopeCappedLocalizedClassifiedTangentDirection search squarefree next
          cap capPositive).vector := by
  let capped := cappedClearanceState next cap capPositive
  have bound := selectedSlopeBoundaryRadiusLower_le_entryRadius search
    (slopeLocalizedEventParameter_lower selected squarefree capped)
    (slopeLocalizedEventParameter_upper selected squarefree capped) member
  simpa [slopeCappedLocalizedEventPoint,
    slopeLocalizedEventPoint_eq_pathValue,
    slopeCappedLocalizedClassifiedTangentDirection,
    slopeLocalizedClassifiedTangentDirection, selectedPath, capped] using bound

theorem selectedSlopeBoundaryRadiusLower_le_cappedBoundaryRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    selectedSlopeBoundaryRadiusLower selected ≤
      boundaryRadius (eventPayloadIncrementalActiveOwnerForms selected)
        (slopeCappedLocalizedEventPoint selected squarefree next cap capPositive)
        (slopeCappedLocalizedClassifiedTangentDirection search squarefree next
          cap capPositive).vector := by
  apply FTA.Maximality.le_positiveMinimum
    (selectedSlopeBoundaryRadiusLower_le_one selected)
  intro radius radiusMember
  rw [List.mem_map] at radiusMember
  rcases radiusMember with ⟨form, formMember, rfl⟩
  exact selectedSlopeBoundaryRadiusLower_le_cappedEntryRadius search squarefree
    next cap capPositive formMember

theorem selectedStrictFormMargin_le_slopePathValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {t : ℚ}
    (slopeLower : (selectedSlopeSigns selected).refined.interval.lower ≤ t)
    (slopeUpper : t ≤ (selectedSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalStrictPriorForms selected) :
    selectedStrictFormMargin selected ≤
      |form.eval ((selectedPath selected).value t)| := by
  let path := selectedPath selected
  let signs := selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent
  have lower : signs.refined.interval.lower ≤ t :=
    (selectedSlopeSigns_refines_inputCell selected).1.trans slopeLower
  have upper : t ≤ signs.refined.interval.upper :=
    slopeUpper.trans (selectedSlopeSigns_refines_inputCell selected).2
  have canonicalNonzero : canonicalEventValue
      selected.candidate.inputCell.branch.factor.input
      (clearedForm form path) signs.refined.interval.lower ≠ 0 := by
    simpa only [eventPayloadCanonicalValue, selectedPath, path, signs] using
      strictPriorForms_value_ne
        (inputIncrementalAdvanceFormula state selected.bit)
        (eventPayloadCanonicalValue selected) member
  have clearedLower :=
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent signs
      (selectedStrictPolynomial_mem selected member) canonicalNonzero lower upper
  have denominatorLe := selectedEventDenominator_le selected lower upper
  have denominatorNonzero :=
    selected.candidate.inputCell.path_denominator_ne_on_cell lower upper
  have clearedIdentity : |(clearedForm form path).eval t| =
      |(denominatorNorm path).eval t| * |form.eval (path.value t)| := by
    rw [eval_clearedForm form path t denominatorNonzero, abs_mul]
  unfold selectedStrictFormMargin
  apply (div_le_iff₀ (selectedEventDenominatorUpper_pos selected)).2
  calc
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
        selected.candidate.inputCell.branch.relations
        selected.candidate.inputCell.parent signs ≤
      |(clearedForm form path).eval t| := clearedLower
    _ = |(denominatorNorm path).eval t| * |form.eval (path.value t)| :=
      clearedIdentity
    _ ≤ selectedEventDenominatorUpper selected * |form.eval (path.value t)| :=
      mul_le_mul_of_nonneg_right denominatorLe (abs_nonneg _)
    _ = |form.eval (path.value t)| * selectedEventDenominatorUpper selected :=
      by ring

theorem selectedStrictFormMargin_le_slopeCappedLocalizedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) (cap : ℚ) (capPositive : 0 < cap)
    {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalStrictPriorForms selected) :
    selectedStrictFormMargin selected ≤
      |form.eval (slopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive)| := by
  let capped := cappedClearanceState next cap capPositive
  rw [slopeCappedLocalizedEventPoint, slopeLocalizedEventPoint_eq_pathValue]
  exact selectedStrictFormMargin_le_slopePathValue selected
    (slopeLocalizedEventParameter_lower selected squarefree capped)
    (slopeLocalizedEventParameter_upper selected squarefree capped) member

theorem slopeCappedLocalizedEventPoint_residual_lt_cap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) (cap : ℚ) (capPositive : 0 < cap) :
    normSq (p.eval (slopeCappedLocalizedEventPoint selected squarefree next cap
      capPositive)) < cap / 8 := by
  let capped := cappedClearanceState next cap capPositive
  have residual := localizedCellPoint_residual_lt output
    (selectedSlopeInputCell selected) squarefree capped
  have clearanceLe : capped.clearance.bound / 8 ≤ cap / 8 := by
    gcongr
    simpa only [capped] using
      cappedClearanceState_clearance_le next cap capPositive
  simpa only [slopeCappedLocalizedEventPoint, slopeLocalizedEventPoint,
    capped] using residual.trans_le clearanceLe

theorem slopeCappedLocalizedEventPoint_residual_le_originalClearance
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) (cap : ℚ) (capPositive : 0 < cap) :
    normSq (p.eval (slopeCappedLocalizedEventPoint selected squarefree next cap
      capPositive)) ≤ next.clearance.bound / 16 := by
  let capped := cappedClearanceState next cap capPositive
  let clearance := localizedClearance output capped
  have residual := eventSourcePoint_residual (selectedSlopeInputCell selected)
    squarefree clearance
  have thresholdLe := eventSourceResidualThreshold_le_clearance squarefree
    clearance
  have clearanceLeCapped : clearance.bound ≤ capped.clearance.bound := by
    apply (shrinkBoundaryClearance_bound_le_cap output.state.clearance
      (localizationClearanceCap output capped)
      (localizationClearanceCap_pos output capped)).trans
    exact min_le_left _ _
  have cappedLeOriginal : capped.clearance.bound ≤ next.clearance.bound := by
    change min next.clearance.bound cap ≤ next.clearance.bound
    exact min_le_left _ _
  change normSq (p.eval (eventSourcePoint (selectedSlopeInputCell selected)
    squarefree clearance)) ≤ _
  calc
    normSq (p.eval (eventSourcePoint (selectedSlopeInputCell selected)
        squarefree clearance)) ≤
      eventSourceResidualThreshold squarefree clearance := residual
    _ ≤ clearance.bound / 16 := thresholdLe
    _ ≤ capped.clearance.bound / 16 := by gcongr
    _ ≤ next.clearance.bound / 16 := by gcongr

theorem slopeCappedLocalizedEventPoint_deepInside
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap) :
    let point := slopeCappedLocalizedEventPoint selected squarefree next cap
      capPositive
    let radius := boundaryInteriorRadius p next.box next.clearance
    next.box.xLower + 4 * radius < point.re ∧
      point.re < next.box.xUpper - 4 * radius ∧
      next.box.yLower + 4 * radius < point.im ∧
      point.im < next.box.yUpper - 4 * radius := by
  exact deepInside_of_small_residual next.clearance
    (slopeCappedLocalizedEventPoint_strictContains output selected squarefree
      degreeNonzero elimination next nextRefines cap capPositive)
    (slopeCappedLocalizedEventPoint_residual_le_originalClearance output
      selected squarefree next cap capPositive)

theorem boundaryInteriorRadius_le_slopeCappedBoxForm
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap) {form : HermitianForm}
    (member : form ∈ boxForms next.box) :
    boundaryInteriorRadius p next.box next.clearance ≤
      |form.eval (slopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive)| := by
  let point := slopeCappedLocalizedEventPoint selected squarefree next cap
    capPositive
  let radius := boundaryInteriorRadius p next.box next.clearance
  have radiusPositive : 0 < radius :=
    boundaryInteriorRadius_pos p next.box next.clearance
  have deep := slopeCappedLocalizedEventPoint_deepInside output selected
    squarefree degreeNonzero elimination next nextRefines cap capPositive
  change next.box.xLower + 4 * radius < point.re ∧
    point.re < next.box.xUpper - 4 * radius ∧
    next.box.yLower + 4 * radius < point.im ∧
    point.im < next.box.yUpper - 4 * radius at deep
  rcases deep with ⟨left, right, bottom, top⟩
  simp only [boxForms, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · simp only [eval_boxXLowerForm]
    rw [abs_of_pos (by linarith)]
    linarith
  · simp only [eval_boxXUpperForm]
    rw [abs_of_pos (by linarith)]
    linarith
  · simp only [eval_boxYLowerForm]
    rw [abs_of_pos (by linarith)]
    linarith
  · simp only [eval_boxYUpperForm]
    rw [abs_of_pos (by linarith)]
    linarith

theorem slopeCappedLocalizedEventPoint_normSq_lower
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLe : cap ≤ normSq (p.eval 0)) :
    normSq (p.eval 0) /
        (8 * denseLipschitzBound p (nearbyAmbient next.box)) ≤
      normSq (slopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive) := by
  let point := slopeCappedLocalizedEventPoint selected squarefree next cap
    capPositive
  let L := denseLipschitzBound p (nearbyAmbient next.box)
  let zeroResidual := normSq (p.eval 0)
  have LPositive : 0 < L :=
    denseLipschitzBound_pos p (nearbyAmbient next.box)
  have zeroResidualPositive : 0 < zeroResidual := capPositive.trans_le capLe
  have strict := slopeCappedLocalizedEventPoint_strictContains output selected
    squarefree degreeNonzero elimination next nextRefines cap capPositive
  have pointNearby : (nearbyAmbient next.box).Contains point :=
    nearbyAmbient_contains strict.contains
  have zeroNearby : (nearbyAmbient next.box).Contains (0 : CCL.GaussianRat) := by
    dsimp only [nearbyAmbient, RatBox.symmetric, RatBox.Contains, zero_re,
      zero_im]
    have radiusNonnegative := next.box.coordinateRadius_nonneg
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have residualCap := slopeCappedLocalizedEventPoint_residual_lt_cap selected
    squarefree next cap capPositive
  have residual : normSq (p.eval point) < zeroResidual / 8 := by
    apply residualCap.trans_le
    exact div_le_div_of_nonneg_right capLe (by norm_num)
  change zeroResidual / (8 * L) ≤ normSq point
  by_contra notLower
  have pointSmall : normSq point < zeroResidual / (8 * L) :=
    lt_of_not_ge notLower
  have lipschitz := normSq_dense_eval_sub_eval_le_denseLipschitzBound p
    pointNearby zeroNearby
  have evaluationDifference :
      normSq (p.eval point + -(p.eval 0)) < zeroResidual / 8 := by
    calc
      normSq (p.eval point + -(p.eval 0)) ≤
          L * normSq (point + -(0 : CCL.GaussianRat)) := lipschitz
      _ = L * normSq point := by simp
      _ < L * (zeroResidual / (8 * L)) :=
        mul_lt_mul_of_pos_left pointSmall LPositive
      _ = zeroResidual / 8 := by field_simp
  have decomposition :
      -(p.eval point + -(p.eval 0)) + p.eval point = p.eval 0 := by
    ext <;> simp only [add_re, add_im, neg_re, neg_im] <;> ring
  have sumBound := normSq_add_le_two
    (-(p.eval point + -(p.eval 0))) (p.eval point)
  rw [decomposition, normSq_neg] at sumBound
  nlinarith

def checkpointEventPriorForms
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (box : RatBox) :
    List HermitianForm :=
  eventPayloadIncrementalStrictPriorForms selected ++ boxForms box ++
    [affineNormForm 1 0]

def slopeZeroNormLower (p : GaussianPolynomial) (box : RatBox) : ℚ :=
  normSq (p.eval 0) / (8 * denseLipschitzBound p (nearbyAmbient box))

theorem slopeZeroNormLower_pos
    (p : GaussianPolynomial) (box : RatBox) (zeroNonzero : p.eval 0 ≠ 0) :
    0 < slopeZeroNormLower p box := by
  exact div_pos (normSq_pos zeroNonzero)
    (mul_pos (by norm_num)
      (denseLipschitzBound_pos p (nearbyAmbient box)))

def checkpointPriorEvaluationLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient) : ℚ :=
  min (selectedStrictFormMargin selected)
    (min (boundaryInteriorRadius p next.box next.clearance)
      (slopeZeroNormLower p next.box))

theorem checkpointPriorEvaluationLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient) (zeroNonzero : p.eval 0 ≠ 0) :
    0 < checkpointPriorEvaluationLower selected next := by
  exact lt_min (selectedStrictFormMargin_pos selected)
    (lt_min (boundaryInteriorRadius_pos p next.box next.clearance)
      (slopeZeroNormLower_pos p next.box zeroNonzero))

theorem checkpointPriorEvaluationLower_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLeZeroResidual : cap ≤ normSq (p.eval 0)) :
    ∀ form ∈ checkpointEventPriorForms selected next.box,
      checkpointPriorEvaluationLower selected next ≤
        |form.eval (slopeCappedLocalizedEventPoint selected squarefree next cap
          capPositive)| := by
  intro form member
  simp only [checkpointEventPriorForms, List.mem_append,
    List.mem_singleton] at member
  rcases member with (selectedStrict | boxForm) | normForm
  · apply (min_le_left _ _).trans
    exact selectedStrictFormMargin_le_slopeCappedLocalizedEventPoint selected
      squarefree next cap capPositive selectedStrict
  · apply ((min_le_right _ _).trans (min_le_left _ _)).trans
    exact boundaryInteriorRadius_le_slopeCappedBoxForm output selected
      squarefree degreeNonzero elimination next nextRefines cap capPositive
      boxForm
  · subst form
    apply ((min_le_right _ _).trans (min_le_right _ _)).trans
    have lower := slopeCappedLocalizedEventPoint_normSq_lower output selected
      squarefree degreeNonzero elimination next nextRefines cap capPositive
        capLeZeroResidual
    simpa [slopeZeroNormLower, eval_affineNormForm,
      abs_of_nonneg (normSq_nonneg
        (slopeCappedLocalizedEventPoint selected squarefree next cap
          capPositive))] using lower

def checkpointUniformOwnerRadiusLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient) : ℚ :=
  min 1 (min (selectedSlopeBoundaryRadiusLower selected)
    (priorRadiusLower (checkpointEventPriorForms selected next.box) next.box
      (checkpointPriorEvaluationLower selected next)))

theorem checkpointUniformOwnerRadiusLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient) (zeroNonzero : p.eval 0 ≠ 0) :
    0 < checkpointUniformOwnerRadiusLower selected next := by
  exact lt_min zero_lt_one
    (lt_min (selectedSlopeBoundaryRadiusLower_pos selected)
      (priorRadiusLower_pos _ _
        (checkpointPriorEvaluationLower_pos selected next zeroNonzero)))

theorem checkpointUniformOwnerRadiusLower_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient) :
    checkpointUniformOwnerRadiusLower selected next ≤ 1 :=
  min_le_left _ _

theorem checkpointUniformOwnerRadiusLower_le_multiOwnerRadius
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLeZeroResidual : cap ≤ normSq (p.eval 0))
    {searchDirection : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some searchDirection) :
    checkpointUniformOwnerRadiusLower selected next ≤
      multiOwnerRadius
        (slopeCappedLocalizedClassifiedTangentDirection search squarefree next
          cap capPositive)
        (checkpointEventPriorForms selected next.box) := by
  let point := slopeCappedLocalizedEventPoint selected squarefree next cap
    capPositive
  let direction := slopeCappedLocalizedClassifiedTangentDirection search
    squarefree next cap capPositive
  have strict := slopeCappedLocalizedEventPoint_strictContains output selected
    squarefree degreeNonzero elimination next nextRefines cap capPositive
  have priorLower := priorRadiusLower_le_strictRadius
    (priors := checkpointEventPriorForms selected next.box)
    (box := next.box)
    (evaluationLower := checkpointPriorEvaluationLower selected next)
    strict.contains direction.normSq_le_one
    (checkpointPriorEvaluationLower_le output selected squarefree degreeNonzero
      elimination next nextRefines cap capPositive capLeZeroResidual)
  unfold checkpointUniformOwnerRadiusLower multiOwnerRadius
  apply le_min (min_le_left _ _)
  apply le_min
  · apply ((min_le_right _ _).trans (min_le_left _ _)).trans
    exact selectedSlopeBoundaryRadiusLower_le_cappedBoundaryRadius search
      squarefree next cap capPositive
  · apply ((min_le_right _ _).trans (min_le_right _ _)).trans
    simpa only [point, direction] using priorLower

def checkpointUniformBoundaryBudgetLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient) : ℚ :=
  checkpointUniformOwnerRadiusLower selected next / 3 *
    selectedSlopeBoundaryRadiusLower selected

theorem checkpointUniformBoundaryBudgetLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient) (zeroNonzero : p.eval 0 ≠ 0) :
    0 < checkpointUniformBoundaryBudgetLower selected next := by
  exact mul_pos
    (div_pos (checkpointUniformOwnerRadiusLower_pos selected next zeroNonzero)
      (by norm_num))
    (selectedSlopeBoundaryRadiusLower_pos selected)

theorem checkpointUniformBoundaryBudgetLower_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLeZeroResidual : cap ≤ normSq (p.eval 0))
    {searchDirection : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some searchDirection) :
    checkpointUniformBoundaryBudgetLower selected next ≤
      approximateBoundaryBudget
        (slopeCappedLocalizedClassifiedTangentDirection search squarefree next
          cap capPositive)
        (checkpointEventPriorForms selected next.box) := by
  let point := slopeCappedLocalizedEventPoint selected squarefree next cap
    capPositive
  let direction := slopeCappedLocalizedClassifiedTangentDirection search
    squarefree next cap capPositive
  let priors := checkpointEventPriorForms selected next.box
  have priorNonzero : ∀ form ∈ priors, form.eval point ≠ 0 := by
    intro form member zero
    have lower := checkpointPriorEvaluationLower_le output selected squarefree
      degreeNonzero elimination next nextRefines cap capPositive
        capLeZeroResidual form member
    have positive := checkpointPriorEvaluationLower_pos selected next
      zeroNonzero
    rw [zero, abs_zero] at lower
    linarith
  have radiusPositive := checkpointUniformOwnerRadiusLower_pos selected next
    zeroNonzero
  have radiusLe := checkpointUniformOwnerRadiusLower_le_multiOwnerRadius output
    selected squarefree degreeNonzero elimination next nextRefines cap
      capPositive capLeZeroResidual search
  have epsilonLowerLe : checkpointUniformOwnerRadiusLower selected next / 3 ≤
      multiOwnerEpsilon direction priors :=
    (radiusLower_div_three_lt_multiOwnerEpsilon direction priors
      radiusPositive radiusLe priorNonzero).le
  have epsilonLowerAtMostOne :
      checkpointUniformOwnerRadiusLower selected next / 3 ≤ 1 := by
    have radiusLeOne := checkpointUniformOwnerRadiusLower_le_one selected next
    nlinarith [radiusPositive]
  unfold checkpointUniformBoundaryBudgetLower
  exact mul_le_approximateBoundaryBudget_of_lower_bounds direction priors
    priorNonzero epsilonLowerLe epsilonLowerAtMostOne
    (selectedSlopeBoundaryRadiusLower_pos selected).le
    (selectedSlopeBoundaryRadiusLower_le_one selected)
    (fun form member =>
      selectedSlopeBoundaryRadiusLower_le_cappedEntryRadius search squarefree
        next cap capPositive member)

def selectedSlopeActiveCoefficientSum
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  1 + ((eventPayloadIncrementalActiveOwnerForms selected).map fun form =>
    selectedSlopeActiveEventCoefficient selected form).sum

theorem selectedSlopeActiveCoefficientSum_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedSlopeActiveCoefficientSum selected := by
  have sumNonnegative : 0 ≤
      ((eventPayloadIncrementalActiveOwnerForms selected).map fun form =>
        selectedSlopeActiveEventCoefficient selected form).sum := by
    apply List.sum_nonneg
    intro coefficient coefficientMember
    rw [List.mem_map] at coefficientMember
    rcases coefficientMember with ⟨form, _formMember, rfl⟩
    exact selectedSlopeActiveEventCoefficient_nonneg selected form
  unfold selectedSlopeActiveCoefficientSum
  linarith

theorem selectedSlopeActiveCoefficient_lt_sum
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    selectedSlopeActiveEventCoefficient selected form <
      selectedSlopeActiveCoefficientSum selected := by
  have coefficientLeSum : selectedSlopeActiveEventCoefficient selected form ≤
      ((eventPayloadIncrementalActiveOwnerForms selected).map fun item =>
        selectedSlopeActiveEventCoefficient selected item).sum := by
    apply List.single_le_sum
    · intro coefficient coefficientMember
      rw [List.mem_map] at coefficientMember
      rcases coefficientMember with ⟨item, _itemMember, rfl⟩
      exact selectedSlopeActiveEventCoefficient_nonneg selected item
    · exact List.mem_map.mpr ⟨form, member, rfl⟩
  unfold selectedSlopeActiveCoefficientSum
  linarith

def checkpointStaticGridCap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient) : ℚ :=
  min (normSq (p.eval 0) / 2)
    (checkpointUniformBoundaryBudgetLower selected next /
      (2 * selectedSlopeActiveCoefficientSum selected))

theorem checkpointStaticGridCap_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient) (zeroNonzero : p.eval 0 ≠ 0) :
    0 < checkpointStaticGridCap selected next := by
  apply lt_min
  · exact div_pos (normSq_pos zeroNonzero) (by norm_num)
  · exact div_pos
      (checkpointUniformBoundaryBudgetLower_pos selected next zeroNonzero)
      (mul_pos (by norm_num) (selectedSlopeActiveCoefficientSum_pos selected))

theorem checkpointStaticGridCap_le_zeroResidual
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient) :
    checkpointStaticGridCap selected next ≤ normSq (p.eval 0) := by
  apply (min_le_left _ _).trans
  exact div_le_self (normSq_nonneg (p.eval 0)) (by norm_num)

theorem checkpointStaticGridCap_residualBudget
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    {searchDirection : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some searchDirection) :
    selectedSlopeActiveCoefficientSum selected *
        checkpointStaticGridCap selected next <
      approximateBoundaryBudget
        (slopeCappedLocalizedClassifiedTangentDirection search squarefree next
          (checkpointStaticGridCap selected next)
          (checkpointStaticGridCap_pos selected next zeroNonzero))
        (checkpointEventPriorForms selected next.box) := by
  let lower := checkpointUniformBoundaryBudgetLower selected next
  let coefficient := selectedSlopeActiveCoefficientSum selected
  let cap := checkpointStaticGridCap selected next
  have lowerPositive : 0 < lower :=
    checkpointUniformBoundaryBudgetLower_pos selected next zeroNonzero
  have coefficientPositive : 0 < coefficient :=
    selectedSlopeActiveCoefficientSum_pos selected
  have capLeRatio : cap ≤ lower / (2 * coefficient) := min_le_right _ _
  have productLe : coefficient * cap ≤
      coefficient * (lower / (2 * coefficient)) :=
    mul_le_mul_of_nonneg_left capLeRatio coefficientPositive.le
  have identity : coefficient * (lower / (2 * coefficient)) = lower / 2 := by
    field_simp
  have lowerLeBudget := checkpointUniformBoundaryBudgetLower_le output selected
    squarefree degreeNonzero zeroNonzero elimination next nextRefines cap
    (checkpointStaticGridCap_pos selected next zeroNonzero)
    (checkpointStaticGridCap_le_zeroResidual selected next) search
  change coefficient * cap < _
  calc
    coefficient * cap ≤ coefficient * (lower / (2 * coefficient)) := productLe
    _ = lower / 2 := identity
    _ < lower := by linarith
    _ ≤ _ := lowerLeBudget

def cappedCheckpointEventGridData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLeZeroResidual : cap ≤ normSq (p.eval 0))
    {searchDirection : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some searchDirection)
    (residualBudget : selectedSlopeActiveCoefficientSum selected * cap <
      approximateBoundaryBudget
        (slopeCappedLocalizedClassifiedTangentDirection search squarefree next
          cap capPositive)
        (checkpointEventPriorForms selected next.box)) :
    EventGridData current.asCoupled separation selected next nextRefines where
  base := slopeCappedLocalizedEventPoint selected squarefree next cap capPositive
  baseStrict := slopeCappedLocalizedEventPoint_strictContains separation
    selected squarefree degreeNonzero elimination next nextRefines cap
      capPositive
  baseNonzero := slopeCappedLocalizedEventPoint_ne_zero selected squarefree next
    cap capPositive capLeZeroResidual
  baseRepresented := current.wraps
    (separation.refines.contains (nextRefines.contains
      (slopeCappedLocalizedEventPoint_strictContains separation selected
        squarefree degreeNonzero elimination next nextRefines cap
          capPositive).contains))
  basePriors := []
  basePriorsNonzero := by simp
  baseStable := by
    intro point inside _preserved
    exact current.wraps inside
  direction := slopeCappedLocalizedClassifiedTangentDirection search squarefree
    next cap capPositive
  selectedStrictAtBase := slopeCappedLocalizedEventStrict selected squarefree
    next cap capPositive
  selectedActiveResidual := by
    intro form member
    have coefficientBound := mul_lt_mul_of_pos_right
      (selectedSlopeActiveCoefficient_lt_sum selected member) capPositive
    exact (slopeCappedLocalizedEventActive_le selected squarefree next cap
      capPositive member).trans_lt (coefficientBound.trans residualBudget)

def checkpointStaticEventGridData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {searchDirection : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some searchDirection) :
    EventGridData current.asCoupled separation selected next nextRefines := by
  let cap := checkpointStaticGridCap selected next
  let capPositive : 0 < cap :=
    checkpointStaticGridCap_pos selected next zeroNonzero
  apply cappedCheckpointEventGridData current separation selected squarefree
    degreeNonzero elimination next nextRefines cap capPositive
      (checkpointStaticGridCap_le_zeroResidual selected next) search
  have residual := checkpointStaticGridCap_residualBudget separation selected
    squarefree degreeNonzero zeroNonzero elimination next nextRefines search
  have positiveEquality :
      checkpointStaticGridCap_pos selected next zeroNonzero = capPositive :=
    Subsingleton.elim _ _
  rw [positiveEquality] at residual
  simpa only [cap] using residual

theorem checkpointStaticEventGridData_basePriors
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {searchDirection : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some searchDirection) :
    (checkpointStaticEventGridData current separation selected squarefree
      degreeNonzero zeroNonzero elimination next nextRefines
        search).basePriors = [] := by
  simp only [checkpointStaticEventGridData, cappedCheckpointEventGridData]

def checkpointStaticPersistentEventGridDataFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {searchDirection : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some searchDirection) :
    PersistentEventGridDataFamily current.asCoupled separation selected where
  data next nextRefines :=
    checkpointStaticEventGridData current separation selected squarefree
      degreeNonzero zeroNonzero elimination next nextRefines search
  basePriors := by
    intro next nextRefines
    change (checkpointStaticEventGridData current separation selected squarefree
      degreeNonzero zeroNonzero elimination next nextRefines
        search).basePriors = []
    exact checkpointStaticEventGridData_basePriors current separation selected
      squarefree degreeNonzero zeroNonzero elimination next nextRefines search
  baseSameSigns := by
    simp [State.asCoupled]

def checkpointStaticPersistentEventOwnerSamples
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {searchDirection : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some searchDirection) :
    PersistentEventOwnerSamples current.asCoupled separation selected :=
  (checkpointStaticPersistentEventGridDataFamily current separation selected
    squarefree degreeNonzero zeroNonzero elimination search).ownerSamples

/-- Close an already complete event-owner payload through the history-free
checkpoint grid.  Unlike conversion from the incremental truth table, this
route needs no canonical-current premise: the complete classifier has already
certified the selected child formula itself. -/
def nextOfCheckpointCompleteGridOwner
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CCLCoupledTrack.StepResult current.asCoupled := by
  match selected.decision with
  | .identicallyZero realZero imagZero =>
      let exactRoot :=
        FTA.CCLEventTerminal.InputEventCell.identicallyZeroRoot
          selected.candidate.inputCell realZero imagZero
      if zero : exactRoot.point = 0 then
        exact .zero (by simpa only [zero] using exactRoot.root)
      else
        exact .terminal exactRoot.point exactRoot.root zero
          (RationalEncoder.encode exactRoot.point zero) rfl
  | .positive _evidence =>
      let direct := selected.toIncrementalPayload
      exact nextOfPersistentEventPayload current.asCoupled separation direct
        (checkpointStaticPersistentEventOwnerSamples current separation direct
          squarefree degreeNonzero zeroNonzero elimination
            (parsedClassifiedTangentDirection_spec selected))

/-- Every nonterminal complete-owner result carries the phase-indexed
algebraic support proved by the selected complete payload. -/
theorem nextOfCheckpointCompleteGridOwner_canonical
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (evidence : PositiveCurveEventEvidence p
      selected.candidate.sourceEvent.partition.entry.chart.path
      separation.state.box selected.candidate.sourceEvent.event)
    (decisionEq : selected.decision = .positive evidence)
    {bit : Bool}
    {next : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {refines : next.numerical.box.Refines current.asCoupled.numerical.box}
    {wordEq : next.word = current.asCoupled.word ++ [bit]}
    (resultEq : nextOfCheckpointCompleteGridOwner current separation selected
      squarefree degreeNonzero zeroNonzero elimination =
        .next bit next refines wordEq) :
    CompletedSectorCanonicalData next.numerical next.word := by
  unfold nextOfCheckpointCompleteGridOwner at resultEq
  rw [decisionEq] at resultEq
  unfold nextOfPersistentEventPayload nextOfStableRepresentedOutcome at resultEq
  cases resultEq
  exact CompletedSectorCanonicalData.ofSelectedPayload
    current.core.numerical current.core.word separation selected squarefree
      degreeNonzero elimination

def nextOfCheckpointIncrementalGridOwner
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CCLCoupledTrack.StepResult current.asCoupled := by
  match selected.decision with
  | .identicallyZero realZero imagZero =>
      let exactRoot :=
        FTA.CCLEventTerminal.InputEventCell.identicallyZeroRoot
          selected.candidate.inputCell realZero imagZero
      if zero : exactRoot.point = 0 then
        exact .zero (by simpa only [zero] using exactRoot.root)
      else
        exact .terminal exactRoot.point exactRoot.root zero
          (RationalEncoder.encode exactRoot.point zero) rfl
  | .positive _evidence =>
      exact nextOfPersistentEventPayload current.asCoupled separation selected
        (checkpointStaticPersistentEventOwnerSamples current separation selected
          squarefree degreeNonzero zeroNonzero elimination
            (parsedIncrementalClassifiedTangentDirection_spec selected
              notCompleted))

/-- Feed the now-total checkpoint event-owner result into the existing metric
state transition.  Exact-root outcomes are retained, while a positive owner
restricts the inherited cylinder along the appended raw bit. -/
def metricStepOfCheckpointIncrementalGridOwner
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CCLMetricTrack.StepResult (checkpointMetricState current) :=
  CCLMetricTrack.liftStepResult (checkpointMetricState current)
    (nextOfCheckpointIncrementalGridOwner current separation selected
      notCompleted squarefree degreeNonzero zeroNonzero elimination).toPersistent

/-- Metric lift of the no-validity complete-owner route. -/
def metricStepOfCheckpointCompleteGridOwner
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CCLMetricTrack.StepResult (checkpointMetricState current) :=
  CCLMetricTrack.liftStepResult (checkpointMetricState current)
    (nextOfCheckpointCompleteGridOwner current separation selected squarefree
      degreeNonzero zeroNonzero elimination).toPersistent

/-- Compatibility entry point for callers that still carry current-event
canonical support.  Non-completed phases use the history-free successor;
only a completed sector reconstructs the legacy complete payload. -/
def metricStepOfCheckpointIncrementalGridOwnerWithCanonical
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (currentCanonical : currentFormulaCanonicalCheck
      selected.candidate.inputCell = true)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CCLMetricTrack.StepResult (checkpointMetricState current) := by
  match phaseEq : (RawParser.parse current.core.word).phase with
  | .initial =>
      exact metricStepOfCheckpointIncrementalGridOwner current separation
        selected (by simp [phaseEq]) squarefree degreeNonzero zeroNonzero
          elimination
  | .highUnary count =>
      exact metricStepOfCheckpointIncrementalGridOwner current separation
        selected (by simp [phaseEq]) squarefree degreeNonzero zeroNonzero
          elimination
  | .lowUnary count =>
      exact metricStepOfCheckpointIncrementalGridOwner current separation
        selected (by simp [phaseEq]) squarefree degreeNonzero zeroNonzero
          elimination
  | .loopUnary count =>
      exact metricStepOfCheckpointIncrementalGridOwner current separation
        selected (by simp [phaseEq]) squarefree degreeNonzero zeroNonzero
          elimination
  | .sector kind exponent .zero =>
      exact metricStepOfCheckpointIncrementalGridOwner current separation
        selected (by simp [phaseEq]) squarefree degreeNonzero zeroNonzero
          elimination
  | .sector kind exponent (.one first) =>
      exact metricStepOfCheckpointIncrementalGridOwner current separation
        selected (by simp [phaseEq]) squarefree degreeNonzero zeroNonzero
          elimination
  | .sector kind exponent (.two first second) =>
      let complete := toCompletePayload selected squarefree degreeNonzero
        elimination currentCanonical
      exact metricStepOfCheckpointCompleteGridOwner current separation complete
        squarefree degreeNonzero zeroNonzero elimination

/-- Phase-indexed controller support carried by the nonterminal branch of a
metric step.  Exact-root outcomes have no successor obligation. -/
def MetricStepControllerCanonical
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLMetricTrack.State p ambient} :
    CCLMetricTrack.StepResult current → Prop
  | .zero _ | .terminal .. => True
  | .next _ state _ _ =>
      CompletedSectorControllerCanonicalData state.core.numerical
        state.core.word

/-- An incremental-owner successor needs no algebraic support payload unless
its appended word has just reached the completed-sector phase.  This closes
all other parser positions directly, without strengthening a history-free
owner into a complete historical owner. -/
theorem metricStepOfCheckpointIncrementalGridOwner_canonical_of_append_not_completed
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (appendNotCompleted : ¬∃ kind exponent first second,
      (RawParser.parse (current.core.word ++ [selected.bit])).phase =
        .sector kind exponent (.two first second)) :
    MetricStepControllerCanonical
      (metricStepOfCheckpointIncrementalGridOwner current separation selected
        notCompleted squarefree degreeNonzero zeroNonzero elimination) := by
  let result := nextOfCheckpointIncrementalGridOwner current separation selected
    notCompleted squarefree degreeNonzero zeroNonzero elimination
  generalize resultEq :
    nextOfCheckpointIncrementalGridOwner current separation selected
      notCompleted squarefree degreeNonzero zeroNonzero elimination = result
  unfold metricStepOfCheckpointIncrementalGridOwner
  rw [resultEq]
  cases result with
  | zero root => trivial
  | terminal point root nonzero completeWord complete => trivial
  | next bit next refines wordEq =>
      change CompletedSectorControllerCanonicalData next.numerical next.word
      cases decisionEq : selected.decision with
      | identicallyZero realZero imagZero =>
          simp [nextOfCheckpointIncrementalGridOwner, decisionEq] at resultEq
          split at resultEq <;> contradiction
      | positive evidence =>
          unfold nextOfCheckpointIncrementalGridOwner at resultEq
          rw [decisionEq] at resultEq
          unfold nextOfPersistentEventPayload nextOfStableRepresentedOutcome
            at resultEq
          cases resultEq
          intro completed
          exact (appendNotCompleted completed).elim

/-- The complete event-owner route already proves this support before its
coupled successor is lifted into the metric cylinder. -/
theorem metricStepOfCheckpointCompleteGridOwner_canonical
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    MetricStepControllerCanonical
      (metricStepOfCheckpointCompleteGridOwner current separation selected
        squarefree degreeNonzero zeroNonzero elimination) := by
  let result := nextOfCheckpointCompleteGridOwner current separation selected
    squarefree degreeNonzero zeroNonzero elimination
  generalize resultEq :
    nextOfCheckpointCompleteGridOwner current separation selected squarefree
      degreeNonzero zeroNonzero elimination = result
  unfold metricStepOfCheckpointCompleteGridOwner
  rw [resultEq]
  cases result with
  | zero root => trivial
  | terminal point root nonzero completeWord complete => trivial
  | next bit next refines wordEq =>
      change CompletedSectorControllerCanonicalData next.numerical next.word
      cases decisionEq : selected.decision with
      | identicallyZero realZero imagZero =>
          simp [nextOfCheckpointCompleteGridOwner, decisionEq] at resultEq
          split at resultEq <;> contradiction
      | positive evidence =>
          exact (nextOfCheckpointCompleteGridOwner_canonical current separation
            selected squarefree degreeNonzero zeroNonzero elimination evidence
              decisionEq resultEq).controllerCanonical

/-- Complete-form checkpoint event traversal.  This is the constructive
fallback immediately after a matrix-updating completed block, when only the
phase-indexed support invariant is available and conversion of an incremental
owner would ask for unnecessarily strong full current support. -/
inductive CheckpointCompleteEventOpening
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR)) where
  | ready (result : CCLMetricTrack.StepResult
      (checkpointMetricState current))
      (canonical : MetricStepControllerCanonical result)
  | allNeither
      (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
        current.core.numerical
        (adjugate (RawParser.parse current.core.word).matrix))
      (globalNone : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.core.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.core.word) separation,
        candidate.inputCell.ownerChecks = (false, false))

/-- Execute denominator separation and the complete two-child owner tables
without assuming canonical truth of the old parser predicate. -/
def openCheckpointCompleteEvents
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CheckpointCompleteEventOpening p R hR current :=
  match CCLDenominator.decide track current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix)
      (CCLBranchEvidence.adjugate_lowerRow_ne
        (RawParser.parse current.core.word).matrix (by
          simpa only [determinant, Mat2.det] using
            RawParser.parse_det_ne current.core.word)) with
  | .terminal point root _contains _strict _denominatorZero => by
      if zero : point = 0 then
        exact .ready (.zero (by simpa only [zero] using root)) (by trivial)
      else
        exact .ready (.terminal point root zero
          (RationalEncoder.encode point zero) rfl) (by trivial)
  | .separated separation =>
      match decideCombinedEventOwners
          (RawParser.parse current.core.word) separation with
      | .globalOwner selected =>
          .ready (metricStepOfCheckpointCompleteGridOwner current separation
            selected.toPayload squarefree degreeNonzero zeroNonzero
              elimination)
            (metricStepOfCheckpointCompleteGridOwner_canonical current
              separation selected.toPayload squarefree degreeNonzero
                zeroNonzero elimination)
      | .guardOwner selected =>
          .ready (metricStepOfCheckpointCompleteGridOwner current separation
            selected.toPayload squarefree degreeNonzero zeroNonzero
              elimination)
            (metricStepOfCheckpointCompleteGridOwner_canonical current
              separation selected.toPayload squarefree degreeNonzero
                zeroNonzero elimination)
      | .allNeither globalNone guardNone =>
          .allNeither separation globalNone guardNone

/-- Exact retained provenance of the sole positive terminal-guard branch in
the no-validity checkpoint traversal.  Factoring this record out of the
opening lets the next finite controller inspect its history-free owner table
without duplicating the clearance and terminal-separation certificates. -/
structure CheckpointPositiveGuardData
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)) where
  separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
        current.core.numerical
        (adjugate (RawParser.parse current.core.word).matrix)
  globalNone : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.core.word) separation,
        candidate.inputCell.ownerChecks = (false, false)
  guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.core.word) separation,
        candidate.inputCell.ownerChecks = (false, false)
  noIdenticallyZero : CCLCoupledController.firstIdenticallyZeroRoot?
    (RawParser.parse current.core.word) separation = Option.none
  arcs : List (BoundaryArc p)
  evidence : AllClear p arcs
  alignment : ClearFamilyAlignment p separation.state.box
    (separatedRelevantClearCells p (RawParser.parse current.core.word)
      separation) arcs
  terminal : CCLTerminalSeparation.SeparationOutput p
    (RatBox.symmetric R hR) (RawParser.parse current.core.word)
      separation.state [false, true]
  output : RefinementOutput p (RatBox.symmetric R hR)
    terminal.numerical evidence
  sourceCell : SourceEventGuardCell p separation.state.box
  member : sourceCell ∈ separatedEventGuardCells p
    (RawParser.parse current.core.word) separation
  clearedNonzero :
    (FTA.ProjectivePath.clearedReal p
      sourceCell.partition.entry.chart.path).isZero = false ∨
    (FTA.ProjectivePath.clearedImag p
      sourceCell.partition.entry.chart.path).isZero = false
  countPositive : 0 < FTA.ProjectivePath.commonFactorRootCount2 p
    sourceCell.partition.entry.chart.path clearedNonzero
    sourceCell.item.cell.cell.interval.lower
    sourceCell.item.cell.cell.interval.upper
  event : RelevantCurveEvent p
    sourceCell.partition.entry.chart.path separation.state.box
  eventMember : event ∈
    CCLBranchEvent.EventGuardCell.relevantCurveEvents sourceCell.item.cell

theorem CheckpointPositiveGuardData.source_partition_mem_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    data.sourceCell.partition ∈ separatedChartPartitions p
      (RawParser.parse current.core.word) data.separation := by
  apply sourceEventGuardCell_partition_mem_of_mem
  simpa only [separatedEventGuardCells] using data.member

theorem CheckpointPositiveGuardData.source_entry_mem_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    data.sourceCell.partition.entry ∈
      separatedCharts (RawParser.parse current.core.word) data.separation := by
  apply SourceChartPartition.entry_mem_of_mem_build
  simpa only [separatedChartPartitions] using
    data.source_partition_mem_separated

theorem CheckpointPositiveGuardData.source_mem_inputPlan
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    data.sourceCell.partition.entry.source ∈
      inputPlan (RawParser.parse current.core.word) :=
  separatedChart_source_mem_inputPlan data.source_entry_mem_separated

theorem CheckpointPositiveGuardData.source_determinant_ne
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (stateDeterminant :
      determinant (RawParser.parse current.core.word).matrix ≠ 0) :
    determinant data.sourceCell.partition.entry.source.matrix ≠ 0 :=
  separatedChart_determinant_ne stateDeterminant
    data.source_entry_mem_separated

/-- Repackage the retained positive guard as the exact source-labelled event
whose parser-cell refinement will support the boundary continuation. -/
def CheckpointPositiveGuardData.sourceEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    SourceGuardCurveEvent p data.separation.state.box :=
  ⟨data.sourceCell, data.event, data.eventMember⟩

/-- Constructively select one executable parser-cell refinement of the
positive guard.  The finite refinement family is intrinsically nonempty, so
its head is available without choice or an owner decision. -/
def CheckpointPositiveGuardData.boundaryCandidate
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    SourceGuardInputEventCell p data.separation.state.box
      (RawParser.parse current.core.word) :=
  (sourceGuardInputEventCells (RawParser.parse current.core.word)
    data.sourceEvent).head
  (sourceGuardInputEventCells_ne_nil
        (RawParser.parse current.core.word) data.sourceEvent)

theorem CheckpointPositiveGuardData.boundaryCandidate_sourceEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    data.boundaryCandidate.sourceEvent = data.sourceEvent := by
  have member : data.boundaryCandidate ∈ sourceGuardInputEventCells
      (RawParser.parse current.core.word) data.sourceEvent := by
    exact List.head_mem (sourceGuardInputEventCells_ne_nil
      (RawParser.parse current.core.word) data.sourceEvent)
  rw [sourceGuardInputEventCells, List.mem_map] at member
  rcases member with ⟨cell, _cellMember, equality⟩
  exact (congrArg (fun candidate => candidate.sourceEvent) equality).symm

/-- Add the squarefree event derivative as one coprime sign condition.  This
orients every later lower-endpoint approximation without selecting the
algebraic event parameter. -/
def CheckpointPositiveGuardData.boundaryDerivativeCondition
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    CoprimeCondition
      data.boundaryCandidate.inputCell.branch.factor.polynomial where
  polynomial := derivative
    data.boundaryCandidate.inputCell.branch.factor.polynomial
  coprime := data.boundaryCandidate.inputCell.branch.factor.input.squarefree

/-- One finite common refinement fixes the event derivative's strict sign. -/
def CheckpointPositiveGuardData.boundaryDerivativeSigns
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    CommonEventSigns
      data.boundaryCandidate.inputCell.branch.factor.input
      [data.boundaryDerivativeCondition]
      data.boundaryCandidate.inputCell.parent :=
  computeCommonEventSigns
    data.boundaryCandidate.inputCell.branch.factor.input
    [data.boundaryDerivativeCondition]
    data.boundaryCandidate.inputCell.parent

/-- Rebase the parser-classified cell on the derivative-oriented parent.  All
condition relations and divisibility evidence are unchanged. -/
def CheckpointPositiveGuardData.boundaryOrientedInputCell
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    InputEventCell (RawParser.parse current.core.word)
      data.boundaryCandidate.sourceEvent.event where
  branch := data.boundaryCandidate.inputCell.branch
  divides := data.boundaryCandidate.inputCell.divides
  parent := data.boundaryDerivativeSigns.refined
  refines := FTA.SturmTransducer.RationalInterval.refines_trans
    data.boundaryDerivativeSigns.refines
      data.boundaryCandidate.inputCell.refines

/-- Derivative sign certificate inherited by every approximation below the
oriented parser cell. -/
def CheckpointPositiveGuardData.boundaryDerivativeSign
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    IntervalSignCertificate
      (derivative data.boundaryOrientedInputCell.branch.factor.polynomial)
      data.boundaryOrientedInputCell.parent.interval.lower
      data.boundaryOrientedInputCell.parent.interval.upper := by
  exact data.boundaryDerivativeSigns.signs data.boundaryDerivativeCondition
    (by simp)

/-- The fixed rational source-path interval attached to the selected boundary
cell.  It is deliberately independent of all later numerical refinements. -/
def CheckpointPositiveGuardData.boundaryPathCylinder
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
  RationalPathCylinder where
  path := data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path
  interval := (data.boundaryOrientedInputCell.branch.computeEventSigns
    data.boundaryOrientedInputCell.parent).refined.interval
  denominator_ne := by
    intro parameter lower upper
    exact data.boundaryOrientedInputCell.path_denominator_ne_on_cell
      lower upper

theorem CheckpointPositiveGuardData.boundaryPathCylinder_path
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    data.boundaryPathCylinder.path =
      data.sourceCell.partition.entry.chart.path := by
  change data.boundaryCandidate.sourceEvent.sourceCell.partition.entry.chart.path =
    data.sourceCell.partition.entry.chart.path
  rw [data.boundaryCandidate_sourceEvent]
  rfl

/-- Positive residual cap used to distinguish every localized boundary sample
from zero. -/
def checkpointBoundaryCap (p : GaussianPolynomial) : ℚ :=
  normSq (p.eval 0) / 2

theorem checkpointBoundaryCap_pos
    (p : GaussianPolynomial) (zeroNonzero : p.eval 0 ≠ 0) :
    0 < checkpointBoundaryCap p :=
  div_pos (normSq_pos zeroNonzero) (by norm_num)

theorem checkpointBoundaryCap_le_zeroResidual (p : GaussianPolynomial) :
    checkpointBoundaryCap p ≤ normSq (p.eval 0) :=
  div_le_self (normSq_nonneg (p.eval 0)) (by norm_num)

/-- Proof-bearing count-one approximation used by one boundary sample.  The
underlying narrowing automatically includes the event-classifier resolution
cap in addition to the numerical localization width. -/
def checkpointBoundaryApproximation
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    NarrowEventApproximation
      data.boundaryOrientedInputCell.branch.factor.input
      (data.boundaryOrientedInputCell.branch.computeEventSigns
        data.boundaryOrientedInputCell.parent).refined
      (eventSourceApproximationWidth data.boundaryOrientedInputCell squarefree
        (localizedClearance data.separation
          (cappedClearanceState next (checkpointBoundaryCap p)
            (checkpointBoundaryCap_pos p zeroNonzero)))) :=
  data.boundaryOrientedInputCell.clearedApproximation
    (eventSourceApproximationWidth data.boundaryOrientedInputCell squarefree
      (localizedClearance data.separation
        (cappedClearanceState next (checkpointBoundaryCap p)
          (checkpointBoundaryCap_pos p zeroNonzero))))
    (eventSourceApproximationWidth_pos data.boundaryOrientedInputCell
      squarefree (localizedClearance data.separation
        (cappedClearanceState next (checkpointBoundaryCap p)
          (checkpointBoundaryCap_pos p zeroNonzero))))

/-- Canonical lower parameter underlying the localized rational path point. -/
def checkpointBoundaryParameter
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) : ℚ :=
  (checkpointBoundaryApproximation data squarefree zeroNonzero next).refined.interval.lower

/-- Canonical rational point on the retained boundary path in an arbitrary
later winding box.  Only the stored clearance is capped; the box itself is
definitionally unchanged. -/
def checkpointBoundaryPoint
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) : QI :=
  localizedCellPoint data.separation data.boundaryOrientedInputCell
    squarefree (cappedClearanceState next (checkpointBoundaryCap p)
      (checkpointBoundaryCap_pos p zeroNonzero))

theorem checkpointBoundaryPoint_eq_pathValue
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    checkpointBoundaryPoint data squarefree zeroNonzero next =
      data.boundaryPathCylinder.path.value
        (checkpointBoundaryParameter data squarefree zeroNonzero next) := by
  rfl

/-- Every boundary parameter is the lower endpoint of a canonically oriented
count-one event approximation. -/
theorem checkpointBoundaryParameter_derivative_mul_neg
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    data.boundaryOrientedInputCell.branch.factor.polynomial.eval
          (checkpointBoundaryParameter data squarefree zeroNonzero next) *
        (derivative
          data.boundaryOrientedInputCell.branch.factor.polynomial).eval
          (checkpointBoundaryParameter data squarefree zeroNonzero next) <
      0 := by
  exact narrowEventApproximation_lower_derivative_mul_neg
    data.boundaryOrientedInputCell.branch.factor.input
    (data.boundaryOrientedInputCell.branch.computeEventSigns
      data.boundaryOrientedInputCell.parent).refined
    (eventSourceApproximationWidth data.boundaryOrientedInputCell squarefree
      (localizedClearance data.separation
        (cappedClearanceState next (checkpointBoundaryCap p)
          (checkpointBoundaryCap_pos p zeroNonzero))))
    (eventSourceApproximationWidth_pos data.boundaryOrientedInputCell
      squarefree (localizedClearance data.separation
        (cappedClearanceState next (checkpointBoundaryCap p)
          (checkpointBoundaryCap_pos p zeroNonzero))))

/-- All canonical lower parameters lie on the same strict side of the one
squarefree event factor, even though they arise from independent numerical
box refinements. -/
theorem checkpointBoundaryEventFactor_mul_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    0 < data.boundaryOrientedInputCell.branch.factor.polynomial.eval
          (checkpointBoundaryParameter data squarefree zeroNonzero
            data.output.state) *
        data.boundaryOrientedInputCell.branch.factor.polynomial.eval
          (checkpointBoundaryParameter data squarefree zeroNonzero next) := by
  let cell := data.boundaryOrientedInputCell
  let signs := cell.branch.computeEventSigns cell.parent
  let baseApproximation := checkpointBoundaryApproximation data squarefree
    zeroNonzero data.output.state
  let nextApproximation := checkpointBoundaryApproximation data squarefree
    zeroNonzero next
  have baseLower : cell.parent.interval.lower ≤
      checkpointBoundaryParameter data squarefree zeroNonzero
        data.output.state :=
    signs.refines.1.trans baseApproximation.refines.1
  have baseUpper : checkpointBoundaryParameter data squarefree zeroNonzero
      data.output.state ≤ cell.parent.interval.upper :=
    baseApproximation.refined.proper.le.trans
      (baseApproximation.refines.2.trans signs.refines.2)
  have nextLower : cell.parent.interval.lower ≤
      checkpointBoundaryParameter data squarefree zeroNonzero next :=
    signs.refines.1.trans nextApproximation.refines.1
  have nextUpper : checkpointBoundaryParameter data squarefree zeroNonzero
      next ≤ cell.parent.interval.upper :=
    nextApproximation.refined.proper.le.trans
      (nextApproximation.refines.2.trans signs.refines.2)
  have derivativeAligned := data.boundaryDerivativeSign.eval_mul_pos_between
    baseLower baseUpper nextLower nextUpper
  exact mul_pos_of_mul_neg_of_orienters_mul_pos
    (checkpointBoundaryParameter_derivative_mul_neg data squarefree
      zeroNonzero data.output.state)
    (checkpointBoundaryParameter_derivative_mul_neg data squarefree
      zeroNonzero next)
    derivativeAligned

/-- A current decision form which is canonically strict in the classified
event cell has the same cleared sign at any two independently localized lower
approximations. -/
theorem checkpointBoundaryClearedForm_mul_pos_of_canonicalNonzero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (form : HermitianForm)
    (member : form ∈
      inputDecisionForms (RawParser.parse current.core.word))
    (canonicalNonzero :
      inputEventCanonicalValue data.boundaryOrientedInputCell form ≠ 0) :
    0 < (clearedForm form data.boundaryPathCylinder.path).eval
          (checkpointBoundaryParameter data squarefree zeroNonzero
            data.output.state) *
        (clearedForm form data.boundaryPathCylinder.path).eval
          (checkpointBoundaryParameter data squarefree zeroNonzero next) := by
  let cell := data.boundaryOrientedInputCell
  let signs := cell.branch.computeEventSigns cell.parent
  let baseApproximation := checkpointBoundaryApproximation data squarefree
    zeroNonzero data.output.state
  let nextApproximation := checkpointBoundaryApproximation data squarefree
    zeroNonzero next
  have polynomialMember :
      clearedForm form data.boundaryPathCylinder.path ∈
        inputEventPolynomials (RawParser.parse current.core.word)
          data.boundaryPathCylinder.path :=
    clearedForm_mem_inputEventPolynomials_of_inputDecisionForm
      (RawParser.parse current.core.word) data.boundaryPathCylinder.path form
        member
  have baseSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      cell.branch.relations cell.parent signs polynomialMember (by
        simpa only [inputEventCanonicalValue,
          CheckpointPositiveGuardData.boundaryPathCylinder, cell, signs] using
          canonicalNonzero)
      baseApproximation.refines.1
      (baseApproximation.refined.proper.le.trans
        baseApproximation.refines.2)
  have nextSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      cell.branch.relations cell.parent signs polynomialMember (by
        simpa only [inputEventCanonicalValue,
          CheckpointPositiveGuardData.boundaryPathCylinder, cell, signs] using
          canonicalNonzero)
      nextApproximation.refines.1
      (nextApproximation.refined.proper.le.trans
        nextApproximation.refines.2)
  exact CCLCoupledTrack.sameSign_of_common_anchor baseSign nextSign

private theorem mul_pos_of_positive_scales
    {leftScale rightScale left right : ℚ}
    (scaled : 0 < (leftScale * left) * (rightScale * right))
    (leftScalePositive : 0 < leftScale)
    (rightScalePositive : 0 < rightScale) :
    0 < left * right := by
  have scalesPositive : 0 < leftScale * rightScale :=
    mul_pos leftScalePositive rightScalePositive
  have rearranged : 0 < (leftScale * rightScale) * (left * right) := by
    calc
      0 < (leftScale * left) * (rightScale * right) := scaled
      _ = (leftScale * rightScale) * (left * right) := by ring
  exact (mul_pos_iff_of_pos_left scalesPositive).mp rearranged

/-- Positive denominator norms transfer any strict cleared-polynomial sign
between two canonical boundary samples back to the actual Hermitian form. -/
theorem checkpointBoundaryForm_mul_pos_of_clearedForm_mul_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (form : HermitianForm)
    (clearedSign :
      0 < (clearedForm form data.boundaryPathCylinder.path).eval
            (checkpointBoundaryParameter data squarefree zeroNonzero
              data.output.state) *
          (clearedForm form data.boundaryPathCylinder.path).eval
            (checkpointBoundaryParameter data squarefree zeroNonzero next)) :
    0 < form.eval (checkpointBoundaryPoint data squarefree zeroNonzero
          data.output.state) *
        form.eval (checkpointBoundaryPoint data squarefree zeroNonzero next) := by
  let baseApproximation := checkpointBoundaryApproximation data squarefree
    zeroNonzero data.output.state
  let nextApproximation := checkpointBoundaryApproximation data squarefree
    zeroNonzero next
  have baseDenominator :=
    data.boundaryOrientedInputCell.path_denominator_ne_on_cell
      baseApproximation.refines.1
      (baseApproximation.refined.proper.le.trans
        baseApproximation.refines.2)
  have nextDenominator :=
    data.boundaryOrientedInputCell.path_denominator_ne_on_cell
      nextApproximation.refines.1
      (nextApproximation.refined.proper.le.trans
        nextApproximation.refines.2)
  rw [eval_clearedForm form data.boundaryPathCylinder.path
        (checkpointBoundaryParameter data squarefree zeroNonzero
          data.output.state) baseDenominator,
      eval_clearedForm form data.boundaryPathCylinder.path
        (checkpointBoundaryParameter data squarefree zeroNonzero next)
        nextDenominator] at clearedSign
  have baseScalePositive : 0 <
      (denominatorNorm data.boundaryPathCylinder.path).eval
        (checkpointBoundaryParameter data squarefree zeroNonzero
          data.output.state) :=
    eval_denominatorNorm_pos data.boundaryPathCylinder.path _ baseDenominator
  have nextScalePositive : 0 <
      (denominatorNorm data.boundaryPathCylinder.path).eval
        (checkpointBoundaryParameter data squarefree zeroNonzero next) :=
    eval_denominatorNorm_pos data.boundaryPathCylinder.path _ nextDenominator
  rw [checkpointBoundaryPoint_eq_pathValue,
    checkpointBoundaryPoint_eq_pathValue]
  exact mul_pos_of_positive_scales clearedSign baseScalePositive
    nextScalePositive

/-- Positive denominator norms transfer the preceding cleared-polynomial sign
back to the actual Hermitian comparison at the two rational path points. -/
theorem checkpointBoundaryForm_mul_pos_of_canonicalNonzero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (form : HermitianForm)
    (member : form ∈
      inputDecisionForms (RawParser.parse current.core.word))
    (canonicalNonzero :
      inputEventCanonicalValue data.boundaryOrientedInputCell form ≠ 0) :
    0 < form.eval (checkpointBoundaryPoint data squarefree zeroNonzero
          data.output.state) *
        form.eval (checkpointBoundaryPoint data squarefree zeroNonzero next) := by
  apply checkpointBoundaryForm_mul_pos_of_clearedForm_mul_pos data squarefree
    zeroNonzero next form
  exact checkpointBoundaryClearedForm_mul_pos_of_canonicalNonzero data
    squarefree zeroNonzero next form member canonicalNonzero

/-- Canonical equality for a current decision form exposes the exact
event-factor divisibility certificate retained by the classifier. -/
theorem checkpointBoundaryEventFactor_dvd_of_canonicalZero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (form : HermitianForm)
    (member : form ∈
      inputDecisionForms (RawParser.parse current.core.word))
    (canonicalZero :
      inputEventCanonicalValue data.boundaryOrientedInputCell form = 0) :
    data.boundaryOrientedInputCell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form data.boundaryPathCylinder.path).toPolynomial := by
  let cell := data.boundaryOrientedInputCell
  let signs := cell.branch.computeEventSigns cell.parent
  have polynomialMember :
      clearedForm form data.boundaryPathCylinder.path ∈
        inputEventPolynomials (RawParser.parse current.core.word)
          data.boundaryPathCylinder.path :=
    clearedForm_mem_inputEventPolynomials_of_inputDecisionForm
      (RawParser.parse current.core.word) data.boundaryPathCylinder.path form
        member
  apply ConditionRelations.dvd_of_canonicalEventValue_eq_zero
    cell.branch.relations cell.parent signs polynomialMember
  simpa only [inputEventCanonicalValue,
    CheckpointPositiveGuardData.boundaryPathCylinder, cell, signs] using
      canonicalZero

theorem checkpointBoundaryPoint_supported
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    data.boundaryPathCylinder.Contains
      (checkpointBoundaryPoint data squarefree zeroNonzero next) := by
  let cap := checkpointBoundaryCap p
  let capPositive := checkpointBoundaryCap_pos p zeroNonzero
  let capped := cappedClearanceState next cap capPositive
  let cell := data.boundaryOrientedInputCell
  let clearance := localizedClearance data.separation capped
  let approximation := cell.clearedApproximation
    (eventSourceApproximationWidth cell squarefree clearance)
    (eventSourceApproximationWidth_pos cell squarefree clearance)
  let parameter := approximation.refined.interval.lower
  refine ⟨parameter, approximation.refines.1,
    approximation.refined.proper.le.trans approximation.refines.2, ?_⟩
  rfl

theorem checkpointBoundaryPoint_strictContains
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.separation.state.box) :
    next.box.StrictContains
      (checkpointBoundaryPoint data squarefree zeroNonzero next) := by
  let cap := checkpointBoundaryCap p
  let capPositive := checkpointBoundaryCap_pos p zeroNonzero
  let capped := cappedClearanceState next cap capPositive
  have cappedRefines : capped.box.Refines data.separation.state.box := by
    simpa only [capped, cappedClearanceState_box] using nextRefines
  simpa only [checkpointBoundaryPoint, cap, capPositive, capped,
    cappedClearanceState_box] using
      localizedCellPoint_strictContains data.separation
        data.boundaryOrientedInputCell squarefree degreeNonzero elimination
        capped cappedRefines

theorem checkpointBoundaryPoint_ne_zero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    checkpointBoundaryPoint data squarefree zeroNonzero next ≠ 0 := by
  let cap := checkpointBoundaryCap p
  let capPositive := checkpointBoundaryCap_pos p zeroNonzero
  let capped := cappedClearanceState next cap capPositive
  have residual := localizedCellPoint_residual_lt data.separation
    data.boundaryOrientedInputCell squarefree capped
  have clearanceLe : capped.clearance.bound / 8 ≤ cap / 8 := by
    gcongr
    simpa only [capped] using
      cappedClearanceState_clearance_le next cap capPositive
  have capDivLe : cap / 8 ≤ normSq (p.eval 0) := by
    apply (div_le_self capPositive.le (by norm_num : (1 : ℚ) ≤ 8)).trans
    exact checkpointBoundaryCap_le_zeroResidual p
  intro zero
  have pointZero : localizedCellPoint data.separation
      data.boundaryOrientedInputCell squarefree capped = 0 := by
    simpa only [checkpointBoundaryPoint, cap, capPositive, capped] using zero
  rw [pointZero] at residual
  exact (not_lt_of_ge (clearanceLe.trans capDivLe)) residual

/-- Every later path-localized point still represents the unchanged checkpoint
word.  This uses universal wrapping only to retain the old prefix; no child is
asserted on an exact boundary. -/
theorem checkpointBoundaryPoint_represented
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.separation.state.box) :
    RawParserSemantics.Represented current.core.word
      (checkpointBoundaryPoint data squarefree zeroNonzero next) := by
  have inside := (checkpointBoundaryPoint_strictContains data squarefree
    degreeNonzero zeroNonzero elimination next nextRefines).contains
  exact current.wraps (data.separation.refines.contains
    (nextRefines.contains inside))

/-- The clear-family output retained by the positive guard refines the original
denominator-separated box through the intervening terminal separation. -/
theorem CheckpointPositiveGuardData.output_refines_separation
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    data.output.state.box.Refines data.separation.state.box :=
  data.output.refines.trans data.terminal.refines

/-- Every localized sample after the retained terminal separation admits at
least one actual complete child formula.  This is a pointwise existence fact;
the subsequent path-side stability argument must still show that one Boolean
works for all later samples. -/
theorem checkpointBoundaryPoint_hasChild
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.output.state.box) :
    ∃ bit, (inputAdvanceFormula (RawParser.parse current.core.word) bit).Holds
      (checkpointBoundaryPoint data squarefree zeroNonzero next) := by
  have separationRefines : next.box.Refines data.separation.state.box :=
    nextRefines.trans data.output_refines_separation
  have inside := (checkpointBoundaryPoint_strictContains data squarefree
    degreeNonzero zeroNonzero elimination next separationRefines).contains
  apply current.exists_inputAdvance_of_wrapped data.separation data.terminal
    (checkpointBoundaryPoint data squarefree zeroNonzero next)
  exact data.output.refines.contains (nextRefines.contains inside)

/-- Executable child label at one later constrained sample.  False is chosen
when it holds; terminal separation proves that true holds otherwise. -/
def checkpointBoundaryBit
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p (RatBox.symmetric R hR)) : Bool :=
  if (inputAdvanceFormula (RawParser.parse current.core.word) false).evalBool
      (checkpointBoundaryPoint data squarefree zeroNonzero next) then
    false
  else
    true

theorem checkpointBoundaryBit_holds
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines data.output.state.box) :
    (inputAdvanceFormula (RawParser.parse current.core.word)
      (checkpointBoundaryBit data squarefree zeroNonzero next)).Holds
        (checkpointBoundaryPoint data squarefree zeroNonzero next) := by
  by_cases falseCheck :
      (inputAdvanceFormula (RawParser.parse current.core.word) false).evalBool
        (checkpointBoundaryPoint data squarefree zeroNonzero next) = true
  · have falseHolds :=
      (CCLParserGeometry.Formula.evalBool_eq_true
        (inputAdvanceFormula (RawParser.parse current.core.word) false)
        (checkpointBoundaryPoint data squarefree zeroNonzero next)).1
          falseCheck
    simpa only [checkpointBoundaryBit, falseCheck, if_true] using falseHolds
  · rcases checkpointBoundaryPoint_hasChild data squarefree degreeNonzero
      zeroNonzero elimination next nextRefines with ⟨bit, holds⟩
    cases bit with
    | false =>
        exact (falseCheck
          ((CCLParserGeometry.Formula.evalBool_eq_true
            (inputAdvanceFormula (RawParser.parse current.core.word) false)
            (checkpointBoundaryPoint data squarefree zeroNonzero next)).2
              holds)).elim
    | true =>
        have falseEval :
            (inputAdvanceFormula (RawParser.parse current.core.word)
              false).evalBool
                (checkpointBoundaryPoint data squarefree zeroNonzero next) =
              false := Bool.eq_false_of_not_eq_true falseCheck
        simpa only [checkpointBoundaryBit, falseEval, Bool.false_eq_true,
          if_false] using holds

/-- Fixed child label selected at the retained boundary state's own rational
sample.  The remaining one-sided theorem states that this same label works in
every later nested box. -/
def checkpointBoundarySelectedBit
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) : Bool :=
  checkpointBoundaryBit data squarefree zeroNonzero data.output.state

theorem checkpointBoundarySelectedBit_holds
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (inputAdvanceFormula (RawParser.parse current.core.word)
      (checkpointBoundarySelectedBit data squarefree zeroNonzero)).Holds
        (checkpointBoundaryPoint data squarefree zeroNonzero
          data.output.state) := by
  exact checkpointBoundaryBit_holds data squarefree degreeNonzero zeroNonzero
    elimination data.output.state (RatBox.refines_refl data.output.state.box)

/-- Precise residual obligation for exact-boundary progress: the executable
base label must remain true on the canonical lower-side sample in every later
winding box. -/
def CheckpointBoundaryBitStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) : Prop :=
  ∀ (next : WindingOneState p (RatBox.symmetric R hR))
    (_nextRefines : next.box.Refines data.output.state.box),
    (inputAdvanceFormula (RawParser.parse current.core.word)
      (checkpointBoundarySelectedBit data squarefree zeroNonzero)).Holds
        (checkpointBoundaryPoint data squarefree zeroNonzero next)

/-- Geometric core of exact-boundary bit stability.  Every phase-local input
form must either keep one strict sign between the retained base sample and a
later sample, or be exact equality at both.  Historical parser atoms do not
occur in this obligation. -/
def CheckpointBoundaryDecisionFormsStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) : Prop :=
  ∀ (next : WindingOneState p (RatBox.symmetric R hR))
    (_nextRefines : next.box.Refines data.output.state.box)
    (form : HermitianForm)
    (_member : form ∈ inputDecisionForms (RawParser.parse current.core.word)),
    SameSignOrBothZero
      (form.eval (checkpointBoundaryPoint data squarefree zeroNonzero
        data.output.state))
      (form.eval (checkpointBoundaryPoint data squarefree zeroNonzero next))

/-- Residual geometric obligation after exact path equalities are removed:
only nonzero cleared restrictions of phase-local forms must keep their strict
side between lower event approximations. -/
def CheckpointBoundaryDecisionCrossingFormsStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) : Prop :=
  ∀ (next : WindingOneState p (RatBox.symmetric R hR))
    (_nextRefines : next.box.Refines data.output.state.box)
    (form : HermitianForm)
    (_member : form ∈ inputDecisionForms (RawParser.parse current.core.word)),
    (clearedForm form data.boundaryPathCylinder.path).isZero = false →
      0 < form.eval (checkpointBoundaryPoint data squarefree zeroNonzero
          data.output.state) *
        form.eval (checkpointBoundaryPoint data squarefree zeroNonzero next)

/-- The sole remaining shared-factor obligation: a nonzero current decision
form which is an exact multiple of the isolated event factor must keep its
one-sided sign at independently narrowed lower approximations. -/
def CheckpointBoundarySharedDecisionFormsStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) : Prop :=
  ∀ (next : WindingOneState p (RatBox.symmetric R hR))
    (_nextRefines : next.box.Refines data.output.state.box)
    (form : HermitianForm)
    (_member : form ∈
      inputDecisionForms (RawParser.parse current.core.word)),
    (clearedForm form data.boundaryPathCylinder.path).isZero = false →
    inputEventCanonicalValue data.boundaryOrientedInputCell form = 0 →
      0 < form.eval (checkpointBoundaryPoint data squarefree zeroNonzero
          data.output.state) *
        form.eval (checkpointBoundaryPoint data squarefree zeroNonzero next)

/-- Shared event factors are stable because every nonzero decision-form
restriction is affine.  Divisibility therefore leaves only a nonzero constant
cofactor, so the oriented event factor's same-side sign transfers verbatim. -/
theorem checkpointBoundarySharedDecisionFormsStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) :
    CheckpointBoundarySharedDecisionFormsStable data squarefree
      zeroNonzero := by
  intro next _nextRefines form member nonzero canonicalZero
  have stateDeterminant :
      determinant (RawParser.parse current.core.word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.core.word
  have sourceNondegenerate :
      data.sourceCell.partition.entry.source.ParametrizationNondegenerate :=
    inputPlan_parametrizationNondegenerate
      (RawParser.parse current.core.word) data.source_mem_inputPlan
  have degree :
      (clearedForm form data.boundaryPathCylinder.path).natDegree ≤ 1 := by
    rw [data.boundaryPathCylinder_path] at nonzero ⊢
    exact inputDecisionForm_clearedForm_natDegree_le_one
      (RawParser.parse current.core.word) data.source_mem_inputPlan
      data.sourceCell.partition.entry.chart
      (data.source_determinant_ne stateDeterminant) sourceNondegenerate form
      member nonzero
  have clearedSign := evals_mul_pos_of_dvd_natDegree_le_one
    data.boundaryOrientedInputCell.branch.factor.input nonzero degree
    (checkpointBoundaryEventFactor_dvd_of_canonicalZero data form member
      canonicalZero)
    (checkpointBoundaryEventFactor_mul_pos data squarefree zeroNonzero next)
  exact checkpointBoundaryForm_mul_pos_of_clearedForm_mul_pos data squarefree
    zeroNonzero next form clearedSign

/-- Coprime decision forms are already stable by their common event-cell sign
certificate, so a proof of the shared-factor case closes every genuine
crossing form. -/
theorem checkpointBoundaryDecisionCrossingFormsStable_of_shared
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (shared : CheckpointBoundarySharedDecisionFormsStable data squarefree
      zeroNonzero) :
    CheckpointBoundaryDecisionCrossingFormsStable data squarefree
      zeroNonzero := by
  intro next nextRefines form member nonzero
  by_cases canonicalZero :
      inputEventCanonicalValue data.boundaryOrientedInputCell form = 0
  · exact shared next nextRefines form member nonzero canonicalZero
  · exact checkpointBoundaryForm_mul_pos_of_canonicalNonzero data squarefree
      zeroNonzero next form member canonicalZero

/-- The executable zero-polynomial split closes every retained path-equality
form automatically, leaving only genuine crossing forms to the strict-side
argument. -/
theorem checkpointBoundaryDecisionFormsStable_of_crossingForms
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (crossing : CheckpointBoundaryDecisionCrossingFormsStable data squarefree
      zeroNonzero) :
    CheckpointBoundaryDecisionFormsStable data squarefree zeroNonzero := by
  intro next nextRefines form member
  cases zero : (clearedForm form data.boundaryPathCylinder.path).isZero with
  | false =>
      exact Or.inl (crossing next nextRefines form member zero)
  | true =>
      right
      rcases checkpointBoundaryPoint_supported data squarefree zeroNonzero
          data.output.state with ⟨baseParameter, baseLower, baseUpper, baseEq⟩
      rcases checkpointBoundaryPoint_supported data squarefree zeroNonzero
          next with ⟨nextParameter, nextLower, nextUpper, nextEq⟩
      have equalityMember : form ∈ pathEqualityForms
          (inputDecisionForms (RawParser.parse current.core.word))
          data.boundaryPathCylinder.path := by
        exact (mem_pathEqualityForms_iff _ _ _).2 ⟨member, zero⟩
      constructor
      · rw [baseEq]
        exact eval_eq_zero_of_mem_pathEqualityForms _ _ equalityMember
          baseParameter
          (data.boundaryPathCylinder.denominator_ne baseLower baseUpper)
      · rw [nextEq]
        exact eval_eq_zero_of_mem_pathEqualityForms _ _ equalityMember
          nextParameter
          (data.boundaryPathCylinder.denominator_ne nextLower nextUpper)

/-- Every current decision form is stable at all later boundary samples.  The
proof is total: canonical nonzero forms use their classified sign, canonical
zero forms use affine shared-factor divisibility, and path equalities remain
exact equalities. -/
theorem checkpointBoundaryDecisionFormsStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0) :
    CheckpointBoundaryDecisionFormsStable data squarefree zeroNonzero :=
  checkpointBoundaryDecisionFormsStable_of_crossingForms data squarefree
    zeroNonzero
      (checkpointBoundaryDecisionCrossingFormsStable_of_shared data squarefree
        zeroNonzero
          (checkpointBoundarySharedDecisionFormsStable data squarefree
            zeroNonzero))

/-- Closed-stratum stability of the finite local forms is sufficient for the
same executable child bit to hold at every later boundary sample. -/
theorem checkpointBoundaryBitStable_of_inputForms
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (stable : CheckpointBoundaryDecisionFormsStable data squarefree
      zeroNonzero) :
    CheckpointBoundaryBitStable data squarefree zeroNonzero := by
  intro next nextRefines
  let state := RawParser.parse current.core.word
  let basePoint := checkpointBoundaryPoint data squarefree zeroNonzero
    data.output.state
  let nextPoint := checkpointBoundaryPoint data squarefree zeroNonzero next
  have baseInsideOutput :=
    (checkpointBoundaryPoint_strictContains data squarefree degreeNonzero
      zeroNonzero elimination data.output.state
        data.output_refines_separation).contains
  have baseInsideSeparation : data.separation.state.box.Contains basePoint :=
    data.output_refines_separation.contains baseInsideOutput
  have nextInside :=
    (checkpointBoundaryPoint_strictContains data squarefree degreeNonzero
      zeroNonzero elimination next
        (nextRefines.trans data.output_refines_separation)).contains
  have nextInsideSeparation : data.separation.state.box.Contains nextPoint :=
    data.output_refines_separation.contains (nextRefines.contains nextInside)
  have baseDenominator := separation_denominator_ne data.separation
    baseInsideSeparation
  have nextDenominator := separation_denominator_ne data.separation
    nextInsideSeparation
  have baseHolds := checkpointBoundarySelectedBit_holds data squarefree
    degreeNonzero zeroNonzero elimination
  rcases checkpointBoundaryPoint_hasChild data squarefree degreeNonzero
      zeroNonzero elimination next nextRefines with ⟨nextBit, nextHolds⟩
  have bitEq := inputAdvance_bits_eq_of_inputDecisionForms_sameSignOrBothZero state
    basePoint nextPoint baseDenominator nextDenominator baseHolds nextHolds
      (stable next nextRefines)
  simpa only [bitEq] using nextHolds

/-- The selected child is unconditionally stable along the retained boundary
cylinder while the independent winding box continues to refine. -/
theorem checkpointBoundaryBitStable
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CheckpointBoundaryBitStable data squarefree zeroNonzero :=
  checkpointBoundaryBitStable_of_inputForms data squarefree degreeNonzero
    zeroNonzero elimination
      (checkpointBoundaryDecisionFormsStable data squarefree zeroNonzero)

/-- Honest same-word constrained persistence for the all-neither boundary
case.  Numerical contraction continues independently while every symbolic
sample remains on the one fixed rational source cylinder. -/
def checkpointBoundarySamples
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    PersistentConstrainedRepresentedSamples current.core.word
      data.output.state data.boundaryPathCylinder.Contains where
  sample next nextRefines :=
    let separationRefines := nextRefines.trans data.output_refines_separation
    { point := checkpointBoundaryPoint data squarefree zeroNonzero next
      inside := (checkpointBoundaryPoint_strictContains data squarefree
        degreeNonzero zeroNonzero elimination next separationRefines).contains
      nonzero := checkpointBoundaryPoint_ne_zero data squarefree zeroNonzero
        next
      semantics := checkpointBoundaryPoint_represented data squarefree
        degreeNonzero zeroNonzero elimination next separationRefines
      supported := checkpointBoundaryPoint_supported data squarefree
        zeroNonzero next }

/-- Rebase the retained denominator margin at the already refined boundary
state.  Its numerical output is definitionally unchanged, so a path-local bit
can be appended without another box refinement. -/
def CheckpointPositiveGuardData.boundaryDenominator
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current) :
    CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      data.output.state
      (adjugate (RawParser.parse current.core.word).matrix) where
  state := data.output.state
  refines := RatBox.refines_refl data.output.state.box
  margin := data.separation.margin
  margin_pos := data.separation.margin_pos
  lower := by
    intro input inside
    exact data.separation.lower (data.output_refines_separation.contains inside)

/-- Once one-sided stability is supplied, the same-word constrained family
extends to the fixed selected child without claiming a whole-box formula. -/
def checkpointBoundaryAppendedSamples
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    PersistentConstrainedRepresentedSamples
      (current.core.word ++
        [checkpointBoundarySelectedBit data squarefree zeroNonzero])
      data.output.state data.boundaryPathCylinder.Contains :=
  constrainedAfterSampleFormula data.boundaryPathCylinder
    (checkpointBoundarySamples data squarefree degreeNonzero zeroNonzero
      elimination)
    data.boundaryDenominator
    (checkpointBoundarySelectedBit data squarefree zeroNonzero) (by
      intro next nextRefines
      exact checkpointBoundaryBitStable data squarefree degreeNonzero
        zeroNonzero elimination next nextRefines)

/-- Persistent coupled state reached without appending a bit at a genuine CCL
boundary. -/
def checkpointBoundaryPersistentState
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CCLCoupledTrack.PersistentState p (RatBox.symmetric R hR) :=
  CCLCoupledTrack.PersistentState.ofConstrainedSamples
    data.boundaryPathCylinder
    (checkpointBoundarySamples data squarefree degreeNonzero zeroNonzero
      elimination)

/-- Appended constrained successor exposed in the exact shape consumed by the
persistent controller once one-sided bit stability has been proved. -/
def checkpointBoundaryPersistentStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CCLCoupledTrack.PersistentStepResult
      (checkpointBoundaryPersistentState data squarefree degreeNonzero
        zeroNonzero elimination) :=
  nextOfConstrainedSampleFormula data.boundaryPathCylinder
    (checkpointBoundarySamples data squarefree degreeNonzero zeroNonzero
      elimination)
    data.boundaryDenominator
    (checkpointBoundarySelectedBit data squarefree zeroNonzero) (by
      intro next nextRefines
      exact checkpointBoundaryBitStable data squarefree degreeNonzero
        zeroNonzero elimination next nextRefines)

/-- Metric continuation that keeps the old raw cylinder while switching its
semantic persistence mode to the exact rational boundary path. -/
def checkpointBoundaryMetricState
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CCLMetricTrack.State p (RatBox.symmetric R hR) where
  core := checkpointBoundaryPersistentState data squarefree degreeNonzero
    zeroNonzero elimination
  cylinder := current.cylinder
  cylinder_word := current.cylinder_word

/-- Metric-cylinder lift of the exact-boundary appended successor. -/
def checkpointBoundaryMetricStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CCLMetricTrack.StepResult
      (checkpointBoundaryMetricState data squarefree degreeNonzero zeroNonzero
        elimination) :=
  CCLMetricTrack.liftStepResult
    (checkpointBoundaryMetricState data squarefree degreeNonzero zeroNonzero
      elimination)
    (checkpointBoundaryPersistentStep data squarefree degreeNonzero
      zeroNonzero elimination)

/-- At a completed sector, the exact-boundary bit step enters the same
completed-history half-radius contraction as an open-cell persistent step.
The contraction theorem is deliberately independent of persistence mode. -/
def checkpointBoundaryCompletedMetricStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second)) :
    CompletedMetricStepResult
      (checkpointBoundaryMetricState data squarefree degreeNonzero zeroNonzero
        elimination) :=
  tightenCompletedStep (by
    change (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second)
    exact phase)
      (checkpointBoundaryMetricStep data squarefree degreeNonzero zeroNonzero
        elimination)

theorem checkpointBoundaryMetricState_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (checkpointBoundaryMetricState data squarefree degreeNonzero zeroNonzero
      elimination).Refines (checkpointMetricState current) := by
  exact ⟨data.output_refines_separation.trans data.separation.refines,
    RawCylinderEnvelope.refines_refl _⟩

@[simp] theorem checkpointBoundaryMetricState_word
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p
      (RatBox.symmetric R hR)}
    (data : CheckpointPositiveGuardData p R hR current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (checkpointBoundaryMetricState data squarefree degreeNonzero zeroNonzero
      elimination).core.word = current.core.word :=
  rfl

/-- Complete-table fallback after ordinary clearance, terminal separation,
and guard traversal.  A positive guard is retained with complete all-neither
provenance; every other branch is already a metric step or an exact root. -/
inductive CheckpointCompleteClearOpening
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR)) where
  | ready (result : CCLMetricTrack.StepResult
      (checkpointMetricState current))
      (canonical : MetricStepControllerCanonical result)
  | planned (plan : CCLDirectTrack.PlannedBit current.core)
  | positiveGuard (data : CheckpointPositiveGuardData p R hR current)

/-- Continue the no-validity complete-table fallback through every finite
clear branch.  The same strict-cell plan preserves whole-box wrapping; only a
genuinely positive terminal guard remains for a later relevance argument. -/
def CheckpointCompleteEventOpening.resolveClear
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR)}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (clearOwnerLabel : Bool) :
    CheckpointCompleteEventOpening p R hR current →
      CheckpointCompleteClearOpening p R hR current
  | .ready result canonical => .ready result canonical
  | .allNeither separation globalNone guardNone =>
      match refineSeparatedClearFamily track current.core.numerical
          (RawParser.parse current.core.word) (by
            simpa only [determinant, Mat2.det] using
              RawParser.parse_det_ne current.core.word)
          separation clearOwnerLabel with
      | .terminal point _contains root => by
          if zero : point = 0 then
            exact .ready (.zero (by simpa only [zero] using root)) (by trivial)
          else
            exact .ready (.terminal point root zero
              (RationalEncoder.encode point zero) rfl) (by trivial)
      | .refined arcs evidence alignment _preliminaryOutput =>
          match rootCheck : CCLCoupledController.firstIdenticallyZeroRoot?
              (RawParser.parse current.core.word) separation with
          | some exactRoot => by
              if zero : exactRoot.point = 0 then
                exact .ready (.zero (by
                  simpa only [zero] using exactRoot.root)) (by trivial)
              else
                exact .ready (.terminal exactRoot.point exactRoot.root zero
                  (RationalEncoder.encode exactRoot.point zero) rfl) (by trivial)
          | none =>
              match CCLTerminalSeparation.separate track
                  (RawParser.parse current.core.word) separation.state with
              | .terminal point root _contains => by
                  if zero : point = 0 then
                    exact .ready (.zero (by simpa only [zero] using root))
                      (by trivial)
                  else
                    exact .ready (.terminal point root zero
                      (RationalEncoder.encode point zero) rfl) (by trivial)
              | .separated terminal =>
                  let output := refineForClearance track terminal.numerical
                    evidence
                  match decideSeparatedGuardCurveFamily
                      (RawParser.parse current.core.word) separation (by
                        simpa only [determinant, Mat2.det] using
                          RawParser.parse_det_ne current.core.word) with
                  | .allClear guardEvidence =>
                      let planned := plannedBitOfGuardClearPlan track
                        strictRefine current.core separation terminal evidence
                          alignment output guardEvidence
                      .planned planned
                  | .identicallyZero sourceCell member realZero imagZero
                      _relevance => by
                      let exactRoot :=
                        CCLCoupledController.exactRootOfSeparatedIdenticallyZeroGuardCell
                          separation (by
                            simpa only [determinant, Mat2.det] using
                              RawParser.parse_det_ne current.core.word)
                          sourceCell member realZero imagZero
                      if zero : exactRoot.point = 0 then
                        exact .ready (.zero (by
                          simpa only [zero] using exactRoot.root)) (by trivial)
                      else
                        exact .ready (.terminal exactRoot.point exactRoot.root
                          zero (RationalEncoder.encode exactRoot.point zero)
                            rfl) (by trivial)
                  | .positive sourceCell member clearedNonzero countPositive
                      event eventMember =>
                      .positiveGuard
                        { separation := separation
                          globalNone := globalNone
                          guardNone := guardNone
                          noIdenticallyZero := rootCheck
                          arcs := arcs
                          evidence := evidence
                          alignment := alignment
                          terminal := terminal
                          output := output
                          sourceCell := sourceCell
                          member := member
                          clearedNonzero := clearedNonzero
                          countPositive := countPositive
                          event := event
                          eventMember := eventMember }

/-- No-validity checkpoint controller through complete event tables and all
finite clear/terminal stages. -/
def openCheckpointCompleteClearStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CheckpointCompleteClearOpening p R hR current :=
  (openCheckpointCompleteEvents track current squarefree degreeNonzero
    zeroNonzero elimination).resolveClear track strictRefine clearOwnerLabel

/-- The checkpoint front half is now total through denominator separation and
both history-free event families.  Only the all-neither branch is retained for
the clear/strict-cell half of the x--y descent. -/
inductive CheckpointIncrementalEventOpening
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR)) where
  | ready (result : CCLMetricTrack.StepResult
      (checkpointMetricState current))
  | allNeither
      (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
        current.core.numerical
        (adjugate (RawParser.parse current.core.word).matrix))
      (globalNone : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.core.word) separation,
        CCLPositiveEventSemantics.inputEventIncrementalChecks
          candidate.inputCell = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.core.word) separation,
        CCLPositiveEventSemantics.inputEventIncrementalChecks
          candidate.inputCell = (false, false))

/-- Execute the checkpoint's denominator and event-owner half.  Exact decoder
roots terminate immediately; every genuine owner uses the total classified
grid and enters the metric pipeline with the inherited cylinder restricted. -/
def openCheckpointIncrementalEvents
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (valid : ControllerCanonicalOnInputEvents current.core.numerical
      current.core.word)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CheckpointIncrementalEventOpening p R hR current :=
  match CCLDenominator.decide track current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix)
      (CCLBranchEvidence.adjugate_lowerRow_ne
        (RawParser.parse current.core.word).matrix (by
          simpa only [determinant, Mat2.det] using
            RawParser.parse_det_ne current.core.word)) with
  | .terminal point root _contains _strict _denominatorZero => by
      if zero : point = 0 then
        exact .ready (.zero (by simpa only [zero] using root))
      else
        exact .ready (.terminal point root zero
          (RationalEncoder.encode point zero) rfl)
  | .separated separation =>
      match CCLIncrementalEventOwner.decideCombined
          (RawParser.parse current.core.word) separation with
      | .globalOwner selected =>
          .ready
            (metricStepOfCheckpointIncrementalGridOwnerWithCanonical current
              separation selected.toPayload
                ((valid separation).1 selected.candidate selected.member)
                  squarefree degreeNonzero zeroNonzero elimination)
      | .guardOwner selected =>
          .ready
            (metricStepOfCheckpointIncrementalGridOwnerWithCanonical current
              separation selected.toPayload
                ((valid separation).2 selected.candidate selected.member)
                  squarefree degreeNonzero zeroNonzero elimination)
      | .allNeither globalNone guardNone =>
          .allNeither separation globalNone guardNone

/-- Checkpoint result after the all-neither branch has run ordinary clearance,
exact-root scans, terminal separation, and the guard-family trichotomy.  A
positive terminal guard is retained with all of its finite provenance. -/
inductive CheckpointIncrementalClearOpening
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR)) where
  | ready (result : CCLMetricTrack.StepResult
      (checkpointMetricState current))
  | positiveGuard
      (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
        current.core.numerical
        (adjugate (RawParser.parse current.core.word).matrix))
      (globalNone : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.core.word) separation,
        CCLPositiveEventSemantics.inputEventIncrementalChecks
          candidate.inputCell = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.core.word) separation,
        CCLPositiveEventSemantics.inputEventIncrementalChecks
          candidate.inputCell = (false, false))
      (noIdenticallyZero : CCLCoupledController.firstIdenticallyZeroRoot?
        (RawParser.parse current.core.word) separation = Option.none)
      (arcs : List (BoundaryArc p)) (evidence : AllClear p arcs)
      (alignment : ClearFamilyAlignment p separation.state.box
        (separatedRelevantClearCells p (RawParser.parse current.core.word)
          separation) arcs)
      (terminal : CCLTerminalSeparation.SeparationOutput p
        (RatBox.symmetric R hR) (RawParser.parse current.core.word)
          separation.state [false, true])
      (output : RefinementOutput p (RatBox.symmetric R hR)
        terminal.numerical evidence)
      (sourceCell : SourceEventGuardCell p separation.state.box)
      (member : sourceCell ∈ separatedEventGuardCells p
        (RawParser.parse current.core.word) separation)
      (clearedNonzero :
        (FTA.ProjectivePath.clearedReal p
          sourceCell.partition.entry.chart.path).isZero = false ∨
        (FTA.ProjectivePath.clearedImag p
          sourceCell.partition.entry.chart.path).isZero = false)
      (countPositive : 0 < FTA.ProjectivePath.commonFactorRootCount2 p
        sourceCell.partition.entry.chart.path clearedNonzero
        sourceCell.item.cell.cell.interval.lower
        sourceCell.item.cell.cell.interval.upper)
      (event : RelevantCurveEvent p
        sourceCell.partition.entry.chart.path separation.state.box)
      (eventMember : event ∈
        CCLBranchEvent.EventGuardCell.relevantCurveEvents
          sourceCell.item.cell)

/-- Finish the checkpoint all-neither branch constructively.  The all-clear
guard case retains whole-box wrapping through `PlannedBit`; only a genuinely
positive guard cell remains pending. -/
def CheckpointIncrementalEventOpening.resolveClear
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR)}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (clearOwnerLabel : Bool) :
    CheckpointIncrementalEventOpening p R hR current →
      CheckpointIncrementalClearOpening p R hR current
  | .ready result => .ready result
  | .allNeither separation globalNone guardNone =>
      match refineSeparatedClearFamily track current.core.numerical
          (RawParser.parse current.core.word) (by
            simpa only [determinant, Mat2.det] using
              RawParser.parse_det_ne current.core.word)
          separation clearOwnerLabel with
      | .terminal point _contains root => by
          if zero : point = 0 then
            exact .ready (.zero (by simpa only [zero] using root))
          else
            exact .ready (.terminal point root zero
              (RationalEncoder.encode point zero) rfl)
      | .refined arcs evidence alignment _preliminaryOutput =>
          match rootCheck : CCLCoupledController.firstIdenticallyZeroRoot?
              (RawParser.parse current.core.word) separation with
          | some exactRoot => by
              if zero : exactRoot.point = 0 then
                exact .ready (.zero (by
                  simpa only [zero] using exactRoot.root))
              else
                exact .ready (.terminal exactRoot.point exactRoot.root zero
                  (RationalEncoder.encode exactRoot.point zero) rfl)
          | none =>
              match CCLTerminalSeparation.separate track
                  (RawParser.parse current.core.word) separation.state with
              | .terminal point root _contains => by
                  if zero : point = 0 then
                    exact .ready (.zero (by simpa only [zero] using root))
                  else
                    exact .ready (.terminal point root zero
                      (RationalEncoder.encode point zero) rfl)
              | .separated terminal =>
                  let output := refineForClearance track terminal.numerical
                    evidence
                  match decideSeparatedGuardCurveFamily
                      (RawParser.parse current.core.word) separation (by
                        simpa only [determinant, Mat2.det] using
                          RawParser.parse_det_ne current.core.word) with
                  | .allClear guardEvidence =>
                      let planned := plannedBitOfGuardClearPlan track
                        strictRefine current.core separation terminal evidence
                          alignment output guardEvidence
                      .ready (metricStepOfCheckpointPlannedBit current planned)
                  | .identicallyZero sourceCell member realZero imagZero
                      _relevance => by
                      let exactRoot :=
                        CCLCoupledController.exactRootOfSeparatedIdenticallyZeroGuardCell
                          separation (by
                            simpa only [determinant, Mat2.det] using
                              RawParser.parse_det_ne current.core.word)
                          sourceCell member realZero imagZero
                      if zero : exactRoot.point = 0 then
                        exact .ready (.zero (by
                          simpa only [zero] using exactRoot.root))
                      else
                        exact .ready (.terminal exactRoot.point exactRoot.root
                          zero (RationalEncoder.encode exactRoot.point zero)
                            rfl)
                  | .positive sourceCell member clearedNonzero countPositive
                      event eventMember =>
                      .positiveGuard separation globalNone guardNone rootCheck
                        arcs evidence alignment terminal output sourceCell
                          member clearedNonzero countPositive event eventMember

/-- Complete the checkpoint controller through every finite clear stage except
the retained positive-guard relevance branch. -/
def openCheckpointIncrementalClearStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (clearOwnerLabel : Bool)
    (valid : ControllerCanonicalOnInputEvents current.core.numerical
      current.core.word)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CheckpointIncrementalClearOpening p R hR current :=
  (openCheckpointIncrementalEvents track current valid squarefree degreeNonzero
    zeroNonzero elimination).resolveClear track strictRefine clearOwnerLabel

/-- A completed parser sector cannot retain the positive guard produced by
the executable family traversal: its relevant event would have to be owned by
one of the two incremental children, contradicting the computed all-`neither`
certificate. -/
def CheckpointIncrementalClearOpening.resolveCompletedSector
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR)}
    (valid : ControllerCanonicalOnInputEvents current.core.numerical
      current.core.word)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second)) :
    CheckpointIncrementalClearOpening p R hR current →
      CCLMetricTrack.StepResult (checkpointMetricState current)
  | .ready result => result
  | .positiveGuard separation _globalNone guardNone _noIdenticallyZero _arcs
      _evidence _alignment terminal output sourceCell member _clearedNonzero
      _countPositive event eventMember =>
      (incrementalAllNeither_excludes_completedSector_guard_cellControllerData
        current.core.numerical current.core.word valid separation guardNone
          sourceCell member event eventMember squarefree degreeNonzero
            elimination terminal output.state output.refines kind exponent
              first second phase).elim

/-- Complete one checkpoint controller call at a fully parsed sector.  Every
finite event and clearance branch now returns a metric successor or an exact
terminal root. -/
def openCheckpointCompletedIncrementalStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (clearOwnerLabel : Bool)
    (valid : ControllerCanonicalOnInputEvents current.core.numerical
      current.core.word)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second)) :
    CCLMetricTrack.StepResult (checkpointMetricState current) :=
  (openCheckpointIncrementalClearStep track strictRefine current
    clearOwnerLabel valid squarefree degreeNonzero zeroNonzero
      elimination).resolveCompletedSector valid squarefree degreeNonzero
        elimination phase

/-- A whole-box checkpoint with the separate algebraic support certificate
needed at completed sectors.  Universal rational wrapping and canonical event
support remain distinct fields. -/
structure CanonicalCheckpoint
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R) where
  state : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR)
  canonical : CompletedSectorControllerCanonicalData state.core.numerical
    state.core.word

/-- Initial supported checkpoint: the empty word wraps every rational point,
and its parser phase is not completed. -/
def CanonicalCheckpoint.ofWindingOne
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (initial : WindingOneState p (RatBox.symmetric R hR)) :
    CanonicalCheckpoint p R hR := by
  let core := CCLDirectTrack.State.ofWindingOne initial
  let wraps : CCLBoxCylinderCheckpoint.Wraps core.word core.numerical.box := by
    intro point _inside
    refine ⟨point, ?_⟩
    simpa only [core, CCLDirectTrack.State.ofWindingOne, RawParser.parse,
      List.foldl_nil] using RawParserSemantics.initialState_represents point
  let state := CCLBoxCylinderCheckpoint.State.ofDirect core wraps
  exact
    { state := state
      canonical := by
        intro completed
        rcases completed with ⟨kind, exponent, first, second, phase⟩
        simp [state, core, CCLBoxCylinderCheckpoint.State.ofDirect,
          CCLDirectTrack.State.ofWindingOne, RawParser.parse,
          RawParser.initialState] at phase }

/-- Keep an all-clear strict-cell successor in the repeatable checkpoint
pipeline.  Unlike a positive algebraic-event successor, this branch retains
whole-box wrapping; the lookahead strict signs now also provide the target
completed-sector support certificate. -/
def CanonicalCheckpoint.nextOfPlannedBit
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CanonicalCheckpoint p R hR)
    (planned : CCLDirectTrack.PlannedBit current.state.core)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CanonicalCheckpoint p R hR := by
  let core : CCLDirectTrack.State p (RatBox.symmetric R hR) :=
    { numerical := planned.numerical
      word := current.state.core.word ++ [planned.decision.bit] }
  let wraps : CCLBoxCylinderCheckpoint.Wraps core.word core.numerical.box := by
    change CCLBoxCylinderCheckpoint.Wraps
      (current.state.core.word ++ [planned.decision.bit])
        planned.numerical.box
    exact current.state.wraps_append_of_plannedBit planned
  let state := CCLBoxCylinderCheckpoint.State.next current.state
    planned.decision.bit core (by rfl) wraps
  exact
    { state := state
      canonical := by
        simpa only [state, core, CCLBoxCylinderCheckpoint.State.next] using
          plannedBit_completedSectorControllerCanonicalData planned squarefree
            degreeNonzero elimination }

theorem CanonicalCheckpoint.nextOfPlannedBit_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CanonicalCheckpoint p R hR)
    (planned : CCLDirectTrack.PlannedBit current.state.core)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (current.nextOfPlannedBit planned squarefree degreeNonzero
      elimination).state.Refines current.state := by
  apply CCLBoxCylinderCheckpoint.State.next_refines current.state
    planned.decision.bit
    { numerical := planned.numerical
      word := current.state.core.word ++ [planned.decision.bit] }
      planned.refines (by rfl)
  exact current.state.wraps_append_of_plannedBit planned

/-- One complete-table checkpoint call either enters the persistent metric
pipeline, remains a universally wrapped canonical checkpoint after an
all-clear bit, or switches a positive boundary track to same-word constrained
persistence. -/
inductive CanonicalCheckpointCompleteOpening
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (current : CanonicalCheckpoint p R hR) where
  | persistent (result : CCLMetricTrack.StepResult
      (checkpointMetricState current.state))
      (canonical : MetricStepControllerCanonical result)
  | checkpoint (next : CanonicalCheckpoint p R hR)
      (refines : next.state.Refines current.state)
  | constrainedBoundary
      (data : CheckpointPositiveGuardData p R hR current.state)
      (notCompleted : ¬∃ kind exponent first second,
        (RawParser.parse current.state.core.word).phase =
          .sector kind exponent (.two first second))
      (state : CCLMetricTrack.State p (RatBox.symmetric R hR))
      (refines : state.Refines (checkpointMetricState current.state))
      (word_eq : state.core.word = current.state.core.word)
      (step : CCLMetricTrack.StepResult state)

/-- Close one selected history-free owner.  Every parser position except the
second sector bit has a non-completed child and therefore enters the supported
metric pipeline immediately.  At the sole sector-completion position, the
already certified positive guard supplies an honest constrained-path step;
no unsupported historical-current claim is introduced. -/
def CheckpointPositiveGuardData.toSelectedIncrementalContinuation
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CanonicalCheckpoint p R hR}
    (data : CheckpointPositiveGuardData p R hR current.state)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.state.core.word).phase =
        .sector kind exponent (.two first second))
    (selected : CCLIncrementalEventOwner.SelectedPayload data.separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CanonicalCheckpointCompleteOpening p R hR current := by
  let result := metricStepOfCheckpointIncrementalGridOwner current.state
    data.separation selected notCompleted squarefree degreeNonzero zeroNonzero
      elimination
  match phaseEq : (RawParser.parse current.state.core.word).phase with
  | .initial =>
      exact .persistent result
        (metricStepOfCheckpointIncrementalGridOwner_canonical_of_append_not_completed
          current.state data.separation selected notCompleted squarefree
            degreeNonzero zeroNonzero elimination (by
              rw [rawParser_parse_append_singleton]
              cases selectedBit : selected.bit <;>
                simp [RawParser.step, phaseEq]))
  | .highUnary count =>
      exact .persistent result
        (metricStepOfCheckpointIncrementalGridOwner_canonical_of_append_not_completed
          current.state data.separation selected notCompleted squarefree
            degreeNonzero zeroNonzero elimination (by
              rw [rawParser_parse_append_singleton]
              cases selectedBit : selected.bit <;>
                simp [RawParser.step, phaseEq]))
  | .lowUnary count =>
      exact .persistent result
        (metricStepOfCheckpointIncrementalGridOwner_canonical_of_append_not_completed
          current.state data.separation selected notCompleted squarefree
            degreeNonzero zeroNonzero elimination (by
              rw [rawParser_parse_append_singleton]
              cases selectedBit : selected.bit <;>
                simp [RawParser.step, phaseEq]))
  | .loopUnary count =>
      exact .persistent result
        (metricStepOfCheckpointIncrementalGridOwner_canonical_of_append_not_completed
          current.state data.separation selected notCompleted squarefree
            degreeNonzero zeroNonzero elimination (by
              rw [rawParser_parse_append_singleton]
              cases selectedBit : selected.bit <;>
                simp [RawParser.step, phaseEq]))
  | .sector kind exponent .zero =>
      exact .persistent result
        (metricStepOfCheckpointIncrementalGridOwner_canonical_of_append_not_completed
          current.state data.separation selected notCompleted squarefree
            degreeNonzero zeroNonzero elimination (by
              rw [rawParser_parse_append_singleton]
              cases selectedBit : selected.bit <;>
                simp [RawParser.step, phaseEq]))
  | .sector kind exponent (.one first) =>
      exact .constrainedBoundary data notCompleted
        (checkpointBoundaryMetricState data squarefree degreeNonzero
          zeroNonzero elimination)
        (checkpointBoundaryMetricState_refines data squarefree degreeNonzero
          zeroNonzero elimination)
        (checkpointBoundaryMetricState_word data squarefree degreeNonzero
          zeroNonzero elimination)
        (checkpointBoundaryMetricStep data squarefree degreeNonzero
          zeroNonzero elimination)
  | .sector kind exponent (.two first second) =>
      exact (notCompleted ⟨kind, exponent, first, second, phaseEq⟩).elim

/-- Execute the history-free event table once the parser phase has been
constructively shown not to be a completed sector. -/
def CheckpointPositiveGuardData.toIncrementalContinuation
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CanonicalCheckpoint p R hR}
    (data : CheckpointPositiveGuardData p R hR current.state)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.state.core.word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CanonicalCheckpointCompleteOpening p R hR current :=
  match CCLIncrementalEventOwner.decideCombined
      (RawParser.parse current.state.core.word) data.separation with
  | .globalOwner selected =>
      data.toSelectedIncrementalContinuation notCompleted selected.toPayload
        squarefree degreeNonzero zeroNonzero elimination
  | .guardOwner selected =>
      data.toSelectedIncrementalContinuation notCompleted selected.toPayload
        squarefree degreeNonzero zeroNonzero elimination
  | .allNeither _globalNone _guardNone =>
      .constrainedBoundary data notCompleted
        (checkpointBoundaryMetricState data squarefree degreeNonzero
          zeroNonzero elimination)
        (checkpointBoundaryMetricState_refines data squarefree degreeNonzero
          zeroNonzero elimination)
        (checkpointBoundaryMetricState_word data squarefree degreeNonzero
          zeroNonzero elimination)
        (checkpointBoundaryMetricStep data squarefree degreeNonzero
          zeroNonzero elimination)

/-- Promote the complete-table result to the supported checkpoint/persistent
split.  Exhaustiveness ensures the residual wrapper contains a positive guard:
the ready and planned constructors have already been consumed. -/
def CheckpointCompleteClearOpening.toCanonicalContinuation
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CanonicalCheckpoint p R hR)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CheckpointCompleteClearOpening p R hR current.state →
      CanonicalCheckpointCompleteOpening p R hR current
  | .ready result canonical => .persistent result canonical
  | .planned plan =>
      .checkpoint
        (current.nextOfPlannedBit plan squarefree degreeNonzero elimination)
        (current.nextOfPlannedBit_refines plan squarefree degreeNonzero
          elimination)
  | .positiveGuard data => by
      match phaseEq : (RawParser.parse current.state.core.word).phase with
      | .initial =>
          exact data.toIncrementalContinuation (by simp [phaseEq]) squarefree
            degreeNonzero zeroNonzero elimination
      | .highUnary count =>
          exact data.toIncrementalContinuation (by simp [phaseEq]) squarefree
            degreeNonzero zeroNonzero elimination
      | .lowUnary count =>
          exact data.toIncrementalContinuation (by simp [phaseEq]) squarefree
            degreeNonzero zeroNonzero elimination
      | .loopUnary count =>
          exact data.toIncrementalContinuation (by simp [phaseEq]) squarefree
            degreeNonzero zeroNonzero elimination
      | .sector kind exponent .zero =>
          exact data.toIncrementalContinuation (by simp [phaseEq]) squarefree
            degreeNonzero zeroNonzero elimination
      | .sector kind exponent (.one first) =>
          exact data.toIncrementalContinuation (by simp [phaseEq]) squarefree
            degreeNonzero zeroNonzero elimination
      | .sector kind exponent (.two first second) =>
        exact (allNeither_excludes_completedSector_guard_cellControllerData
          current.state.core.numerical current.state.core.word
          (current.canonical ⟨kind, exponent, first, second, phaseEq⟩)
          data.separation data.guardNone data.sourceCell data.member data.event
          data.eventMember squarefree degreeNonzero elimination data.terminal
          data.output.state data.output.refines kind exponent first second
          phaseEq).elim

/-- Repeatable supported checkpoint front end for phases where no current
canonical event premise is available.  An all-clear decision stays in this
front end; a positive algebraic owner switches to the persistent metric
pipeline.  A positive terminal guard is now split by the history-free table,
so the remaining alternatives state exactly whether its new predicate has an
owner or every incremental candidate is `neither`. -/
def openCanonicalCheckpointCompleteClearStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (current : CanonicalCheckpoint p R hR)
    (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CanonicalCheckpointCompleteOpening p R hR current :=
  CheckpointCompleteClearOpening.toCanonicalContinuation current squarefree
    degreeNonzero zeroNonzero elimination
      (openCheckpointCompleteClearStep track strictRefine current.state
        clearOwnerLabel squarefree degreeNonzero zeroNonzero elimination)

/-- Independent fixed-word box refinement preserves both universal wrapping
and the phase-indexed algebraic support certificate. -/
def CanonicalCheckpoint.refineBox
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CanonicalCheckpoint p R hR)
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (refines : numerical.box.Refines current.state.core.numerical.box) :
    CanonicalCheckpoint p R hR where
  state := current.state.refineBox numerical refines
  canonical := by
    intro completed
    apply ControllerCanonicalOnInputEvents.refine (current.canonical completed)
      refines

theorem CanonicalCheckpoint.refineBox_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CanonicalCheckpoint p R hR)
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (refines : numerical.box.Refines current.state.core.numerical.box) :
    (current.refineBox numerical refines).state.Refines current.state :=
  CCLBoxCylinderCheckpoint.State.refineBox_refines current.state numerical
    refines

/-- Same-state cylinder replacement is orthogonal to algebraic support. -/
def CanonicalCheckpoint.replaceCylinder
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CanonicalCheckpoint p R hR)
    (cylinder : RawCylinderEnvelope)
    (word : cylinder.truncation.word = current.state.core.word) :
    CanonicalCheckpoint p R hR where
  state := current.state.replaceCylinder cylinder word
  canonical := current.canonical

/-- Checkpoint specialization of the persistence-independent completed metric
result.  Whole-box wrapping is needed by this controller front end, but not by
the contraction theorem itself. -/
abbrev CompletedCheckpointMetricStepResult
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR)) :=
  CompletedMetricStepResult (checkpointMetricState current)

/-- Tighten an ordinary metric step taken from a completed sector with the
new completed-block envelope. -/
def tightenCompletedCheckpoint
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR)}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second)) :
    CCLMetricTrack.StepResult (checkpointMetricState current) →
      CompletedCheckpointMetricStepResult current :=
  tightenCompletedStep phase

/-- Completed-sector checkpoint step with the cylinder contraction installed
in the same finite operation. -/
def openCheckpointCompletedContractingStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (clearOwnerLabel : Bool)
    (valid : ControllerCanonicalOnInputEvents current.core.numerical
      current.core.word)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second)) :
    CompletedCheckpointMetricStepResult current :=
  tightenCompletedCheckpoint phase
    (openCheckpointCompletedIncrementalStep track strictRefine current
      clearOwnerLabel valid squarefree degreeNonzero zeroNonzero elimination
        phase)

/-- Supported-state wrapper: the completed-phase premise extracts precisely
the full canonical event fact needed by the controller, while the successor
result carries the phase-indexed support invariant forward. -/
def openCanonicalCheckpointCompletedContractingStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (current : CanonicalCheckpoint p R hR)
    (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.state.core.word).phase =
      .sector kind exponent (.two first second)) :
    CompletedCheckpointMetricStepResult current.state :=
  openCheckpointCompletedContractingStep track strictRefine current.state
    clearOwnerLabel
    (current.canonical ⟨kind, exponent, first, second, phase⟩)
      squarefree degreeNonzero zeroNonzero elimination phase

def cappedCheckpointPersistentEventGridDataFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {searchDirection : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some searchDirection)
    (cap : (next : WindingOneState p (RatBox.symmetric R hR)) →
      next.box.Refines separation.state.box → ℚ)
    (capPositive : ∀ next nextRefines, 0 < cap next nextRefines)
    (capLeZeroResidual : ∀ next nextRefines,
      cap next nextRefines ≤ normSq (p.eval 0))
    (residualBudget : ∀ next nextRefines,
      selectedSlopeActiveCoefficientSum selected * cap next nextRefines <
        approximateBoundaryBudget
          (slopeCappedLocalizedClassifiedTangentDirection search squarefree next
            (cap next nextRefines) (capPositive next nextRefines))
          (checkpointEventPriorForms selected next.box)) :
    PersistentEventGridDataFamily current.asCoupled separation selected where
  data next nextRefines :=
    cappedCheckpointEventGridData current separation selected squarefree
      degreeNonzero elimination next nextRefines (cap next nextRefines)
        (capPositive next nextRefines) (capLeZeroResidual next nextRefines)
          search (residualBudget next nextRefines)
  basePriors := by
    intro next nextRefines
    rfl
  baseSameSigns := by
    simp [State.asCoupled]

def cappedCheckpointPersistentEventOwnerSamples
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLBoxCylinderCheckpoint.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {searchDirection : CCL.GaussianRat}
    (search : classifiedTangentDirection? selected = some searchDirection)
    (cap : (next : WindingOneState p (RatBox.symmetric R hR)) →
      next.box.Refines separation.state.box → ℚ)
    (capPositive : ∀ next nextRefines, 0 < cap next nextRefines)
    (capLeZeroResidual : ∀ next nextRefines,
      cap next nextRefines ≤ normSq (p.eval 0))
    (residualBudget : ∀ next nextRefines,
      selectedSlopeActiveCoefficientSum selected * cap next nextRefines <
        approximateBoundaryBudget
          (slopeCappedLocalizedClassifiedTangentDirection search squarefree next
            (cap next nextRefines) (capPositive next nextRefines))
          (checkpointEventPriorForms selected next.box)) :
    PersistentEventOwnerSamples current.asCoupled separation selected :=
  (cappedCheckpointPersistentEventGridDataFamily current separation selected
    squarefree degreeNonzero elimination search cap capPositive
      capLeZeroResidual residualBudget).ownerSamples

end CCLBoxCylinderIncrementalEventGrid
end FTA
