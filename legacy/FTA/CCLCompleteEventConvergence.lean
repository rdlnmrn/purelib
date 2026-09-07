import FTA.CCLCompleteEventTangentSigns
import FTA.CCLPositiveEventConvergence

/-!
# Localized complete-child event convergence

This module applies the generic event localization pipeline to the divisor
cell on which all active slopes of the complete selected child formula have
been classified.  A caller-selected rational cap simultaneously controls the
active residuals, preserves every complete strict atom, keeps the point in a
later winding box, and can exclude zero.
-/

namespace FTA
namespace CCLCompleteEventConvergence

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLClearanceExclusion
open FTA.CCLCompleteEventTangentSigns
open FTA.CCLCompleteOwnerShapes
open FTA.CCLEventExtraction
open FTA.CCLEventTangentSigns
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLGuardedEventGrid
open FTA.CCLHermitianBox
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLPathIntersection
open FTA.CCLPositiveEventGrid
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventApproximation
open FTA.CCLPositiveEventLocalization
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventTrack
open FTA.ConstructiveTrack
open FTA.GaussianPolynomialBounds
open FTA.LocalExtraction
open FTA.RationalPolynomialBounds
open FTA.RootCountDivisibility
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Rational point extracted from the complete slope-classified divisor cell
and localized against a later winding-one owner box. -/
def completeSlopeLocalizedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : QI :=
  localizedCellPoint output (selectedCompleteSlopeInputCell selected)
    squarefree next

def completeSlopeLocalizedEventApproximationWidth
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : ℚ :=
  eventSourceApproximationWidth (selectedCompleteSlopeInputCell selected)
    squarefree (localizedClearance output next)

theorem completeSlopeLocalizedEventApproximationWidth_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    0 < completeSlopeLocalizedEventApproximationWidth selected squarefree
      next :=
  eventSourceApproximationWidth_pos
    (selectedCompleteSlopeInputCell selected) squarefree
    (localizedClearance output next)

def completeSlopeLocalizedEventParameter
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : ℚ :=
  ((selectedCompleteSlopeInputCell selected).clearedApproximation
    (completeSlopeLocalizedEventApproximationWidth selected squarefree next)
    (completeSlopeLocalizedEventApproximationWidth_pos selected squarefree
      next)).refined.interval.lower

theorem completeSlopeLocalizedEventPoint_eq_pathValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    completeSlopeLocalizedEventPoint selected squarefree next =
      (selectedCompletePath selected).value
        (completeSlopeLocalizedEventParameter selected squarefree next) := by
  rfl

theorem completeSlopeLocalizedEventParameter_lower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    (selectedCompleteSlopeSigns selected).refined.interval.lower ≤
      completeSlopeLocalizedEventParameter selected squarefree next := by
  let cell := selectedCompleteSlopeInputCell selected
  let approximation := cell.clearedApproximation
    (completeSlopeLocalizedEventApproximationWidth selected squarefree next)
    (completeSlopeLocalizedEventApproximationWidth_pos selected squarefree
      next)
  exact (selectedCompleteSlopeInputSigns selected).refines.1.trans
    approximation.refines.1

theorem completeSlopeLocalizedEventParameter_upper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    completeSlopeLocalizedEventParameter selected squarefree next ≤
      (selectedCompleteSlopeSigns selected).refined.interval.upper := by
  let cell := selectedCompleteSlopeInputCell selected
  let approximation := cell.clearedApproximation
    (completeSlopeLocalizedEventApproximationWidth selected squarefree next)
    (completeSlopeLocalizedEventApproximationWidth_pos selected squarefree
      next)
  exact (approximation.refined.proper.le.trans approximation.refines.2).trans
    (selectedCompleteSlopeInputSigns selected).refines.2

/-- Every canonically strict complete-child form has one common explicit
absolute-value margin at every rational point of the final classified event
cell. -/
theorem selectedStrictFormMargin_le_completeSlopePathValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {t : ℚ}
    (completeLower :
      (selectedCompleteSlopeSigns selected).refined.interval.lower ≤ t)
    (completeUpper : t ≤
      (selectedCompleteSlopeSigns selected).refined.interval.upper)
    {form : HermitianForm}
    (member : form ∈ eventPayloadStrictPriorForms selected) :
    selectedStrictFormMargin selected.toIncrementalPayload ≤
      |form.eval ((selectedCompletePath selected).value t)| := by
  let path := selectedCompletePath selected
  let signs := selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent
  have lower : signs.refined.interval.lower ≤ t :=
    (selectedCompleteSlopeSigns_refines_inputCell selected).1.trans
      completeLower
  have upper : t ≤ signs.refined.interval.upper :=
    completeUpper.trans
      (selectedCompleteSlopeSigns_refines_inputCell selected).2
  have canonicalNonzero : canonicalEventValue
      selected.candidate.inputCell.branch.factor.input
      (clearedForm form path) signs.refined.interval.lower ≠ 0 := by
    simpa only [eventPayloadCanonicalValue, toIncrementalPayload_candidate,
      selectedCompletePath, path, signs] using
      strictPriorForms_value_ne
        (inputAdvanceFormula state selected.bit)
        (eventPayloadCanonicalValue selected.toIncrementalPayload) member
  have clearedLower :=
    ConditionRelations.strictMargin_le_abs_eval
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent signs
      (selectedCompleteStrictPolynomial_mem selected member)
      canonicalNonzero lower upper
  have denominatorLe := selectedEventDenominator_le
    selected.toIncrementalPayload lower upper
  have denominatorNonzero :=
    selected.candidate.inputCell.path_denominator_ne_on_cell lower upper
  have clearedIdentity : |(clearedForm form path).eval t| =
      |(denominatorNorm path).eval t| *
        |form.eval (path.value t)| := by
    rw [eval_clearedForm form path t denominatorNonzero, abs_mul]
  unfold selectedStrictFormMargin
  simp only [toIncrementalPayload_candidate]
  apply (div_le_iff₀
    (selectedEventDenominatorUpper_pos selected.toIncrementalPayload)).2
  calc
    ConditionRelations.strictMargin
        selected.candidate.inputCell.branch.relations
        selected.candidate.inputCell.parent signs ≤
      |(clearedForm form path).eval t| := clearedLower
    _ = |(denominatorNorm path).eval t| *
        |form.eval (path.value t)| := clearedIdentity
    _ ≤ selectedEventDenominatorUpper selected.toIncrementalPayload *
        |form.eval (path.value t)| :=
      mul_le_mul_of_nonneg_right denominatorLe (abs_nonneg _)
    _ = |form.eval (path.value t)| *
        selectedEventDenominatorUpper selected.toIncrementalPayload := by ring

theorem selectedStrictFormMargin_le_completeSlopeLocalizedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) {form : HermitianForm}
    (member : form ∈ eventPayloadStrictPriorForms selected) :
    selectedStrictFormMargin selected.toIncrementalPayload ≤
      |form.eval
        (completeSlopeLocalizedEventPoint selected squarefree next)| := by
  rw [completeSlopeLocalizedEventPoint_eq_pathValue]
  exact selectedStrictFormMargin_le_completeSlopePathValue selected
    (completeSlopeLocalizedEventParameter_lower selected squarefree next)
    (completeSlopeLocalizedEventParameter_upper selected squarefree next)
    member

theorem completeSlopeLocalizedEventPoint_strictContains
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    next.box.StrictContains
      (completeSlopeLocalizedEventPoint selected squarefree next) :=
  localizedCellPoint_strictContains output
    (selectedCompleteSlopeInputCell selected) squarefree degreeNonzero
    elimination next nextRefines

/-- A successful complete algebraic table entry is a genuine tangent vector
at the localized rational point. -/
def completeSlopeLocalizedClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : classifiedCompleteTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    TangentDirection (eventPayloadActiveOwnerForms selected)
      (completeSlopeLocalizedEventPoint selected squarefree next) :=
  completeClassifiedTangentDirectionAt search
    (completeSlopeLocalizedEventParameter selected squarefree next)
    (completeSlopeLocalizedEventParameter_lower selected squarefree next)
    (completeSlopeLocalizedEventParameter_upper selected squarefree next)

/-- Shrink only the stored clearance certificate of the later owner state. -/
def completeSlopeCappedLocalizedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) : QI :=
  completeSlopeLocalizedEventPoint selected squarefree
    (cappedClearanceState next cap capPositive)

theorem completeSlopeCappedLocalizedEventPoint_strictContains
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap) :
    next.box.StrictContains
      (completeSlopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive) := by
  let capped := cappedClearanceState next cap capPositive
  have cappedRefines : capped.box.Refines output.state.box := by
    simpa only [capped, cappedClearanceState_box] using nextRefines
  simpa only [completeSlopeCappedLocalizedEventPoint, capped,
    cappedClearanceState_box] using
      completeSlopeLocalizedEventPoint_strictContains output selected
        squarefree degreeNonzero elimination capped cappedRefines

def completeSlopeCappedLocalizedClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : classifiedCompleteTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    TangentDirection (eventPayloadActiveOwnerForms selected)
      (completeSlopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive) :=
  completeSlopeLocalizedClassifiedTangentDirection search squarefree
    (cappedClearanceState next cap capPositive)

/-- The complete classified cell supplies one cap-independent lower bound for
every active entry radius at every capped localized point. -/
theorem selectedCompleteBoundaryRadiusLower_le_cappedEntryRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : classifiedCompleteTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap)
    {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    selectedCompleteBoundaryRadiusLower selected ≤
      entryRadius form
        (completeSlopeCappedLocalizedEventPoint selected squarefree next cap
          capPositive)
        (completeSlopeCappedLocalizedClassifiedTangentDirection search
          squarefree next cap capPositive).vector := by
  let capped := cappedClearanceState next cap capPositive
  have lower := completeSlopeLocalizedEventParameter_lower selected squarefree
    capped
  have upper := completeSlopeLocalizedEventParameter_upper selected squarefree
    capped
  have bound := selectedCompleteBoundaryRadiusLower_le_entryRadius search
    lower upper member
  simpa [completeSlopeCappedLocalizedEventPoint,
    completeSlopeLocalizedEventPoint_eq_pathValue,
    completeSlopeCappedLocalizedClassifiedTangentDirection,
    completeSlopeLocalizedClassifiedTangentDirection,
    completeClassifiedTangentDirectionAt, capped] using bound

/-- Linear residual coefficient for one complete-child active face. -/
def selectedCompleteSlopeActiveEventCoefficient
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (form : HermitianForm) : ℚ :=
  approximationCoefficient (clearedForm form (selectedCompletePath selected))
      (selectedCompleteSlopeClassification selected).branch.factor.polynomial
      (selectedCompleteSlopeInputSigns selected).refined *
    (32 * denseLipschitzBound p (nearbyAmbient output.state.box)) /
      (RelevantCurveEvent.ownerDenominatorCertificate
        selected.candidate.sourceEvent.event).bound

theorem selectedCompleteSlopeActiveEventCoefficient_nonneg
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (form : HermitianForm) :
    0 ≤ selectedCompleteSlopeActiveEventCoefficient selected form := by
  apply div_nonneg
  · exact mul_nonneg (approximationCoefficient_nonneg _ _ _)
      (mul_nonneg (by norm_num)
        (denseLipschitzBound_pos p
          (nearbyAmbient output.state.box)).le)
  · exact (RelevantCurveEvent.ownerDenominatorCertificate
      selected.candidate.sourceEvent.event).positive.le

theorem selectedCompleteSlopeEventSourceActive_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p output.state.box)
    (radius : ℚ)
    (clearanceLe : clearance.bound ≤
      512 * denseLipschitzBound p (nearbyAmbient output.state.box) * radius)
    {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    |form.eval (eventSourcePoint (selectedCompleteSlopeInputCell selected)
        squarefree clearance)| ≤
      selectedCompleteSlopeActiveEventCoefficient selected form * radius := by
  let cell := selectedCompleteSlopeInputCell selected
  let width := eventSourceApproximationWidth cell squarefree clearance
  let coefficient := approximationCoefficient
    (clearedForm form (selectedCompletePath selected))
    (selectedCompleteSlopeClassification selected).branch.factor.polynomial
    (selectedCompleteSlopeInputSigns selected).refined
  let cap := 32 * denseLipschitzBound p
    (nearbyAmbient output.state.box) * radius
  let denominator := RelevantCurveEvent.ownerDenominatorCertificate
    selected.candidate.sourceEvent.event
  have raw : |form.eval (eventSourcePoint cell squarefree clearance)| ≤
      coefficient * width / denominator.bound := by
    have bounded :=
      selectedCompleteActiveAtCompleteSlopeInputCellApproximation_le selected
        (eventSourceApproximationWidth_pos cell squarefree clearance) member
    rw [approximationBound_eq_coefficient_mul] at bounded
    simpa only [eventSourcePoint, cell, width, coefficient, denominator,
      selectedPath] using bounded
  have widthLe : width ≤ cap := by
    simpa only [width, cell, cap] using
      eventSourceApproximationWidth_le_of_clearance_bound cell squarefree
        clearance radius clearanceLe
  have numeratorLe : coefficient * width ≤ coefficient * cap :=
    mul_le_mul_of_nonneg_left widthLe
      (approximationCoefficient_nonneg _ _ _)
  calc
    |form.eval (eventSourcePoint cell squarefree clearance)| ≤
        coefficient * width / denominator.bound := raw
    _ ≤ coefficient * cap / denominator.bound :=
      div_le_div_of_nonneg_right numeratorLe denominator.positive.le
    _ = selectedCompleteSlopeActiveEventCoefficient selected form * radius := by
      dsimp only [selectedCompleteSlopeActiveEventCoefficient, coefficient,
        cap, denominator]
      ring

theorem completeSlopeCappedLocalizedEventActive_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap)
    {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    |form.eval (completeSlopeCappedLocalizedEventPoint selected squarefree
        next cap capPositive)| ≤
      selectedCompleteSlopeActiveEventCoefficient selected form * cap := by
  let capped := cappedClearanceState next cap capPositive
  change |form.eval (eventSourcePoint
      (selectedCompleteSlopeInputCell selected) squarefree
      (localizedClearance output capped))| ≤
    selectedCompleteSlopeActiveEventCoefficient selected form * cap
  exact selectedCompleteSlopeEventSourceActive_le selected squarefree
    (localizedClearance output capped) cap
    (localizedClearance_cappedState_le output next cap capPositive) member

theorem completeSlopeCappedLocalizedEventStrict
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    ∀ form ∈ eventPayloadStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected.toIncrementalPayload form *
        form.eval (completeSlopeCappedLocalizedEventPoint selected squarefree
          next cap capPositive) := by
  intro form member
  let capped := cappedClearanceState next cap capPositive
  let clearance := localizedClearance output capped
  have strict :=
    selectedCompleteStrictAtCompleteSlopeInputCellApproximation selected
      (eventSourceApproximationWidth
        (selectedCompleteSlopeInputCell selected) squarefree clearance)
      (eventSourceApproximationWidth_pos
        (selectedCompleteSlopeInputCell selected) squarefree clearance)
      form member
  simpa only [completeSlopeCappedLocalizedEventPoint,
    completeSlopeLocalizedEventPoint, localizedCellPoint, eventSourcePoint,
    selectedPath, capped, clearance] using strict

/-- The same cap used for active-face approximation bounds the polynomial
residual at the capped complete-event point. -/
theorem completeSlopeCappedLocalizedEventPoint_residual_lt_cap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    normSq (p.eval
      (completeSlopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive)) < cap / 8 := by
  let capped := cappedClearanceState next cap capPositive
  have residual := localizedCellPoint_residual_lt output
    (selectedCompleteSlopeInputCell selected) squarefree capped
  have clearanceLe : capped.clearance.bound / 8 ≤ cap / 8 := by
    gcongr
    simpa only [capped] using
      cappedClearanceState_clearance_le next cap capPositive
  simpa only [completeSlopeCappedLocalizedEventPoint,
    completeSlopeLocalizedEventPoint, capped] using
      residual.trans_le clearanceLe

/-- Capping the auxiliary localization clearance never consumes the original
later box's one-sixteenth residual budget. -/
theorem completeSlopeCappedLocalizedEventPoint_residual_le_originalClearance
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    normSq (p.eval
      (completeSlopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive)) ≤ next.clearance.bound / 16 := by
  let capped := cappedClearanceState next cap capPositive
  let clearance := localizedClearance output capped
  have residual := eventSourcePoint_residual
    (selectedCompleteSlopeInputCell selected) squarefree clearance
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
  change normSq (p.eval (eventSourcePoint
    (selectedCompleteSlopeInputCell selected) squarefree clearance)) ≤ _
  calc
    normSq (p.eval (eventSourcePoint
        (selectedCompleteSlopeInputCell selected) squarefree clearance)) ≤
      eventSourceResidualThreshold squarefree clearance := residual
    _ ≤ clearance.bound / 16 := thresholdLe
    _ ≤ capped.clearance.bound / 16 := by gcongr
    _ ≤ next.clearance.bound / 16 := by gcongr

/-- Every capped complete-event point retains a fixed interior gap determined
only by the original later box and its boundary-clearance certificate. -/
theorem completeSlopeCappedLocalizedEventPoint_deepInside
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap) :
    let point := completeSlopeCappedLocalizedEventPoint selected squarefree
      next cap capPositive
    let radius := boundaryInteriorRadius p next.box next.clearance
    next.box.xLower + 4 * radius < point.re ∧
      point.re < next.box.xUpper - 4 * radius ∧
      next.box.yLower + 4 * radius < point.im ∧
      point.im < next.box.yUpper - 4 * radius := by
  exact deepInside_of_small_residual next.clearance
    (completeSlopeCappedLocalizedEventPoint_strictContains output selected
      squarefree degreeNonzero elimination next nextRefines cap capPositive)
    (completeSlopeCappedLocalizedEventPoint_residual_le_originalClearance
      output selected squarefree next cap capPositive)

/-- Every inward form of the original later box has a cap-independent
absolute-value margin at the capped complete-event point. -/
theorem boundaryInteriorRadius_le_completeSlopeCappedBoxForm
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap)
    {form : HermitianForm} (member : form ∈ boxForms next.box) :
    boundaryInteriorRadius p next.box next.clearance ≤
      |form.eval (completeSlopeCappedLocalizedEventPoint selected squarefree
        next cap capPositive)| := by
  let point := completeSlopeCappedLocalizedEventPoint selected squarefree
    next cap capPositive
  let radius := boundaryInteriorRadius p next.box next.clearance
  have radiusPositive : 0 < radius :=
    boundaryInteriorRadius_pos p next.box next.clearance
  have deep := completeSlopeCappedLocalizedEventPoint_deepInside output
    selected squarefree degreeNonzero elimination next nextRefines cap
    capPositive
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

theorem completeSlopeCappedLocalizedEventPoint_ne_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLe : cap ≤ normSq (p.eval 0)) :
    completeSlopeCappedLocalizedEventPoint selected squarefree next cap
      capPositive ≠ 0 := by
  have residual := completeSlopeCappedLocalizedEventPoint_residual_lt_cap
    selected squarefree next cap capPositive
  have capDivLe : cap / 8 ≤ normSq (p.eval 0) :=
    (div_le_self capPositive.le (by norm_num : (1 : ℚ) ≤ 8)).trans capLe
  intro zero
  rw [zero] at residual
  exact (not_lt_of_ge capDivLe) residual

/-- If zero is not a root, every sufficiently capped complete-event point is
uniformly separated from zero.  The lower bound is rational and independent
of the cap. -/
theorem completeSlopeCappedLocalizedEventPoint_normSq_lower
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLe : cap ≤ normSq (p.eval 0)) :
    normSq (p.eval 0) /
        (8 * denseLipschitzBound p (nearbyAmbient next.box)) ≤
      normSq (completeSlopeCappedLocalizedEventPoint selected squarefree next
        cap capPositive) := by
  let point := completeSlopeCappedLocalizedEventPoint selected squarefree next
    cap capPositive
  let L := denseLipschitzBound p (nearbyAmbient next.box)
  let zeroResidual := normSq (p.eval 0)
  have LPositive : 0 < L :=
    denseLipschitzBound_pos p (nearbyAmbient next.box)
  have zeroResidualPositive : 0 < zeroResidual := capPositive.trans_le capLe
  have strict := completeSlopeCappedLocalizedEventPoint_strictContains output
    selected squarefree degreeNonzero elimination next nextRefines cap
    capPositive
  have pointNearby : (nearbyAmbient next.box).Contains point :=
    nearbyAmbient_contains strict.contains
  have zeroNearby : (nearbyAmbient next.box).Contains (0 : QI) := by
    dsimp only [nearbyAmbient, RatBox.symmetric, RatBox.Contains, zero_re,
      zero_im]
    have radiusNonnegative := next.box.coordinateRadius_nonneg
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have residualCap :=
    completeSlopeCappedLocalizedEventPoint_residual_lt_cap selected squarefree
      next cap capPositive
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
          L * normSq (point + -(0 : QI)) := lipschitz
      _ = L * normSq point := by simp
      _ < L * (zeroResidual / (8 * L)) :=
        mul_lt_mul_of_pos_left pointSmall LPositive
      _ = zeroResidual / 8 := by
        field_simp
  have decomposition :
      -(p.eval point + -(p.eval 0)) + p.eval point = p.eval 0 := by
    ext <;> simp only [add_re, add_im, neg_re, neg_im] <;> ring
  have sumBound := normSq_add_le_two
    (-(p.eval point + -(p.eval 0))) (p.eval point)
  rw [decomposition, normSq_neg] at sumBound
  nlinarith

/-! ## Complete-event convergence at the represented grid base -/

/-- Use the same requested-width inner winding box for the represented sample
and a complete-slope event point whose auxiliary clearance is capped by that
width. -/
def completeConvergentEventPoint
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (radius : ℚ) (radiusPositive : 0 < radius) : QI :=
  let inner := refineState squarefree elimination next radius radiusPositive
  completeSlopeCappedLocalizedEventPoint selected squarefree inner radius
    radiusPositive

theorem completeConvergentEventPoint_inside_inner
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (refineState squarefree elimination next radius radiusPositive).box.Contains
      (completeConvergentEventPoint current separation selected squarefree
        elimination next radius radiusPositive) := by
  let inner := refineState squarefree elimination next radius radiusPositive
  have innerRefines : inner.box.Refines separation.state.box :=
    (refineState_refines squarefree elimination next radius
      radiusPositive).trans nextRefines
  exact (completeSlopeCappedLocalizedEventPoint_strictContains separation
    selected squarefree degreeNonzero elimination inner innerRefines radius
    radiusPositive).contains

/-- Sharing one inner box improves the earlier maximality estimate from ten
requested radii to two. -/
theorem completeConvergentGridBase_event_distance
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    let eventPoint := completeConvergentEventPoint current separation selected
      squarefree elimination next radius radiusPositive
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| ≤
      2 * radius := by
  let inner := refineState squarefree elimination next radius radiusPositive
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventPoint := completeConvergentEventPoint current separation selected
    squarefree elimination next radius radiusPositive
  have baseInside : inner.box.Contains base.point := by
    simpa only [inner, base] using convergentGridBase_inside_inner current
      separation squarefree elimination next nextRefines radius radiusPositive
  have eventInside : inner.box.Contains eventPoint := by
    simpa only [inner, eventPoint] using
      completeConvergentEventPoint_inside_inner current separation selected
        squarefree degreeNonzero elimination next nextRefines radius
        radiusPositive
  have realDistance : |base.point.re - eventPoint.re| ≤ inner.box.widthX := by
    rw [abs_le]
    dsimp only [RatBox.widthX]
    constructor <;> linarith [baseInside.1, baseInside.2.1,
      eventInside.1, eventInside.2.1]
  have imagDistance : |base.point.im - eventPoint.im| ≤ inner.box.widthY := by
    rw [abs_le]
    dsimp only [RatBox.widthY]
    constructor <;> linarith [baseInside.2.2.1, baseInside.2.2.2,
      eventInside.2.2.1, eventInside.2.2.2]
  have widthX : inner.box.widthX ≤ radius := by
    simpa only [inner] using refineState_widthX_le_request squarefree
      elimination next radius radiusPositive
  have widthY : inner.box.widthY ≤ radius := by
    simpa only [inner] using refineState_widthY_le_request squarefree
      elimination next radius radiusPositive
  dsimp only [base, eventPoint]
  linarith

/-- Linear coefficient transferring one complete active residual from the
capped event point to the represented grid base. -/
def selectedCompleteConvergentActiveCoefficient
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (form : HermitianForm) : ℚ :=
  selectedCompleteSlopeActiveEventCoefficient selected form +
    2 * variationMajorant form output.state.box

theorem selectedCompleteConvergentActiveCoefficient_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) (form : HermitianForm) :
    0 < selectedCompleteConvergentActiveCoefficient selected form := by
  exact add_pos_of_nonneg_of_pos
    (selectedCompleteSlopeActiveEventCoefficient_nonneg selected form)
    (mul_pos (by norm_num) (variationMajorant_pos form output.state.box))

theorem completeConvergentGridBase_active_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {form : HermitianForm} (member : form ∈ eventPayloadActiveOwnerForms selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    |form.eval base.point| ≤
      selectedCompleteConvergentActiveCoefficient selected form * radius := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventPoint := completeConvergentEventPoint current separation selected
    squarefree elimination next radius radiusPositive
  have baseInside : separation.state.box.Contains base.point :=
    nextRefines.contains base.strict.contains
  have eventInside : separation.state.box.Contains eventPoint := by
    apply nextRefines.contains
    apply (refineState_refines squarefree elimination next radius
      radiusPositive).contains
    exact completeConvergentEventPoint_inside_inner current separation selected
      squarefree degreeNonzero elimination next nextRefines radius radiusPositive
  have variation := abs_eval_sub_eval_le form baseInside eventInside
  have distance := completeConvergentGridBase_event_distance current separation
    selected squarefree degreeNonzero elimination next nextRefines radius
    radiusPositive
  have variationLe : |form.eval base.point - form.eval eventPoint| ≤
      2 * variationMajorant form separation.state.box * radius := by
    apply variation.trans
    exact (mul_le_mul_of_nonneg_left distance
      (variationMajorant_pos form separation.state.box).le).trans_eq (by ring)
  have eventLe := completeSlopeCappedLocalizedEventActive_le selected squarefree
    (refineState squarefree elimination next radius radiusPositive) radius
    radiusPositive member
  have triangle := abs_add_le
    (form.eval base.point - form.eval eventPoint) (form.eval eventPoint)
  have identity : form.eval base.point - form.eval eventPoint +
      form.eval eventPoint = form.eval base.point := by ring
  rw [identity] at triangle
  exact triangle.trans (by
    calc
      |form.eval base.point - form.eval eventPoint| +
          |form.eval eventPoint| ≤
        2 * variationMajorant form separation.state.box * radius +
          selectedCompleteSlopeActiveEventCoefficient selected form * radius :=
        add_le_add variationLe (by
          simpa only [eventPoint, completeConvergentEventPoint] using eventLe)
      _ = selectedCompleteConvergentActiveCoefficient selected form * radius := by
        unfold selectedCompleteConvergentActiveCoefficient
        ring)

/-- One cap-independent request radius transfers every complete strict face
from the classified event point to the represented convergence base. -/
def selectedCompleteConvergentStrictRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  FTA.Maximality.positiveMinimum
    ((eventPayloadStrictPriorForms selected).map fun form =>
      selectedStrictFormMargin selected.toIncrementalPayload /
        (4 * variationMajorant form output.state.box))

theorem selectedCompleteConvergentStrictRadius_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < selectedCompleteConvergentStrictRadius selected := by
  apply FTA.Maximality.positiveMinimum_pos
  intro value member
  rw [List.mem_map] at member
  rcases member with ⟨form, _formMember, rfl⟩
  exact div_pos (selectedStrictFormMargin_pos selected.toIncrementalPayload)
    (mul_pos (by norm_num) (variationMajorant_pos form output.state.box))

theorem selectedCompleteConvergentStrictRadius_le_form
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadStrictPriorForms selected) :
    selectedCompleteConvergentStrictRadius selected ≤
      selectedStrictFormMargin selected.toIncrementalPayload /
        (4 * variationMajorant form output.state.box) := by
  apply FTA.Maximality.positiveMinimum_le_of_mem
  exact List.mem_map.mpr ⟨form, member, rfl⟩

theorem completeConvergentGridBase_strict
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < selectedCompleteConvergentStrictRadius selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    ∀ form ∈ eventPayloadStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected.toIncrementalPayload form * form.eval base.point := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventPoint := completeConvergentEventPoint current separation selected
    squarefree elimination next radius radiusPositive
  change ∀ form ∈ eventPayloadStrictPriorForms selected,
    0 < eventPayloadCanonicalValue selected.toIncrementalPayload form * form.eval base.point
  intro form member
  have radiusForm : radius < selectedStrictFormMargin selected.toIncrementalPayload /
      (4 * variationMajorant form separation.state.box) :=
    radiusSmall.trans_le
      (selectedCompleteConvergentStrictRadius_le_form selected member)
  have coefficientPositive :
      0 < 4 * variationMajorant form separation.state.box :=
    mul_pos (by norm_num) (variationMajorant_pos form separation.state.box)
  have variationSmall :
      2 * variationMajorant form separation.state.box * radius <
        selectedStrictFormMargin selected.toIncrementalPayload := by
    have scaled := (lt_div_iff₀ coefficientPositive).mp radiusForm
    nlinarith [radiusPositive]
  have baseInside : separation.state.box.Contains base.point :=
    nextRefines.contains base.strict.contains
  have eventInside : separation.state.box.Contains eventPoint := by
    apply nextRefines.contains
    apply (refineState_refines squarefree elimination next radius
      radiusPositive).contains
    exact completeConvergentEventPoint_inside_inner current separation selected
      squarefree degreeNonzero elimination next nextRefines radius radiusPositive
  have variation := abs_eval_sub_eval_le form baseInside eventInside
  have distance := completeConvergentGridBase_event_distance current separation
    selected squarefree degreeNonzero elimination next nextRefines radius
    radiusPositive
  have variationLe : |form.eval base.point - form.eval eventPoint| ≤
      2 * variationMajorant form separation.state.box * radius := by
    apply variation.trans
    exact (mul_le_mul_of_nonneg_left distance
      (variationMajorant_pos form separation.state.box).le).trans_eq (by ring)
  let inner := refineState squarefree elimination next radius radiusPositive
  let capped := cappedClearanceState inner radius radiusPositive
  have eventMargin : selectedStrictFormMargin selected.toIncrementalPayload ≤
      |form.eval eventPoint| := by
    have margin := selectedStrictFormMargin_le_completeSlopeLocalizedEventPoint
      selected squarefree capped member
    simpa only [eventPoint, completeConvergentEventPoint,
      completeSlopeCappedLocalizedEventPoint, inner, capped] using margin
  have close : |form.eval eventPoint - form.eval base.point| <
      |form.eval eventPoint| := by
    rw [abs_sub_comm]
    exact variationLe.trans_lt (variationSmall.trans_le eventMargin)
  have eventBase : 0 < form.eval eventPoint * form.eval base.point :=
    mul_pos_of_abs_sub_lt_abs_left close
  have canonicalEvent := completeSlopeCappedLocalizedEventStrict selected
    squarefree inner radius radiusPositive form member
  apply FTA.CCLPositiveEventGrid.mul_pos_trans
    (by simpa only [eventPoint, completeConvergentEventPoint, inner] using
      canonicalEvent)
    eventBase

/-- Uniform lower bound for the tangent-stability radius of the fixed
classified direction anywhere in the complete slope cell. -/
def selectedCompleteTangentStabilityLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  FTA.Maximality.positiveMinimum
    ((eventPayloadActiveOwnerForms selected).map fun form =>
      selectedCompleteSlopeDirectionalLower selected /
        (2 * FTA.CCLTangentStability.slopeVariationCoefficient form))

theorem selectedCompleteTangentStabilityLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < selectedCompleteTangentStabilityLower selected := by
  apply FTA.Maximality.positiveMinimum_pos
  intro value member
  rw [List.mem_map] at member
  rcases member with ⟨form, _formMember, rfl⟩
  exact div_pos (selectedCompleteSlopeDirectionalLower_pos selected)
    (mul_pos (by norm_num)
      (FTA.CCLTangentStability.slopeVariationCoefficient_pos form))

theorem selectedCompleteSlopeDirectionalLower_le_completeConvergentEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    {searchDirection : QI}
    (search : classifiedCompleteTangentDirection? selected =
      some searchDirection)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (radius : ℚ) (radiusPositive : 0 < radius)
    {form : HermitianForm} (member : form ∈ eventPayloadActiveOwnerForms selected) :
    selectedCompleteSlopeDirectionalLower selected ≤
      directionalSlope form
        (completeConvergentEventPoint current separation selected squarefree
          elimination next radius radiusPositive) searchDirection := by
  let inner := refineState squarefree elimination next radius radiusPositive
  let capped := cappedClearanceState inner radius radiusPositive
  have lower := completeSlopeLocalizedEventParameter_lower selected squarefree
    capped
  have upper := completeSlopeLocalizedEventParameter_upper selected squarefree
    capped
  have slope := selectedCompleteSlopeDirectionalLower_le search lower upper
    member
  simpa only [completeConvergentEventPoint,
    completeSlopeCappedLocalizedEventPoint,
    completeSlopeLocalizedEventPoint_eq_pathValue, inner, capped] using slope

theorem selectedCompleteTangentStabilityLower_le_completeConvergentDirection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    {searchDirection : QI}
    (search : classifiedCompleteTangentDirection? selected =
      some searchDirection)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (radius : ℚ) (radiusPositive : 0 < radius) :
    selectedCompleteTangentStabilityLower selected ≤
      FTA.CCLTangentStability.tangentStabilityRadius
        (completeSlopeCappedLocalizedClassifiedTangentDirection search
          squarefree
          (refineState squarefree elimination next radius radiusPositive)
          radius radiusPositive) := by
  let direction := completeSlopeCappedLocalizedClassifiedTangentDirection
    search squarefree
      (refineState squarefree elimination next radius radiusPositive)
      radius radiusPositive
  unfold selectedCompleteTangentStabilityLower
  unfold FTA.CCLTangentStability.tangentStabilityRadius
  apply FTA.Maximality.le_positiveMinimum
    (FTA.Maximality.positiveMinimum_le_one _)
  intro value valueMember
  rw [List.mem_map] at valueMember
  rcases valueMember with ⟨form, formMember, rfl⟩
  apply (FTA.Maximality.positiveMinimum_le_of_mem
    (List.mem_map.mpr ⟨form, formMember, rfl⟩)).trans
  apply div_le_div_of_nonneg_right
  · have slope :=
      selectedCompleteSlopeDirectionalLower_le_completeConvergentEvent
        current separation selected search squarefree elimination next radius
          radiusPositive formMember
    simpa only [direction,
      completeConvergentEventPoint,
      completeSlopeCappedLocalizedClassifiedTangentDirection,
      completeSlopeLocalizedClassifiedTangentDirection,
      completeClassifiedTangentDirectionAt] using slope
  · exact (mul_pos (by norm_num)
      (FTA.CCLTangentStability.slopeVariationCoefficient_pos form)).le

/-- The total complete classifier therefore supplies the executable tangent
certificate required by the represented-prefix grid whenever the request
radius is below one static rational cap. -/
def completeConvergentGridBaseTangentDirection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    {searchDirection : QI}
    (search : classifiedCompleteTangentDirection? selected =
      some searchDirection)
    (radiusLe : radius ≤
      selectedCompleteTangentStabilityLower selected / 4) :
    TangentDirection (eventPayloadIncrementalActiveOwnerForms selected.toIncrementalPayload)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point := by
  let inner := refineState squarefree elimination next radius radiusPositive
  let eventPoint := completeConvergentEventPoint current separation selected
    squarefree elimination next radius radiusPositive
  let eventDirection :=
    completeSlopeCappedLocalizedClassifiedTangentDirection search squarefree
      inner radius radiusPositive
  have stability :=
    selectedCompleteTangentStabilityLower_le_completeConvergentDirection
      current separation selected search squarefree elimination next radius
        radiusPositive
  have distance := completeConvergentGridBase_event_distance current separation
    selected squarefree degreeNonzero elimination next nextRefines radius
      radiusPositive
  have near : FTA.CCLTangentStability.coordinateDistance
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point eventPoint <
      FTA.CCLTangentStability.tangentStabilityRadius eventDirection := by
    unfold FTA.CCLTangentStability.coordinateDistance
    apply distance.trans_lt
    apply lt_of_lt_of_le _ stability
    have lowerPositive := selectedCompleteTangentStabilityLower_pos selected
    nlinarith
  let completeDirection :=
    FTA.CCLTangentStability.TangentDirection.atNearby eventDirection _ near
  exact
    { vector := completeDirection.vector
      normSqLeOne := completeDirection.normSqLeOne
      slopes := by
        intro form member
        apply completeDirection.slopes form
        rw [← eventPayloadIncrementalActiveOwnerForms_eq_active_of_completedSector
          selected phase]
        exact member }

theorem completeConvergentGridBaseTangentDirection_vector
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    {searchDirection : QI}
    (search : classifiedCompleteTangentDirection? selected =
      some searchDirection)
    (radiusLe : radius ≤
      selectedCompleteTangentStabilityLower selected / 4) :
    (completeConvergentGridBaseTangentDirection current separation selected
      squarefree degreeNonzero elimination next nextRefines radius
        radiusPositive phase search radiusLe).vector = searchDirection := by
  simp [completeConvergentGridBaseTangentDirection,
    FTA.CCLTangentStability.TangentDirection.atNearby,
    completeSlopeCappedLocalizedClassifiedTangentDirection,
    completeSlopeLocalizedClassifiedTangentDirection,
    completeClassifiedTangentDirectionAt]

theorem tangentDirectionCertificate?_isSome_at_completeConvergentGridBase
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    {searchDirection : QI}
    (search : classifiedCompleteTangentDirection? selected =
      some searchDirection)
    (radiusLe : radius ≤
      selectedCompleteTangentStabilityLower selected / 4) :
    (tangentDirectionCertificate?
      (eventPayloadActiveForms current selected.toIncrementalPayload
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point).isSome := by
  let direction := completeConvergentGridBaseTangentDirection current
    separation selected squarefree degreeNonzero elimination next nextRefines
      radius radiusPositive phase search radiusLe
  apply tangentDirectionCertificate?_isSome_of_mem
    (classifiedCompleteTangentDirection?_some_mem search)
  intro form member
  have slope := direction.slopes form member
  rw [completeConvergentGridBaseTangentDirection_vector current separation
    selected squarefree degreeNonzero elimination next nextRefines radius
      radiusPositive phase search radiusLe] at slope
  exact slope

/-- One positive coefficient dominates every complete active-face residual at
the represented convergence base. -/
def selectedCompleteConvergentActiveCoefficientSum
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  1 + ((eventPayloadActiveOwnerForms selected).map fun form =>
    selectedCompleteConvergentActiveCoefficient selected form).sum

theorem selectedCompleteConvergentActiveCoefficientSum_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < selectedCompleteConvergentActiveCoefficientSum selected := by
  have sumNonnegative : 0 ≤
      ((eventPayloadActiveOwnerForms selected).map fun form =>
        selectedCompleteConvergentActiveCoefficient selected form).sum := by
    apply List.sum_nonneg
    intro value valueMember
    rw [List.mem_map] at valueMember
    rcases valueMember with ⟨form, _formMember, rfl⟩
    exact (selectedCompleteConvergentActiveCoefficient_pos selected form).le
  unfold selectedCompleteConvergentActiveCoefficientSum
  linarith

theorem selectedCompleteConvergentActiveCoefficient_lt_sum
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadActiveOwnerForms selected) :
    selectedCompleteConvergentActiveCoefficient selected form <
      selectedCompleteConvergentActiveCoefficientSum selected := by
  have singleLe : selectedCompleteConvergentActiveCoefficient selected form ≤
      ((eventPayloadActiveOwnerForms selected).map fun item =>
        selectedCompleteConvergentActiveCoefficient selected item).sum := by
    apply List.single_le_sum
    · intro value valueMember
      rw [List.mem_map] at valueMember
      rcases valueMember with ⟨item, _itemMember, rfl⟩
      exact (selectedCompleteConvergentActiveCoefficient_pos selected item).le
    · exact List.mem_map.mpr ⟨form, member, rfl⟩
  unfold selectedCompleteConvergentActiveCoefficientSum
  linarith

theorem completeConvergentGridBase_active_lt_sum
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {form : HermitianForm} (member : form ∈ eventPayloadActiveOwnerForms selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    |form.eval base.point| <
      selectedCompleteConvergentActiveCoefficientSum selected * radius := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  have individual := completeConvergentGridBase_active_le current separation
    selected squarefree degreeNonzero elimination next nextRefines radius
      radiusPositive member
  have coefficient :=
    selectedCompleteConvergentActiveCoefficient_lt_sum selected member
  exact individual.trans_lt (mul_lt_mul_of_pos_right coefficient radiusPositive)

/-- Once the transferred tangent table has returned its concrete direction,
all strict and active complete-event checks are automatic.  Executable grid
success is reduced to the single displayed budget for the fixed historical
priors. -/
theorem completeConvergentGridData?_isSome
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < selectedCompleteConvergentStrictRadius selected)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    (direction : TangentDirection
      (eventPayloadActiveForms current selected.toIncrementalPayload
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point)
    (search : tangentDirectionCertificate?
      (eventPayloadActiveForms current selected.toIncrementalPayload
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point = some direction)
    (residualBudget : selectedCompleteConvergentActiveCoefficientSum selected *
        radius < approximateBoundaryBudget direction
      (eventPayloadPriorForms current selected.toIncrementalPayload
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).priors
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point next.box)) :
    (eventGridData? current separation selected next nextRefines
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive)).isSome := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  have strictAt :
      ∀ form ∈ eventPayloadIncrementalStrictPriorForms
        selected.toIncrementalPayload,
      0 < eventPayloadCanonicalValue selected.toIncrementalPayload form * form.eval base.point := by
    rw [eventPayloadIncrementalStrictPriorForms_eq_strict_of_completedSector
      selected phase]
    simpa only [base] using completeConvergentGridBase_strict current separation
      selected squarefree degreeNonzero elimination next nextRefines radius
        radiusPositive radiusSmall
  have residualAt :
      ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected.toIncrementalPayload,
      |form.eval base.point| < approximateBoundaryBudget direction
        (eventPayloadPriorForms current selected.toIncrementalPayload base.priors base.point
          next.box) := by
    intro form member
    have completeMember : form ∈ eventPayloadActiveOwnerForms selected := by
      rw [← eventPayloadIncrementalActiveOwnerForms_eq_active_of_completedSector
        selected phase]
      exact member
    exact (completeConvergentGridBase_active_lt_sum current separation selected
      squarefree degreeNonzero elimination next nextRefines radius radiusPositive
        completeMember).trans (by simpa only [base] using residualBudget)
  simp only [eventGridData?, search]
  rw [dif_pos (by simpa only [base] using strictAt)]
  rw [dif_pos (by simpa only [base] using residualAt)]
  rfl

/-- Static completed-sector request width which simultaneously transfers the
complete tangent certificate and every complete strict sign. -/
def completedConvergentRadiusCap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  min (selectedCompleteTangentStabilityLower selected / 4)
    (selectedCompleteConvergentStrictRadius selected / 2)

theorem completedConvergentRadiusCap_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < completedConvergentRadiusCap selected := by
  exact lt_min
    (div_pos (selectedCompleteTangentStabilityLower_pos selected) (by norm_num))
    (div_pos (selectedCompleteConvergentStrictRadius_pos selected) (by norm_num))

theorem completedConvergentRadiusCap_le_tangent
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    completedConvergentRadiusCap selected ≤
      selectedCompleteTangentStabilityLower selected / 4 :=
  min_le_left _ _

theorem completedConvergentRadiusCap_lt_strict
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    completedConvergentRadiusCap selected <
      selectedCompleteConvergentStrictRadius selected := by
  apply (min_le_right _ _).trans_lt
  have positive := selectedCompleteConvergentStrictRadius_pos selected
  linarith

/-- Actual proof-bearing direction returned by the executable base-point
table at the static completed-sector radius. -/
def completedConvergentGridDirection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second)) :
    TangentDirection
      (eventPayloadActiveForms current selected.toIncrementalPayload
        (convergentGridBase current separation squarefree elimination next
          nextRefines (completedConvergentRadiusCap selected)
            (completedConvergentRadiusCap_pos selected)).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines (completedConvergentRadiusCap selected)
          (completedConvergentRadiusCap_pos selected)).point := by
  let determinantNonzero :
      determinant (RawParser.parse current.word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  let historyValid := parse_historyMatricesInvertible current.word
  let searchDirection := completedPhaseClassifiedTangentDirection selected phase
    determinantNonzero historyValid
  let search := completedPhaseClassifiedTangentDirection_spec selected phase
    determinantNonzero historyValid
  let success := tangentDirectionCertificate?_isSome_at_completeConvergentGridBase
    current separation selected squarefree degreeNonzero elimination next
      nextRefines (completedConvergentRadiusCap selected)
        (completedConvergentRadiusCap_pos selected) phase search
          (completedConvergentRadiusCap_le_tangent selected)
  exact (tangentDirectionCertificate?
    (eventPayloadActiveForms current selected.toIncrementalPayload
      (convergentGridBase current separation squarefree elimination next
        nextRefines (completedConvergentRadiusCap selected)
          (completedConvergentRadiusCap_pos selected)).point)
    (convergentGridBase current separation squarefree elimination next
      nextRefines (completedConvergentRadiusCap selected)
        (completedConvergentRadiusCap_pos selected)).point).get success

theorem completedConvergentGridDirection_search
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second)) :
    tangentDirectionCertificate?
      (eventPayloadActiveForms current selected.toIncrementalPayload
        (convergentGridBase current separation squarefree elimination next
          nextRefines (completedConvergentRadiusCap selected)
            (completedConvergentRadiusCap_pos selected)).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines (completedConvergentRadiusCap selected)
          (completedConvergentRadiusCap_pos selected)).point =
      some (completedConvergentGridDirection current separation selected
        squarefree degreeNonzero elimination next nextRefines phase) := by
  unfold completedConvergentGridDirection
  exact (Option.some_get _).symm

/-- At the static completed-sector radius, the historical-prior boundary
budget is now literally the only possible failed test. -/
theorem completedConvergentGridData?_isSome_of_residualBudget
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    (residualBudget :
      let radius := completedConvergentRadiusCap selected
      let base := convergentGridBase current separation squarefree elimination
        next nextRefines radius (completedConvergentRadiusCap_pos selected)
      selectedCompleteConvergentActiveCoefficientSum selected * radius <
        approximateBoundaryBudget
          (completedConvergentGridDirection current separation selected
            squarefree degreeNonzero elimination next nextRefines phase)
          (eventPayloadPriorForms current selected.toIncrementalPayload base.priors base.point
            next.box)) :
    (eventGridData? current separation selected next nextRefines
      (convergentGridBase current separation squarefree elimination next
        nextRefines (completedConvergentRadiusCap selected)
          (completedConvergentRadiusCap_pos selected))).isSome := by
  apply completeConvergentGridData?_isSome current separation selected
    squarefree degreeNonzero elimination next nextRefines
      (completedConvergentRadiusCap selected)
        (completedConvergentRadiusCap_pos selected)
          (completedConvergentRadiusCap_lt_strict selected) phase
            (completedConvergentGridDirection current separation selected
              squarefree degreeNonzero elimination next nextRefines phase)
  · exact completedConvergentGridDirection_search current separation selected
      squarefree degreeNonzero elimination next nextRefines phase
  · simpa only using residualBudget

/-- A uniform proof of the sole historical-prior budget inequality closes the
entire per-refinement convergence family. -/
def completedConvergentGridSuccessFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    (residualBudget : ∀ next nextRefines,
      let radius := completedConvergentRadiusCap selected
      let base := convergentGridBase current separation squarefree elimination
        next nextRefines radius (completedConvergentRadiusCap_pos selected)
      selectedCompleteConvergentActiveCoefficientSum selected * radius <
        approximateBoundaryBudget
          (completedConvergentGridDirection current separation selected
            squarefree degreeNonzero elimination next nextRefines phase)
          (eventPayloadPriorForms current selected.toIncrementalPayload base.priors base.point
            next.box)) :
    ConvergentGridSuccessFamily current separation selected squarefree
      elimination where
  radius _next _nextRefines := completedConvergentRadiusCap selected
  radiusPositive _next _nextRefines :=
    completedConvergentRadiusCap_pos selected
  success next nextRefines :=
    completedConvergentGridData?_isSome_of_residualBudget current separation
      selected squarefree degreeNonzero elimination next nextRefines phase
        (residualBudget next nextRefines)

/-- Consequently the same single finite inequality supplies the fully
coherent persistent sampler consumed by the coupled controller. -/
def completedConvergentPersistentOwnerSamples
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    (residualBudget : ∀ next nextRefines,
      let radius := completedConvergentRadiusCap selected
      let base := convergentGridBase current separation squarefree elimination
        next nextRefines radius (completedConvergentRadiusCap_pos selected)
      selectedCompleteConvergentActiveCoefficientSum selected * radius <
        approximateBoundaryBudget
          (completedConvergentGridDirection current separation selected
            squarefree degreeNonzero elimination next nextRefines phase)
          (eventPayloadPriorForms current selected.toIncrementalPayload base.priors base.point
            next.box)) :
    CCLCoupledController.PersistentEventOwnerSamples current separation selected :=
  (completedConvergentGridSuccessFamily current separation selected squarefree
    degreeNonzero elimination phase residualBudget).ownerSamples

/-- Event-owner controller closure with no obligations left except the one
explicit historical-prior budget inequality. -/
def nextOfCompletedConvergentEventOwner
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    (residualBudget : ∀ next nextRefines,
      let radius := completedConvergentRadiusCap selected
      let base := convergentGridBase current separation squarefree elimination
        next nextRefines radius (completedConvergentRadiusCap_pos selected)
      selectedCompleteConvergentActiveCoefficientSum selected * radius <
        approximateBoundaryBudget
          (completedConvergentGridDirection current separation selected
            squarefree degreeNonzero elimination next nextRefines phase)
          (eventPayloadPriorForms current selected.toIncrementalPayload base.priors base.point
            next.box)) :
    CCLCoupledTrack.StepResult current :=
  CCLCoupledController.nextOfPersistentEventPayload current separation selected
    (completedConvergentPersistentOwnerSamples current separation selected
      squarefree degreeNonzero elimination phase residualBudget)

end CCLCompleteEventConvergence
end FTA
