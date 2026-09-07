import FTA.CCLCompleteEventConvergence
import FTA.CCLHistoricalOwnerGrid

/-!
# Localized convergence for complete historical owner grids

This module constructs the quantitative family required by
`CCLHistoricalOwnerGrid` directly at the final history-classified event cell.
Shrinking the later winding state's stored clearance leaves its box unchanged
while making every active historical residual linearly small.  Fixed lower
bounds from the original later box control all protected strict forms, so one
computed rational cap supplies a complete grid in every refinement.
-/

namespace FTA
namespace CCLHistoricalGridConvergence

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBoundaryPreservingOwner
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLClearanceExclusion
open FTA.CCLCompleteEventConvergence
open FTA.CCLCompleteEventTangentSigns
open FTA.CCLCoupledController
open FTA.CCLEventExtraction
open FTA.CCLEventTangentSigns
open FTA.CCLFormulaPath
open FTA.CCLGeometry
open FTA.CCLHistoricalEventOwner
open FTA.CCLHistoricalEventTangentSigns
open FTA.CCLHistoricalOwnerGrid
open FTA.CCLHermitianBox
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.CCLPathIntersection
open FTA.CCLPositiveEventApproximation
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventLocalization
open FTA.CCLPositiveEventTrack
open FTA.CCLTangentStability
open FTA.GaussianPolynomialBounds
open FTA.LocalExtraction
open FTA.RationalPolynomialBounds
open FTA.RootCountDivisibility
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Rational event point localized inside an arbitrary later winding box. -/
def historicalSlopeLocalizedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : QI :=
  localizedCellPoint output (historicalSlopeInputCell selected) squarefree next

def historicalSlopeLocalizedEventApproximationWidth
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : ℚ :=
  eventSourceApproximationWidth (historicalSlopeInputCell selected) squarefree
    (localizedClearance output next)

theorem historicalSlopeLocalizedEventApproximationWidth_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    0 < historicalSlopeLocalizedEventApproximationWidth selected squarefree
      next :=
  eventSourceApproximationWidth_pos (historicalSlopeInputCell selected)
    squarefree (localizedClearance output next)

def historicalSlopeLocalizedEventParameter
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : ℚ :=
  ((historicalSlopeInputCell selected).clearedApproximation
    (historicalSlopeLocalizedEventApproximationWidth selected squarefree next)
    (historicalSlopeLocalizedEventApproximationWidth_pos selected squarefree
      next)).refined.interval.lower

theorem historicalSlopeLocalizedEventPoint_eq_pathValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    historicalSlopeLocalizedEventPoint selected squarefree next =
      (selectedCompletePath selected).value
        (historicalSlopeLocalizedEventParameter selected squarefree next) := by
  rfl

theorem historicalSlopeLocalizedEventParameter_lower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    (historicalSlopeSigns selected).refined.interval.lower ≤
      historicalSlopeLocalizedEventParameter selected squarefree next := by
  let cell := historicalSlopeInputCell selected
  let approximation := cell.clearedApproximation
    (historicalSlopeLocalizedEventApproximationWidth selected squarefree next)
    (historicalSlopeLocalizedEventApproximationWidth_pos selected squarefree
      next)
  exact (cell.branch.computeEventSigns cell.parent).refines.1.trans
    approximation.refines.1

theorem historicalSlopeLocalizedEventParameter_upper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    historicalSlopeLocalizedEventParameter selected squarefree next ≤
      (historicalSlopeSigns selected).refined.interval.upper := by
  let cell := historicalSlopeInputCell selected
  let approximation := cell.clearedApproximation
    (historicalSlopeLocalizedEventApproximationWidth selected squarefree next)
    (historicalSlopeLocalizedEventApproximationWidth_pos selected squarefree
      next)
  exact (approximation.refined.proper.le.trans approximation.refines.2).trans
    (cell.branch.computeEventSigns cell.parent).refines.2

theorem historicalSlopeLocalizedEventPoint_strictContains
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
      (historicalSlopeLocalizedEventPoint selected squarefree next) :=
  localizedCellPoint_strictContains output (historicalSlopeInputCell selected)
    squarefree degreeNonzero elimination next nextRefines

/-- The classified historical vector is a genuine tangent at every localized
point of the final common-sign cell. -/
def historicalSlopeLocalizedClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    TangentDirection (historicalActiveOwnerForms selected)
      (historicalSlopeLocalizedEventPoint selected squarefree next) :=
  historicalClassifiedTangentDirectionAt search
    (historicalSlopeLocalizedEventParameter selected squarefree next)
    (historicalSlopeLocalizedEventParameter_lower selected squarefree next)
    (historicalSlopeLocalizedEventParameter_upper selected squarefree next)

/-- Localize after replacing only the later state's clearance certificate by
a smaller positive rational cap. -/
def historicalSlopeCappedLocalizedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) : QI :=
  historicalSlopeLocalizedEventPoint selected squarefree
    (cappedClearanceState next cap capPositive)

theorem historicalSlopeCappedLocalizedEventPoint_strictContains
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
      (historicalSlopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive) := by
  let capped := cappedClearanceState next cap capPositive
  have cappedRefines : capped.box.Refines output.state.box := by
    simpa only [capped, cappedClearanceState_box] using nextRefines
  simpa only [historicalSlopeCappedLocalizedEventPoint, capped,
    cappedClearanceState_box] using
      historicalSlopeLocalizedEventPoint_strictContains output selected
        squarefree degreeNonzero elimination capped cappedRefines

def historicalSlopeCappedLocalizedClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    TangentDirection (historicalActiveOwnerForms selected)
      (historicalSlopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive) :=
  historicalSlopeLocalizedClassifiedTangentDirection search squarefree
    (cappedClearanceState next cap capPositive)

/-- Generic linear residual estimate for a cleared form divisible by the
event factor at a source point whose retained clearance has the usual cap. -/
theorem eventSourceForm_le_of_dvd_of_clearance_bound
    {p : GaussianPolynomial} {path : FTA.ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State}
    {event : CCLBranchEvent.RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    (radius : ℚ)
    (clearanceLe : clearance.bound ≤
      512 * denseLipschitzBound p (nearbyAmbient box) * radius)
    (form : HermitianForm)
    (divides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form path).toPolynomial) :
    |form.eval (eventSourcePoint cell squarefree clearance)| ≤
      inputEventFormCoefficient cell form * radius := by
  let width := eventSourceApproximationWidth cell squarefree clearance
  let coefficient := approximationCoefficient (clearedForm form path)
    cell.branch.factor.polynomial
    (cell.branch.computeEventSigns cell.parent).refined
  let cap := 32 * denseLipschitzBound p (nearbyAmbient box) * radius
  let denominator :=
    CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate event
  have raw : |form.eval (eventSourcePoint cell squarefree clearance)| ≤
      coefficient * width / denominator.bound := by
    have bounded := inputEventFormAtApproximation_le_of_dvd cell
      (eventSourceApproximationWidth_pos cell squarefree clearance) form divides
    rw [approximationBound_eq_coefficient_mul] at bounded
    simpa only [eventSourcePoint, width, coefficient, denominator] using bounded
  have widthLe : width ≤ cap := by
    apply eventSourceApproximationWidth_le_of_clearance_bound cell squarefree
      clearance radius clearanceLe
  have numeratorLe : coefficient * width ≤ coefficient * cap :=
    mul_le_mul_of_nonneg_left widthLe
      (approximationCoefficient_nonneg _ _ _)
  calc
    |form.eval (eventSourcePoint cell squarefree clearance)| ≤
        coefficient * width / denominator.bound := raw
    _ ≤ coefficient * cap / denominator.bound :=
      div_le_div_of_nonneg_right numeratorLe denominator.positive.le
    _ = inputEventFormCoefficient cell form * radius := by
      dsimp only [inputEventFormCoefficient, coefficient, cap, denominator]
      ring

/-- Every complete historical active face is linearly small at the capped
localized point. -/
theorem historicalSlopeCappedLocalizedEventActive_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap)
    {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    |form.eval (historicalSlopeCappedLocalizedEventPoint selected squarefree
        next cap capPositive)| ≤
      inputEventFormCoefficient (historicalSlopeInputCell selected) form *
        cap := by
  let capped := cappedClearanceState next cap capPositive
  change |form.eval (eventSourcePoint (historicalSlopeInputCell selected)
      squarefree (localizedClearance output capped))| ≤ _
  apply eventSourceForm_le_of_dvd_of_clearance_bound
    (historicalSlopeInputCell selected) squarefree
    (localizedClearance output capped) cap
  · exact localizedClearance_cappedState_le output next cap capPositive
  · exact historicalSlopeActivePolynomial_dvd selected member

theorem historicalSlopeCappedLocalizedEventActive_lt_sum
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (cap : ℚ) (capPositive : 0 < cap)
    {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    |form.eval (historicalSlopeCappedLocalizedEventPoint selected squarefree
        next cap capPositive)| <
      historicalActiveCoefficientSum selected * cap := by
  have residual := historicalSlopeCappedLocalizedEventActive_le selected
    squarefree next cap capPositive member
  have inputLe :
      inputEventFormCoefficient (historicalSlopeInputCell selected) form ≤
        historicalActiveBaseCoefficient selected form := by
    unfold historicalActiveBaseCoefficient
    have positive := variationMajorant_pos form output.state.box
    linarith
  exact residual.trans
    (mul_le_mul_of_nonneg_right inputLe capPositive.le) |>.trans_lt
      (mul_lt_mul_of_pos_right
        (historicalActiveBaseCoefficient_lt_sum selected member) capPositive)

/-- Every canonically strict historical form keeps its selected sign at the
same capped localized point. -/
theorem historicalSlopeCappedLocalizedEventStrict
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    ∀ form ∈ historicalStrictPriorForms selected,
      0 < historicalCanonicalValue selected form *
        form.eval (historicalSlopeCappedLocalizedEventPoint selected
          squarefree next cap capPositive) := by
  intro form member
  let capped := cappedClearanceState next cap capPositive
  let parameter := historicalSlopeLocalizedEventParameter selected squarefree
    capped
  have sign := historicalStrictPriorForms_mul_eval_pos selected
    (historicalSlopeLocalizedEventParameter_lower selected squarefree capped)
    (historicalSlopeLocalizedEventParameter_upper selected squarefree capped)
    form member
  simpa only [historicalSlopeCappedLocalizedEventPoint,
    historicalSlopeLocalizedEventPoint_eq_pathValue, parameter, capped] using
      sign

/-- The common historical strict margin lower-bounds the absolute evaluation
of every strict prior at every capped localized point. -/
theorem historicalStrictFormMargin_le_cappedLocalizedEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (cap : ℚ) (capPositive : 0 < cap)
    {form : HermitianForm}
    (member : form ∈ historicalStrictPriorForms selected) :
    historicalStrictFormMargin selected ≤
      |form.eval (historicalSlopeCappedLocalizedEventPoint selected squarefree
        next cap capPositive)| := by
  let capped := cappedClearanceState next cap capPositive
  let t := historicalSlopeLocalizedEventParameter selected squarefree capped
  have lower := historicalSlopeLocalizedEventParameter_lower selected
    squarefree capped
  have upper := historicalSlopeLocalizedEventParameter_upper selected
    squarefree capped
  rw [historicalStrictPriorForms_eq_append] at member
  rcases List.mem_append.mp member with currentMember | childMember
  · apply (min_le_left _ _).trans
    simpa only [historicalSlopeCappedLocalizedEventPoint,
      historicalSlopeLocalizedEventPoint_eq_pathValue, capped, t] using
        historicalCurrentStrictFormMargin_le_pathValue selected lower upper
          currentMember
  · apply (min_le_right _ _).trans
    simpa only [historicalSlopeCappedLocalizedEventPoint,
      historicalSlopeLocalizedEventPoint_eq_pathValue, capped, t] using
        historicalChildStrictFormMargin_le_pathValue selected lower upper
          childMember

/-- The capped historical point has polynomial residual below one eighth of
the supplied cap. -/
theorem historicalSlopeCappedLocalizedEventPoint_residual_lt_cap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    normSq (p.eval (historicalSlopeCappedLocalizedEventPoint selected
      squarefree next cap capPositive)) < cap / 8 := by
  let capped := cappedClearanceState next cap capPositive
  have residual := localizedCellPoint_residual_lt output
    (historicalSlopeInputCell selected) squarefree capped
  have clearanceLe : capped.clearance.bound / 8 ≤ cap / 8 := by
    gcongr
    simpa only [capped] using
      cappedClearanceState_clearance_le next cap capPositive
  simpa only [historicalSlopeCappedLocalizedEventPoint,
    historicalSlopeLocalizedEventPoint, capped] using
      residual.trans_le clearanceLe

/-- The capped point also retains the original later box's one-sixteenth
boundary-clearance residual budget. -/
theorem historicalSlopeCappedLocalizedEventPoint_residual_le_originalClearance
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    normSq (p.eval (historicalSlopeCappedLocalizedEventPoint selected
      squarefree next cap capPositive)) ≤ next.clearance.bound / 16 := by
  let capped := cappedClearanceState next cap capPositive
  let clearance := localizedClearance output capped
  have residual := eventSourcePoint_residual
    (historicalSlopeInputCell selected) squarefree clearance
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
  change normSq (p.eval (eventSourcePoint (historicalSlopeInputCell selected)
    squarefree clearance)) ≤ _
  calc
    normSq (p.eval (eventSourcePoint (historicalSlopeInputCell selected)
        squarefree clearance)) ≤
      eventSourceResidualThreshold squarefree clearance := residual
    _ ≤ clearance.bound / 16 := thresholdLe
    _ ≤ capped.clearance.bound / 16 := by gcongr
    _ ≤ next.clearance.bound / 16 := by gcongr

theorem historicalSlopeCappedLocalizedEventPoint_deepInside
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
    let point := historicalSlopeCappedLocalizedEventPoint selected squarefree
      next cap capPositive
    let radius := boundaryInteriorRadius p next.box next.clearance
    next.box.xLower + 4 * radius < point.re ∧
      point.re < next.box.xUpper - 4 * radius ∧
      next.box.yLower + 4 * radius < point.im ∧
      point.im < next.box.yUpper - 4 * radius := by
  exact deepInside_of_small_residual next.clearance
    (historicalSlopeCappedLocalizedEventPoint_strictContains output selected
      squarefree degreeNonzero elimination next nextRefines cap capPositive)
    (historicalSlopeCappedLocalizedEventPoint_residual_le_originalClearance
      output selected squarefree next cap capPositive)

/-- Every inward side form of the original later box has a cap-independent
absolute margin at the capped historical point. -/
theorem boundaryInteriorRadius_le_historicalSlopeCappedBoxForm
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
      |form.eval (historicalSlopeCappedLocalizedEventPoint selected squarefree
        next cap capPositive)| := by
  let point := historicalSlopeCappedLocalizedEventPoint selected squarefree
    next cap capPositive
  let radius := boundaryInteriorRadius p next.box next.clearance
  have radiusPositive : 0 < radius :=
    boundaryInteriorRadius_pos p next.box next.clearance
  have deep := historicalSlopeCappedLocalizedEventPoint_deepInside output
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

theorem historicalSlopeCappedLocalizedEventPoint_ne_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLe : cap ≤ normSq (p.eval 0)) :
    historicalSlopeCappedLocalizedEventPoint selected squarefree next cap
      capPositive ≠ 0 := by
  have residual := historicalSlopeCappedLocalizedEventPoint_residual_lt_cap
    selected squarefree next cap capPositive
  have capDivLe : cap / 8 ≤ normSq (p.eval 0) :=
    (div_le_self capPositive.le (by norm_num : (1 : ℚ) ≤ 8)).trans capLe
  intro zero
  rw [zero] at residual
  exact (not_lt_of_ge capDivLe) residual

/-- If zero is not a root, every sufficiently capped historical event point
has a rational cap-independent squared-norm lower bound. -/
theorem historicalSlopeCappedLocalizedEventPoint_normSq_lower
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
      normSq (historicalSlopeCappedLocalizedEventPoint selected squarefree
        next cap capPositive) := by
  let point := historicalSlopeCappedLocalizedEventPoint selected squarefree
    next cap capPositive
  let L := denseLipschitzBound p (nearbyAmbient next.box)
  let zeroResidual := normSq (p.eval 0)
  have LPositive : 0 < L :=
    denseLipschitzBound_pos p (nearbyAmbient next.box)
  have zeroResidualPositive : 0 < zeroResidual := capPositive.trans_le capLe
  have strict := historicalSlopeCappedLocalizedEventPoint_strictContains output
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
    historicalSlopeCappedLocalizedEventPoint_residual_lt_cap selected
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
          L * normSq (point + -(0 : QI)) := lipschitz
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

/-- Cap-independent lower bound used for the protected nonzero norm form. -/
def historicalZeroNormLower
    (p : GaussianPolynomial) (box : RatBox) : ℚ :=
  normSq (p.eval 0) /
    (8 * denseLipschitzBound p (nearbyAmbient box))

theorem historicalZeroNormLower_pos
    (p : GaussianPolynomial) (box : RatBox)
    (zeroNonzero : p.eval 0 ≠ 0) :
    0 < historicalZeroNormLower p box :=
  div_pos (normSq_pos zeroNonzero)
    (mul_pos (by norm_num)
      (denseLipschitzBound_pos p (nearbyAmbient box)))

/-- One positive lower bound for every historical strict form, later-box
side, and the protected nonzero norm form. -/
def historicalPriorEvaluationLower
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (next : WindingOneState p (RatBox.symmetric R hR)) : ℚ :=
  min (historicalStrictFormMargin selected)
    (min (boundaryInteriorRadius p next.box next.clearance)
      (historicalZeroNormLower p next.box))

theorem historicalPriorEvaluationLower_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (zeroNonzero : p.eval 0 ≠ 0) :
    0 < historicalPriorEvaluationLower selected next :=
  lt_min (historicalStrictFormMargin_pos selected)
    (lt_min (boundaryInteriorRadius_pos p next.box next.clearance)
      (historicalZeroNormLower_pos p next.box zeroNonzero))

theorem historicalPriorEvaluationLower_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLeZeroResidual : cap ≤ normSq (p.eval 0)) :
    ∀ form ∈ historicalGridPriorForms selected
        (historicalSlopeCappedLocalizedEventPoint selected squarefree next cap
          capPositive) next.box,
      historicalPriorEvaluationLower selected next ≤
        |form.eval (historicalSlopeCappedLocalizedEventPoint selected
          squarefree next cap capPositive)| := by
  intro form member
  simp only [historicalGridPriorForms, List.mem_append,
    List.mem_singleton] at member
  rcases member with (historicalStrict | boxForm) | normForm
  · exact (min_le_left _ _).trans
      (historicalStrictFormMargin_le_cappedLocalizedEvent selected squarefree
        next cap capPositive historicalStrict)
  · exact ((min_le_right _ _).trans (min_le_left _ _)).trans
      (boundaryInteriorRadius_le_historicalSlopeCappedBoxForm output selected
        squarefree degreeNonzero elimination next nextRefines cap capPositive
        boxForm)
  · subst form
    apply ((min_le_right _ _).trans (min_le_right _ _)).trans
    have lower := historicalSlopeCappedLocalizedEventPoint_normSq_lower output
      selected squarefree degreeNonzero elimination next nextRefines cap
      capPositive capLeZeroResidual
    simpa [historicalZeroNormLower, eval_affineNormForm,
      abs_of_nonneg (normSq_nonneg
        (historicalSlopeCappedLocalizedEventPoint selected squarefree next cap
          capPositive))] using lower

/-- Uniform lower bound for every historical active-face entry radius on the
classified event cell. -/
def historicalBoundaryRadiusLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : ℚ :=
  FTA.Maximality.positiveMinimum
    ((historicalActiveOwnerForms selected).map fun form =>
      historicalSlopeDirectionalLower selected / (|form.radial| + 1))

theorem historicalBoundaryRadiusLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    0 < historicalBoundaryRadiusLower selected := by
  apply FTA.Maximality.positiveMinimum_pos
  intro radius member
  rw [List.mem_map] at member
  rcases member with ⟨form, _formMember, rfl⟩
  exact div_pos (historicalSlopeDirectionalLower_pos selected) (by positivity)

theorem historicalBoundaryRadiusLower_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) :
    historicalBoundaryRadiusLower selected ≤ 1 :=
  FTA.Maximality.positiveMinimum_le_one _

theorem historicalBoundaryRadiusLower_le_entryRadius
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
    historicalBoundaryRadiusLower selected ≤
      entryRadius form ((selectedCompletePath selected).value t) direction := by
  apply (FTA.Maximality.positiveMinimum_le_of_mem
    (List.mem_map.mpr ⟨form, member, rfl⟩)).trans
  unfold entryRadius
  exact div_le_div_of_nonneg_right
    (historicalSlopeDirectionalLower_le search lower upper member)
    (by positivity)

theorem historicalBoundaryRadiusLower_le_cappedEntryRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : SelectedEventPayload output} {direction : QI}
    (search : historicalClassifiedTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap)
    {form : HermitianForm}
    (member : form ∈ historicalActiveOwnerForms selected) :
    historicalBoundaryRadiusLower selected ≤
      entryRadius form
        (historicalSlopeCappedLocalizedEventPoint selected squarefree next cap
          capPositive)
        (historicalSlopeCappedLocalizedClassifiedTangentDirection search
          squarefree next cap capPositive).vector := by
  let capped := cappedClearanceState next cap capPositive
  have bound := historicalBoundaryRadiusLower_le_entryRadius search
    (historicalSlopeLocalizedEventParameter_lower selected squarefree capped)
    (historicalSlopeLocalizedEventParameter_upper selected squarefree capped)
    member
  change historicalBoundaryRadiusLower selected ≤ entryRadius form
    ((selectedCompletePath selected).value
      (historicalSlopeLocalizedEventParameter selected squarefree capped))
    direction
  exact bound

/-- Static lower bound for the complete multi-owner radius.  It depends on
the classified cell and original later box, but not on the localization cap. -/
def historicalUniformOwnerRadiusLower
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (next : WindingOneState p (RatBox.symmetric R hR)) : ℚ :=
  min 1 (min (historicalBoundaryRadiusLower selected)
    (priorRadiusLower
      (historicalGridPriorForms selected (0 : QI) next.box) next.box
      (historicalPriorEvaluationLower selected next)))

theorem historicalUniformOwnerRadiusLower_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (zeroNonzero : p.eval 0 ≠ 0) :
    0 < historicalUniformOwnerRadiusLower selected next :=
  lt_min zero_lt_one
    (lt_min (historicalBoundaryRadiusLower_pos selected)
      (priorRadiusLower_pos _ _
        (historicalPriorEvaluationLower_pos selected next zeroNonzero)))

theorem historicalUniformOwnerRadiusLower_le_one
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    historicalUniformOwnerRadiusLower selected next ≤ 1 :=
  min_le_left _ _

theorem historicalUniformOwnerRadiusLower_le_multiOwnerRadius
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLeZeroResidual : cap ≤ normSq (p.eval 0))
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection) :
    historicalUniformOwnerRadiusLower selected next ≤
      multiOwnerRadius
        (historicalSlopeCappedLocalizedClassifiedTangentDirection search
          squarefree next cap capPositive)
        (historicalGridPriorForms selected
          (historicalSlopeCappedLocalizedEventPoint selected squarefree next
            cap capPositive) next.box) := by
  let point := historicalSlopeCappedLocalizedEventPoint selected squarefree
    next cap capPositive
  let direction := historicalSlopeCappedLocalizedClassifiedTangentDirection
    search squarefree next cap capPositive
  let priors := historicalGridPriorForms selected point next.box
  have strict := historicalSlopeCappedLocalizedEventPoint_strictContains output
    selected squarefree degreeNonzero elimination next nextRefines cap
    capPositive
  have priorLower := priorRadiusLower_le_strictRadius
    (priors := priors) (box := next.box)
    (evaluationLower := historicalPriorEvaluationLower selected next)
    strict.contains direction.normSq_le_one
    (historicalPriorEvaluationLower_le selected squarefree degreeNonzero
      elimination next nextRefines cap capPositive capLeZeroResidual)
  unfold historicalUniformOwnerRadiusLower multiOwnerRadius
  apply le_min (min_le_left _ _)
  apply le_min
  · apply ((min_le_right _ _).trans (min_le_left _ _)).trans
    apply FTA.Maximality.le_positiveMinimum
      (historicalBoundaryRadiusLower_le_one selected)
    intro radius radiusMember
    rw [List.mem_map] at radiusMember
    rcases radiusMember with ⟨form, formMember, rfl⟩
    exact historicalBoundaryRadiusLower_le_cappedEntryRadius search squarefree
      next cap capPositive formMember
  · apply ((min_le_right _ _).trans (min_le_right _ _)).trans
    simpa only [priors, point, direction, historicalGridPriorForms] using
      priorLower

/-- Cap-independent positive lower bound for the complete historical
approximate-boundary budget. -/
def historicalUniformBoundaryBudgetLower
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (next : WindingOneState p (RatBox.symmetric R hR)) : ℚ :=
  historicalUniformOwnerRadiusLower selected next / 3 *
    historicalBoundaryRadiusLower selected

theorem historicalUniformBoundaryBudgetLower_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (zeroNonzero : p.eval 0 ≠ 0) :
    0 < historicalUniformBoundaryBudgetLower selected next :=
  mul_pos
    (div_pos
      (historicalUniformOwnerRadiusLower_pos selected next zeroNonzero)
      (by norm_num))
    (historicalBoundaryRadiusLower_pos selected)

theorem historicalUniformBoundaryBudgetLower_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLeZeroResidual : cap ≤ normSq (p.eval 0))
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection) :
    historicalUniformBoundaryBudgetLower selected next ≤
      approximateBoundaryBudget
        (historicalSlopeCappedLocalizedClassifiedTangentDirection search
          squarefree next cap capPositive)
        (historicalGridPriorForms selected
          (historicalSlopeCappedLocalizedEventPoint selected squarefree next
            cap capPositive) next.box) := by
  let point := historicalSlopeCappedLocalizedEventPoint selected squarefree
    next cap capPositive
  let direction := historicalSlopeCappedLocalizedClassifiedTangentDirection
    search squarefree next cap capPositive
  let priors := historicalGridPriorForms selected point next.box
  have evaluationLowerPositive := historicalPriorEvaluationLower_pos selected
    next zeroNonzero
  have evaluationLower := historicalPriorEvaluationLower_le selected squarefree
    degreeNonzero elimination next nextRefines cap capPositive
    capLeZeroResidual
  have priorNonzero : ∀ form ∈ priors, form.eval point ≠ 0 := by
    intro form member zero
    have lower := evaluationLower form member
    rw [zero, abs_zero] at lower
    exact (not_lt_of_ge lower) evaluationLowerPositive
  have radiusPositive := historicalUniformOwnerRadiusLower_pos selected next
    zeroNonzero
  have radiusLe := historicalUniformOwnerRadiusLower_le_multiOwnerRadius
    selected squarefree degreeNonzero elimination next nextRefines cap
    capPositive capLeZeroResidual search
  have epsilonLowerLe : historicalUniformOwnerRadiusLower selected next / 3 ≤
      multiOwnerEpsilon direction priors :=
    (radiusLower_div_three_lt_multiOwnerEpsilon direction priors
      radiusPositive radiusLe priorNonzero).le
  have epsilonLowerAtMostOne :
      historicalUniformOwnerRadiusLower selected next / 3 ≤ 1 := by
    have radiusLeOne := historicalUniformOwnerRadiusLower_le_one selected next
    nlinarith [radiusPositive]
  unfold historicalUniformBoundaryBudgetLower
  exact mul_le_approximateBoundaryBudget_of_lower_bounds direction priors
    priorNonzero epsilonLowerLe epsilonLowerAtMostOne
    (historicalBoundaryRadiusLower_pos selected).le
    (historicalBoundaryRadiusLower_le_one selected)
    (fun form member =>
      historicalBoundaryRadiusLower_le_cappedEntryRadius search squarefree
        next cap capPositive member)

/-- Direct per-refinement cap below both zero separation and half the uniform
historical owner budget. -/
def historicalStaticGridCap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (next : WindingOneState p (RatBox.symmetric R hR)) : ℚ :=
  min (normSq (p.eval 0) / 2)
    (historicalUniformBoundaryBudgetLower selected next /
      (2 * historicalActiveCoefficientSum selected))

theorem historicalStaticGridCap_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (zeroNonzero : p.eval 0 ≠ 0) :
    0 < historicalStaticGridCap selected next := by
  apply lt_min
  · exact div_pos (normSq_pos zeroNonzero) (by norm_num)
  · exact div_pos
      (historicalUniformBoundaryBudgetLower_pos selected next zeroNonzero)
      (mul_pos (by norm_num)
        (historicalActiveCoefficientSum_pos selected))

theorem historicalStaticGridCap_le_zeroResidual
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    historicalStaticGridCap selected next ≤ normSq (p.eval 0) := by
  apply (min_le_left _ _).trans
  exact div_le_self (normSq_nonneg (p.eval 0)) (by norm_num)

theorem historicalStaticGridCap_residualBudget
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection) :
    historicalActiveCoefficientSum selected *
        historicalStaticGridCap selected next <
      approximateBoundaryBudget
        (historicalSlopeCappedLocalizedClassifiedTangentDirection search
          squarefree next (historicalStaticGridCap selected next)
          (historicalStaticGridCap_pos selected next zeroNonzero))
        (historicalGridPriorForms selected
          (historicalSlopeCappedLocalizedEventPoint selected squarefree next
            (historicalStaticGridCap selected next)
            (historicalStaticGridCap_pos selected next zeroNonzero))
          next.box) := by
  let lower := historicalUniformBoundaryBudgetLower selected next
  let coefficient := historicalActiveCoefficientSum selected
  let cap := historicalStaticGridCap selected next
  have lowerPositive : 0 < lower :=
    historicalUniformBoundaryBudgetLower_pos selected next zeroNonzero
  have coefficientPositive : 0 < coefficient :=
    historicalActiveCoefficientSum_pos selected
  have capLeRatio : cap ≤ lower / (2 * coefficient) := min_le_right _ _
  have productLe : coefficient * cap ≤
      coefficient * (lower / (2 * coefficient)) :=
    mul_le_mul_of_nonneg_left capLeRatio coefficientPositive.le
  have identity : coefficient * (lower / (2 * coefficient)) =
      lower / 2 := by field_simp
  have lowerLeBudget := historicalUniformBoundaryBudgetLower_le selected
    squarefree degreeNonzero zeroNonzero elimination next nextRefines cap
    (historicalStaticGridCap_pos selected next zeroNonzero)
    (historicalStaticGridCap_le_zeroResidual selected next) search
  change coefficient * cap < _
  calc
    coefficient * cap ≤ coefficient * (lower / (2 * coefficient)) :=
      productLe
    _ = lower / 2 := identity
    _ < lower := by linarith
    _ ≤ _ := lowerLeBudget

/-- Direct complete historical-grid data using the static localized cap. -/
def historicalStaticGridData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection) :
    HistoricalGridData current output selected next nextRefines := by
  let cap := historicalStaticGridCap selected next
  let capPositive := historicalStaticGridCap_pos selected next zeroNonzero
  let point := historicalSlopeCappedLocalizedEventPoint selected squarefree
    next cap capPositive
  let direction := historicalSlopeCappedLocalizedClassifiedTangentDirection
    search squarefree next cap capPositive
  exact
    { base := point
      baseStrict := historicalSlopeCappedLocalizedEventPoint_strictContains
        output selected squarefree degreeNonzero elimination next nextRefines
        cap capPositive
      baseNonzero := historicalSlopeCappedLocalizedEventPoint_ne_zero selected
        squarefree next cap capPositive
        (historicalStaticGridCap_le_zeroResidual selected next)
      direction := direction
      strictAtBase := by
        simpa only [point, cap, capPositive] using
          historicalSlopeCappedLocalizedEventStrict selected squarefree next
            cap capPositive
      activeResidual := by
        intro form member
        have activeSmall :=
          historicalSlopeCappedLocalizedEventActive_lt_sum selected squarefree
            next cap capPositive member
        exact activeSmall.trans (by
          simpa only [point, direction, cap, capPositive] using
            historicalStaticGridCap_residualBudget selected squarefree
              degreeNonzero zeroNonzero elimination next nextRefines search) }

/-- A successful historical classifier therefore supplies the full uniform
data family required by the persistent coupled controller. -/
def historicalStaticGridDataFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection) :
    HistoricalGridDataFamily current output selected where
  data next nextRefines := historicalStaticGridData current output selected
    squarefree degreeNonzero zeroNonzero elimination next nextRefines search

/-- Concrete event-owner step in the compatible historical tangent-cone
branch, with no residual or continuity obligation left to the caller. -/
def nextOfHistoricalStaticGrid
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (valid : SelectedCurrentFormulaCanonical selected)
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected =
      some classifiedDirection) :
    CCLCoupledTrack.StepResult current :=
  (historicalStaticGridDataFamily current output selected squarefree
    degreeNonzero zeroNonzero elimination search).step squarefree degreeNonzero
      elimination valid

/-- Global-event adapter from the finite controller invariant to the local
historical grid premise.  No canonical statement about unrelated projective
paths is required. -/
def nextOfHistoricalStaticGridOfControllerEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (canonical : CCLCanonicalEvent.ControllerCanonicalOnInputEvents current.numerical
      current.word)
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected.toPayload =
      some classifiedDirection) :
    CCLCoupledTrack.StepResult current :=
  nextOfHistoricalStaticGrid current output selected.toPayload squarefree
    degreeNonzero zeroNonzero elimination
      (SelectedCurrentFormulaCanonical.ofSelectedEventCount canonical selected)
      search

/-- Guard-event specialization of the same finite-support adapter. -/
def nextOfHistoricalStaticGridOfControllerGuard
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (canonical : CCLCanonicalEvent.ControllerCanonicalOnInputEvents current.numerical
      current.word)
    {classifiedDirection : QI}
    (search : historicalClassifiedTangentDirection? selected.toPayload =
      some classifiedDirection) :
    CCLCoupledTrack.StepResult current :=
  nextOfHistoricalStaticGrid current output selected.toPayload squarefree
    degreeNonzero zeroNonzero elimination
      (SelectedCurrentFormulaCanonical.ofSelectedGuardEventCount canonical
        selected)
      search

end CCLHistoricalGridConvergence
end FTA
