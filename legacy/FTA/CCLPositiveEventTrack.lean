import FTA.CCLBranchController
import FTA.CCLEventExtraction
import FTA.CCLPositiveEventSemantics

/-!
# Concrete tracks for selected positive CCL events

This module is a thin, separately elaborated adapter from the controller's
source-labelled selected event to the generic residual-based extraction.
Keeping the adapter small avoids expanding the complete selected-event
payload inside the coupled controller.
-/

namespace FTA
namespace CCLPositiveEventTrack

open CCL
open FTA.AxisSafeCuts
open FTA.CCLBranchEvent
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLClearanceExclusion
open FTA.CCLEventExtraction
open FTA.CCLGeometry
open FTA.CCLPositiveEventSemantics
open FTA.CentralBandGrid
open FTA.GaussianPolynomialBounds
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

def selectedEventPointPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p) : QI :=
  eventSourcePoint selected.candidate.inputCell squarefree output.state.clearance

/-- The selected event's direct Newton band as an ordinary state in the
global numerical ambient box. -/
def selectedEventStatePayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    WindingOneState p ambient :=
  eventWindingOneState output.state.refinesAmbient
    selected.candidate.inputCell squarefree output.state.clearance elimination

theorem selectedEventStatePayload_strictInterior
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StrictInterior (selectedEventStatePayload selected squarefree elimination).box
      output.state.box := by
  exact extractedEventBand_strictInterior selected.candidate.inputCell
    squarefree output.state.clearance elimination

theorem selectedEventStatePayload_contains_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (selectedEventStatePayload selected squarefree elimination).box.Contains
      (selectedEventPointPayload selected squarefree) :=
  eventWindingOneState_contains_sourcePoint output.state.refinesAmbient
    selected.candidate.inputCell squarefree output.state.clearance elimination

/-- Fully constructive track generated from the selected event state. -/
def selectedEventTrackPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    WindingOneTrack p ambient :=
  eventWindingOneTrack output.state.refinesAmbient
    selected.candidate.inputCell squarefree output.state.clearance elimination

/-! Compatibility and guarded-owner wrappers over the common payload. -/

def selectedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p) : QI :=
  selectedEventPointPayload selected.toPayload.toIncrementalPayload squarefree

def guardedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p) : QI :=
  selectedEventPointPayload selected.toPayload.toIncrementalPayload squarefree

def selectedEventState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    WindingOneState p ambient :=
  selectedEventStatePayload selected.toPayload.toIncrementalPayload squarefree elimination

def guardedEventState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    WindingOneState p ambient :=
  selectedEventStatePayload selected.toPayload.toIncrementalPayload squarefree elimination

theorem selectedEventState_strictInterior
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StrictInterior (selectedEventState selected squarefree elimination).box
      output.state.box :=
  selectedEventStatePayload_strictInterior selected.toPayload.toIncrementalPayload squarefree
    elimination

theorem guardedEventState_strictInterior
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StrictInterior (guardedEventState selected squarefree elimination).box
      output.state.box :=
  selectedEventStatePayload_strictInterior selected.toPayload.toIncrementalPayload squarefree
    elimination

theorem selectedEventState_contains_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (selectedEventState selected squarefree elimination).box.Contains
      (selectedEventPoint selected squarefree) :=
  selectedEventStatePayload_contains_point selected.toPayload.toIncrementalPayload squarefree
    elimination

theorem guardedEventState_contains_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (guardedEventState selected squarefree elimination).box.Contains
      (guardedEventPoint selected squarefree) :=
  selectedEventStatePayload_contains_point selected.toPayload.toIncrementalPayload squarefree
    elimination

def selectedEventTrack
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    WindingOneTrack p ambient :=
  selectedEventTrackPayload selected.toPayload.toIncrementalPayload squarefree elimination

def guardedEventTrack
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    WindingOneTrack p ambient :=
  selectedEventTrackPayload selected.toPayload.toIncrementalPayload squarefree elimination

/-! ## Localization inside an arbitrary later owner state -/

/-- Preserve a winding-one state and all of its geometry while replacing its
boundary-clearance certificate by a smaller, caller-requested positive cap.
This is an executable data transformation, not a resource safeguard. -/
def cappedClearanceState
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) (cap : ℚ) (capPositive : 0 < cap) :
    WindingOneState p ambient :=
  { box := next.box
    refinesAmbient := next.refinesAmbient
    proper := next.proper
    rawWindingFour := next.rawWindingFour
    clearance := shrinkBoundaryClearance next.clearance cap capPositive
    ambientLeftClearance := next.ambientLeftClearance
    ambientRightClearance := next.ambientRightClearance
    ambientBottomClearance := next.ambientBottomClearance
    ambientTopClearance := next.ambientTopClearance }

@[simp] theorem cappedClearanceState_box
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) (cap : ℚ) (capPositive : 0 < cap) :
    (cappedClearanceState next cap capPositive).box = next.box := rfl

theorem cappedClearanceState_clearance_le
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) (cap : ℚ) (capPositive : 0 < cap) :
    (cappedClearanceState next cap capPositive).clearance.bound ≤ cap :=
  shrinkBoundaryClearance_bound_le_cap next.clearance cap capPositive

/-- Squared-distance tolerance consumed by the later state's boundary
clearance argument. -/
def localizationSpatial
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) : ℚ :=
  min 1 (next.clearance.bound /
    (16 * denseLipschitzBound p (nearbyAmbient next.box)))

theorem localizationSpatial_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) : 0 < localizationSpatial next := by
  exact lt_min zero_lt_one
    (div_pos next.clearance.positive
      (mul_pos (by norm_num)
        (denseLipschitzBound_pos p (nearbyAmbient next.box))))

theorem localizationSpatial_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) : localizationSpatial next ≤ 1 :=
  min_le_left _ _

theorem localizationSpatial_distanceBudget
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) :
    denseLipschitzBound p (nearbyAmbient next.box) * localizationSpatial next <
      next.clearance.bound / 8 := by
  let L := denseLipschitzBound p (nearbyAmbient next.box)
  have LPositive : 0 < L := denseLipschitzBound_pos p (nearbyAmbient next.box)
  have thresholdLe : localizationSpatial next ≤ next.clearance.bound / (16 * L) :=
    min_le_right _ _
  have scaled : L * localizationSpatial next ≤ next.clearance.bound / 16 := by
    have product := (le_div_iff₀ (mul_pos (by norm_num) LPositive)).mp
      thresholdLe
    dsimp only [L] at product ⊢
    nlinarith
  dsimp only [L] at scaled ⊢
  nlinarith [next.clearance.positive]

/-- A conservative event-band radius whose resulting coordinate slack fits
the later state's boundary-clearance budget without a square root. -/
def localizationRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) : ℚ :=
  localizationSpatial next / 96

theorem localizationRadius_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) : 0 < localizationRadius next := by
  exact div_pos (localizationSpatial_pos next) (by norm_num)

theorem localizationRadius_le_one
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) : localizationRadius next ≤ 1 :=
  by
    have := localizationSpatial_le_one next
    dsimp only [localizationRadius]
    linarith

/-- Shrinking only the stored clearance forces the localization radius below
the same caller-supplied cap while leaving the owner box unchanged. -/
theorem localizationRadius_cappedClearanceState_le_cap
    {p : GaussianPolynomial} {ambient : RatBox}
    (next : WindingOneState p ambient) (cap : ℚ) (capPositive : 0 < cap) :
    localizationRadius (cappedClearanceState next cap capPositive) ≤ cap := by
  let capped := cappedClearanceState next cap capPositive
  let L := denseLipschitzBound p (nearbyAmbient capped.box)
  have LPositive : 0 < L := denseLipschitzBound_pos p (nearbyAmbient capped.box)
  have LOne : 1 ≤ L := by
    dsimp only [L, denseLipschitzBound]
    exact le_max_left _ _
  have clearanceLe : capped.clearance.bound ≤ cap := by
    simpa only [capped] using
      cappedClearanceState_clearance_le next cap capPositive
  have ratioLe : capped.clearance.bound / (16 * L) ≤ cap := by
    apply (div_le_iff₀ (mul_pos (by norm_num) LPositive)).2
    calc
      capped.clearance.bound ≤ cap := clearanceLe
      _ ≤ cap * (16 * L) := by nlinarith
  have spatialLe : localizationSpatial capped ≤ cap :=
    (min_le_right _ _).trans (by simpa only [L] using ratioLe)
  unfold localizationRadius
  linarith [capPositive]

/-- The requested upper bound for the retained event box's clearance.  Its
second component forces the extracted Newton band below the localization
radius; its first component makes the rational event residual small for the
later box. -/
def localizationClearanceCap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (next : WindingOneState p ambient) : ℚ :=
  min next.clearance.bound
    (512 * denseLipschitzBound p (nearbyAmbient output.state.box) *
      localizationRadius next)

theorem localizationClearanceCap_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (next : WindingOneState p ambient) :
    0 < localizationClearanceCap output next := by
  exact lt_min next.clearance.positive
    (mul_pos
      (mul_pos (by norm_num)
        (denseLipschitzBound_pos p (nearbyAmbient output.state.box)))
      (localizationRadius_pos next))

def localizedClearance
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (next : WindingOneState p ambient) :
    BoxBoundaryClearanceCertificate p output.state.box :=
  shrinkBoundaryClearance output.state.clearance
    (localizationClearanceCap output next)
    (localizationClearanceCap_pos output next)

/-- Localized rational source point for any reclassified divisor cell of a
relevant event in the separated box.  Keeping the cell explicit lets later
sign refinements reuse the geometric localization proof. -/
def localizedCellPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : QI :=
  eventSourcePoint cell squarefree (localizedClearance output next)

/-- Specialization to the initially selected parser event cell. -/
def localizedEventPointPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : QI :=
  localizedCellPoint output selected.candidate.inputCell squarefree next

/-- Extracted winding-one state for an arbitrary localized divisor cell. -/
def localizedCellState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) : WindingOneState p ambient :=
  eventWindingOneState output.state.refinesAmbient cell squarefree
    (localizedClearance output next) elimination

/-- Specialization to the initially selected parser event cell. -/
def localizedEventStatePayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) : WindingOneState p ambient :=
  localizedCellState output selected.candidate.inputCell squarefree elimination
    next

def localizedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : QI :=
  localizedEventPointPayload selected.toPayload.toIncrementalPayload squarefree next

def localizedGuardedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : QI :=
  localizedEventPointPayload selected.toPayload.toIncrementalPayload squarefree next

def localizedEventState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) : WindingOneState p ambient :=
  localizedEventStatePayload selected.toPayload.toIncrementalPayload squarefree elimination next

def localizedGuardedEventState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) : WindingOneState p ambient :=
  localizedEventStatePayload selected.toPayload.toIncrementalPayload squarefree elimination next

theorem localizedEventBandRadius_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    eventBandRadius squarefree (localizedClearance output next) ≤
      localizationRadius next := by
  apply eventBandRadius_le_of_clearance_bound squarefree
  exact (shrinkBoundaryClearance_bound_le_cap output.state.clearance
    (localizationClearanceCap output next)
    (localizationClearanceCap_pos output next)).trans
      ((min_le_right _ _) : localizationClearanceCap output next ≤
        512 * denseLipschitzBound p (nearbyAmbient output.state.box) *
          localizationRadius next)

end CCLPositiveEventTrack
end FTA
