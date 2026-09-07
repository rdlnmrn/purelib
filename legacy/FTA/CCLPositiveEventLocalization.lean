import FTA.CCLPositiveEventTrack
import FTA.Maximality

/-!
# Localizing a positive CCL event in later winding boxes

The selected algebraic event can be rebuilt with an arbitrarily small
clearance constant.  Maximality prevents that localized winding-one state
from being separated from a strict refinement of any later owner state.
Elementary rectangle arithmetic then places its rational source-curve point
within the later state's boundary-clearance budget.

The argument is deliberately split into short lemmas so ordinary elaboration
does not expand the complete selected-event payload and maximality proof in a
single declaration.
-/

namespace FTA
namespace CCLPositiveEventLocalization

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBranchController
open FTA.CCLClearanceExclusion
open FTA.CCLEventExtraction
open FTA.CCLGeometry
open FTA.CCLIntersectionSampler
open FTA.CCLPositiveEventTrack
open FTA.CentralBandGrid
open FTA.ConstructiveTrack
open FTA.GaussianPolynomialBounds
open FTA.LocalExtraction
open FTA.Maximality
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-! ## Cell-generic localization -/

/-- Every reclassified divisor cell uses the same extracted-band geometry;
the proof does not depend on which parser sign refinement selected it. -/
theorem localizedCellState_strictInterior
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    {path : FTA.ProjectivePath.Path}
    {event : CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : CCLBranchEventOwner.InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) :
    StrictInterior
      (localizedCellState output cell squarefree elimination next).box
      output.state.box := by
  change StrictInterior
    (eventWindingOneState output.state.refinesAmbient cell squarefree
      (localizedClearance output next) elimination).box output.state.box
  exact eventWindingOneState_strictInterior output.state.refinesAmbient cell
    squarefree (localizedClearance output next) elimination

theorem localizedCellState_widthX_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    {path : FTA.ProjectivePath.Path}
    {event : CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : CCLBranchEventOwner.InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) :
    (localizedCellState output cell squarefree elimination next).box.xUpper -
        (localizedCellState output cell squarefree elimination next).box.xLower ≤
      4 * localizationRadius next := by
  calc
    (localizedCellState output cell squarefree elimination next).box.xUpper -
          (localizedCellState output cell squarefree elimination next).box.xLower ≤
        4 * eventBandRadius squarefree (localizedClearance output next) := by
      change
        (eventWindingOneState output.state.refinesAmbient cell squarefree
          (localizedClearance output next) elimination).box.xUpper -
            (eventWindingOneState output.state.refinesAmbient cell squarefree
              (localizedClearance output next) elimination).box.xLower ≤ _
      exact eventWindingOneState_widthX_le output.state.refinesAmbient cell
        squarefree (localizedClearance output next) elimination
    _ ≤ 4 * localizationRadius next := by
      gcongr
      exact localizedEventBandRadius_le output squarefree next

theorem localizedCellState_widthY_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    {path : FTA.ProjectivePath.Path}
    {event : CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : CCLBranchEventOwner.InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) :
    (localizedCellState output cell squarefree elimination next).box.yUpper -
        (localizedCellState output cell squarefree elimination next).box.yLower ≤
      4 * localizationRadius next := by
  calc
    (localizedCellState output cell squarefree elimination next).box.yUpper -
          (localizedCellState output cell squarefree elimination next).box.yLower ≤
        4 * eventBandRadius squarefree (localizedClearance output next) := by
      change
        (eventWindingOneState output.state.refinesAmbient cell squarefree
          (localizedClearance output next) elimination).box.yUpper -
            (eventWindingOneState output.state.refinesAmbient cell squarefree
              (localizedClearance output next) elimination).box.yLower ≤ _
      exact eventWindingOneState_widthY_le output.state.refinesAmbient cell
        squarefree (localizedClearance output next) elimination
    _ ≤ 4 * localizationRadius next := by
      gcongr
      exact localizedEventBandRadius_le output squarefree next

/-- Maximality localizes every classified divisor cell against every later
winding-one owner box. -/
theorem localizedCellState_not_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    {path : FTA.ProjectivePath.Path}
    {event : CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : CCLBranchEventOwner.InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    ¬(localizedCellState output cell squarefree elimination next).box.Separated
      (refineState squarefree elimination next 1 zero_lt_one).box := by
  intro separated
  have eventInside := localizedCellState_strictInterior output cell squarefree
    elimination next
  have innerStrict := refineState_strictInterior squarefree elimination next 1
    zero_lt_one
  have innerInside : StrictInterior
      (refineState squarefree elimination next 1 zero_lt_one).box
      output.state.box :=
    { left := lt_of_le_of_lt nextRefines.1 innerStrict.left
      right := lt_of_lt_of_le innerStrict.right nextRefines.2.1
      bottom := lt_of_le_of_lt nextRefines.2.2.1 innerStrict.bottom
      top := lt_of_lt_of_le innerStrict.top nextRefines.2.2.2 }
  exact separated_states_not_both_inside_windingOne p R hR squarefree
    degreeNonzero elimination output.state
    (localizedCellState output cell squarefree elimination next)
    (refineState squarefree elimination next 1 zero_lt_one)
    eventInside innerInside separated

theorem localizedEventState_strictInterior
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) :
    StrictInterior
      (localizedEventState selected squarefree elimination next).box
      output.state.box := by
  change StrictInterior
    (eventWindingOneState output.state.refinesAmbient
      selected.candidate.inputCell squarefree
      (localizedClearance output next) elimination).box output.state.box
  exact eventWindingOneState_strictInterior output.state.refinesAmbient
    selected.candidate.inputCell squarefree (localizedClearance output next)
    elimination

theorem localizedEventState_widthX_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) :
    (localizedEventState selected squarefree elimination next).box.xUpper -
        (localizedEventState selected squarefree elimination next).box.xLower ≤
      4 * localizationRadius next := by
  calc
    (localizedEventState selected squarefree elimination next).box.xUpper -
          (localizedEventState selected squarefree elimination next).box.xLower ≤
        4 * eventBandRadius squarefree (localizedClearance output next) := by
      change
        (eventWindingOneState output.state.refinesAmbient
          selected.candidate.inputCell squarefree
          (localizedClearance output next) elimination).box.xUpper -
            (eventWindingOneState output.state.refinesAmbient
              selected.candidate.inputCell squarefree
              (localizedClearance output next) elimination).box.xLower ≤ _
      exact eventWindingOneState_widthX_le output.state.refinesAmbient
        selected.candidate.inputCell squarefree (localizedClearance output next)
        elimination
    _ ≤ 4 * localizationRadius next := by
      gcongr
      exact localizedEventBandRadius_le output squarefree next

theorem localizedEventState_widthY_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) :
    (localizedEventState selected squarefree elimination next).box.yUpper -
        (localizedEventState selected squarefree elimination next).box.yLower ≤
      4 * localizationRadius next := by
  calc
    (localizedEventState selected squarefree elimination next).box.yUpper -
          (localizedEventState selected squarefree elimination next).box.yLower ≤
        4 * eventBandRadius squarefree (localizedClearance output next) := by
      change
        (eventWindingOneState output.state.refinesAmbient
          selected.candidate.inputCell squarefree
          (localizedClearance output next) elimination).box.yUpper -
            (eventWindingOneState output.state.refinesAmbient
              selected.candidate.inputCell squarefree
              (localizedClearance output next) elimination).box.yLower ≤ _
      exact eventWindingOneState_widthY_le output.state.refinesAmbient
        selected.candidate.inputCell squarefree (localizedClearance output next)
        elimination
    _ ≤ 4 * localizationRadius next := by
      gcongr
      exact localizedEventBandRadius_le output squarefree next

/-- A localized positive-event state and a strict concrete refinement of a
later owner state cannot have a positive coordinate gap inside their common
winding-one owner. -/
theorem localizedEventState_not_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    ¬(localizedEventState selected squarefree elimination next).box.Separated
      (refineState squarefree elimination next 1 zero_lt_one).box := by
  intro separated
  have eventInside := localizedEventState_strictInterior selected squarefree
    elimination next
  have innerStrict := refineState_strictInterior squarefree elimination next 1
    zero_lt_one
  have innerInside : StrictInterior
      (refineState squarefree elimination next 1 zero_lt_one).box
      output.state.box :=
    { left := lt_of_le_of_lt nextRefines.1 innerStrict.left
      right := lt_of_lt_of_le innerStrict.right nextRefines.2.1
      bottom := lt_of_le_of_lt nextRefines.2.2.1 innerStrict.bottom
      top := lt_of_lt_of_le innerStrict.top nextRefines.2.2.2 }
  exact separated_states_not_both_inside_windingOne p R hR squarefree
    degreeNonzero elimination output.state
    (localizedEventState selected squarefree elimination next)
    (refineState squarefree elimination next 1 zero_lt_one)
    eventInside innerInside separated

/-! ## Guarded-owner specializations of the cell-generic localization -/

theorem localizedGuardedEventState_strictInterior
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) :
    StrictInterior
      (localizedGuardedEventState selected squarefree elimination next).box
      output.state.box := by
  change StrictInterior
    (localizedCellState output selected.candidate.inputCell squarefree
      elimination next).box output.state.box
  exact localizedCellState_strictInterior output selected.candidate.inputCell
    squarefree elimination next

theorem localizedGuardedEventState_widthX_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) :
    (localizedGuardedEventState selected squarefree elimination next).box.xUpper -
        (localizedGuardedEventState selected squarefree elimination next).box.xLower ≤
      4 * localizationRadius next := by
  change
    (localizedCellState output selected.candidate.inputCell squarefree
        elimination next).box.xUpper -
      (localizedCellState output selected.candidate.inputCell squarefree
        elimination next).box.xLower ≤ 4 * localizationRadius next
  exact localizedCellState_widthX_le output selected.candidate.inputCell
    squarefree elimination next

theorem localizedGuardedEventState_widthY_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient) :
    (localizedGuardedEventState selected squarefree elimination next).box.yUpper -
        (localizedGuardedEventState selected squarefree elimination next).box.yLower ≤
      4 * localizationRadius next := by
  change
    (localizedCellState output selected.candidate.inputCell squarefree
        elimination next).box.yUpper -
      (localizedCellState output selected.candidate.inputCell squarefree
        elimination next).box.yLower ≤ 4 * localizationRadius next
  exact localizedCellState_widthY_le output selected.candidate.inputCell
    squarefree elimination next

theorem localizedGuardedEventState_not_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    ¬(localizedGuardedEventState selected squarefree elimination next).box.Separated
      (refineState squarefree elimination next 1 zero_lt_one).box := by
  change ¬(localizedCellState output selected.candidate.inputCell squarefree
      elimination next).box.Separated
    (refineState squarefree elimination next 1 zero_lt_one).box
  exact localizedCellState_not_separated output selected.candidate.inputCell
    squarefree degreeNonzero elimination next nextRefines

/-- Four rational slacks placing the localized source point within one band
width of the later owner box. -/
structure CoordinateSlack (box : RatBox) (point : QI) (margin : ℚ) : Prop where
  xLower : box.xLower - margin ≤ point.re
  xUpper : point.re ≤ box.xUpper + margin
  yLower : box.yLower - margin ≤ point.im
  yUpper : point.im ≤ box.yUpper + margin

theorem localizedCellPoint_coordinateSlack
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    {path : FTA.ProjectivePath.Path}
    {event : CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : CCLBranchEventOwner.InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    CoordinateSlack next.box
      (localizedCellPoint output cell squarefree next)
      (4 * localizationRadius next) := by
  let eventState := localizedCellState output cell squarefree elimination next
  let inner := refineState squarefree elimination next 1 zero_lt_one
  let point := localizedCellPoint output cell squarefree next
  have notSeparated : ¬eventState.box.Separated inner.box := by
    simpa only [eventState, inner] using localizedCellState_not_separated
      output cell squarefree degreeNonzero elimination next nextRefines
  have overlaps := RatBox.not_separated_coordinate_overlaps notSeparated
  have pointInEvent : eventState.box.Contains point := by
    change
      (eventWindingOneState output.state.refinesAmbient cell squarefree
        (localizedClearance output next) elimination).box.Contains
          (eventSourcePoint cell squarefree (localizedClearance output next))
    exact eventWindingOneState_contains_sourcePoint output.state.refinesAmbient
      cell squarefree (localizedClearance output next) elimination
  have widthX : eventState.box.xUpper - eventState.box.xLower ≤
      4 * localizationRadius next := by
    simpa only [eventState] using localizedCellState_widthX_le output cell
      squarefree elimination next
  have widthY : eventState.box.yUpper - eventState.box.yLower ≤
      4 * localizationRadius next := by
    simpa only [eventState] using localizedCellState_widthY_le output cell
      squarefree elimination next
  have innerRefines : inner.box.Refines next.box := by
    simpa only [inner] using refineState_refines squarefree elimination next 1
      zero_lt_one
  exact
    { xLower := by
        linarith [innerRefines.1, overlaps.1, pointInEvent.1, widthX]
      xUpper := by
        linarith [innerRefines.2.1, overlaps.2.1, pointInEvent.2.1, widthX]
      yLower := by
        linarith [innerRefines.2.2.1, overlaps.2.2.1,
          pointInEvent.2.2.1, widthY]
      yUpper := by
        linarith [innerRefines.2.2.2, overlaps.2.2.2,
          pointInEvent.2.2.2, widthY] }

theorem localizedCellPoint_clampDistance
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    {path : FTA.ProjectivePath.Path}
    {event : CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : CCLBranchEventOwner.InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    normSq (localizedCellPoint output cell squarefree next -
        clampToBox next.box (localizedCellPoint output cell squarefree next)) <
      localizationSpatial next := by
  let margin := 4 * localizationRadius next
  have marginPositive : 0 < margin :=
    mul_pos (by norm_num) (localizationRadius_pos next)
  have slack := localizedCellPoint_coordinateSlack output cell squarefree
    degreeNonzero elimination next nextRefines
  have raw := normSq_sub_clampToBox_lt_of_coordinate_slack marginPositive
    slack.xLower slack.xUpper slack.yLower slack.yUpper
  have radiusOne := localizationRadius_le_one next
  have radiusPositive := localizationRadius_pos next
  have squareBound : 3 * margin ^ 2 < localizationSpatial next := by
    dsimp only [margin, localizationRadius] at radiusOne radiusPositive ⊢
    nlinarith [localizationSpatial_pos next]
  exact raw.trans squareBound

theorem localizedCellPoint_residual_lt
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    {path : FTA.ProjectivePath.Path}
    {event : CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : CCLBranchEventOwner.InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    normSq (p.eval (localizedCellPoint output cell squarefree next)) <
      next.clearance.bound / 8 := by
  let clearance := localizedClearance output next
  have residual := eventSourcePoint_residual cell squarefree clearance
  have thresholdLe := eventSourceResidualThreshold_le_clearance squarefree
    clearance
  have clearanceLeNext : clearance.bound ≤ next.clearance.bound :=
    (shrinkBoundaryClearance_bound_le_cap output.state.clearance
      (localizationClearanceCap output next)
      (localizationClearanceCap_pos output next)).trans (min_le_left _ _)
  change normSq (p.eval (eventSourcePoint cell squarefree clearance)) < _
  calc
    normSq (p.eval (eventSourcePoint cell squarefree clearance)) ≤
      eventSourceResidualThreshold squarefree clearance := residual
    _ ≤ clearance.bound / 16 := thresholdLe
    _ ≤ next.clearance.bound / 16 := by gcongr
    _ < next.clearance.bound / 8 := by linarith [next.clearance.positive]

/-- The rational endpoint of any final event-sign refinement lies strictly
inside every later winding-one owner box. -/
theorem localizedCellPoint_strictContains
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    {path : FTA.ProjectivePath.Path}
    {event : CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : CCLBranchEventOwner.InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    next.box.StrictContains
      (localizedCellPoint output cell squarefree next) := by
  exact strictContains_of_clamp next.clearance
    (localizationSpatial_le_one next)
    (localizedCellPoint_clampDistance output cell squarefree degreeNonzero
      elimination next nextRefines)
    (localizedCellPoint_residual_lt output cell squarefree next)
    (localizationSpatial_distanceBudget next)

theorem localizedEventPoint_coordinateSlack
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    CoordinateSlack next.box (localizedEventPoint selected squarefree next)
      (4 * localizationRadius next) := by
  let eventState := localizedEventState selected squarefree elimination next
  let inner := refineState squarefree elimination next 1 zero_lt_one
  let point := localizedEventPoint selected squarefree next
  have notSeparated : ¬eventState.box.Separated inner.box := by
    simpa only [eventState, inner] using localizedEventState_not_separated
      selected squarefree degreeNonzero elimination next nextRefines
  have overlaps := RatBox.not_separated_coordinate_overlaps notSeparated
  have pointInEvent : eventState.box.Contains point := by
    change
      (eventWindingOneState output.state.refinesAmbient
        selected.candidate.inputCell squarefree
        (localizedClearance output next) elimination).box.Contains
          (eventSourcePoint selected.candidate.inputCell squarefree
            (localizedClearance output next))
    exact eventWindingOneState_contains_sourcePoint output.state.refinesAmbient
      selected.candidate.inputCell squarefree (localizedClearance output next)
      elimination
  have widthX : eventState.box.xUpper - eventState.box.xLower ≤
      4 * localizationRadius next := by
    simpa only [eventState] using localizedEventState_widthX_le selected
      squarefree elimination next
  have widthY : eventState.box.yUpper - eventState.box.yLower ≤
      4 * localizationRadius next := by
    simpa only [eventState] using localizedEventState_widthY_le selected
      squarefree elimination next
  have innerRefines : inner.box.Refines next.box := by
    simpa only [inner] using refineState_refines squarefree elimination next 1
      zero_lt_one
  exact
    { xLower := by
        linarith [innerRefines.1, overlaps.1, pointInEvent.1, widthX]
      xUpper := by
        linarith [innerRefines.2.1, overlaps.2.1, pointInEvent.2.1, widthX]
      yLower := by
        linarith [innerRefines.2.2.1, overlaps.2.2.1,
          pointInEvent.2.2.1, widthY]
      yUpper := by
        linarith [innerRefines.2.2.2, overlaps.2.2.2,
          pointInEvent.2.2.2, widthY] }

theorem localizedEventPoint_clampDistance
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    normSq (localizedEventPoint selected squarefree next -
        clampToBox next.box (localizedEventPoint selected squarefree next)) <
      localizationSpatial next := by
  let margin := 4 * localizationRadius next
  have marginPositive : 0 < margin :=
    mul_pos (by norm_num) (localizationRadius_pos next)
  have slack := localizedEventPoint_coordinateSlack selected squarefree
    degreeNonzero elimination next nextRefines
  have raw := normSq_sub_clampToBox_lt_of_coordinate_slack marginPositive
    slack.xLower slack.xUpper slack.yLower slack.yUpper
  have radiusOne := localizationRadius_le_one next
  have radiusPositive := localizationRadius_pos next
  have squareBound : 3 * margin ^ 2 < localizationSpatial next := by
    dsimp only [margin, localizationRadius] at radiusOne radiusPositive ⊢
    nlinarith [localizationSpatial_pos next]
  exact raw.trans squareBound

theorem localizedEventPoint_residual_lt
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    normSq (p.eval (localizedEventPoint selected squarefree next)) <
      next.clearance.bound / 8 := by
  let clearance := localizedClearance output next
  have residual := eventSourcePoint_residual selected.candidate.inputCell
    squarefree clearance
  have thresholdLe := eventSourceResidualThreshold_le_clearance squarefree
    clearance
  have clearanceLeNext : clearance.bound ≤ next.clearance.bound :=
    (shrinkBoundaryClearance_bound_le_cap output.state.clearance
      (localizationClearanceCap output next)
      (localizationClearanceCap_pos output next)).trans (min_le_left _ _)
  change normSq (p.eval
    (eventSourcePoint selected.candidate.inputCell squarefree clearance)) < _
  calc
    normSq (p.eval
        (eventSourcePoint selected.candidate.inputCell squarefree clearance)) ≤
      eventSourceResidualThreshold squarefree clearance := residual
    _ ≤ clearance.bound / 16 := thresholdLe
    _ ≤ next.clearance.bound / 16 := by gcongr
    _ < next.clearance.bound / 8 := by linarith [next.clearance.positive]

/-- The localized rational point is an exact point of the selected planned
Hermitian boundary, even though it only approximates the polynomial root. -/
theorem localizedEventPoint_onBoundary
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    selected.candidate.sourceEvent.partition.entry.source.form.eval
      (localizedEventPoint selected squarefree next) = 0 := by
  let clearance := localizedClearance output next
  change selected.candidate.sourceEvent.partition.entry.source.form.eval
    (eventSourcePoint selected.candidate.inputCell squarefree clearance) = 0
  exact selected.candidate.sourceEvent.partition.entry.onBoundary
    (selected.candidate.source_determinant_ne stateDeterminant selected.member)
    (eventSourcePoint_pathDenominator_ne selected.candidate.inputCell
      squarefree clearance)

/-- Final geometric localization result used by the finite owner sampler. -/
theorem localizedEventPoint_strictContains
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    next.box.StrictContains
      (localizedEventPoint selected squarefree next) := by
  exact strictContains_of_clamp next.clearance
    (localizationSpatial_le_one next)
    (localizedEventPoint_clampDistance selected squarefree degreeNonzero
      elimination next nextRefines)
    (localizedEventPoint_residual_lt selected squarefree next)
    (localizationSpatial_distanceBudget next)

/-! ## Guarded-owner point geometry -/

theorem localizedGuardedEventPoint_coordinateSlack
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    CoordinateSlack next.box
      (localizedGuardedEventPoint selected squarefree next)
      (4 * localizationRadius next) := by
  change CoordinateSlack next.box
    (localizedCellPoint output selected.candidate.inputCell squarefree next)
    (4 * localizationRadius next)
  exact localizedCellPoint_coordinateSlack output selected.candidate.inputCell
    squarefree degreeNonzero elimination next nextRefines

theorem localizedGuardedEventPoint_clampDistance
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    normSq (localizedGuardedEventPoint selected squarefree next -
        clampToBox next.box
          (localizedGuardedEventPoint selected squarefree next)) <
      localizationSpatial next := by
  change normSq
      (localizedCellPoint output selected.candidate.inputCell squarefree next -
        clampToBox next.box
          (localizedCellPoint output selected.candidate.inputCell squarefree
            next)) < localizationSpatial next
  exact localizedCellPoint_clampDistance output selected.candidate.inputCell
    squarefree degreeNonzero elimination next nextRefines

theorem localizedGuardedEventPoint_residual_lt
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    normSq (p.eval
        (localizedGuardedEventPoint selected squarefree next)) <
      next.clearance.bound / 8 := by
  change normSq (p.eval
      (localizedCellPoint output selected.candidate.inputCell squarefree next)) <
    next.clearance.bound / 8
  exact localizedCellPoint_residual_lt output selected.candidate.inputCell
    squarefree next

/-- The guarded event point lies on the same planned Hermitian boundary as
its retained terminal guard cell. -/
theorem localizedGuardedEventPoint_onBoundary
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    selected.candidate.sourceEvent.sourceCell.partition.entry.source.form.eval
      (localizedGuardedEventPoint selected squarefree next) = 0 := by
  let clearance := localizedClearance output next
  change
    selected.candidate.sourceEvent.sourceCell.partition.entry.source.form.eval
      (eventSourcePoint selected.candidate.inputCell squarefree clearance) = 0
  exact selected.candidate.sourceEvent.sourceCell.partition.entry.onBoundary
    (selected.candidate.source_determinant_ne stateDeterminant selected.member)
    (eventSourcePoint_pathDenominator_ne selected.candidate.inputCell squarefree
      clearance)

theorem localizedGuardedEventPoint_strictContains
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    next.box.StrictContains
      (localizedGuardedEventPoint selected squarefree next) := by
  change next.box.StrictContains
    (localizedCellPoint output selected.candidate.inputCell squarefree next)
  exact localizedCellPoint_strictContains output selected.candidate.inputCell
    squarefree degreeNonzero elimination next nextRefines

end CCLPositiveEventLocalization
end FTA
