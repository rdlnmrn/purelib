import FTA.CCLHermitianBox
import FTA.CCLGuardedEventGrid
import FTA.CCLEventTangentSigns
import FTA.CCLPositiveEventApproximation
import FTA.CCLPositiveEventLocalization
import FTA.CCLTangentStability

/-!
# Convergence of positive-event and represented samples

The selected rational curve point and the coupled track's represented sample
are produced independently.  Both nevertheless lie in arbitrarily small
winding-one boxes inside the same owner.  Maximality prevents those boxes from
being separated, giving a fully rational coordinate-distance bound.  This is
the geometric half of the finite grid-success argument.
-/

namespace FTA
namespace CCLPositiveEventConvergence

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBranchController
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLClearanceExclusion
open FTA.CCLEventExtraction
open FTA.CCLEventTangentSigns
open FTA.CCLGeometry
open FTA.CCLGuardedEventGrid
open FTA.CCLHermitianBox
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLNextBitFormula
open FTA.CCLPathIntersection
open FTA.CCLPathTangent
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventGrid
open FTA.CCLPositiveEventApproximation
open FTA.CCLPositiveEventLocalization
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventTrack
open FTA.CentralBandGrid
open FTA.ConstructiveTrack
open FTA.GaussianPolynomialBounds
open FTA.LocalExtraction
open FTA.Maximality
open FTA.CCLMultiOwnerGrid
open FTA.CCLOwnerDirection
open FTA.RationalPolynomialBounds
open FTA.RootCountDivisibility
open FTA.RootTrackSeparation
open FTA.SturmTransducer

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Points in two nonseparated boxes are at most the sum of the two side
lengths apart in each coordinate. -/
theorem coordinateDistance_le_of_not_separated
    {left right : RatBox} {z w : QI}
    (zInside : left.Contains z) (wInside : right.Contains w)
    (notSeparated : ¬left.Separated right) :
    |z.re - w.re| ≤ left.widthX + right.widthX ∧
      |z.im - w.im| ≤ left.widthY + right.widthY := by
  have overlaps := RatBox.not_separated_coordinate_overlaps notSeparated
  constructor
  · rw [abs_le]
    constructor
    · dsimp only [RatBox.widthX]
      linarith [zInside.1, wInside.2.1, overlaps.2.1]
    · dsimp only [RatBox.widthX]
      linarith [zInside.2.1, wInside.1, overlaps.1]
  · rw [abs_le]
    constructor
    · dsimp only [RatBox.widthY]
      linarith [zInside.2.2.1, wInside.2.2.2, overlaps.2.2.2]
    · dsimp only [RatBox.widthY]
      linarith [zInside.2.2.2, wInside.2.2.1, overlaps.2.2.1]

/-- A common side-length bound gives the coordinate sum used by the
Hermitian variation estimate. -/
theorem coordinateDistanceSum_le
    {left right : RatBox} {z w : QI}
    (zInside : left.Contains z) (wInside : right.Contains w)
    (notSeparated : ¬left.Separated right)
    {leftWidth rightWidth : ℚ}
    (leftX : left.widthX ≤ leftWidth)
    (leftY : left.widthY ≤ leftWidth)
    (rightX : right.widthX ≤ rightWidth)
    (rightY : right.widthY ≤ rightWidth) :
    |z.re - w.re| + |z.im - w.im| ≤
      2 * (leftWidth + rightWidth) := by
  have distances := coordinateDistance_le_of_not_separated zInside wInside
    notSeparated
  calc
    |z.re - w.re| + |z.im - w.im| ≤
        (left.widthX + right.widthX) +
          (left.widthY + right.widthY) :=
      add_le_add distances.1 distances.2
    _ ≤ 2 * (leftWidth + rightWidth) := by linarith

/-- Shrink the selected-event extraction so its Newton band has any supplied
positive rational radius. -/
def shrinkingEventClearance
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (radius : ℚ) (radiusPositive : 0 < radius) :
    BoxBoundaryClearanceCertificate p output.state.box :=
  shrinkBoundaryClearance output.state.clearance
    (512 * denseLipschitzBound p (nearbyAmbient output.state.box) * radius)
    (mul_pos
      (mul_pos (by norm_num)
        (denseLipschitzBound_pos p (nearbyAmbient output.state.box)))
      radiusPositive)

/-- The shrinking Newton point attached to an arbitrary parser event cell.
No owner bit is needed: positive curve count and local extraction depend only
on the re-isolated event factor and the containing winding box. -/
def shrinkingInputEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {denominatorState cellState : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate denominatorState.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell cellState event)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) : QI :=
  eventSourcePoint cell squarefree
    (shrinkingEventClearance output radius radiusPositive)

/-- The shrinking winding-one state attached to an arbitrary parser event
cell.  This owner-independent form is the state used to compare positive
all-`neither` events with the current root track. -/
def shrinkingInputEventState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {denominatorState cellState : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate denominatorState.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell cellState event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    WindingOneState p ambient :=
  eventWindingOneState output.state.refinesAmbient cell squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination

def shrinkingEventPointPayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) : QI :=
  eventSourcePoint selected.candidate.inputCell squarefree
    (shrinkingEventClearance output radius radiusPositive)

def shrinkingEventStatePayload
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    WindingOneState p ambient :=
  eventWindingOneState output.state.refinesAmbient
    selected.candidate.inputCell squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination

def shrinkingEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) : QI :=
  shrinkingEventPointPayload selected squarefree radius radiusPositive

def guardedShrinkingEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) : QI :=
  shrinkingEventPointPayload selected.toPayload.toIncrementalPayload squarefree radius radiusPositive

def shrinkingEventState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    WindingOneState p ambient :=
  shrinkingEventStatePayload selected squarefree elimination radius
    radiusPositive

def guardedShrinkingEventState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    WindingOneState p ambient :=
  shrinkingEventStatePayload selected.toPayload.toIncrementalPayload squarefree elimination radius
    radiusPositive

/-- The same extraction, seeded by the refined input cell whose whole parent
interval already carries all classified tangent-slope signs. -/
def slopeShrinkingEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) : QI :=
  eventSourcePoint (selectedSlopeInputCell selected) squarefree
    (shrinkingEventClearance output radius radiusPositive)

def slopeShrinkingEventState
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    WindingOneState p ambient :=
  eventWindingOneState output.state.refinesAmbient
    (selectedSlopeInputCell selected) squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination

def slopeShrinkingEventApproximationWidth
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) : ℚ :=
  eventSourceApproximationWidth (selectedSlopeInputCell selected) squarefree
    (shrinkingEventClearance output radius radiusPositive)

theorem slopeShrinkingEventApproximationWidth_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    0 < slopeShrinkingEventApproximationWidth selected squarefree radius
      radiusPositive :=
  eventSourceApproximationWidth_pos (selectedSlopeInputCell selected)
    squarefree (shrinkingEventClearance output radius radiusPositive)

def slopeShrinkingEventParameter
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) : ℚ :=
  ((selectedSlopeInputCell selected).clearedApproximation
    (slopeShrinkingEventApproximationWidth selected squarefree radius
      radiusPositive)
    (slopeShrinkingEventApproximationWidth_pos selected squarefree radius
      radiusPositive)).refined.interval.lower

theorem slopeShrinkingEventPoint_eq_pathValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    slopeShrinkingEventPoint selected squarefree radius radiusPositive =
      selected.candidate.sourceEvent.partition.entry.chart.path.value
        (slopeShrinkingEventParameter selected squarefree radius
          radiusPositive) := by
  rfl

theorem slopeShrinkingEventParameter_lower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (selectedSlopeSigns selected).refined.interval.lower ≤
      slopeShrinkingEventParameter selected squarefree radius
        radiusPositive := by
  let cell := selectedSlopeInputCell selected
  let approximation := cell.clearedApproximation
    (slopeShrinkingEventApproximationWidth selected squarefree radius
      radiusPositive)
    (slopeShrinkingEventApproximationWidth_pos selected squarefree radius
      radiusPositive)
  exact (cell.branch.computeEventSigns cell.parent).refines.1.trans
    approximation.refines.1

theorem slopeShrinkingEventParameter_upper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    slopeShrinkingEventParameter selected squarefree radius radiusPositive ≤
      (selectedSlopeSigns selected).refined.interval.upper := by
  let cell := selectedSlopeInputCell selected
  let approximation := cell.clearedApproximation
    (slopeShrinkingEventApproximationWidth selected squarefree radius
      radiusPositive)
    (slopeShrinkingEventApproximationWidth_pos selected squarefree radius
      radiusPositive)
  exact (approximation.refined.proper.le.trans approximation.refines.2).trans
    (cell.branch.computeEventSigns cell.parent).refines.2

/-- The actual Newton seed selected by the existing extractor now lies in the
classified slope interval, so the ordinary tangent table succeeds there. -/
theorem tangentDirectionCertificate?_isSome_at_slopeShrinkingEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {direction : QI}
    (search : classifiedTangentDirection? selected = some direction)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (tangentDirectionCertificate?
      (eventPayloadIncrementalActiveOwnerForms selected)
      (slopeShrinkingEventPoint selected squarefree radius
        radiusPositive)).isSome := by
  rw [slopeShrinkingEventPoint_eq_pathValue]
  apply tangentDirectionCertificate?_isSome_of_classified_search search
  · exact slopeShrinkingEventParameter_lower selected squarefree radius
      radiusPositive
  · exact slopeShrinkingEventParameter_upper selected squarefree radius
      radiusPositive

/-! ## Direct localization of the final slope-classified cell -/

/-- Rational event point obtained from the final common slope-sign cell and
localized directly against a later winding-one owner box. -/
def slopeLocalizedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : QI :=
  localizedCellPoint output (selectedSlopeInputCell selected) squarefree next

def slopeLocalizedEventApproximationWidth
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : ℚ :=
  eventSourceApproximationWidth (selectedSlopeInputCell selected) squarefree
    (localizedClearance output next)

theorem slopeLocalizedEventApproximationWidth_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    0 < slopeLocalizedEventApproximationWidth selected squarefree next :=
  eventSourceApproximationWidth_pos (selectedSlopeInputCell selected)
    squarefree (localizedClearance output next)

def slopeLocalizedEventParameter
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) : ℚ :=
  ((selectedSlopeInputCell selected).clearedApproximation
    (slopeLocalizedEventApproximationWidth selected squarefree next)
    (slopeLocalizedEventApproximationWidth_pos selected squarefree next)).refined.interval.lower

theorem slopeLocalizedEventPoint_eq_pathValue
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    slopeLocalizedEventPoint selected squarefree next =
      selected.candidate.sourceEvent.partition.entry.chart.path.value
        (slopeLocalizedEventParameter selected squarefree next) := by
  rfl

theorem slopeLocalizedEventParameter_lower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    (selectedSlopeSigns selected).refined.interval.lower ≤
      slopeLocalizedEventParameter selected squarefree next := by
  let cell := selectedSlopeInputCell selected
  let approximation := cell.clearedApproximation
    (slopeLocalizedEventApproximationWidth selected squarefree next)
    (slopeLocalizedEventApproximationWidth_pos selected squarefree next)
  exact (cell.branch.computeEventSigns cell.parent).refines.1.trans
    approximation.refines.1

theorem slopeLocalizedEventParameter_upper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    slopeLocalizedEventParameter selected squarefree next ≤
      (selectedSlopeSigns selected).refined.interval.upper := by
  let cell := selectedSlopeInputCell selected
  let approximation := cell.clearedApproximation
    (slopeLocalizedEventApproximationWidth selected squarefree next)
    (slopeLocalizedEventApproximationWidth_pos selected squarefree next)
  exact (approximation.refined.proper.le.trans approximation.refines.2).trans
    (cell.branch.computeEventSigns cell.parent).refines.2

/-- The final slope-classified rational point is already strictly inside the
requested later owner box. -/
theorem slopeLocalizedEventPoint_strictContains
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
    (nextRefines : next.box.Refines output.state.box) :
    next.box.StrictContains
      (slopeLocalizedEventPoint selected squarefree next) := by
  exact localizedCellPoint_strictContains output
    (selectedSlopeInputCell selected) squarefree degreeNonzero elimination next
    nextRefines

/-- The fixed classified vector is a genuine tangent direction at the point
which is already inside the requested owner box. -/
def slopeLocalizedClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient) :
    TangentDirection (eventPayloadIncrementalActiveOwnerForms selected)
      (slopeLocalizedEventPoint selected squarefree next) :=
  { vector := classifiedDirection
    normSqLeOne := coordinateDirection_normSq_le_one
      (classifiedTangentDirection?_some_mem search)
    slopes := by
      intro form member
      rw [slopeLocalizedEventPoint_eq_pathValue]
      let t := slopeLocalizedEventParameter selected squarefree next
      have lower := slopeLocalizedEventParameter_lower selected squarefree next
      have upper := slopeLocalizedEventParameter_upper selected squarefree next
      have rootLower :
          (selected.candidate.inputCell.branch.computeEventSigns
            selected.candidate.inputCell.parent).refined.interval.lower ≤ t :=
        (selectedSlopeSigns_refines_inputCell selected).1.trans lower
      have rootUpper : t ≤
          (selected.candidate.inputCell.branch.computeEventSigns
            selected.candidate.inputCell.parent).refined.interval.upper :=
        upper.trans (selectedSlopeSigns_refines_inputCell selected).2
      have denominator :=
        selected.candidate.inputCell.path_denominator_ne_on_cell
          rootLower rootUpper
      apply (eval_clearedDirectionalSlope_pos_iff form
        (selectedPath selected) classifiedDirection t denominator).1
      exact classifiedTangentDirection?_some_clearedSlopes search lower upper
        form member }

/-- Localize after shrinking only the later state's stored clearance.  The
underlying winding box is definitionally unchanged. -/
def slopeCappedLocalizedEventPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) : QI :=
  slopeLocalizedEventPoint selected squarefree
    (cappedClearanceState next cap capPositive)

/-- The doubly shrunken event clearance satisfies the same linear cap used
by the active-residual estimate. -/
theorem localizedClearance_cappedState_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    (localizedClearance output
      (cappedClearanceState next cap capPositive)).bound ≤
        512 * denseLipschitzBound p (nearbyAmbient output.state.box) * cap := by
  let capped := cappedClearanceState next cap capPositive
  calc
    (localizedClearance output capped).bound ≤
        localizationClearanceCap output capped :=
      shrinkBoundaryClearance_bound_le_cap output.state.clearance _ _
    _ ≤ 512 * denseLipschitzBound p (nearbyAmbient output.state.box) *
          localizationRadius capped := min_le_right _ _
    _ ≤ 512 * denseLipschitzBound p (nearbyAmbient output.state.box) * cap := by
      exact mul_le_mul_of_nonneg_left
        (localizationRadius_cappedClearanceState_le_cap next cap capPositive)
        (mul_nonneg (by norm_num)
          (denseLipschitzBound_pos p
            (nearbyAmbient output.state.box)).le)

theorem slopeCappedLocalizedEventPoint_strictContains
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
    next.box.StrictContains
      (slopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive) := by
  let capped := cappedClearanceState next cap capPositive
  have cappedRefines : capped.box.Refines output.state.box := by
    simpa only [capped, cappedClearanceState_box] using nextRefines
  simpa only [slopeCappedLocalizedEventPoint, capped,
    cappedClearanceState_box] using
      slopeLocalizedEventPoint_strictContains output selected squarefree
        degreeNonzero elimination capped cappedRefines

/-- A positive cap no larger than the exact residual at zero forces the capped
localized event point itself to be nonzero.  Such a cap exists precisely in
the non-root case and supplies the encoder side condition without borrowing
an unrelated represented sample. -/
theorem slopeCappedLocalizedEventPoint_ne_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap)
    (capLe : cap ≤ normSq (p.eval 0)) :
    slopeCappedLocalizedEventPoint selected squarefree next cap capPositive ≠
      0 := by
  let capped := cappedClearanceState next cap capPositive
  have residual := localizedCellPoint_residual_lt output
    (selectedSlopeInputCell selected) squarefree capped
  have clearanceLe : capped.clearance.bound / 8 ≤ cap / 8 := by
    gcongr
    simpa only [capped] using
      cappedClearanceState_clearance_le next cap capPositive
  have capDivLe : cap / 8 ≤ normSq (p.eval 0) := by
    apply (div_le_self capPositive.le (by norm_num : (1 : ℚ) ≤ 8)).trans
    exact capLe
  intro zero
  have pointZero : localizedCellPoint output (selectedSlopeInputCell selected)
      squarefree capped = 0 := by
    simpa only [slopeCappedLocalizedEventPoint, slopeLocalizedEventPoint,
      capped] using zero
  rw [pointZero] at residual
  exact (not_lt_of_ge (clearanceLe.trans capDivLe)) residual

/-- The fixed classified vector remains a tangent direction at every capped
localized point. -/
def slopeCappedLocalizedClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    TangentDirection (eventPayloadIncrementalActiveOwnerForms selected)
      (slopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive) :=
  slopeLocalizedClassifiedTangentDirection search squarefree
    (cappedClearanceState next cap capPositive)

/-- Proof-bearing tangent certificate using the classified table vector
itself.  Keeping this vector fixed is useful for the later uniform radius
bound; it does not depend on which earlier successful entry the ordinary
pointwise search might return. -/
def slopeShrinkingClassifiedTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    TangentDirection (eventPayloadIncrementalActiveOwnerForms selected)
      (slopeShrinkingEventPoint selected squarefree radius radiusPositive) :=
  { vector := classifiedDirection
    normSqLeOne := coordinateDirection_normSq_le_one
      (classifiedTangentDirection?_some_mem search)
    slopes := by
      intro form member
      rw [slopeShrinkingEventPoint_eq_pathValue]
      let t := slopeShrinkingEventParameter selected squarefree radius
        radiusPositive
      have lower := slopeShrinkingEventParameter_lower selected squarefree
        radius radiusPositive
      have upper := slopeShrinkingEventParameter_upper selected squarefree
        radius radiusPositive
      have rootLower :
          (selected.candidate.inputCell.branch.computeEventSigns
            selected.candidate.inputCell.parent).refined.interval.lower ≤ t :=
        (selectedSlopeSigns_refines_inputCell selected).1.trans lower
      have rootUpper : t ≤
          (selected.candidate.inputCell.branch.computeEventSigns
            selected.candidate.inputCell.parent).refined.interval.upper :=
        upper.trans (selectedSlopeSigns_refines_inputCell selected).2
      have denominator :=
        selected.candidate.inputCell.path_denominator_ne_on_cell
          rootLower rootUpper
      apply (eval_clearedDirectionalSlope_pos_iff form
        (selectedPath selected) classifiedDirection t denominator).1
      exact classifiedTangentDirection?_some_clearedSlopes search lower upper
        form member }

/-- Constructively unwrap the successful finite tangent search.  The data is
still computed by the option-valued table; the proof only rules out `none`. -/
def slopeShrinkingEventTangentDirection
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    TangentDirection (eventPayloadIncrementalActiveOwnerForms selected)
      (slopeShrinkingEventPoint selected squarefree radius radiusPositive) :=
  (tangentDirectionCertificate?
    (eventPayloadIncrementalActiveOwnerForms selected)
    (slopeShrinkingEventPoint selected squarefree radius
      radiusPositive)).get
        (tangentDirectionCertificate?_isSome_at_slopeShrinkingEventPoint
          search squarefree radius radiusPositive)

theorem slopeShrinkingEventTangentDirection_search
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    tangentDirectionCertificate?
        (eventPayloadIncrementalActiveOwnerForms selected)
        (slopeShrinkingEventPoint selected squarefree radius radiusPositive) =
      some (slopeShrinkingEventTangentDirection search squarefree radius
        radiusPositive) := by
  exact (Option.some_get
    (tangentDirectionCertificate?_isSome_at_slopeShrinkingEventPoint
      search squarefree radius radiusPositive)).symm

theorem shrinkingEventBandRadius_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    eventBandRadius squarefree
        (shrinkingEventClearance output radius radiusPositive) ≤ radius := by
  apply eventBandRadius_le_of_clearance_bound squarefree
  exact shrinkBoundaryClearance_bound_le_cap output.state.clearance
    (512 * denseLipschitzBound p (nearbyAmbient output.state.box) * radius)
    (mul_pos
      (mul_pos (by norm_num)
        (denseLipschitzBound_pos p (nearbyAmbient output.state.box)))
      radiusPositive)

/-- Uniform horizontal width bound for an arbitrary shrinking parser-event
state. -/
theorem shrinkingInputEventState_widthX_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {denominatorState cellState : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate denominatorState.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell cellState event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (shrinkingInputEventState cell squarefree elimination radius
      radiusPositive).box.widthX ≤ 4 * radius := by
  exact (eventWindingOneState_widthX_le output.state.refinesAmbient cell
    squarefree (shrinkingEventClearance output radius radiusPositive)
    elimination).trans (mul_le_mul_of_nonneg_left
      (shrinkingEventBandRadius_le output squarefree radius radiusPositive)
      (by norm_num))

/-- Uniform vertical width bound for an arbitrary shrinking parser-event
state. -/
theorem shrinkingInputEventState_widthY_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {denominatorState cellState : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate denominatorState.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell cellState event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (shrinkingInputEventState cell squarefree elimination radius
      radiusPositive).box.widthY ≤ 4 * radius := by
  exact (eventWindingOneState_widthY_le output.state.refinesAmbient cell
    squarefree (shrinkingEventClearance output radius radiusPositive)
    elimination).trans (mul_le_mul_of_nonneg_left
      (shrinkingEventBandRadius_le output squarefree radius radiusPositive)
      (by norm_num))

/-- The rational approximation produced from an arbitrary event cell lies in
its shrinking winding-one state. -/
theorem shrinkingInputEventState_contains_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {denominatorState cellState : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate denominatorState.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell cellState event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (shrinkingInputEventState cell squarefree elimination radius
      radiusPositive).box.Contains
        (shrinkingInputEventPoint cell squarefree radius radiusPositive) :=
  eventWindingOneState_contains_sourcePoint output.state.refinesAmbient cell
    squarefree (shrinkingEventClearance output radius radiusPositive)
    elimination

theorem shrinkingEventStatePayload_widthX_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (shrinkingEventStatePayload selected squarefree elimination radius
      radiusPositive).box.widthX ≤ 4 * radius := by
  exact (eventWindingOneState_widthX_le output.state.refinesAmbient
    selected.candidate.inputCell squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination).trans
      (mul_le_mul_of_nonneg_left
        (shrinkingEventBandRadius_le output squarefree radius radiusPositive)
        (by norm_num))

theorem shrinkingEventStatePayload_widthY_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (shrinkingEventStatePayload selected squarefree elimination radius
      radiusPositive).box.widthY ≤ 4 * radius := by
  exact (eventWindingOneState_widthY_le output.state.refinesAmbient
    selected.candidate.inputCell squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination).trans
      (mul_le_mul_of_nonneg_left
        (shrinkingEventBandRadius_le output squarefree radius radiusPositive)
        (by norm_num))

theorem shrinkingEventStatePayload_contains_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (shrinkingEventStatePayload selected squarefree elimination radius
      radiusPositive).box.Contains
        (shrinkingEventPointPayload selected squarefree radius radiusPositive) :=
  eventWindingOneState_contains_sourcePoint output.state.refinesAmbient
    selected.candidate.inputCell squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination

theorem shrinkingEventState_widthX_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (shrinkingEventState selected squarefree elimination radius
      radiusPositive).box.widthX ≤ 4 * radius := by
  exact (eventWindingOneState_widthX_le output.state.refinesAmbient
    selected.candidate.inputCell squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination).trans
      (mul_le_mul_of_nonneg_left
        (shrinkingEventBandRadius_le output squarefree radius radiusPositive)
        (by norm_num))

theorem shrinkingEventState_widthY_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (shrinkingEventState selected squarefree elimination radius
      radiusPositive).box.widthY ≤ 4 * radius := by
  exact (eventWindingOneState_widthY_le output.state.refinesAmbient
    selected.candidate.inputCell squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination).trans
      (mul_le_mul_of_nonneg_left
        (shrinkingEventBandRadius_le output squarefree radius radiusPositive)
        (by norm_num))

theorem shrinkingEventState_contains_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (shrinkingEventState selected squarefree elimination radius
      radiusPositive).box.Contains
        (shrinkingEventPoint selected squarefree radius radiusPositive) := by
  exact eventWindingOneState_contains_sourcePoint output.state.refinesAmbient
    selected.candidate.inputCell squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination

theorem guardedShrinkingEventState_widthX_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (guardedShrinkingEventState selected squarefree elimination radius
      radiusPositive).box.widthX ≤ 4 * radius := by
  change
    (shrinkingEventStatePayload selected.toPayload.toIncrementalPayload squarefree elimination radius
      radiusPositive).box.widthX ≤ 4 * radius
  exact shrinkingEventStatePayload_widthX_le selected.toPayload.toIncrementalPayload squarefree
    elimination radius radiusPositive

theorem guardedShrinkingEventState_widthY_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (guardedShrinkingEventState selected squarefree elimination radius
      radiusPositive).box.widthY ≤ 4 * radius := by
  change
    (shrinkingEventStatePayload selected.toPayload.toIncrementalPayload squarefree elimination radius
      radiusPositive).box.widthY ≤ 4 * radius
  exact shrinkingEventStatePayload_widthY_le selected.toPayload.toIncrementalPayload squarefree
    elimination radius radiusPositive

theorem guardedShrinkingEventState_contains_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedGuardEventCount output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (guardedShrinkingEventState selected squarefree elimination radius
      radiusPositive).box.Contains
        (guardedShrinkingEventPoint selected squarefree radius
          radiusPositive) := by
  change
    (shrinkingEventStatePayload selected.toPayload.toIncrementalPayload squarefree elimination radius
      radiusPositive).box.Contains
        (shrinkingEventPointPayload selected.toPayload.toIncrementalPayload squarefree radius
          radiusPositive)
  exact shrinkingEventStatePayload_contains_point selected.toPayload.toIncrementalPayload squarefree
    elimination radius radiusPositive

theorem slopeShrinkingEventState_widthX_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (slopeShrinkingEventState selected squarefree elimination radius
      radiusPositive).box.widthX ≤ 4 * radius := by
  exact (eventWindingOneState_widthX_le output.state.refinesAmbient
    (selectedSlopeInputCell selected) squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination).trans
      (mul_le_mul_of_nonneg_left
        (shrinkingEventBandRadius_le output squarefree radius radiusPositive)
        (by norm_num))

theorem slopeShrinkingEventState_widthY_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (slopeShrinkingEventState selected squarefree elimination radius
      radiusPositive).box.widthY ≤ 4 * radius := by
  exact (eventWindingOneState_widthY_le output.state.refinesAmbient
    (selectedSlopeInputCell selected) squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination).trans
      (mul_le_mul_of_nonneg_left
        (shrinkingEventBandRadius_le output squarefree radius radiusPositive)
        (by norm_num))

theorem slopeShrinkingEventState_contains_point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (slopeShrinkingEventState selected squarefree elimination radius
      radiusPositive).box.Contains
        (slopeShrinkingEventPoint selected squarefree radius
          radiusPositive) := by
  exact eventWindingOneState_contains_sourcePoint output.state.refinesAmbient
    (selectedSlopeInputCell selected) squarefree
    (shrinkingEventClearance output radius radiusPositive) elimination

theorem refineState_widthX_le_request
    {p : GaussianPolynomial} {ambient : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (state : WindingOneState p ambient)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (refineState squarefree elimination state radius radiusPositive).box.widthX ≤
      radius := by
  have accurate := refineState_accurate squarefree elimination state radius
    radiusPositive
  rw [RatBox.diagonalSq_eq] at accurate
  have widthNonnegative :=
    (refineState squarefree elimination state radius radiusPositive).box.widthX_nonneg
  have otherSquareNonnegative : 0 ≤
      (refineState squarefree elimination state radius
        radiusPositive).box.widthY ^ 2 := sq_nonneg _
  nlinarith

theorem refineState_widthY_le_request
    {p : GaussianPolynomial} {ambient : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (state : WindingOneState p ambient)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (refineState squarefree elimination state radius radiusPositive).box.widthY ≤
      radius := by
  have accurate := refineState_accurate squarefree elimination state radius
    radiusPositive
  rw [RatBox.diagonalSq_eq] at accurate
  have widthNonnegative :=
    (refineState squarefree elimination state radius radiusPositive).box.widthY_nonneg
  have otherSquareNonnegative : 0 ≤
      (refineState squarefree elimination state radius
        radiusPositive).box.widthX ^ 2 := sq_nonneg _
  nlinarith

/-- Maximality compares the current track with every positive parser event,
not merely with an event whose canonical owner check has already selected a
bit.  Both arbitrarily small winding-one states lie strictly inside the same
displayed owner box, so they cannot be separated. -/
theorem shrinkingInputEventState_not_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {denominatorState cellState : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate denominatorState.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell cellState event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    ¬(shrinkingInputEventState cell squarefree elimination radius
        radiusPositive).box.Separated
      (refineState squarefree elimination next radius radiusPositive).box := by
  intro separated
  have eventInside : StrictInterior
      (shrinkingInputEventState cell squarefree elimination radius
        radiusPositive).box output.state.box :=
    eventWindingOneState_strictInterior output.state.refinesAmbient cell
      squarefree (shrinkingEventClearance output radius radiusPositive)
      elimination
  have innerStrict := refineState_strictInterior squarefree elimination next
    radius radiusPositive
  have innerInside : StrictInterior
      (refineState squarefree elimination next radius radiusPositive).box
      output.state.box :=
    { left := lt_of_le_of_lt nextRefines.1 innerStrict.left
      right := lt_of_lt_of_le innerStrict.right nextRefines.2.1
      bottom := lt_of_le_of_lt nextRefines.2.2.1 innerStrict.bottom
      top := lt_of_lt_of_le innerStrict.top nextRefines.2.2.2 }
  exact separated_states_not_both_inside_windingOne p R hR squarefree
    degreeNonzero elimination output.state
    (shrinkingInputEventState cell squarefree elimination radius
      radiusPositive)
    (refineState squarefree elimination next radius radiusPositive)
    eventInside innerInside separated

/-- Two positive parser events retained in nested denominator boxes represent
the same winding-one track.  Their independently constructed shrinking event
states therefore cannot be separated inside the earlier winding-one box. -/
theorem shrinkingInputEventStates_not_separated_of_refinement
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {firstDenominatorState secondDenominatorState : RawParser.State}
    {firstCellState secondCellState : RawParser.State}
    {firstOutput : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate firstDenominatorState.matrix)}
    {secondOutput : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      firstOutput.state (adjugate secondDenominatorState.matrix)}
    {firstPath secondPath : ProjectivePath.Path}
    {firstEvent : RelevantCurveEvent p firstPath firstOutput.state.box}
    {secondEvent : RelevantCurveEvent p secondPath secondOutput.state.box}
    (firstCell : InputEventCell firstCellState firstEvent)
    (secondCell : InputEventCell secondCellState secondEvent)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    ¬(shrinkingInputEventState firstCell squarefree elimination radius
        radiusPositive).box.Separated
      (shrinkingInputEventState secondCell squarefree elimination radius
        radiusPositive).box := by
  intro separated
  have firstInside : StrictInterior
      (shrinkingInputEventState firstCell squarefree elimination radius
        radiusPositive).box firstOutput.state.box :=
    eventWindingOneState_strictInterior firstOutput.state.refinesAmbient
      firstCell squarefree
      (shrinkingEventClearance firstOutput radius radiusPositive) elimination
  have secondLocal : StrictInterior
      (shrinkingInputEventState secondCell squarefree elimination radius
        radiusPositive).box secondOutput.state.box :=
    eventWindingOneState_strictInterior secondOutput.state.refinesAmbient
      secondCell squarefree
      (shrinkingEventClearance secondOutput radius radiusPositive) elimination
  have secondInside : StrictInterior
      (shrinkingInputEventState secondCell squarefree elimination radius
        radiusPositive).box firstOutput.state.box :=
    { left := lt_of_le_of_lt secondOutput.refines.1 secondLocal.left
      right := lt_of_lt_of_le secondLocal.right secondOutput.refines.2.1
      bottom := lt_of_le_of_lt secondOutput.refines.2.2.1 secondLocal.bottom
      top := lt_of_lt_of_le secondLocal.top secondOutput.refines.2.2.2 }
  exact separated_states_not_both_inside_windingOne p R hR squarefree
    degreeNonzero elimination firstOutput.state
    (shrinkingInputEventState firstCell squarefree elimination radius
      radiusPositive)
    (shrinkingInputEventState secondCell squarefree elimination radius
      radiusPositive)
    firstInside secondInside separated

/-- Quantitative event-to-event form of the same-track identification: two
positive event approximations in nested denominator boxes have coordinate
distance at most sixteen times the requested shrinking radius. -/
theorem shrinkingInputEventPoints_distance_of_refinement
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {firstDenominatorState secondDenominatorState : RawParser.State}
    {firstCellState secondCellState : RawParser.State}
    {firstOutput : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate firstDenominatorState.matrix)}
    {secondOutput : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      firstOutput.state (adjugate secondDenominatorState.matrix)}
    {firstPath secondPath : ProjectivePath.Path}
    {firstEvent : RelevantCurveEvent p firstPath firstOutput.state.box}
    {secondEvent : RelevantCurveEvent p secondPath secondOutput.state.box}
    (firstCell : InputEventCell firstCellState firstEvent)
    (secondCell : InputEventCell secondCellState secondEvent)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    let firstPoint := shrinkingInputEventPoint firstCell squarefree radius
      radiusPositive
    let secondPoint := shrinkingInputEventPoint secondCell squarefree radius
      radiusPositive
    |firstPoint.re - secondPoint.re| +
        |firstPoint.im - secondPoint.im| ≤ 16 * radius := by
  let firstPoint := shrinkingInputEventPoint firstCell squarefree radius
    radiusPositive
  let secondPoint := shrinkingInputEventPoint secondCell squarefree radius
    radiusPositive
  have distance := coordinateDistanceSum_le
    (shrinkingInputEventState_contains_point firstCell squarefree elimination
      radius radiusPositive)
    (shrinkingInputEventState_contains_point secondCell squarefree elimination
      radius radiusPositive)
    (shrinkingInputEventStates_not_separated_of_refinement firstCell secondCell
      squarefree degreeNonzero elimination radius radiusPositive)
    (shrinkingInputEventState_widthX_le firstCell squarefree elimination radius
      radiusPositive)
    (shrinkingInputEventState_widthY_le firstCell squarefree elimination radius
      radiusPositive)
    (shrinkingInputEventState_widthX_le secondCell squarefree elimination radius
      radiusPositive)
    (shrinkingInputEventState_widthY_le secondCell squarefree elimination radius
      radiusPositive)
  simpa only [firstPoint, secondPoint] using distance.trans_eq (by ring)

theorem shrinkingEventStatePayload_not_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    ¬(shrinkingEventStatePayload selected squarefree elimination radius
        radiusPositive).box.Separated
      (refineState squarefree elimination next radius radiusPositive).box := by
  exact shrinkingInputEventState_not_separated
    selected.candidate.inputCell squarefree degreeNonzero elimination next
      nextRefines radius radiusPositive

/-- The arbitrarily shrunken event state and the equally accurate later
track state cannot acquire a positive coordinate gap inside their common
winding-one owner. -/
theorem shrinkingEventState_not_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    ¬(shrinkingEventState selected squarefree elimination radius
        radiusPositive).box.Separated
      (refineState squarefree elimination next radius radiusPositive).box := by
  change
    ¬(shrinkingEventStatePayload selected squarefree elimination radius
        radiusPositive).box.Separated
      (refineState squarefree elimination next radius radiusPositive).box
  exact shrinkingEventStatePayload_not_separated selected squarefree
    degreeNonzero elimination next nextRefines radius radiusPositive

theorem guardedShrinkingEventState_not_separated
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
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    ¬(guardedShrinkingEventState selected squarefree elimination radius
        radiusPositive).box.Separated
      (refineState squarefree elimination next radius radiusPositive).box := by
  change
    ¬(shrinkingEventStatePayload selected.toPayload.toIncrementalPayload squarefree elimination radius
        radiusPositive).box.Separated
      (refineState squarefree elimination next radius radiusPositive).box
  exact shrinkingEventStatePayload_not_separated selected.toPayload.toIncrementalPayload squarefree
    degreeNonzero elimination next nextRefines radius radiusPositive

/-- The slope-refined event extraction represents the same winding-one track,
so maximality supplies the identical nonseparation bound. -/
theorem slopeShrinkingEventState_not_separated
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    ¬(slopeShrinkingEventState selected squarefree elimination radius
        radiusPositive).box.Separated
      (refineState squarefree elimination next radius radiusPositive).box := by
  intro separated
  have eventInside : StrictInterior
      (slopeShrinkingEventState selected squarefree elimination radius
        radiusPositive).box output.state.box := by
    exact eventWindingOneState_strictInterior output.state.refinesAmbient
      (selectedSlopeInputCell selected) squarefree
      (shrinkingEventClearance output radius radiusPositive) elimination
  have innerStrict := refineState_strictInterior squarefree elimination next
    radius radiusPositive
  have innerInside : StrictInterior
      (refineState squarefree elimination next radius radiusPositive).box
      output.state.box :=
    { left := lt_of_le_of_lt nextRefines.1 innerStrict.left
      right := lt_of_lt_of_le innerStrict.right nextRefines.2.1
      bottom := lt_of_le_of_lt nextRefines.2.2.1 innerStrict.bottom
      top := lt_of_lt_of_le innerStrict.top nextRefines.2.2.2 }
  exact separated_states_not_both_inside_windingOne p R hR squarefree
    degreeNonzero elimination output.state
    (slopeShrinkingEventState selected squarefree elimination radius
      radiusPositive)
    (refineState squarefree elimination next radius radiusPositive)
    eventInside innerInside separated

/-- The persistent old-prefix sample chosen in the same requested-width
refinement used by the event convergence argument. -/
def convergentGridBase
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) : GridBase current next :=
  let inner := refineState squarefree elimination next radius radiusPositive
  gridBaseOfCurrentRefinement current next inner
    (nextRefines.trans separation.refines)
    (refineState_strictInterior squarefree elimination next radius
      radiusPositive)

theorem convergentGridBase_inside_inner
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (refineState squarefree elimination next radius radiusPositive).box.Contains
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point := by
  let inner := refineState squarefree elimination next radius radiusPositive
  let nested := nextRefines.trans separation.refines
  let strict := refineState_strictInterior squarefree elimination next radius
    radiusPositive
  let outcome := current.sampleInRefinement inner (strict.refines.trans nested)
  change inner.box.Contains outcome.point
  exact outcome.inside

/-- Every convergence base exposes the coupled state's fixed historical form
list; refinement changes only the rational witness. -/
theorem convergentGridBase_priors
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (convergentGridBase current separation squarefree elimination next
      nextRefines radius radiusPositive).priors = current.priors := by
  simpa only [convergentGridBase, gridBaseOfCurrentRefinement,
    GridBase.ofStrictRefinement] using
      current.sampleInRefinement_priors
        (refineState squarefree elimination next radius radiusPositive)
        ((refineState_strictInterior squarefree elimination next radius
          radiusPositive).refines.trans
            (nextRefines.trans separation.refines))

/-- Every convergence base also retains the fixed orientation of each
historical form relative to the coupled state's anchor sample. -/
theorem convergentGridBase_sameSigns
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (form : HermitianForm) (member : form ∈ current.priors) :
    0 < form.eval current.sample *
      form.eval (convergentGridBase current separation squarefree elimination
        next nextRefines radius radiusPositive).point := by
  simpa only [convergentGridBase, gridBaseOfCurrentRefinement,
    GridBase.ofStrictRefinement] using
      current.sampleInRefinement_sameSigns
        (refineState squarefree elimination next radius radiusPositive)
        ((refineState_strictInterior squarefree elimination next radius
          radiusPositive).refines.trans
            (nextRefines.trans separation.refines)) form member

/-- Owner-independent convergence between any positive parser-event
approximation and the coupled track's represented rational base.  This is the
metric form needed for all-`neither` event cells, whose geometry is valid even
though no selected-owner payload exists. -/
theorem convergentGridBase_inputEvent_distance
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path separation.state.box}
    (cell : InputEventCell (RawParser.parse current.word) event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    let eventPoint := shrinkingInputEventPoint cell squarefree radius
      radiusPositive
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| ≤
      10 * radius := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventState := shrinkingInputEventState cell squarefree elimination radius
    radiusPositive
  let eventPoint := shrinkingInputEventPoint cell squarefree radius
    radiusPositive
  let inner := refineState squarefree elimination next radius radiusPositive
  have distance := coordinateDistanceSum_le
    (shrinkingInputEventState_contains_point cell squarefree elimination radius
      radiusPositive)
    (convergentGridBase_inside_inner current separation squarefree elimination
      next nextRefines radius radiusPositive)
    (shrinkingInputEventState_not_separated cell squarefree degreeNonzero
      elimination next nextRefines radius radiusPositive)
    (shrinkingInputEventState_widthX_le cell squarefree elimination radius
      radiusPositive)
    (shrinkingInputEventState_widthY_le cell squarefree elimination radius
      radiusPositive)
    (refineState_widthX_le_request squarefree elimination next radius
      radiusPositive)
    (refineState_widthY_le_request squarefree elimination next radius
      radiusPositive)
  calc
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| =
        |eventPoint.re - base.point.re| + |eventPoint.im - base.point.im| := by
      rw [abs_sub_comm base.point.re eventPoint.re,
        abs_sub_comm base.point.im eventPoint.im]
    _ ≤ 2 * (4 * radius + radius) := by
      simpa only [base, eventState, eventPoint, inner] using distance
    _ = 10 * radius := by ring

/-! ## Sample-free convergence base -/

/-- The center of the independently refined winding box is a canonical
rational convergence base.  Unlike `convergentGridBase`, it carries no
represented-prefix or historical-sign data. -/
def convergentBoxCenter
    {p : GaussianPolynomial} {ambient : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (radius : ℚ) (radiusPositive : 0 < radius) : QI :=
  (refineState squarefree elimination next radius radiusPositive).box.center

theorem convergentBoxCenter_inside_inner
    {p : GaussianPolynomial} {ambient : RatBox}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p ambient)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    (refineState squarefree elimination next radius radiusPositive).box.Contains
      (convergentBoxCenter squarefree elimination next radius
        radiusPositive) := by
  simpa only [convergentBoxCenter] using
    (RatBox.contains_center
      (refineState squarefree elimination next radius radiusPositive).box)

/-- Owner-independent convergence to an isolated positive event using only
the nested winding boxes.  The represented sample in the legacy grid-base
statement played no role in this metric estimate. -/
theorem convergentBoxCenter_inputEvent_distance
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    let base := convergentBoxCenter squarefree elimination next radius
      radiusPositive
    let eventPoint := shrinkingInputEventPoint cell squarefree radius
      radiusPositive
    |base.re - eventPoint.re| + |base.im - eventPoint.im| ≤
      10 * radius := by
  let base := convergentBoxCenter squarefree elimination next radius
    radiusPositive
  let eventState := shrinkingInputEventState cell squarefree elimination radius
    radiusPositive
  let eventPoint := shrinkingInputEventPoint cell squarefree radius
    radiusPositive
  let inner := refineState squarefree elimination next radius radiusPositive
  have distance := coordinateDistanceSum_le
    (shrinkingInputEventState_contains_point cell squarefree elimination radius
      radiusPositive)
    (convergentBoxCenter_inside_inner squarefree elimination next radius
      radiusPositive)
    (shrinkingInputEventState_not_separated cell squarefree degreeNonzero
      elimination next nextRefines radius radiusPositive)
    (shrinkingInputEventState_widthX_le cell squarefree elimination radius
      radiusPositive)
    (shrinkingInputEventState_widthY_le cell squarefree elimination radius
      radiusPositive)
    (refineState_widthX_le_request squarefree elimination next radius
      radiusPositive)
    (refineState_widthY_le_request squarefree elimination next radius
      radiusPositive)
  calc
    |base.re - eventPoint.re| + |base.im - eventPoint.im| =
        |eventPoint.re - base.re| + |eventPoint.im - base.im| := by
      rw [abs_sub_comm base.re eventPoint.re,
        abs_sub_comm base.im eventPoint.im]
    _ ≤ 2 * (4 * radius + radius) := by
      simpa only [base, eventState, eventPoint, inner] using distance
    _ = 10 * radius := by ring

/-- Cell-representation-independent convergence between a selected event
approximation and the coupled track's represented rational base. -/
theorem convergentGridBase_eventPayload_distance
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    let eventPoint := shrinkingEventPointPayload selected squarefree radius
      radiusPositive
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| ≤
      10 * radius := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventState := shrinkingEventStatePayload selected squarefree elimination
    radius radiusPositive
  let eventPoint := shrinkingEventPointPayload selected squarefree radius
    radiusPositive
  let inner := refineState squarefree elimination next radius radiusPositive
  have distance := coordinateDistanceSum_le
    (shrinkingEventStatePayload_contains_point selected squarefree elimination
      radius radiusPositive)
    (convergentGridBase_inside_inner current separation squarefree elimination
      next nextRefines radius radiusPositive)
    (shrinkingEventStatePayload_not_separated selected squarefree degreeNonzero
      elimination next nextRefines radius radiusPositive)
    (shrinkingEventStatePayload_widthX_le selected squarefree elimination radius
      radiusPositive)
    (shrinkingEventStatePayload_widthY_le selected squarefree elimination radius
      radiusPositive)
    (refineState_widthX_le_request squarefree elimination next radius
      radiusPositive)
    (refineState_widthY_le_request squarefree elimination next radius
      radiusPositive)
  calc
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| =
        |eventPoint.re - base.point.re| + |eventPoint.im - base.point.im| := by
      rw [abs_sub_comm base.point.re eventPoint.re,
        abs_sub_comm base.point.im eventPoint.im]
    _ ≤ 2 * (4 * radius + radius) := by
      simpa only [base, eventState, eventPoint, inner] using distance
    _ = 10 * radius := by ring

/-- The two independently computed rational points are within ten times the
common requested radius in coordinate-sum distance. -/
theorem convergentGridBase_event_distance
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    let eventPoint := shrinkingEventPoint selected squarefree radius radiusPositive
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| ≤
      10 * radius := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventState := shrinkingEventState selected squarefree elimination radius
    radiusPositive
  let eventPoint := shrinkingEventPoint selected squarefree radius radiusPositive
  let inner := refineState squarefree elimination next radius radiusPositive
  have distance := coordinateDistanceSum_le
    (shrinkingEventState_contains_point selected squarefree elimination radius
      radiusPositive)
    (convergentGridBase_inside_inner current separation squarefree elimination
      next nextRefines radius radiusPositive)
    (shrinkingEventState_not_separated selected squarefree degreeNonzero
      elimination next nextRefines radius radiusPositive)
    (shrinkingEventState_widthX_le selected squarefree elimination radius
      radiusPositive)
    (shrinkingEventState_widthY_le selected squarefree elimination radius
      radiusPositive)
    (refineState_widthX_le_request squarefree elimination next radius
      radiusPositive)
    (refineState_widthY_le_request squarefree elimination next radius
      radiusPositive)
  calc
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| =
        |eventPoint.re - base.point.re| + |eventPoint.im - base.point.im| := by
      rw [abs_sub_comm base.point.re eventPoint.re,
        abs_sub_comm base.point.im eventPoint.im]
    _ ≤ 2 * (4 * radius + radius) := by
      simpa only [base, eventState, eventPoint, inner] using distance
    _ = 10 * radius := by ring

theorem convergentGridBase_guarded_event_distance
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedGuardEventCount separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    let eventPoint := guardedShrinkingEventPoint selected squarefree radius
      radiusPositive
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| ≤
      10 * radius := by
  change
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    let eventPoint := shrinkingEventPointPayload selected.toPayload.toIncrementalPayload squarefree
      radius radiusPositive
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| ≤
      10 * radius
  exact convergentGridBase_eventPayload_distance current separation
    selected.toPayload.toIncrementalPayload squarefree degreeNonzero elimination next nextRefines
    radius radiusPositive

/-- Distance form using the event extraction whose source parameter is inside
the classified tangent-sign cell. -/
theorem convergentGridBase_slope_event_distance
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    let eventPoint := slopeShrinkingEventPoint selected squarefree radius
      radiusPositive
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| ≤
      10 * radius := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventState := slopeShrinkingEventState selected squarefree elimination
    radius radiusPositive
  let eventPoint := slopeShrinkingEventPoint selected squarefree radius
    radiusPositive
  let inner := refineState squarefree elimination next radius radiusPositive
  have distance := coordinateDistanceSum_le
    (slopeShrinkingEventState_contains_point selected squarefree elimination
      radius radiusPositive)
    (convergentGridBase_inside_inner current separation squarefree elimination
      next nextRefines radius radiusPositive)
    (slopeShrinkingEventState_not_separated selected squarefree degreeNonzero
      elimination next nextRefines radius radiusPositive)
    (slopeShrinkingEventState_widthX_le selected squarefree elimination radius
      radiusPositive)
    (slopeShrinkingEventState_widthY_le selected squarefree elimination radius
      radiusPositive)
    (refineState_widthX_le_request squarefree elimination next radius
      radiusPositive)
    (refineState_widthY_le_request squarefree elimination next radius
      radiusPositive)
  calc
    |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| =
        |eventPoint.re - base.point.re| +
          |eventPoint.im - base.point.im| := by
      rw [abs_sub_comm base.point.re eventPoint.re,
        abs_sub_comm base.point.im eventPoint.im]
    _ ≤ 2 * (4 * radius + radius) := by
      simpa only [base, eventState, eventPoint, inner] using distance
    _ = 10 * radius := by ring

/-- Any tangent certificate at the rational event approximation transfers to
the independently represented base once the existing `10·radius` distance
bound is below its computed stability radius. -/
def convergentGridBase_tangentDirection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {forms : List HermitianForm}
    (direction : TangentDirection forms
      (shrinkingEventPoint selected squarefree radius radiusPositive))
    (stable : 10 * radius <
      FTA.CCLTangentStability.tangentStabilityRadius direction) :
    TangentDirection forms
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point := by
  apply FTA.CCLTangentStability.TangentDirection.atNearby direction
  unfold FTA.CCLTangentStability.coordinateDistance
  exact (convergentGridBase_event_distance current separation selected
    squarefree degreeNonzero elimination next nextRefines radius
    radiusPositive).trans_lt stable

/-- Computed request-radius cap that leaves half of a displayed event
certificate's tangent-stability margin after the `10·radius` transfer bound. -/
def eventTangentRadiusCap
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) : ℚ :=
  FTA.CCLTangentStability.tangentStabilityRadius direction / 20

theorem eventTangentRadiusCap_pos
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) :
    0 < eventTangentRadiusCap direction := by
  exact div_pos
    (FTA.CCLTangentStability.tangentStabilityRadius_pos direction)
    (by norm_num)

theorem ten_mul_eventTangentRadiusCap_lt_stabilityRadius
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) :
    10 * eventTangentRadiusCap direction <
      FTA.CCLTangentStability.tangentStabilityRadius direction := by
  unfold eventTangentRadiusCap
  have positive :=
    FTA.CCLTangentStability.tangentStabilityRadius_pos direction
  linarith

/-- Uniform tangent-stability lower bound obtained from the classified
whole-cell slope margin rather than from a radius-dependent pointwise search. -/
def selectedSlopeTangentRadiusLower
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  FTA.Maximality.positiveMinimum
    ((eventPayloadIncrementalActiveOwnerForms selected).map fun form =>
      selectedSlopeDirectionalLower selected /
        (2 * FTA.CCLTangentStability.slopeVariationCoefficient form))

theorem selectedSlopeTangentRadiusLower_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedSlopeTangentRadiusLower selected := by
  apply FTA.Maximality.positiveMinimum_pos
  intro value member
  rw [List.mem_map] at member
  rcases member with ⟨form, _formMember, rfl⟩
  exact div_pos (selectedSlopeDirectionalLower_pos selected)
    (mul_pos (by norm_num)
      (FTA.CCLTangentStability.slopeVariationCoefficient_pos form))

theorem selectedSlopeTangentRadiusLower_le_stabilityRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    selectedSlopeTangentRadiusLower selected ≤
      FTA.CCLTangentStability.tangentStabilityRadius
        (slopeShrinkingClassifiedTangentDirection search squarefree radius
          radiusPositive) := by
  unfold FTA.CCLTangentStability.tangentStabilityRadius
  apply FTA.Maximality.le_positiveMinimum
    (FTA.Maximality.positiveMinimum_le_one _)
  intro value valueMember
  rw [List.mem_map] at valueMember
  rcases valueMember with ⟨form, formMember, rfl⟩
  have lowerMember : selectedSlopeDirectionalLower selected /
        (2 * FTA.CCLTangentStability.slopeVariationCoefficient form) ∈
      (eventPayloadIncrementalActiveOwnerForms selected).map fun item =>
        selectedSlopeDirectionalLower selected /
          (2 * FTA.CCLTangentStability.slopeVariationCoefficient item) :=
    List.mem_map.mpr ⟨form, formMember, rfl⟩
  apply (FTA.Maximality.positiveMinimum_le_of_mem lowerMember).trans
  have slopeLe := selectedSlopeDirectionalLower_le search
    (slopeShrinkingEventParameter_lower selected squarefree radius
      radiusPositive)
    (slopeShrinkingEventParameter_upper selected squarefree radius
      radiusPositive) formMember
  change selectedSlopeDirectionalLower selected /
      (2 * FTA.CCLTangentStability.slopeVariationCoefficient form) ≤
    directionalSlope form ((selectedPath selected).value
      (slopeShrinkingEventParameter selected squarefree radius
        radiusPositive)) classifiedDirection /
      (2 * FTA.CCLTangentStability.slopeVariationCoefficient form)
  exact (div_le_div_iff_of_pos_right (mul_pos (by norm_num)
    (FTA.CCLTangentStability.slopeVariationCoefficient_pos form))).2 slopeLe

/-- Fixed positive request-radius cap guaranteeing transfer of the classified
vector from every slope-refined event seed. -/
def selectedSlopeEventRadiusCap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  selectedSlopeTangentRadiusLower selected / 20

theorem selectedSlopeEventRadiusCap_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedSlopeEventRadiusCap selected :=
  div_pos (selectedSlopeTangentRadiusLower_pos selected) (by norm_num)

theorem selectedSlopeEventRadiusCap_le_eventTangentRadiusCap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output} {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    selectedSlopeEventRadiusCap selected ≤ eventTangentRadiusCap
      (slopeShrinkingClassifiedTangentDirection search squarefree radius
        radiusPositive) := by
  apply (div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 20)).2
  exact selectedSlopeTangentRadiusLower_le_stabilityRadius search squarefree
    radius radiusPositive

/-- Fixed-cap transfer theorem used by the bounded persistent sampler. -/
def convergentGridBase_classifiedTangentDirection
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusLe : radius ≤ selectedSlopeEventRadiusCap selected) :
    TangentDirection
      (eventPayloadActiveForms current selected
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point := by
  let direction := slopeShrinkingClassifiedTangentDirection search squarefree
    radius radiusPositive
  apply FTA.CCLTangentStability.TangentDirection.atNearby direction
  unfold FTA.CCLTangentStability.coordinateDistance
  apply (convergentGridBase_slope_event_distance current separation selected
    squarefree degreeNonzero elimination next nextRefines radius
    radiusPositive).trans_lt
  have radiusLePoint : radius ≤ eventTangentRadiusCap direction :=
    radiusLe.trans (selectedSlopeEventRadiusCap_le_eventTangentRadiusCap
      search squarefree radius radiusPositive)
  exact (mul_le_mul_of_nonneg_left radiusLePoint (by norm_num)).trans_lt
    (ten_mul_eventTangentRadiusCap_lt_stabilityRadius direction)

theorem tangentDirectionCertificate?_isSome_at_convergentGridBase_of_fixed_cap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusLe : radius ≤ selectedSlopeEventRadiusCap selected) :
    (tangentDirectionCertificate?
      (eventPayloadActiveForms current selected
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point).isSome := by
  let direction := convergentGridBase_classifiedTangentDirection current
    separation selected squarefree degreeNonzero elimination next nextRefines
    search radius radiusPositive radiusLe
  exact tangentDirectionCertificate?_isSome_of_mem
    (classifiedTangentDirection?_some_mem search) direction.slopes

/-- Transfer the tangent direction computed at the slope-refined Newton seed
to the independently represented grid base. -/
def convergentGridBase_tangentDirection_of_classified_search
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusLe : radius ≤ eventTangentRadiusCap
      (slopeShrinkingEventTangentDirection search squarefree radius
        radiusPositive)) :
    TangentDirection
      (eventPayloadActiveForms current selected
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point := by
  let direction := slopeShrinkingEventTangentDirection search squarefree
    radius radiusPositive
  apply FTA.CCLTangentStability.TangentDirection.atNearby direction
  unfold FTA.CCLTangentStability.coordinateDistance
  apply (convergentGridBase_slope_event_distance current separation selected
    squarefree degreeNonzero elimination next nextRefines radius
    radiusPositive).trans_lt
  exact (mul_le_mul_of_nonneg_left radiusLe (by norm_num)).trans_lt
    (ten_mul_eventTangentRadiusCap_lt_stabilityRadius direction)

/-- Proposition-facing success of the actual table at the represented base,
under the same computed radius cap. -/
theorem tangentDirectionCertificate?_isSome_at_convergentGridBase_of_classified_search
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    {classifiedDirection : QI}
    (search : classifiedTangentDirection? selected = some classifiedDirection)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusLe : radius ≤ eventTangentRadiusCap
      (slopeShrinkingEventTangentDirection search squarefree radius
        radiusPositive)) :
    (tangentDirectionCertificate?
      (eventPayloadActiveForms current selected
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point).isSome := by
  let direction := slopeShrinkingEventTangentDirection search squarefree
    radius radiusPositive
  apply FTA.CCLTangentStability.tangentDirectionCertificate?_isSome_atNearby
    (slopeShrinkingEventTangentDirection_search search squarefree radius
      radiusPositive)
  unfold FTA.CCLTangentStability.coordinateDistance
  apply (convergentGridBase_slope_event_distance current separation selected
    squarefree degreeNonzero elimination next nextRefines radius
    radiusPositive).trans_lt
  exact (mul_le_mul_of_nonneg_left radiusLe (by norm_num)).trans_lt
    (ten_mul_eventTangentRadiusCap_lt_stabilityRadius direction)

/-- Radius-cap form of tangent transfer, with no free continuity inequality. -/
def convergentGridBase_tangentDirection_of_le_cap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {forms : List HermitianForm}
    (direction : TangentDirection forms
      (shrinkingEventPoint selected squarefree radius radiusPositive))
    (radiusLe : radius ≤ eventTangentRadiusCap direction) :
    TangentDirection forms
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point := by
  apply convergentGridBase_tangentDirection current separation selected
    squarefree degreeNonzero elimination next nextRefines radius radiusPositive
    direction
  exact (mul_le_mul_of_nonneg_left radiusLe (by norm_num)).trans_lt
    (ten_mul_eventTangentRadiusCap_lt_stabilityRadius direction)

/-- The transferred certificate may simultaneously discard inactive faces or
reuse duplicate obligations at the represented base. -/
def convergentGridBase_tangentDirection_of_le_cap_of_subset
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {supporting forms : List HermitianForm}
    (direction : TangentDirection supporting
      (shrinkingEventPoint selected squarefree radius radiusPositive))
    (radiusLe : radius ≤ eventTangentRadiusCap direction)
    (subset : ∀ form ∈ forms, form ∈ supporting) :
    TangentDirection forms
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point := by
  apply FTA.CCLTangentStability.TangentDirection.atNearbySubset direction _ _
    subset
  unfold FTA.CCLTangentStability.coordinateDistance
  apply (convergentGridBase_event_distance current separation selected
    squarefree degreeNonzero elimination next nextRefines radius
    radiusPositive).trans_lt
  exact (mul_le_mul_of_nonneg_left radiusLe (by norm_num)).trans_lt
    (ten_mul_eventTangentRadiusCap_lt_stabilityRadius direction)

/-- Proposition-facing form for the actual executable direction search. -/
theorem tangentDirectionCertificate?_isSome_at_convergentGridBase
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    {forms : List HermitianForm}
    {direction : TangentDirection forms
      (shrinkingEventPoint selected squarefree radius radiusPositive)}
    (search : tangentDirectionCertificate? forms
      (shrinkingEventPoint selected squarefree radius radiusPositive) =
        some direction)
    (stable : 10 * radius <
      FTA.CCLTangentStability.tangentStabilityRadius direction) :
    (tangentDirectionCertificate? forms
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point).isSome := by
  apply FTA.CCLTangentStability.tangentDirectionCertificate?_isSome_atNearby
    search
  unfold FTA.CCLTangentStability.coordinateDistance
  exact (convergentGridBase_event_distance current separation selected
    squarefree degreeNonzero elimination next nextRefines radius
    radiusPositive).trans_lt stable

def shrinkingEventApproximationWidth
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) : ℚ :=
  eventSourceApproximationWidth selected.candidate.inputCell squarefree
    (shrinkingEventClearance output radius radiusPositive)

theorem shrinkingEventApproximationWidth_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    0 < shrinkingEventApproximationWidth selected squarefree radius
      radiusPositive :=
  eventSourceApproximationWidth_pos selected.candidate.inputCell squarefree
    (shrinkingEventClearance output radius radiusPositive)

theorem shrinkingEventPoint_eq_selectedApproximationPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    shrinkingEventPoint selected squarefree radius radiusPositive =
      selectedApproximationPoint selected
        (shrinkingEventApproximationWidth selected squarefree radius
          radiusPositive)
      (shrinkingEventApproximationWidth_pos selected squarefree radius
          radiusPositive) := by
  rfl

/-- Any extracted event cell whose stored clearance is below the standard
linear cap has a correspondingly bounded parameter-refinement width. -/
theorem eventSourceApproximationWidth_le_of_clearance_bound
    {p : GaussianPolynomial} {path : FTA.ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p box)
    (radius : ℚ)
    (clearanceLe : clearance.bound ≤
      512 * denseLipschitzBound p (nearbyAmbient box) * radius) :
    eventSourceApproximationWidth cell squarefree clearance ≤
      32 * denseLipschitzBound p (nearbyAmbient box) * radius := by
  let threshold := eventSourceResidualThreshold squarefree clearance
  let majorant := cell.affineApproximationMajorant
  have widthLeAffine : eventSourceApproximationWidth cell squarefree clearance ≤
      cell.affineApproximationWidth threshold := by
    exact min_le_left _ _
  have affineLeRatio : cell.affineApproximationWidth threshold ≤
      threshold / majorant := min_le_right _ _
  have thresholdPositive : 0 < threshold :=
    eventSourceResidualThreshold_pos squarefree clearance
  have majorantPositive : 0 < majorant :=
    cell.affineApproximationMajorant_pos
  have majorantOne : 1 ≤ majorant := le_max_left _ _
  have ratioLeThreshold : threshold / majorant ≤ threshold := by
    apply (div_le_iff₀ majorantPositive).2
    nlinarith
  have thresholdLeClearance : threshold ≤ clearance.bound / 16 :=
    eventSourceResidualThreshold_le_clearance squarefree clearance
  calc
    eventSourceApproximationWidth cell squarefree clearance ≤
        cell.affineApproximationWidth threshold := widthLeAffine
    _ ≤ threshold / majorant := affineLeRatio
    _ ≤ threshold := ratioLeThreshold
    _ ≤ clearance.bound / 16 := thresholdLeClearance
    _ ≤ (512 * denseLipschitzBound p (nearbyAmbient box) * radius) / 16 := by
      gcongr
    _ = 32 * denseLipschitzBound p (nearbyAmbient box) * radius := by ring

/-- Linear coefficient for an arbitrary event-factor multiple.  Unlike the
selected-owner coefficient below, this definition needs neither a chosen bit
nor a tangent classification. -/
def inputEventFormCoefficient
    {p : GaussianPolynomial} {path : FTA.ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (form : HermitianForm) : ℚ :=
  approximationCoefficient (clearedForm form path)
      cell.branch.factor.polynomial
      (cell.branch.computeEventSigns cell.parent).refined *
    (32 * denseLipschitzBound p (nearbyAmbient box)) /
      (CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
        event).bound

theorem inputEventFormCoefficient_nonneg
    {p : GaussianPolynomial} {path : FTA.ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (form : HermitianForm) :
    0 ≤ inputEventFormCoefficient cell form := by
  apply div_nonneg
  · exact mul_nonneg (approximationCoefficient_nonneg _ _ _)
      (mul_nonneg (by norm_num)
        (denseLipschitzBound_pos p (nearbyAmbient box)).le)
  · exact (CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
      event).positive.le

/-- A condition that is canonically nonzero has the same strict sign at the
owner-independent shrinking event point.  This is the arbitrary-event
counterpart of the selected-owner strict-sign transfer and is useful when a
whole-box decision must be transported to an algebraic event oracle. -/
theorem inputEventCanonicalValue_mul_shrinkingPoint_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {denominatorState cellState : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate denominatorState.matrix)}
    {path : FTA.ProjectivePath.Path}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell cellState event)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) (form : HermitianForm)
    (member : clearedForm form path ∈ inputEventPolynomials cellState path)
    (canonicalNonzero : inputEventCanonicalValue cell form ≠ 0) :
    0 < inputEventCanonicalValue cell form *
      form.eval (shrinkingInputEventPoint cell squarefree radius
        radiusPositive) := by
  let clearance := shrinkingEventClearance output radius radiusPositive
  let epsilon := eventSourceApproximationWidth cell squarefree clearance
  let epsilonPositive : 0 < epsilon :=
    eventSourceApproximationWidth_pos cell squarefree clearance
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let t := approximation.refined.interval.lower
  let signs := cell.branch.computeEventSigns cell.parent
  have lower : signs.refined.interval.lower ≤ t := by
    exact approximation.refines.1
  have upper : t ≤ signs.refined.interval.upper := by
    exact approximation.refined.proper.le.trans approximation.refines.2
  have polynomialSign :=
    ConditionRelations.canonicalEventValue_mul_eval_pos
      cell.branch.relations cell.parent signs member (by
        simpa only [inputEventCanonicalValue] using canonicalNonzero)
      lower upper
  have denominator :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
    apply cell.path_denominator_ne_on_cell
    · exact approximation.refines.1
    · exact approximation.refined.proper.le.trans approximation.refines.2
  have denominatorPositive :
      0 < (denominatorNorm path).eval t :=
    CCLPathIntersection.eval_denominatorNorm_pos path t denominator
  rw [eval_clearedForm form path t denominator] at polynomialSign
  have rearranged :
      0 < (denominatorNorm path).eval t *
        (inputEventCanonicalValue cell form *
          form.eval (shrinkingInputEventPoint cell squarefree radius
            radiusPositive)) := by
    simpa only [inputEventCanonicalValue, shrinkingInputEventPoint,
      eventSourcePoint, clearance, epsilon, epsilonPositive, approximation,
      t, signs, mul_assoc, mul_left_comm, mul_comm] using polynomialSign
  rcases mul_pos_iff.mp rearranged with positive | negative
  · exact positive.2
  · exact (not_lt_of_ge denominatorPositive.le negative.1).elim

/-- Every cleared form divisible by an arbitrary positive event factor is
linearly small at the owner-independent shrinking source point.  This is the
quantitative bridge from all-`neither` residual divisibility to the isolated
terminal input excluded by the coupled controller. -/
theorem shrinkingInputEventForm_le_of_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {denominatorState cellState : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate denominatorState.matrix)}
    {path : FTA.ProjectivePath.Path}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell cellState event)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) (form : HermitianForm)
    (divides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form path).toPolynomial) :
    |form.eval (shrinkingInputEventPoint cell squarefree radius
      radiusPositive)| ≤ inputEventFormCoefficient cell form * radius := by
  let clearance := shrinkingEventClearance output radius radiusPositive
  let width := eventSourceApproximationWidth cell squarefree clearance
  let coefficient := approximationCoefficient (clearedForm form path)
    cell.branch.factor.polynomial
    (cell.branch.computeEventSigns cell.parent).refined
  let cap := 32 * denseLipschitzBound p
    (nearbyAmbient output.state.box) * radius
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
      clearance radius
    exact shrinkBoundaryClearance_bound_le_cap output.state.clearance
      (512 * denseLipschitzBound p (nearbyAmbient output.state.box) * radius)
      (mul_pos
        (mul_pos (by norm_num)
          (denseLipschitzBound_pos p (nearbyAmbient output.state.box)))
        radiusPositive)
  have numeratorLe : coefficient * width ≤ coefficient * cap :=
    mul_le_mul_of_nonneg_left widthLe
      (approximationCoefficient_nonneg _ _ _)
  calc
    |form.eval (shrinkingInputEventPoint cell squarefree radius
        radiusPositive)| =
        |form.eval (eventSourcePoint cell squarefree clearance)| := rfl
    _ ≤ coefficient * width / denominator.bound := raw
    _ ≤ coefficient * cap / denominator.bound :=
      div_le_div_of_nonneg_right numeratorLe denominator.positive.le
    _ = inputEventFormCoefficient cell form * radius := by
      dsimp only [inputEventFormCoefficient, coefficient, cap, denominator]
      ring

/-- If an all-`neither` event factor divides a completed-sector residual,
the shrinking event point approaches the corresponding isolated terminal
input at an explicit linear rate. -/
theorem shrinkingInputEvent_terminal_distance_le_of_residual_dvd
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {path : FTA.ProjectivePath.Path}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (determinantNonzero : determinant state.matrix ≠ 0)
    {terminalPoint : QI}
    (terminal : CCLTerminalSeparation.terminalInputForBit? state bit =
      some terminalPoint)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (divides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
        (pullbackForm (adjugate state.matrix)
          (residualForm kind exponent
            (RawParser.sectorOfBits first second bit))) path).toPolynomial) :
    let sector := RawParser.sectorOfBits first second bit
    let normalized := normalizedMatrix kind exponent RawParser.identityMatrix
    let u := normalized.a - sector.rep * normalized.c
    let v := normalized.b - sector.rep * normalized.d
    let inverse := adjugate state.matrix
    let transformedU := u * inverse.a + v * inverse.c
    normSq (shrinkingInputEventPoint cell squarefree radius radiusPositive -
        terminalPoint) ≤
      inputEventFormCoefficient cell
          (pullbackForm inverse (residualForm kind exponent sector)) /
        normSq transformedU * radius := by
  let sector := RawParser.sectorOfBits first second bit
  let normalized := normalizedMatrix kind exponent RawParser.identityMatrix
  let u := normalized.a - sector.rep * normalized.c
  let v := normalized.b - sector.rep * normalized.d
  let inverse := adjugate state.matrix
  let transformedU := u * inverse.a + v * inverse.c
  let transformedV := u * inverse.b + v * inverse.d
  let form := pullbackForm inverse (residualForm kind exponent sector)
  let eventPoint := shrinkingInputEventPoint cell squarefree radius
    radiusPositive
  rcases CCLTerminalSeparation.terminalInputForBit_affineResidual state kind
      exponent first second bit phase determinantNonzero terminal with
    ⟨transformedUNonzero, terminalZero, formShape⟩
  have transformedUNonzero' : transformedU ≠ 0 := by
    simpa only [transformedU, u, v, normalized, inverse, sector] using
      transformedUNonzero
  have terminalZero' : transformedU * terminalPoint + transformedV = 0 := by
    simpa only [transformedU, transformedV, u, v, normalized, inverse, sector]
      using terminalZero
  have formShape' : form = affineNormForm transformedU transformedV := by
    simpa only [form, transformedU, transformedV, u, v, normalized, inverse,
      sector] using formShape
  have small : |form.eval eventPoint| ≤
      inputEventFormCoefficient cell form * radius := by
    apply shrinkingInputEventForm_le_of_dvd cell squarefree radius
      radiusPositive form
    simpa only [form, inverse, sector] using divides
  have evaluation : form.eval eventPoint =
      normSq transformedU * normSq (eventPoint - terminalPoint) := by
    rw [formShape']
    exact eval_affineNorm_eq_normSq_mul_distance_of_root transformedU
      transformedV terminalPoint eventPoint terminalZero'
  have evaluationNonnegative : 0 ≤ form.eval eventPoint := by
    rw [evaluation]
    exact mul_nonneg (normSq_nonneg transformedU)
      (normSq_nonneg (eventPoint - terminalPoint))
  rw [abs_of_nonneg evaluationNonnegative, evaluation] at small
  have transformedUNormPositive : 0 < normSq transformedU :=
    normSq_pos transformedUNonzero'
  have divided : normSq (eventPoint - terminalPoint) ≤
      (inputEventFormCoefficient cell form * radius) / normSq transformedU := by
    apply (le_div_iff₀ transformedUNormPositive).2
    simpa only [_root_.mul_comm] using small
  calc
    normSq (shrinkingInputEventPoint cell squarefree radius radiusPositive -
        terminalPoint) = normSq (eventPoint - terminalPoint) := rfl
    _ ≤ (inputEventFormCoefficient cell form * radius) /
        normSq transformedU := divided
    _ = inputEventFormCoefficient cell
          (pullbackForm inverse (residualForm kind exponent sector)) /
        normSq transformedU * radius := by
      dsimp only [form]
      field_simp

/-- Residual divisibility cannot select the projective terminal at infinity.
In that case the pulled-back residual is a nonzero constant times the path
denominator norm, while every relevant event factor is certified coprime to
that denominator. -/
theorem terminalInputForBit?_isSome_of_residual_dvd
    {p : GaussianPolynomial} {box : RatBox} {state : RawParser.State}
    {path : FTA.ProjectivePath.Path}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (determinantNonzero : determinant state.matrix ≠ 0)
    (divides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
        (pullbackForm (adjugate state.matrix)
          (residualForm kind exponent
            (RawParser.sectorOfBits first second bit))) path).toPolynomial) :
    ∃ terminalPoint,
      CCLTerminalSeparation.terminalInputForBit? state bit =
        some terminalPoint := by
  cases terminal : CCLTerminalSeparation.terminalInputForBit? state bit with
  | some terminalPoint => exact ⟨terminalPoint, rfl⟩
  | none =>
      let sector := RawParser.sectorOfBits first second bit
      let normalized := normalizedMatrix kind exponent RawParser.identityMatrix
      let u := normalized.a - sector.rep * normalized.c
      let v := normalized.b - sector.rep * normalized.d
      let inverse := adjugate state.matrix
      let transformedU := u * inverse.a + v * inverse.c
      let transformedV := u * inverse.b + v * inverse.d
      rcases CCLTerminalSeparation.terminalInputForBit_none_affineResidual
          state kind exponent first second bit phase determinantNonzero
          terminal with ⟨_transformedUZero, transformedVNonzero, formShape⟩
      have dividesConstant : cell.branch.factor.polynomial.toPolynomial ∣
          Polynomial.C (normSq transformedV) *
            (denominatorNorm path).toPolynomial := by
        rw [formShape,
          toPolynomial_clearedForm_affineNorm_zero_linear] at divides
        simpa only [sector, normalized, u, v, inverse, transformedU,
          transformedV] using divides
      have scaleNonzero : normSq transformedV ≠ 0 :=
        (normSq_pos transformedVNonzero).ne'
      have scaleUnit : IsUnit (Polynomial.C (normSq transformedV)) :=
        Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr scaleNonzero)
      have denominatorDivides : cell.branch.factor.polynomial.toPolynomial ∣
          (denominatorNorm path).toPolynomial :=
        scaleUnit.dvd_mul_left.mp dividesConstant
      let condition := CCLBranchEvent.denominatorCoprimeCondition event.branch
        event.denominatorNonEquality
      have denominatorDivides' :
          cell.branch.factor.polynomial.toPolynomial ∣
            condition.polynomial.toPolynomial := by
        simpa only [condition,
          CCLBranchEvent.denominatorCoprimeCondition_polynomial] using
            denominatorDivides
      have unit := condition.coprime.isCoprime.isUnit_of_dvd'
        cell.divides denominatorDivides'
      have degree := Polynomial.natDegree_eq_zero_of_isUnit unit
      rw [FTA.ComputablePolynomial.DensePolynomial.natDegree_toPolynomial
        cell.branch.factor.input.nonzero] at degree
      exact (cell.branch.factor.input.nonconstant degree).elim

/-- Terminal separation rules out residual divisibility for any positive
all-`neither` event carried by the same winding-one track.  The proof chooses
one explicit radius below the excluded terminal's coordinate margin and then
combines the two linear convergence estimates. -/
theorem inputEvent_residual_not_dvd_of_terminalSeparation
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    {path : FTA.ProjectivePath.Path}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path separation.state.box}
    (cell : InputEventCell (RawParser.parse current.word) event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse current.word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    {terminalPoint : QI}
    (terminal : CCLTerminalSeparation.terminalInputForBit?
      (RawParser.parse current.word) bit = some terminalPoint) :
    ¬cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
        (pullbackForm (adjugate (RawParser.parse current.word).matrix)
          (residualForm kind exponent
            (RawParser.sectorOfBits first second bit))) path).toPolynomial := by
  intro divides
  let state := RawParser.parse current.word
  let sector := RawParser.sectorOfBits first second bit
  let normalized := normalizedMatrix kind exponent RawParser.identityMatrix
  let u := normalized.a - sector.rep * normalized.c
  let v := normalized.b - sector.rep * normalized.d
  let inverse := adjugate state.matrix
  let transformedU := u * inverse.a + v * inverse.c
  let transformedV := u * inverse.b + v * inverse.d
  let form := pullbackForm inverse (residualForm kind exponent sector)
  have determinantNonzero : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  rcases CCLTerminalSeparation.terminalInputForBit_affineResidual state kind
      exponent first second bit (by simpa only [state] using phase)
      determinantNonzero (by simpa only [state] using terminal) with
    ⟨transformedUNonzero, _terminalZero, _formShape⟩
  have transformedUNonzero' : transformedU ≠ 0 := by
    simpa only [transformedU, u, v, normalized, inverse, sector, state] using
      transformedUNonzero
  let coefficient := inputEventFormCoefficient cell form / normSq transformedU
  have coefficientNonnegative : 0 ≤ coefficient := by
    exact div_nonneg (inputEventFormCoefficient_nonneg cell form)
      (normSq_nonneg transformedU)
  have terminalExcluded : ¬terminalOutput.numerical.box.Contains terminalPoint :=
    terminalOutput.excludes bit (by cases bit <;> simp) terminal
  let side := CCLDenominator.outsideSide terminalExcluded
  let margin := side.margin
  have marginPositive : 0 < margin := side.margin_pos
  let radius := min 1 (margin / (400 * (1 + coefficient)))
  have coefficientDenominatorPositive : 0 < 400 * (1 + coefficient) := by
    positivity
  have radiusPositive : 0 < radius := by
    exact lt_min zero_lt_one
      (div_pos marginPositive coefficientDenominatorPositive)
  have radiusLeOne : radius ≤ 1 := min_le_left _ _
  have radiusLeRatio : radius ≤
      margin / (400 * (1 + coefficient)) := min_le_right _ _
  have scaledRadius : 400 * (1 + coefficient) * radius ≤ margin :=
    by
      simpa only [_root_.mul_comm] using
        (le_div_iff₀ coefficientDenominatorPositive).mp radiusLeRatio
  have nextRefinesSeparation : next.box.Refines separation.state.box :=
    nextRefines.trans terminalOutput.refines
  let base := convergentGridBase current separation squarefree elimination next
    nextRefinesSeparation radius radiusPositive
  let eventPoint := shrinkingInputEventPoint cell squarefree radius radiusPositive
  have baseInsideNext : next.box.Contains base.point := by
    apply (refineState_strictInterior squarefree elimination next radius
      radiusPositive).refines.contains
    exact convergentGridBase_inside_inner current separation squarefree
      elimination next nextRefinesSeparation radius radiusPositive
  have lowerDistance : margin ≤ normSq (base.point - terminalPoint) := by
    exact side.margin_le_normSq_sub (nextRefines.contains baseInsideNext)
  have baseEventCoordinates :
      |base.point.re - eventPoint.re| + |base.point.im - eventPoint.im| ≤
        10 * radius := by
    simpa only [base, eventPoint] using
      convergentGridBase_inputEvent_distance current separation cell squarefree
        degreeNonzero elimination next nextRefinesSeparation radius
          radiusPositive
  have baseEventDistance : normSq (base.point - eventPoint) ≤
      100 * radius ^ 2 := by
    have coordinatesNonnegative : 0 ≤
        |base.point.re - eventPoint.re| +
          |base.point.im - eventPoint.im| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    have radiusTenNonnegative : 0 ≤ 10 * radius := by positivity
    have squareBound :
        (|base.point.re - eventPoint.re| +
          |base.point.im - eventPoint.im|) ^ 2 ≤ (10 * radius) ^ 2 := by
      nlinarith
    simp only [normSq, sub_re, sub_im]
    rw [show (100 : ℚ) * radius ^ 2 = (10 * radius) ^ 2 by ring]
    calc
      (base.point.re - eventPoint.re) ^ 2 +
          (base.point.im - eventPoint.im) ^ 2 ≤
        (|base.point.re - eventPoint.re| +
          |base.point.im - eventPoint.im|) ^ 2 := by
            rw [← sq_abs (base.point.re - eventPoint.re),
              ← sq_abs (base.point.im - eventPoint.im)]
            nlinarith [mul_nonneg (abs_nonneg
              (base.point.re - eventPoint.re))
              (abs_nonneg (base.point.im - eventPoint.im))]
      _ ≤ (10 * radius) ^ 2 := squareBound
  have eventTerminalDistance : normSq (eventPoint - terminalPoint) ≤
      coefficient * radius := by
    have bound := shrinkingInputEvent_terminal_distance_le_of_residual_dvd
      cell squarefree kind exponent first second bit phase determinantNonzero
      terminal radius radiusPositive divides
    simpa only [eventPoint, coefficient, form, inverse, transformedU, u, v,
      normalized, sector, state] using bound
  have decomposition : base.point - terminalPoint =
      (base.point - eventPoint) + (eventPoint - terminalPoint) := by
    apply GaussianRat.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;>
      ring
  have upperDistance : normSq (base.point - terminalPoint) ≤
      2 * (100 * radius ^ 2 + coefficient * radius) := by
    rw [decomposition]
    apply (normSq_add_le_two (base.point - eventPoint)
      (eventPoint - terminalPoint)).trans
    gcongr
  have radiusSquareLe : radius ^ 2 ≤ radius := by nlinarith
  have upperStrict :
      2 * (100 * radius ^ 2 + coefficient * radius) < margin := by
    have coarse :
        2 * (100 * radius ^ 2 + coefficient * radius) ≤
          200 * (1 + coefficient) * radius := by
      nlinarith
    have halfMargin : 200 * (1 + coefficient) * radius ≤ margin / 2 := by
      nlinarith
    exact coarse.trans_lt (halfMargin.trans_lt (by linarith))
  exact (lowerDistance.trans_lt (upperDistance.trans_lt upperStrict)).false

/-- Terminal-output form with the affine/projective split discharged
internally. -/
theorem inputEvent_residual_not_dvd_of_terminalOutput
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    {path : FTA.ProjectivePath.Path}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path separation.state.box}
    (cell : InputEventCell (RawParser.parse current.word) event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse current.word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second)) :
    ¬cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
        (pullbackForm (adjugate (RawParser.parse current.word).matrix)
          (residualForm kind exponent
            (RawParser.sectorOfBits first second bit))) path).toPolynomial := by
  intro divides
  have determinantNonzero :
      determinant (RawParser.parse current.word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  rcases terminalInputForBit?_isSome_of_residual_dvd cell kind exponent first
      second bit phase determinantNonzero divides with
    ⟨terminalPoint, terminal⟩
  exact inputEvent_residual_not_dvd_of_terminalSeparation current separation
    cell squarefree degreeNonzero elimination terminalOutput next nextRefines
      kind exponent first second bit phase terminal divides

/-! ## Sample-free completed-sector exclusion -/

/-- The completed-sector terminal contradiction needs only the numerical
winding state, raw word, and independently shrinking box center.  In
particular, no represented rational base or persistent prior list is used. -/
theorem inputEvent_residual_not_dvd_of_terminalSeparationData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    {path : FTA.ProjectivePath.Path}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path
      separation.state.box}
    (cell : InputEventCell (RawParser.parse word) event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (phase : (RawParser.parse word).phase =
      .sector kind exponent (.two first second))
    {terminalPoint : QI}
    (terminal : CCLTerminalSeparation.terminalInputForBit?
      (RawParser.parse word) bit = some terminalPoint) :
    ¬cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
        (pullbackForm (adjugate (RawParser.parse word).matrix)
          (residualForm kind exponent
            (RawParser.sectorOfBits first second bit))) path).toPolynomial := by
  intro divides
  let state := RawParser.parse word
  let sector := RawParser.sectorOfBits first second bit
  let normalized := normalizedMatrix kind exponent RawParser.identityMatrix
  let u := normalized.a - sector.rep * normalized.c
  let v := normalized.b - sector.rep * normalized.d
  let inverse := adjugate state.matrix
  let transformedU := u * inverse.a + v * inverse.c
  let transformedV := u * inverse.b + v * inverse.d
  let form := pullbackForm inverse (residualForm kind exponent sector)
  have determinantNonzero : determinant state.matrix ≠ 0 := by
    simpa only [state, determinant, Mat2.det] using
      RawParser.parse_det_ne word
  rcases CCLTerminalSeparation.terminalInputForBit_affineResidual state kind
      exponent first second bit (by simpa only [state] using phase)
      determinantNonzero (by simpa only [state] using terminal) with
    ⟨transformedUNonzero, _terminalZero, _formShape⟩
  have transformedUNonzero' : transformedU ≠ 0 := by
    simpa only [transformedU, u, v, normalized, inverse, sector, state] using
      transformedUNonzero
  let coefficient := inputEventFormCoefficient cell form / normSq transformedU
  have coefficientNonnegative : 0 ≤ coefficient := by
    exact div_nonneg (inputEventFormCoefficient_nonneg cell form)
      (normSq_nonneg transformedU)
  have terminalExcluded : ¬terminalOutput.numerical.box.Contains terminalPoint :=
    terminalOutput.excludes bit (by cases bit <;> simp) terminal
  let side := CCLDenominator.outsideSide terminalExcluded
  let margin := side.margin
  have marginPositive : 0 < margin := side.margin_pos
  let radius := min 1 (margin / (400 * (1 + coefficient)))
  have coefficientDenominatorPositive : 0 < 400 * (1 + coefficient) := by
    positivity
  have radiusPositive : 0 < radius := by
    exact lt_min zero_lt_one
      (div_pos marginPositive coefficientDenominatorPositive)
  have radiusLeOne : radius ≤ 1 := min_le_left _ _
  have radiusLeRatio : radius ≤
      margin / (400 * (1 + coefficient)) := min_le_right _ _
  have scaledRadius : 400 * (1 + coefficient) * radius ≤ margin := by
    simpa only [_root_.mul_comm] using
      (le_div_iff₀ coefficientDenominatorPositive).mp radiusLeRatio
  have nextRefinesSeparation : next.box.Refines separation.state.box :=
    nextRefines.trans terminalOutput.refines
  let base := convergentBoxCenter squarefree elimination next radius
    radiusPositive
  let eventPoint := shrinkingInputEventPoint cell squarefree radius radiusPositive
  have baseInsideNext : next.box.Contains base := by
    apply (refineState_strictInterior squarefree elimination next radius
      radiusPositive).refines.contains
    exact convergentBoxCenter_inside_inner squarefree elimination next radius
      radiusPositive
  have lowerDistance : margin ≤ normSq (base - terminalPoint) := by
    exact side.margin_le_normSq_sub (nextRefines.contains baseInsideNext)
  have baseEventCoordinates :
      |base.re - eventPoint.re| + |base.im - eventPoint.im| ≤
        10 * radius := by
    simpa only [base, eventPoint] using
      convergentBoxCenter_inputEvent_distance cell squarefree degreeNonzero
        elimination next nextRefinesSeparation radius radiusPositive
  have baseEventDistance : normSq (base - eventPoint) ≤
      100 * radius ^ 2 := by
    have coordinatesNonnegative : 0 ≤
        |base.re - eventPoint.re| + |base.im - eventPoint.im| :=
      add_nonneg (abs_nonneg _) (abs_nonneg _)
    have radiusTenNonnegative : 0 ≤ 10 * radius := by positivity
    have squareBound :
        (|base.re - eventPoint.re| + |base.im - eventPoint.im|) ^ 2 ≤
          (10 * radius) ^ 2 := by
      nlinarith
    simp only [normSq, sub_re, sub_im]
    rw [show (100 : ℚ) * radius ^ 2 = (10 * radius) ^ 2 by ring]
    calc
      (base.re - eventPoint.re) ^ 2 + (base.im - eventPoint.im) ^ 2 ≤
        (|base.re - eventPoint.re| +
          |base.im - eventPoint.im|) ^ 2 := by
            rw [← sq_abs (base.re - eventPoint.re),
              ← sq_abs (base.im - eventPoint.im)]
            nlinarith [mul_nonneg (abs_nonneg
              (base.re - eventPoint.re))
              (abs_nonneg (base.im - eventPoint.im))]
      _ ≤ (10 * radius) ^ 2 := squareBound
  have eventTerminalDistance : normSq (eventPoint - terminalPoint) ≤
      coefficient * radius := by
    have bound := shrinkingInputEvent_terminal_distance_le_of_residual_dvd
      cell squarefree kind exponent first second bit phase determinantNonzero
      terminal radius radiusPositive divides
    simpa only [eventPoint, coefficient, form, inverse, transformedU, u, v,
      normalized, sector, state] using bound
  have decomposition : base - terminalPoint =
      (base - eventPoint) + (eventPoint - terminalPoint) := by
    apply GaussianRat.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;>
      ring
  have upperDistance : normSq (base - terminalPoint) ≤
      2 * (100 * radius ^ 2 + coefficient * radius) := by
    rw [decomposition]
    apply (normSq_add_le_two (base - eventPoint)
      (eventPoint - terminalPoint)).trans
    gcongr
  have radiusSquareLe : radius ^ 2 ≤ radius := by nlinarith
  have upperStrict :
      2 * (100 * radius ^ 2 + coefficient * radius) < margin := by
    have coarse :
        2 * (100 * radius ^ 2 + coefficient * radius) ≤
          200 * (1 + coefficient) * radius := by
      nlinarith
    have halfMargin : 200 * (1 + coefficient) * radius ≤ margin / 2 := by
      nlinarith
    exact coarse.trans_lt (halfMargin.trans_lt (by linarith))
  exact (lowerDistance.trans_lt (upperDistance.trans_lt upperStrict)).false

/-- Sample-free terminal-output form with the affine/projective split
discharged internally. -/
theorem inputEvent_residual_not_dvd_of_terminalOutputData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    {path : FTA.ProjectivePath.Path}
    {event : FTA.CCLBranchEvent.RelevantCurveEvent p path
      separation.state.box}
    (cell : InputEventCell (RawParser.parse word) event)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second bit : Bool)
    (phase : (RawParser.parse word).phase =
      .sector kind exponent (.two first second)) :
    ¬cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm
        (pullbackForm (adjugate (RawParser.parse word).matrix)
          (residualForm kind exponent
            (RawParser.sectorOfBits first second bit))) path).toPolynomial := by
  intro divides
  have determinantNonzero : determinant (RawParser.parse word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using RawParser.parse_det_ne word
  rcases terminalInputForBit?_isSome_of_residual_dvd cell kind exponent first
      second bit phase determinantNonzero divides with
    ⟨terminalPoint, terminal⟩
  exact inputEvent_residual_not_dvd_of_terminalSeparationData numerical word
    separation cell squarefree degreeNonzero elimination terminalOutput next
      nextRefines kind exponent first second bit phase terminal divides

/-- Linear coefficient for active-form residuals when the approximation is
taken from the final slope-classified divisor cell. -/
def selectedSlopeActiveEventCoefficient
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (form : HermitianForm) : ℚ :=
  approximationCoefficient (clearedForm form (selectedPath selected))
      (selectedSlopeClassification selected).branch.factor.polynomial
      (selectedSlopeInputSigns selected).refined *
    (32 * denseLipschitzBound p (nearbyAmbient output.state.box)) /
      (CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
        selected.candidate.sourceEvent.event).bound

theorem selectedSlopeActiveEventCoefficient_nonneg
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (form : HermitianForm) :
    0 ≤ selectedSlopeActiveEventCoefficient selected form := by
  apply div_nonneg
  · exact mul_nonneg
      (approximationCoefficient_nonneg _ _ _)
      (mul_nonneg (by norm_num)
        (denseLipschitzBound_pos p
          (nearbyAmbient output.state.box)).le)
  · exact (CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
      selected.candidate.sourceEvent.event).positive.le

/-- Every incremental active face has a linear residual bound at the source
point of the final slope cell whenever the chosen clearance obeys the usual
linear cap. -/
theorem selectedSlopeEventSourceActive_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (clearance : BoxBoundaryClearanceCertificate p output.state.box)
    (radius : ℚ)
    (clearanceLe : clearance.bound ≤
      512 * denseLipschitzBound p (nearbyAmbient output.state.box) * radius)
    {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    |form.eval (eventSourcePoint (selectedSlopeInputCell selected) squarefree
        clearance)| ≤
      selectedSlopeActiveEventCoefficient selected form * radius := by
  let cell := selectedSlopeInputCell selected
  let width := eventSourceApproximationWidth cell squarefree clearance
  let coefficient := approximationCoefficient
    (clearedForm form (selectedPath selected))
    (selectedSlopeClassification selected).branch.factor.polynomial
    (selectedSlopeInputSigns selected).refined
  let cap := 32 * denseLipschitzBound p
    (nearbyAmbient output.state.box) * radius
  let denominator :=
    CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
      selected.candidate.sourceEvent.event
  have raw : |form.eval (eventSourcePoint cell squarefree clearance)| ≤
      coefficient * width / denominator.bound := by
    have bounded := selectedActiveAtSlopeInputCellApproximation_le selected
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
    _ = selectedSlopeActiveEventCoefficient selected form * radius := by
      dsimp only [selectedSlopeActiveEventCoefficient, coefficient, cap,
        denominator]
      ring

/-- Complete-child active faces obey the same linear residual bound.  The
coefficient is unchanged; only membership in the larger finite form list is
used to obtain divisibility by the final event factor. -/
theorem selectedSlopeCompleteEventSourceActive_le
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
    |form.eval (eventSourcePoint
        (selectedSlopeInputCell selected.toIncrementalPayload) squarefree
          clearance)| ≤
      selectedSlopeActiveEventCoefficient selected.toIncrementalPayload form *
        radius := by
  let direct := selected.toIncrementalPayload
  let cell := selectedSlopeInputCell direct
  let width := eventSourceApproximationWidth cell squarefree clearance
  let coefficient := approximationCoefficient
    (clearedForm form (selectedPath direct))
    (selectedSlopeClassification direct).branch.factor.polynomial
    (selectedSlopeInputSigns direct).refined
  let cap := 32 * denseLipschitzBound p
    (nearbyAmbient output.state.box) * radius
  let denominator :=
    CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
      direct.candidate.sourceEvent.event
  have raw : |form.eval (eventSourcePoint cell squarefree clearance)| ≤
      coefficient * width / denominator.bound := by
    have bounded := selectedCompleteActiveAtSlopeInputCellApproximation_le
      selected (eventSourceApproximationWidth_pos cell squarefree clearance)
      member
    rw [approximationBound_eq_coefficient_mul] at bounded
    change |form.eval (eventSourcePoint cell squarefree clearance)| ≤
      coefficient * width / denominator.bound at bounded
    exact bounded
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
    _ = selectedSlopeActiveEventCoefficient direct form * radius := by
      dsimp only [selectedSlopeActiveEventCoefficient, coefficient, cap,
        denominator]
      ring

theorem slopeCappedLocalizedEventActive_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap)
    {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    |form.eval (slopeCappedLocalizedEventPoint selected squarefree next cap
        capPositive)| ≤
      selectedSlopeActiveEventCoefficient selected form * cap := by
  let capped := cappedClearanceState next cap capPositive
  simpa only [slopeCappedLocalizedEventPoint, slopeLocalizedEventPoint,
    localizedCellPoint, capped] using
      selectedSlopeEventSourceActive_le selected squarefree
        (localizedClearance output capped) cap
        (localizedClearance_cappedState_le output next cap capPositive) member

/-- Every incremental strict atom keeps its selected algebraic-event sign at
the same capped localized point used by the active-residual estimate. -/
theorem slopeCappedLocalizedEventStrict
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (next : WindingOneState p ambient)
    (cap : ℚ) (capPositive : 0 < cap) :
    ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form *
        form.eval (slopeCappedLocalizedEventPoint selected squarefree next cap
          capPositive) := by
  intro form member
  let capped := cappedClearanceState next cap capPositive
  let clearance := localizedClearance output capped
  have strict := selectedStrictAtSlopeInputCellApproximation selected
    (eventSourceApproximationWidth (selectedSlopeInputCell selected)
      squarefree clearance)
    (eventSourceApproximationWidth_pos (selectedSlopeInputCell selected)
      squarefree clearance) form member
  simpa only [slopeCappedLocalizedEventPoint, slopeLocalizedEventPoint,
    localizedCellPoint, eventSourcePoint, selectedPath, capped, clearance]
    using strict

/-- Every active face in the complete selected child formula is linearly
small at the capped localized point. -/
theorem slopeCappedLocalizedEventCompleteActive_le
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
    |form.eval (slopeCappedLocalizedEventPoint selected.toIncrementalPayload
        squarefree next cap capPositive)| ≤
      selectedSlopeActiveEventCoefficient selected.toIncrementalPayload form *
        cap := by
  let capped := cappedClearanceState next cap capPositive
  simpa only [slopeCappedLocalizedEventPoint, slopeLocalizedEventPoint,
    localizedCellPoint, capped] using
      selectedSlopeCompleteEventSourceActive_le selected squarefree
        (localizedClearance output capped) cap
        (localizedClearance_cappedState_le output next cap capPositive) member

/-- Every strict face in the complete selected child formula retains its
canonical sign at the same capped localized point. -/
theorem slopeCappedLocalizedEventCompleteStrict
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
        form.eval (slopeCappedLocalizedEventPoint
          selected.toIncrementalPayload squarefree next cap capPositive) := by
  intro form member
  let capped := cappedClearanceState next cap capPositive
  let clearance := localizedClearance output capped
  have strict := selectedCompleteStrictAtSlopeInputCellApproximation selected
    (eventSourceApproximationWidth
      (selectedSlopeInputCell selected.toIncrementalPayload)
      squarefree clearance)
    (eventSourceApproximationWidth_pos
      (selectedSlopeInputCell selected.toIncrementalPayload)
      squarefree clearance) form member
  simpa only [slopeCappedLocalizedEventPoint, slopeLocalizedEventPoint,
    localizedCellPoint, eventSourcePoint, selectedPath, capped, clearance]
    using strict

/-- The event extractor's internal parameter refinement also shrinks
linearly with the requested Newton-band radius. -/
theorem shrinkingEventApproximationWidth_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    shrinkingEventApproximationWidth selected squarefree radius
        radiusPositive ≤
      32 * denseLipschitzBound p (nearbyAmbient output.state.box) * radius := by
  let clearance := shrinkingEventClearance output radius radiusPositive
  let threshold := eventSourceResidualThreshold squarefree clearance
  let cell := selected.candidate.inputCell
  let majorant := cell.affineApproximationMajorant
  have widthLeAffine : shrinkingEventApproximationWidth selected squarefree
      radius radiusPositive ≤ cell.affineApproximationWidth threshold := by
    exact min_le_left _ _
  have affineLeRatio : cell.affineApproximationWidth threshold ≤
      threshold / majorant := min_le_right _ _
  have thresholdPositive : 0 < threshold :=
    eventSourceResidualThreshold_pos squarefree clearance
  have majorantPositive : 0 < majorant :=
    cell.affineApproximationMajorant_pos
  have majorantOne : 1 ≤ majorant := le_max_left _ _
  have ratioLeThreshold : threshold / majorant ≤ threshold := by
    apply (div_le_iff₀ majorantPositive).2
    nlinarith
  have thresholdLeClearance : threshold ≤ clearance.bound / 16 :=
    eventSourceResidualThreshold_le_clearance squarefree clearance
  have clearanceLeCap : clearance.bound ≤
      512 * denseLipschitzBound p (nearbyAmbient output.state.box) * radius :=
    shrinkBoundaryClearance_bound_le_cap output.state.clearance _ _
  calc
    shrinkingEventApproximationWidth selected squarefree radius
        radiusPositive ≤ cell.affineApproximationWidth threshold := widthLeAffine
    _ ≤ threshold / majorant := affineLeRatio
    _ ≤ threshold := ratioLeThreshold
    _ ≤ clearance.bound / 16 := thresholdLeClearance
    _ ≤ (512 * denseLipschitzBound p
          (nearbyAmbient output.state.box) * radius) / 16 := by gcongr
    _ = 32 * denseLipschitzBound p
          (nearbyAmbient output.state.box) * radius := by ring

theorem shrinkingEventStrict
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) :
    ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form *
        form.eval (shrinkingEventPoint selected squarefree radius
          radiusPositive) := by
  rw [shrinkingEventPoint_eq_selectedApproximationPoint selected squarefree
    radius radiusPositive]
  exact selectedStrictAtApproximation selected _ _

def selectedActiveEventCoefficient
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (form : HermitianForm) : ℚ :=
  approximationCoefficient
      (clearedForm form
        selected.candidate.sourceEvent.partition.entry.chart.path)
      selected.candidate.inputCell.branch.factor.polynomial
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent).refined *
    (32 * denseLipschitzBound p (nearbyAmbient output.state.box)) /
      (CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
        selected.candidate.sourceEvent.event).bound

theorem selectedActiveEventCoefficient_nonneg
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (form : HermitianForm) :
    0 ≤ selectedActiveEventCoefficient selected form := by
  apply div_nonneg
  · exact mul_nonneg
      (approximationCoefficient_nonneg _ _ _)
      (mul_nonneg (by norm_num)
        (denseLipschitzBound_pos p
          (nearbyAmbient output.state.box)).le)
  · exact (CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
      selected.candidate.sourceEvent.event).positive.le

theorem shrinkingEventActive_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    |form.eval (shrinkingEventPoint selected squarefree radius radiusPositive)| ≤
      selectedActiveEventCoefficient selected form * radius := by
  let width := shrinkingEventApproximationWidth selected squarefree radius
    radiusPositive
  let coefficient := approximationCoefficient
    (clearedForm form
      selected.candidate.sourceEvent.partition.entry.chart.path)
    selected.candidate.inputCell.branch.factor.polynomial
    (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined
  let cap := 32 * denseLipschitzBound p
    (nearbyAmbient output.state.box) * radius
  let denominator :=
    CCLBranchEventOwner.RelevantCurveEvent.ownerDenominatorCertificate
      selected.candidate.sourceEvent.event
  have raw : |form.eval (shrinkingEventPoint selected squarefree radius
      radiusPositive)| ≤ coefficient * width / denominator.bound := by
    have bound := selectedActiveAtApproximation_le selected
      (shrinkingEventApproximationWidth_pos selected squarefree radius
        radiusPositive) member
    rw [← shrinkingEventPoint_eq_selectedApproximationPoint selected squarefree
      radius radiusPositive] at bound
    rw [approximationBound_eq_coefficient_mul] at bound
    simpa only [coefficient, width, denominator] using bound
  have widthLe : width ≤ cap := by
    simpa only [width, cap] using
      shrinkingEventApproximationWidth_le selected squarefree radius
        radiusPositive
  have coefficientNonnegative : 0 ≤ coefficient := by
    exact approximationCoefficient_nonneg _ _ _
  have numeratorLe : coefficient * width ≤ coefficient * cap :=
    mul_le_mul_of_nonneg_left widthLe coefficientNonnegative
  have quotientLe : coefficient * width / denominator.bound ≤
      coefficient * cap / denominator.bound := by
    exact div_le_div_of_nonneg_right numeratorLe denominator.positive.le
  calc
    |form.eval (shrinkingEventPoint selected squarefree radius radiusPositive)| ≤
        coefficient * width / denominator.bound := raw
    _ ≤ coefficient * cap / denominator.bound := quotientLe
    _ = selectedActiveEventCoefficient selected form * radius := by
      dsimp only [selectedActiveEventCoefficient, coefficient, cap, denominator]
      ring

def selectedActiveBaseCoefficient
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (form : HermitianForm) : ℚ :=
  selectedActiveEventCoefficient selected form +
    10 * variationMajorant form output.state.box

theorem selectedActiveBaseCoefficient_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) (form : HermitianForm) :
    0 < selectedActiveBaseCoefficient selected form := by
  exact add_pos_of_nonneg_of_pos
    (selectedActiveEventCoefficient_nonneg selected form)
    (mul_pos (by norm_num) (variationMajorant_pos form output.state.box))

/-- Active selected forms are explicitly small at the represented coupled
sample, not merely at the independently computed event point. -/
theorem convergentGridBase_active_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    |form.eval base.point| ≤
      selectedActiveBaseCoefficient selected form * radius := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventPoint := shrinkingEventPoint selected squarefree radius radiusPositive
  have baseInsideSeparation : separation.state.box.Contains base.point :=
    nextRefines.contains base.strict.contains
  have eventInsideSeparation : separation.state.box.Contains eventPoint := by
    have strict := eventWindingOneState_strictInterior
      separation.state.refinesAmbient selected.candidate.inputCell squarefree
      (shrinkingEventClearance separation radius radiusPositive) elimination
    exact strict.refines.contains
      (shrinkingEventState_contains_point selected squarefree elimination radius
        radiusPositive)
  have variation := abs_eval_sub_eval_le form baseInsideSeparation
    eventInsideSeparation
  have distance := convergentGridBase_event_distance current separation selected
    squarefree degreeNonzero elimination next nextRefines radius radiusPositive
  have variationLe :
      |form.eval base.point - form.eval eventPoint| ≤
        10 * variationMajorant form separation.state.box * radius := by
    apply variation.trans
    exact mul_le_mul_of_nonneg_left distance
      (variationMajorant_pos form separation.state.box).le |>.trans_eq (by ring)
  have eventLe := shrinkingEventActive_le selected squarefree radius
    radiusPositive member
  have triangle : |form.eval base.point| ≤
      |form.eval base.point - form.eval eventPoint| +
        |form.eval eventPoint| := by
    have := abs_add_le
      (form.eval base.point - form.eval eventPoint) (form.eval eventPoint)
    simpa only [sub_add_cancel] using this
  exact triangle.trans (by
    dsimp only [selectedActiveBaseCoefficient]
    calc
      |form.eval base.point - form.eval eventPoint| +
          |form.eval eventPoint| ≤
        10 * variationMajorant form separation.state.box * radius +
          selectedActiveEventCoefficient selected form * radius :=
        add_le_add variationLe eventLe
      _ = (selectedActiveEventCoefficient selected form +
          10 * variationMajorant form separation.state.box) * radius := by ring)

/-- A positive upper bound for the projective denominator norm throughout
the selected event's common sign interval. -/
def selectedEventDenominatorUpper
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  let path := selected.candidate.sourceEvent.partition.entry.chart.path
  let interval := (selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent).refined.interval
  max 1 (denseEvalAbsBound (denominatorNorm path)
    (intervalMagnitude interval.lower interval.upper))

theorem selectedEventDenominatorUpper_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedEventDenominatorUpper selected := by
  unfold selectedEventDenominatorUpper
  exact zero_lt_one.trans_le (le_max_left _ _)

theorem selectedEventDenominator_le
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {t : ℚ}
    (lower : (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined.interval.lower ≤ t)
    (upper : t ≤ (selected.candidate.inputCell.branch.computeEventSigns
      selected.candidate.inputCell.parent).refined.interval.upper) :
    |(denominatorNorm
      selected.candidate.sourceEvent.partition.entry.chart.path).eval t| ≤
        selectedEventDenominatorUpper selected := by
  let interval := (selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent).refined.interval
  let magnitude := intervalMagnitude interval.lower interval.upper
  have parameterBound : |t| ≤ magnitude :=
    abs_le_intervalMagnitude lower upper
  have evaluationBound := abs_dense_eval_le_denseEvalAbsBound
    (denominatorNorm
      selected.candidate.sourceEvent.partition.entry.chart.path)
    (intervalMagnitude_pos interval.lower interval.upper).le parameterBound
  exact evaluationBound.trans (le_max_right _ _)

/-- The common strict polynomial margin, divided by a uniform projective
denominator upper bound, is a positive margin for every selected strict
Hermitian form. -/
def selectedStrictFormMargin
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent) /
    selectedEventDenominatorUpper selected

theorem selectedStrictFormMargin_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedStrictFormMargin selected := by
  apply div_pos
  · exact FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_pos
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent
      (selected.candidate.inputCell.branch.computeEventSigns
        selected.candidate.inputCell.parent)
  · exact selectedEventDenominatorUpper_pos selected

/-- Every selected strict form has the common explicit absolute-value margin
at the rational point produced by the shrinking event extraction. -/
theorem selectedStrictFormMargin_le_event
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalStrictPriorForms selected) :
    selectedStrictFormMargin selected ≤
      |form.eval (shrinkingEventPoint selected squarefree radius
        radiusPositive)| := by
  let epsilon := shrinkingEventApproximationWidth selected squarefree radius
    radiusPositive
  let epsilonPositive : 0 < epsilon :=
    shrinkingEventApproximationWidth_pos selected squarefree radius
      radiusPositive
  let path := selected.candidate.sourceEvent.partition.entry.chart.path
  let signs := selected.candidate.inputCell.branch.computeEventSigns
    selected.candidate.inputCell.parent
  let t := selectedApproximationParameter selected epsilon epsilonPositive
  have canonicalNonzero : canonicalEventValue
      selected.candidate.inputCell.branch.factor.input
      (clearedForm form path) signs.refined.interval.lower ≠ 0 := by
    simpa only [eventPayloadCanonicalValue, path, signs] using
      strictPriorForms_value_ne
        (inputIncrementalAdvanceFormula state selected.bit)
        (eventPayloadCanonicalValue selected) member
  have clearedLower :=
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin_le_abs_eval
      selected.candidate.inputCell.branch.relations
      selected.candidate.inputCell.parent signs
      (selectedStrictPolynomial_mem selected member) canonicalNonzero
      (selectedApproximationParameter_lower selected epsilon epsilonPositive)
      (selectedApproximationParameter_upper selected epsilon epsilonPositive)
  have denominatorLe := selectedEventDenominator_le selected
    (selectedApproximationParameter_lower selected epsilon epsilonPositive)
    (selectedApproximationParameter_upper selected epsilon epsilonPositive)
  have denominatorNonzero := selectedApproximation_denominator_ne selected
    epsilon epsilonPositive
  have clearedIdentity : |(clearedForm form path).eval t| =
      |(denominatorNorm path).eval t| *
        |form.eval (selectedApproximationPoint selected epsilon
          epsilonPositive)| := by
    rw [eval_clearedForm form path t denominatorNonzero, abs_mul]
    rfl
  rw [shrinkingEventPoint_eq_selectedApproximationPoint selected squarefree
    radius radiusPositive]
  unfold selectedStrictFormMargin
  apply (div_le_iff₀ (selectedEventDenominatorUpper_pos selected)).2
  calc
    FTA.CCLBranchEventOwner.ConditionRelations.strictMargin
        selected.candidate.inputCell.branch.relations
        selected.candidate.inputCell.parent signs ≤
      |(clearedForm form path).eval t| := clearedLower
    _ = |(denominatorNorm path).eval t| *
        |form.eval (selectedApproximationPoint selected epsilon
          epsilonPositive)| := clearedIdentity
    _ ≤ selectedEventDenominatorUpper selected *
        |form.eval (selectedApproximationPoint selected epsilon
          epsilonPositive)| :=
      mul_le_mul_of_nonneg_right denominatorLe (abs_nonneg _)
    _ = |form.eval (selectedApproximationPoint selected epsilon
          epsilonPositive)| * selectedEventDenominatorUpper selected := by ring

/-- One positive rational radius preserves all selected strict signs when the
represented base point is compared with the shrinking event point. -/
def selectedStrictRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  FTA.Maximality.positiveMinimum
    ((eventPayloadIncrementalStrictPriorForms selected).map fun form =>
      selectedStrictFormMargin selected /
        (10 * variationMajorant form output.state.box))

theorem selectedStrictRadius_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedStrictRadius selected := by
  apply FTA.Maximality.positiveMinimum_pos
  intro value valueMember
  rw [List.mem_map] at valueMember
  rcases valueMember with ⟨form, formMember, rfl⟩
  exact div_pos (selectedStrictFormMargin_pos selected)
    (mul_pos (by norm_num) (variationMajorant_pos form output.state.box))

theorem selectedStrictRadius_le_form
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalStrictPriorForms selected) :
    selectedStrictRadius selected ≤ selectedStrictFormMargin selected /
      (10 * variationMajorant form output.state.box) := by
  apply FTA.Maximality.positiveMinimum_le_of_mem
  exact List.mem_map.mpr ⟨form, member, rfl⟩

/-- At every smaller requested radius, all selected strict canonical signs
have transferred to the represented coupled-track base point. -/
theorem convergentGridBase_strict
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < selectedStrictRadius selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form * form.eval base.point := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  let eventPoint := shrinkingEventPoint selected squarefree radius radiusPositive
  change ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
    0 < eventPayloadCanonicalValue selected form * form.eval base.point
  intro form member
  have radiusForm : radius < selectedStrictFormMargin selected /
      (10 * variationMajorant form separation.state.box) :=
    radiusSmall.trans_le (selectedStrictRadius_le_form selected member)
  have coefficientPositive : 0 <
      10 * variationMajorant form separation.state.box :=
    mul_pos (by norm_num) (variationMajorant_pos form separation.state.box)
  have variationSmall :
      10 * variationMajorant form separation.state.box * radius <
        selectedStrictFormMargin selected := by
    have := (lt_div_iff₀ coefficientPositive).mp radiusForm
    nlinarith
  have baseInsideSeparation : separation.state.box.Contains base.point :=
    nextRefines.contains base.strict.contains
  have eventInsideSeparation : separation.state.box.Contains eventPoint := by
    have strict := eventWindingOneState_strictInterior
      separation.state.refinesAmbient selected.candidate.inputCell squarefree
      (shrinkingEventClearance separation radius radiusPositive) elimination
    exact strict.refines.contains
      (shrinkingEventState_contains_point selected squarefree elimination radius
        radiusPositive)
  have variation := abs_eval_sub_eval_le form baseInsideSeparation
    eventInsideSeparation
  have distance := convergentGridBase_event_distance current separation selected
    squarefree degreeNonzero elimination next nextRefines radius radiusPositive
  have variationLe :
      |form.eval base.point - form.eval eventPoint| ≤
        10 * variationMajorant form separation.state.box * radius := by
    apply variation.trans
    exact mul_le_mul_of_nonneg_left distance
      (variationMajorant_pos form separation.state.box).le |>.trans_eq (by ring)
  have eventMargin := selectedStrictFormMargin_le_event selected squarefree
    radius radiusPositive member
  have close : |form.eval eventPoint - form.eval base.point| <
      |form.eval eventPoint| := by
    rw [abs_sub_comm]
    exact variationLe.trans_lt (variationSmall.trans_le eventMargin)
  have eventBaseSame :
      0 < form.eval eventPoint * form.eval base.point :=
    mul_pos_of_abs_sub_lt_abs_left close
  exact FTA.CCLPositiveEventGrid.mul_pos_trans
    (shrinkingEventStrict selected squarefree radius radiusPositive form member)
    eventBaseSame

/-- Below the selected strict radius, every protected current/selected/box
form and the nonzero norm form is nonzero at the represented grid base. -/
theorem convergentGridBase_priors_nonzero
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < selectedStrictRadius selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    ∀ form ∈ eventPayloadPriorForms current selected base.priors
      base.point next.box,
      form.eval base.point ≠ 0 := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  have selectedStrict :
      ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form * form.eval base.point := by
    simpa only [base] using convergentGridBase_strict current separation
      selected squarefree degreeNonzero elimination next nextRefines radius
      radiusPositive radiusSmall
  change ∀ form ∈ eventPayloadPriorForms current selected base.priors
    base.point next.box, form.eval base.point ≠ 0
  intro form member
  simp only [eventPayloadPriorForms, List.mem_append,
    List.mem_singleton] at member
  rcases member with ((currentPrior | selectedMember) | boxForm) | normForm
  · exact base.priorsNonzero form currentPrior
  · intro zero
    have positive := selectedStrict form selectedMember
    rw [zero] at positive
    norm_num at positive
  · exact (boxForms_pos_of_strictContains base.strict form boxForm).ne'
  · subst form
    simpa [eval_affineNormForm] using (normSq_pos base.nonzero).ne'

/-- A single positive coefficient dominates the linear residual coefficient
of every selected active form.  A sum is used instead of a maximum so the
bound remains executable without a nonempty-list side condition. -/
def selectedActiveCoefficientSum
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) : ℚ :=
  1 + ((eventPayloadIncrementalActiveOwnerForms selected).map fun form =>
    selectedActiveBaseCoefficient selected form).sum

theorem selectedActiveCoefficientSum_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) :
    0 < selectedActiveCoefficientSum selected := by
  have sumNonnegative : 0 ≤
      ((eventPayloadIncrementalActiveOwnerForms selected).map fun form =>
        selectedActiveBaseCoefficient selected form).sum := by
    apply List.sum_nonneg
    intro coefficient coefficientMember
    rw [List.mem_map] at coefficientMember
    rcases coefficientMember with ⟨form, _formMember, rfl⟩
    exact (selectedActiveBaseCoefficient_pos selected form).le
  unfold selectedActiveCoefficientSum
  linarith

theorem selectedActiveBaseCoefficient_lt_sum
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    selectedActiveBaseCoefficient selected form <
      selectedActiveCoefficientSum selected := by
  have coefficientLeSum : selectedActiveBaseCoefficient selected form ≤
      ((eventPayloadIncrementalActiveOwnerForms selected).map fun item =>
        selectedActiveBaseCoefficient selected item).sum := by
    apply List.single_le_sum
    · intro coefficient coefficientMember
      rw [List.mem_map] at coefficientMember
      rcases coefficientMember with ⟨item, _itemMember, rfl⟩
      exact (selectedActiveBaseCoefficient_pos selected item).le
    · exact List.mem_map.mpr ⟨form, member, rfl⟩
  unfold selectedActiveCoefficientSum
  linarith

/-- Radius cap obtained by dividing the positive grid residual budget by
twice the common selected-active coefficient. -/
def selectedResidualRadiusCap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm) : ℚ :=
  approximateBoundaryBudget direction priors /
    (2 * selectedActiveCoefficientSum selected)

theorem selectedResidualRadiusCap_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    0 < selectedResidualRadiusCap selected direction priors := by
  exact div_pos (approximateBoundaryBudget_pos direction priors priorNonzero)
    (mul_pos (by norm_num) (selectedActiveCoefficientSum_pos selected))

/-- The common active coefficient times that cap consumes exactly half of
the available residual budget, hence is strictly below it. -/
theorem selectedActiveCoefficient_mul_residualRadiusCap_lt_budget
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    selectedActiveCoefficientSum selected *
        selectedResidualRadiusCap selected direction priors <
      approximateBoundaryBudget direction priors := by
  have coefficientPositive := selectedActiveCoefficientSum_pos selected
  have budgetPositive :=
    approximateBoundaryBudget_pos direction priors priorNonzero
  have identity : selectedActiveCoefficientSum selected *
        selectedResidualRadiusCap selected direction priors =
      approximateBoundaryBudget direction priors / 2 := by
    unfold selectedResidualRadiusCap
    field_simp
  rw [identity]
  linarith

/-- One computed positive cap handles both selected strict-sign transfer and
the active residual budget for a displayed successful direction. -/
def selectedGridRadiusCap
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm) : ℚ :=
  min (selectedStrictRadius selected / 2)
    (selectedResidualRadiusCap selected direction priors)

theorem selectedGridRadiusCap_pos
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    0 < selectedGridRadiusCap selected direction priors := by
  apply lt_min
  · exact div_pos (selectedStrictRadius_pos selected) (by norm_num)
  · exact selectedResidualRadiusCap_pos selected direction priors
      priorNonzero

theorem selectedGridRadiusCap_lt_strictRadius
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm) :
    selectedGridRadiusCap selected direction priors <
      selectedStrictRadius selected := by
  have halfLe : selectedGridRadiusCap selected direction priors ≤
      selectedStrictRadius selected / 2 := min_le_left _ _
  exact halfLe.trans_lt (by
    have positive := selectedStrictRadius_pos selected
    linarith)

theorem selectedActiveCoefficient_mul_gridRadiusCap_lt_budget
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : IncrementalEventPayload output)
    {forms : List HermitianForm} {z : QI}
    (direction : TangentDirection forms z) (priors : List HermitianForm)
    (priorNonzero : ∀ form ∈ priors, form.eval z ≠ 0) :
    selectedActiveCoefficientSum selected *
        selectedGridRadiusCap selected direction priors <
      approximateBoundaryBudget direction priors := by
  apply (mul_le_mul_of_nonneg_left (min_le_right _ _)
    (selectedActiveCoefficientSum_pos selected).le).trans_lt
  exact selectedActiveCoefficient_mul_residualRadiusCap_lt_budget selected
    direction priors priorNonzero

/-- The common coefficient gives a strict linear residual bound at the
represented base for every selected active owner. -/
theorem convergentGridBase_active_lt_sum
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius) {form : HermitianForm}
    (member : form ∈ eventPayloadIncrementalActiveOwnerForms selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    |form.eval base.point| < selectedActiveCoefficientSum selected * radius := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  have individual := convergentGridBase_active_le current separation selected
    squarefree degreeNonzero elimination next nextRefines radius radiusPositive
    member
  exact individual.trans_lt (mul_lt_mul_of_pos_right
    (selectedActiveBaseCoefficient_lt_sum selected member) radiusPositive)

/-- Once the finite direction table supplies a direction with a budget above
the common linear residual, all convergence facts assemble directly into the
complete proof-bearing grid input. -/
def convergentGridData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < selectedStrictRadius selected) :
    let base := convergentGridBase current separation squarefree elimination
      next nextRefines radius radiusPositive
    (direction : TangentDirection
      (eventPayloadActiveForms current selected base.point) base.point) →
    selectedActiveCoefficientSum selected * radius <
      approximateBoundaryBudget direction
        (eventPayloadPriorForms current selected base.priors base.point
          next.box) →
    EventGridData current separation selected next nextRefines := by
  dsimp only
  intro direction residualBudget
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  exact
    { base := base.point
      baseStrict := base.strict
      baseNonzero := base.nonzero
      baseRepresented := base.represented
      basePriors := base.priors
      basePriorsNonzero := base.priorsNonzero
      baseStable := base.stable
      direction := direction
      selectedStrictAtBase := by
        simpa only [base] using convergentGridBase_strict current separation
          selected squarefree degreeNonzero elimination next nextRefines radius
          radiusPositive radiusSmall
      selectedActiveResidual := by
        intro form member
        exact (convergentGridBase_active_lt_sum current separation selected
          squarefree degreeNonzero elimination next nextRefines radius
          radiusPositive member).trans residualBudget }

/-- The same quantitative hypotheses force the executable `gridData?` check
to return a proof-bearing result, rather than merely permitting an external
construction of `GridData`. -/
theorem convergentGridData?_isSome
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (radiusSmall : radius < selectedStrictRadius selected)
    (direction : TangentDirection
      (eventPayloadActiveForms current selected
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point)
    (search : tangentDirectionCertificate?
      (eventPayloadActiveForms current selected
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point = some direction)
    (residualBudget : selectedActiveCoefficientSum selected * radius <
      approximateBoundaryBudget direction
        (eventPayloadPriorForms current selected
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
      ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form * form.eval base.point := by
    simpa only [base] using convergentGridBase_strict current separation
      selected squarefree degreeNonzero elimination next nextRefines radius
      radiusPositive radiusSmall
  have residualAt :
      ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
      |form.eval base.point| < approximateBoundaryBudget direction
        (eventPayloadPriorForms current selected base.priors base.point
          next.box) := by
    intro form member
    exact (convergentGridBase_active_lt_sum current separation selected
      squarefree degreeNonzero elimination next nextRefines radius
      radiusPositive member).trans residualBudget
  unfold eventGridData?
  rw [search]
  simp only
  rw [dif_pos (by simpa only [base] using strictAt)]
  rw [dif_pos (by simpa only [base] using residualAt)]
  rfl

/-- The executable grid attempt needs no separately supplied strict or
residual inequality once the requested localization radius is below the one
computed common cap for its successful table direction. -/
theorem convergentGridData?_isSome_of_le_radiusCap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines separation.state.box)
    (radius : ℚ) (radiusPositive : 0 < radius)
    (direction : TangentDirection
      (eventPayloadActiveForms current selected
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point)
    (search : tangentDirectionCertificate?
      (eventPayloadActiveForms current selected
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point)
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive).point = some direction)
    (radiusLe : radius ≤ selectedGridRadiusCap selected direction
      (eventPayloadPriorForms current selected
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).priors
        (convergentGridBase current separation squarefree elimination next
          nextRefines radius radiusPositive).point next.box)) :
    (eventGridData? current separation selected next nextRefines
      (convergentGridBase current separation squarefree elimination next
        nextRefines radius radiusPositive)).isSome := by
  let base := convergentGridBase current separation squarefree elimination
    next nextRefines radius radiusPositive
  have radiusLe' : radius ≤ selectedGridRadiusCap selected direction
      (eventPayloadPriorForms current selected base.priors base.point
        next.box) := by
    simpa only [base] using radiusLe
  have radiusSmall : radius < selectedStrictRadius selected :=
    radiusLe'.trans_lt
      (selectedGridRadiusCap_lt_strictRadius selected direction _)
  have priorNonzero :
      ∀ form ∈ eventPayloadPriorForms current selected base.priors
        base.point next.box, form.eval base.point ≠ 0 := by
    simpa only [base] using convergentGridBase_priors_nonzero current separation
      selected squarefree degreeNonzero elimination next nextRefines radius
      radiusPositive radiusSmall
  have capBudget : selectedActiveCoefficientSum selected *
        selectedGridRadiusCap selected direction
          (eventPayloadPriorForms current selected base.priors base.point
            next.box) <
      approximateBoundaryBudget direction
        (eventPayloadPriorForms current selected base.priors base.point
          next.box) :=
    selectedActiveCoefficient_mul_gridRadiusCap_lt_budget selected direction _
      priorNonzero
  have residualBudget : selectedActiveCoefficientSum selected * radius <
      approximateBoundaryBudget direction
        (eventPayloadPriorForms current selected base.priors base.point
          next.box) := by
    apply (mul_le_mul_of_nonneg_left radiusLe'
      (selectedActiveCoefficientSum_pos selected).le).trans_lt
    exact capBudget
  apply convergentGridData?_isSome current separation selected squarefree
    degreeNonzero elimination next nextRefines radius radiusPositive radiusSmall
    direction
  · simpa only [base] using search
  · simpa only [base] using residualBudget

/-- A successful finite convergence-grid attempt in every later winding box.
The only remaining geometric obligation is the displayed executable success
proof; fixed historical priors and their cross-refinement orientation are
recovered automatically from the coupled state. -/
structure ConvergentGridSuccessFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (selected : IncrementalEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) where
  radius : (next : WindingOneState p (RatBox.symmetric R hR)) →
    next.box.Refines separation.state.box → ℚ
  radiusPositive : ∀ next nextRefines, 0 < radius next nextRefines
  success : ∀ next nextRefines,
    (eventGridData? current separation selected next nextRefines
      (convergentGridBase current separation squarefree elimination next
        nextRefines (radius next nextRefines)
          (radiusPositive next nextRefines))).isSome

/-- Extract all successful records and discharge their coherence fields. -/
def ConvergentGridSuccessFamily.gridFamily
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {squarefree : GaussianSquarefreeCertificate p}
    {D : ℕ} {elimination : AxisEliminationCertificate p D}
    (family : ConvergentGridSuccessFamily current separation selected squarefree
      elimination) :
    PersistentEventGridDataFamily current separation selected where
  data next nextRefines :=
    eventGridDataOfIsSome current separation selected next nextRefines
      (convergentGridBase current separation squarefree elimination next
        nextRefines (family.radius next nextRefines)
          (family.radiusPositive next nextRefines))
      (family.success next nextRefines)
  basePriors := by
    intro next nextRefines
    apply (eventGridDataOfIsSome_basePriors current separation selected next
      nextRefines
      (convergentGridBase current separation squarefree elimination next
        nextRefines (family.radius next nextRefines)
          (family.radiusPositive next nextRefines))
      (family.success next nextRefines)).trans
    exact convergentGridBase_priors current separation squarefree elimination
      next nextRefines (family.radius next nextRefines)
        (family.radiusPositive next nextRefines)
  baseSameSigns := by
    intro next nextRefines form member
    rw [eventGridDataOfIsSome_base current separation selected next nextRefines
      (convergentGridBase current separation squarefree elimination next
        nextRefines (family.radius next nextRefines)
          (family.radiusPositive next nextRefines))
      (family.success next nextRefines)]
    exact convergentGridBase_sameSigns current separation squarefree elimination
      next nextRefines (family.radius next nextRefines)
        (family.radiusPositive next nextRefines) form member

/-- The successful convergence family is therefore already the persistent
owner sampler consumed by the coupled controller. -/
def ConvergentGridSuccessFamily.ownerSamples
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix)}
    {selected : IncrementalEventPayload separation}
    {squarefree : GaussianSquarefreeCertificate p}
    {D : ℕ} {elimination : AxisEliminationCertificate p D}
    (family : ConvergentGridSuccessFamily current separation selected squarefree
      elimination) :
    CCLCoupledController.PersistentEventOwnerSamples current separation
      selected :=
  family.gridFamily.ownerSamples

end CCLPositiveEventConvergence
end FTA
