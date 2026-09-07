import FTA.CCLHistoricalGridConvergence

/-!
# Persistent samples on lower-dimensional historical CCL cylinders

When the complete historical owner cone has no common strict entry
direction, the represented cylinder can be forced to remain on its selected
rational source path.  This module packages the pure boundary stratum as a
semantic sample in every later winding-one box.  It deliberately makes no
open-neighbourhood claim.
-/

namespace FTA
namespace CCLHistoricalPathPersistence

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLBoundaryPreservingOwner
open FTA.CCLBranchController
open FTA.CCLBranchEventOwner
open FTA.CCLCanonicalEvent
open FTA.CCLCompleteEventTangentSigns
open FTA.CCLCoupledTrack
open FTA.CCLEventTangentSigns
open FTA.CCLEventExtraction
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLHistoricalEventOwner
open FTA.CCLHistoricalEventTangentSigns
open FTA.CCLHistoricalGridConvergence
open FTA.CCLNextBitFormula
open FTA.CCLPathIntersection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventLocalization
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventTrack
open FTA.LocalExtraction
open FTA.ProjectivePath
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- The fixed rational path cylinder selected by the final historical slope
cell. -/
def historicalSourcePathCylinder
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : RationalPathCylinder where
  path := selectedCompletePath selected
  interval := (historicalSlopeSigns selected).refined.interval
  denominator_ne := by
    intro parameter lower upper
    apply (historicalInputCell selected).path_denominator_ne_on_cell
    · exact (historicalSlopeSigns_refines_inputCell selected).1.trans lower
    · exact upper.trans
        (historicalSlopeSigns_refines_inputCell selected).2

def historicalSourcePathSupport
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output) : QI → Prop :=
  (historicalSourcePathCylinder selected).Contains

/-- A fixed positive cap small enough to distinguish every localized path
sample from zero when zero is not a polynomial root. -/
def historicalPathCap (p : GaussianPolynomial) : ℚ :=
  normSq (p.eval 0) / 2

theorem historicalPathCap_pos
    (p : GaussianPolynomial) (zeroNonzero : p.eval 0 ≠ 0) :
    0 < historicalPathCap p :=
  div_pos (normSq_pos zeroNonzero) (by norm_num)

theorem historicalPathCap_le_zeroResidual (p : GaussianPolynomial) :
    historicalPathCap p ≤ normSq (p.eval 0) := by
  exact div_le_self (normSq_nonneg (p.eval 0)) (by norm_num)

/-- The canonical source-path point in an arbitrary later winding box. -/
def historicalPureBoundaryPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p ambient) : QI :=
  historicalSlopeCappedLocalizedEventPoint selected squarefree next
    (historicalPathCap p) (historicalPathCap_pos p zeroNonzero)

theorem historicalPureBoundaryPoint_supported
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p ambient) :
    historicalSourcePathSupport selected
      (historicalPureBoundaryPoint selected squarefree zeroNonzero next) := by
  let cap := historicalPathCap p
  let capPositive := historicalPathCap_pos p zeroNonzero
  let capped := cappedClearanceState next cap capPositive
  let parameter := historicalSlopeLocalizedEventParameter selected squarefree
    capped
  refine ⟨parameter,
    historicalSlopeLocalizedEventParameter_lower selected squarefree capped,
    historicalSlopeLocalizedEventParameter_upper selected squarefree capped,
    ?_⟩
  simpa only [historicalPureBoundaryPoint,
      historicalSlopeCappedLocalizedEventPoint, capped, cap, capPositive,
      historicalSourcePathSupport, historicalSourcePathCylinder,
      RationalPathCylinder.Contains, parameter] using
      historicalSlopeLocalizedEventPoint_eq_pathValue selected squarefree
        capped

theorem historicalPureBoundaryPoint_strictContains
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    next.box.StrictContains
      (historicalPureBoundaryPoint selected squarefree zeroNonzero next) := by
  exact historicalSlopeCappedLocalizedEventPoint_strictContains output
    selected squarefree degreeNonzero elimination next nextRefines
    (historicalPathCap p) (historicalPathCap_pos p zeroNonzero)

theorem historicalPureBoundaryPoint_ne_zero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (zeroNonzero : p.eval 0 ≠ 0)
    (next : WindingOneState p ambient) :
    historicalPureBoundaryPoint selected squarefree zeroNonzero next ≠ 0 :=
  historicalSlopeCappedLocalizedEventPoint_ne_zero selected squarefree next
    (historicalPathCap p) (historicalPathCap_pos p zeroNonzero)
    (historicalPathCap_le_zeroResidual p)

/-- On the pure boundary stratum, every capped localized point realizes the
complete historical old-prefix-plus-child formula. -/
theorem historicalPureBoundaryPoint_holds
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
    (noCrossings : historicalPathCrossingForms selected = [])
    (next : WindingOneState p (RatBox.symmetric R hR)) :
    (historicalOwnerFormula (RawParser.parse current.word) selected.bit).Holds
      (historicalPureBoundaryPoint selected squarefree zeroNonzero next) := by
  rcases historicalPureBoundaryPoint_supported selected squarefree zeroNonzero
      next with ⟨parameter, lower, upper, pointEq⟩
  have denominator : (selectedCompletePath selected).denominator.eval
      (PathPolynomial.ofRat parameter) ≠ 0 := by
    exact (historicalSourcePathCylinder selected).denominator_ne lower upper
  rw [pointEq]
  apply historicalOwnerFormula_holds_of_path_partition current output selected
    squarefree degreeNonzero elimination valid parameter denominator
  · simp [noCrossings]
  · exact historicalStrictPriorForms_mul_eval_pos selected lower upper

/-- Exact extended-word semantics at every pure boundary sample. -/
theorem historicalPureBoundaryPoint_represented
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
    (noCrossings : historicalPathCrossingForms selected = [])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    RawParserSemantics.Represented (current.word ++ [selected.bit])
      (historicalPureBoundaryPoint selected squarefree zeroNonzero next) := by
  let point := historicalPureBoundaryPoint selected squarefree zeroNonzero next
  have complete := historicalPureBoundaryPoint_holds current output selected
    squarefree degreeNonzero zeroNonzero elimination valid noCrossings next
  have components :
      (inputStateFormula (RawParser.parse current.word)).Holds point ∧
        (inputAdvanceFormula (RawParser.parse current.word)
          selected.bit).Holds point := by
    simpa only [historicalOwnerFormula, Formula.Holds, point] using complete
  have insideNext : next.box.Contains point :=
    (historicalPureBoundaryPoint_strictContains output selected squarefree
      degreeNonzero zeroNonzero elimination next nextRefines).contains
  have insideOutput : output.state.box.Contains point :=
    nextRefines.contains insideNext
  have inverseDenominator :=
    CCLBranchEvidence.separation_denominator_ne output insideOutput
  have representedCurrent : RawParserSemantics.Represented current.word point :=
    represented_of_inputStateFormula current.word point inverseDenominator
      components.1
  have extended :=
    CCLBranchSampling.represented_append_of_inputFormula current.word point
      selected.bit inverseDenominator representedCurrent components.2
  simpa only [point] using extended

/-- The pure historical boundary stratum supplies an honest constrained
represented sample in every later winding-one box. -/
def historicalPureBoundarySamples
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
    (noCrossings : historicalPathCrossingForms selected = []) :
    PersistentConstrainedRepresentedSamples
      (current.word ++ [selected.bit]) output.state
      (historicalSourcePathSupport selected) where
  sample next nextRefines :=
    { point := historicalPureBoundaryPoint selected squarefree zeroNonzero next
      inside := (historicalPureBoundaryPoint_strictContains output selected
        squarefree degreeNonzero zeroNonzero elimination next
        nextRefines).contains
      nonzero := historicalPureBoundaryPoint_ne_zero selected squarefree
        zeroNonzero next
      semantics := historicalPureBoundaryPoint_represented current output
        selected squarefree degreeNonzero zeroNonzero elimination valid
        noCrossings next nextRefines
      supported := historicalPureBoundaryPoint_supported selected squarefree
        zeroNonzero next }

/-- The pure boundary family is a concrete successor state in the generalized
open-or-constrained coupled-state model. -/
def historicalPureBoundaryState
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
    (noCrossings : historicalPathCrossingForms selected = []) :
    CCLCoupledTrack.PersistentState p (RatBox.symmetric R hR) where
  numerical := output.state
  word := current.word ++ [selected.bit]
  persistence := .constrained (historicalSourcePathCylinder selected)
    (historicalPureBoundarySamples current output selected squarefree
      degreeNonzero zeroNonzero elimination valid noCrossings)

/-- Concrete generalized controller step for a pure lower-dimensional
historical cylinder. -/
def nextOfHistoricalPureBoundary
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
    (noCrossings : historicalPathCrossingForms selected = []) :
    CCLCoupledTrack.PersistentStepResult current.toPersistentState :=
  .next selected.bit
    (historicalPureBoundaryState current output selected squarefree
      degreeNonzero zeroNonzero elimination valid noCrossings)
    output.refines rfl

/-- Executable historical-owner opening in the generalized persistence model.
The complete tangent cone gives an ordinary stable successor, while a pure
path-equality stratum gives an honest constrained successor.  The two
remaining constructors retain exactly the finite certificates needed by the
side-persistence and cone-compatibility lemmas; neither is collapsed to an
unexplained failed search. -/
inductive HistoricalPersistentOpening
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload output) : Type where
  | ready
      (result : CCLCoupledTrack.PersistentStepResult
        current.toPersistentState)
  | pathSide
      (parameter : ℚ)
      (search : historicalPathParameter? selected = some parameter)
      (holds : (historicalOwnerFormula (RawParser.parse current.word)
        selected.bit).Holds ((selectedCompletePath selected).value parameter))
      (crossings : historicalPathCrossingForms selected ≠ [])
      (tangentFailure :
        historicalClassifiedTangentDirection? selected = none)
  | coneObstructed
      (obstruction : HistoricalFormulaConeObstruction current output selected)

/-- Run every already-supported historical branch before exposing a residual
geometric obligation.  Tangent entry is preferred because it immediately
produces an open stable family.  If no strict compass direction exists, an
empty crossing list is precisely the lower-dimensional path case already
handled above. -/
def openHistoricalPersistent
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
    (valid : SelectedCurrentFormulaCanonical selected) :
    HistoricalPersistentOpening current output selected := by
  cases tangentSearch :
      historicalClassifiedTangentDirection? selected with
  | some direction =>
      exact .ready
        (nextOfHistoricalStaticGrid current output selected squarefree
          degreeNonzero zeroNonzero elimination valid tangentSearch).toPersistent
  | none =>
      cases crossingsEq : historicalPathCrossingForms selected with
      | nil =>
          exact .ready
            (nextOfHistoricalPureBoundary current output selected squarefree
              degreeNonzero zeroNonzero elimination valid crossingsEq)
      | cons head tail =>
          cases pathSearch : historicalPathParameter? selected with
          | some parameter =>
              exact .pathSide parameter pathSearch
                (historicalPathParameter?_some_holds pathSearch) (by
                intro empty
                rw [crossingsEq] at empty
                cases empty) tangentSearch
          | none =>
              exact .coneObstructed
                (historicalFormulaConeObstructionOfFailures current output
                  selected squarefree degreeNonzero elimination valid
                    pathSearch tangentSearch)

/-- Global-event adapter from the finite controller invariant to the complete
historical persistence opening. -/
def openHistoricalPersistentOfControllerEvent
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
    (canonical : ControllerCanonicalOnInputEvents current.numerical
      current.word) :
    HistoricalPersistentOpening current output selected.toPayload :=
  openHistoricalPersistent current output selected.toPayload squarefree
    degreeNonzero zeroNonzero elimination
      (SelectedCurrentFormulaCanonical.ofSelectedEventCount canonical selected)

/-- Guard-event specialization of the same finite opening. -/
def openHistoricalPersistentOfControllerGuard
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
    (canonical : ControllerCanonicalOnInputEvents current.numerical
      current.word) :
    HistoricalPersistentOpening current output selected.toPayload :=
  openHistoricalPersistent current output selected.toPayload squarefree
    degreeNonzero zeroNonzero elimination
      (SelectedCurrentFormulaCanonical.ofSelectedGuardEventCount canonical
        selected)

end CCLHistoricalPathPersistence
end FTA
