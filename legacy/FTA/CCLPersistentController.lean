import FTA.CCLCoupledController
import FTA.CCLHistoricalGridConvergence
import FTA.CCLHistoricalPathPersistence

/-!
# Controller adapters for constrained CCL cylinders

This module routes the generalized open-or-path persistence state through the
controller operations that need only semantic samples.  In particular,
whole-box formula decisions extend a constrained sample family without
inventing an open neighbourhood.
-/

namespace FTA
namespace CCLPersistentController

open CCL
open FTA.AxisSafeCuts
open FTA.CCLBoundaryPreservingOwner
open FTA.CCLBranchController
open FTA.CCLBranchEvidence
open FTA.CCLBranchSampling
open FTA.CCLCanonicalEvent
open FTA.CCLCompleteEventTangentSigns
open FTA.CCLCoupledController
open FTA.CCLCoupledTrack
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLHistoricalEventOwner
open FTA.CCLHistoricalEventTangentSigns
open FTA.CCLHistoricalPathPersistence
open FTA.CCLNextBitFormula
open FTA.CCLParserGeometry
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Lift a legacy stable-state result while retaining the original factored
stable family as the generalized current-state index. -/
def liftStableStep
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical : WindingOneState p ambient}
    (samples : PersistentStableRepresentedSamples word numerical)
    (result : CCLCoupledTrack.StepResult
      (CCLCoupledTrack.State.ofStableSamples samples)) :
    PersistentStepResult (PersistentState.ofStableSamples samples) :=
  match result with
  | .zero root => .zero root
  | .terminal point root nonzero completeWord complete =>
      .terminal point root nonzero completeWord complete
  | .next bit next refines wordEq =>
      .next bit next.toPersistentState refines wordEq

/-- Extend a constrained represented family through a child formula that is
true throughout the denominator-separated box. -/
def constrainedAfterUniformFormula
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical : WindingOneState p ambient}
    (cylinder : RationalPathCylinder)
    (samples : PersistentConstrainedRepresentedSamples word numerical
      cylinder.Contains)
    (output : CCLDenominator.SeparationOutput p ambient numerical
      (adjugate (RawParser.parse word).matrix))
    (bit : Bool)
    (selected : ∀ {input : QI}, output.state.box.Contains input →
      (inputAdvanceFormula (RawParser.parse word) bit).Holds input) :
    PersistentConstrainedRepresentedSamples (word ++ [bit]) output.state
      cylinder.Contains where
  sample next nextRefines := by
    let prior := samples.sample next (nextRefines.trans output.refines)
    have insideOutput : output.state.box.Contains prior.point :=
      nextRefines.contains prior.inside
    have inverseDenominator := separation_denominator_ne output insideOutput
    exact
      { point := prior.point
        inside := prior.inside
        nonzero := prior.nonzero
        semantics := represented_append_of_inputFormula word prior.point bit
          inverseDenominator prior.semantics (selected insideOutput)
        supported := prior.supported }

/-- Extend a constrained represented family when the selected child formula
is certified directly on its distinguished sample in every later box.  This
is the path-local counterpart of `constrainedAfterUniformFormula`: no open
neighbourhood or whole-box sign claim is introduced. -/
def constrainedAfterSampleFormula
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical : WindingOneState p ambient}
    (cylinder : RationalPathCylinder)
    (samples : PersistentConstrainedRepresentedSamples word numerical
      cylinder.Contains)
    (output : CCLDenominator.SeparationOutput p ambient numerical
      (adjugate (RawParser.parse word).matrix))
    (bit : Bool)
    (selected : ∀ (next : WindingOneState p ambient)
      (nextRefines : next.box.Refines output.state.box),
      (inputAdvanceFormula (RawParser.parse word) bit).Holds
        (samples.sample next
          (nextRefines.trans output.refines)).point) :
    PersistentConstrainedRepresentedSamples (word ++ [bit]) output.state
      cylinder.Contains where
  sample next nextRefines := by
    let prior := samples.sample next (nextRefines.trans output.refines)
    have insideOutput : output.state.box.Contains prior.point :=
      nextRefines.contains prior.inside
    have inverseDenominator := separation_denominator_ne output insideOutput
    exact
      { point := prior.point
        inside := prior.inside
        nonzero := prior.nonzero
        semantics := represented_append_of_inputFormula word prior.point bit
          inverseDenominator prior.semantics (selected next nextRefines)
        supported := prior.supported }

/-- A whole-box child decision is therefore a concrete generalized step from
a path-constrained current state. -/
def nextOfConstrainedUniformFormula
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical : WindingOneState p ambient}
    (cylinder : RationalPathCylinder)
    (samples : PersistentConstrainedRepresentedSamples word numerical
      cylinder.Contains)
    (output : CCLDenominator.SeparationOutput p ambient numerical
      (adjugate (RawParser.parse word).matrix))
    (bit : Bool)
    (selected : ∀ {input : QI}, output.state.box.Contains input →
      (inputAdvanceFormula (RawParser.parse word) bit).Holds input) :
    PersistentStepResult
      (PersistentState.ofConstrainedSamples cylinder samples) :=
  .next bit
    (PersistentState.ofConstrainedSamples cylinder
      (constrainedAfterUniformFormula cylinder samples output bit selected))
    output.refines rfl

/-- A child formula stable only on the selected rational path samples still
gives an honest generalized controller step. -/
def nextOfConstrainedSampleFormula
    {p : GaussianPolynomial} {ambient : RatBox} {word : Prefix.Word}
    {numerical : WindingOneState p ambient}
    (cylinder : RationalPathCylinder)
    (samples : PersistentConstrainedRepresentedSamples word numerical
      cylinder.Contains)
    (output : CCLDenominator.SeparationOutput p ambient numerical
      (adjugate (RawParser.parse word).matrix))
    (bit : Bool)
    (selected : ∀ (next : WindingOneState p ambient)
      (nextRefines : next.box.Refines output.state.box),
      (inputAdvanceFormula (RawParser.parse word) bit).Holds
        (samples.sample next
          (nextRefines.trans output.refines)).point) :
    PersistentStepResult
      (PersistentState.ofConstrainedSamples cylinder samples) :=
  .next bit
    (PersistentState.ofConstrainedSamples cylinder
      (constrainedAfterSampleFormula cylinder samples output bit selected))
    output.refines rfl

/-- The exact whole-box formula evaluator requires only a represented sample,
so it applies uniformly to open and constrained persistence modes. -/
def resolvePersistentSeparatedCell
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : PersistentState p ambient)
    (output : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)) :
    ResolvedCellOutcome (RawParser.parse current.word) output.state.box := by
  let prior := current.persistence.sampleOutcome output.refines
  have determinantNonzero :
      determinant (RawParser.parse current.word).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne current.word
  have inverseDenominator :
      (adjugate (RawParser.parse current.word).matrix).c * prior.point +
        (adjugate (RawParser.parse current.word).matrix).d ≠ 0 :=
    separation_denominator_ne output prior.inside
  let witness : CellWitness (RawParser.parse current.word)
      output.state.box :=
    { input := prior.point
      contains := prior.inside
      inverseDenominator := inverseDenominator
      holds := by
        rcases prior.semantics with ⟨tail, represents⟩
        rw [inverse_tail_eq_of_represents
          (RawParser.parse current.word) prior.point tail determinantNonzero
          inverseDenominator represents]
        exact represents.2.2 }
  exact resolveCell (RawParser.parse current.word) output.state.box
    determinantNonzero witness

/-- Executable strict-cell closure for either generalized persistence mode. -/
def nextOfPersistentSeparatedCell?
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : PersistentState p ambient)
    (output : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix)) :
    Option (PersistentStepResult current) := by
  match current with
  | ⟨numerical, word, .stable samples⟩ =>
      let legacy := CCLCoupledTrack.State.ofStableSamples samples
      let legacyOutput : CCLDenominator.SeparationOutput p ambient
          legacy.numerical
          (adjugate (RawParser.parse legacy.word).matrix) := output
      match nextOfSeparatedCell? legacy legacyOutput with
      | some result => exact some (liftStableStep samples result)
      | none => exact none
  | ⟨numerical, word, .constrained cylinder samples⟩ =>
      match resolvePersistentSeparatedCell
          (PersistentState.ofConstrainedSamples cylinder samples) output with
      | .unresolved | .terminal _ _ _ => exact none
      | .next bit _selectedStrict _otherStrict selected _otherFails =>
          exact some
            (nextOfConstrainedUniformFormula cylinder samples output bit
              selected)

/-! ## Complete historical-owner resolution -/

/-- The two genuinely geometric obligations left after the historical owner
dispatcher has consumed every supported branch.  Keeping this type separate
from `HistoricalPersistentOpening` means downstream controllers cannot
accidentally treat a supported tangent or pure-boundary step as unresolved. -/
inductive HistoricalOwnerResidual
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload output) : Type where
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

/-- Consume the supported constructors of the historical dispatcher. -/
def resolveHistoricalPersistentOpening
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    {output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix)}
    {selected : SelectedEventPayload output} :
    HistoricalPersistentOpening current output selected →
      Sum (PersistentStepResult current.toPersistentState)
        (HistoricalOwnerResidual current output selected)
  | .ready result => .inl result
  | .pathSide parameter search holds crossings tangentFailure =>
      .inr (.pathSide parameter search holds crossings tangentFailure)
  | .coneObstructed obstruction => .inr (.coneObstructed obstruction)

/-- Resolve a selected global event through every implemented historical
persistence branch. -/
def resolveHistoricalControllerEvent
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
    Sum (PersistentStepResult current.toPersistentState)
      (HistoricalOwnerResidual current output selected.toPayload) :=
  resolveHistoricalPersistentOpening
    (openHistoricalPersistentOfControllerEvent current output selected
      squarefree degreeNonzero zeroNonzero elimination canonical)

/-- Guard-event specialization of the complete historical resolver. -/
def resolveHistoricalControllerGuard
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
    Sum (PersistentStepResult current.toPersistentState)
      (HistoricalOwnerResidual current output selected.toPayload) :=
  resolveHistoricalPersistentOpening
    (openHistoricalPersistentOfControllerGuard current output selected
      squarefree degreeNonzero zeroNonzero elimination canonical)

/-- One finite coupled-controller opening after resolving both selected owner
variants through the complete historical dispatcher.  Only the two explicit
historical residuals or the pre-existing no-owner clearance branches remain. -/
inductive HistoricalControllerOpening
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR)) where
  | ready (result : PersistentStepResult current.toPersistentState)
  | ownerResidual
      (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (selected : SelectedEventPayload output)
      (residual : HistoricalOwnerResidual current output selected)
  | noOwner (opening : CCLCoupledController.Opening p
      (RatBox.symmetric R hR) current)

/-- Consume both global and guarded owner constructors of a low-level opening.
The implementation emits `noOwner` only for the two clearance constructors;
all selected owner cells pass through the historical dispatcher. -/
def resolveHistoricalOwners
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLCoupledTrack.State p (RatBox.symmetric R hR)}
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (canonical : ControllerCanonicalOnInputEvents current.numerical
      current.word) :
    CCLCoupledController.Opening p (RatBox.symmetric R hR) current →
      HistoricalControllerOpening p R hR current
  | .ready result => .ready result.toPersistent
  | .eventOwner output selected =>
      match resolveHistoricalControllerEvent current output selected
          squarefree degreeNonzero zeroNonzero elimination canonical with
      | .inl result => .ready result
      | .inr residual => .ownerResidual output selected.toPayload residual
  | .guardEventOwner output selected =>
      match resolveHistoricalControllerGuard current output selected
          squarefree degreeNonzero zeroNonzero elimination canonical with
      | .inl result => .ready result
      | .inr residual => .ownerResidual output selected.toPayload residual
  | .noEventOwner separation allNeither guardNone noIdenticallyZero arcs evidence
      alignment guardCurve terminal output =>
      .noOwner (.noEventOwner separation allNeither guardNone
        noIdenticallyZero arcs evidence alignment guardCurve terminal output)
  | .guardClear separation allNeither guardNone noIdenticallyZero arcs evidence
      alignment terminal output guardEvidence guardOutput =>
      .noOwner (.guardClear separation allNeither guardNone noIdenticallyZero
        arcs evidence alignment terminal output guardEvidence guardOutput)

end CCLPersistentController
end FTA
