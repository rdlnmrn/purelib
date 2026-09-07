import FTA.CCLActiveBoxCoupling
import FTA.CCLBoxCylinderIncrementalEventGrid

/-!
# History-free event points for active box--cylinder coupling

A positive x--y event already decides one incremental CCL child.  To couple
the resulting winding box to the appended tagged truncation, it is enough to
enter the active faces of that child at one rational point.  This module
removes the represented-prefix and historical-prior fields from the older
event grid and retains exactly that finite geometric construction.
-/

namespace FTA
namespace CCLActiveEventGrid

open CCL CCL.GaussianRat
open CCL.EncoderParserBridge
open FTA.AxisSafeCuts
open FTA.CCLActiveBoxCoupling
open FTA.CCLBoxCylinderIncrementalEventGrid
open FTA.CCLBranchPlan
open FTA.CCLBranchEvidence
open FTA.CCLBranchEventOwner
open FTA.CCLBranchController
open FTA.CCLEventTangentSigns
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLHermitianBox
open FTA.CCLIncrementalPhaseCompatibility
open FTA.CCLMultiOwnerGrid
open FTA.CCLNextBitFormula
open FTA.CCLOwnerDirection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventGrid
open FTA.CCLPositiveEventSemantics
open FTA.CCLStrictChildSemantics
open FTA.CCLDirectTrack
open FTA.CentralBandGrid
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Erase retained history while preserving the parser phase and decoder.
The incremental child predicate depends only on these two fields. -/
def activeOnlyState (state : RawParser.State) : RawParser.State :=
  { state with history := [] }

/-- A child admissible for the history-erased parser satisfies the original
state's incremental formula. -/
private theorem incremental_holds_of_activeOnly_canAdvanceAt
    (state : RawParser.State) (bit : Bool) (value : QI)
    (advance : CanAdvanceAt (activeOnlyState state) bit value) :
    (incrementalAdvanceFormula state bit).Holds value := by
  have formula :
      (advanceFormula (activeOnlyState state) bit).Holds value :=
    (advanceFormula_iff (activeOnlyState state) bit value).2 advance
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      have next := (stateFormula_iff
        (RawParser.step (activeOnlyState ⟨.initial, matrix, history⟩) bit)
          value).1 formula
      apply (activeFormula_iff
        (RawParser.step ⟨.initial, matrix, history⟩ bit).phase value).2
      cases bit <;> simpa [activeOnlyState, RawParser.step] using next.2
  | highUnary count =>
      have next := (stateFormula_iff
        (RawParser.step
          (activeOnlyState ⟨.highUnary count, matrix, history⟩) bit)
          value).1 formula
      apply (activeFormula_iff
        (RawParser.step ⟨.highUnary count, matrix, history⟩ bit).phase
          value).2
      cases bit <;> simpa [activeOnlyState, RawParser.step] using next.2
  | lowUnary count =>
      have next := (stateFormula_iff
        (RawParser.step
          (activeOnlyState ⟨.lowUnary count, matrix, history⟩) bit)
          value).1 formula
      apply (activeFormula_iff
        (RawParser.step ⟨.lowUnary count, matrix, history⟩ bit).phase
          value).2
      cases bit <;> simpa [activeOnlyState, RawParser.step] using next.2
  | loopUnary count =>
      have next := (stateFormula_iff
        (RawParser.step
          (activeOnlyState ⟨.loopUnary count, matrix, history⟩) bit)
          value).1 formula
      apply (activeFormula_iff
        (RawParser.step ⟨.loopUnary count, matrix, history⟩ bit).phase
          value).2
      cases bit <;> simpa [activeOnlyState, RawParser.step] using next.2
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          have next := (stateFormula_iff
            (RawParser.step (activeOnlyState
              ⟨.sector kind exponent .zero, matrix, history⟩) bit) value).1
                formula
          apply (activeFormula_iff
            (RawParser.step
              ⟨.sector kind exponent .zero, matrix, history⟩ bit).phase
              value).2
          simpa [activeOnlyState, RawParser.step] using next.2
      | one first =>
          have next := (stateFormula_iff
            (RawParser.step (activeOnlyState
              ⟨.sector kind exponent (.one first), matrix, history⟩) bit)
                value).1 formula
          apply (activeFormula_iff
            (RawParser.step
              ⟨.sector kind exponent (.one first), matrix, history⟩ bit).phase
              value).2
          simpa [activeOnlyState, RawParser.step] using next.2
      | two first second =>
          simpa [activeOnlyState, incrementalAdvanceFormula, advanceFormula]
            using formula

/-- Active-phase validity has a constructive next local bit unless the
current affine tail is the isolated completed-sector terminal.  The proof
runs the two finite Boolean child tests on the history-erased state. -/
theorem incremental_holds_localBit_of_active_notTerminal
    (state : RawParser.State) (value : QI)
    (active : RawParser.activeHolds state.phase value)
    (notTerminal : ¬TerminalSectorAt state value) :
    (incrementalAdvanceFormula state
      (localBit state.phase value)).Holds value := by
  let localState := activeOnlyState state
  have current : localState.Holds value := by
    refine ⟨?_, ?_⟩
    · simp [localState, activeOnlyState]
    · simpa [localState, activeOnlyState] using active
  by_cases falseAdvance : CanAdvanceAt localState false value
  · have bitEq : false = localBit state.phase value := by
      simpa [localState, activeOnlyState] using
        canAdvanceAt_bit_eq_localBit localState value false falseAdvance
    rw [← bitEq]
    exact incremental_holds_of_activeOnly_canAdvanceAt state false value
      falseAdvance
  · by_cases trueAdvance : CanAdvanceAt localState true value
    · have bitEq : true = localBit state.phase value := by
        simpa [localState, activeOnlyState] using
          canAdvanceAt_bit_eq_localBit localState value true trueAdvance
      rw [← bitEq]
      exact incremental_holds_of_activeOnly_canAdvanceAt state true value
        trueAdvance
    · have terminalLocal := terminalSectorAt_of_no_canAdvanceAt localState
        value current (by
          intro bit
          cases bit
          · exact falseAdvance
          · exact trueAdvance)
      have terminalState : TerminalSectorAt state value := by
        rcases terminalLocal with
          ⟨kind, exponent, first, second, third, phase, full, residual⟩
        exact .mk kind exponent first second third
          (by simpa [localState, activeOnlyState] using phase) full residual
      exact (notTerminal terminalState).elim

/-- Original-coordinate form of the history-free local-bit existence lemma. -/
theorem inputIncremental_holds_localBit_of_active_notTerminal
    (state : RawParser.State) (input : QI)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (active : (inputActiveFormula state).Holds input)
    (notTerminal : ¬TerminalSectorAt state
      (RatBox.homographic (adjugate state.matrix) input)) :
    (inputIncrementalAdvanceFormula state
      (inputLocalBit state input)).Holds input := by
  apply (inputIncrementalAdvanceFormula_iff state
    (inputLocalBit state input) input inverseDenominator).2
  simpa only [inputLocalBit] using
    incremental_holds_localBit_of_active_notTerminal state
      (RatBox.homographic (adjugate state.matrix) input)
      ((inputActiveFormula_iff state input inverseDenominator).1 active)
      notTerminal

/-- A current active-phase sample can be reconstructed in every later
winding refinement.  This is the deliberately small persistence invariant:
it retains neither a particular rational representative nor old histories. -/
structure PersistentActiveSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    (word : Prefix.Word) (current : WindingOneState p ambient) where
  sample : (next : WindingOneState p ambient) →
    next.box.Refines current.box → ActiveBoxSample word next.box

/-- Denominator separation seeds the empty word with a persistent active
sample: its active formula is `True`, so the center of every later rational
box suffices. -/
def initialPersistentActiveSamples
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse []).matrix)) :
    PersistentActiveSamples [] separation.state where
  sample next nextRefines :=
    { point := next.box.center
      inside := next.box.contains_center
      inverseDenominator := separation_denominator_ne separation
        (nextRefines.contains next.box.contains_center)
      active := by
        simp [inputActiveFormula, RawParser.parse, RawParser.initialState,
          activeFormula, FTA.CCLFormulaPullback.Formula.pullback,
          CCLParserGeometry.Formula.Holds] }

/-- The minimal grid data needed to enter one selected incremental child.
There is deliberately no represented old word and no historical sign list. -/
structure Data
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (selected : IncrementalEventPayload output)
    (next : WindingOneState p ambient)
    (_nextRefines : next.box.Refines output.state.box) where
  base : QI
  baseStrict : next.box.StrictContains base
  baseNonzero : base ≠ 0
  direction : TangentDirection
    (eventPayloadIncrementalActiveOwnerForms selected) base
  selectedStrictAtBase :
    ∀ form ∈ eventPayloadIncrementalStrictPriorForms selected,
      0 < eventPayloadCanonicalValue selected form * form.eval base
  selectedActiveResidual :
    ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
      |form.eval base| < approximateBoundaryBudget direction
        (checkpointEventPriorForms selected next.box)

namespace Data

/-- The rational point obtained by taking the common inward tangent step. -/
def point
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines output.state.box}
    (data : Data output selected next nextRefines) : QI :=
  step data.base
    (multiOwnerEpsilon data.direction
      (checkpointEventPriorForms selected next.box))
    data.direction.vector

/-- Every retained strict prior is nonzero at the event-grid base. -/
theorem priors_nonzero
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines output.state.box}
    (data : Data output selected next nextRefines) :
    ∀ form ∈ checkpointEventPriorForms selected next.box,
      form.eval data.base ≠ 0 := by
  intro form member
  simp only [checkpointEventPriorForms, List.mem_append,
    List.mem_singleton] at member
  rcases member with (selectedStrict | boxForm) | normForm
  · intro zero
    have positive := data.selectedStrictAtBase form selectedStrict
    rw [zero] at positive
    norm_num at positive
  · exact (boxForms_pos_of_strictContains data.baseStrict form boxForm).ne'
  · subst form
    simpa [eval_affineNormForm] using (normSq_pos data.baseNonzero).ne'

/-- The chosen tangent step enters every active owner face. -/
theorem entered
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines output.state.box}
    (data : Data output selected next nextRefines) :
    ∀ form ∈ eventPayloadIncrementalActiveOwnerForms selected,
      0 < form.eval (point data) := by
  simpa only [point] using
    enters_all_boundaries_of_residual data.direction
      (checkpointEventPriorForms selected next.box)
      (priors_nonzero data) data.selectedActiveResidual

/-- The same step preserves the sign of every strict and box prior. -/
theorem preserved
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines output.state.box}
    (data : Data output selected next nextRefines) :
    ∀ form ∈ checkpointEventPriorForms selected next.box,
      0 < form.eval data.base * form.eval (point data) := by
  simpa only [point] using
    preserves_all_priors data.direction
      (checkpointEventPriorForms selected next.box) (priors_nonzero data)

/-- The entered point remains in the requested later winding box. -/
theorem point_inside
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines output.state.box}
    (data : Data output selected next nextRefines) :
    next.box.Contains (point data) := by
  change next.box.Contains (step data.base
    (multiOwnerEpsilon data.direction
      (checkpointEventPriorForms selected next.box))
    data.direction.vector)
  apply multiOwner_step_mem_box_of_strict_priors data.direction
    (priors_nonzero data) next.box
    (boxForms_pos_of_strictContains data.baseStrict)
  intro form member
  simp [checkpointEventPriorForms, member]

/-- The tangent-entered point satisfies exactly the selected incremental
formula, without any premise about the old parser history. -/
theorem incremental_holds
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines output.state.box}
    (data : Data output selected next nextRefines) :
    (inputIncrementalAdvanceFormula state selected.bit).Holds
      (point data) := by
  apply eventPayloadIncremental_holds_of_owner_form_lists selected (point data)
  · exact entered data
  · intro form member
    apply FTA.CCLPositiveEventGrid.mul_pos_trans
      (data.selectedStrictAtBase form member)
    apply preserved data form
    simp [checkpointEventPriorForms, member]

/-- The old inverse decoder remains affine at the entered point. -/
theorem inverseDenominator
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {selected : IncrementalEventPayload output}
    {next : WindingOneState p ambient}
    {nextRefines : next.box.Refines output.state.box}
    (data : Data output selected next nextRefines) :
    (adjugate state.matrix).c * point data +
      (adjugate state.matrix).d ≠ 0 :=
  separation_denominator_ne output
    (nextRefines.contains (point_inside data))

/-- A denominator separation for the successor parser turns the history-free
event point into the active box sample used by the metric coupling. -/
def activeSampleOfSuccessorSeparation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {word : Prefix.Word}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse word).matrix)}
    {selected : IncrementalEventPayload output}
    {successor : WindingOneState p ambient}
    (successorSeparation : CCLDenominator.SeparationOutput p ambient successor
      (adjugate
        (RawParser.step (RawParser.parse word) selected.bit).matrix))
    (refinesOld : successorSeparation.state.box.Refines output.state.box)
    (data : Data output selected successorSeparation.state refinesOld) :
    ActiveBoxSample (word ++ [selected.bit])
      successorSeparation.state.box :=
  ActiveBoxSample.ofIncrementalStep selected.bit (point data)
    (point_inside data) (inverseDenominator data)
    (separation_denominator_ne successorSeparation (point_inside data))
    (incremental_holds data)

end Data

/-- The existing static rational cap constructs the minimal history-free
grid in every later winding box. -/
def staticData
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
    {searchDirection : QI}
    (search : classifiedTangentDirection? selected = some searchDirection) :
    Data output selected next nextRefines where
  base := slopeCappedLocalizedEventPoint selected squarefree next
    (checkpointStaticGridCap selected next)
    (checkpointStaticGridCap_pos selected next zeroNonzero)
  baseStrict := slopeCappedLocalizedEventPoint_strictContains output selected
    squarefree degreeNonzero elimination next nextRefines
      (checkpointStaticGridCap selected next)
      (checkpointStaticGridCap_pos selected next zeroNonzero)
  baseNonzero := slopeCappedLocalizedEventPoint_ne_zero selected squarefree next
    (checkpointStaticGridCap selected next)
    (checkpointStaticGridCap_pos selected next zeroNonzero)
    (checkpointStaticGridCap_le_zeroResidual selected next)
  direction := slopeCappedLocalizedClassifiedTangentDirection search squarefree
    next (checkpointStaticGridCap selected next)
      (checkpointStaticGridCap_pos selected next zeroNonzero)
  selectedStrictAtBase := slopeCappedLocalizedEventStrict selected squarefree
    next (checkpointStaticGridCap selected next)
      (checkpointStaticGridCap_pos selected next zeroNonzero)
  selectedActiveResidual := by
    intro form member
    have coefficientBound := mul_lt_mul_of_pos_right
      (selectedSlopeActiveCoefficient_lt_sum selected member)
      (checkpointStaticGridCap_pos selected next zeroNonzero)
    exact (slopeCappedLocalizedEventActive_le selected squarefree next
      (checkpointStaticGridCap selected next)
      (checkpointStaticGridCap_pos selected next zeroNonzero) member).trans_lt
        (coefficientBound.trans
          (checkpointStaticGridCap_residualBudget output selected squarefree
            degreeNonzero zeroNonzero elimination next nextRefines search))

/-- For a complete selected event of a parsed word, tangent-table totality
discharges the last input of `staticData` in every parser phase. -/
def parsedStaticData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {word : Prefix.Word}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate (RawParser.parse word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    Data output selected.toIncrementalPayload next nextRefines :=
  staticData output selected.toIncrementalPayload squarefree degreeNonzero
    zeroNonzero elimination next nextRefines
      (parsedClassifiedTangentDirection_spec selected)

/-- Outside a completed sector, the incremental owner alone has a total
history-free tangent table and therefore constructs the same static grid. -/
def parsedIncrementalStaticData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {word : Prefix.Word}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate (RawParser.parse word).matrix))
    (selected : IncrementalEventPayload output)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines output.state.box) :
    Data output selected next nextRefines :=
  staticData output selected squarefree degreeNonzero zeroNonzero elimination
    next nextRefines
      (parsedIncrementalClassifiedTangentDirection_spec selected notCompleted)

/-- A complete positive event followed by successor denominator separation
now yields the active metric sample directly.  The old represented-prefix
invariant is absent from the statement. -/
def activeSampleOfParsedEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {word : Prefix.Word}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate (RawParser.parse word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {successor : WindingOneState p (RatBox.symmetric R hR)}
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) successor
      (adjugate (RawParser.step (RawParser.parse word)
        selected.toIncrementalPayload.bit).matrix))
    (refinesOld : successorSeparation.state.box.Refines output.state.box) :
    ActiveBoxSample (word ++ [selected.toIncrementalPayload.bit])
      successorSeparation.state.box := by
  let data := parsedStaticData output selected squarefree degreeNonzero
    zeroNonzero elimination successorSeparation.state refinesOld
  exact Data.activeSampleOfSuccessorSeparation successorSeparation refinesOld
    data

/-- The positive-event construction persists through every later refinement
of the successor denominator-separated box.  Each call recomputes a finite
rational tangent point in that requested box; no fixed representative is
transported. -/
def persistentActiveSamplesOfParsedEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {word : Prefix.Word}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate (RawParser.parse word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {successor : WindingOneState p (RatBox.symmetric R hR)}
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) successor
      (adjugate (RawParser.step (RawParser.parse word)
        selected.toIncrementalPayload.bit).matrix))
    (refinesOld : successorSeparation.state.box.Refines output.state.box) :
    PersistentActiveSamples
      (word ++ [selected.toIncrementalPayload.bit])
      successorSeparation.state where
  sample next nextRefines := by
    have nextRefinesOld : next.box.Refines output.state.box :=
      nextRefines.trans refinesOld
    let data := parsedStaticData output selected squarefree degreeNonzero
      zeroNonzero elimination next nextRefinesOld
    exact ActiveBoxSample.ofIncrementalStep
      selected.toIncrementalPayload.bit (Data.point data)
      (Data.point_inside data)
      (separation_denominator_ne output
        (nextRefinesOld.contains (Data.point_inside data)))
      (separation_denominator_ne successorSeparation
        (nextRefines.contains (Data.point_inside data)))
      (Data.incremental_holds data)

/-- A history-free incremental owner outside a completed sector supplies the
same persistent active provider as a complete owner.  The phase exclusion is
exactly the hypothesis needed by the finite incremental tangent table; no
historical parser predicate is reconstructed. -/
def persistentActiveSamplesOfParsedIncrementalEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {word : Prefix.Word}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate (RawParser.parse word).matrix))
    (selected : IncrementalEventPayload output)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    {successor : WindingOneState p (RatBox.symmetric R hR)}
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) successor
      (adjugate (RawParser.step (RawParser.parse word) selected.bit).matrix))
    (refinesOld : successorSeparation.state.box.Refines output.state.box) :
    PersistentActiveSamples (word ++ [selected.bit])
      successorSeparation.state where
  sample next nextRefines := by
    have nextRefinesOld : next.box.Refines output.state.box :=
      nextRefines.trans refinesOld
    let data := parsedIncrementalStaticData output selected notCompleted
      squarefree degreeNonzero zeroNonzero elimination next nextRefinesOld
    exact ActiveBoxSample.ofIncrementalStep selected.bit (Data.point data)
      (Data.point_inside data)
      (separation_denominator_ne output
        (nextRefinesOld.contains (Data.point_inside data)))
      (separation_denominator_ne successorSeparation
        (nextRefines.contains (Data.point_inside data)))
      (Data.incremental_holds data)

/-- An all-clear strict-cell bit transports any persistent active sample
provider through the planned box.  The provider supplies a fresh old-active
point in each requested refinement; strict interval signs identify its local
bit with the plan's center bit, and terminal separation rules out the sole
zero-residual exception. -/
def persistentActiveSamplesOfPlannedBit
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLDirectTrack.State p ambient}
    (currentSamples : PersistentActiveSamples current.word current.numerical)
    (planned : CCLDirectTrack.PlannedBit current)
    {successor : WindingOneState p ambient}
    (successorSeparation : CCLDenominator.SeparationOutput p ambient successor
      (adjugate (RawParser.step (RawParser.parse current.word)
        planned.decision.bit).matrix))
    (refinesPlanned :
      successorSeparation.state.box.Refines planned.numerical.box) :
    PersistentActiveSamples
      (current.word ++ [planned.decision.bit]) successorSeparation.state where
  sample next nextRefines := by
    have nextRefinesPlanned : next.box.Refines planned.numerical.box :=
      nextRefines.trans refinesPlanned
    let oldSample := currentSamples.sample next
      (nextRefinesPlanned.trans planned.refines)
    have insidePlanned : planned.numerical.box.Contains oldSample.point :=
      nextRefinesPlanned.contains oldSample.inside
    have localHolds := inputIncremental_holds_localBit_of_active_notTerminal
      (RawParser.parse current.word) oldSample.point
      oldSample.inverseDenominator oldSample.active
      (planned.notTerminal insidePlanned)
    have localBitEq :
        inputLocalBit (RawParser.parse current.word) oldSample.point =
          inputLocalBit (RawParser.parse current.word)
            planned.numerical.box.center := by
      apply inputLocalBit_eq_of_inputForms_sameSigns
        (RawParser.parse current.word) oldSample.point
          planned.numerical.box.center oldSample.inverseDenominator
            (planned.inverseDenominator planned.numerical.box.contains_center)
      intro form member
      rw [inputForms] at member
      rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
      have same := eval_center_mul_pos_of_strictSignCheck source.form
        (planned.strictSigns source sourceMember) insidePlanned
      simpa only [_root_.mul_comm] using same
    have pointBit :
        inputLocalBit (RawParser.parse current.word) oldSample.point =
          planned.decision.bit :=
      localBitEq.trans planned.decisionBit.symm
    rw [pointBit] at localHolds
    exact ActiveBoxSample.ofIncrementalStep planned.decision.bit
      oldSample.point oldSample.inside oldSample.inverseDenominator
      (separation_denominator_ne successorSeparation
        (nextRefines.contains oldSample.inside)) localHolds

end CCLActiveEventGrid
end FTA
