import FTA.CCLActiveEventGrid
import FTA.CCLPositiveAllNeither

/-!
# Canonical algebraic support for the active parser phase

The history-free metric state needs canonical event truth only for the current
active parser predicate.  A selected incremental event propagates that truth
to every later event on the same winding track, including a transition into a
completed two-bit sector.  This is strictly weaker than reconstructing the
retained historical parser formula and is exactly what the active terminal-
guard contradiction consumes.
-/

namespace FTA
namespace CCLActiveCanonicalEvent

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLActiveBoxCoupling
open FTA.CCLBranchController
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchEvidence
open FTA.CCLBranchPartition
open FTA.CCLBranchPlan
open FTA.CCLCanonicalEvent
open FTA.CCLCountOneClassification
open FTA.CCLEventExtraction
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLGuardCellClearance
open FTA.CCLHermitianBox
open FTA.CCLNextBitFormula
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventLocalization
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventTrack
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial CCL.GaussianRat

/-- Follow the unique count-one descendant after classifying exactly the
atoms of the current active parser predicate.  The ordinary event table
contains only the two proposed child predicates, so this finite refinement is
needed before the active predicate has a canonical algebraic truth value. -/
def activeFormulaClassification
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :=
  followCountOneConditions cell.branch.factor
    (cell.branch.computeEventSigns cell.parent).refined
    (eventFormulaPolynomials (inputActiveFormula state) path)

/-- Repackage the active-formula descendant as an ordinary input event cell.
The existing child relations restrict to the selected divisor. -/
def activeFormulaInputCell
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : InputEventCell state event :=
  let classification := activeFormulaClassification cell
  { branch :=
      { factor := classification.branch.factor
        relations := cell.branch.relations.ofDvd
          classification.branch.factor.input classification.divides }
    divides := classification.divides.trans cell.divides
    parent := (classification.branch.computeEventSigns
      classification.parent).refined
    refines := FTA.SturmTransducer.RationalInterval.refines_trans
      classification.signRefines cell.signRefines }

/-- Continue that descendant through the child conditions of an arbitrary
comparison parser state. -/
def activeFormulaConditionClassification
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (conditionState : RawParser.State) :=
  let activeClassification := activeFormulaClassification cell
  let activeSigns := activeClassification.branch.computeEventSigns
    activeClassification.parent
  followCountOneConditions activeClassification.branch.factor
    activeSigns.refined (inputEventPolynomials conditionState path)

/-- Repackage the common descendant under the comparison state's child
conditions.  This lets a later active event be compared with the preceding
incremental owner without asserting that active atoms occur in the ordinary
two-child table. -/
def activeFormulaReclassifiedInputCell
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (conditionState : RawParser.State) :
    InputEventCell conditionState event :=
  let activeClassification := activeFormulaClassification cell
  let conditionClassification :=
    activeFormulaConditionClassification cell conditionState
  { branch := conditionClassification.branch
    divides := conditionClassification.divides.trans
      (activeClassification.divides.trans cell.divides)
    parent := conditionClassification.parent
    refines :=
      FTA.SturmTransducer.RationalInterval.refines_trans
        conditionClassification.refines
        (FTA.SturmTransducer.RationalInterval.refines_trans
          activeClassification.signRefines cell.signRefines) }

/-- Canonical truth of only the active parser predicate at one classified
algebraic event. -/
def activeFormulaCanonicalCheck
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : Bool :=
  formulaEvalWith (inputActiveFormula state)
    (inputEventCanonicalValue (activeFormulaInputCell cell))

/-- The projected active input cell agrees with the active formula's direct
condition classifier. -/
theorem activeFormulaCanonicalCheck_eq_eventFormulaCheck
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    activeFormulaCanonicalCheck cell =
      eventFormulaCheck (activeFormulaClassification cell).branch
        (activeFormulaClassification cell).parent := by
  rw [eventFormulaCheck_eq_canonicalEval]
  apply formulaEvalWith_eq_of_atomTests
  intro atom member
  let classification := activeFormulaClassification cell
  let formulaSigns := classification.branch.computeEventSigns
    classification.parent
  let refinedCell := activeFormulaInputCell cell
  let refinedSigns := refinedCell.branch.computeEventSigns refinedCell.parent
  have polynomialMember : clearedForm atom.form path ∈
      eventFormulaPolynomials (inputActiveFormula state) path :=
    List.mem_map.mpr ⟨atom, member, rfl⟩
  have lower : formulaSigns.refined.interval.lower ≤
      refinedSigns.refined.interval.lower := by
    simpa only [formulaSigns, refinedSigns, refinedCell,
      activeFormulaInputCell, classification] using refinedSigns.refines.1
  have upper : refinedSigns.refined.interval.lower ≤
      formulaSigns.refined.interval.upper := by
    have bound := refinedSigns.refined.proper.le.trans refinedSigns.refines.2
    simpa only [formulaSigns, refinedSigns, refinedCell,
      activeFormulaInputCell, classification] using bound
  have agreement :=
    ConditionRelations.canonicalEventValue_holds_iff_between
      classification.branch.relations classification.parent formulaSigns
      polynomialMember atom.sign lower upper
  simpa only [activeFormulaCanonicalCheck, inputEventCanonicalValue,
    refinedCell, refinedSigns, formulaSigns, classification,
    activeFormulaInputCell] using agreement.symm

/-- The active-formula oracle agrees with the same descendant repackaged
under any comparison parser state's child conditions. -/
theorem activeFormulaCanonicalCheck_eq_reclassifiedInputCell
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (conditionState : RawParser.State) :
    activeFormulaCanonicalCheck cell =
      formulaEvalWith (inputActiveFormula state)
        (inputEventCanonicalValue
          (activeFormulaReclassifiedInputCell cell conditionState)) := by
  rw [activeFormulaCanonicalCheck_eq_eventFormulaCheck,
    eventFormulaCheck_eq_canonicalEval]
  apply formulaEvalWith_eq_of_atomTests
  intro atom member
  let activeClassification := activeFormulaClassification cell
  let activeSigns := activeClassification.branch.computeEventSigns
    activeClassification.parent
  let conditionClassification :=
    activeFormulaConditionClassification cell conditionState
  let conditionSigns := conditionClassification.branch.computeEventSigns
    conditionClassification.parent
  have polynomialMember : clearedForm atom.form path ∈
      eventFormulaPolynomials (inputActiveFormula state) path :=
    List.mem_map.mpr ⟨atom, member, rfl⟩
  have lower : activeSigns.refined.interval.lower ≤
      conditionSigns.refined.interval.lower :=
    conditionClassification.refines.1.trans conditionSigns.refines.1
  have upper : conditionSigns.refined.interval.lower ≤
      activeSigns.refined.interval.upper :=
    (conditionSigns.refined.proper.le.trans
      conditionSigns.refines.2).trans conditionClassification.refines.2
  have agreement :=
    ConditionRelations.canonicalEventValue_holds_iff_ofDvd_between
      activeClassification.branch.relations activeClassification.parent
      activeSigns conditionClassification.branch.factor.input
      conditionClassification.divides polynomialMember atom.sign lower upper
  simpa only [inputEventCanonicalValue,
    activeFormulaReclassifiedInputCell,
    activeFormulaConditionClassification, conditionClassification,
    conditionSigns, activeClassification, activeSigns] using agreement

/-- Provenance-independent active truth at every later positive event. -/
def ActiveFormulaCanonicalOnInputEvents
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) (word : Prefix.Word) : Prop :=
  ∀ (separation : CCLDenominator.SeparationOutput p ambient numerical
      (adjugate (RawParser.parse word).matrix))
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path separation.state.box}
    (cell : InputEventCell (RawParser.parse word) event),
    activeFormulaCanonicalCheck cell = true

/-- Finite-family form consumed by the executable controller. -/
def ActiveControllerCanonicalOnInputEvents
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) (word : Prefix.Word) : Prop :=
  ∀ (separation : CCLDenominator.SeparationOutput p ambient numerical
      (adjugate (RawParser.parse word).matrix)),
    (∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse word) separation,
      activeFormulaCanonicalCheck candidate.inputCell = true) ∧
    (∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse word) separation,
      activeFormulaCanonicalCheck candidate.inputCell = true)

theorem ActiveFormulaCanonicalOnInputEvents.controllerCanonical
    {p : GaussianPolynomial} {ambient : RatBox}
    {numerical : WindingOneState p ambient} {word : Prefix.Word}
    (valid : ActiveFormulaCanonicalOnInputEvents numerical word) :
    ActiveControllerCanonicalOnInputEvents numerical word := by
  intro separation
  constructor
  · intro candidate _member
    exact valid separation candidate.inputCell
  · intro candidate _member
    exact valid separation candidate.inputCell

/-- Active support is required only while a parser waits for its third sector
bit. -/
def CompletedSectorActiveControllerCanonicalData
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) (word : Prefix.Word) : Prop :=
  (∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second)) →
    ActiveControllerCanonicalOnInputEvents numerical word

theorem ActiveControllerCanonicalOnInputEvents.refine
    {p : GaussianPolynomial} {ambient : RatBox}
    {outer inner : WindingOneState p ambient} {word : Prefix.Word}
    (valid : ActiveControllerCanonicalOnInputEvents outer word)
    (refines : inner.box.Refines outer.box) :
    ActiveControllerCanonicalOnInputEvents inner word := by
  intro separation
  exact valid (separation.rebase refines)

theorem CompletedSectorActiveControllerCanonicalData.refine
    {p : GaussianPolynomial} {ambient : RatBox}
    {outer inner : WindingOneState p ambient} {word : Prefix.Word}
    (valid : CompletedSectorActiveControllerCanonicalData outer word)
    (refines : inner.box.Refines outer.box) :
    CompletedSectorActiveControllerCanonicalData inner word := by
  intro completed
  exact ActiveControllerCanonicalOnInputEvents.refine
    (valid completed) refines

/-- Outside the matrix-updating third sector bit, the next active predicate is
literally the pulled-back incremental predicate. -/
theorem inputActiveFormula_step_eq_inputIncremental_of_not_completed
    (state : RawParser.State) (bit : Bool)
    (notCompleted : ¬∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second)) :
    inputActiveFormula (RawParser.step state bit) =
      inputIncrementalAdvanceFormula state bit := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial => cases bit <;> rfl
  | highUnary count => cases bit <;> rfl
  | lowUnary count => cases bit <;> rfl
  | loopUnary count => cases bit <;> rfl
  | sector kind exponent bits =>
      cases bits with
      | zero => cases bit <;> rfl
      | one first => cases bit <;> rfl
      | two first second =>
          exact (notCompleted ⟨kind, exponent, first, second, rfl⟩).elim

/-- In a completed two-bit sector, active truth and two false children force
one candidate-sector residual to vanish.  Historical block constraints play
no role in this finite sign-table argument. -/
theorem completedSector_residualZero_of_active_neither
    (state : RawParser.State) (value : HermitianForm → ℚ)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (active : formulaEvalWith (inputActiveFormula state) value = true)
    (neither : ∀ bit,
      formulaEvalWith (inputAdvanceFormula state bit) value = false)
    (residualNonnegative : ∀ third,
      0 ≤ value (FTA.CCLFormulaPullback.pullbackForm (adjugate state.matrix)
        (residualForm kind exponent
          (RawParser.sectorOfBits first second third)))) :
    ∃ third, value
      (FTA.CCLFormulaPullback.pullbackForm (adjugate state.matrix)
        (residualForm kind exponent
          (RawParser.sectorOfBits first second third))) = 0 := by
  rcases state with ⟨statePhase, matrix, history⟩
  change statePhase = .sector kind exponent (.two first second) at phase
  subst statePhase
  have falseCheck := neither false
  have trueCheck := neither true
  cases first with
  | false =>
      cases second with
      | false =>
          simp [inputActiveFormula, inputAdvanceFormula, advanceFormula,
            activeFormula, radialFormula, sectorBitsFormula, sectorFormula,
            Formula.pullback, formulaEvalWith, RawParser.sectorOfBits,
            SignTest.Holds] at active falseCheck trueCheck
          by_cases split : 0 ≤ value
              (FTA.CCLFormulaPullback.pullbackForm (adjugate matrix)
                (imagComparisonForm
                  (normalizedMatrix kind exponent RawParser.identityMatrix)
                  (2 : ℚ)⁻¹))
          · refine ⟨true, ?_⟩
            have nonnegative := residualNonnegative true
            have nonpositive := trueCheck active.1 active.2.1 split
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
          · refine ⟨false, ?_⟩
            have negative := lt_of_not_ge split
            have nonnegative := residualNonnegative false
            have nonpositive := falseCheck active.1 active.2.1 active.2.2
              negative
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
      | true =>
          simp [inputActiveFormula, inputAdvanceFormula, advanceFormula,
            activeFormula, radialFormula, sectorBitsFormula, sectorFormula,
            Formula.pullback, formulaEvalWith, RawParser.sectorOfBits,
            SignTest.Holds] at active falseCheck trueCheck
          by_cases split : value
              (FTA.CCLFormulaPullback.pullbackForm (adjugate matrix)
                (realComparisonForm
                  (normalizedMatrix kind exponent RawParser.identityMatrix)
                  (-1 / 2))) ≤ 0
          · refine ⟨true, ?_⟩
            have nonnegative := residualNonnegative true
            have nonpositive := trueCheck active.1 split active.2.2
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
          · refine ⟨false, ?_⟩
            have positive := lt_of_not_ge split
            have nonnegative := residualNonnegative false
            have nonpositive := falseCheck active.1 positive active.2.1
              active.2.2
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
  | true =>
      cases second with
      | false =>
          simp [inputActiveFormula, inputAdvanceFormula, advanceFormula,
            activeFormula, radialFormula, sectorBitsFormula, sectorFormula,
            Formula.pullback, formulaEvalWith, RawParser.sectorOfBits,
            SignTest.Holds] at active falseCheck trueCheck
          by_cases split : value
              (FTA.CCLFormulaPullback.pullbackForm (adjugate matrix)
                (imagComparisonForm
                  (normalizedMatrix kind exponent RawParser.identityMatrix)
                  (-1 / 2))) ≤ 0
          · refine ⟨true, ?_⟩
            have nonnegative := residualNonnegative true
            have nonpositive := trueCheck active.1 active.2.1 split
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
          · refine ⟨false, ?_⟩
            have positive := lt_of_not_ge split
            have nonnegative := residualNonnegative false
            have nonpositive := falseCheck active.1 active.2.1 positive
              active.2.2
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
      | true =>
          simp [inputActiveFormula, inputAdvanceFormula, advanceFormula,
            activeFormula, radialFormula, sectorBitsFormula, sectorFormula,
            Formula.pullback, formulaEvalWith, RawParser.sectorOfBits,
            SignTest.Holds] at active falseCheck trueCheck
          by_cases split : 0 ≤ value
              (FTA.CCLFormulaPullback.pullbackForm (adjugate matrix)
                (realComparisonForm
                  (normalizedMatrix kind exponent RawParser.identityMatrix)
                  (2 : ℚ)⁻¹))
          · refine ⟨true, ?_⟩
            have nonnegative := residualNonnegative true
            have nonpositive := trueCheck active.1 split active.2.2
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative
          · refine ⟨false, ?_⟩
            have negative := lt_of_not_ge split
            have nonnegative := residualNonnegative false
            have nonpositive := falseCheck active.1 active.2.1 negative
              active.2.2
            simpa [RawParser.sectorOfBits] using
              le_antisymm nonpositive nonnegative

/-- Event specialization of the active completed-sector sign table. -/
theorem inputEventCanonical_residualZero_of_completedSector_active
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (checks : cell.ownerChecks = (false, false))
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (active : formulaEvalWith (inputActiveFormula state)
      (inputEventCanonicalValue cell) = true) :
    ∃ third, inputEventCanonicalValue cell
      (FTA.CCLFormulaPullback.pullbackForm (adjugate state.matrix)
        (residualForm kind exponent
          (RawParser.sectorOfBits first second third))) = 0 := by
  apply completedSector_residualZero_of_active_neither state
    (inputEventCanonicalValue cell) kind exponent first second phase active
    (inputEventCanonical_fails_of_neither cell checks)
  intro third
  exact inputEventCanonical_residual_nonneg cell kind exponent
    (RawParser.sectorOfBits first second third)

/-- Active canonical terminality gives the same exact residual divisibility
as the historical-current formulation. -/
theorem inputEvent_residualPolynomial_dvd_of_completedSector_active
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event)
    (checks : cell.ownerChecks = (false, false))
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (active : formulaEvalWith (inputActiveFormula state)
      (inputEventCanonicalValue cell) = true) :
    ∃ third,
      cell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm
          (FTA.CCLFormulaPullback.pullbackForm (adjugate state.matrix)
            (residualForm kind exponent
              (RawParser.sectorOfBits first second third))) path).toPolynomial := by
  rcases inputEventCanonical_residualZero_of_completedSector_active cell checks
      kind exponent first second phase active with ⟨third, residualZero⟩
  refine ⟨third, ConditionRelations.dvd_of_canonicalEventValue_eq_zero
    cell.branch.relations cell.parent
      (cell.branch.computeEventSigns cell.parent)
      (completedSector_residualPolynomial_mem_inputEvent state path kind
        exponent first second third phase) ?_⟩
  simpa only [inputEventCanonicalValue] using residualZero

/-- Refining an event factor against the active formula preserves both
already-classified child-owner bits. -/
theorem activeFormulaInputCell_ownerChecks_eq
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
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    cell.ownerChecks = (activeFormulaInputCell cell).ownerChecks := by
  let localOutput : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR) output.state (adjugate state.matrix) :=
    { state := output.state
      refines := RatBox.refines_refl output.state.box
      margin := output.margin
      margin_pos := output.margin_pos
      lower := output.lower }
  have formulaEquality (bit : Bool) :
      formulaEvalWith (inputAdvanceFormula state bit)
          (inputEventCanonicalValue cell) =
        formulaEvalWith (inputAdvanceFormula state bit)
          (inputEventCanonicalValue (activeFormulaInputCell cell)) := by
    apply formulaEvalWith_inputEvents_eq_of_refinement
      (firstOutput := output) (secondOutput := localOutput)
      cell (activeFormulaInputCell cell) squarefree degreeNonzero elimination
    · intro atom member
      exact clearedForm_mem_inputEventPolynomials_of_advance_atom state path
        bit atom member
    · intro atom member
      exact clearedForm_mem_inputEventPolynomials_of_advance_atom state path
        bit atom member
  rw [inputEventPair_eq_canonical, inputEventPair_eq_canonical]
  exact Prod.ext (formulaEquality false) (formulaEquality true)

/-- An all-neither completed event contradicts terminal separation using only
the active canonical predicate. -/
theorem inputCell_allNeither_excludes_completedSectorActiveData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path separation.state.box}
    (cell : InputEventCell (RawParser.parse word) event)
    (checks : cell.ownerChecks = (false, false))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse word).phase =
      .sector kind exponent (.two first second))
    (activeCanonical : activeFormulaCanonicalCheck cell = true) :
    False := by
  let refinedCell := activeFormulaInputCell cell
  have refinedChecks : refinedCell.ownerChecks = (false, false) := by
    rw [← activeFormulaInputCell_ownerChecks_eq cell squarefree
      degreeNonzero elimination]
    exact checks
  have refinedCanonical : formulaEvalWith
      (inputActiveFormula (RawParser.parse word))
      (inputEventCanonicalValue refinedCell) = true := by
    simpa only [refinedCell, activeFormulaCanonicalCheck] using
      activeCanonical
  rcases inputEvent_residualPolynomial_dvd_of_completedSector_active
      refinedCell refinedChecks kind exponent first second phase
      refinedCanonical with ⟨third, divides⟩
  exact (inputEvent_residual_not_dvd_of_terminalOutputData numerical word
    separation refinedCell squarefree degreeNonzero elimination terminalOutput
    next nextRefines kind exponent first second third phase) divides

/-- Finite guard-controller form of the active completed-sector
contradiction. -/
theorem activeAllNeither_excludes_completedSector_guard_cellControllerData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (activeValid : ActiveControllerCanonicalOnInputEvents numerical word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
      (RawParser.parse word) separation,
      candidate.inputCell.ownerChecks = (false, false))
    (sourceCell : SourceEventGuardCell p separation.state.box)
    (sourceMember : sourceCell ∈ separatedEventGuardCells p
      (RawParser.parse word) separation)
    (event : RelevantCurveEvent p
      sourceCell.partition.entry.chart.path separation.state.box)
    (eventMember : event ∈
      CCLBranchEvent.EventGuardCell.relevantCurveEvents sourceCell.item.cell)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse word).phase =
      .sector kind exponent (.two first second)) :
    False := by
  let sourceEvent : SourceGuardCurveEvent p separation.state.box :=
    ⟨sourceCell, event, eventMember⟩
  have sourceEventMember : sourceEvent ∈ separatedSourceGuardCurveEvents p
      (RawParser.parse word) separation := by
    simpa only [separatedSourceGuardCurveEvents, sourceEvent] using
      sourceGuardCurveEvent_mem_of_cell_event sourceCell sourceMember event
        eventMember
  rcases separatedGuardInputEventCells_exists_of_sourceEvent_mem separation
      sourceEvent sourceEventMember with
    ⟨candidate, candidateMember, _sourceEquality⟩
  apply inputCell_allNeither_excludes_completedSectorActiveData numerical word
    separation candidate.inputCell (guardNone candidate candidateMember)
      squarefree degreeNonzero elimination terminalOutput next nextRefines kind
        exponent first second phase
  exact (activeValid separation).2 candidate candidateMember

/-- A selected incremental owner becomes active-canonical at every later
positive event on the same nested winding track. -/
theorem activeFormulaCanonicalCheck_of_selected_incremental_refinement
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State} {bit : Bool}
    {firstOutput : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix)}
    {secondOutput : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      firstOutput.state (adjugate (RawParser.step state bit).matrix)}
    {firstPath secondPath : ProjectivePath.Path}
    {firstEvent : RelevantCurveEvent p firstPath firstOutput.state.box}
    {secondEvent : RelevantCurveEvent p secondPath secondOutput.state.box}
    (firstCell : InputEventCell state firstEvent)
    (secondCell : InputEventCell (RawParser.step state bit) secondEvent)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (notCompleted : ¬∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second))
    (selected : formulaEvalWith (inputIncrementalAdvanceFormula state bit)
      (inputEventCanonicalValue firstCell) = true) :
    activeFormulaCanonicalCheck secondCell = true := by
  let reclassified : InputEventCell state secondEvent :=
    activeFormulaReclassifiedInputCell secondCell state
  have equality :
      formulaEvalWith (inputIncrementalAdvanceFormula state bit)
          (inputEventCanonicalValue firstCell) =
        formulaEvalWith (inputIncrementalAdvanceFormula state bit)
          (inputEventCanonicalValue reclassified) := by
    apply formulaEvalWith_eq_of_atomTests
    intro atom member
    apply inputEventCanonicalValue_test_iff_of_refinement
      (firstDenominatorState := state)
      (secondDenominatorState := RawParser.step state bit)
      (firstCellState := state) (secondCellState := state)
      (firstOutput := firstOutput) (secondOutput := secondOutput)
      firstCell reclassified squarefree degreeNonzero elimination atom.form
    · exact clearedForm_mem_inputEventPolynomials_of_advance_atom state
        firstPath bit atom
          (inputIncrementalAdvanceFormula_atoms_subset state bit atom member)
    · exact clearedForm_mem_inputEventPolynomials_of_advance_atom state
        secondPath bit atom
          (inputIncrementalAdvanceFormula_atoms_subset state bit atom member)
  have transferred :
      formulaEvalWith (inputIncrementalAdvanceFormula state bit)
        (inputEventCanonicalValue reclassified) = true := by
    rw [← equality]
    exact selected
  rw [activeFormulaCanonicalCheck_eq_reclassifiedInputCell secondCell state,
    inputActiveFormula_step_eq_inputIncremental_of_not_completed state bit
      notCompleted]
  exact transferred

/-- Numerical/word propagation of active canonical support from one selected
incremental event. -/
theorem activeFormulaCanonicalOnInputEvents_ofSelectedIncrementalData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    (selected : IncrementalEventPayload separation)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    ActiveFormulaCanonicalOnInputEvents separation.state
      (word ++ [selected.bit]) := by
  unfold ActiveFormulaCanonicalOnInputEvents
  rw [rawParser_parse_append_singleton]
  intro later path event cell
  apply activeFormulaCanonicalCheck_of_selected_incremental_refinement
    (firstOutput := separation) (secondOutput := later)
    selected.candidate.inputCell cell squarefree degreeNonzero elimination
      notCompleted
  exact selected.canonical_holds

theorem CompletedSectorActiveControllerCanonicalData.ofSelectedIncremental
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    (selected : IncrementalEventPayload separation)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CompletedSectorActiveControllerCanonicalData separation.state
      (word ++ [selected.bit]) := by
  intro _completed
  exact (activeFormulaCanonicalOnInputEvents_ofSelectedIncrementalData
    numerical word separation selected notCompleted squarefree degreeNonzero
      elimination).controllerCanonical

/-- A complete selected event supplies the same active-only phase-indexed
certificate.  A completed source resets out of the supported phase; every
other source uses its incremental payload. -/
theorem CompletedSectorActiveControllerCanonicalData.ofSelectedPayload
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CompletedSectorActiveControllerCanonicalData separation.state
      (word ++ [selected.bit]) := by
  let state := RawParser.parse word
  by_cases completed : ∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second)
  · intro nextCompleted
    have impossible := rawParser_step_not_completed_of_completed state
      selected.bit completed
    rw [rawParser_parse_append_singleton] at nextCompleted
    exact (impossible nextCompleted).elim
  · exact CompletedSectorActiveControllerCanonicalData.ofSelectedIncremental
      numerical word separation selected.toIncrementalPayload completed
        squarefree degreeNonzero elimination

/-- If a strict all-clear plan enters a completed sector, both target event
families are empty.  Consequently it establishes the active-only controller
certificate without reconstructing historical parser constraints. -/
theorem activeControllerCanonicalOnInputEvents_of_completed_strictPriorPlan
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word) (bit : Bool)
    (strictSigns : ∀ source ∈ inputPlan (RawParser.parse word),
      strictSignCheck source.form numerical.box = true)
    (completed : ∃ kind exponent first second,
      (RawParser.parse (word ++ [bit])).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    ActiveControllerCanonicalOnInputEvents numerical (word ++ [bit]) := by
  have completedStep : ∃ kind exponent first second,
      (RawParser.step (RawParser.parse word) bit).phase =
        .sector kind exponent (.two first second) := by
    simpa only [rawParser_parse_append_singleton] using completed
  have targetDeterminant :
      determinant (RawParser.parse (word ++ [bit])).matrix ≠ 0 := by
    simpa only [determinant, Mat2.det] using
      RawParser.parse_det_ne (word ++ [bit])
  intro separation
  constructor
  · intro candidate member
    have targetMember := candidate.source_mem_inputPlan member
    have targetMemberStep :
        candidate.sourceEvent.partition.entry.source ∈
          inputPlan (RawParser.step (RawParser.parse word) bit) := by
      simpa only [rawParser_parse_append_singleton] using targetMember
    have priorMember := inputPlan_step_subset_of_completed
      (RawParser.parse word) bit completedStep _ targetMemberStep
    let point := localizedCellPoint separation candidate.inputCell squarefree
      separation.state
    have pointInsideLater : separation.state.box.Contains point :=
      (localizedCellPoint_strictContains separation candidate.inputCell
        squarefree degreeNonzero elimination separation.state
          (RatBox.refines_refl separation.state.box)).contains
    have pointInside : numerical.box.Contains point :=
      separation.refines.contains pointInsideLater
    have boundary :
        candidate.sourceEvent.partition.entry.source.form.eval point = 0 := by
      change candidate.sourceEvent.partition.entry.source.form.eval
        (eventSourcePoint candidate.inputCell squarefree
          (localizedClearance separation separation.state)) = 0
      exact candidate.sourceEvent.partition.entry.onBoundary
        (candidate.source_determinant_ne targetDeterminant member)
        (eventSourcePoint_pathDenominator_ne candidate.inputCell squarefree
          (localizedClearance separation separation.state))
    have sameSign := eval_center_mul_pos_of_strictSignCheck
      candidate.sourceEvent.partition.entry.source.form
      (strictSigns _ priorMember) pointInside
    rw [boundary] at sameSign
    norm_num at sameSign
  · intro candidate member
    have targetMember := candidate.source_mem_inputPlan member
    have targetMemberStep :
        candidate.sourceEvent.sourceCell.partition.entry.source ∈
          inputPlan (RawParser.step (RawParser.parse word) bit) := by
      simpa only [rawParser_parse_append_singleton] using targetMember
    have priorMember := inputPlan_step_subset_of_completed
      (RawParser.parse word) bit completedStep _ targetMemberStep
    let point := localizedCellPoint separation candidate.inputCell squarefree
      separation.state
    have pointInsideLater : separation.state.box.Contains point :=
      (localizedCellPoint_strictContains separation candidate.inputCell
        squarefree degreeNonzero elimination separation.state
          (RatBox.refines_refl separation.state.box)).contains
    have pointInside : numerical.box.Contains point :=
      separation.refines.contains pointInsideLater
    have boundary :
        candidate.sourceEvent.sourceCell.partition.entry.source.form.eval
          point = 0 := by
      change
        candidate.sourceEvent.sourceCell.partition.entry.source.form.eval
          (eventSourcePoint candidate.inputCell squarefree
            (localizedClearance separation separation.state)) = 0
      exact candidate.sourceEvent.sourceCell.partition.entry.onBoundary
        (candidate.source_determinant_ne targetDeterminant member)
        (eventSourcePoint_pathDenominator_ne candidate.inputCell squarefree
          (localizedClearance separation separation.state))
    have sameSign := eval_center_mul_pos_of_strictSignCheck
      candidate.sourceEvent.sourceCell.partition.entry.source.form
      (strictSigns _ priorMember) pointInside
    rw [boundary] at sameSign
    norm_num at sameSign

/-- Planned-bit wrapper used by the active metric state. -/
theorem plannedBit_completedSectorActiveControllerCanonicalData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : CCLDirectTrack.State p (RatBox.symmetric R hR)}
    (planned : CCLDirectTrack.PlannedBit current)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CompletedSectorActiveControllerCanonicalData planned.numerical
      (current.word ++ [planned.decision.bit]) := by
  intro completed
  exact activeControllerCanonicalOnInputEvents_of_completed_strictPriorPlan
    planned.numerical current.word planned.decision.bit planned.strictSigns
      completed squarefree degreeNonzero elimination

end CCLActiveCanonicalEvent
end FTA
