import FTA.CCLCoupledController
import FTA.CCLCanonicalEvent
import FTA.CCLPositiveEventConvergence

/-!
# Excluding positive all-neither input events

The finite event classifier can report that neither proposed parser child
owns an isolated positive input event.  At a completed sector, canonical
truth of the current state then forces one child residual to vanish on that
event factor.  Terminal separation and convergence rule out exactly that
divisibility, so the all-neither case is impossible.
-/

namespace FTA
namespace CCLPositiveAllNeither

open CCL
open FTA.AxisSafeCuts
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchEvidence
open FTA.CCLBranchPartition
open FTA.CCLCanonicalEvent
open FTA.CCLFormulaPath
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLGuardCellClearance
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventSemantics
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Provenance-independent core of the completed-sector contradiction.  It
applies equally to a globally isolated input event and to an event recovered
from a terminal guard cell. -/
theorem inputCell_allNeither_excludes_completedSector_current_event
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path separation.state.box}
    (cell : InputEventCell (RawParser.parse current.word) event)
    (checks : cell.ownerChecks = (false, false))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse current.word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    (currentCanonical : currentFormulaCanonicalCheck cell = true) :
    False := by
  let refinedCell := currentFormulaInputCell cell
  have refinedChecks : refinedCell.ownerChecks = (false, false) := by
    rw [← currentFormulaInputCell_ownerChecks_eq cell squarefree
      degreeNonzero elimination]
    exact checks
  have refinedCanonical : formulaEvalWith
      (inputStateFormula (RawParser.parse current.word))
      (inputEventCanonicalValue refinedCell) = true := by
    simpa only [refinedCell, currentFormulaCanonicalCheck] using
      currentCanonical
  rcases inputEvent_residualPolynomial_dvd_of_completedSector
      refinedCell refinedChecks kind exponent first second phase
      refinedCanonical with
    ⟨third, divides⟩
  exact (inputEvent_residual_not_dvd_of_terminalOutput current separation
    refinedCell squarefree degreeNonzero elimination terminalOutput
    next nextRefines kind exponent first second third phase) divides

/-- A completed-sector positive input event cannot be classified as
all-`neither` when its canonical value satisfies the current parser formula.
The conclusion is the local contradiction needed to eliminate this event
from the coupled controller's `noEventOwner` branch. -/
theorem noEventOwner_excludes_completedSector_current_event
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (none : ∀ candidate ∈ separatedInputEventCells p
      (RawParser.parse current.word) separation,
      candidate.inputCell.ownerChecks = (false, false))
    (candidate : SourceInputEventCell p separation.state.box
      (RawParser.parse current.word))
    (member : candidate ∈ separatedInputEventCells p
      (RawParser.parse current.word) separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse current.word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second))
    (currentCanonical :
      currentFormulaCanonicalCheck candidate.inputCell = true) :
    False := by
  exact inputCell_allNeither_excludes_completedSector_current_event current
    separation candidate.inputCell (none candidate member) squarefree
    degreeNonzero elimination terminalOutput next nextRefines kind exponent
    first second phase currentCanonical

/-- Reachable-state form: the explicit canonical-current premise is supplied
by the coupled track's algebraic-event invariant. -/
theorem noEventOwner_excludes_completedSector_event
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (currentValid : CompletedSectorCanonicalOnInputEvents current)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (none : ∀ candidate ∈ separatedInputEventCells p
      (RawParser.parse current.word) separation,
      candidate.inputCell.ownerChecks = (false, false))
    (candidate : SourceInputEventCell p separation.state.box
      (RawParser.parse current.word))
    (member : candidate ∈ separatedInputEventCells p
      (RawParser.parse current.word) separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse current.word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second)) :
    False := by
  apply noEventOwner_excludes_completedSector_current_event current separation
    none candidate member squarefree degreeNonzero elimination terminalOutput
    next nextRefines kind exponent first second phase
  exact (currentValid ⟨kind, exponent, first, second, phase⟩)
    separation candidate.inputCell

/-- Guard-cell specialization: a positive event recovered from terminal guard
provenance is subject to the same completed-sector contradiction as a member
of the global event family. -/
theorem noEventOwner_excludes_completedSector_guard_event
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (currentValid : CompletedSectorCanonicalOnInputEvents current)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
      (RawParser.parse current.word) separation,
      candidate.inputCell.ownerChecks = (false, false))
    (candidate : SourceGuardInputEventCell p separation.state.box
      (RawParser.parse current.word))
    (member : candidate ∈ separatedGuardInputEventCells p
      (RawParser.parse current.word) separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse current.word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second)) :
    False := by
  apply inputCell_allNeither_excludes_completedSector_current_event current
    separation candidate.inputCell (guardNone candidate member) squarefree
    degreeNonzero elimination terminalOutput next nextRefines kind exponent
    first second phase
  exact (currentValid ⟨kind, exponent, first, second, phase⟩)
    separation candidate.inputCell

/-- Source-cell form of the guarded contradiction.  A retained relevant
event contributes a parser-owner cell even when its algebraic parameter is
not rational, so the guarded all-`neither` certificate rules it out at a
completed sector. -/
theorem noEventOwner_excludes_completedSector_guard_cell_relevant
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (currentValid : CompletedSectorCanonicalOnInputEvents current)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical (adjugate (RawParser.parse current.word).matrix))
    (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
      (RawParser.parse current.word) separation,
      candidate.inputCell.ownerChecks = (false, false))
    (sourceCell : SourceEventGuardCell p separation.state.box)
    (sourceMember : sourceCell ∈ separatedEventGuardCells p
      (RawParser.parse current.word) separation)
    (event : RelevantCurveEvent p
      sourceCell.partition.entry.chart.path separation.state.box)
    (eventMember : event ∈
      CCLBranchEvent.EventGuardCell.relevantCurveEvents sourceCell.item.cell)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (terminalOutput : CCLTerminalSeparation.SeparationOutput p
      (RatBox.symmetric R hR) (RawParser.parse current.word) separation.state
      [false, true])
    (next : WindingOneState p (RatBox.symmetric R hR))
    (nextRefines : next.box.Refines terminalOutput.numerical.box)
    (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool)
    (phase : (RawParser.parse current.word).phase =
      .sector kind exponent (.two first second)) :
    False := by
  let sourceEvent : SourceGuardCurveEvent p separation.state.box :=
    ⟨sourceCell, event, eventMember⟩
  have sourceEventMember : sourceEvent ∈ separatedSourceGuardCurveEvents p
      (RawParser.parse current.word) separation := by
    simpa only [separatedSourceGuardCurveEvents, sourceEvent] using
      sourceGuardCurveEvent_mem_of_cell_event sourceCell sourceMember event
        eventMember
  rcases separatedGuardInputEventCells_exists_of_sourceEvent_mem separation
      sourceEvent sourceEventMember with
    ⟨candidate, candidateMember, _sourceEquality⟩
  exact noEventOwner_excludes_completedSector_guard_event current currentValid
    separation guardNone candidate candidateMember squarefree degreeNonzero
      elimination terminalOutput next nextRefines kind exponent first second
        phase

/-- Sample-free core of the complete completed-sector contradiction. -/
theorem inputCell_allNeither_excludes_completedSectorData
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
    (currentCanonical : currentFormulaCanonicalCheck cell = true) :
    False := by
  let refinedCell := currentFormulaInputCell cell
  have refinedChecks : refinedCell.ownerChecks = (false, false) := by
    rw [← currentFormulaInputCell_ownerChecks_eq cell squarefree
      degreeNonzero elimination]
    exact checks
  have refinedCanonical : formulaEvalWith
      (inputStateFormula (RawParser.parse word))
      (inputEventCanonicalValue refinedCell) = true := by
    simpa only [refinedCell, currentFormulaCanonicalCheck] using
      currentCanonical
  rcases inputEvent_residualPolynomial_dvd_of_completedSector
      refinedCell refinedChecks kind exponent first second phase
      refinedCanonical with ⟨third, divides⟩
  exact (inputEvent_residual_not_dvd_of_terminalOutputData numerical word
    separation refinedCell squarefree degreeNonzero elimination terminalOutput
    next nextRefines kind exponent first second third phase) divides

/-- Finite-controller form of the complete guarded contradiction.  As in the
incremental specialization below, only the enumerated guard candidate
recovered from the retained source event needs canonical current support. -/
theorem allNeither_excludes_completedSector_guard_cellControllerData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (currentValid : ControllerCanonicalOnInputEvents numerical word)
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
  apply inputCell_allNeither_excludes_completedSectorData numerical word
    separation candidate.inputCell (guardNone candidate candidateMember)
      squarefree degreeNonzero elimination terminalOutput next nextRefines kind
        exponent first second phase
  exact (currentValid separation).2 candidate candidateMember

/-! ## Sample-free incremental specialization -/

/-- Data-only completed-sector contradiction for the history-free truth
table.  At a completed sector the incremental and complete child formulas
coincide, while the terminal convergence contradiction now uses only the
independently shrinking box center. -/
theorem inputCell_incrementalAllNeither_excludes_completedSectorData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path separation.state.box}
    (cell : InputEventCell (RawParser.parse word) event)
    (checks : inputEventIncrementalChecks cell = (false, false))
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
    (currentCanonical : currentFormulaCanonicalCheck cell = true) :
    False := by
  have completeChecks : cell.ownerChecks = (false, false) := by
    exact InputEventCell.ownerChecks_eq_neither_of_incrementalChecks cell
      checks
  let refinedCell := currentFormulaInputCell cell
  have refinedChecks : refinedCell.ownerChecks = (false, false) := by
    rw [← currentFormulaInputCell_ownerChecks_eq cell squarefree
      degreeNonzero elimination]
    exact completeChecks
  have refinedCanonical : formulaEvalWith
      (inputStateFormula (RawParser.parse word))
      (inputEventCanonicalValue refinedCell) = true := by
    simpa only [refinedCell, currentFormulaCanonicalCheck] using
      currentCanonical
  rcases inputEvent_residualPolynomial_dvd_of_completedSector
      refinedCell refinedChecks kind exponent first second phase
      refinedCanonical with
    ⟨third, divides⟩
  exact (inputEvent_residual_not_dvd_of_terminalOutputData numerical word
    separation refinedCell squarefree degreeNonzero elimination terminalOutput
    next nextRefines kind exponent first second third phase) divides

/-- Guard-event form of the sample-free incremental contradiction. -/
theorem incrementalAllNeither_excludes_completedSector_guard_eventData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (currentValid : FormulaCanonicalOnInputEvents numerical word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
      (RawParser.parse word) separation,
      inputEventIncrementalChecks candidate.inputCell = (false, false))
    (candidate : SourceGuardInputEventCell p separation.state.box
      (RawParser.parse word))
    (member : candidate ∈ separatedGuardInputEventCells p
      (RawParser.parse word) separation)
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
  apply inputCell_incrementalAllNeither_excludes_completedSectorData numerical
    word separation candidate.inputCell (guardNone candidate member)
      squarefree degreeNonzero elimination terminalOutput next nextRefines kind
        exponent first second phase
  exact currentValid separation candidate.inputCell

/-- Source guard-cell form used directly by the sample-free controller. -/
theorem incrementalAllNeither_excludes_completedSector_guard_cellData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (currentValid : FormulaCanonicalOnInputEvents numerical word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
      (RawParser.parse word) separation,
      inputEventIncrementalChecks candidate.inputCell = (false, false))
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
  exact incrementalAllNeither_excludes_completedSector_guard_eventData
    numerical word currentValid separation guardNone candidate candidateMember
      squarefree degreeNonzero elimination terminalOutput next nextRefines kind
        exponent first second phase

/-- Finite-controller specialization of the guarded contradiction.  Only the
canonical truth of the enumerated guard candidate recovered from this source
cell is used; unrelated projective paths are intentionally absent. -/
theorem incrementalAllNeither_excludes_completedSector_guard_cellControllerData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (currentValid : ControllerCanonicalOnInputEvents numerical word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
      (RawParser.parse word) separation,
      inputEventIncrementalChecks candidate.inputCell = (false, false))
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
  apply inputCell_incrementalAllNeither_excludes_completedSectorData numerical
    word separation candidate.inputCell (guardNone candidate candidateMember)
      squarefree degreeNonzero elimination terminalOutput next nextRefines kind
        exponent first second phase
  exact (currentValid separation).2 candidate candidateMember

end CCLPositiveAllNeither
end FTA
