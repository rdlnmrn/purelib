import FTA.CCLPositiveEventConvergence

/-!
# Transporting strict box decisions to algebraic event oracles

A clear-cell branch is decided by interval arithmetic on a rational box,
whereas a later positive event is evaluated by the canonical isolated-event
oracle.  This module proves that a successful all-atoms-strict box check has
the same Boolean value in every such event oracle.  The proof is constructive:
an allegedly zero canonical atom would make rational event approximations
arbitrarily small, contradicting the explicit strict box margin.
-/

namespace FTA
namespace CCLCanonicalEvent

open CCL
open FTA.AxisSafeCuts
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchController
open FTA.CCLBranchPlan
open FTA.CCLCountOneClassification
open FTA.CCLEventExtraction
open FTA.CCLFormulaPath
open FTA.CCLFormulaStability
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLHermitianBox
open FTA.CCLNextBitFormula
open FTA.CCLPathIntersection
open FTA.CCLParserGeometry
open FTA.CCLPositiveEventConvergence
open FTA.CCLPositiveEventLocalization
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventTrack
open FTA.LocalExtraction
open FTA.RationalPolynomialBounds
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Follow the unique count-one descendant of an input event after also
classifying every atom of the current parser predicate.  The ordinary event
classifier intentionally contains only the two proposed children; this
additional finite refinement supplies the historical predicate exactly where
the reachability invariant needs it. -/
def currentFormulaClassification
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :=
  followCountOneConditions cell.branch.factor
    (cell.branch.computeEventSigns cell.parent).refined
    (eventFormulaPolynomials (inputStateFormula state) path)

/-- Repackage the current-formula descendant as an ordinary parser input
cell.  Existing child relations restrict constructively to the selected
divisor, so its owner table remains available without rerunning that part of
the classifier. -/
def currentFormulaInputCell
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : InputEventCell state event :=
  let classification := currentFormulaClassification cell
  { branch :=
      { factor := classification.branch.factor
        relations := cell.branch.relations.ofDvd
          classification.branch.factor.input classification.divides }
    divides := classification.divides.trans cell.divides
    parent := (classification.branch.computeEventSigns
      classification.parent).refined
    refines := FTA.SturmTransducer.RationalInterval.refines_trans
      classification.signRefines cell.signRefines }

/-- Continue the historical-form descendant through the child conditions of
an arbitrary comparison parser state.  This is the finite bridge used when a
later event must be compared with the owner cell that selected the preceding
bit. -/
def currentFormulaConditionClassification
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (conditionState : RawParser.State) :=
  let currentClassification := currentFormulaClassification cell
  let currentSigns := currentClassification.branch.computeEventSigns
    currentClassification.parent
  followCountOneConditions currentClassification.branch.factor
    currentSigns.refined (inputEventPolynomials conditionState path)

/-- Repackage that common descendant as an input event cell indexed by the
comparison state's child-condition list. -/
def currentFormulaReclassifiedInputCell
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (conditionState : RawParser.State) :
    InputEventCell conditionState event :=
  let currentClassification := currentFormulaClassification cell
  let conditionClassification :=
    currentFormulaConditionClassification cell conditionState
  { branch := conditionClassification.branch
    divides := conditionClassification.divides.trans
      (currentClassification.divides.trans cell.divides)
    parent := conditionClassification.parent
    refines :=
      FTA.SturmTransducer.RationalInterval.refines_trans
        conditionClassification.refines
        (FTA.SturmTransducer.RationalInterval.refines_trans
          currentClassification.signRefines cell.signRefines) }

/-- Canonical truth value of the current parser predicate after the explicit
historical-form classification above. -/
def currentFormulaCanonicalCheck
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : Bool :=
  formulaEvalWith (inputStateFormula state)
    (inputEventCanonicalValue (currentFormulaInputCell cell))

/-- Evaluating the current predicate through the projected child cell agrees
with evaluating it through its own direct classification.  The projected
cell performs a further child-sign refinement inside the historical common
sign interval, so every atom keeps the same exact `SignTest` outcome. -/
theorem currentFormulaCanonicalCheck_eq_eventFormulaCheck
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    currentFormulaCanonicalCheck cell =
      eventFormulaCheck (currentFormulaClassification cell).branch
        (currentFormulaClassification cell).parent := by
  rw [eventFormulaCheck_eq_canonicalEval]
  apply formulaEvalWith_eq_of_atomTests
  intro atom member
  let classification := currentFormulaClassification cell
  let formulaSigns := classification.branch.computeEventSigns
    classification.parent
  let refinedCell := currentFormulaInputCell cell
  let refinedSigns := refinedCell.branch.computeEventSigns refinedCell.parent
  have polynomialMember : clearedForm atom.form path ∈
      eventFormulaPolynomials (inputStateFormula state) path :=
    List.mem_map.mpr ⟨atom, member, rfl⟩
  have lower : formulaSigns.refined.interval.lower ≤
      refinedSigns.refined.interval.lower := by
    simpa only [formulaSigns, refinedSigns, refinedCell,
      currentFormulaInputCell, classification] using refinedSigns.refines.1
  have upper : refinedSigns.refined.interval.lower ≤
      formulaSigns.refined.interval.upper := by
    have bound := refinedSigns.refined.proper.le.trans refinedSigns.refines.2
    simpa only [formulaSigns, refinedSigns, refinedCell,
      currentFormulaInputCell, classification] using bound
  have agreement :=
    ConditionRelations.canonicalEventValue_holds_iff_between
      classification.branch.relations classification.parent formulaSigns
      polynomialMember atom.sign lower upper
  simpa only [currentFormulaCanonicalCheck, inputEventCanonicalValue,
    refinedCell, refinedSigns, formulaSigns, classification,
    currentFormulaInputCell] using agreement.symm

/-- The current-formula oracle agrees with the same descendant repackaged
under any comparison parser state's child conditions.  Extra gcd splits can
only restrict the already classified equality/coprime relations, while their
sample remains inside the original common sign interval. -/
theorem currentFormulaCanonicalCheck_eq_reclassifiedInputCell
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) (conditionState : RawParser.State) :
    currentFormulaCanonicalCheck cell =
      formulaEvalWith (inputStateFormula state)
        (inputEventCanonicalValue
          (currentFormulaReclassifiedInputCell cell conditionState)) := by
  rw [currentFormulaCanonicalCheck_eq_eventFormulaCheck,
    eventFormulaCheck_eq_canonicalEval]
  apply formulaEvalWith_eq_of_atomTests
  intro atom member
  let currentClassification := currentFormulaClassification cell
  let currentSigns := currentClassification.branch.computeEventSigns
    currentClassification.parent
  let conditionClassification :=
    currentFormulaConditionClassification cell conditionState
  let conditionSigns := conditionClassification.branch.computeEventSigns
    conditionClassification.parent
  have polynomialMember : clearedForm atom.form path ∈
      eventFormulaPolynomials (inputStateFormula state) path :=
    List.mem_map.mpr ⟨atom, member, rfl⟩
  have lower : currentSigns.refined.interval.lower ≤
      conditionSigns.refined.interval.lower :=
    conditionClassification.refines.1.trans conditionSigns.refines.1
  have upper : conditionSigns.refined.interval.lower ≤
      currentSigns.refined.interval.upper :=
    (conditionSigns.refined.proper.le.trans
      conditionSigns.refines.2).trans conditionClassification.refines.2
  have agreement :=
    ConditionRelations.canonicalEventValue_holds_iff_ofDvd_between
      currentClassification.branch.relations currentClassification.parent
      currentSigns conditionClassification.branch.factor.input
      conditionClassification.divides polynomialMember atom.sign lower upper
  simpa only [inputEventCanonicalValue,
    currentFormulaReclassifiedInputCell, currentFormulaConditionClassification,
    conditionClassification, conditionSigns, currentClassification,
    currentSigns] using agreement

/-- Algebraic-event validity depends only on a winding-one numerical state
and its raw parser word, not on the coupled state's sampling witnesses or on
which of the two finite source-provenance families exposed the event. -/
def FormulaCanonicalOnInputEvents
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) (word : Prefix.Word) : Prop :=
  ∀ (separation : CCLDenominator.SeparationOutput p ambient
      numerical (adjugate (RawParser.parse word).matrix))
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path separation.state.box}
    (cell : InputEventCell (RawParser.parse word) event),
    currentFormulaCanonicalCheck cell = true

/-- Exact finite canonical support consumed by the executable controller: the
current parser predicate is true at every candidate in its two enumerated
global and terminal-guard event families.  This deliberately avoids asking
for unrelated projective paths that the controller never inspects. -/
def ControllerCanonicalOnInputEvents
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) (word : Prefix.Word) : Prop :=
  ∀ (separation : CCLDenominator.SeparationOutput p ambient numerical
      (adjugate (RawParser.parse word).matrix)),
    (∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse word) separation,
      currentFormulaCanonicalCheck candidate.inputCell = true) ∧
    (∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse word) separation,
      currentFormulaCanonicalCheck candidate.inputCell = true)

/-- The earlier provenance-independent invariant is a conservative
strengthening of the finite controller invariant. -/
theorem FormulaCanonicalOnInputEvents.controllerCanonical
    {p : GaussianPolynomial} {ambient : RatBox}
    {numerical : WindingOneState p ambient} {word : Prefix.Word}
    (valid : FormulaCanonicalOnInputEvents numerical word) :
    ControllerCanonicalOnInputEvents numerical word := by
  intro separation
  constructor
  · intro candidate _member
    exact valid separation candidate.inputCell
  · intro candidate _member
    exact valid separation candidate.inputCell

/-- The finite controller invariant is likewise monotone under fixed-word
numerical refinement. -/
theorem ControllerCanonicalOnInputEvents.refine
    {p : GaussianPolynomial} {ambient : RatBox}
    {outer inner : WindingOneState p ambient} {word : Prefix.Word}
    (valid : ControllerCanonicalOnInputEvents outer word)
    (refines : inner.box.Refines outer.box) :
    ControllerCanonicalOnInputEvents inner word := by
  intro separation
  exact valid (separation.rebase refines)

/-- Canonical event reachability is monotone under numerical box refinement
when the raw word is unchanged.  This is the sample-free rebase operation
used by the direct x--y controller. -/
theorem FormulaCanonicalOnInputEvents.refine
    {p : GaussianPolynomial} {ambient : RatBox}
    {outer inner : WindingOneState p ambient} {word : Prefix.Word}
    (valid : FormulaCanonicalOnInputEvents outer word)
    (refines : inner.box.Refines outer.box) :
    FormulaCanonicalOnInputEvents inner word := by
  intro separation path event cell
  let rebased := separation.rebase refines
  exact valid rebased cell

/-- Reachability property needed by the positive-event branch: every positive
root event below the coupled state's numerical box sees the current parser
predicate as canonically true, independently of source provenance. -/
def CurrentFormulaCanonicalOnInputEvents
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient) : Prop :=
  FormulaCanonicalOnInputEvents current.numerical current.word

/-- Data-only phase-indexed algebraic support.  This form applies to direct,
persistent, checkpoint, and metric states without manufacturing a legacy
coupled-state sample. -/
def CompletedSectorCanonicalData
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) (word : Prefix.Word) : Prop :=
  (∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second)) →
    FormulaCanonicalOnInputEvents numerical word

/-- Phase-indexed form of the exact finite support actually consumed by the
controller. -/
def CompletedSectorControllerCanonicalData
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) (word : Prefix.Word) : Prop :=
  (∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second)) →
    ControllerCanonicalOnInputEvents numerical word

theorem CompletedSectorCanonicalData.controllerCanonical
    {p : GaussianPolynomial} {ambient : RatBox}
    {numerical : WindingOneState p ambient} {word : Prefix.Word}
    (valid : CompletedSectorCanonicalData numerical word) :
    CompletedSectorControllerCanonicalData numerical word := by
  intro completed
  exact (valid completed).controllerCanonical

/-- Reachability needs the current-formula event invariant only while the
parser is waiting for the third sector bit.  Reading that bit resets the
phase to `loopUnary 0`; ordinary intervening transitions re-establish the
full invariant before another completed sector can be reached. -/
def CompletedSectorCanonicalOnInputEvents
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLCoupledTrack.State p ambient) : Prop :=
  CompletedSectorCanonicalData current.numerical current.word

/-- The empty parser predicate is canonically true at every event. -/
theorem currentFormulaCanonicalOnInputEvents_ofWindingOne
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) :
    CurrentFormulaCanonicalOnInputEvents
      (CCLCoupledTrack.State.ofWindingOne numerical) := by
  intro separation path event cell
  simp [CCLCoupledTrack.State.ofWindingOne, inputStateFormula,
    RawParser.parse, RawParser.initialState, RawParser.identityMatrix, adjugate,
    stateFormula, activeFormula, FTA.CCLFormulaPullback.Formula.pullback,
    Formula.all, formulaEvalWith, currentFormulaCanonicalCheck]

theorem completedSectorCanonicalOnInputEvents_ofWindingOne
    {p : GaussianPolynomial} {ambient : RatBox}
    (initial : WindingOneState p ambient) :
    CompletedSectorCanonicalOnInputEvents
      (CCLCoupledTrack.State.ofWindingOne initial) := by
  intro completed
  simp [CCLCoupledTrack.State.ofWindingOne, RawParser.parse,
    RawParser.initialState] at completed

/-- Accuracy refinement changes neither the parser word nor its algebraic
event predicate, so the canonical-event invariant simply rebases a later
denominator certificate to the previous numerical state. -/
theorem CurrentFormulaCanonicalOnInputEvents.refineWithTrack
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (current : CCLCoupledTrack.State p ambient)
    (valid : CurrentFormulaCanonicalOnInputEvents current)
    (epsilon : ℚ) (positive : 0 < epsilon) :
    CurrentFormulaCanonicalOnInputEvents
      (current.refineWithTrack track epsilon positive) := by
  intro separation path event cell
  simp only [CCLCoupledTrack.State.refineWithTrack] at separation path event cell
  change currentFormulaCanonicalCheck cell = true
  let rebased := separation.rebase
    (track.nested current.numerical epsilon positive)
  exact valid rebased cell

theorem CompletedSectorCanonicalOnInputEvents.refineWithTrack
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (current : CCLCoupledTrack.State p ambient)
    (valid : CompletedSectorCanonicalOnInputEvents current)
    (epsilon : ℚ) (positive : 0 < epsilon) :
    CompletedSectorCanonicalOnInputEvents
      (current.refineWithTrack track epsilon positive) := by
  intro completed
  apply CurrentFormulaCanonicalOnInputEvents.refineWithTrack track current
    (valid (by
      simpa only [CCLCoupledTrack.State.refineWithTrack] using completed))

/-- Before the third sector bit updates the decoder matrix, the proposed
input-coordinate child formula is literally the next parser state's current
formula. -/
theorem inputStateFormula_step_eq_inputAdvanceFormula_of_not_completed
    (state : RawParser.State) (bit : Bool)
    (notCompleted : ¬∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second)) :
    inputStateFormula (RawParser.step state bit) =
      inputAdvanceFormula state bit := by
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

theorem rawParser_step_matrix_eq_of_not_completed
    (state : RawParser.State) (bit : Bool)
    (notCompleted : ¬∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second)) :
    (RawParser.step state bit).matrix = state.matrix := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial => cases bit <;> rfl
  | highUnary count => cases bit <;> rfl
  | lowUnary count => cases bit <;> rfl
  | loopUnary count => cases bit <;> rfl
  | sector kind exponent bits =>
      cases bits with
      | zero => rfl
      | one first => rfl
      | two first second =>
          exact (notCompleted ⟨kind, exponent, first, second, rfl⟩).elim

/-- Reading the third bit of a completed sector always leaves the only phase
where the canonical-current invariant is required. -/
theorem rawParser_step_not_completed_of_completed
    (state : RawParser.State) (bit : Bool)
    (completed : ∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second)) :
    ¬∃ kind exponent first second,
      (RawParser.step state bit).phase =
        .sector kind exponent (.two first second) := by
  rcases completed with ⟨kind, exponent, first, second, phase⟩
  rw [RawParserSemantics.step_eq_completeSector state kind exponent first
    second bit phase]
  simp [RawParser.completeSector]

theorem rawParser_parse_append_singleton
    (word : Prefix.Word) (bit : Bool) :
    RawParser.parse (word ++ [bit]) = RawParser.step (RawParser.parse word) bit := by
  simp [RawParser.parse, List.foldl_append]

/-- If an all-clear strict plan enters the phase waiting for a sector's third
bit, its one-step lookahead wall makes both finite target event families
empty.  A hypothetical target candidate supplies a rational point exactly on
its planned source boundary and inside the later box, contradicting the
retained interval-strict sign of that source. -/
theorem controllerCanonicalOnInputEvents_of_completed_strictPriorPlan
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
    ControllerCanonicalOnInputEvents numerical (word ++ [bit]) := by
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

/-- Every atom of either complete child formula is one of the conditions
classified by an input event cell. -/
theorem clearedForm_mem_inputEventPolynomials_of_advance_atom
    (state : RawParser.State) (path : ProjectivePath.Path) (bit : Bool)
    (atom : Atom)
    (member : atom ∈ formulaAtoms (inputAdvanceFormula state bit)) :
    clearedForm atom.form path ∈ inputEventPolynomials state path := by
  cases bit with
  | false =>
      simp only [inputEventPolynomials, eventFormulaPolynomials, formulaAtoms,
        List.map_append, List.mem_append, List.mem_map]
      exact Or.inl ⟨atom, member, rfl⟩
  | true =>
      simp only [inputEventPolynomials, eventFormulaPolynomials, formulaAtoms,
        List.map_append, List.mem_append, List.mem_map]
      exact Or.inr ⟨atom, member, rfl⟩

/-- Every comparison form read by the current local discriminator is present
among the two complete child condition lists classified by an input event
cell.  Deliberate next-grid lookahead walls are not current decision forms. -/
theorem clearedForm_mem_inputEventPolynomials_of_inputDecisionForm
    (state : RawParser.State) (path : ProjectivePath.Path)
    (form : HermitianForm) (member : form ∈ inputDecisionForms state) :
    clearedForm form path ∈ inputEventPolynomials state path := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simp [inputDecisionForms, localDecisionForms] at member
      subst form
      simp [inputEventPolynomials,
        eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
        stateFormula, activeFormula, Formula.pullback, formulaAtoms,
        RawParser.step]
  | highUnary count =>
      simp [inputDecisionForms, localDecisionForms] at member
      subst form
      simp [inputEventPolynomials,
        eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
        stateFormula, activeFormula, Formula.pullback, formulaAtoms,
        RawParser.step]
  | lowUnary count =>
      cases count with
      | zero =>
          simp [inputDecisionForms, localDecisionForms] at member
          subst form
          simp [inputEventPolynomials,
            eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
            stateFormula, activeFormula, Formula.pullback, formulaAtoms,
            RawParser.step]
      | succ count =>
          simp [inputDecisionForms, localDecisionForms] at member
          subst form
          simp [inputEventPolynomials,
            eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
            stateFormula, activeFormula, Formula.pullback, formulaAtoms,
            RawParser.step]
  | loopUnary count =>
      simp [inputDecisionForms, localDecisionForms] at member
      subst form
      simp [inputEventPolynomials,
        eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
        stateFormula, activeFormula, Formula.pullback, formulaAtoms,
        RawParser.step]
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp [inputDecisionForms, localDecisionForms] at member
          rcases member with rfl | rfl | rfl <;>
            simp [inputEventPolynomials,
              eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
              stateFormula, activeFormula, sectorBitsFormula,
              Formula.pullback, formulaAtoms, RawParser.step]
      | one first =>
          cases first <;>
            simp [inputDecisionForms, localDecisionForms] at member <;>
            subst form <;>
            simp [inputEventPolynomials,
              eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
              stateFormula, activeFormula, sectorBitsFormula,
              Formula.pullback, formulaAtoms, RawParser.step]
      | two first second =>
          cases first <;> cases second <;>
            simp [inputDecisionForms, localDecisionForms] at member <;>
            subst form <;>
            simp [inputEventPolynomials,
              eventFormulaPolynomials, inputAdvanceFormula, advanceFormula,
              sectorFormula, Formula.pullback, formulaAtoms,
              RawParser.sectorOfBits]

/-- Membership in a formula's atom list exposes the corresponding successful
strict sign check from a recursive whole-box check. -/
theorem strictSignCheck_of_mem_formulaAtoms
    (formula : Formula) (box : RatBox)
    (check : CCLHermitianBox.Formula.strictOnBox formula box = true)
    {atom : Atom}
    (member : atom ∈ formulaAtoms formula) :
    strictSignCheck atom.form box = true := by
  induction formula with
  | truth => simp [formulaAtoms] at member
  | falsity => simp [formulaAtoms] at member
  | atom current =>
      simp only [formulaAtoms, List.mem_singleton] at member
      subst atom
      exact check
  | and left right leftIH rightIH =>
      simp only [CCLHermitianBox.Formula.strictOnBox,
        Bool.and_eq_true] at check
      simp only [formulaAtoms, List.mem_append] at member
      rcases member with leftMember | rightMember
      · exact leftIH check.1 leftMember
      · exact rightIH check.2 rightMember
  | or left right leftIH rightIH =>
      simp only [CCLHermitianBox.Formula.strictOnBox,
        Bool.and_eq_true] at check
      simp only [formulaAtoms, List.mem_append] at member
      rcases member with leftMember | rightMember
      · exact leftIH check.1 leftMember
      · exact rightIH check.2 rightMember

/-- A positive upper bound for the projective denominator norm throughout an
arbitrary input event cell's common sign interval. -/
def inputEventDenominatorUpper
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : ℚ :=
  let interval := (cell.branch.computeEventSigns cell.parent).refined.interval
  max 1 (denseEvalAbsBound (denominatorNorm path)
    (intervalMagnitude interval.lower interval.upper))

theorem inputEventDenominatorUpper_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    0 < inputEventDenominatorUpper cell := by
  unfold inputEventDenominatorUpper
  exact zero_lt_one.trans_le (le_max_left _ _)

theorem inputEventDenominator_le
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) {t : ℚ}
    (lower : (cell.branch.computeEventSigns
      cell.parent).refined.interval.lower ≤ t)
    (upper : t ≤ (cell.branch.computeEventSigns
      cell.parent).refined.interval.upper) :
    |(denominatorNorm path).eval t| ≤ inputEventDenominatorUpper cell := by
  let interval := (cell.branch.computeEventSigns cell.parent).refined.interval
  have parameterBound : |t| ≤
      intervalMagnitude interval.lower interval.upper :=
    abs_le_intervalMagnitude lower upper
  have evaluationBound := abs_dense_eval_le_denseEvalAbsBound
    (denominatorNorm path)
    (intervalMagnitude_pos interval.lower interval.upper).le parameterBound
  exact evaluationBound.trans (le_max_right _ _)

/-- Common strict polynomial margin converted to a genuine affine-form
margin for an arbitrary positive input event. -/
def inputEventStrictFormMargin
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) : ℚ :=
  ConditionRelations.strictMargin cell.branch.relations cell.parent
      (cell.branch.computeEventSigns cell.parent) /
    inputEventDenominatorUpper cell

theorem inputEventStrictFormMargin_pos
    {p : GaussianPolynomial} {path : ProjectivePath.Path} {box : RatBox}
    {state : RawParser.State} {event : RelevantCurveEvent p path box}
    (cell : InputEventCell state event) :
    0 < inputEventStrictFormMargin cell := by
  apply div_pos
  · exact ConditionRelations.strictMargin_pos cell.branch.relations cell.parent
      (cell.branch.computeEventSigns cell.parent)
  · exact inputEventDenominatorUpper_pos cell

/-- Every canonically nonzero classified form stays above the common affine
margin at every shrinking rational event point. -/
theorem inputEventStrictFormMargin_le_shrinkingPoint
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    {denominatorState cellState : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate denominatorState.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    (cell : InputEventCell cellState event)
    (squarefree : GaussianSquarefreeCertificate p)
    (radius : ℚ) (radiusPositive : 0 < radius) (form : HermitianForm)
    (member : clearedForm form path ∈ inputEventPolynomials cellState path)
    (canonicalNonzero : inputEventCanonicalValue cell form ≠ 0) :
    inputEventStrictFormMargin cell ≤
      |form.eval (shrinkingInputEventPoint cell squarefree radius
        radiusPositive)| := by
  let clearance := shrinkingEventClearance output radius radiusPositive
  let epsilon := eventSourceApproximationWidth cell squarefree clearance
  let epsilonPositive : 0 < epsilon :=
    eventSourceApproximationWidth_pos cell squarefree clearance
  let approximation := cell.clearedApproximation epsilon epsilonPositive
  let signs := cell.branch.computeEventSigns cell.parent
  let t := approximation.refined.interval.lower
  have lower : signs.refined.interval.lower ≤ t := approximation.refines.1
  have upper : t ≤ signs.refined.interval.upper :=
    approximation.refined.proper.le.trans approximation.refines.2
  have clearedLower := ConditionRelations.strictMargin_le_abs_eval
    cell.branch.relations cell.parent signs member (by
      simpa only [inputEventCanonicalValue] using canonicalNonzero) lower upper
  have denominatorLe := inputEventDenominator_le cell lower upper
  have denominatorNonzero :
      path.denominator.eval (PathPolynomial.ofRat t) ≠ 0 := by
    apply cell.path_denominator_ne_on_cell
    · exact approximation.refines.1
    · exact approximation.refined.proper.le.trans approximation.refines.2
  have clearedIdentity : |(clearedForm form path).eval t| =
      |(denominatorNorm path).eval t| *
        |form.eval (shrinkingInputEventPoint cell squarefree radius
          radiusPositive)| := by
    rw [eval_clearedForm form path t denominatorNonzero, abs_mul]
    rfl
  unfold inputEventStrictFormMargin
  apply (div_le_iff₀ (inputEventDenominatorUpper_pos cell)).2
  calc
    ConditionRelations.strictMargin cell.branch.relations cell.parent signs ≤
        |(clearedForm form path).eval t| := clearedLower
    _ = |(denominatorNorm path).eval t| *
        |form.eval (shrinkingInputEventPoint cell squarefree radius
          radiusPositive)| := clearedIdentity
    _ ≤ inputEventDenominatorUpper cell *
        |form.eval (shrinkingInputEventPoint cell squarefree radius
          radiusPositive)| :=
      mul_le_mul_of_nonneg_right denominatorLe (abs_nonneg _)
    _ = |form.eval (shrinkingInputEventPoint cell squarefree radius
          radiusPositive)| * inputEventDenominatorUpper cell := by ring

/-- Canonically nonzero values of the same classified Hermitian form have
the same strict sign at two positive events carried by nested boxes of the
same winding-one track.  The second event is proved nonzero internally. -/
theorem inputEventCanonicalValues_mul_pos_of_refinement
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
    (form : HermitianForm)
    (firstMember : clearedForm form firstPath ∈
      inputEventPolynomials firstCellState firstPath)
    (secondMember : clearedForm form secondPath ∈
      inputEventPolynomials secondCellState secondPath)
    (firstNonzero : inputEventCanonicalValue firstCell form ≠ 0) :
    0 < inputEventCanonicalValue firstCell form *
      inputEventCanonicalValue secondCell form := by
  let margin := inputEventStrictFormMargin firstCell
  have marginPositive : 0 < margin := inputEventStrictFormMargin_pos firstCell
  let secondCoefficient := inputEventFormCoefficient secondCell form
  have secondCoefficientNonnegative : 0 ≤ secondCoefficient :=
    inputEventFormCoefficient_nonneg secondCell form
  let variation := variationMajorant form firstOutput.state.box
  have variationPositive : 0 < variation :=
    variationMajorant_pos form firstOutput.state.box
  let denominator := 2 * (1 + secondCoefficient + 16 * variation)
  have denominatorPositive : 0 < denominator := by positivity
  let radius := margin / denominator
  have radiusPositive : 0 < radius :=
    div_pos marginPositive denominatorPositive
  let firstPoint := shrinkingInputEventPoint firstCell squarefree radius
    radiusPositive
  let secondPoint := shrinkingInputEventPoint secondCell squarefree radius
    radiusPositive
  have firstInside : firstOutput.state.box.Contains firstPoint := by
    have strict := eventWindingOneState_strictInterior
      firstOutput.state.refinesAmbient firstCell squarefree
      (shrinkingEventClearance firstOutput radius radiusPositive) elimination
    exact strict.refines.contains
      (shrinkingInputEventState_contains_point firstCell squarefree elimination
        radius radiusPositive)
  have secondInside : firstOutput.state.box.Contains secondPoint := by
    have strict := eventWindingOneState_strictInterior
      secondOutput.state.refinesAmbient secondCell squarefree
      (shrinkingEventClearance secondOutput radius radiusPositive) elimination
    apply secondOutput.refines.contains
    exact strict.refines.contains
      (shrinkingInputEventState_contains_point secondCell squarefree elimination
        radius radiusPositive)
  have pointDistance : |firstPoint.re - secondPoint.re| +
      |firstPoint.im - secondPoint.im| ≤ 16 * radius := by
    simpa only [firstPoint, secondPoint] using
      shrinkingInputEventPoints_distance_of_refinement firstCell secondCell
        squarefree degreeNonzero elimination radius radiusPositive
  have evaluationDistance :
      |form.eval firstPoint - form.eval secondPoint| ≤
        16 * variation * radius := by
    have bound := abs_eval_sub_eval_le form firstInside secondInside
    apply bound.trans
    exact (mul_le_mul_of_nonneg_left pointDistance variationPositive.le).trans_eq
      (by ring)
  have firstMargin : margin ≤ |form.eval firstPoint| := by
    simpa only [margin, firstPoint] using
      inputEventStrictFormMargin_le_shrinkingPoint firstCell squarefree radius
        radiusPositive form firstMember firstNonzero
  have scaledRadius : denominator * radius = margin := by
    dsimp only [radius]
    exact mul_div_cancel₀ margin denominatorPositive.ne'
  have distanceStrict : 16 * variation * radius < margin := by
    nlinarith
  have secondNonzero : inputEventCanonicalValue secondCell form ≠ 0 := by
    intro secondZero
    have secondDivides : secondCell.branch.factor.polynomial.toPolynomial ∣
        (clearedForm form secondPath).toPolynomial :=
      ConditionRelations.dvd_of_canonicalEventValue_eq_zero
        secondCell.branch.relations secondCell.parent
        (secondCell.branch.computeEventSigns secondCell.parent) secondMember (by
          simpa only [inputEventCanonicalValue] using secondZero)
    have secondSmall := shrinkingInputEventForm_le_of_dvd secondCell squarefree
      radius radiusPositive form secondDivides
    have triangle : |form.eval firstPoint| ≤
        |form.eval firstPoint - form.eval secondPoint| +
          |form.eval secondPoint| := by
      have sum := abs_add_le
        (form.eval firstPoint - form.eval secondPoint)
        (form.eval secondPoint)
      simpa only [sub_add_cancel] using sum
    have strictSum : 16 * variation * radius +
        secondCoefficient * radius < margin := by
      nlinarith
    exact (firstMargin.trans_lt (triangle.trans_lt
      ((add_le_add evaluationDistance secondSmall).trans_lt strictSum))).false
  have firstCanonicalPoint :
      0 < inputEventCanonicalValue firstCell form * form.eval firstPoint := by
    simpa only [firstPoint] using
      inputEventCanonicalValue_mul_shrinkingPoint_pos firstCell squarefree
        radius radiusPositive form firstMember firstNonzero
  have secondCanonicalPoint :
      0 < inputEventCanonicalValue secondCell form * form.eval secondPoint := by
    simpa only [secondPoint] using
      inputEventCanonicalValue_mul_shrinkingPoint_pos secondCell squarefree
        radius radiusPositive form secondMember secondNonzero
  have pointsSameSign : 0 < form.eval firstPoint * form.eval secondPoint := by
    apply mul_pos_of_abs_sub_lt_abs_left
    exact evaluationDistance.trans_lt (distanceStrict.trans_le firstMargin)
  apply FTA.CCLPositiveEventGrid.mul_pos_trans firstCanonicalPoint
  apply FTA.CCLPositiveEventGrid.mul_pos_trans pointsSameSign
  simpa only [_root_.mul_comm] using secondCanonicalPoint

/-- A canonical equality at one positive event remains an equality at every
later positive event on the same winding-one track. -/
theorem inputEventCanonicalValue_eq_zero_of_refinement
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
    (form : HermitianForm)
    (firstMember : clearedForm form firstPath ∈
      inputEventPolynomials firstCellState firstPath)
    (secondMember : clearedForm form secondPath ∈
      inputEventPolynomials secondCellState secondPath)
    (firstZero : inputEventCanonicalValue firstCell form = 0) :
    inputEventCanonicalValue secondCell form = 0 := by
  by_contra secondNonzero
  let margin := inputEventStrictFormMargin secondCell
  have marginPositive : 0 < margin := inputEventStrictFormMargin_pos secondCell
  let firstCoefficient := inputEventFormCoefficient firstCell form
  have firstCoefficientNonnegative : 0 ≤ firstCoefficient :=
    inputEventFormCoefficient_nonneg firstCell form
  let variation := variationMajorant form firstOutput.state.box
  have variationPositive : 0 < variation :=
    variationMajorant_pos form firstOutput.state.box
  let denominator := 2 * (1 + firstCoefficient + 16 * variation)
  have denominatorPositive : 0 < denominator := by positivity
  let radius := margin / denominator
  have radiusPositive : 0 < radius :=
    div_pos marginPositive denominatorPositive
  let firstPoint := shrinkingInputEventPoint firstCell squarefree radius
    radiusPositive
  let secondPoint := shrinkingInputEventPoint secondCell squarefree radius
    radiusPositive
  have firstInside : firstOutput.state.box.Contains firstPoint := by
    have strict := eventWindingOneState_strictInterior
      firstOutput.state.refinesAmbient firstCell squarefree
      (shrinkingEventClearance firstOutput radius radiusPositive) elimination
    exact strict.refines.contains
      (shrinkingInputEventState_contains_point firstCell squarefree elimination
        radius radiusPositive)
  have secondInside : firstOutput.state.box.Contains secondPoint := by
    have strict := eventWindingOneState_strictInterior
      secondOutput.state.refinesAmbient secondCell squarefree
      (shrinkingEventClearance secondOutput radius radiusPositive) elimination
    apply secondOutput.refines.contains
    exact strict.refines.contains
      (shrinkingInputEventState_contains_point secondCell squarefree elimination
        radius radiusPositive)
  have pointDistance : |firstPoint.re - secondPoint.re| +
      |firstPoint.im - secondPoint.im| ≤ 16 * radius := by
    simpa only [firstPoint, secondPoint] using
      shrinkingInputEventPoints_distance_of_refinement firstCell secondCell
        squarefree degreeNonzero elimination radius radiusPositive
  have evaluationDistance :
      |form.eval firstPoint - form.eval secondPoint| ≤
        16 * variation * radius := by
    have bound := abs_eval_sub_eval_le form firstInside secondInside
    apply bound.trans
    exact (mul_le_mul_of_nonneg_left pointDistance variationPositive.le).trans_eq
      (by ring)
  have firstDivides : firstCell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form firstPath).toPolynomial :=
    ConditionRelations.dvd_of_canonicalEventValue_eq_zero
      firstCell.branch.relations firstCell.parent
      (firstCell.branch.computeEventSigns firstCell.parent) firstMember (by
        simpa only [inputEventCanonicalValue] using firstZero)
  have firstSmall := shrinkingInputEventForm_le_of_dvd firstCell squarefree
    radius radiusPositive form firstDivides
  have secondMargin : margin ≤ |form.eval secondPoint| := by
    simpa only [margin, secondPoint] using
      inputEventStrictFormMargin_le_shrinkingPoint secondCell squarefree radius
        radiusPositive form secondMember secondNonzero
  have triangle : |form.eval secondPoint| ≤
      |form.eval firstPoint - form.eval secondPoint| + |form.eval firstPoint| := by
    have sum := abs_add_le
      (form.eval secondPoint - form.eval firstPoint) (form.eval firstPoint)
    rw [abs_sub_comm]
    simpa only [sub_add_cancel] using sum
  have scaledRadius : denominator * radius = margin := by
    dsimp only [radius]
    exact mul_div_cancel₀ margin denominatorPositive.ne'
  have strictSum : 16 * variation * radius +
      firstCoefficient * radius < margin := by
    nlinarith
  exact (secondMargin.trans_lt (triangle.trans_lt
    ((add_le_add evaluationDistance firstSmall).trans_lt strictSum))).false

/-- Consequently every sign test on a form classified at both events has the
same Boolean outcome in their canonical oracles. -/
theorem inputEventCanonicalValue_test_iff_of_refinement
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
    (form : HermitianForm)
    (firstMember : clearedForm form firstPath ∈
      inputEventPolynomials firstCellState firstPath)
    (secondMember : clearedForm form secondPath ∈
      inputEventPolynomials secondCellState secondPath)
    (test : SignTest) :
    test.Holds (inputEventCanonicalValue firstCell form) ↔
      test.Holds (inputEventCanonicalValue secondCell form) := by
  by_cases firstZero : inputEventCanonicalValue firstCell form = 0
  · have secondZero := inputEventCanonicalValue_eq_zero_of_refinement
      firstCell secondCell squarefree degreeNonzero elimination form
      firstMember secondMember firstZero
    rw [firstZero, secondZero]
  · exact SignTest.holds_iff_of_mul_pos test
      (inputEventCanonicalValues_mul_pos_of_refinement firstCell secondCell
        squarefree degreeNonzero elimination form firstMember secondMember
        firstZero)

/-- Every formula whose atoms were classified at both positive events has
the same Boolean value in their canonical oracles. -/
theorem formulaEvalWith_inputEvents_eq_of_refinement
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
    (formula : Formula)
    (firstMembers : ∀ atom ∈ formulaAtoms formula,
      clearedForm atom.form firstPath ∈
        inputEventPolynomials firstCellState firstPath)
    (secondMembers : ∀ atom ∈ formulaAtoms formula,
      clearedForm atom.form secondPath ∈
        inputEventPolynomials secondCellState secondPath) :
    formulaEvalWith formula (inputEventCanonicalValue firstCell) =
      formulaEvalWith formula (inputEventCanonicalValue secondCell) := by
  apply formulaEvalWith_eq_of_atomTests
  intro atom member
  exact inputEventCanonicalValue_test_iff_of_refinement firstCell secondCell
    squarefree degreeNonzero elimination atom.form
    (firstMembers atom member) (secondMembers atom member) atom.sign

/-- Refining an event factor against the historical current formula does not
change either already-classified child-owner bit.  All original child
relations restrict to the selected divisor, and the same-track sign theorem
compares the original and refined canonical oracles inside the same separated
box. -/
theorem currentFormulaInputCell_ownerChecks_eq
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
    cell.ownerChecks = (currentFormulaInputCell cell).ownerChecks := by
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
          (inputEventCanonicalValue (currentFormulaInputCell cell)) := by
    apply formulaEvalWith_inputEvents_eq_of_refinement
      (firstOutput := output) (secondOutput := localOutput)
      cell (currentFormulaInputCell cell) squarefree degreeNonzero elimination
    · intro atom member
      exact clearedForm_mem_inputEventPolynomials_of_advance_atom state path
        bit atom member
    · intro atom member
      exact clearedForm_mem_inputEventPolynomials_of_advance_atom state path
        bit atom member
  rw [inputEventPair_eq_canonical, inputEventPair_eq_canonical]
  exact Prod.ext (formulaEquality false) (formulaEquality true)

/-- Away from the matrix-updating third sector bit, a canonically selected
owner formula becomes the canonically true current predicate at every later
positive event on the same track.  The later event is reclassified under the
old child conditions only for the comparison; its own invariant remains
indexed by the new parser state. -/
theorem currentFormulaCanonicalCheck_of_selected_event_refinement
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
    (selected : formulaEvalWith (inputAdvanceFormula state bit)
      (inputEventCanonicalValue firstCell) = true) :
    currentFormulaCanonicalCheck secondCell = true := by
  let reclassified : InputEventCell state secondEvent :=
    currentFormulaReclassifiedInputCell secondCell state
  have evaluationEquality :
      formulaEvalWith (inputAdvanceFormula state bit)
          (inputEventCanonicalValue firstCell) =
        formulaEvalWith (inputAdvanceFormula state bit)
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
        firstPath bit atom member
    · exact clearedForm_mem_inputEventPolynomials_of_advance_atom state
        secondPath bit atom member
  have transferred : formulaEvalWith (inputAdvanceFormula state bit)
      (inputEventCanonicalValue reclassified) = true := by
    rw [← evaluationEquality]
    exact selected
  rw [currentFormulaCanonicalCheck_eq_reclassifiedInputCell secondCell state,
    inputStateFormula_step_eq_inputAdvanceFormula_of_not_completed state bit
      notCompleted]
  exact transferred

/-- Word-and-box propagation for an ordinary owner step, stated directly on
the numerical state and word.  No rational sample or coupled-state fields are
used by this algebraic event theorem. -/
theorem formulaCanonicalOnInputEvents_ofSelectedPayloadData
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse word).phase =
        .sector kind exponent (.two first second)) :
    FormulaCanonicalOnInputEvents separation.state
      (word ++ [selected.bit]) := by
  unfold FormulaCanonicalOnInputEvents
  rw [rawParser_parse_append_singleton]
  intro later path event cell
  apply currentFormulaCanonicalCheck_of_selected_event_refinement
    (firstOutput := separation) (secondOutput := later)
    selected.candidate.inputCell cell squarefree degreeNonzero
      elimination notCompleted
  have selectedValue : eventPayloadCanonicalValue
      selected.toIncrementalPayload =
      inputEventCanonicalValue selected.candidate.inputCell := rfl
  rw [← selectedValue]
  exact eventPayloadCanonical_holds selected

/-- A complete algebraic event owner supplies the phase-indexed support
certificate for its child directly.  An ordinary source phase establishes
the stronger full current-formula statement; a completed source phase resets
to `loopUnary 0`, so the child obligation is empty. -/
theorem CompletedSectorCanonicalData.ofSelectedPayload
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CompletedSectorCanonicalData separation.state
      (word ++ [selected.bit]) := by
  let state := RawParser.parse word
  by_cases completed : ∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second)
  · intro nextCompleted
    have impossible := rawParser_step_not_completed_of_completed state
      selected.bit completed
    rw [rawParser_parse_append_singleton] at nextCompleted
    exact (impossible nextCompleted).elim
  · intro _nextCompleted
    exact formulaCanonicalOnInputEvents_ofSelectedPayloadData numerical word
      separation selected squarefree degreeNonzero elimination completed

theorem CompletedSectorControllerCanonicalData.ofSelectedPayload
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (numerical : WindingOneState p (RatBox.symmetric R hR))
    (word : Prefix.Word)
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      numerical (adjugate (RawParser.parse word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    CompletedSectorControllerCanonicalData separation.state
      (word ++ [selected.bit]) :=
  (CompletedSectorCanonicalData.ofSelectedPayload numerical word separation
    selected squarefree degreeNonzero elimination).controllerCanonical

/-- Coupled-state compatibility wrapper for the direct word-and-box theorem. -/
theorem formulaCanonicalOnInputEvents_ofSelectedPayload
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.word).phase =
        .sector kind exponent (.two first second)) :
    FormulaCanonicalOnInputEvents separation.state
      (current.word ++ [selected.bit]) :=
  formulaCanonicalOnInputEvents_ofSelectedPayloadData current.numerical
    current.word separation selected squarefree degreeNonzero elimination
    notCompleted

/-- Global-family specialization of the common selected-payload theorem. -/
theorem formulaCanonicalOnInputEvents_ofSelectedEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.word).phase =
        .sector kind exponent (.two first second)) :
    FormulaCanonicalOnInputEvents separation.state
      (current.word ++ [selected.bit]) :=
  formulaCanonicalOnInputEvents_ofSelectedPayload current separation
    selected.toPayload squarefree degreeNonzero elimination notCompleted

/-- State-level wrapper: the successor may be built by any persistent
sampling construction; only its numerical box and appended word matter. -/
theorem CurrentFormulaCanonicalOnInputEvents.ofSelectedEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.word).phase =
        .sector kind exponent (.two first second))
    (next : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (numerical_eq : next.numerical = separation.state)
    (word_eq : next.word = current.word ++ [selected.bit]) :
    CurrentFormulaCanonicalOnInputEvents next := by
  unfold CurrentFormulaCanonicalOnInputEvents
  rw [numerical_eq, word_eq]
  exact formulaCanonicalOnInputEvents_ofSelectedEvent current separation
    selected squarefree degreeNonzero elimination notCompleted

theorem CurrentFormulaCanonicalOnInputEvents.ofSelectedPayload
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.word).phase =
        .sector kind exponent (.two first second))
    (next : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (numerical_eq : next.numerical = separation.state)
    (word_eq : next.word = current.word ++ [selected.bit]) :
    CurrentFormulaCanonicalOnInputEvents next := by
  unfold CurrentFormulaCanonicalOnInputEvents
  rw [numerical_eq, word_eq]
  exact formulaCanonicalOnInputEvents_ofSelectedPayload current separation
    selected squarefree degreeNonzero elimination notCompleted

/-- Every selected event transition preserves exactly the phase-indexed
reachable invariant.  Ordinary transitions establish the stronger full
current-formula statement; a completed-sector transition resets to
`loopUnary 0`, making the target obligation vacuous. -/
theorem CompletedSectorCanonicalOnInputEvents.ofSelectedPayload
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (numerical_eq : next.numerical = separation.state)
    (word_eq : next.word = current.word ++ [selected.bit]) :
    CompletedSectorCanonicalOnInputEvents next := by
  let state := RawParser.parse current.word
  by_cases completed : ∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second)
  · intro nextCompleted
    have impossible :=
      rawParser_step_not_completed_of_completed state selected.bit completed
    rw [word_eq, rawParser_parse_append_singleton] at nextCompleted
    exact (impossible nextCompleted).elim
  · intro _nextCompleted
    exact CurrentFormulaCanonicalOnInputEvents.ofSelectedPayload current
      separation selected squarefree degreeNonzero elimination completed next
      numerical_eq word_eq

theorem CompletedSectorCanonicalOnInputEvents.ofSelectedEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventCount separation)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (next : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (numerical_eq : next.numerical = separation.state)
    (word_eq : next.word = current.word ++ [selected.bit]) :
    CompletedSectorCanonicalOnInputEvents next :=
  CompletedSectorCanonicalOnInputEvents.ofSelectedPayload current separation
    selected.toPayload squarefree degreeNonzero elimination next numerical_eq
      word_eq

/-- A form whose interval enclosure avoids zero cannot receive canonical
value zero at a positive event contained in that box. -/
theorem inputEventCanonicalValue_ne_zero_of_strictSignCheck
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    {decisionBox : RatBox}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (eventRefines : output.state.box.Refines decisionBox)
    (form : HermitianForm)
    (check : strictSignCheck form decisionBox = true)
    (member : clearedForm form path ∈ inputEventPolynomials state path) :
    inputEventCanonicalValue cell form ≠ 0 := by
  intro canonicalZero
  have divides : cell.branch.factor.polynomial.toPolynomial ∣
      (clearedForm form path).toPolynomial :=
    ConditionRelations.dvd_of_canonicalEventValue_eq_zero
      cell.branch.relations cell.parent
      (cell.branch.computeEventSigns cell.parent) member (by
        simpa only [inputEventCanonicalValue] using canonicalZero)
  have marginExists : ∃ margin : ℚ, 0 < margin ∧
      ∀ {point : QI}, decisionBox.Contains point →
        margin ≤ |form.eval point| := by
    rcases (strictSignCheck_eq_true_iff form decisionBox).mp check with
        lowerPositive | upperNegative
    · refine ⟨lowerBound form decisionBox, lowerPositive, ?_⟩
      intro point inside
      have lower := lowerBound_le_eval form inside
      have valuePositive := lowerPositive.trans_le lower
      rw [abs_of_pos valuePositive]
      exact lower
    · refine ⟨-upperBound form decisionBox, neg_pos.mpr upperNegative, ?_⟩
      intro point inside
      have upper := eval_le_upperBound form inside
      have valueNegative := upper.trans_lt upperNegative
      rw [abs_of_neg valueNegative]
      linarith
  rcases marginExists with ⟨margin, marginPositive, marginLe⟩
  let coefficient := inputEventFormCoefficient cell form
  have coefficientNonnegative : 0 ≤ coefficient := by
    exact inputEventFormCoefficient_nonneg cell form
  let radius := margin / (2 * (1 + coefficient))
  have denominatorPositive : 0 < 2 * (1 + coefficient) := by
    positivity
  have radiusPositive : 0 < radius :=
    div_pos marginPositive denominatorPositive
  have eventInside : decisionBox.Contains
      (shrinkingInputEventPoint cell squarefree radius radiusPositive) := by
    have strict := eventWindingOneState_strictInterior
      output.state.refinesAmbient cell squarefree
      (shrinkingEventClearance output radius radiusPositive) elimination
    apply eventRefines.contains
    exact strict.refines.contains
      (shrinkingInputEventState_contains_point cell squarefree elimination
        radius radiusPositive)
  have lowerAbsolute := marginLe eventInside
  have upperAbsolute := shrinkingInputEventForm_le_of_dvd cell squarefree
    radius radiusPositive form divides
  have scaledRadius : 2 * (1 + coefficient) * radius = margin := by
    dsimp only [radius]
    exact mul_div_cancel₀ margin denominatorPositive.ne'
  have strictUpper : coefficient * radius < margin := by
    nlinarith
  exact (lowerAbsolute.trans_lt (upperAbsolute.trans_lt strictUpper)).false

/-- A successful strict box check fixes the sign of an event's canonical
form to the sign at the rational box center. -/
theorem inputEventCanonicalValue_mul_center_pos_of_strictSignCheck
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    {decisionBox : RatBox}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (eventRefines : output.state.box.Refines decisionBox)
    (form : HermitianForm)
    (check : strictSignCheck form decisionBox = true)
    (member : clearedForm form path ∈ inputEventPolynomials state path) :
    0 < inputEventCanonicalValue cell form *
      form.eval decisionBox.center := by
  have canonicalNonzero :=
    inputEventCanonicalValue_ne_zero_of_strictSignCheck cell squarefree
      elimination eventRefines form check member
  let point := shrinkingInputEventPoint cell squarefree 1 zero_lt_one
  have canonicalPoint :
      0 < inputEventCanonicalValue cell form * form.eval point := by
    simpa only [point] using
      inputEventCanonicalValue_mul_shrinkingPoint_pos cell squarefree 1
        zero_lt_one form member canonicalNonzero
  have pointInside : decisionBox.Contains point := by
    have strict := eventWindingOneState_strictInterior
      output.state.refinesAmbient cell squarefree
      (shrinkingEventClearance output 1 zero_lt_one) elimination
    apply eventRefines.contains
    exact strict.refines.contains
      (shrinkingInputEventState_contains_point cell squarefree elimination 1
        zero_lt_one)
  have centerPoint :
      0 < form.eval decisionBox.center * form.eval point :=
    eval_center_mul_pos_of_strictSignCheck form check pointInside
  apply CCLCoupledTrack.sameSign_of_common_anchor
      (anchor := form.eval point)
  · simpa only [_root_.mul_comm] using canonicalPoint
  · simpa only [_root_.mul_comm] using centerPoint

/-- A child formula decided by strict interval arithmetic has the same truth
value in every positive event oracle retained in that box. -/
theorem inputAdvanceFormula_canonical_eq_center_of_strictOnBox
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    {decisionBox : RatBox}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (eventRefines : output.state.box.Refines decisionBox)
    (bit : Bool)
    (check : CCLHermitianBox.Formula.strictOnBox
      (inputAdvanceFormula state bit) decisionBox = true) :
    formulaEvalWith (inputAdvanceFormula state bit)
        (inputEventCanonicalValue cell) =
      formulaEvalWith (inputAdvanceFormula state bit)
        (fun form => form.eval decisionBox.center) := by
  apply formulaEvalWith_eq_of_atomTests
  intro atom member
  have atomCheck := strictSignCheck_of_mem_formulaAtoms
    (inputAdvanceFormula state bit) decisionBox check member
  have polynomialMember :=
    clearedForm_mem_inputEventPolynomials_of_advance_atom state path bit atom
      member
  have sameSign :=
    inputEventCanonicalValue_mul_center_pos_of_strictSignCheck cell squarefree
      elimination eventRefines atom.form atomCheck polynomialMember
  exact SignTest.holds_iff_of_mul_pos atom.sign sameSign

/-- In particular, a uniformly true child remains canonically true at every
later positive event in the strictly decided box. -/
theorem inputAdvanceFormula_canonical_holds_of_strictOnBox
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    {output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix)}
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path output.state.box}
    {decisionBox : RatBox}
    (cell : InputEventCell state event)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (eventRefines : output.state.box.Refines decisionBox)
    (bit : Bool)
    (check : CCLHermitianBox.Formula.strictOnBox
      (inputAdvanceFormula state bit) decisionBox = true)
    (centerHolds : (inputAdvanceFormula state bit).Holds
      decisionBox.center) :
    formulaEvalWith (inputAdvanceFormula state bit)
      (inputEventCanonicalValue cell) = true := by
  rw [inputAdvanceFormula_canonical_eq_center_of_strictOnBox cell squarefree
    elimination eventRefines bit check]
  exact (formulaEvalWith_eval_eq_true_iff _ _).2 centerHolds

/-- The certificate retained by a strict-cell child decision remains valid
for every positive event found after any further denominator refinement. -/
theorem strictChild_canonicalOnSeparatedInputEvents
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient} {state : RawParser.State}
    (output : CCLDenominator.SeparationOutput p ambient current
      (adjugate state.matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (bit : Bool)
    (strict : CCLHermitianBox.Formula.strictOnBox
      (inputAdvanceFormula state bit) output.state.box = true)
    (holds : ∀ {input : QI}, output.state.box.Contains input →
      (inputAdvanceFormula state bit).Holds input)
    (later : CCLDenominator.SeparationOutput p ambient output.state
      (adjugate state.matrix))
    (candidate : SourceInputEventCell p later.state.box state) :
    formulaEvalWith (inputAdvanceFormula state bit)
      (inputEventCanonicalValue candidate.inputCell) = true := by
  apply inputAdvanceFormula_canonical_holds_of_strictOnBox
    candidate.inputCell squarefree elimination later.refines bit strict
  exact holds output.state.box.contains_center

/-- A uniformly strict ordinary child becomes the canonically true current
predicate at every later positive event.  The event is reclassified under
the old child conditions exactly as in the equality-owner proof. -/
theorem currentFormulaCanonicalCheck_of_strictChild
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : WindingOneState p (RatBox.symmetric R hR)}
    {state : RawParser.State} {bit : Bool}
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current (adjugate state.matrix))
    (later : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      output.state (adjugate state.matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (notCompleted : ¬∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second))
    (strict : CCLHermitianBox.Formula.strictOnBox
      (inputAdvanceFormula state bit) output.state.box = true)
    (holds : ∀ {input : QI}, output.state.box.Contains input →
      (inputAdvanceFormula state bit).Holds input)
    {path : ProjectivePath.Path}
    {event : RelevantCurveEvent p path later.state.box}
    (cell : InputEventCell (RawParser.step state bit) event) :
    currentFormulaCanonicalCheck cell = true := by
  let reclassified : InputEventCell state event :=
    currentFormulaReclassifiedInputCell cell state
  have selected : formulaEvalWith (inputAdvanceFormula state bit)
      (inputEventCanonicalValue reclassified) = true := by
    apply inputAdvanceFormula_canonical_holds_of_strictOnBox reclassified
      squarefree elimination later.refines bit strict
    exact holds output.state.box.contains_center
  rw [currentFormulaCanonicalCheck_eq_reclassifiedInputCell cell state,
    inputStateFormula_step_eq_inputAdvanceFormula_of_not_completed state bit
      notCompleted]
  exact selected

/-- Full ordinary-transition invariant supplied by a uniformly strict child. -/
theorem formulaCanonicalOnInputEvents_ofStrictChild
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (bit : Bool)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.word).phase =
        .sector kind exponent (.two first second))
    (strict : CCLHermitianBox.Formula.strictOnBox
      (inputAdvanceFormula (RawParser.parse current.word) bit)
        output.state.box = true)
    (holds : ∀ {input : QI}, output.state.box.Contains input →
      (inputAdvanceFormula (RawParser.parse current.word) bit).Holds input) :
    FormulaCanonicalOnInputEvents output.state (current.word ++ [bit]) := by
  unfold FormulaCanonicalOnInputEvents
  rw [rawParser_parse_append_singleton]
  intro later path event cell
  have matrixEq := rawParser_step_matrix_eq_of_not_completed
    (RawParser.parse current.word) bit notCompleted
  let oldLater : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      output.state (adjugate (RawParser.parse current.word).matrix) :=
    { state := later.state
      refines := later.refines
      margin := later.margin
      margin_pos := later.margin_pos
      lower := by
        intro input contains
        simpa only [matrixEq] using later.lower contains }
  exact currentFormulaCanonicalCheck_of_strictChild output oldLater squarefree
    elimination notCompleted strict holds cell

/-- Every strict-cell transition preserves the phase-indexed reachable
invariant; a completed-sector transition again has no target obligation. -/
theorem CompletedSectorCanonicalOnInputEvents.ofStrictChild
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (bit : Bool)
    (strict : CCLHermitianBox.Formula.strictOnBox
      (inputAdvanceFormula (RawParser.parse current.word) bit)
        output.state.box = true)
    (holds : ∀ {input : QI}, output.state.box.Contains input →
      (inputAdvanceFormula (RawParser.parse current.word) bit).Holds input)
    (next : CCLCoupledTrack.State p (RatBox.symmetric R hR))
    (numerical_eq : next.numerical = output.state)
    (word_eq : next.word = current.word ++ [bit]) :
    CompletedSectorCanonicalOnInputEvents next := by
  let state := RawParser.parse current.word
  by_cases completed : ∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second)
  · intro nextCompleted
    have impossible := rawParser_step_not_completed_of_completed state bit
      completed
    rw [word_eq, rawParser_parse_append_singleton] at nextCompleted
    exact (impossible nextCompleted).elim
  · intro _nextCompleted
    rw [numerical_eq, word_eq]
    exact formulaCanonicalOnInputEvents_ofStrictChild current output squarefree
      elimination bit completed strict holds

end CCLCanonicalEvent
end FTA
