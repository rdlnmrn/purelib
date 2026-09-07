import FTA.CCLBranchController
import FTA.CCLBoundaryStrictCell
import FTA.CCLCoupledController
import FTA.CCLEventTerminal
import FTA.CCLGuardCellClearance
import FTA.CCLIncrementalEventOwner
import FTA.CCLPositiveEventTrack
import FTA.CCLStrictChildSemantics
import FTA.CCLTerminalSeparation
import FTA.GlobalNonnegativity
import CCL.RationalEncoder

/-!
# Sample-free CCL decisions on a winding-one track

The branch decision of Theorem 10.2 is logically prior to the compatible
rational sample of Lemma 10.4.  This module records that separation directly:
a state contains only its winding-one numerical box and finite raw word.
Positive x--y curve counts choose the next raw bit at the isolated algebraic
event, while an identically-zero event or decoder pole terminates exactly.

No rational witness is required to persist through future boxes.  The
remaining all-clear constructor retains the complete finite clearance data
needed to decide the unique strict child in the sample-free invariant.
-/

namespace FTA
namespace CCLDirectTrack

open CCL
open FTA.AxisSafeCuts
open FTA.CCLBoundaryNeighborhood
open FTA.CCLBoundaryStrictCell
open FTA.CCLBranchController
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchEvidence
open FTA.CCLBranchPartition
open FTA.CCLBranchPlan
open FTA.CCLClearanceExclusion
open FTA.CCLGeometry
open FTA.CCLGuardCellClearance
open FTA.CCLHermitianBox
open FTA.CCLIncrementalEventOwner
open FTA.CCLPositiveEventTrack
open FTA.CCLStrictChildSemantics
open FTA.CCLTerminalSeparation
open FTA.CentralBandGrid
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- The direct Theorem 10.2 state: numerical winding data and a symbolic raw
prefix, without the stronger future-box sample family. -/
structure State (p : GaussianPolynomial) (ambient : RatBox) where
  numerical : WindingOneState p ambient
  word : Prefix.Word

/-- Initial direct state at the empty raw word. -/
def State.ofWindingOne
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) : State p ambient where
  numerical := numerical
  word := []

/-- Numerical refinement at a fixed raw word.  This is the direct track's
sample-free accuracy operation: no represented point has to be transported
into the smaller box. -/
def State.refine
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) (numerical : WindingOneState p ambient)
    (_refines : numerical.box.Refines current.numerical.box) :
    State p ambient where
  numerical := numerical
  word := current.word

@[simp] theorem State.refine_word
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines current.numerical.box) :
    (current.refine numerical refines).word = current.word := rfl

theorem State.refine_box
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines current.numerical.box) :
    (current.refine numerical refines).numerical.box.Refines
      current.numerical.box :=
  refines

/-- One direct CCL decision.  A nonterminal result appends exactly one bit and
retains the numerical nesting proof independently of any rational sample. -/
inductive StepResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) where
  | zero (root : p.eval 0 = 0) : StepResult current
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero) :
      StepResult current
  | next (bit : Bool) (state : State p ambient)
      (refines : state.numerical.box.Refines current.numerical.box)
      (word_eq : state.word = current.word ++ [bit]) : StepResult current

/-! ## History-free algebraic event opening -/

/-- The denominator and algebraic-event front half of a direct step.  A
selected event already carries its unique incremental bit and exact curve
count decision.  The all-neither branch is retained explicitly for terminal
separation or the subsequent strict-cell analysis. -/
inductive IncrementalEventOpening
    (p : GaussianPolynomial) (ambient : RatBox)
    (current : State p ambient) where
  | ready (result : StepResult current) :
      IncrementalEventOpening p ambient current
  | owner
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (selected : CCLIncrementalEventOwner.SelectedPayload separation) :
      IncrementalEventOpening p ambient current
  | allNeither
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (globalNone : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.word) separation,
        CCLPositiveEventSemantics.inputEventIncrementalChecks
          candidate.inputCell = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.word) separation,
        CCLPositiveEventSemantics.inputEventIncrementalChecks
          candidate.inputCell = (false, false)) :
      IncrementalEventOpening p ambient current

/-- Execute denominator separation and both finite history-free event
families.  No historical owner check and no represented sample is consulted. -/
def openIncrementalEvents
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient) (current : State p ambient) :
    IncrementalEventOpening p ambient current :=
  match CCLDenominator.decide track current.numerical
      (adjugate (RawParser.parse current.word).matrix)
      (CCLBranchEvidence.adjugate_lowerRow_ne
        (RawParser.parse current.word).matrix (by
          simpa only [determinant, Mat2.det] using
            RawParser.parse_det_ne current.word)) with
  | .terminal point root _contains _strict _denominatorZero => by
      if zero : point = 0 then
        exact .ready (.zero (by simpa only [zero] using root))
      else
        exact .ready (.terminal point root zero
          (RationalEncoder.encode point zero) rfl)
  | .separated separation =>
      match CCLIncrementalEventOwner.decideCombined
          (RawParser.parse current.word) separation with
      | .globalOwner selected => .owner separation selected.toPayload
      | .guardOwner selected => .owner separation selected.toPayload
      | .allNeither globalNone guardNone =>
          .allNeither separation globalNone guardNone

/-- Resolve identically-zero direct events immediately.  Positive events
retain their already-decided incremental bit and count certificate for the
Newton-band extraction. -/
def IncrementalEventOpening.resolveExact :
    {p : GaussianPolynomial} → {ambient : RatBox} →
    {current : State p ambient} →
    IncrementalEventOpening p ambient current →
      IncrementalEventOpening p ambient current
  | _, _, _, .ready result => .ready result
  | _, _, _, .allNeither separation globalNone guardNone =>
      .allNeither separation globalNone guardNone
  | _, _, _, .owner separation selected =>
      match selected.decision with
      | .positive evidence =>
          .owner separation { selected with decision := .positive evidence }
      | .identicallyZero realZero imagZero => by
          let exactRoot :=
            FTA.CCLEventTerminal.InputEventCell.identicallyZeroRoot
              selected.candidate.inputCell realZero imagZero
          if zero : exactRoot.point = 0 then
            exact .ready (.zero (by simpa only [zero] using exactRoot.root))
          else
            exact .ready (.terminal exactRoot.point exactRoot.root zero
              (RationalEncoder.encode exactRoot.point zero) rfl)

/-- Close one history-free event owner to a direct terminal or appended-bit
successor.  A positive event contributes only its numerical Newton band and
selected local bit; the direct state has no historical sample invariant to
reconstruct. -/
def resolveIncrementalOwner
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : CCLIncrementalEventOwner.SelectedPayload separation)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StepResult current :=
  match selected.decision with
  | .identicallyZero realZero imagZero => by
      let exactRoot :=
        FTA.CCLEventTerminal.InputEventCell.identicallyZeroRoot
          selected.candidate.inputCell realZero imagZero
      if zero : exactRoot.point = 0 then
        exact .zero (by simpa only [zero] using exactRoot.root)
      else
        exact .terminal exactRoot.point exactRoot.root zero
          (RationalEncoder.encode exactRoot.point zero) rfl
  | .positive _evidence =>
      let numerical := selected.numericalState squarefree elimination
      .next selected.bit
        { numerical := numerical
          word := current.word ++ [selected.bit] }
        ((selected.numericalState_strictInterior squarefree
          elimination).refines.trans separation.refines)
        rfl

/-- Resolve every selected incremental owner, retaining only the all-neither
case for the clear/terminal half of the direct controller. -/
def IncrementalEventOpening.resolveOwner
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : State p ambient}
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    IncrementalEventOpening p ambient current →
      IncrementalEventOpening p ambient current
  | .ready result => .ready result
  | .allNeither separation globalNone guardNone =>
      .allNeither separation globalNone guardNone
  | .owner separation selected =>
      .ready (resolveIncrementalOwner current separation selected squarefree
        elimination)

/-- Complete the denominator and positive-event half of one direct step. -/
def openIncrementalStep
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient) (current : State p ambient)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    IncrementalEventOpening p ambient current :=
  (openIncrementalEvents track current).resolveOwner squarefree elimination

/-- The winding-one state extracted directly from a selected positive event,
with the selected raw bit appended symbolically. -/
def positiveEventState
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    State p (RatBox.symmetric R hR) where
  numerical := selectedEventStatePayload selected.toIncrementalPayload
    squarefree elimination
  word := current.word ++ [selected.bit]

theorem positiveEventState_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (positiveEventState current output selected squarefree
      elimination).numerical.box.Refines current.numerical.box := by
  exact (selectedEventStatePayload_strictInterior selected.toIncrementalPayload
    squarefree elimination).refines.trans output.refines

/-- Resolve a selected algebraic owner without a compatible rational sample.
The finite curve-count decision either reconstructs an exact rational root or
supplies the positive event whose owner truth table already selected the bit. -/
def resolveSelectedEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StepResult current :=
  match selected.decision with
  | .identicallyZero realZero imagZero => by
      let exactRoot :=
        FTA.CCLEventTerminal.InputEventCell.identicallyZeroRoot
          selected.candidate.inputCell realZero imagZero
      if zero : exactRoot.point = 0 then
        exact .zero (by simpa only [zero] using exactRoot.root)
      else
        exact .terminal exactRoot.point exactRoot.root zero
          (RationalEncoder.encode exactRoot.point zero) rfl
  | .positive _evidence =>
      .next selected.bit
        (positiveEventState current output selected squarefree elimination)
        (positiveEventState_refines current output selected squarefree
          elimination)
        rfl

/-- Sample-free result of the complete denominator and curve-family opening.
Every positive algebraic owner event is already a direct bit step.  The two
remaining constructors retain the zero-count arc clearances, terminal
separation, and optional terminal-guard clearance used by the strict child. -/
inductive Opening
    (p : GaussianPolynomial) (ambient : RatBox)
    (current : State p ambient) where
  | ready (result : StepResult current) : Opening p ambient current
  | noEventOwner
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (none : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (noIdenticallyZero : CCLCoupledController.firstIdenticallyZeroRoot?
        (RawParser.parse current.word) separation = Option.none)
      (arcs : List (BoundaryArc p)) (evidence : AllClear p arcs)
      (alignment : ClearFamilyAlignment p separation.state.box
        (separatedRelevantClearCells p (RawParser.parse current.word)
          separation) arcs)
      (guardCurve : GuardCurveFamilyDecision p separation.state.box
        (separatedEventGuardCells p (RawParser.parse current.word) separation))
      (terminal : CCLTerminalSeparation.SeparationOutput p ambient
        (RawParser.parse current.word) separation.state [false, true])
      (output : RefinementOutput p ambient terminal.numerical evidence) :
      Opening p ambient current
  | guardClear
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (none : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (noIdenticallyZero : CCLCoupledController.firstIdenticallyZeroRoot?
        (RawParser.parse current.word) separation = Option.none)
      (arcs : List (BoundaryArc p)) (evidence : AllClear p arcs)
      (alignment : ClearFamilyAlignment p separation.state.box
        (separatedRelevantClearCells p (RawParser.parse current.word)
          separation) arcs)
      (terminal : CCLTerminalSeparation.SeparationOutput p ambient
        (RawParser.parse current.word) separation.state [false, true])
      (output : RefinementOutput p ambient terminal.numerical evidence)
      (guardEvidence : AllGuardClear p separation.state.box
        (separatedEventGuardCells p (RawParser.parse current.word) separation))
      (guardOutput : GuardRefinementOutput p ambient output.state
        guardEvidence) :
      Opening p ambient current

/-- Run the existing finite x--y Sturm/curve-count analysis on a direct state.
The event branches decide their CCL bit immediately; no owner sampler is
consulted. -/
def openStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : State p (RatBox.symmetric R hR))
    (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    Opening p (RatBox.symmetric R hR) current :=
  match analyzeBranchFamilies track current.numerical
      (RawParser.parse current.word) (by
        simpa only [determinant, Mat2.det] using
          RawParser.parse_det_ne current.word) clearOwnerLabel with
  | .terminalPole point root _contains _strict _denominatorZero => by
      if zero : point = 0 then
        exact .ready (.zero (by simpa only [zero] using root))
      else
        exact .ready (.terminal point root zero
          (RationalEncoder.encode point zero) rfl)
  | .eventOwner output selected =>
      .ready (resolveSelectedEvent current output selected.toPayload
        squarefree elimination)
  | .guardEventOwner output selected =>
      .ready (resolveSelectedEvent current output selected.toPayload
        squarefree elimination)
  | .noEventOwner output allNone guardNone clear =>
      match clear with
      | .terminal point _contains root => by
          if zero : point = 0 then
            exact .ready (.zero (by simpa only [zero] using root))
          else
            exact .ready (.terminal point root zero
              (RationalEncoder.encode point zero) rfl)
      | .refined arcs evidence alignment _preliminaryOutput =>
          match rootCheck : CCLCoupledController.firstIdenticallyZeroRoot?
              (RawParser.parse current.word) output with
          | some exactRoot => by
              if zero : exactRoot.point = 0 then
                exact .ready (.zero (by
                  simpa only [zero] using exactRoot.root))
              else
                exact .ready (.terminal exactRoot.point exactRoot.root zero
                  (RationalEncoder.encode exactRoot.point zero) rfl)
          | none =>
              match CCLTerminalSeparation.separate track
                  (RawParser.parse current.word) output.state with
              | .terminal point root _contains => by
                  if zero : point = 0 then
                    exact .ready (.zero (by simpa only [zero] using root))
                  else
                    exact .ready (.terminal point root zero
                      (RationalEncoder.encode point zero) rfl)
              | .separated terminal =>
                  let refined := refineForClearance track terminal.numerical
                    evidence
                  let guardCurve := decideSeparatedGuardCurveFamily
                    (RawParser.parse current.word) output (by
                      simpa only [determinant, Mat2.det] using
                        RawParser.parse_det_ne current.word)
                  .noEventOwner output allNone guardNone rootCheck arcs
                    evidence alignment guardCurve terminal refined

/-- Execute the sample-free terminal-guard trichotomy.  Its clear branch
performs the second quantitative refinement, while an identically-zero guard
returns the exact terminal root. -/
def Opening.resolveGuardClearance
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : State p ambient}
    (track : WindingOneTrack p ambient) :
    Opening p ambient current → Opening p ambient current
  | .ready result => .ready result
  | .guardClear separation allNone guardNone noIdenticallyZero arcs evidence
      alignment terminal output guardEvidence guardOutput =>
      .guardClear separation allNone guardNone noIdenticallyZero arcs evidence
        alignment terminal output guardEvidence guardOutput
  | .noEventOwner separation allNone guardNone noIdenticallyZero arcs evidence
      alignment guardCurve terminal output =>
      match guardCurve with
      | .allClear guardEvidence =>
          let guardOutput := refineForGuardClearance track output.state
            guardEvidence
          .guardClear separation allNone guardNone noIdenticallyZero arcs
            evidence alignment terminal output guardEvidence guardOutput
      | .identicallyZero sourceCell member realZero imagZero _relevance => by
          let exactRoot :=
            CCLCoupledController.exactRootOfSeparatedIdenticallyZeroGuardCell
              separation (by
                simpa only [determinant, Mat2.det] using
                  RawParser.parse_det_ne current.word)
              sourceCell member realZero imagZero
          if zero : exactRoot.point = 0 then
            exact .ready (.zero (by
              simpa only [zero] using exactRoot.root))
          else
            exact .ready (.terminal exactRoot.point exactRoot.root zero
              (RationalEncoder.encode exactRoot.point zero) rfl)
      | .positive sourceCell member clearedNonzero countPositive event
          eventMember =>
          .noEventOwner separation allNone guardNone noIdenticallyZero arcs
            evidence alignment
              (.positive sourceCell member clearedNonzero countPositive
                event eventMember)
            terminal output

/-- Complete sample-free opening through both ordinary and terminal-guard
zero-count refinements. -/
def openGuardStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : State p (RatBox.symmetric R hR))
    (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    Opening p (RatBox.symmetric R hR) current :=
  (openStep track current clearOwnerLabel squarefree
    elimination).resolveGuardClearance track

/-! ## Direct decision on the completed strict cell -/

/-- The output of the all-clear branch before historical reachability is
attached to the appended word.  Its Boolean is computed at the rational box
center and is forced for every admissible root-track point in that box. -/
structure PlannedBit
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) where
  numerical : WindingOneState p ambient
  refines : numerical.box.Refines current.numerical.box
  inverseDenominator : ∀ {input : QI}, numerical.box.Contains input →
    (adjugate (RawParser.parse current.word).matrix).c * input +
      (adjugate (RawParser.parse current.word).matrix).d ≠ 0
  strictSigns : ∀ source ∈ inputPlan (RawParser.parse current.word),
    strictSignCheck source.form numerical.box = true
  decision : StrictCellDecision (RawParser.parse current.word) numerical.box
  decisionBit : decision.bit = inputLocalBit (RawParser.parse current.word)
    numerical.box.center
  notTerminal : ∀ {input : QI}, numerical.box.Contains input →
    ¬CCL.EncoderParserBridge.TerminalSectorAt (RawParser.parse current.word)
      (RatBox.homographic
        (adjugate (RawParser.parse current.word).matrix) input)
  representedAppend : ∀ {input : QI}, numerical.box.Contains input →
    RawParserSemantics.Represented current.word input →
      RawParserSemantics.Represented
        (current.word ++ [decision.bit]) input

/-- Complete the all-clear x--y Sturm branch through the sample-free strict
cell decision.  No represented rational is chosen or retained: clearance
excludes the finite planned boundaries, interval strictness fixes their sign
cell, and the center of that cell computes the unique possible next bit. -/
def plannedBitOfGuardClearPlan
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (current : State p ambient)
    (separation : CCLDenominator.SeparationOutput p ambient current.numerical
      (adjugate (RawParser.parse current.word).matrix))
    (terminal : CCLTerminalSeparation.SeparationOutput p ambient
      (RawParser.parse current.word) separation.state [false, true])
    {arcs : List (BoundaryArc p)} (evidence : AllClear p arcs)
    (alignment : ClearFamilyAlignment p separation.state.box
      (separatedRelevantClearCells p (RawParser.parse current.word)
        separation) arcs)
    (output : RefinementOutput p ambient terminal.numerical evidence)
    (guardEvidence : AllGuardClear p separation.state.box
      (separatedEventGuardCells p (RawParser.parse current.word)
        separation)) :
    PlannedBit current := by
  let guardOutput := refineForGuardClearance track output.state guardEvidence
  have guardStrictOutput : StrictInterior guardOutput.state.box
      output.state.box := by
    simpa only [guardOutput] using
      refineForGuardClearance_strictInterior track strictRefine output.state
        guardEvidence
  have outputRefinesSeparation : output.state.box.Refines
      separation.state.box := output.refines.trans terminal.refines
  have guardStrictSeparation : StrictInterior guardOutput.state.box
      separation.state.box :=
    FTA.GlobalNonnegativity.strictInterior_trans_refines guardStrictOutput
      outputRefinesSeparation
  let rebasedOutput := output.rebase terminal.refines
  let boundaryEpsilon := min rebasedOutput.epsilon guardOutput.epsilon
  have boundaryEpsilonPositive : 0 < boundaryEpsilon :=
    lt_min rebasedOutput.epsilonPositive guardOutput.epsilonPositive
  let planned := refineForPlannedStrictCellOfExclusion track current.word
    guardOutput.state separation.state.box boundaryEpsilon
      guardStrictSeparation boundaryEpsilonPositive (by
        intro source sourceMember point contains boundary near
        exact alignedAllClear_guardClear_not_near_boundary alignment
          rebasedOutput guardEvidence guardOutput source sourceMember point
            contains boundary near)
  have plannedRefinesSeparation : planned.state.box.Refines
      separation.state.box :=
    planned.refines.trans guardStrictSeparation.refines
  have plannedRefinesTerminal : planned.state.box.Refines
      terminal.numerical.box :=
    planned.refines.trans (guardOutput.refines.trans output.refines)
  have centerDenominator :
      (adjugate (RawParser.parse current.word).matrix).c *
          planned.state.box.center +
        (adjugate (RawParser.parse current.word).matrix).d ≠ 0 :=
    separation_denominator_ne separation
      (plannedRefinesSeparation.contains planned.state.box.contains_center)
  let decision := decideStrictCell (RawParser.parse current.word)
    planned.state.box planned.strictSigns centerDenominator
  exact
    { numerical := planned.state
      refines := plannedRefinesSeparation.trans separation.refines
      inverseDenominator := by
        intro input inside
        exact separation_denominator_ne separation
          (plannedRefinesSeparation.contains inside)
      strictSigns := planned.strictSigns
      decision := decision
      decisionBit := rfl
      notTerminal := by
        intro input inside
        apply terminal.excludes_terminalSectorAt input
          (by simpa only [determinant, Mat2.det] using
            RawParser.parse_det_ne current.word)
          (separation_denominator_ne separation
            (plannedRefinesSeparation.contains inside))
        exact plannedRefinesTerminal.contains inside
      representedAppend := by
        intro input inside represented
        have terminalInside : terminal.numerical.box.Contains input :=
          plannedRefinesTerminal.contains inside
        let parser := RawParser.parse current.word
        have determinantNonzero : determinant parser.matrix ≠ 0 := by
          simpa only [parser, determinant, Mat2.det] using
            RawParser.parse_det_ne current.word
        have inverseDenominator :
            (adjugate parser.matrix).c * input +
              (adjugate parser.matrix).d ≠ 0 :=
          separation_denominator_ne separation
            (plannedRefinesSeparation.contains inside)
        have currentHolds : parser.Holds
            (RatBox.homographic (adjugate parser.matrix) input) := by
          rcases represented with ⟨tail, represents⟩
          rw [CCLBranchSampling.inverse_tail_eq_of_represents parser input tail
            determinantNonzero inverseDenominator represents]
          exact represents.2.2
        have existsChild : ∃ bit,
            (FTA.CCLFormulaPullback.inputAdvanceFormula parser bit).Holds
              input := by
          by_cases falseHolds :
              (FTA.CCLFormulaPullback.inputAdvanceFormula parser false).Holds
                input
          · exact ⟨false, falseHolds⟩
          · by_cases trueHolds :
                (FTA.CCLFormulaPullback.inputAdvanceFormula parser true).Holds
                  input
            · exact ⟨true, trueHolds⟩
            · have none : ∀ bit,
                  ¬(FTA.CCLFormulaPullback.inputAdvanceFormula
                    parser bit).Holds input := by
                intro bit
                cases bit
                · exact falseHolds
                · exact trueHolds
              exact ((terminal.excludes_no_children input determinantNonzero
                inverseDenominator currentHolds none) terminalInside).elim
        rcases existsChild with ⟨other, otherHolds⟩
        have bitEq : other = decision.bit :=
          decision.selects inside inverseDenominator otherHolds
        subst other
        exact CCLBranchSampling.represented_append_of_inputFormula
          current.word input decision.bit inverseDenominator represented
            otherHolds }

/-- Close the all-clear plan to a direct appended-bit successor.  The
pointwise `representedAppend` theorem remains available to a wrapping
checkpoint, but no point enters the direct state itself. -/
def PlannedBit.toStepResult
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : State p ambient} (planned : PlannedBit current) :
    StepResult current :=
  .next planned.decision.bit
    { numerical := planned.numerical
      word := current.word ++ [planned.decision.bit] }
    planned.refines rfl

/-! ## Completing the incremental all-neither branch -/

/-- Result after the history-free event opening has also run the ordinary
clear family, exact-root scan, terminal separation, and guard trichotomy.
Every all-clear guard family is closed to a concrete direct bit.  The sole
remaining geometric constructor is a positive terminal guard cell, retaining
all finite provenance needed for its later relevance argument. -/
inductive IncrementalClearOpening
    (p : GaussianPolynomial) (ambient : RatBox)
    (current : State p ambient) where
  | ready (result : StepResult current) :
      IncrementalClearOpening p ambient current
  | positiveGuard
      (separation : CCLDenominator.SeparationOutput p ambient
        current.numerical
        (adjugate (RawParser.parse current.word).matrix))
      (globalNone : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.word) separation,
        CCLPositiveEventSemantics.inputEventIncrementalChecks
          candidate.inputCell = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.word) separation,
        CCLPositiveEventSemantics.inputEventIncrementalChecks
          candidate.inputCell = (false, false))
      (noIdenticallyZero : CCLCoupledController.firstIdenticallyZeroRoot?
        (RawParser.parse current.word) separation = Option.none)
      (arcs : List (BoundaryArc p)) (evidence : AllClear p arcs)
      (alignment : ClearFamilyAlignment p separation.state.box
        (separatedRelevantClearCells p (RawParser.parse current.word)
          separation) arcs)
      (terminal : CCLTerminalSeparation.SeparationOutput p ambient
        (RawParser.parse current.word) separation.state [false, true])
      (output : RefinementOutput p ambient terminal.numerical evidence)
      (sourceCell : SourceEventGuardCell p separation.state.box)
      (member : sourceCell ∈ separatedEventGuardCells p
        (RawParser.parse current.word) separation)
      (clearedNonzero :
        (FTA.ProjectivePath.clearedReal p
          sourceCell.partition.entry.chart.path).isZero = false ∨
        (FTA.ProjectivePath.clearedImag p
          sourceCell.partition.entry.chart.path).isZero = false)
      (countPositive : 0 < FTA.ProjectivePath.commonFactorRootCount2 p
        sourceCell.partition.entry.chart.path clearedNonzero
        sourceCell.item.cell.cell.interval.lower
        sourceCell.item.cell.cell.interval.upper)
      (event : RelevantCurveEvent p
        sourceCell.partition.entry.chart.path separation.state.box)
      (eventMember : event ∈
        CCLBranchEvent.EventGuardCell.relevantCurveEvents
          sourceCell.item.cell) : IncrementalClearOpening p ambient current

/-- Continue a history-free opening through every finite clear/terminal
stage.  The all-clear guard case invokes the already-proved strict-cell plan
and immediately returns its direct successor. -/
def IncrementalEventOpening.resolveClear
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : State p ambient}
    (track : WindingOneTrack p ambient)
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    IncrementalEventOpening p ambient current →
      IncrementalClearOpening p ambient current
  | .ready result => .ready result
  | .owner separation selected =>
      .ready (resolveIncrementalOwner current separation selected squarefree
        elimination)
  | .allNeither separation globalNone guardNone =>
      match refineSeparatedClearFamily track current.numerical
          (RawParser.parse current.word) (by
            simpa only [determinant, Mat2.det] using
              RawParser.parse_det_ne current.word)
          separation clearOwnerLabel with
      | .terminal point _contains root => by
          if zero : point = 0 then
            exact .ready (.zero (by simpa only [zero] using root))
          else
            exact .ready (.terminal point root zero
              (RationalEncoder.encode point zero) rfl)
      | .refined arcs evidence alignment _preliminaryOutput =>
          match rootCheck : CCLCoupledController.firstIdenticallyZeroRoot?
              (RawParser.parse current.word) separation with
          | some exactRoot => by
              if zero : exactRoot.point = 0 then
                exact .ready (.zero (by
                  simpa only [zero] using exactRoot.root))
              else
                exact .ready (.terminal exactRoot.point exactRoot.root zero
                  (RationalEncoder.encode exactRoot.point zero) rfl)
          | none =>
              match CCLTerminalSeparation.separate track
                  (RawParser.parse current.word) separation.state with
              | .terminal point root _contains => by
                  if zero : point = 0 then
                    exact .ready (.zero (by simpa only [zero] using root))
                  else
                    exact .ready (.terminal point root zero
                      (RationalEncoder.encode point zero) rfl)
              | .separated terminal =>
                  let output := refineForClearance track terminal.numerical
                    evidence
                  match decideSeparatedGuardCurveFamily
                      (RawParser.parse current.word) separation (by
                        simpa only [determinant, Mat2.det] using
                          RawParser.parse_det_ne current.word) with
                  | .allClear guardEvidence =>
                      .ready ((plannedBitOfGuardClearPlan track strictRefine
                        current separation terminal evidence alignment output
                          guardEvidence).toStepResult)
                  | .identicallyZero sourceCell member realZero imagZero
                      _relevance => by
                      let exactRoot :=
                        CCLCoupledController.exactRootOfSeparatedIdenticallyZeroGuardCell
                          separation (by
                            simpa only [determinant, Mat2.det] using
                              RawParser.parse_det_ne current.word)
                          sourceCell member realZero imagZero
                      if zero : exactRoot.point = 0 then
                        exact .ready (.zero (by
                          simpa only [zero] using exactRoot.root))
                      else
                        exact .ready (.terminal exactRoot.point exactRoot.root
                          zero (RationalEncoder.encode exactRoot.point zero)
                            rfl)
                  | .positive sourceCell member clearedNonzero countPositive
                      event eventMember =>
                      .positiveGuard separation globalNone guardNone rootCheck
                        arcs evidence alignment terminal output sourceCell
                          member clearedNonzero countPositive event eventMember

/-- One direct controller call through all finite stages except the retained
positive-guard relevance case. -/
def openIncrementalClearStep
    {p : GaussianPolynomial} {ambient : RatBox}
    (track : WindingOneTrack p ambient)
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (current : State p ambient) (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    IncrementalClearOpening p ambient current :=
  (openIncrementalEvents track current).resolveClear track strictRefine
    clearOwnerLabel squarefree elimination

end CCLDirectTrack
end FTA
