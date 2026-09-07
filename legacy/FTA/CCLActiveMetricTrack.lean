import FTA.CCLActiveCanonicalEvent
import FTA.CCLPersistentBlockObservations

/-!
# Direct CCL track with persistent active metric samples

This state joins the sample-free x--y Sturm controller to the history-free
box--truncation coupling.  Its numerical winding box may be refined at a fixed
word independently.  A persistent active provider reconstructs the one
rational point needed by the chordal estimate in whatever later box is
requested.
-/

namespace FTA
namespace CCLActiveMetricTrack

open CCL CCL.GaussianRat
open FTA.AxisSafeCuts
open FTA.CCLActiveBoxCoupling
open FTA.CCLActiveCanonicalEvent
open FTA.CCLActiveEventGrid
open FTA.CCLBoundaryNeighborhood
open FTA.CCLBoundaryStrictCell
open FTA.CCLBranchController
open FTA.CCLBranchEvidence
open FTA.CCLBranchEvent
open FTA.CCLBranchEventOwner
open FTA.CCLBranchPartition
open FTA.CCLBranchPlan
open FTA.CCLBoxCylinderIncrementalEventGrid
open FTA.CCLCanonicalEvent
open FTA.CCLClearanceExclusion
open FTA.CCLChordalEnvelope
open FTA.CCLCompletedBlockContraction
open FTA.CCLCompletedBlockObservation
open FTA.CCLCoupledController
open FTA.CCLDirectTrack
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLGuardCellClearance
open FTA.CCLHermitianBox
open FTA.CCLIncrementalEventOwner
open FTA.CCLMetricTrack
open FTA.CCLPositiveAllNeither
open FTA.CCLPositiveEventSemantics
open FTA.CCLPositiveEventTrack
open FTA.CCLPersistentBlockObservations
open FTA.CCLStrictChildSemantics
open FTA.CCLTerminalSeparation
open FTA.CentralBandGrid
open FTA.GlobalNonnegativity
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Policy for the sole phase that historically used exact canonical active
truth.  Ordinary states retain that stronger certificate.  A sector boundary
entered by a rational tangent instead records that a later completed-sector
all-neither event must be handled by the same constructive boundary geometry,
not eliminated through a false exact-event premise. -/
inductive CompletedSectorPolicy
    {p : GaussianPolynomial} {ambient : RatBox}
    (numerical : WindingOneState p ambient) (word : Prefix.Word) where
  | canonical
      (valid : CompletedSectorActiveControllerCanonicalData numerical word) :
      CompletedSectorPolicy numerical word
  | boundary : CompletedSectorPolicy numerical word

/-- Direct numerical/raw-word state plus exactly the active sample persistence
needed by the metric estimate. -/
structure State (p : GaussianPolynomial) (ambient : RatBox) where
  core : CCLDirectTrack.State p ambient
  samples : PersistentActiveSamples core.word core.numerical
  observations : PersistentObservationChain RawParser.identityMatrix
    (parserBlocks core.word) core.numerical
  completedSector : CompletedSectorPolicy core.numerical core.word

/-- Refine only the winding box.  The raw word is unchanged and the active
provider is restricted by composition of box refinements. -/
def State.refine
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines current.core.numerical.box) :
    State p ambient where
  core := current.core.refine numerical refines
  samples :=
    { sample := by
        intro next nextRefines
        exact current.samples.sample next (nextRefines.trans refines) }
  observations := current.observations.refine refines
  completedSector := match current.completedSector with
    | .canonical valid => .canonical (by
        intro completed
        exact ActiveControllerCanonicalOnInputEvents.refine
          (valid completed) refines)
    | .boundary => .boundary

@[simp] theorem State.refine_word
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines current.core.numerical.box) :
    (current.refine numerical refines).core.word = current.core.word := rfl

theorem State.refine_box
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) (numerical : WindingOneState p ambient)
    (refines : numerical.box.Refines current.core.numerical.box) :
    (current.refine numerical refines).core.numerical.box.Refines
      current.core.numerical.box :=
  refines

/-- Current rational active sample, obtained by asking the provider for the
displayed box itself. -/
def State.currentSample
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) :
    ActiveBoxSample state.core.word state.core.numerical.box :=
  state.samples.sample state.core.numerical
    (RatBox.refines_refl state.core.numerical.box)

/-- In the initial history-free fragment, install any raw-cylinder diameter
certificate directly on the active state.  This covers the long initial-low
branch, whose affine cylinder contracts around zero while its formal parser
truncation remains `ω`. -/
def State.rawCouplingOfHistoryEqNil
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient)
    (cylinder : CCLRawCylinderEnvelope.RawCylinderEnvelope)
    (cylinderWord : cylinder.truncation.word = state.core.word)
    (history : (RawParser.parse state.core.word).history = []) :
    CCLRawCylinderEnvelope.BoxCylinderCoupling where
  box := state.core.numerical.box
  cylinder := cylinder
  witness := state.currentSample.point
  witnessInside := state.currentSample.inside
  witnessRepresented := by
    rw [cylinderWord]
    exact state.currentSample.represented_of_history_eq_nil history

/-- Raw-cylinder coupling during a nonempty initial-low unary run. -/
def State.initialLowUnaryCoupling
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (count : ℕ)
    (phase : (RawParser.parse state.core.word).phase =
      .lowUnary (count + 1)) :
    CCLRawCylinderEnvelope.BoxCylinderCoupling :=
  state.rawCouplingOfHistoryEqNil
    (CCLHomographicCylinder.lowUnaryEnvelopeOfPhase state.core.word count
      phase) rfl
    (RawParser.parse_history_eq_nil_of_lowUnary phase)

/-- The active sample likewise couples the partial initial-low sector
cylinder before the first decoder matrix update. -/
def State.initialLowSectorCoupling
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (exponent : ℕ)
    (bits : RawParser.SectorBits)
    (phase : (RawParser.parse state.core.word).phase =
      .sector .initialLow exponent bits) :
    CCLRawCylinderEnvelope.BoxCylinderCoupling :=
  state.rawCouplingOfHistoryEqNil
    (CCLHomographicCylinder.initialLowSectorEnvelopeOfPhase
      state.core.word exponent bits phase) rfl
    (RawParser.parse_history_eq_nil_of_initialLow_sector phase)

/-- Once the initial-low unary counter reaches its computable target, the
independent box and raw-cylinder errors have the requested summed bound. -/
theorem State.initialLowUnaryCoupling_errorSq_le
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (count : ℕ)
    (phase : (RawParser.parse state.core.word).phase =
      .lowUnary (count + 1))
    {epsilon boxError : ℚ} (epsilonPositive : 0 < epsilon)
    (reached : CCLHomographicCylinder.initialLowContractionDepth epsilon ≤
      count + 1)
    (boxBound : state.core.numerical.box.diagonalSq ≤ boxError) :
    (state.initialLowUnaryCoupling count phase).errorSq ≤
      2 * (boxError + epsilon) := by
  have depthLe : CCLUnaryCylinder.binaryDepth epsilon ≤ count := by
    simp only [CCLHomographicCylinder.initialLowContractionDepth] at reached
    omega
  have cylinderBound : CCLUnaryCylinder.lowRadiusSq count ≤ epsilon :=
    (CCLUnaryCylinder.lowRadiusSq_le_of_le depthLe).trans
    (CCLUnaryCylinder.lowRadiusSq_binaryDepth_le epsilonPositive)
  change 2 * (state.core.numerical.box.diagonalSq +
    CCLUnaryCylinder.lowRadiusSq count) ≤ 2 * (boxError + epsilon)
  linarith

/-- The same componentwise bound after the initial-low delimiter and through
its partial sector code. -/
theorem State.initialLowSectorCoupling_errorSq_le
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (exponent : ℕ)
    (bits : RawParser.SectorBits)
    (phase : (RawParser.parse state.core.word).phase =
      .sector .initialLow exponent bits)
    {epsilon boxError : ℚ} (epsilonPositive : 0 < epsilon)
    (reached : CCLHomographicCylinder.initialLowContractionDepth epsilon ≤
      exponent)
    (boxBound : state.core.numerical.box.diagonalSq ≤ boxError) :
    (state.initialLowSectorCoupling exponent bits phase).errorSq ≤
      2 * (boxError + epsilon) := by
  have cylinderBound :
      CCLHomographicCylinder.initialLowSectorRadiusSq exponent ≤ epsilon :=
    (CCLHomographicCylinder.initialLowSectorRadiusSq_le_of_le reached).trans
      (CCLHomographicCylinder.initialLowSectorRadiusSq_contractionDepth_le
        epsilonPositive)
  change 2 * (state.core.numerical.box.diagonalSq +
    CCLHomographicCylinder.initialLowSectorRadiusSq exponent) ≤
      2 * (boxError + epsilon)
  linarith

/-- Install any phase-local large-tail certificate as the current coupled
box--truncation envelope. -/
def State.envelope
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (bound : ActiveTailLowerBound state.core.word) :
    CoupledEnvelope :=
  state.currentSample.coupledEnvelope bound

/-- Total current envelope: use the sharper active radial estimate when its
finite positivity test succeeds and otherwise retain the universal unit
reference error. -/
def State.bestEnvelope
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) : CoupledEnvelope where
  box := state.core.numerical.box
  certificate := state.currentSample.bestReferenceError
  referenceInside := by
    unfold ActiveBoxSample.bestReferenceError
    split <;> exact state.currentSample.inside

/-- Rational coupling inequality exposed directly by an active metric state. -/
theorem State.box_point_le_radiusSq
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (bound : ActiveTailLowerBound state.core.word)
    {point : QI} (inside : state.core.numerical.box.Contains point) :
    chordalSq (Proj.affine point)
        (⟨state.core.word⟩ : TaggedTruncation).point ≤
      (state.envelope bound).radiusSq :=
  state.currentSample.box_point_le_radiusSq bound inside

/-- Active computed-depth envelope for a requested rational cylinder error. -/
def State.computedDepthEnvelope
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (lower : ∀ {tail : QI},
      RawParser.activeHolds (RawParser.parse state.core.word).phase tail →
        (2 : ℚ) ^ FTA.CCLHomographicCylinder.decoderUnaryDepth
          (RawParser.parse state.core.word).matrix epsilon ≤ normSq tail) :
    CoupledEnvelope :=
  state.envelope (computedDepthActiveTailLowerBound state.core.word epsilon
    epsilonPositive lower)

/-- Independent box and active-cylinder bounds add through the exact rational
coupling inequality. -/
theorem State.computedDepthEnvelope_radiusSq_le
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) {epsilon boxError : ℚ}
    (epsilonPositive : 0 < epsilon)
    (lower : ∀ {tail : QI},
      RawParser.activeHolds (RawParser.parse state.core.word).phase tail →
        (2 : ℚ) ^ FTA.CCLHomographicCylinder.decoderUnaryDepth
          (RawParser.parse state.core.word).matrix epsilon ≤ normSq tail)
    (boxBound : state.core.numerical.box.diagonalSq ≤ boxError) :
    (state.computedDepthEnvelope epsilon epsilonPositive lower).radiusSq ≤
      2 * (boxError + epsilon) := by
  simpa only [State.computedDepthEnvelope, State.envelope] using
    state.currentSample.computedDepthCoupledEnvelope_radiusSq_le
      epsilonPositive lower boxBound

/-- Once the two independently computed coupled errors fall below the stored
root-region gap, the two tagged projective truncations are provably distinct. -/
theorem computedDepthEnvelopes_not_equivalent_of_error_sum_lt_gap
    {p : GaussianPolynomial} {ambient : RatBox}
    (left right : State p ambient)
    (gap : RegionGap left.core.numerical.box right.core.numerical.box)
    {leftError rightError : ℚ}
    (leftErrorPositive : 0 < leftError)
    (rightErrorPositive : 0 < rightError)
    (leftLower : ∀ {tail : QI},
      RawParser.activeHolds (RawParser.parse left.core.word).phase tail →
        (2 : ℚ) ^ FTA.CCLHomographicCylinder.decoderUnaryDepth
          (RawParser.parse left.core.word).matrix leftError ≤ normSq tail)
    (rightLower : ∀ {tail : QI},
      RawParser.activeHolds (RawParser.parse right.core.word).phase tail →
        (2 : ℚ) ^ FTA.CCLHomographicCylinder.decoderUnaryDepth
          (RawParser.parse right.core.word).matrix rightError ≤ normSq tail)
    (thin : 4 *
      ((left.computedDepthEnvelope leftError leftErrorPositive
          leftLower).radiusSq +
        (right.computedDepthEnvelope rightError rightErrorPositive
          rightLower).radiusSq) <
      chordalGapSq left.core.numerical.box right.core.numerical.box
        gap.coordinateGap) :
    ¬((left.computedDepthEnvelope leftError leftErrorPositive
        leftLower).certificate.truncation.point).Equivalent
      ((right.computedDepthEnvelope rightError rightErrorPositive
        rightLower).certificate.truncation.point) := by
  exact truncations_not_equivalent_of_error_sum_lt_gap gap.positive
    gap.separated rfl rfl thin

/-- Fully componentwise form of the separation criterion: the two box errors
and two active cylinder errors are compared directly with the precomputed
region gap. -/
theorem computedDepthEnvelopes_not_equivalent_of_component_error_lt_gap
    {p : GaussianPolynomial} {ambient : RatBox}
    (left right : State p ambient)
    (gap : RegionGap left.core.numerical.box right.core.numerical.box)
    {leftCylinder rightCylinder leftBoxError rightBoxError : ℚ}
    (leftCylinderPositive : 0 < leftCylinder)
    (rightCylinderPositive : 0 < rightCylinder)
    (leftLower : ∀ {tail : QI},
      RawParser.activeHolds (RawParser.parse left.core.word).phase tail →
        (2 : ℚ) ^ FTA.CCLHomographicCylinder.decoderUnaryDepth
          (RawParser.parse left.core.word).matrix leftCylinder ≤ normSq tail)
    (rightLower : ∀ {tail : QI},
      RawParser.activeHolds (RawParser.parse right.core.word).phase tail →
        (2 : ℚ) ^ FTA.CCLHomographicCylinder.decoderUnaryDepth
          (RawParser.parse right.core.word).matrix rightCylinder ≤ normSq tail)
    (leftBoxBound :
      left.core.numerical.box.diagonalSq ≤ leftBoxError)
    (rightBoxBound :
      right.core.numerical.box.diagonalSq ≤ rightBoxError)
    (thin : 8 * ((leftBoxError + leftCylinder) +
      (rightBoxError + rightCylinder)) <
        chordalGapSq left.core.numerical.box right.core.numerical.box
          gap.coordinateGap) :
    ¬((left.computedDepthEnvelope leftCylinder leftCylinderPositive
        leftLower).certificate.truncation.point).Equivalent
      ((right.computedDepthEnvelope rightCylinder rightCylinderPositive
        rightLower).certificate.truncation.point) := by
  have leftRadius := left.computedDepthEnvelope_radiusSq_le
    leftCylinderPositive leftLower leftBoxBound
  have rightRadius := right.computedDepthEnvelope_radiusSq_le
    rightCylinderPositive rightLower rightBoxBound
  apply computedDepthEnvelopes_not_equivalent_of_error_sum_lt_gap left right
    gap leftCylinderPositive rightCylinderPositive leftLower rightLower
  linarith

/-- Initial denominator separation seeds the empty raw word. -/
def ofInitialSeparation
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : WindingOneState p ambient}
    (separation : CCLDenominator.SeparationOutput p ambient current
      (adjugate (RawParser.parse []).matrix)) : State p ambient where
  core :=
    { numerical := separation.state
      word := [] }
  samples := initialPersistentActiveSamples separation
  observations := PersistentObservationChain.nil RawParser.identityMatrix
    separation.state
  completedSector := .canonical (by
    intro completed
    simp [RawParser.parse, RawParser.initialState] at completed)

/-- Restrict the completed-block providers across an ordinary raw bit. -/
def persistentObservationsOfNoncompletedStep
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines current.core.numerical.box)
    (bit : Bool)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent (.two first second)) :
    PersistentObservationChain RawParser.identityMatrix
      (parserBlocks (current.core.word ++ [bit])) next :=
  (current.observations.refine nextRefines).castBlocks
    (parserBlocks_append_singleton_eq_of_not_completed current.core.word bit
      notCompleted).symm

/-- Persist an arbitrary raw step.  Ordinary bits only restrict the existing
providers; a third sector bit appends the newly supplied block observation. -/
def persistentObservationsOfStep
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient)
    (next : WindingOneState p ambient)
    (nextRefines : next.box.Refines current.core.numerical.box)
    (bit : Bool)
    (completedProvider :
      ∀ (kind : RawParser.BlockKind) (exponent : ℕ) (first second : Bool),
        (RawParser.parse current.core.word).phase =
          .sector kind exponent (.two first second) →
        (later : WindingOneState p ambient) →
        later.box.Refines next.box →
          BlockObservationSample
            (DecoderBlock.matrixProduct RawParser.identityMatrix
              (parserBlocks current.core.word))
            ⟨kind, exponent, RawParser.sectorOfBits first second bit⟩
            later.box) :
    PersistentObservationChain RawParser.identityMatrix
      (parserBlocks (current.core.word ++ [bit])) next := by
  cases phase : (RawParser.parse current.core.word).phase with
  | initial =>
      exact persistentObservationsOfNoncompletedStep current next nextRefines
        bit (by
          rintro ⟨_, _, _, _, equality⟩
          rw [phase] at equality
          cases equality)
  | highUnary count =>
      exact persistentObservationsOfNoncompletedStep current next nextRefines
        bit (by
          rintro ⟨_, _, _, _, equality⟩
          rw [phase] at equality
          cases equality)
  | lowUnary count =>
      exact persistentObservationsOfNoncompletedStep current next nextRefines
        bit (by
          rintro ⟨_, _, _, _, equality⟩
          rw [phase] at equality
          cases equality)
  | loopUnary count =>
      exact persistentObservationsOfNoncompletedStep current next nextRefines
        bit (by
          rintro ⟨_, _, _, _, equality⟩
          rw [phase] at equality
          cases equality)
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          exact persistentObservationsOfNoncompletedStep current next
            nextRefines bit (by
              intro completed
              rcases completed with ⟨_, _, _, _, equality⟩
              rw [phase] at equality
              cases equality)
      | one first =>
          exact persistentObservationsOfNoncompletedStep current next
            nextRefines bit (by
              intro completed
              rcases completed with ⟨_, _, _, _, equality⟩
              rw [phase] at equality
              cases equality)
      | two first second =>
          let appended :=
            (current.observations.refine nextRefines).appendSingleton
              (completedProvider kind exponent first second phase)
          exact appended.castBlocks
            (parserBlocks_append_completedSector current.core.word bit
              phase).symm

/-- Complete a positive parsed event and immediately apply denominator
separation for the appended parser.  The resulting state has a fresh active
sample provider in every later refinement, with no dependency on the old
provider or retained parser history. -/
def nextOfParsedEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR)
      (selectedEventStatePayload selected.toIncrementalPayload squarefree
        elimination)
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        selected.toIncrementalPayload.bit).matrix)) :
    State p (RatBox.symmetric R hR) := by
  have eventRefines :
      (selectedEventStatePayload selected.toIncrementalPayload squarefree
        elimination).box.Refines output.state.box :=
    (selectedEventStatePayload_strictInterior selected.toIncrementalPayload
      squarefree elimination).refines
  have refinesOld : successorSeparation.state.box.Refines output.state.box :=
    successorSeparation.refines.trans eventRefines
  have refinesCurrent : successorSeparation.state.box.Refines
      current.core.numerical.box :=
    refinesOld.trans output.refines
  exact
    { core :=
        { numerical := successorSeparation.state
          word := current.core.word ++
            [selected.toIncrementalPayload.bit] }
      samples := persistentActiveSamplesOfParsedEvent output selected
        squarefree degreeNonzero zeroNonzero elimination successorSeparation
          refinesOld
      observations := persistentObservationsOfStep current
        successorSeparation.state refinesCurrent
        selected.toIncrementalPayload.bit (by
          intro kind exponent first second phase later laterRefines
          have laterRefinesOld : later.box.Refines output.state.box :=
            laterRefines.trans refinesOld
          let data := parsedStaticData output selected squarefree degreeNonzero
            zeroNonzero elimination later laterRefinesOld
          have inside : later.box.Contains (Data.point data) :=
            Data.point_inside data
          have parserEq : RawParser.parse current.core.word =
              ⟨.sector kind exponent (.two first second),
                (RawParser.parse current.core.word).matrix,
                (RawParser.parse current.core.word).history⟩ := by
            cases parsed : RawParser.parse current.core.word with
            | mk parserPhase matrix history =>
                have phase' : parserPhase =
                    .sector kind exponent (.two first second) := by
                  simpa only [parsed] using phase
                subst parserPhase
                rfl
          have incremental :
              (inputIncrementalAdvanceFormula
                ⟨.sector kind exponent (.two first second),
                  (RawParser.parse current.core.word).matrix,
                  (RawParser.parse current.core.word).history⟩
                selected.toIncrementalPayload.bit).Holds
                  (Data.point data) := by
            rw [← parserEq]
            exact Data.incremental_holds data
          have oldDenominator := separation_denominator_ne output
            (laterRefinesOld.contains inside)
          have newDenominator := separation_denominator_ne successorSeparation
            (laterRefines.contains inside)
          rw [DecoderBlock.matrixProduct_parserBlocks current.core.word]
          apply BlockObservationSample.ofCompletedIncremental
            (RawParser.parse current.core.word).matrix
            (RawParser.parse current.core.word).history kind exponent first
              second selected.toIncrementalPayload.bit later.box
                (Data.point data) inside
          · simpa only [determinant, Mat2.det] using
              RawParser.parse_det_ne current.core.word
          · exact oldDenominator
          · rw [RawParserSemantics.step_eq_completeSector
                (RawParser.parse current.core.word) kind exponent first second
                  selected.toIncrementalPayload.bit phase] at newDenominator
            simpa only [RawParser.completeSector] using newDenominator
          · exact incremental)
      completedSector := .canonical (by
        intro completed
        exact ActiveControllerCanonicalOnInputEvents.refine
          ((CompletedSectorActiveControllerCanonicalData.ofSelectedPayload
            current.core.numerical current.core.word output selected squarefree
              degreeNonzero elimination) completed) refinesOld) }

theorem nextOfParsedEvent_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR)
      (selectedEventStatePayload selected.toIncrementalPayload squarefree
        elimination)
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        selected.toIncrementalPayload.bit).matrix)) :
    (nextOfParsedEvent current output selected squarefree degreeNonzero
      zeroNonzero elimination successorSeparation).core.numerical.box.Refines
        current.core.numerical.box := by
  exact successorSeparation.refines.trans
    ((selectedEventStatePayload_strictInterior selected.toIncrementalPayload
      squarefree elimination).refines.trans output.refines)

/-- Outside a completed source sector, an incremental x--y owner produces the
same active successor as a complete owner.  Active canonical truth propagates
through the selected event even when the appended parser is waiting for its
third sector bit. -/
def nextOfParsedIncrementalEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload output)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR)
      (selectedEventStatePayload selected squarefree elimination)
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        selected.bit).matrix)) : State p (RatBox.symmetric R hR) := by
  have eventRefines :
      (selectedEventStatePayload selected squarefree elimination).box.Refines
        output.state.box :=
    (selectedEventStatePayload_strictInterior selected squarefree
      elimination).refines
  have refinesOld : successorSeparation.state.box.Refines output.state.box :=
    successorSeparation.refines.trans eventRefines
  have refinesCurrent : successorSeparation.state.box.Refines
      current.core.numerical.box :=
    refinesOld.trans output.refines
  exact
    { core :=
        { numerical := successorSeparation.state
          word := current.core.word ++ [selected.bit] }
      samples := persistentActiveSamplesOfParsedIncrementalEvent output
        selected notCompleted squarefree degreeNonzero zeroNonzero elimination
          successorSeparation refinesOld
      observations := persistentObservationsOfNoncompletedStep current
        successorSeparation.state refinesCurrent selected.bit notCompleted
      completedSector := .canonical (by
        intro completed
        exact ActiveControllerCanonicalOnInputEvents.refine
          ((CompletedSectorActiveControllerCanonicalData.ofSelectedIncremental
            current.core.numerical current.core.word output selected
              notCompleted squarefree degreeNonzero elimination) completed)
          refinesOld) }

theorem nextOfParsedIncrementalEvent_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload output)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR)
      (selectedEventStatePayload selected squarefree elimination)
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        selected.bit).matrix)) :
    (nextOfParsedIncrementalEvent current output selected notCompleted
      squarefree degreeNonzero zeroNonzero elimination
        successorSeparation).core.numerical.box.Refines
          current.core.numerical.box := by
  exact successorSeparation.refines.trans
    ((selectedEventStatePayload_strictInterior selected squarefree
      elimination).refines.trans output.refines)

/-- Complete an all-clear planned bit and immediately separate the appended
decoder denominator.  The old active provider is restricted to each later
box and transported through the strict-cell decision. -/
def nextOfPlannedBit
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (planned : CCLDirectTrack.PlannedBit current.core)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR)
      planned.numerical
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        planned.decision.bit).matrix)) :
    State p (RatBox.symmetric R hR) := by
  have refinesCurrent : successorSeparation.state.box.Refines
      current.core.numerical.box :=
    successorSeparation.refines.trans planned.refines
  exact
    { core :=
        { numerical := successorSeparation.state
          word := current.core.word ++ [planned.decision.bit] }
      samples := persistentActiveSamplesOfPlannedBit current.samples planned
        successorSeparation successorSeparation.refines
      observations := persistentObservationsOfStep current
        successorSeparation.state refinesCurrent planned.decision.bit (by
          intro kind exponent first second phase later laterRefines
          have laterRefinesPlanned : later.box.Refines planned.numerical.box :=
            laterRefines.trans successorSeparation.refines
          let oldSample := current.samples.sample later
            (laterRefinesPlanned.trans planned.refines)
          have insidePlanned :
              planned.numerical.box.Contains oldSample.point :=
            laterRefinesPlanned.contains oldSample.inside
          have localHolds :=
            inputIncremental_holds_localBit_of_active_notTerminal
              (RawParser.parse current.core.word) oldSample.point
              oldSample.inverseDenominator oldSample.active
              (planned.notTerminal insidePlanned)
          have localBitEq :
              inputLocalBit (RawParser.parse current.core.word)
                  oldSample.point =
                inputLocalBit (RawParser.parse current.core.word)
                  planned.numerical.box.center := by
            apply inputLocalBit_eq_of_inputForms_sameSigns
              (RawParser.parse current.core.word) oldSample.point
                planned.numerical.box.center oldSample.inverseDenominator
                  (planned.inverseDenominator
                    planned.numerical.box.contains_center)
            intro form member
            rw [inputForms] at member
            rcases List.mem_map.mp member with ⟨source, sourceMember, rfl⟩
            have same := eval_center_mul_pos_of_strictSignCheck source.form
              (planned.strictSigns source sourceMember) insidePlanned
            simpa only [_root_.mul_comm] using same
          have pointBit :
              inputLocalBit (RawParser.parse current.core.word)
                  oldSample.point = planned.decision.bit :=
            localBitEq.trans planned.decisionBit.symm
          rw [pointBit] at localHolds
          have parserEq : RawParser.parse current.core.word =
              ⟨.sector kind exponent (.two first second),
                (RawParser.parse current.core.word).matrix,
                (RawParser.parse current.core.word).history⟩ := by
            cases parsed : RawParser.parse current.core.word with
            | mk parserPhase matrix history =>
                have phase' : parserPhase =
                    .sector kind exponent (.two first second) := by
                  simpa only [parsed] using phase
                subst parserPhase
                rfl
          have incremental :
              (inputIncrementalAdvanceFormula
                ⟨.sector kind exponent (.two first second),
                  (RawParser.parse current.core.word).matrix,
                  (RawParser.parse current.core.word).history⟩
                planned.decision.bit).Holds oldSample.point := by
            rw [← parserEq]
            exact localHolds
          have newDenominator := separation_denominator_ne successorSeparation
            (laterRefines.contains oldSample.inside)
          rw [DecoderBlock.matrixProduct_parserBlocks current.core.word]
          apply BlockObservationSample.ofCompletedIncremental
            (RawParser.parse current.core.word).matrix
            (RawParser.parse current.core.word).history kind exponent first
              second planned.decision.bit later.box oldSample.point
                oldSample.inside
          · simpa only [determinant, Mat2.det] using
              RawParser.parse_det_ne current.core.word
          · exact oldSample.inverseDenominator
          · rw [RawParserSemantics.step_eq_completeSector
                (RawParser.parse current.core.word) kind exponent first second
                  planned.decision.bit phase] at newDenominator
            simpa only [RawParser.completeSector] using newDenominator
          · exact incremental)
      completedSector := .canonical (by
        intro completed
        exact ActiveControllerCanonicalOnInputEvents.refine
          ((plannedBit_completedSectorActiveControllerCanonicalData planned
            squarefree degreeNonzero elimination) completed)
          successorSeparation.refines) }

theorem nextOfPlannedBit_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (planned : CCLDirectTrack.PlannedBit current.core)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D)
    (successorSeparation : CCLDenominator.SeparationOutput p
      (RatBox.symmetric R hR)
      planned.numerical
      (adjugate (RawParser.step (RawParser.parse current.core.word)
        planned.decision.bit).matrix)) :
    (nextOfPlannedBit current planned squarefree degreeNonzero elimination
      successorSeparation).core.numerical.box.Refines
        current.core.numerical.box :=
  successorSeparation.refines.trans planned.refines

/-- One repeatable active metric transition.  Nonterminal results have already
run denominator separation for the appended parser and therefore satisfy the
state invariant needed by the next controller call. -/
inductive StepResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : State p ambient) where
  | zero (root : p.eval 0 = 0) : StepResult current
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = CCL.RationalEncoder.encode point nonzero)
      (contains : current.core.numerical.box.Contains point) :
      StepResult current
  | next (bit : Bool) (state : State p ambient)
      (refines : state.core.numerical.box.Refines
        current.core.numerical.box)
      (word_eq : state.core.word = current.core.word ++ [bit]) :
      StepResult current

/-- Resolve a complete x--y selected event and close the successor's decoder
pole before returning.  The positive branch installs the history-free event
provider; the zero polynomial event returns its exact rational root. -/
def resolveParsedEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : SelectedEventPayload output)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StepResult current :=
  match selected.decision with
  | .identicallyZero realZero imagZero => by
      let exactRoot :=
        FTA.CCLEventTerminal.InputEventCell.identicallyZeroLocalizedRoot
          selected.candidate.inputCell output.state.clearance realZero imagZero
      if zero : exactRoot.point = 0 then
        exact .zero (by simpa only [zero] using exactRoot.root)
      else
        exact .terminal exactRoot.point exactRoot.root zero
          (CCL.RationalEncoder.encode exactRoot.point zero) rfl
          (output.refines.contains exactRoot.contains)
  | .positive _evidence => by
      let direct := selected.toIncrementalPayload
      let numerical := selectedEventStatePayload direct squarefree elimination
      let parser := RawParser.step (RawParser.parse current.core.word) direct.bit
      have parserDeterminant : determinant parser.matrix ≠ 0 := by
        simpa only [parser, determinant, Mat2.det] using
          RawParser.step_det_ne (RawParser.parse current.core.word) direct.bit
            (RawParser.parse_det_ne current.core.word)
      exact match CCLDenominator.decide track numerical (adjugate parser.matrix)
          (CCLBranchEvidence.adjugate_lowerRow_ne parser.matrix
            parserDeterminant) with
      | CCLDenominator.Decision.terminal point root contains _ _ => by
          if zero : point = 0 then
            exact .zero (by simpa only [zero] using root)
          else
            exact .terminal point root zero
              (CCL.RationalEncoder.encode point zero) rfl
              (output.refines.contains
                ((selectedEventStatePayload_strictInterior
                  selected.toIncrementalPayload squarefree elimination).refines.contains
                    contains))
      | CCLDenominator.Decision.separated successorSeparation =>
          let next := nextOfParsedEvent current output selected squarefree
            degreeNonzero zeroNonzero elimination successorSeparation
          .next direct.bit next
            (nextOfParsedEvent_refines current output selected squarefree
              degreeNonzero zeroNonzero elimination successorSeparation)
            rfl

/-- Resolve a selected history-free owner outside a completed source phase.
Its tangent grid establishes the new active predicate, including when the bit
enters a completed sector, and denominator separation makes the result
immediately repeatable. -/
def resolveParsedIncrementalEvent
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : State p (RatBox.symmetric R hR))
    (output : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
      current.core.numerical
      (adjugate (RawParser.parse current.core.word).matrix))
    (selected : IncrementalEventPayload output)
    (notCompleted : ¬∃ kind exponent first second,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent (.two first second))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StepResult current :=
  match selected.decision with
  | .identicallyZero realZero imagZero => by
      let exactRoot :=
        FTA.CCLEventTerminal.InputEventCell.identicallyZeroLocalizedRoot
          selected.candidate.inputCell output.state.clearance realZero imagZero
      if zero : exactRoot.point = 0 then
        exact .zero (by simpa only [zero] using exactRoot.root)
      else
        exact .terminal exactRoot.point exactRoot.root zero
          (CCL.RationalEncoder.encode exactRoot.point zero) rfl
          (output.refines.contains exactRoot.contains)
  | .positive _evidence => by
      let numerical := selectedEventStatePayload selected squarefree
        elimination
      let parser := RawParser.step (RawParser.parse current.core.word)
        selected.bit
      have parserDeterminant : determinant parser.matrix ≠ 0 := by
        simpa only [parser, determinant, Mat2.det] using
          RawParser.step_det_ne (RawParser.parse current.core.word)
            selected.bit (RawParser.parse_det_ne current.core.word)
      exact match CCLDenominator.decide track numerical
          (adjugate parser.matrix)
          (CCLBranchEvidence.adjugate_lowerRow_ne parser.matrix
            parserDeterminant) with
      | CCLDenominator.Decision.terminal point root contains _ _ => by
          if zero : point = 0 then
            exact .zero (by simpa only [zero] using root)
          else
            exact .terminal point root zero
              (CCL.RationalEncoder.encode point zero) rfl
              (output.refines.contains
                ((selectedEventStatePayload_strictInterior selected squarefree
                  elimination).refines.contains contains))
      | CCLDenominator.Decision.separated successorSeparation =>
          let next := nextOfParsedIncrementalEvent current output selected
            notCompleted squarefree degreeNonzero
              zeroNonzero elimination successorSeparation
          .next selected.bit next
            (nextOfParsedIncrementalEvent_refines current output selected
              notCompleted squarefree degreeNonzero
                zeroNonzero elimination successorSeparation)
            rfl

/-- Resolve an all-clear strict-cell bit and close the successor denominator
before returning the next active metric state. -/
def resolvePlannedBit
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : State p (RatBox.symmetric R hR))
    (planned : CCLDirectTrack.PlannedBit current.core)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StepResult current := by
  let parser := RawParser.step (RawParser.parse current.core.word)
    planned.decision.bit
  have parserDeterminant : determinant parser.matrix ≠ 0 := by
    simpa only [parser, determinant, Mat2.det] using
      RawParser.step_det_ne (RawParser.parse current.core.word)
        planned.decision.bit (RawParser.parse_det_ne current.core.word)
  exact match CCLDenominator.decide track planned.numerical
      (adjugate parser.matrix)
      (CCLBranchEvidence.adjugate_lowerRow_ne parser.matrix
        parserDeterminant) with
  | CCLDenominator.Decision.terminal point root contains _ _ => by
      if zero : point = 0 then
        exact .zero (by simpa only [zero] using root)
      else
        exact .terminal point root zero
          (CCL.RationalEncoder.encode point zero) rfl
          (planned.refines.contains contains)
  | CCLDenominator.Decision.separated successorSeparation =>
      let next := nextOfPlannedBit current planned squarefree degreeNonzero
        elimination successorSeparation
      .next planned.decision.bit next
        (nextOfPlannedBit_refines current planned squarefree degreeNonzero
          elimination successorSeparation) rfl

/-- Active controller opening after direct event owners have already been
resolved.  The two retained constructors are precisely the ordinary and
terminal-guard all-clear pipeline; no event branch loses its selected payload. -/
inductive Opening
    (p : GaussianPolynomial) (ambient : RatBox)
    (current : State p ambient) where
  | ready (result : StepResult current) : Opening p ambient current
  | noEventOwner
      (separation : CCLDenominator.SeparationOutput p ambient
        current.core.numerical
        (adjugate (RawParser.parse current.core.word).matrix))
      (none : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.core.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.core.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (noIdenticallyZero :
        CCLCoupledController.firstLocalizedIdenticallyZeroRoot?
        (RawParser.parse current.core.word) separation = Option.none)
      (arcs : List (BoundaryArc p)) (evidence : AllClear p arcs)
      (alignment : ClearFamilyAlignment p separation.state.box
        (separatedRelevantClearCells p (RawParser.parse current.core.word)
          separation) arcs)
      (guardCurve : GuardCurveFamilyDecision p separation.state.box
        (separatedEventGuardCells p (RawParser.parse current.core.word)
          separation))
      (terminal : CCLTerminalSeparation.SeparationOutput p ambient
        (RawParser.parse current.core.word) separation.state [false, true])
      (output : RefinementOutput p ambient terminal.numerical evidence) :
      Opening p ambient current

  | guardClear
      (separation : CCLDenominator.SeparationOutput p ambient
        current.core.numerical
        (adjugate (RawParser.parse current.core.word).matrix))
      (none : ∀ candidate ∈ separatedInputEventCells p
        (RawParser.parse current.core.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
        (RawParser.parse current.core.word) separation,
        candidate.inputCell.ownerChecks = (false, false))
      (noIdenticallyZero :
        CCLCoupledController.firstLocalizedIdenticallyZeroRoot?
        (RawParser.parse current.core.word) separation = Option.none)
      (arcs : List (BoundaryArc p)) (evidence : AllClear p arcs)
      (alignment : ClearFamilyAlignment p separation.state.box
        (separatedRelevantClearCells p (RawParser.parse current.core.word)
          separation) arcs)
      (terminal : CCLTerminalSeparation.SeparationOutput p ambient
        (RawParser.parse current.core.word) separation.state [false, true])
      (output : RefinementOutput p ambient terminal.numerical evidence)
      (guardEvidence : AllGuardClear p separation.state.box
        (separatedEventGuardCells p (RawParser.parse current.core.word)
          separation))
      (guardOutput : GuardRefinementOutput p ambient output.state
        guardEvidence) : Opening p ambient current

/-- The exact-boundary residue after every ordinary controller alternative
has been executed.  It retains the positive guard's algebraic path together
with the complete history-free incremental table, but no represented-prefix
sample or historical formula witness. -/
structure ActivePositiveGuardData
    (p : GaussianPolynomial) (R : ℚ) (hR : 0 ≤ R)
    (current : State p (RatBox.symmetric R hR)) where
  separation : CCLDenominator.SeparationOutput p (RatBox.symmetric R hR)
    current.core.numerical
    (adjugate (RawParser.parse current.core.word).matrix)
  globalNone : ∀ candidate ∈ separatedInputEventCells p
    (RawParser.parse current.core.word) separation,
    candidate.inputCell.ownerChecks = (false, false)
  guardNone : ∀ candidate ∈ separatedGuardInputEventCells p
    (RawParser.parse current.core.word) separation,
    candidate.inputCell.ownerChecks = (false, false)
  noIdenticallyZero : CCLCoupledController.firstLocalizedIdenticallyZeroRoot?
    (RawParser.parse current.core.word) separation = Option.none
  arcs : List (BoundaryArc p)
  evidence : AllClear p arcs
  alignment : ClearFamilyAlignment p separation.state.box
    (separatedRelevantClearCells p (RawParser.parse current.core.word)
      separation) arcs
  terminal : CCLTerminalSeparation.SeparationOutput p
    (RatBox.symmetric R hR) (RawParser.parse current.core.word)
      separation.state [false, true]
  output : RefinementOutput p (RatBox.symmetric R hR) terminal.numerical
    evidence
  sourceCell : SourceEventGuardCell p separation.state.box
  member : sourceCell ∈ separatedEventGuardCells p
    (RawParser.parse current.core.word) separation
  clearedNonzero :
    (FTA.ProjectivePath.clearedReal p
      sourceCell.partition.entry.chart.path).isZero = false ∨
    (FTA.ProjectivePath.clearedImag p
      sourceCell.partition.entry.chart.path).isZero = false
  countPositive : 0 < FTA.ProjectivePath.commonFactorRootCount2 p
    sourceCell.partition.entry.chart.path clearedNonzero
    sourceCell.item.cell.cell.interval.lower
    sourceCell.item.cell.cell.interval.upper
  event : RelevantCurveEvent p
    sourceCell.partition.entry.chart.path separation.state.box
  eventMember : event ∈
    CCLBranchEvent.EventGuardCell.relevantCurveEvents sourceCell.item.cell
  incremental : CCLIncrementalEventOwner.CombinedDecision separation

/-- A total active front-end call either returns an ordinary executable bit
step/root or isolates a genuine exact-boundary stratum for the constructive
geometric resolver. -/
inductive StepOrBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR)) where
  | ready (result : StepResult current) : StepOrBoundary current
  | boundary (data : ActivePositiveGuardData p R hR current) :
      StepOrBoundary current

/-- Run denominator separation and both x--y event families.  Positive events
are resolved immediately to an active metric successor, so their algebraic
bit provenance remains available to the history-free tangent grid. -/
def openStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (current : State p (RatBox.symmetric R hR))
    (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    Opening p (RatBox.symmetric R hR) current :=
  match analyzeBranchFamilies track current.core.numerical
      (RawParser.parse current.core.word) (by
        simpa only [determinant, Mat2.det] using
          RawParser.parse_det_ne current.core.word) clearOwnerLabel with
  | .terminalPole point root contains _strict _denominatorZero => by
      if zero : point = 0 then
        exact .ready (.zero (by simpa only [zero] using root))
      else
        exact .ready (.terminal point root zero
          (CCL.RationalEncoder.encode point zero) rfl contains)
  | .eventOwner output selected =>
      .ready (resolveParsedEvent track current output selected.toPayload
        squarefree degreeNonzero zeroNonzero elimination)
  | .guardEventOwner output selected =>
      .ready (resolveParsedEvent track current output selected.toPayload
        squarefree degreeNonzero zeroNonzero elimination)
  | .noEventOwner separation allNone guardNone clear =>
      match clear with
      | .terminal point contains root => by
          if zero : point = 0 then
            exact .ready (.zero (by simpa only [zero] using root))
          else
            exact .ready (.terminal point root zero
              (CCL.RationalEncoder.encode point zero) rfl
              (separation.refines.contains contains))
      | .refined arcs evidence alignment _preliminaryOutput =>
          match rootCheck : CCLCoupledController.firstLocalizedIdenticallyZeroRoot?
              (RawParser.parse current.core.word) separation with
          | some exactRoot => by
              if zero : exactRoot.point = 0 then
                exact .ready (.zero (by
                  simpa only [zero] using exactRoot.root))
              else
                exact .ready (.terminal exactRoot.point exactRoot.root zero
                  (CCL.RationalEncoder.encode exactRoot.point zero) rfl
                  (separation.refines.contains exactRoot.contains))
          | none =>
              match CCLTerminalSeparation.separate track
                  (RawParser.parse current.core.word) separation.state with
              | .terminal point root contains => by
                  if zero : point = 0 then
                    exact .ready (.zero (by simpa only [zero] using root))
                  else
                    exact .ready (.terminal point root zero
                      (CCL.RationalEncoder.encode point zero) rfl
                      (separation.refines.contains contains))
              | .separated terminal =>
                  let refined := refineForClearance track terminal.numerical
                    evidence
                  let guardCurve := decideSeparatedGuardCurveFamily
                    (RawParser.parse current.core.word) separation (by
                      simpa only [determinant, Mat2.det] using
                        RawParser.parse_det_ne current.core.word)
                  .noEventOwner separation allNone guardNone rootCheck arcs
                    evidence alignment guardCurve terminal refined

/-- Execute the terminal-guard trichotomy.  All-clear data is retained for
the strict-cell bit, exact zero guards terminate, and only a positive relevant
guard cell remains for the dedicated relevance argument. -/
def Opening.resolveGuardClearance
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : State p ambient}
    (track : WindingOneTrack p ambient)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0) :
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
          have polynomialNonzero : p.toPolynomial ≠ 0 := by
            intro polynomialZero
            apply degreeNonzero
            rw [polynomialZero]
            exact Polynomial.natDegree_zero
          have clearedNonzero :=
            CCLCoupledController.clearedCoordinatesNonzeroOfSeparatedGuardCell
              separation (by
                simpa only [determinant, Mat2.det] using
                  RawParser.parse_det_ne current.core.word)
              sourceCell member polynomialNonzero
          have impossible : False := by
            rcases clearedNonzero with realNonzero | imagNonzero
            · exact Bool.false_ne_true (realNonzero.symm.trans realZero)
            · exact Bool.false_ne_true (imagNonzero.symm.trans imagZero)
          exact impossible.elim
      | .positive sourceCell member clearedNonzero countPositive event
          eventMember =>
          .noEventOwner separation allNone guardNone noIdenticallyZero arcs
            evidence alignment
              (.positive sourceCell member clearedNonzero countPositive
                event eventMember)
            terminal output

/-- Close an all-clear guard opening through its strict planned bit and the
appended denominator separation. -/
def Opening.resolvePlannedBit
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    Opening p (RatBox.symmetric R hR) current →
      Opening p (RatBox.symmetric R hR) current
  | .ready result => .ready result
  | .noEventOwner separation allNone guardNone noIdenticallyZero arcs evidence
      alignment guardCurve terminal output =>
      .noEventOwner separation allNone guardNone noIdenticallyZero arcs evidence
        alignment guardCurve terminal output
  | .guardClear separation _allNone _guardNone _noIdenticallyZero _arcs
      evidence alignment terminal output guardEvidence _guardOutput =>
      let planned := CCLDirectTrack.plannedBitOfGuardClearPlan track
        strictRefine current.core separation terminal evidence alignment output
          guardEvidence
      .ready (CCLActiveMetricTrack.resolvePlannedBit track current planned
        squarefree degreeNonzero elimination)

/-- One active controller call through event owners, terminal cases, and the
all-clear strict child.  A positive relevant terminal guard is the only
retained constructor. -/
def openPlannedStep
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (current : State p (RatBox.symmetric R hR))
    (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    Opening p (RatBox.symmetric R hR) current :=
  ((openStep track current clearOwnerLabel squarefree degreeNonzero zeroNonzero
    elimination).resolveGuardClearance track degreeNonzero).resolvePlannedBit track
      strictRefine squarefree degreeNonzero elimination

/-- Execute every selected incremental owner outside a completed source
phase.  An all-neither table is retained as the exact-boundary stratum for the
dedicated path-side argument. -/
def ActivePositiveGuardData.resolveIncremental
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (data : ActivePositiveGuardData p R hR current)
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    (¬∃ kind exponent first second,
      (RawParser.parse current.core.word).phase =
        .sector kind exponent (.two first second)) →
    StepOrBoundary current :=
  fun notCompleted =>
  match data.incremental with
  | .globalOwner selected =>
      .ready (resolveParsedIncrementalEvent track current data.separation
        selected.toPayload notCompleted squarefree degreeNonzero
          zeroNonzero elimination)
  | .guardOwner selected =>
      .ready (resolveParsedIncrementalEvent track current data.separation
        selected.toPayload notCompleted squarefree degreeNonzero
          zeroNonzero elimination)
  | .allNeither _globalNone _guardNone => .boundary data

/-- Finish every ordinary active-controller branch.  Canonical completed
sectors exclude positive guards directly; tangent-entered completed sectors
and ordinary all-neither events retain a genuine exact-boundary stratum,
explicitly tagged and carrying its finite incremental table. -/
def Opening.finish
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    {current : State p (RatBox.symmetric R hR)}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    Opening p (RatBox.symmetric R hR) current → StepOrBoundary current
  | .ready result => .ready result
  | .guardClear separation _allNone _guardNone _noIdenticallyZero _arcs
      evidence alignment terminal output guardEvidence _guardOutput =>
      let planned := CCLDirectTrack.plannedBitOfGuardClearPlan track
        strictRefine current.core separation terminal evidence alignment output
          guardEvidence
      .ready (CCLActiveMetricTrack.resolvePlannedBit track current planned
        squarefree degreeNonzero elimination)
  | .noEventOwner separation allNone guardNone noIdenticallyZero arcs evidence
      alignment guardCurve terminal output =>
      match guardCurve with
      | .allClear guardEvidence =>
          let planned := CCLDirectTrack.plannedBitOfGuardClearPlan track
            strictRefine current.core separation terminal evidence alignment
              output guardEvidence
          .ready (CCLActiveMetricTrack.resolvePlannedBit track current planned
            squarefree degreeNonzero elimination)
      | .identicallyZero sourceCell member realZero imagZero _relevance => by
          have polynomialNonzero : p.toPolynomial ≠ 0 := by
            intro polynomialZero
            apply degreeNonzero
            rw [polynomialZero]
            exact Polynomial.natDegree_zero
          have clearedNonzero :=
            CCLCoupledController.clearedCoordinatesNonzeroOfSeparatedGuardCell
              separation (by
                simpa only [determinant, Mat2.det] using
                  RawParser.parse_det_ne current.core.word)
              sourceCell member polynomialNonzero
          have impossible : False := by
            rcases clearedNonzero with realNonzero | imagNonzero
            · exact Bool.false_ne_true (realNonzero.symm.trans realZero)
            · exact Bool.false_ne_true (imagNonzero.symm.trans imagZero)
          exact impossible.elim
      | .positive sourceCell member clearedNonzero countPositive event
          eventMember => by
          let parser := RawParser.parse current.core.word
          let incremental := CCLIncrementalEventOwner.decideCombined parser
            separation
          let data : ActivePositiveGuardData p R hR current :=
            { separation := separation
              globalNone := allNone
              guardNone := guardNone
              noIdenticallyZero := noIdenticallyZero
              arcs := arcs
              evidence := evidence
              alignment := alignment
              terminal := terminal
              output := output
              sourceCell := sourceCell
              member := member
              clearedNonzero := clearedNonzero
              countPositive := countPositive
              event := event
              eventMember := eventMember
              incremental := by
                simpa only [parser] using incremental }
          match phaseEq : parser.phase with
          | .initial =>
              exact data.resolveIncremental track squarefree degreeNonzero
                zeroNonzero elimination (by simp [parser, phaseEq])
          | .highUnary count =>
              exact data.resolveIncremental track squarefree degreeNonzero
                zeroNonzero elimination (by simp [parser, phaseEq])
          | .lowUnary count =>
              exact data.resolveIncremental track squarefree degreeNonzero
                zeroNonzero elimination (by simp [parser, phaseEq])
          | .loopUnary count =>
              exact data.resolveIncremental track squarefree degreeNonzero
                zeroNonzero elimination (by simp [parser, phaseEq])
          | .sector kind exponent .zero =>
              exact data.resolveIncremental track squarefree degreeNonzero
                zeroNonzero elimination (by simp [parser, phaseEq])
          | .sector kind exponent (.one first) =>
              exact data.resolveIncremental track squarefree degreeNonzero
                zeroNonzero elimination (by simp [parser, phaseEq])
          | .sector kind exponent (.two first second) =>
              match current.completedSector with
              | .boundary => exact .boundary data
              | .canonical valid =>
                  exact
                    (activeAllNeither_excludes_completedSector_guard_cellControllerData
                      current.core.numerical current.core.word
                      (valid ⟨kind, exponent, first, second, by
                        simpa only [parser] using phaseEq⟩)
                      separation guardNone sourceCell member event eventMember
                        squarefree degreeNonzero elimination terminal
                          output.state output.refines kind exponent first second
                            (by simpa only [parser] using phaseEq)).elim

/-- One active controller call through every open-cell event, denominator,
terminal, and strict-cell branch.  A genuine algebraic boundary stratum is
returned separately for the total geometric resolver. -/
def openStepOrBoundary
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (track : WindingOneTrack p (RatBox.symmetric R hR))
    (strictRefine : ∀ numerical epsilon positive,
      StrictInterior (track.refine numerical epsilon positive).box
        numerical.box)
    (current : State p (RatBox.symmetric R hR))
    (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    StepOrBoundary current :=
  (openStep track current clearOwnerLabel squarefree degreeNonzero zeroNonzero
    elimination).finish track strictRefine squarefree degreeNonzero
      zeroNonzero elimination

end CCLActiveMetricTrack
end FTA
