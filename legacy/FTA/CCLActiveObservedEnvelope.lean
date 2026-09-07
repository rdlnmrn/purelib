import FTA.CCLObservedChordalEnvelope
import FTA.CCLActiveMetricProgress

/-!
# Active-controller observation envelopes

This module turns the persistent block observations stored in an active metric
state into the word-tagged shrinking chordal envelope requested by the root
controller.  One ordinary winding refinement simultaneously meets the inverse-
tail stability request and the independent box-accuracy request.
-/

namespace FTA
namespace CCLActiveObservedEnvelope

open CCL
open FTA.CCLActiveMetricProgress
open FTA.CCLActiveMetricTrack
open FTA.CCLCompletedBlockContraction
open FTA.CCLObservedChordalEnvelope
open FTA.CCLPersistentBlockObservations
open FTA.LocalExtraction
open FTA.RootTrackSeparation

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- One positive rational request that is small enough both for every
inverse-tail link and for the independently shrinking winding box. -/
def jointObservationBoxRequest (word : Prefix.Word) (target : ℚ) : ℚ :=
  min (observationBoxRequest word target) target

theorem jointObservationBoxRequest_pos (word : Prefix.Word)
    {target : ℚ} (targetPositive : 0 < target) :
    0 < jointObservationBoxRequest word target := by
  rw [jointObservationBoxRequest, lt_min_iff]
  exact ⟨observationBoxRequest_pos word targetPositive, targetPositive⟩

/-- Refine only the winding box far enough to stabilize the already completed
observation history.  The CCL word and every observation provider persist. -/
def refineForObservationEnvelope
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target) :
    State p (RatBox.symmetric R hR) :=
  machine.refine current (jointObservationBoxRequest current.core.word target)
    (jointObservationBoxRequest_pos current.core.word targetPositive)

theorem refineForObservationEnvelope_refines
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target) :
    StateRefines
      (refineForObservationEnvelope machine current target targetPositive)
      current :=
  machine.refine_refines current
    (jointObservationBoxRequest current.core.word target)
    (jointObservationBoxRequest_pos current.core.word targetPositive)

theorem refineForObservationEnvelope_word
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target) :
    (refineForObservationEnvelope machine current target
      targetPositive).core.word = current.core.word :=
  rfl

theorem refineForObservationEnvelope_box_accurate
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target) :
    (refineForObservationEnvelope machine current target
      targetPositive).core.numerical.box.diagonalSq ≤ target ^ 2 := by
  have accurate := machine.refine_accurate current
    (jointObservationBoxRequest current.core.word target)
    (jointObservationBoxRequest_pos current.core.word targetPositive)
  have jointNonnegative :
      0 ≤ jointObservationBoxRequest current.core.word target :=
    (jointObservationBoxRequest_pos current.core.word targetPositive).le
  have jointLe :
      jointObservationBoxRequest current.core.word target ≤ target := by
    exact min_le_right _ _
  have squareLe :
      jointObservationBoxRequest current.core.word target ^ 2 ≤
        target ^ 2 := by
    nlinarith
  exact accurate.trans squareLe

private theorem refineForObservationEnvelope_stability
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target) :
    (refineForObservationEnvelope machine current target
      targetPositive).core.numerical.box.diagonalSq ≤
        SampleChain.stabilityRequest RawParser.identityMatrix
          (parserBlocks current.core.word) (observationLinkError target) ^ 2 := by
  have accurate := machine.refine_accurate current
    (jointObservationBoxRequest current.core.word target)
    (jointObservationBoxRequest_pos current.core.word targetPositive)
  have jointNonnegative :
      0 ≤ jointObservationBoxRequest current.core.word target :=
    (jointObservationBoxRequest_pos current.core.word targetPositive).le
  have requestPositive := observationBoxRequest_pos current.core.word
    targetPositive
  have jointLe : jointObservationBoxRequest current.core.word target ≤
      observationBoxRequest current.core.word target :=
    min_le_left _ _
  have squareLe :
      jointObservationBoxRequest current.core.word target ^ 2 ≤
        observationBoxRequest current.core.word target ^ 2 := by
    nlinarith
  exact accurate.trans (by
    simpa only [observationBoxRequest] using squareLe)

/-- Materialize the current nonempty completed history after the joint box
refinement. -/
def coupledObservationEnvelope
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target)
    (first : DecoderBlock) (remaining : List DecoderBlock)
    (blocksEq : parserBlocks current.core.word = first :: remaining) :
    CoupledObservationEnvelope :=
  CoupledObservationEnvelope.ofPersistent current.observations blocksEq
    (refineForObservationEnvelope_refines machine current target
      targetPositive).box
    (observationLinkError target) (observationLinkError_pos targetPositive)
    (by
      have stable := refineForObservationEnvelope_stability machine current
        target targetPositive
      simpa only [blocksEq] using stable)

theorem coupledObservationEnvelope_box
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target)
    (first : DecoderBlock) (remaining : List DecoderBlock)
    (blocksEq : parserBlocks current.core.word = first :: remaining) :
    (coupledObservationEnvelope machine current target targetPositive first
      remaining blocksEq).box =
      (refineForObservationEnvelope machine current target
        targetPositive).core.numerical.box :=
  rfl

theorem coupledObservationEnvelope_word
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target)
    (first : DecoderBlock) (remaining : List DecoderBlock)
    (blocksEq : parserBlocks current.core.word = first :: remaining) :
    (coupledObservationEnvelope machine current target targetPositive first
      remaining blocksEq).tag.word = current.core.word :=
  rfl

theorem coupledObservationEnvelope_cylinderRadiusSq_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target)
    (first : DecoderBlock) (remaining : List DecoderBlock)
    (blocksEq : parserBlocks current.core.word = first :: remaining)
    (enoughBlocks : observationBlockDepth target ≤
      (first :: remaining).length) :
    (coupledObservationEnvelope machine current target targetPositive first
      remaining blocksEq).cylinderRadiusSq ≤ target := by
  apply SampleChain.StableEnvelope.radiusSq_le_target
  exact targetPositive
  exact enoughBlocks

theorem coupledObservationEnvelope_radiusSq_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target)
    (first : DecoderBlock) (remaining : List DecoderBlock)
    (blocksEq : parserBlocks current.core.word = first :: remaining)
    (enoughBlocks : observationBlockDepth target ≤
      (first :: remaining).length) :
    (coupledObservationEnvelope machine current target targetPositive first
      remaining blocksEq).radiusSq ≤ 2 * (target ^ 2 + target) := by
  apply CoupledObservationEnvelope.radiusSq_le
  · rw [coupledObservationEnvelope_box]
    exact refineForObservationEnvelope_box_accurate machine current target
      targetPositive
  · exact coupledObservationEnvelope_cylinderRadiusSq_le machine current
      target targetPositive first remaining blocksEq enoughBlocks

/-- Controller-level certificate produced once the current completed history
meets the explicit observation depth. -/
structure ReachedEnvelope
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR)) (target : ℚ) where
  state : State p (RatBox.symmetric R hR)
  refines : StateRefines state current
  envelope : CoupledObservationEnvelope
  box_eq : envelope.box = state.core.numerical.box
  word_eq : envelope.tag.word = state.core.word
  boxAccurate : state.core.numerical.box.diagonalSq ≤ target ^ 2
  cylinderAccurate : envelope.cylinderRadiusSq ≤ target
  coupledAccurate : envelope.radiusSq ≤ 2 * (target ^ 2 + target)

def reachedEnvelope
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (target : ℚ) (targetPositive : 0 < target)
    (first : DecoderBlock) (remaining : List DecoderBlock)
    (blocksEq : parserBlocks current.core.word = first :: remaining)
    (enoughBlocks : observationBlockDepth target ≤
      (first :: remaining).length) :
    ReachedEnvelope current target :=
  { state := refineForObservationEnvelope machine current target targetPositive
    refines := refineForObservationEnvelope_refines machine current target
      targetPositive
    envelope := coupledObservationEnvelope machine current target targetPositive
      first remaining blocksEq
    box_eq := rfl
    word_eq := rfl
    boxAccurate := refineForObservationEnvelope_box_accurate machine current
      target targetPositive
    cylinderAccurate := coupledObservationEnvelope_cylinderRadiusSq_le machine
      current target targetPositive first remaining blocksEq enoughBlocks
    coupledAccurate := coupledObservationEnvelope_radiusSq_le machine current
      target targetPositive first remaining blocksEq enoughBlocks }

end CCLActiveObservedEnvelope
end FTA
