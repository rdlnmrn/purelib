import CCL.Acquisition
import CCL.Progressive.GapDivisionExamples
import CCL.Riemann.ExactDecisionExamples
import CCL.Riemann.LegendreSeparatedExamples

/-! # Regression clients through the public finite-acquisition interface -/

namespace CCL.FiniteAcquisitionExamples

open CCL.FiniteAcquisition
open CCL.ProgressiveBoundedDivisionExamples (oneInput tinyInput zeroInput)

theorem bounded_one_ready :
    ∃ ready, (boundedDivision oneInput (State.initial oneInput) 1 (by decide)).2 = .inl ready :=
  ⟨_, rfl⟩

theorem bounded_tiny_small :
    ∃ small, (boundedDivision oneInput (State.initial tinyInput) 1 (by decide)).2 = .inr small :=
  ⟨_, rfl⟩

theorem bounded_preserves_retry_index :
    (boundedDivision oneInput (State.initial tinyInput) 1 (by decide)).1.inspection.retained.nextIndex =
      (State.initial tinyInput).nextIndex :=
  (BoundedResult.spec (boundedDivision oneInput (State.initial tinyInput) 1 (by decide))).2.1

theorem gap_zero_excluded :
    (gapDivision (State.initial zeroInput) 1 (by decide)
      CCL.ProgressiveGapDivisionExamples.zero_gap).2.isPrepared = false := by decide

abbrev negative := CCL.Riemann.LegendreSignedAcquisitionExamples.input (-1)
abbrev negativeStart := CCL.Riemann.LegendrePositivityAcquisition.initial negative

def negativeSigned := signedGap negative negativeStart 1 (by decide)
  (CCL.Riemann.LegendreSignedGapExamples.negative_gap _)

theorem signed_negative : negativeSigned.outcome.isPositive = false := by decide

theorem signed_budget : negativeSigned.count ≤
    Nat.log2 (RFAP.ConstructiveFraction.ceilNat (1 / ((1 : Q) ^ 2 / 16))) + 2 :=
  (signedGap_spec negative negativeStart 1 (by decide)
    (CCL.Riemann.LegendreSignedGapExamples.negative_gap _)).2.2.1

def rationalCancellation := Provenance.rational
  CCL.ProgressiveExactProvenanceExamples.cancellationSidecar

def algebraicCancellation := Provenance.squareRoot
  CCL.Riemann.SquareRootSidecarExamples.cancellationSidecar

theorem exact_cross_provenance :
    (exact rationalCancellation).isPrepared = (exact algebraicCancellation).isPrepared :=
  exact_respects rationalCancellation algebraicCancellation
    (CCL.OperationalEquivalence.NamedEquivalent.refl _)

theorem exact_cancellation_complete :
    CCL.ProgressiveExactProvenance.IsZero CCL.ProgressiveExactProvenanceExamples.cancellation ↔
      ¬ CCL.ProgressiveExactProvenance.IsPrepared CCL.ProgressiveExactProvenanceExamples.cancellation :=
  (exact_complete algebraicCancellation).1

def negativeWord (word : CCL.Knot.FiniteBraid.Word 3) :=
  separatedWord CCL.Riemann.LegendreSeparatedExamples.negativeSeparation word

def negative_reversal (word : CCL.Knot.FiniteBraid.Word 3) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.LegendreFractionalWords.foldAction (negativeWord word).output
        (CCL.Riemann.LegendreFractionalWords.periodBraidMatrices word.inverse)
        (negativeWord word).prepareReversal.reverse).name negative.name :=
  (negativeWord word).reversal

end CCL.FiniteAcquisitionExamples
