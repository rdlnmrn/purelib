import CCL.Translation.SignedDigit
import CCL.Calculus.Exponential
import CCL.Progressive.OneSidedRationalExamples

/-!
# Worked finite-translation examples

These four examples exercise different parts of the protocol: algebraic
bisection, a Liouville-style nonalgebraic digit process, sequential raw CCL
output for a finite exponential program, and a redundant signed-digit
translation of that same non-rational process.
-/

namespace CCL.FiniteTranslationExamples

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Request := CCL.FiniteTranslation.Request

/-! ## 1. Square-three bisection to a rational ball -/

namespace SquareThreeBall

abbrev process :=
  CCL.ProgressiveOneSidedRationalExamples.SquareThree.process

def request : Request :=
  ⟨1 / 7, by decide⟩

def result :=
  (CCL.FiniteTranslation.processToBall process).translate
    FiniteMeasure.SqrtThree.initialState request

theorem refined_state :
    result.source' =
      CCL.ProgressiveOneSidedRationalExamples.SquareThree.refinedState := by
  change process.refine FiniteMeasure.SqrtThree.initialState
    (1 / 7) request.positive = _
  exact CCL.ProgressiveOneSidedRationalExamples.SquareThree.process_refine_eq_refinedState

/-- The certified translation performs the four internal bisections already
accounted for by the source process and exposes their `27/16` sample. -/
theorem translated_center :
    result.output.center.re = 27 / 16 ∧
      result.output.center.im = 0 := by
  change (process.ball result.source').center.re = 27 / 16 ∧
    (process.ball result.source').center.im = 0
  rw [refined_state]
  exact
    CCL.ProgressiveOneSidedRationalExamples.SquareThree.refined_ball_center

theorem translation_cost :
    result.schedule.work = 1 ∧ result.costBound = 1 := by
  exact ⟨rfl, rfl⟩

theorem translated_precision :
    (CCL.FiniteTranslation.ballRepresentation.precisionSq result.output) <
      1 / 7 := by
  calc
    CCL.FiniteTranslation.ballRepresentation.precisionSq result.output <
        request.targetSq + result.precisionLoss := result.precision
    _ = 1 / 7 := by decide

end SquareThreeBall

/-! ## 2. Liouville factorial-position digits to a rational ball -/

namespace LiouvilleBall

def request : Request :=
  ⟨1 / 9, by decide⟩

def result :=
  (CCL.FiniteTranslation.processToBall
    FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess).translate
      FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.initial request

theorem refined_state :
    result.source' =
      CCL.ProgressiveOneSidedRationalExamples.LiouvilleDigits.refinedState := by
  change
    FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.refine
      FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.initial
        (1 / 9) request.positive = _
  exact
    CCL.ProgressiveOneSidedRationalExamples.LiouvilleDigits.process_refine_eq_refinedState

/-- The nonperiodic factorial-position source returns its two-digit cylinder:
centre `5/16`, squared radius `(1/16)²`. -/
theorem translated_ball_data :
    result.output.center.re = 5 / 16 ∧
      result.output.center.im = 0 ∧
      result.output.radiusSq = (1 / 16) ^ 2 := by
  change
    (FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.ball
      result.source').center.re = 5 / 16 ∧
    (FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.ball
      result.source').center.im = 0 ∧
    (FiniteMeasure.OneSidedExamples.LiouvilleDigits.located.toProcess.ball
      result.source').radiusSq = (1 / 16) ^ 2
  rw [refined_state]
  exact
    CCL.ProgressiveOneSidedRationalExamples.LiouvilleDigits.refined_ball_data

theorem translation_cost :
    result.schedule.work = 1 ∧ result.costBound = 1 := by
  exact ⟨rfl, rfl⟩

end LiouvilleBall

/-! ## A shared finite exponential process for Examples 3 and 4 -/

namespace ComplexExponential

def input : Gaussian := ⟨1 / 2, 1 / 3⟩

theorem input_unit :
    RFAP.ConstructiveGaussian.Gaussian.normSq input ≤ 1 := by
  decide

def approximation : CCL.ProgressiveApproximation.Approximation :=
  CCL.ExponentialCalculus.expRelApproximation input input_unit

end ComplexExponential

/-! ## 3. Finite exponential approximation to a persistent CCL prefix -/

namespace ExponentialCursor

def request : Request :=
  ⟨1 / 64,
    RFAP.ConstructiveFraction.div_pos_direct (by decide)
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (by decide : 0 < (64 : Nat)))⟩

def result :=
  CCL.FiniteTranslation.approximationToCursorAt
    ComplexExponential.approximation 0 request

/-- Retaining the external sequential protocol emits one more raw bit than
the selected sampling index and exposes the resulting linear cost exactly. -/
theorem finite_cursor_schedule :
    let translated := CCL.FiniteTranslation.approximationToCursorAt
      ComplexExponential.approximation 0 request
    translated.output.word.length = translated.output.bitCount ∧
      translated.output.bitCount = translated.output.sampleIndex + 1 ∧
      translated.costBound =
        2 * (translated.output.sampleIndex + 1) + 2 :=
  CCL.FiniteTranslation.approximationToCursorAt_schedule
    ComplexExponential.approximation 0 request

theorem exact_raw_prefix :
    result.output.word.length = result.output.bitCount ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        ComplexExponential.approximation.toNamed.process
        ComplexExponential.approximation.toNamed.state
        (CCL.ProgressiveTransducer.advance
          ComplexExponential.approximation.toNamed.machine
          result.output.bitCount) :=
  CCL.FiniteTranslation.approximationToCursor_word_certificate
    ComplexExponential.approximation 0 request

def operationalRoundTrip :
    CCL.OperationalEquivalence.Equivalent
      (CCL.ProgressiveSampling.approximation
        ComplexExponential.approximation.toNamed)
      ComplexExponential.approximation :=
  (CCL.FiniteTranslation.certifiedApproximationCursorRoundTrip
    ComplexExponential.approximation).operational

def certifiedRoundTrip :
    CCL.FiniteTranslation.CertifiedApproximationCursorRoundTrip
      ComplexExponential.approximation :=
  CCL.FiniteTranslation.certifiedApproximationCursorRoundTrip
    ComplexExponential.approximation

def finerRequest : Request :=
  ⟨1 / 256,
    RFAP.ConstructiveFraction.div_pos_direct (by decide)
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (by decide : 0 < (256 : Nat)))⟩

/-- Two independently requested exponential cursors remain on one persistent
raw-prefix chain, even though their source starts and tolerances differ. -/
theorem translated_prefixes_persistent :
    let coarse := CCL.FiniteTranslation.approximationToCursorAt
      ComplexExponential.approximation 0 request
    let fine := CCL.FiniteTranslation.approximationToCursorAt
      ComplexExponential.approximation 2 finerRequest
    ((CCL.FiniteTranslation.cursorRepresentation
          ComplexExponential.approximation.toNamed).Refines
        fine.output coarse.output ∧
      coarse.output.word.IsPrefix fine.output.word) ∨
    ((CCL.FiniteTranslation.cursorRepresentation
          ComplexExponential.approximation.toNamed).Refines
        coarse.output fine.output ∧
      fine.output.word.IsPrefix coarse.output.word) :=
  certifiedRoundTrip.outputs_persistent 0 2 request finerRequest

end ExponentialCursor

/-! ## 4. The same finite exponential process in redundant signed digits -/

namespace ExponentialSignedDigits

def request : Request :=
  ⟨1 / 32,
    RFAP.ConstructiveFraction.div_pos_direct (by decide)
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (by decide : 0 < (32 : Nat)))⟩

/-- The rational search chooses one finite depth; both coordinate words have
that depth and the displayed cost is exactly `4 * depth + 4`.  These prefixes
are a certified finite observation of the exponential process rather than an
algebraic closed form for it. -/
theorem finite_signed_digit_data :
    let translated :=
      CCL.FiniteTranslation.SignedDigit.fromApproximationAt
        ComplexExponential.approximation 0 request
    let depth := CCL.FiniteTranslation.SignedDigit.requestDepth
      ComplexExponential.approximation request
    translated.output.depth = depth ∧
      translated.output.realDigits.length = depth ∧
      translated.output.imagDigits.length = depth ∧
      translated.costBound = 4 * depth + 4 :=
  CCL.FiniteTranslation.SignedDigit.fromApproximationAt_finite_data
    ComplexExponential.approximation 0 request

theorem translated_ball_precision :
    let translated :=
      CCL.FiniteTranslation.SignedDigit.fromApproximationAt
        ComplexExponential.approximation 0 request
    let ball := CCL.FiniteTranslation.SignedDigit.toBall.map translated.output
    CCL.FiniteTranslation.ballRepresentation.precisionSq ball <
      request.targetSq :=
  CCL.FiniteTranslation.SignedDigit.fromApproximationAt_toBall_precision
    ComplexExponential.approximation 0 request

theorem redundancy_is_observable :
    CCL.FiniteTranslation.SignedDigit.prefixValue
        [.positive, .negative] =
      CCL.FiniteTranslation.SignedDigit.prefixValue [.zero, .positive] ∧
    [.positive, .negative] ≠
      ([.zero, .positive] :
        List CCL.FiniteTranslation.SignedDigit.Digit) :=
  ⟨CCL.FiniteTranslation.SignedDigit.nonunique_prefix_center,
    CCL.FiniteTranslation.SignedDigit.nonunique_prefix_syntax⟩

end ExponentialSignedDigits

end CCL.FiniteTranslationExamples
