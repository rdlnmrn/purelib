import FTA.CCLFormulaPullback
import FTA.CCLHomographicCylinder

/-!
# Box--truncation coupling from the active parser phase

The metric invariant does not need a rational point satisfying every retained
historical parser constraint.  It needs a rational point in the winding box
whose current inverse tail satisfies the active radial predicate.  The decoder
homography then gives a direct rational error bound to the tagged truncation.

This is the history-free coupling interface used by the direct Sturm/curve-
count controller.  Historical predicates still determine prefix semantics,
but they are not part of the numerical box--cylinder inequality.
-/

namespace FTA
namespace CCLActiveBoxCoupling

open CCL CCL.GaussianRat
open FTA.CCLChordalEnvelope
open FTA.CCLFormulaPullback
open FTA.CCLGeometry
open FTA.CCLHomographicCylinder
open FTA.CCLNextBitFormula
open FTA.CCLParserGeometry

abbrev QI := CCL.GaussianRat

/-- The current active-phase predicate pulled back to the original input
coordinate.  Unlike `inputStateFormula`, this deliberately omits completed
historical blocks. -/
def inputActiveFormula (state : RawParser.State) : Formula :=
  Formula.pullback (adjugate state.matrix) (activeFormula state.phase)

theorem inputActiveFormula_iff
    (state : RawParser.State) (input : QI)
    (inverseDenominator :
      (adjugate state.matrix).c * input + (adjugate state.matrix).d ≠ 0) :
    (inputActiveFormula state).Holds input ↔
      RawParser.activeHolds state.phase
        (RatBox.homographic (adjugate state.matrix) input) := by
  rw [inputActiveFormula,
    Formula.pullback_iff (adjugate state.matrix) _ input inverseDenominator,
    activeFormula_iff]

/-- The genuinely new predicate introduced by one bit is exactly enough to
establish the active predicate of the appended parser state.  At the third
sector bit the proof performs the rational subtraction/inversion and decoder
matrix update explicitly; no retained historical formula is used. -/
theorem inputActiveFormula_step_of_incremental
    (state : RawParser.State) (bit : Bool) (input : QI)
    (stateDeterminant : determinant state.matrix ≠ 0)
    (inverseDenominator :
      (adjugate state.matrix).c * input +
        (adjugate state.matrix).d ≠ 0)
    (incremental :
      (inputIncrementalAdvanceFormula state bit).Holds input) :
    (inputActiveFormula (RawParser.step state bit)).Holds input := by
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      cases bit <;>
        simpa [inputActiveFormula, inputIncrementalAdvanceFormula,
          incrementalAdvanceFormula, RawParser.step] using incremental
  | highUnary count =>
      cases bit <;>
        simpa [inputActiveFormula, inputIncrementalAdvanceFormula,
          incrementalAdvanceFormula, RawParser.step] using incremental
  | lowUnary count =>
      cases bit <;>
        simpa [inputActiveFormula, inputIncrementalAdvanceFormula,
          incrementalAdvanceFormula, RawParser.step] using incremental
  | loopUnary count =>
      cases bit <;>
        simpa [inputActiveFormula, inputIncrementalAdvanceFormula,
          incrementalAdvanceFormula, RawParser.step] using incremental
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          cases bit <;>
            simpa [inputActiveFormula, inputIncrementalAdvanceFormula,
              incrementalAdvanceFormula, RawParser.step] using incremental
      | one first =>
          cases bit <;>
            simpa [inputActiveFormula, inputIncrementalAdvanceFormula,
              incrementalAdvanceFormula, RawParser.step] using incremental
      | two first second =>
          let oldState : RawParser.State :=
            ⟨.sector kind exponent (.two first second), matrix, history⟩
          let sector := RawParser.sectorOfBits first second bit
          let block := RawParser.blockMatrix kind exponent sector
          let before := RatBox.homographic (adjugate matrix) input
          have incrementalBefore :
              (incrementalAdvanceFormula oldState bit).Holds before :=
            (inputIncrementalAdvanceFormula_iff oldState bit input
              inverseDenominator).1 incremental
          have advanceBefore : (advanceFormula oldState bit).Holds before := by
            simpa [oldState, incrementalAdvanceFormula] using incrementalBefore
          have canAdvance :=
            (advanceFormula_iff oldState bit before).1 advanceBefore
          have full : RawParser.fullBlockHolds kind exponent sector before := by
            simpa only [oldState, CCL.EncoderParserBridge.CanAdvanceAt,
              sector] using canAdvance.1
          have residual :
              RawParser.normalizedValue kind exponent before - sector.rep ≠ 0 := by
            simpa only [oldState, CCL.EncoderParserBridge.CanAdvanceAt,
              sector] using canAdvance.2
          let tail := inv (gamma *
            (RawParser.normalizedValue kind exponent before - sector.rep))
          have tailActive : RawParser.activeHolds (.loopUnary 0) tail := by
            exact CCL.EncoderParserBridge.inverse_selected_loop_active kind
              exponent sector before full residual
          have blockDenominator :
              RawParserSemantics.denominator block tail ≠ 0 := by
            exact CCL.EncoderParserBridge.block_inverse_denominator_ne kind
              exponent sector before residual
          have blockForward : RatBox.homographic block tail = before := by
            exact CCL.EncoderParserBridge.block_homographic_inverse kind
              exponent sector before residual
          have oldForwardDenominator :
              RawParserSemantics.denominator matrix before ≠ 0 := by
            exact denominator_inverse_tail_ne matrix input stateDeterminant
              inverseDenominator
          have oldDecode : RatBox.homographic matrix before = input := by
            exact homographic_adjugate_inverse matrix input stateDeterminant
              inverseDenominator
          have newForwardDenominator :
              RawParserSemantics.denominator (Mat2.mul matrix block) tail ≠ 0 := by
            apply (RawParserSemantics.denominator_mul_ne_iff matrix block tail
              blockDenominator).2
            rw [blockForward]
            exact oldForwardDenominator
          have newDecode :
              RatBox.homographic (Mat2.mul matrix block) tail = input := by
            calc
              RatBox.homographic (Mat2.mul matrix block) tail =
                  RatBox.homographic matrix
                    (RatBox.homographic block tail) :=
                RawParserSemantics.homographic_mul matrix block tail
                  blockDenominator (by
                    rw [blockForward]
                    exact oldForwardDenominator)
              _ = RatBox.homographic matrix before := by rw [blockForward]
              _ = input := oldDecode
          have newDeterminant :
              determinant (Mat2.mul matrix block) ≠ 0 := by
            change (Mat2.mul matrix block).det ≠ 0
            rw [RawParser.det_mul]
            exact mul_ne_zero
              (by
                change determinant matrix ≠ 0
                exact stateDeterminant)
              (by
                simpa only [block, sector] using
                  RawParser.blockMatrix_det_ne kind exponent sector)
          have newInverseDenominator :
              (adjugate (Mat2.mul matrix block)).c * input +
                (adjugate (Mat2.mul matrix block)).d ≠ 0 := by
            rw [← newDecode]
            exact adjugate_denominator_homographic_ne
              (Mat2.mul matrix block) tail newDeterminant
                newForwardDenominator
          have recovered :
              RatBox.homographic (adjugate (Mat2.mul matrix block)) input =
                tail := by
            rw [← newDecode]
            exact homographic_adjugate_forward_inverse
              (Mat2.mul matrix block) tail newDeterminant
                newForwardDenominator
          apply (inputActiveFormula_iff (RawParser.step oldState bit) input
            (by simpa [oldState, RawParser.step, RawParser.completeSector,
              block, sector] using newInverseDenominator)).2
          simpa [oldState, RawParser.step, RawParser.completeSector,
            block, sector, recovered] using tailActive

/-- A rational box point carrying only the active parser predicate and the
affine inverse-decoder certificate needed by the metric estimate. -/
structure ActiveBoxSample (word : Prefix.Word) (box : RatBox) where
  point : QI
  inside : box.Contains point
  inverseDenominator :
    (adjugate (RawParser.parse word).matrix).c * point +
      (adjugate (RawParser.parse word).matrix).d ≠ 0
  active : (inputActiveFormula (RawParser.parse word)).Holds point

namespace ActiveBoxSample

/-- Package a rational point satisfying one history-free child predicate as
an active sample for the appended word.  The successor denominator is kept
as an explicit affine certificate: a subsequent denominator-separation step
can supply it uniformly on the refined winding box. -/
def ofIncrementalStep
    {word : Prefix.Word} {box : RatBox} (bit : Bool) (point : QI)
    (inside : box.Contains point)
    (inverseDenominator :
      (adjugate (RawParser.parse word).matrix).c * point +
        (adjugate (RawParser.parse word).matrix).d ≠ 0)
    (successorInverseDenominator :
      (adjugate (RawParser.step (RawParser.parse word) bit).matrix).c * point +
        (adjugate (RawParser.step (RawParser.parse word) bit).matrix).d ≠ 0)
    (incremental :
      (inputIncrementalAdvanceFormula (RawParser.parse word) bit).Holds
        point) :
    ActiveBoxSample (word ++ [bit]) box where
  point := point
  inside := inside
  inverseDenominator := by
    simpa [RawParser.parse, List.foldl_append] using
      successorInverseDenominator
  active := by
    simpa [RawParser.parse, List.foldl_append] using
      inputActiveFormula_step_of_incremental (RawParser.parse word) bit point
        (by simpa only [determinant, Mat2.det] using
          RawParser.parse_det_ne word)
        inverseDenominator incremental

/-- The active predicate in the actual affine tail coordinate. -/
theorem tail_active {word : Prefix.Word} {box : RatBox}
    (sample : ActiveBoxSample word box) :
    RawParser.activeHolds (RawParser.parse word).phase
      (RatBox.homographic (adjugate (RawParser.parse word).matrix)
        sample.point) :=
  (inputActiveFormula_iff (RawParser.parse word) sample.point
    sample.inverseDenominator).1 sample.active

/-- The inverse tail decodes back to the displayed box point. -/
theorem decode_tail {word : Prefix.Word} {box : RatBox}
    (sample : ActiveBoxSample word box) :
    RatBox.homographic (RawParser.parse word).matrix
        (RatBox.homographic (adjugate (RawParser.parse word).matrix)
          sample.point) = sample.point := by
  apply homographic_adjugate_inverse
  · simpa only [determinant, Mat2.det] using RawParser.parse_det_ne word
  · exact sample.inverseDenominator

/-- The forward decoder denominator at the recovered active tail is nonzero. -/
theorem tail_denominator {word : Prefix.Word} {box : RatBox}
    (sample : ActiveBoxSample word box) :
    RawParserSemantics.denominator (RawParser.parse word).matrix
      (RatBox.homographic (adjugate (RawParser.parse word).matrix)
        sample.point) ≠ 0 := by
  apply denominator_inverse_tail_ne
  · simpa only [determinant, Mat2.det] using RawParser.parse_det_ne word
  · exact sample.inverseDenominator

/-- Before any completed decoder block exists, the active predicate is the
entire parser predicate.  Thus a history-free active sample is already an
ordinary compatible affine realization; no historical persistence argument
is needed in this initial fragment. -/
theorem represented_of_history_eq_nil
    {word : Prefix.Word} {box : RatBox}
    (sample : ActiveBoxSample word box)
    (history : (RawParser.parse word).history = []) :
    RawParserSemantics.Represented word sample.point := by
  let tail := RatBox.homographic
    (adjugate (RawParser.parse word).matrix) sample.point
  refine ⟨tail, sample.tail_denominator, sample.decode_tail.symm, ?_⟩
  constructor
  · intro constraint member
    rw [history] at member
    simp at member
  · exact sample.tail_active

end ActiveBoxSample

/-- A phase-local large-tail estimate.  Its premise is only the active
unfinished parser predicate, not the full retained history. -/
structure ActiveTailLowerBound (word : Prefix.Word) where
  threshold : ℚ
  thresholdPositive : 0 < threshold
  lower : ∀ {tail : QI},
    RawParser.activeHolds (RawParser.parse word).phase tail →
      threshold ≤ normSq tail
  outputLowerPositive :
    0 < outputWeightLower (RawParser.parse word).matrix threshold

/-- Radial information available before checking the decoder-specific output
weight.  Initial-low phases use their separate small-tail estimate. -/
structure ActiveRadialLowerBound (word : Prefix.Word) where
  threshold : ℚ
  thresholdPositive : 0 < threshold
  lower : ∀ {tail : QI},
    RawParser.activeHolds (RawParser.parse word).phase tail →
      threshold ≤ normSq tail

def ActiveRadialLowerBound.withOutputPositive {word : Prefix.Word}
    (bound : ActiveRadialLowerBound word)
    (positive :
      0 < outputWeightLower (RawParser.parse word).matrix bound.threshold) :
    ActiveTailLowerBound word where
  threshold := bound.threshold
  thresholdPositive := bound.thresholdPositive
  lower := bound.lower
  outputLowerPositive := positive

/-- Extract the large-tail inequality from the active phase alone. -/
def activeRadialLowerBound? (word : Prefix.Word) :
    Option (ActiveRadialLowerBound word) := by
  cases phase : (RawParser.parse word).phase with
  | initial => exact none
  | highUnary count =>
      exact some
        { threshold := (2 : ℚ) ^ count
          thresholdPositive := by positivity
          lower := by
            intro tail active
            rw [phase] at active
            exact active }
  | lowUnary _ => exact none
  | loopUnary count =>
      exact some
        { threshold := (2 : ℚ) ^ count
          thresholdPositive := by positivity
          lower := by
            intro tail active
            rw [phase] at active
            exact active.le }
  | sector kind exponent bits =>
      cases kind with
      | initialLow => exact none
      | initialHigh =>
          exact some
            { threshold := (2 : ℚ) ^ exponent
              thresholdPositive := by positivity
              lower := by
                intro tail active
                rw [phase] at active
                exact active.1.1 }
      | loop =>
          exact some
            { threshold := (2 : ℚ) ^ exponent
              thresholdPositive := by positivity
              lower := by
                intro tail active
                rw [phase] at active
                exact active.1.1.le }

/-- Total finite attempt to combine the active radial lower bound with the
decoder output-weight comparison. -/
def activeTailLowerBound? (word : Prefix.Word) :
    Option (ActiveTailLowerBound word) :=
  match activeRadialLowerBound? word with
  | none => none
  | some bound =>
      if positive :
          0 < outputWeightLower (RawParser.parse word).matrix bound.threshold
      then some (bound.withOutputPositive positive)
      else none

/-- Decoder-specific computed unary depth, stated only against the current
active phase rather than the complete retained parser history. -/
def computedDepthActiveTailLowerBound
    (word : Prefix.Word) (epsilon : ℚ) (epsilonPositive : 0 < epsilon)
    (lower : ∀ {tail : QI},
      RawParser.activeHolds (RawParser.parse word).phase tail →
        (2 : ℚ) ^ decoderUnaryDepth
          (RawParser.parse word).matrix epsilon ≤ normSq tail) :
    ActiveTailLowerBound word where
  threshold := (2 : ℚ) ^ decoderUnaryDepth
    (RawParser.parse word).matrix epsilon
  thresholdPositive := by positivity
  lower := lower
  outputLowerPositive := outputWeightLower_depth_power_pos
    (RawParser.parse_det_ne word) epsilonPositive

/-- Direct truncation error from one active box sample.  No represented-word
witness and no historical owner cone occurs in this construction. -/
def ActiveBoxSample.referenceError
    {word : Prefix.Word} {box : RatBox}
    (sample : ActiveBoxSample word box)
    (bound : ActiveTailLowerBound word) : ReferenceError where
  truncation := ⟨word⟩
  reference := sample.point
  radiusSq := truncationRadiusSq (RawParser.parse word).matrix bound.threshold
  radiusSq_nonneg := truncationRadiusSq_nonneg _ bound.outputLowerPositive
  certified := by
    let matrix := (RawParser.parse word).matrix
    let tail := RatBox.homographic (adjugate matrix) sample.point
    have estimate := chordalSq_act_truncation_le
      (matrix := matrix) (R := bound.threshold)
      (by simpa only [matrix, determinant, Mat2.det] using
        RawParser.parse_det_ne word)
      bound.outputLowerPositive (bound.lower sample.tail_active)
    rw [act_affine_eq_scale_homographic matrix tail sample.tail_denominator,
      chordalSq_scale_left _ sample.tail_denominator] at estimate
    simpa only [TaggedTruncation.point, RawParser.State.truncation,
      matrix, tail, sample.decode_tail] using estimate

/-- At the computed decoder depth, the active reference error is bounded by
the requested rational cylinder error. -/
theorem ActiveBoxSample.computedDepthReferenceError_radiusSq_le
    {word : Prefix.Word} {box : RatBox}
    (sample : ActiveBoxSample word box)
    {epsilon : ℚ} (epsilonPositive : 0 < epsilon)
    (lower : ∀ {tail : QI},
      RawParser.activeHolds (RawParser.parse word).phase tail →
        (2 : ℚ) ^ decoderUnaryDepth
          (RawParser.parse word).matrix epsilon ≤ normSq tail) :
    (sample.referenceError
      (computedDepthActiveTailLowerBound word epsilon epsilonPositive
        lower)).radiusSq ≤ epsilon := by
  have diameter := cylinderRadiusSq_depth_power_le
    (RawParser.parse_det_ne word) epsilonPositive
  have radiusNonnegative := truncationRadiusSq_nonneg
    (RawParser.parse word).matrix
    (outputWeightLower_depth_power_pos (RawParser.parse_det_ne word)
      epsilonPositive)
  change truncationRadiusSq (RawParser.parse word).matrix
    ((2 : ℚ) ^ decoderUnaryDepth
      (RawParser.parse word).matrix epsilon) ≤ epsilon
  change 4 * truncationRadiusSq (RawParser.parse word).matrix
    ((2 : ℚ) ^ decoderUnaryDepth
      (RawParser.parse word).matrix epsilon) ≤ epsilon at diameter
  nlinarith

/-- Install the direct reference error as the rational coupled envelope of
the whole winding box. -/
def ActiveBoxSample.coupledEnvelope
    {word : Prefix.Word} {box : RatBox}
    (sample : ActiveBoxSample word box)
    (bound : ActiveTailLowerBound word) : CoupledEnvelope where
  box := box
  certificate := sample.referenceError bound
  referenceInside := sample.inside

/-- Computed active-cylinder error and an independent box-diagonal error add
to the coupled rational radius. -/
theorem ActiveBoxSample.computedDepthCoupledEnvelope_radiusSq_le
    {word : Prefix.Word} {box : RatBox}
    (sample : ActiveBoxSample word box)
    {epsilon boxError : ℚ} (epsilonPositive : 0 < epsilon)
    (lower : ∀ {tail : QI},
      RawParser.activeHolds (RawParser.parse word).phase tail →
        (2 : ℚ) ^ decoderUnaryDepth
          (RawParser.parse word).matrix epsilon ≤ normSq tail)
    (boxBound : box.diagonalSq ≤ boxError) :
    (sample.coupledEnvelope
      (computedDepthActiveTailLowerBound word epsilon epsilonPositive
        lower)).radiusSq ≤ 2 * (boxError + epsilon) := by
  have cylinderBound :=
    sample.computedDepthReferenceError_radiusSq_le epsilonPositive lower
  change truncationRadiusSq (RawParser.parse word).matrix
    ((2 : ℚ) ^ decoderUnaryDepth
      (RawParser.parse word).matrix epsilon) ≤ epsilon at cylinderBound
  change 2 * (box.diagonalSq +
    truncationRadiusSq (RawParser.parse word).matrix
      ((2 : ℚ) ^ decoderUnaryDepth
        (RawParser.parse word).matrix epsilon)) ≤
          2 * (boxError + epsilon)
  linarith

/-- The requested rational coupling inequality, derived from only a current
active-phase sample. -/
theorem ActiveBoxSample.box_point_le_radiusSq
    {word : Prefix.Word} {box : RatBox}
    (sample : ActiveBoxSample word box)
    (bound : ActiveTailLowerBound word)
    {point : QI} (inside : box.Contains point) :
    chordalSq (Proj.affine point) (⟨word⟩ : TaggedTruncation).point ≤
      (sample.coupledEnvelope bound).radiusSq :=
  (sample.coupledEnvelope bound).contains_of_box_contains inside

/-- Coarse total fallback before the active phase has accumulated enough
radial depth for a transported contraction certificate. -/
def unitReferenceError (word : Prefix.Word) (reference : QI) :
    ReferenceError where
  truncation := ⟨word⟩
  reference := reference
  radiusSq := 1
  radiusSq_nonneg := by norm_num
  certified := chordalSq_le_one (Proj.affine_hasNonzeroCoordinate reference)
    (TaggedTruncation.point_hasNonzeroCoordinate ⟨word⟩)

/-- Prefer the phase-local homographic bound when its finite positivity check
succeeds, otherwise retain the universal unit reference error. -/
def ActiveBoxSample.bestReferenceError
    {word : Prefix.Word} {box : RatBox}
    (sample : ActiveBoxSample word box) : ReferenceError :=
  match activeTailLowerBound? word with
  | some bound => sample.referenceError bound
  | none => unitReferenceError word sample.point

end CCLActiveBoxCoupling
end FTA
