import FTA.CCLActiveMetricProgress
import CCL.RawParserProgress

/-!
# Phase-local cylinder certificates for the active metric track

The active controller has two genuinely different initial geometries.  Large
inverse tails contract directly towards the tagged projective truncation.
During the initial-low run, however, the affine cylinder contracts around
zero while the formal tag remains `ω`; because no block history exists yet,
the active sample is a full raw-prefix representative and supplies the old
box--cylinder coupling honestly.
-/

namespace FTA
namespace CCLActiveCylinderProgress

open CCL CCL.GaussianRat
open FTA.CCLActiveBoxCoupling
open FTA.CCLActiveMetricTrack
open FTA.CCLActiveMetricProgress
open FTA.CCLChordalEnvelope
open FTA.CCLHomographicCylinder
open FTA.CCLRawCylinderEnvelope

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- The two finite metric certificates produced at a parser threshold.
Both expose the same rational summed error, but the initial-low constructor
correctly keeps the shrinking raw cylinder distinct from the unchanged tag. -/
inductive ReachedMetricCertificate
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (epsilon : ℚ) where
  | tagged (envelope : CoupledEnvelope)
      (box_eq : envelope.box = state.core.numerical.box)
      (word_eq : envelope.certificate.truncation.word = state.core.word)
      (error_le : envelope.radiusSq ≤
        2 * (state.core.numerical.box.diagonalSq + epsilon)) :
      ReachedMetricCertificate state epsilon
  | initialLow (coupling : BoxCylinderCoupling)
      (box_eq : coupling.box = state.core.numerical.box)
      (word_eq : coupling.cylinder.truncation.word = state.core.word)
      (error_le : coupling.errorSq ≤
        2 * (state.core.numerical.box.diagonalSq + epsilon)) :
      ReachedMetricCertificate state epsilon

/-- Convert every applicable parser threshold into its honest active metric
certificate.  No completed historical predicate is assumed in the tagged
cases; the initial-low cases use the proved-empty parser history. -/
def certificateOfReachedThreshold
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (epsilon : ℚ)
    (epsilonPositive : 0 < epsilon)
    (reached : (RawParser.parse state.core.word).phase.ReachedThreshold
      (decoderUnaryDepth
        (RawParser.parse state.core.word).matrix epsilon)
      (initialLowContractionDepth epsilon)) :
    ReachedMetricCertificate state epsilon := by
  cases phaseEq : (RawParser.parse state.core.word).phase with
  | initial =>
      simp [RawParser.Phase.ReachedThreshold, phaseEq] at reached
  | highUnary count =>
      rw [phaseEq] at reached
      change decoderUnaryDepth
        (RawParser.parse state.core.word).matrix epsilon ≤ count at reached
      let lower : ∀ {tail : QI},
          RawParser.activeHolds
              (RawParser.parse state.core.word).phase tail →
            (2 : ℚ) ^ decoderUnaryDepth
              (RawParser.parse state.core.word).matrix epsilon ≤ normSq tail := by
        intro tail active
        rw [phaseEq] at active
        exact (two_pow_le_two_pow reached).trans active
      let envelope := state.computedDepthEnvelope epsilon epsilonPositive lower
      exact .tagged envelope rfl rfl
        (state.computedDepthEnvelope_radiusSq_le epsilonPositive lower le_rfl)
  | lowUnary count =>
      rw [phaseEq] at reached
      change initialLowContractionDepth epsilon ≤ count at reached
      cases count with
      | zero =>
          simp [initialLowContractionDepth] at reached
      | succ count =>
          let coupling := state.initialLowUnaryCoupling count (by
            simpa only [Nat.succ_eq_add_one] using phaseEq)
          exact .initialLow coupling rfl rfl
            (state.initialLowUnaryCoupling_errorSq_le count (by
              simpa only [Nat.succ_eq_add_one] using phaseEq)
              epsilonPositive (by simpa only [Nat.succ_eq_add_one] using reached)
              le_rfl)
  | loopUnary count =>
      rw [phaseEq] at reached
      change decoderUnaryDepth
        (RawParser.parse state.core.word).matrix epsilon ≤ count at reached
      let lower : ∀ {tail : QI},
          RawParser.activeHolds
              (RawParser.parse state.core.word).phase tail →
            (2 : ℚ) ^ decoderUnaryDepth
              (RawParser.parse state.core.word).matrix epsilon ≤ normSq tail := by
        intro tail active
        rw [phaseEq] at active
        exact (two_pow_le_two_pow reached).trans active.le
      let envelope := state.computedDepthEnvelope epsilon epsilonPositive lower
      exact .tagged envelope rfl rfl
        (state.computedDepthEnvelope_radiusSq_le epsilonPositive lower le_rfl)
  | sector kind exponent bits =>
      cases kind with
      | initialLow =>
          rw [phaseEq] at reached
          change initialLowContractionDepth epsilon ≤ exponent at reached
          let coupling := state.initialLowSectorCoupling exponent bits phaseEq
          exact .initialLow coupling rfl rfl
            (state.initialLowSectorCoupling_errorSq_le exponent bits phaseEq
              epsilonPositive reached le_rfl)
      | initialHigh =>
          rw [phaseEq] at reached
          change decoderUnaryDepth
            (RawParser.parse state.core.word).matrix epsilon ≤ exponent at reached
          let lower : ∀ {tail : QI},
              RawParser.activeHolds
                  (RawParser.parse state.core.word).phase tail →
                (2 : ℚ) ^ decoderUnaryDepth
                  (RawParser.parse state.core.word).matrix epsilon ≤
                    normSq tail := by
            intro tail active
            rw [phaseEq] at active
            exact (two_pow_le_two_pow reached).trans active.1.1
          let envelope := state.computedDepthEnvelope epsilon epsilonPositive lower
          exact .tagged envelope rfl rfl
            (state.computedDepthEnvelope_radiusSq_le epsilonPositive lower le_rfl)
      | loop =>
          rw [phaseEq] at reached
          change decoderUnaryDepth
            (RawParser.parse state.core.word).matrix epsilon ≤ exponent at reached
          let lower : ∀ {tail : QI},
              RawParser.activeHolds
                  (RawParser.parse state.core.word).phase tail →
                (2 : ℚ) ^ decoderUnaryDepth
                  (RawParser.parse state.core.word).matrix epsilon ≤
                    normSq tail := by
            intro tail active
            rw [phaseEq] at active
            exact (two_pow_le_two_pow reached).trans active.1.1.le
          let envelope := state.computedDepthEnvelope epsilon epsilonPositive lower
          exact .tagged envelope rfl rfl
            (state.computedDepthEnvelope_radiusSq_le epsilonPositive lower le_rfl)

/-- The exact natural measure consumed by one active local contraction
attempt. -/
def localProgressBudget
    {p : GaussianPolynomial} {ambient : RatBox}
    (state : State p ambient) (epsilon : ℚ) : ℕ :=
  (RawParser.parse state.core.word).phase.progressBudget
    (decoderUnaryDepth (RawParser.parse state.core.word).matrix epsilon)
    (initialLowContractionDepth epsilon)

/-- One total local active run either terminates, reaches an honest metric
certificate, or completes another decoder block. -/
inductive LocalProgressResult
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR)) (epsilon : ℚ) where
  | zero (root : p.eval 0 = 0) : LocalProgressResult current epsilon
  | terminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : current.core.numerical.box.Contains point) :
      LocalProgressResult current epsilon
  | certified (state : State p (RatBox.symmetric R hR))
      (refines : StateRefines state current)
      (certificate : ReachedMetricCertificate state epsilon)
      (bits : Prefix.Word)
      (word_eq : state.core.word = current.core.word ++ bits) :
      LocalProgressResult current epsilon
  | completedBlock (state : State p (RatBox.symmetric R hR))
      (refines : StateRefines state current)
      (bits : Prefix.Word)
      (word_eq : state.core.word = current.core.word ++ bits)
      (history_grows :
        (RawParser.parse current.core.word).history.length <
          (RawParser.parse state.core.word).history.length) :
      LocalProgressResult current epsilon

/-- Run the active bit controller only until the current parser reaches its
computed metric threshold or applies one completed block.  The recursion
measure is the parser's ordinary progress budget; no user-supplied fuel or
resource override occurs. -/
def advanceToCertificateOrBlock
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon) :
    LocalProgressResult current epsilon := by
  let parser := RawParser.parse current.core.word
  let largeTarget := decoderUnaryDepth parser.matrix epsilon
  let smallTarget := initialLowContractionDepth epsilon
  by_cases reached : parser.phase.ReachedThreshold largeTarget smallTarget
  · exact .certified current (stateRefines_refl current)
      (certificateOfReachedThreshold current epsilon epsilonPositive (by
        simpa only [parser, largeTarget, smallTarget] using reached)) [] (by simp)
  · match stepResult : machine.step current with
    | .zero root => exact .zero root
    | .terminal point root nonzero completeWord complete contains =>
        exact .terminal point root nonzero completeWord complete contains
    | .next bit next boxRefines wordEq =>
        have parsedNext : RawParser.parse next.core.word =
            RawParser.step parser bit := by
          rw [wordEq]
          simp [RawParser.parse, List.foldl_append, parser]
        have nextRefines : StateRefines next current := by
          refine ⟨boxRefines, ?_⟩
          rw [wordEq]
          exact List.prefix_append _ _
        have historyMonotone : parser.history.length ≤
            (RawParser.parse next.core.word).history.length := by
          rw [parsedNext]
          exact RawParser.history_length_le_step parser bit
        by_cases historyGrows : parser.history.length <
            (RawParser.parse next.core.word).history.length
        · exact .completedBlock next nextRefines [bit] wordEq (by
            simpa only [parser] using historyGrows)
        · have historyEq :
              (RawParser.step parser bit).history.length =
                parser.history.length := by
            rw [← parsedNext]
            omega
          have matrixEq : (RawParser.step parser bit).matrix = parser.matrix :=
            RawParser.step_matrix_eq_of_history_length_eq parser bit historyEq
          have budgetDrops : localProgressBudget next epsilon <
              localProgressBudget current epsilon := by
            unfold localProgressBudget
            rw [parsedNext, matrixEq]
            exact RawParser.progressBudget_step_lt parser bit largeTarget
              smallTarget reached historyEq
          match advanceToCertificateOrBlock machine next epsilon
              epsilonPositive with
          | .zero root => exact .zero root
          | .terminal point root nonzero completeWord complete contains =>
              exact .terminal point root nonzero completeWord complete
                (nextRefines.box.contains contains)
          | .certified final finalRefines certificate bits finalWord =>
              exact .certified final (finalRefines.trans nextRefines)
                certificate (bit :: bits) (by
                  rw [finalWord, wordEq]
                  simp [List.append_assoc])
          | .completedBlock final finalRefines bits finalWord finalHistory =>
              exact .completedBlock final (finalRefines.trans nextRefines)
                (bit :: bits) (by
                  rw [finalWord, wordEq]
                  simp [List.append_assoc]) (by
                    have nextHistoryEq :
                        (RawParser.parse next.core.word).history.length =
                          parser.history.length := by
                      rw [parsedNext, historyEq]
                    rw [← nextHistoryEq]
                    exact finalHistory)
termination_by localProgressBudget current epsilon

/-- Bounded repetition of active local attempts.  Exhaustion is positive
evidence that the requested number of additional decoder blocks completed;
it is never reported as an unexplained failure. -/
inductive BlockProgressResult
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (current : State p (RatBox.symmetric R hR))
    (epsilon : ℚ) : ℕ → Type where
  | zero {blockCount : ℕ} (root : p.eval 0 = 0) :
      BlockProgressResult current epsilon blockCount
  | terminal {blockCount : ℕ} (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : current.core.numerical.box.Contains point) :
      BlockProgressResult current epsilon blockCount
  | certified {blockCount : ℕ}
      (state : State p (RatBox.symmetric R hR))
      (refines : StateRefines state current)
      (certificate : ReachedMetricCertificate state epsilon) :
      BlockProgressResult current epsilon blockCount
  | blocksAdvanced {blockCount : ℕ}
      (state : State p (RatBox.symmetric R hR))
      (refines : StateRefines state current)
      (history_growth :
        (RawParser.parse current.core.word).history.length + blockCount ≤
          (RawParser.parse state.core.word).history.length) :
      BlockProgressResult current epsilon blockCount

/-- Repeat the total active local controller structurally on the requested
number of completed blocks. -/
def advanceBlocksOrCertificate
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R}
    (machine : Machine p R hR)
    (current : State p (RatBox.symmetric R hR))
    (epsilon : ℚ) (epsilonPositive : 0 < epsilon) :
    (blockCount : ℕ) → BlockProgressResult current epsilon blockCount
  | 0 => .blocksAdvanced current (stateRefines_refl current) (by simp)
  | blockCount + 1 =>
      match advanceToCertificateOrBlock machine current epsilon
          epsilonPositive with
      | .zero root => .zero root
      | .terminal point root nonzero completeWord complete contains =>
          .terminal point root nonzero completeWord complete contains
      | .certified state refines certificate _bits _wordEq =>
          .certified state refines certificate
      | .completedBlock next nextRefines _bits _wordEq nextHistory =>
          match advanceBlocksOrCertificate machine next epsilon
              epsilonPositive blockCount with
          | .zero root => .zero root
          | .terminal point root nonzero completeWord complete contains =>
              .terminal point root nonzero completeWord complete
                (nextRefines.box.contains contains)
          | .certified state refines certificate =>
              .certified state (refines.trans nextRefines) certificate
          | .blocksAdvanced state refines historyGrowth =>
              .blocksAdvanced state (refines.trans nextRefines) (by
                omega)

end CCLActiveCylinderProgress
end FTA
