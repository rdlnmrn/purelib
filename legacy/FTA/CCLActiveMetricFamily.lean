import FTA.CCLActiveObservedEnvelopeProgress
import FTA.CCLMetricFamily

/-!
# Active shrinking envelopes on the exact isolated root family

Every track returned by exact finite isolation receives an initial active CCL
state.  The proposition-level box separation is materialized as one rational
coordinate gap and transported through arbitrary active-state refinements.
One coefficient-free positive target then makes every mixture of phase-local
and completed-history envelopes projectively keep apart.
-/

namespace FTA
namespace CCLActiveMetricFamily

open CCL
open FTA.CCLActiveMetricProgress
open FTA.CCLActiveMetricTrack
open FTA.CCLActiveObservedEnvelopeProgress
open FTA.CCLFiniteTaggedEnvelope
open FTA.AxisSafeCuts
open FTA.LocalExtraction

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Empty-word active state attached to one exactly isolated winding-one
track. -/
def initialStateAt
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (index : Fin count) : State p (RatBox.symmetric R hR) :=
  CCLActiveMetricProgress.initialState (output.trackAt index)

theorem initialStateAt_word_nil
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (index : Fin count) : (initialStateAt output index).core.word = [] :=
  rfl

theorem initialStateAt_box
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (index : Fin count) :
    (initialStateAt output index).core.numerical.box =
      (output.trackAt index).initial.box :=
  CCLActiveMetricProgress.initialState_box (output.trackAt index)

/-- Executable rational separation gap inherited from exact isolation. -/
def initialGap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (left right : Fin count) (distinct : left ≠ right) :
    CCLMetricTrack.RegionGap (initialStateAt output left).core.numerical.box
      (initialStateAt output right).core.numerical.box := by
  apply CCLMetricTrack.RegionGap.compute
  rw [initialStateAt_box, initialStateAt_box]
  exact output.trackAt_pairwiseSeparated left right distinct

/-- Preserve the initial pair gap through independent active refinements. -/
def refinedGap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (leftIndex rightIndex : Fin count) (distinct : leftIndex ≠ rightIndex)
    {left right : State p (RatBox.symmetric R hR)}
    (leftRefines : StateRefines left (initialStateAt output leftIndex))
    (rightRefines : StateRefines right (initialStateAt output rightIndex)) :
    CCLMetricTrack.RegionGap left.core.numerical.box
      right.core.numerical.box :=
  (initialGap output leftIndex rightIndex distinct).refine leftRefines.box
    rightRefines.box

/-- Initial squared projective gap computed entirely from rational box data. -/
def initialProjectiveGap
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (left right : Fin count) (distinct : left ≠ right) : ℚ :=
  CCLChordalEnvelope.chordalGapSq
    (initialStateAt output left).core.numerical.box
    (initialStateAt output right).core.numerical.box
    (initialGap output left right distinct).coordinateGap

theorem initialProjectiveGap_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (left right : Fin count) (distinct : left ≠ right) :
    0 < initialProjectiveGap output left right distinct :=
  CCLChordalEnvelope.chordalGapSq_pos _ _
    (initialGap output left right distinct).positive

/-- Per-pair positive request.  `min 1` gives the square-free implication
`t² ≤ t`, while division by `64` leaves a strict factor-two separation
margin after both envelopes and both triangle estimates are counted. -/
def pairEnvelopeTarget
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (left right : Fin count) (distinct : left ≠ right) : ℚ :=
  min 1 (initialProjectiveGap output left right distinct / 64)

theorem pairEnvelopeTarget_pos
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (left right : Fin count) (distinct : left ≠ right) :
    0 < pairEnvelopeTarget output left right distinct := by
  rw [pairEnvelopeTarget, lt_min_iff]
  exact ⟨by norm_num,
    div_pos (initialProjectiveGap_pos output left right distinct)
      (by norm_num)⟩

theorem pairEnvelopeTarget_error_le
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (left right : Fin count) (distinct : left ≠ right) :
    2 * (pairEnvelopeTarget output left right distinct ^ 2 +
      pairEnvelopeTarget output left right distinct) ≤
        initialProjectiveGap output left right distinct / 16 := by
  let target := pairEnvelopeTarget output left right distinct
  let gap := initialProjectiveGap output left right distinct
  have targetPositive : 0 < target :=
    pairEnvelopeTarget_pos output left right distinct
  have targetLeOne : target ≤ 1 := min_le_left _ _
  have targetLeGap : target ≤ gap / 64 := min_le_right _ _
  have squareLe : target ^ 2 ≤ target := by
    nlinarith
  change 2 * (target ^ 2 + target) ≤ gap / 16
  calc
    2 * (target ^ 2 + target) ≤ 4 * target := by linarith
    _ ≤ 4 * (gap / 64) :=
      mul_le_mul_of_nonneg_left targetLeGap (by norm_num)
    _ = gap / 16 := by ring

/-- The initial projective gap can only improve when the two winding boxes
are refined. -/
theorem initialProjectiveGap_le_refined
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (leftIndex rightIndex : Fin count) (distinct : leftIndex ≠ rightIndex)
    {left right : State p (RatBox.symmetric R hR)}
    (leftRefines : StateRefines left (initialStateAt output leftIndex))
    (rightRefines : StateRefines right (initialStateAt output rightIndex)) :
    initialProjectiveGap output leftIndex rightIndex distinct ≤
      CCLChordalEnvelope.chordalGapSq left.core.numerical.box
        right.core.numerical.box
        (refinedGap output leftIndex rightIndex distinct leftRefines
          rightRefines).coordinateGap := by
  simpa only [initialProjectiveGap, refinedGap,
    CCLMetricTrack.RegionGap.refine] using
    CCLMetricFamily.chordalGapSq_le_of_refines leftRefines.box
      rightRefines.box (initialGap output leftIndex rightIndex distinct).coordinateGap

/-- Request-facing keep-apart theorem for any mixed pair of active finite
envelopes returned at the precomputed per-pair target. -/
theorem centers_not_equivalent_of_pair_target
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (leftIndex rightIndex : Fin count) (distinct : leftIndex ≠ rightIndex)
    {left right : State p (RatBox.symmetric R hR)}
    (leftRefines : StateRefines left (initialStateAt output leftIndex))
    (rightRefines : StateRefines right (initialStateAt output rightIndex))
    {leftEnvelope rightEnvelope : FiniteTaggedEnvelope}
    (leftBox : leftEnvelope.box = left.core.numerical.box)
    (rightBox : rightEnvelope.box = right.core.numerical.box)
    (leftAccurate : leftEnvelope.errorSq ≤
      2 * (pairEnvelopeTarget output leftIndex rightIndex distinct ^ 2 +
        pairEnvelopeTarget output leftIndex rightIndex distinct))
    (rightAccurate : rightEnvelope.errorSq ≤
      2 * (pairEnvelopeTarget output leftIndex rightIndex distinct ^ 2 +
        pairEnvelopeTarget output leftIndex rightIndex distinct)) :
    ¬leftEnvelope.center.Equivalent rightEnvelope.center := by
  let target := pairEnvelopeTarget output leftIndex rightIndex distinct
  let initialGapSq := initialProjectiveGap output leftIndex rightIndex distinct
  let gap := refinedGap output leftIndex rightIndex distinct leftRefines
    rightRefines
  have componentBound := pairEnvelopeTarget_error_le output leftIndex
    rightIndex distinct
  have leftError : leftEnvelope.errorSq ≤ initialGapSq / 16 :=
    leftAccurate.trans componentBound
  have rightError : rightEnvelope.errorSq ≤ initialGapSq / 16 :=
    rightAccurate.trans componentBound
  have initialPositive : 0 < initialGapSq :=
    initialProjectiveGap_pos output leftIndex rightIndex distinct
  have thinInitial :
      4 * (leftEnvelope.errorSq + rightEnvelope.errorSq) < initialGapSq := by
    calc
      4 * (leftEnvelope.errorSq + rightEnvelope.errorSq) ≤
          4 * (initialGapSq / 16 + initialGapSq / 16) :=
        mul_le_mul_of_nonneg_left (add_le_add leftError rightError)
          (by norm_num)
      _ < initialGapSq := by linarith
  have thin : 4 * (leftEnvelope.errorSq + rightEnvelope.errorSq) <
      CCLChordalEnvelope.chordalGapSq left.core.numerical.box
        right.core.numerical.box gap.coordinateGap :=
    thinInitial.trans_le
      (initialProjectiveGap_le_refined output leftIndex rightIndex distinct
        leftRefines rightRefines)
  apply FiniteTaggedEnvelope.centers_not_equivalent_of_error_sum_lt_gap
    gap.positive gap.separated leftBox rightBox thin

/-- Active controller specialized to one track of the exact isolated family. -/
def machineAt
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (index : Fin count) (clearOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    Machine p R hR where
  track := output.trackAt index
  clearOwnerLabel := clearOwnerLabel
  squarefree := squarefree
  degreeNonzero := degreeNonzero
  zeroNonzero := zeroNonzero
  eliminationDegree := D
  elimination := elimination

/-- Data-bearing result of applying the computed pair target independently to
two distinct tracks. -/
inductive PairRequestResult
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (leftIndex rightIndex : Fin count) (distinct : leftIndex ≠ rightIndex)
    where
  | leftZero (root : p.eval 0 = 0) :
      PairRequestResult output leftIndex rightIndex distinct
  | leftTerminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : (initialStateAt output leftIndex).core.numerical.box.Contains
        point) :
      PairRequestResult output leftIndex rightIndex distinct
  | rightZero (root : p.eval 0 = 0) :
      PairRequestResult output leftIndex rightIndex distinct
  | rightTerminal (point : QI) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : (initialStateAt output rightIndex).core.numerical.box.Contains
        point) :
      PairRequestResult output leftIndex rightIndex distinct
  | separated
      (left right : State p (RatBox.symmetric R hR))
      (leftRefines : StateRefines left (initialStateAt output leftIndex))
      (rightRefines : StateRefines right (initialStateAt output rightIndex))
      (leftEnvelope rightEnvelope : FiniteTaggedEnvelope)
      (leftBox : leftEnvelope.box = left.core.numerical.box)
      (rightBox : rightEnvelope.box = right.core.numerical.box)
      (leftWord : leftEnvelope.tag.word = left.core.word)
      (rightWord : rightEnvelope.tag.word = right.core.word)
      (leftAccurate : leftEnvelope.errorSq ≤
        2 * (pairEnvelopeTarget output leftIndex rightIndex distinct ^ 2 +
          pairEnvelopeTarget output leftIndex rightIndex distinct))
      (rightAccurate : rightEnvelope.errorSq ≤
        2 * (pairEnvelopeTarget output leftIndex rightIndex distinct ^ 2 +
          pairEnvelopeTarget output leftIndex rightIndex distinct))
      (centersApart :
        ¬leftEnvelope.center.Equivalent rightEnvelope.center) :
      PairRequestResult output leftIndex rightIndex distinct

/-- Execute the two independent total requests and attach the proved
keep-apart certificate whenever both tracks remain nonterminal. -/
def requestPair
    {p : GaussianPolynomial} {R : ℚ} {hR : 0 ≤ R} {count : ℕ}
    (output : ExactIsolation.Output p (RatBox.symmetric R hR) count)
    (leftIndex rightIndex : Fin count) (distinct : leftIndex ≠ rightIndex)
    (leftOwnerLabel rightOwnerLabel : Bool)
    (squarefree : GaussianSquarefreeCertificate p)
    (degreeNonzero : p.toPolynomial.natDegree ≠ 0)
    (zeroNonzero : p.eval 0 ≠ 0)
    {D : ℕ} (elimination : AxisEliminationCertificate p D) :
    PairRequestResult output leftIndex rightIndex distinct := by
  let target := pairEnvelopeTarget output leftIndex rightIndex distinct
  let targetPositive := pairEnvelopeTarget_pos output leftIndex rightIndex
    distinct
  let leftMachine := machineAt output leftIndex leftOwnerLabel squarefree
    degreeNonzero zeroNonzero elimination
  let rightMachine := machineAt output rightIndex rightOwnerLabel squarefree
    degreeNonzero zeroNonzero elimination
  let leftRun := requestFinite leftMachine (initialStateAt output leftIndex)
    target targetPositive
  match leftRun with
  | .zero root => exact .leftZero root
  | .terminal point root nonzero completeWord complete contains =>
      exact .leftTerminal point root nonzero completeWord complete contains
  | .nonterminal left leftRefines leftEnvelope leftBox leftWord
      leftBoxAccurate leftAccurate =>
      let rightRun := requestFinite rightMachine
        (initialStateAt output rightIndex) target targetPositive
      match rightRun with
      | .zero root => exact .rightZero root
      | .terminal point root nonzero completeWord complete contains =>
          exact .rightTerminal point root nonzero completeWord complete contains
      | .nonterminal right rightRefines rightEnvelope rightBox rightWord
          rightBoxAccurate rightAccurate =>
          exact .separated left right leftRefines rightRefines leftEnvelope
            rightEnvelope leftBox rightBox leftWord rightWord leftAccurate
              rightAccurate
              (centers_not_equivalent_of_pair_target output leftIndex
                rightIndex distinct leftRefines rightRefines leftBox rightBox
                  leftAccurate rightAccurate)

end CCLActiveMetricFamily
end FTA
