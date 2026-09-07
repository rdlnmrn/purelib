import FTA.CCLZeroDeflatedFamily

/-!
# Keeping the exact zero terminal apart from deflated CCL envelopes

The distinguished zero terminal is represented geometrically by the
singleton rational box at the origin.  Every deflated quotient track starts
in a box that excludes this singleton, so an executable coordinate gap can
be precomputed.  Requesting the same box-plus-cylinder error schedule used
for two nonterminal tracks then proves that the returned projective center
cannot represent zero.
-/

namespace FTA
namespace CCLZeroTerminalSeparation

open CCL
open FTA.CCLActiveMetricProgress
open FTA.CCLActiveMetricTrack
open FTA.CCLChordalEnvelope
open FTA.CCLFiniteTaggedEnvelope
open FTA.CCLZeroDeflatedFamily
open FTA.GaussianZeroDeflation
open FTA.GlobalWinding

abbrev QI := CCL.GaussianRat
abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial QI

/-- Degenerate rational box used only for the exact terminal singleton. -/
def zeroBox : RatBox where
  xLower := 0
  xUpper := 0
  yLower := 0
  yUpper := 0
  x_valid := le_rfl
  y_valid := le_rfl

@[simp] theorem zeroBox_contains_zero : zeroBox.Contains (0 : QI) := by
  simp [zeroBox, RatBox.Contains]

/-- Failure of closed-box membership computes a strict coordinate gap from
the box to the origin singleton. -/
theorem separated_zeroBox_of_excludes_zero
    {box : RatBox} (outside : ¬box.Contains (0 : QI)) :
    box.Separated zeroBox := by
  cases CCLDenominator.outsideSide outside with
  | left separated =>
      have positive : 0 < box.xLower := by simpa using separated
      refine ⟨box.xLower, positive, ?_⟩
      exact Or.inr (Or.inl (by simp [zeroBox]))
  | right separated =>
      have negative : box.xUpper < 0 := by simpa using separated
      refine ⟨-box.xUpper, neg_pos.mpr negative, ?_⟩
      exact Or.inl (by simp [zeroBox])
  | bottom separated =>
      have positive : 0 < box.yLower := by simpa using separated
      refine ⟨box.yLower, positive, ?_⟩
      exact Or.inr (Or.inr (Or.inr (by simp [zeroBox])))
  | top separated =>
      have negative : box.yUpper < 0 := by simpa using separated
      refine ⟨-box.yUpper, neg_pos.mpr negative, ?_⟩
      exact Or.inr (Or.inr (Or.inl (by simp [zeroBox])))

/-- Common-interface exact-zero envelope, used only to invoke the symmetric
finite-envelope separation theorem.  The distinguished terminal tag itself
remains external to the raw CCL word type. -/
def zeroEnvelope : FiniteTaggedEnvelope where
  tag := ⟨[]⟩
  box := zeroBox
  center := Proj.affine 0
  centerValid := Proj.affine_hasNonzeroCoordinate 0
  reference := 0
  referenceInside := zeroBox_contains_zero
  errorSq := 0
  errorSqNonnegative := le_rfl
  certified := by
    rw [chordalSq_eq_zero_of_equivalent
      (Proj.Equivalent.refl (Proj.affine 0))]

end CCLZeroTerminalSeparation
end FTA

namespace FTA.CCLZeroDeflatedFamily.Input

open CCL
open FTA.CCLActiveMetricProgress
open FTA.CCLActiveMetricTrack
open FTA.CCLChordalEnvelope
open FTA.CCLFiniteTaggedEnvelope
open FTA.CCLZeroDeflatedFamily
open FTA.CCLZeroTerminalSeparation
open FTA.GaussianZeroDeflation
open FTA.GlobalWinding

/-- Executable gap between one initially zero-free quotient track and the
distinguished terminal singleton. -/
def originGap
    {p : GaussianPolynomial} (input : CCLZeroDeflatedFamily.Input p)
    (index : Fin (quotient p).natDegree) :
    CCLMetricTrack.RegionGap
      (input.zeroFreeStateAt index).core.numerical.box zeroBox :=
  CCLMetricTrack.RegionGap.compute _ _
    (separated_zeroBox_of_excludes_zero
      (input.zeroFreeStateAt_excludes_zero index))

def originProjectiveGap
    {p : GaussianPolynomial} (input : CCLZeroDeflatedFamily.Input p)
    (index : Fin (quotient p).natDegree) : ℚ :=
  chordalGapSq (input.zeroFreeStateAt index).core.numerical.box zeroBox
    (input.originGap index).coordinateGap

theorem originProjectiveGap_pos
    {p : GaussianPolynomial} (input : CCLZeroDeflatedFamily.Input p)
    (index : Fin (quotient p).natDegree) :
    0 < input.originProjectiveGap index :=
  chordalGapSq_pos _ _ (input.originGap index).positive

/-- The same conservative request scale used for two isolated regions. -/
def originEnvelopeTarget
    {p : GaussianPolynomial} (input : CCLZeroDeflatedFamily.Input p)
    (index : Fin (quotient p).natDegree) : ℚ :=
  min 1 (input.originProjectiveGap index / 64)

theorem originEnvelopeTarget_pos
    {p : GaussianPolynomial} (input : CCLZeroDeflatedFamily.Input p)
    (index : Fin (quotient p).natDegree) :
    0 < input.originEnvelopeTarget index := by
  rw [originEnvelopeTarget, lt_min_iff]
  exact ⟨by norm_num,
    div_pos (input.originProjectiveGap_pos index) (by norm_num)⟩

theorem originEnvelopeTarget_error_le
    {p : GaussianPolynomial} (input : CCLZeroDeflatedFamily.Input p)
    (index : Fin (quotient p).natDegree) :
    2 * (input.originEnvelopeTarget index ^ 2 +
      input.originEnvelopeTarget index) ≤
        input.originProjectiveGap index / 16 := by
  let target := input.originEnvelopeTarget index
  let gap := input.originProjectiveGap index
  have targetPositive : 0 < target := input.originEnvelopeTarget_pos index
  have targetLeOne : target ≤ 1 := min_le_left _ _
  have targetLeGap : target ≤ gap / 64 := min_le_right _ _
  have squareLe : target ^ 2 ≤ target := by nlinarith
  change 2 * (target ^ 2 + target) ≤ gap / 16
  calc
    2 * (target ^ 2 + target) ≤ 4 * target := by linarith
    _ ≤ 4 * (gap / 64) :=
      mul_le_mul_of_nonneg_left targetLeGap (by norm_num)
    _ = gap / 16 := by ring

/-- Result of the coefficient-free request that separates one nonzero
deflated track from the exact zero terminal. -/
inductive OriginRequestResult
    {p : GaussianPolynomial} (input : CCLZeroDeflatedFamily.Input p)
    (index : Fin (quotient p).natDegree) where
  | terminal (point : QI) (quotientRoot : (quotient p).eval point = 0)
      (root : p.eval point = 0) (nonzero : point ≠ 0)
      (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
      (contains : (input.zeroFreeStateAt index).core.numerical.box.Contains
        point) :
      OriginRequestResult input index
  | separated
      (state : CCLActiveMetricTrack.State (quotient p)
        (largeSquareBox (quotient p)))
      (refines : StateRefines state (input.zeroFreeStateAt index))
      (envelope : FiniteTaggedEnvelope)
      (box_eq : envelope.box = state.core.numerical.box)
      (word_eq : envelope.tag.word = state.core.word)
      (accurate : envelope.errorSq ≤
        2 * (input.originEnvelopeTarget index ^ 2 +
          input.originEnvelopeTarget index))
      (centerApart :
        ¬envelope.center.Equivalent (Proj.affine (0 : QI))) :
      OriginRequestResult input index

/-- A finite request either discovers an exact nonzero rational root or
returns a shrinking envelope whose numerical center is projectively distinct
from the exact zero terminal. -/
def requestSeparatedFromZero
    {p : GaussianPolynomial} (input : CCLZeroDeflatedFamily.Input p)
    (index : Fin (quotient p).natDegree) (clearOwnerLabel : Bool) :
    OriginRequestResult input index := by
  let target := input.originEnvelopeTarget index
  let run := input.requestAt index clearOwnerLabel target
    (input.originEnvelopeTarget_pos index)
  match run with
  | .terminal point quotientRoot root nonzero completeWord complete contains =>
      exact .terminal point quotientRoot root nonzero completeWord complete
        contains
  | .nonterminal state refines envelope boxEq wordEq boxAccurate accurate
      excludesZero =>
      let refinedGap := (input.originGap index).refine refines.box
        (RatBox.refines_refl zeroBox)
      have initialGapLe : input.originProjectiveGap index ≤
          chordalGapSq state.core.numerical.box zeroBox
            refinedGap.coordinateGap := by
        simpa only [originProjectiveGap, refinedGap,
          CCLMetricTrack.RegionGap.refine] using
          CCLMetricFamily.chordalGapSq_le_of_refines refines.box
            (RatBox.refines_refl zeroBox)
              (input.originGap index).coordinateGap
      have componentBound := input.originEnvelopeTarget_error_le index
      have envelopeError : envelope.errorSq ≤
          input.originProjectiveGap index / 16 :=
        accurate.trans componentBound
      have initialPositive := input.originProjectiveGap_pos index
      have thinInitial :
          4 * (envelope.errorSq + zeroEnvelope.errorSq) <
            input.originProjectiveGap index := by
        change 4 * (envelope.errorSq + 0) <
          input.originProjectiveGap index
        calc
          4 * (envelope.errorSq + 0) ≤
              4 * (input.originProjectiveGap index / 16) :=
            mul_le_mul_of_nonneg_left (by linarith) (by norm_num)
          _ < input.originProjectiveGap index := by linarith
      have thin : 4 * (envelope.errorSq + zeroEnvelope.errorSq) <
          chordalGapSq state.core.numerical.box zeroBox
            refinedGap.coordinateGap :=
        thinInitial.trans_le initialGapLe
      have apart :=
        FiniteTaggedEnvelope.centers_not_equivalent_of_error_sum_lt_gap
          refinedGap.positive refinedGap.separated boxEq rfl thin
      exact .separated state refines envelope boxEq wordEq accurate (by
        simpa only [zeroEnvelope] using apart)

end FTA.CCLZeroDeflatedFamily.Input
