import FTA.CCLCanonicalEvent
import FTA.CCLCompletedBlockContraction
import FTA.CCLMetricTrack

/-!
# Completed-block contraction for every persistent metric state

The completed-history envelope depends only on the represented raw word.  It
therefore applies to both open-cell and path-constrained persistence, without
requiring the stronger whole-box wrapping checkpoint invariant.
-/

namespace FTA
namespace CCLCompletedMetricContraction

open CCL
open FTA.CCLCanonicalEvent
open FTA.CCLCompletedBlockContraction
open FTA.CCLMetricTrack

abbrev GaussianPolynomial :=
  FTA.ComputablePolynomial.DensePolynomial CCL.GaussianRat

/-- A metric successor from a completed sector, with the completed-history
envelope installed immediately and the phase-indexed algebraic support carried
forward. -/
inductive CompletedMetricStepResult
    {p : GaussianPolynomial} {ambient : RatBox}
    (current : CCLMetricTrack.State p ambient) where
  | zero (root : p.eval 0 = 0)
  | terminal (point : CCL.GaussianRat) (root : p.eval point = 0)
      (nonzero : point ≠ 0) (completeWord : Prefix.Word)
      (complete : completeWord = RationalEncoder.encode point nonzero)
  | next (bit : Bool) (state : CCLMetricTrack.State p ambient)
      (refines : state.Refines current)
      (word_eq : state.core.word = current.core.word ++ [bit])
      (phase_eq : (RawParser.parse state.core.word).phase = .loopUnary 0)
      (history_length_eq :
        (RawParser.parse state.core.word).history.length =
          (RawParser.parse current.core.word).history.length + 1)
      (radiusSq_le_history :
        state.cylinder.radiusSq ≤ historyRadiusSq state.core.word)
      (radiusSq_le_half_previous :
        state.cylinder.radiusSq ≤
          (1 / 2 : ℚ) * historyRadiusSq current.core.word)
      (canonical : CompletedSectorControllerCanonicalData state.core.numerical
        state.core.word)
      (coupledError : state.coupling.errorSq ≤
        2 * (current.core.numerical.box.diagonalSq +
          (1 / 2 : ℚ) * historyRadiusSq current.core.word))

/-- Tighten any persistent metric step taken from a completed sector.  The
construction is independent of whether the represented witness persists in
an open sign cell or on a lower-dimensional rational path. -/
def tightenCompletedStep
    {p : GaussianPolynomial} {ambient : RatBox}
    {current : CCLMetricTrack.State p ambient}
    {kind : RawParser.BlockKind} {exponent : ℕ} {first second : Bool}
    (phase : (RawParser.parse current.core.word).phase =
      .sector kind exponent (.two first second)) :
    CCLMetricTrack.StepResult current → CompletedMetricStepResult current
  | .zero root => .zero root
  | .terminal point root nonzero completeWord complete =>
      .terminal point root nonzero completeWord complete
  | .next bit state stateRefines wordEq => by
      let certificate : state.CylinderContraction
          (historyRadiusSq state.core.word) :=
        { cylinder := historyEnvelope state.core.word
          cylinder_word := rfl
          radiusSq_le := le_rfl }
      let contracted := state.contractWith certificate
      have contractedWord : contracted.contracted.core.word =
          current.core.word ++ [bit] := contracted.word_eq.trans wordEq
      have nextPhase :
          (RawParser.parse contracted.contracted.core.word).phase =
            .loopUnary 0 := by
        rw [contracted.word_eq, wordEq, show RawParser.parse
            (current.core.word ++ [bit]) =
              RawParser.step (RawParser.parse current.core.word) bit by
                simp [RawParser.parse, List.foldl_append],
          RawParserSemantics.step_eq_completeSector
            (RawParser.parse current.core.word) kind exponent first second bit
              phase]
        rfl
      have historyLength :
          (RawParser.parse contracted.contracted.core.word).history.length =
            (RawParser.parse current.core.word).history.length + 1 := by
        rw [contracted.word_eq, wordEq]
        exact completedSector_append_history_length current.core.word bit phase
      have radiusHistory : contracted.contracted.cylinder.radiusSq ≤
          historyRadiusSq contracted.contracted.core.word := by
        rw [contracted.word_eq]
        exact contracted.radiusSq_le
      have radiusHalf : contracted.contracted.cylinder.radiusSq ≤
          (1 / 2 : ℚ) * historyRadiusSq current.core.word := by
        calc
          contracted.contracted.cylinder.radiusSq ≤
              historyRadiusSq state.core.word := contracted.radiusSq_le
          _ = historyRadiusSq (current.core.word ++ [bit]) := by rw [wordEq]
          _ = (1 / 2 : ℚ) * historyRadiusSq current.core.word :=
            historyRadiusSq_append_completedSector current.core.word bit phase
      have contractedRefines := contracted.refines.trans stateRefines
      have nextCanonical : CompletedSectorControllerCanonicalData
          contracted.contracted.core.numerical
          contracted.contracted.core.word := by
        intro completed
        rcases completed with
          ⟨nextKind, nextExponent, nextFirst, nextSecond, nextCompleted⟩
        rw [nextPhase] at nextCompleted
        contradiction
      have diagonalBound :
          contracted.contracted.core.numerical.box.diagonalSq ≤
            current.core.numerical.box.diagonalSq :=
        CCLClearanceExclusion.RatBox.diagonalSq_le_of_refines
          contractedRefines.1
      have coupledError := contracted.contracted.coupling.errorSq_le
        diagonalBound radiusHalf
      exact .next bit contracted.contracted contractedRefines contractedWord
        nextPhase historyLength radiusHistory radiusHalf nextCanonical
          coupledError

end CCLCompletedMetricContraction
end FTA
