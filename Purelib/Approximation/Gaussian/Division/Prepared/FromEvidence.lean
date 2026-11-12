module
public import Purelib.Approximation.Gaussian.Division.Partial.Equivalence
import Purelib.Approximation.Gaussian.Division.Partial.Preparation
public import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Apart.Sampling
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Data.Gaussian.Norm.Separation
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Approximation.Gaussian.Process.Apart.Preparation (ApartState)

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

section
public section

/-!
# Preparing denominators from retained evidence

An original refinement state and its quantitative apartness produce a
prepared denominator and its operational comparison. A supplied certified
apart state reuses an existing whole-ball cache; its absence preserves the
original starting refinement. Retained separated balls and paid comparisons
with an apart anchor provide the same evidence without new observations.
-/

open Purelib.Data.Rat

open Purelib.Data.Gaussian

namespace Purelib.Approximation.Gaussian.Division.Prepared

/-- Build an equivalent prepared denominator from apartness at the exact retained refinement state.

The result keeps the constructed denominator, its whole-ball apartness and
its operational identity to the original channel. A supplied apart state is
consumed literally; the absent request retains the original refinement.
-/
@[expose] def ofEvidence {channel : Coherent.CoherentNamed}
  (state : Name.Coherent.Refinement.State channel)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based channel.name.process state.source))
    (cached : Option (ApartState
      (Gaussian.Process.Based.based channel.name.process state.source) evidence) := none) : Prepared channel :=
  { denominator := Preparation.preparedDenominator state evidence cached
    apart := Preparation.preparedApart state evidence cached
    equivalent := Equivalence.preparedDenominatorEquivalent state evidence cached }

/-- No supplied apart state preserves the complete original evidence preparation. -/
theorem ofEvidence_none {channel : Coherent.CoherentNamed}
    (state : Name.Coherent.Refinement.State channel)
    (evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based channel.name.process state.source)) :
    ofEvidence state evidence none =
      { denominator := Preparation.preparedDenominator state evidence
        apart := Preparation.preparedApart state evidence
        equivalent := Equivalence.preparedDenominatorEquivalent state evidence } := rfl

/-- Prepare an original channel from its supplied cached whole-ball separation without another starting refinement.

The retained apart state uses the same source state as the cached enclosure.
Its whole-ball certificate supplies the existing apartified process directly;
subsequent requests retain that process's ordinary refinement procedure.
-/
@[expose] def ofBall {channel : Coherent.CoherentNamed}
    (state : Name.Coherent.Refinement.State channel)
    (ball : Enclosure.Ball) (readback : ball = channel.name.process.ball state.source)
    (apart : Enclosure.Ball.Apart ball) : Prepared channel := by
  let actual : Enclosure.Ball.Apart (channel.name.process.ball state.source) := readback ▸ apart
  let evidence := Based.possibleApartOfBall channel.name.process state.source actual
  let retained : ApartState
      (Gaussian.Process.Based.based channel.name.process state.source) evidence :=
    { source := Gaussian.Process.Based.BasedState.initial channel.name.process state.source
      wholeBallLower := by
        intro value inside
        change actual.lowerSq / 8 ≤ Norm.Basic.normSq value
        have reduced : actual.lowerSq / 8 ≤ actual.lowerSq := by
          apply (Fraction.Order.Field.div_le_iff_pos (by decide : (0 : Fraction.Rational) < 8)).mpr
          have ordered := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (by decide : (1 : Fraction.Rational) ≤ 8) actual.positive.le
          rewrite [Fraction.Field.mul_one_direct] at ordered
          exact ordered
        exact reduced.trans (actual.lower inside) }
  exact ofEvidence state evidence (some retained)

/-- Cached-ball preparation retains its supplied original source instead of calling the default refinement. -/
theorem ofBall_source {channel : Coherent.CoherentNamed}
    (state : Name.Coherent.Refinement.State channel)
    (ball : Enclosure.Ball) (readback : ball = channel.name.process.ball state.source)
    (apart : Enclosure.Ball.Apart ball) :
    (ofBall state ball readback apart).denominator.name.state.source.source = state.source := rfl

open Purelib

/-- Prepare an original channel from an actual finite comparison with an already guarded original anchor.

The original comparison retains both independent starts and its paid
observations. The anchor's whole-ball lower bound gives the displayed
quarter budget. Original later samples of the requested channel then
satisfy the positive quarter lower bound at that same retained stage;
preparation consumes this evidence without observing either input again.
-/
def ofComparison (channel anchor : Coherent.CoherentNamed)
    (apart : Name.Basic.Named.Apart anchor.name) {leftStart rightStart : Nat}
    (comparison : Gaussian.Equivalence.Comparison (Sampling.approximation channel.name)
      (Sampling.approximation anchor.name) leftStart rightStart (apart.certificate.lowerSq / 4)) :
    Prepared channel := by
  let source := Sampling.approximation channel.name
  let sampled := Coherent.CoherentNamed.ofApproximation source
  let state : Name.Coherent.Refinement.State sampled :=
    { source := comparison.leftIndex
      nextIndex := 0
      persists := by
        intro value possible
        rcases possible with ⟨later, _order, equal⟩
        exact ⟨later, Nat.zero_le _, equal⟩ }
  let lower := apart.certificate.lowerSq / 4
  have positive : 0 < lower := Fraction.Order.Field.div_pos_direct apart.certificate.positive (by decide)
  let evidence : Possible.PossibleApart
      (Gaussian.Process.Based.based sampled.name.process state.source) :=
    { lowerSq := lower
      positive := positive
      lower := by
        intro laterState value possible
        rcases laterState.persists possible with ⟨later, order, equal⟩
        rewrite [equal]
        have close := (comparison.close order (Nat.le_refl comparison.rightIndex)).le
        have anchored := Name.Apart.Sampling.sampled_lower anchor apart comparison.rightIndex
        have budget : Norm.Basic.normSq
            ((Sampling.approximation anchor.name).sample comparison.rightIndex - source.sample later) ≤
            Norm.Basic.normSq
              ((Sampling.approximation anchor.name).sample comparison.rightIndex) / 4 := by
          rewrite [Norm.Bounds.normSq_sub_symm]
          exact close.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
            anchored (by decide : (0 : Fraction.Rational) ≤ (4 : Fraction.Rational)⁻¹))
        exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct anchored
          (by decide : (0 : Fraction.Rational) ≤ (4 : Fraction.Rational)⁻¹)).trans
            (Norm.Bounds.quarter_normSq_le_of_close _ _ budget) }
  let prepared := ofEvidence state evidence
  exact ⟨prepared.denominator, prepared.apart,
    (Gaussian.Sequence.Name.Equivalence.named_toSamplingNamed channel.name).trans prepared.equivalent⟩

/-- Comparison-based preparation retains a fixed thirty-second of the original anchor's lower bound.

The actual candidate comparison pays the quarter bound. Original whole-ball
apartification retains one eighth of that same computed lower bound.
-/
theorem ofComparison_lowerSq (channel anchor : Coherent.CoherentNamed)
    (apart : Name.Basic.Named.Apart anchor.name) {leftStart rightStart : Nat}
    (comparison : Gaussian.Equivalence.Comparison (Sampling.approximation channel.name)
      (Sampling.approximation anchor.name) leftStart rightStart (apart.certificate.lowerSq / 4)) :
    (ofComparison channel anchor apart comparison).apart.certificate.lowerSq =
      (apart.certificate.lowerSq / 4) / 8 := by
  unfold ofComparison ofEvidence
  rfl

end Purelib.Approximation.Gaussian.Division.Prepared

end
