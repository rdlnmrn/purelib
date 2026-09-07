import mathlib.Tactic.QuotientFreeRing
import CCL.Progressive.Sampling

/-!
# Finite operational equivalence of progressive CCL approximations

Analytic laws such as `exp(x + y) = exp(x) * exp(y)` must not be expressed by
first adjoining completed non-rational values.  This module supplies the
finite-request replacement for the approximation sidechannels underlying CCL
names.  From any two current finite indices and any displayed positive
rational tolerance, an equivalence computes later indices and proves that
every still-later pair of displayed samples has smaller squared separation
than the requested tolerance.

All quantifiers range over natural indices and displayed Gaussian rationals.
No limit, completion, or collection of all values is introduced.
-/

namespace CCL.OperationalEquivalence

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev Named := CCL.ProgressiveTransducer.Named

open RFAP.ConstructiveGaussian.Gaussian

/-- One finite tail comparison below a displayed squared tolerance. -/
structure Comparison (left right : Approximation)
    (leftStart rightStart : Nat) (target : Coordinate) where
  leftIndex : Nat
  rightIndex : Nat
  left_ge : leftStart ≤ leftIndex
  right_ge : rightStart ≤ rightIndex
  close : ∀ {leftLater rightLater : Nat},
    leftIndex ≤ leftLater → rightIndex ≤ rightLater →
      normSq (left.sample leftLater - right.sample rightLater) < target

/-- Two approximation sidechannels have the same finite operational value
when their displayed tails can be synchronized below every positive rational
squared tolerance. -/
structure Equivalent (left right : Approximation) where
  compare : ∀ (leftStart rightStart : Nat) (target : Coordinate),
    0 < target → Comparison left right leftStart rightStart target

theorem quarter_pos {target : Coordinate} (positive : 0 < target) :
    0 < target / 4 :=
  RFAP.ConstructiveFraction.div_pos_direct positive (by decide)

private theorem center_sub_eq_neg_sub (center value : Gaussian) :
    center - value = -(value - center) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1

private theorem four_quarters (target : Coordinate) :
    2 * (target / 4 + target / 4) = target := by
  have quarterSum : target / 4 + target / 4 = target / 2 := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      (show (4 : Coordinate) ≠ 0 by decide)
    calc
      (target / 4 + target / 4) * 4 =
          (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
      _ = target + target := by
        rw [show target / 4 * 4 = target from
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 4 (by decide)]
      _ = target * 2 := by ring1
      _ = ((target / 2) * 2) * 2 := by
        rw [show target / 2 * 2 = target from
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2 (by decide)]
      _ = (target / 2) * (2 * 2) :=
        RFAP.ConstructiveFraction.mul_assoc (target / 2) 2 2
      _ = (target / 2) * 4 := by
        rw [show (2 : Coordinate) * 2 = 4 by decide]
  rw [quarterSum, RFAP.ConstructiveFraction.mul_comm]
  exact RFAP.ConstructiveFraction.div_mul_cancel_of_ne target 2 (by decide)

/-- Every approximation is operationally equivalent to itself. -/
def Equivalent.refl (approximation : Approximation) :
    Equivalent approximation approximation where
  compare := by
    intro leftStart rightStart target positive
    let start := max leftStart rightStart
    let index := approximation.refineIndex start (target / 4)
      (quarter_pos positive)
    have radiusSmall : approximation.radiusSq index < target / 4 :=
      approximation.refineIndex_accurate start (target / 4)
        (quarter_pos positive)
    exact
      { leftIndex := index
        rightIndex := index
        left_ge := (Nat.le_max_left _ _).trans
          (approximation.refineIndex_ge start (target / 4)
            (quarter_pos positive))
        right_ge := (Nat.le_max_right _ _).trans
          (approximation.refineIndex_ge start (target / 4)
            (quarter_pos positive))
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftClose := approximation.later_close leftOrder
          have rightClose := approximation.later_close rightOrder
          have rightClose' :
              normSq
                (approximation.sample index -
                  approximation.sample rightLater) ≤
                approximation.radiusSq index := by
            rw [center_sub_eq_neg_sub, normSq_neg]
            exact rightClose
          calc
            normSq
                (approximation.sample leftLater -
                  approximation.sample rightLater) ≤
                2 * (normSq
                    (approximation.sample leftLater -
                      approximation.sample index) +
                  normSq
                    (approximation.sample index -
                      approximation.sample rightLater)) :=
              normSq_sub_le_via _ _ _
            _ ≤ 2 *
                (approximation.radiusSq index +
                  approximation.radiusSq index) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (add_le_add leftClose rightClose') (by decide)
            _ < 2 * (target / 4 + target / 4) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  radiusSmall radiusSmall)
            _ = target := four_quarters target }

/-- Operational equivalence is symmetric. -/
def Equivalent.symm {left right : Approximation}
    (equivalent : Equivalent left right) : Equivalent right left where
  compare := by
    intro rightStart leftStart target positive
    let comparison := equivalent.compare leftStart rightStart target positive
    exact
      { leftIndex := comparison.rightIndex
        rightIndex := comparison.leftIndex
        left_ge := comparison.right_ge
        right_ge := comparison.left_ge
        close := by
          intro rightLater leftLater rightOrder leftOrder
          have close := comparison.close leftOrder rightOrder
          have identity :
              right.sample rightLater - left.sample leftLater =
                -(left.sample leftLater - right.sample rightLater) := by
            apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
              simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
          rw [identity, normSq_neg]
          exact close }

/-- Operational equivalence is transitive by sequentially synchronizing the
middle approximation. -/
def Equivalent.trans {left middle right : Approximation}
    (leftMiddle : Equivalent left middle)
    (middleRight : Equivalent middle right) : Equivalent left right where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget := quarter_pos positive
    let first := leftMiddle.compare leftStart 0 smallTarget smallPositive
    let second := middleRight.compare first.rightIndex rightStart
      smallTarget smallPositive
    exact
      { leftIndex := first.leftIndex
        rightIndex := second.rightIndex
        left_ge := first.left_ge
        right_ge := second.right_ge
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftClose :
              normSq
                (left.sample leftLater -
                  middle.sample second.leftIndex) < smallTarget :=
            first.close leftOrder second.left_ge
          have rightClose :
              normSq
                (middle.sample second.leftIndex -
                  right.sample rightLater) < smallTarget :=
            second.close (Nat.le_refl _) rightOrder
          calc
            normSq (left.sample leftLater - right.sample rightLater) ≤
                2 * (normSq
                    (left.sample leftLater -
                      middle.sample second.leftIndex) +
                  normSq
                    (middle.sample second.leftIndex -
                      right.sample rightLater)) :=
              normSq_sub_le_via _ _ _
            _ < 2 * (smallTarget + smallTarget) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  leftClose rightClose)
            _ = target := by
              dsimp only [smallTarget]
              exact four_quarters target }

/-- Two finite approximation programs which display one and the same exact
Gaussian rational at every index are operationally equivalent. -/
def Equivalent.of_constant_samples (left right : Approximation)
    (value : Gaussian)
    (leftSample : ∀ index, left.sample index = value)
    (rightSample : ∀ index, right.sample index = value) :
    Equivalent left right where
  compare := by
    intro leftStart rightStart target positive
    exact
      { leftIndex := leftStart
        rightIndex := rightStart
        left_ge := Nat.le_refl _
        right_ge := Nat.le_refl _
        close := by
          intro leftLater rightLater _ _
          rw [leftSample leftLater, rightSample rightLater, sub_self,
            normSq_zero]
          exact positive }

/-- Operational equality of finite-request arithmetic CCL programs is equality
of the nested finite witness approximations calculated from their current
states.  This definition compares only displayed rational samples and rational
error requests; it does not quantify over completed values. -/
def NamedEquivalent (left right : Named) :=
  Equivalent
    (CCL.ProgressiveSampling.approximation left)
    (CCL.ProgressiveSampling.approximation right)

/-! ## The approximation-to-CCL round trip -/

/-- The index of the original approximation selected by the canonical
sampling path of the CCL name generated from it. -/
def emittedSampleIndex (approximation : Approximation) (index : Nat) : Nat :=
  CCL.ProgressiveSampling.stateAt approximation.toProcess
    (show approximation.toProcess.State from (0 : Nat)) index

theorem emittedSampleIndex_step (approximation : Approximation) (index : Nat) :
    emittedSampleIndex approximation index ≤
      emittedSampleIndex approximation (index + 1) := by
  change emittedSampleIndex approximation index ≤
    approximation.refineIndex (emittedSampleIndex approximation index)
      (CCL.ProgressiveSampling.refinementTarget (index + 1))
      (CCL.ProgressiveSampling.refinementTarget_pos (index + 1))
  exact approximation.refineIndex_ge _ _ _

theorem emittedSampleIndex_mono (approximation : Approximation)
    {earlier later : Nat} (order : earlier ≤ later) :
    emittedSampleIndex approximation earlier ≤
      emittedSampleIndex approximation later := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  clear order
  induction extra with
  | zero => exact Nat.le_refl _
  | succ extra inductionHypothesis =>
      exact inductionHypothesis.trans (by
        simpa only [Nat.add_assoc] using
          emittedSampleIndex_step approximation (earlier + extra))

theorem emittedSample_eq (approximation : Approximation) (index : Nat) :
    (CCL.ProgressiveSampling.approximation
      approximation.toNamed).sample index =
        approximation.sample (emittedSampleIndex approximation index) := by
  change approximation.sample
      (CCL.ProgressiveSampling.stateAt approximation.toProcess
        (show approximation.toProcess.State from (0 : Nat)) index) =
    approximation.sample (emittedSampleIndex approximation index)
  rfl

/-- Passing a finite approximation through the ordinary productive CCL
controller and then sampling that CCL name preserves its operational value.
The controller may choose different displayed indices, but all comparisons
remain finite and are synchronized through one explicitly accurate emitted
index. -/
def Equivalent.toNamed_sampling (approximation : Approximation) :
    Equivalent
      (CCL.ProgressiveSampling.approximation
        approximation.toNamed)
      approximation where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget := quarter_pos positive
    let leftIndex := CCL.FiniteGeometric.firstQuarterBelow
      1 leftStart smallTarget
    let baseIndex := emittedSampleIndex approximation leftIndex
    let rightIndex := max rightStart baseIndex
    have emittedRadius :
        approximation.radiusSq baseIndex <
          CCL.ProgressiveSampling.refinementTarget leftIndex := by
      exact CCL.ProgressiveSampling.stateAt_accurate
        approximation.toProcess
          (show approximation.toProcess.State from (0 : Nat)) leftIndex
    have targetRadius :
        CCL.ProgressiveSampling.refinementTarget leftIndex <
          smallTarget := by
      exact CCL.FiniteGeometric.firstQuarterBelow_accurate
        1 (by decide) leftStart smallTarget smallPositive
    have radiusSmall : approximation.radiusSq baseIndex < smallTarget :=
      emittedRadius.trans targetRadius
    exact
      { leftIndex := leftIndex
        rightIndex := rightIndex
        left_ge := CCL.FiniteGeometric.firstQuarterBelow_ge
          1 leftStart smallTarget
        right_ge := Nat.le_max_left _ _
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have baseToLeft : baseIndex ≤
              emittedSampleIndex approximation leftLater :=
            emittedSampleIndex_mono approximation leftOrder
          have baseToRight : baseIndex ≤ rightLater :=
            (Nat.le_max_right rightStart baseIndex).trans rightOrder
          have leftClose := approximation.later_close baseToLeft
          have rightCloseForward := approximation.later_close baseToRight
          have rightClose :
              normSq
                  (approximation.sample baseIndex -
                    approximation.sample rightLater) ≤
                approximation.radiusSq baseIndex := by
            have identity :
                approximation.sample baseIndex -
                    approximation.sample rightLater =
                  -(approximation.sample rightLater -
                    approximation.sample baseIndex) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [identity, normSq_neg]
            exact rightCloseForward
          rw [emittedSample_eq]
          calc
            normSq
                (approximation.sample
                    (emittedSampleIndex approximation leftLater) -
                  approximation.sample rightLater) ≤
              2 * (normSq
                  (approximation.sample
                      (emittedSampleIndex approximation leftLater) -
                    approximation.sample baseIndex) +
                normSq
                  (approximation.sample baseIndex -
                    approximation.sample rightLater)) :=
                normSq_sub_le_via _ _ _
            _ ≤ 2 * (approximation.radiusSq baseIndex +
                approximation.radiusSq baseIndex) :=
              RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (add_le_add leftClose rightClose) (by decide)
            _ < 2 * (smallTarget + smallTarget) :=
              RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                (by decide)
                (RFAP.ConstructiveFraction.add_lt_add_direct
                  radiusSmall radiusSmall)
            _ = target := by
              dsimp only [smallTarget]
              exact four_quarters target }

/-- Lift an operational equivalence between two finite approximations through
their ordinary productive CCL wrappers.  This bridge belongs to the core
operational layer: it uses only the two sampler equivalences and does not
depend on any transcendental operation. -/
def Equivalent.toNamed {left right : Approximation}
    (equivalent : Equivalent left right) :
    NamedEquivalent left.toNamed right.toNamed :=
  Equivalent.trans
    (Equivalent.toNamed_sampling left)
    (Equivalent.trans equivalent
      (Equivalent.symm (Equivalent.toNamed_sampling right)))

namespace NamedEquivalent

def refl (name : Named) : NamedEquivalent name name := Equivalent.refl _

def symm {left right : Named} (equivalent : NamedEquivalent left right) :
    NamedEquivalent right left :=
  Equivalent.symm equivalent

def trans {left middle right : Named}
    (leftMiddle : NamedEquivalent left middle)
    (middleRight : NamedEquivalent middle right) :
    NamedEquivalent left right :=
  Equivalent.trans leftMiddle middleRight

end NamedEquivalent

end CCL.OperationalEquivalence
