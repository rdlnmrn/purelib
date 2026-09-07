import mathlib.Tactic.QuotientFreeRing
import CCL.Transcendental.Coherence

/-!
# Operational field laws for coherent CCL names

The declarations in this module compare productive finite processes.  They do
not assign a completed value to a nonterminating CCL.  Exact constants below
are introduced only through the terminating Gaussian-rational constructor.
-/

namespace CCL.OperationalFieldLaws

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev Approximation :=
  CCL.ProgressiveApproximation.Approximation
abbrev NamedEquivalent :=
  CCL.OperationalEquivalence.NamedEquivalent
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed

open RFAP.ConstructiveGaussian.Gaussian
open CCL.TranscendentalCoherence

private def exactCoherent (value : Gaussian) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact value

/-- Three canonical CCL samplers added at one common finite index. -/
def sampledTripleSumApproximation (left middle right : Named) :
    Approximation where
  sample index :=
    ((CCL.ProgressiveSampling.approximation left).sample index +
      (CCL.ProgressiveSampling.approximation middle).sample index) +
        (CCL.ProgressiveSampling.approximation right).sample index
  radiusSq := CCL.FiniteGeometric.quarterRadius 40
  radiusSq_nonneg :=
    CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 40) (by decide)).le
  later_close := by
    intro earlier later order
    let leftSource :=
      CCL.ProgressiveSampling.approximation left
    let middleSource :=
      CCL.ProgressiveSampling.approximation middle
    let rightSource :=
      CCL.ProgressiveSampling.approximation right
    have leftMovement := leftSource.later_close order
    have middleMovement := middleSource.later_close order
    have rightMovement := rightSource.later_close order
    have identity :
        (leftSource.sample later + middleSource.sample later +
              rightSource.sample later) -
            (leftSource.sample earlier + middleSource.sample earlier +
              rightSource.sample earlier) =
          ((leftSource.sample later - leftSource.sample earlier) +
              (middleSource.sample later - middleSource.sample earlier)) +
            (rightSource.sample later - rightSource.sample earlier) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, add_re, add_im] <;> ring1
    rw [identity]
    calc
      normSq
          (((leftSource.sample later - leftSource.sample earlier) +
              (middleSource.sample later - middleSource.sample earlier)) +
            (rightSource.sample later - rightSource.sample earlier)) ≤
        2 *
          (normSq
              ((leftSource.sample later - leftSource.sample earlier) +
                (middleSource.sample later - middleSource.sample earlier)) +
            normSq
              (rightSource.sample later - rightSource.sample earlier)) :=
        normSq_add_le_two _ _
      _ ≤ 2 *
          (2 *
              (CCL.FiniteGeometric.quarterRadius 4 earlier +
                CCL.FiniteGeometric.quarterRadius 4 earlier) +
            CCL.FiniteGeometric.quarterRadius 4 earlier) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add
            ((normSq_add_le_two _ _).trans
              (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                (add_le_add leftMovement middleMovement) (by decide)))
            rightMovement)
          (by decide)
      _ = CCL.FiniteGeometric.quarterRadius 40 earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        ring1
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow 40 current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge 40 current target
  refineIndex_accurate :=
    CCL.FiniteGeometric.firstQuarterBelow_accurate 40
      (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 40) (by decide)).le
  centerBound :=
    2 *
      (2 *
          ((CCL.ProgressiveSampling.approximation left).centerBound +
            (CCL.ProgressiveSampling.approximation middle).centerBound) +
        (CCL.ProgressiveSampling.approximation right).centerBound)
  centerBound_nonneg :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg
            (CCL.ProgressiveSampling.approximation
              left).centerBound_nonneg
            (CCL.ProgressiveSampling.approximation
              middle).centerBound_nonneg))
        (CCL.ProgressiveSampling.approximation
          right).centerBound_nonneg)
  sample_bounded := by
    intro index
    exact (normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add
          ((normSq_add_le_two _ _).trans
            (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add
                ((CCL.ProgressiveSampling.approximation
                  left).sample_bounded index)
                ((CCL.ProgressiveSampling.approximation
                  middle).sample_bounded index))
              (by decide)))
          ((CCL.ProgressiveSampling.approximation
            right).sample_bounded index))
        (by decide))

@[simp] theorem sampledTripleSumApproximation_sample
    (left middle right : Named) (index : Nat) :
    (sampledTripleSumApproximation left middle right).sample index =
      ((CCL.ProgressiveSampling.approximation left).sample index +
        (CCL.ProgressiveSampling.approximation middle).sample index) +
          (CCL.ProgressiveSampling.approximation right).sample
            index :=
  rfl

/-- An actual addition of two approximation-backed coherent names can be
normalized to any finite approximation having their pointwise sum samples. -/
def addToNamed_equivalent_pointwise (left right sum : Approximation)
    (samples : ∀ index,
      sum.sample index = left.sample index + right.sample index) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        left.toNamed right.toNamed)
      sum.toNamed := by
  let leftNamed :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation left
  let rightNamed :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation right
  let canonical := sampledSumApproximation left.toNamed right.toNamed
  have canonicalToSum :
      CCL.OperationalEquivalence.Equivalent canonical sum :=
    pointwiseSumApproximation_respects
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling left)
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling right)
      (by intro index; rfl)
      samples
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by
      simpa only [leftNamed, rightNamed,
        CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
        coherentAdd_toNamed leftNamed rightNamed)
    (approximationEquivalent_toNamed canonicalToSum)

/-- The common equal-index sampler for the two sides of left
distributivity. -/
def sampledLeftDistributiveApproximation
    (left middle right : Named) : Approximation := by
  let leftProduct := sampledProductApproximation left middle
  let rightProduct := sampledProductApproximation left right
  let scale : RFAP.ConstructiveFraction.Rational :=
    2 * (sampledProductErrorScale left middle +
      sampledProductErrorScale left right)
  exact
    { sample := fun index =>
        leftProduct.sample index + rightProduct.sample index
      radiusSq := CCL.FiniteGeometric.quarterRadius scale
      radiusSq_nonneg :=
        CCL.FiniteGeometric.quarterRadius_nonneg
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg
              (sampledProductErrorScale_nonneg left middle)
              (sampledProductErrorScale_nonneg left right)))
      later_close := by
        intro earlier later order
        have leftMovement := leftProduct.later_close order
        have rightMovement := rightProduct.later_close order
        have identity :
            leftProduct.sample later + rightProduct.sample later -
                (leftProduct.sample earlier + rightProduct.sample earlier) =
              (leftProduct.sample later - leftProduct.sample earlier) +
                (rightProduct.sample later - rightProduct.sample earlier) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [sub_re, sub_im, add_re, add_im] <;> ring1
        rw [identity]
        calc
          normSq
              ((leftProduct.sample later - leftProduct.sample earlier) +
                (rightProduct.sample later - rightProduct.sample earlier)) ≤
            2 *
              (normSq
                  (leftProduct.sample later - leftProduct.sample earlier) +
                normSq
                  (rightProduct.sample later - rightProduct.sample earlier)) :=
            normSq_add_le_two _ _
          _ ≤ 2 *
              (CCL.FiniteGeometric.quarterRadius
                  (sampledProductErrorScale left middle) earlier +
                CCL.FiniteGeometric.quarterRadius
                  (sampledProductErrorScale left right) earlier) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add leftMovement rightMovement) (by decide)
          _ = CCL.FiniteGeometric.quarterRadius scale earlier := by
            dsimp only [scale]
            rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
              CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
              CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
            ring1
      refineIndex := fun current target _ =>
        CCL.FiniteGeometric.firstQuarterBelow scale current target
      refineIndex_ge := fun current target _ =>
        CCL.FiniteGeometric.firstQuarterBelow_ge
          scale current target
      refineIndex_accurate :=
        CCL.FiniteGeometric.firstQuarterBelow_accurate scale
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            (add_nonneg
              (sampledProductErrorScale_nonneg left middle)
              (sampledProductErrorScale_nonneg left right)))
      centerBound := 2 *
        (leftProduct.centerBound + rightProduct.centerBound)
      centerBound_nonneg :=
        RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg leftProduct.centerBound_nonneg
            rightProduct.centerBound_nonneg)
      sample_bounded := by
        intro index
        exact (normSq_add_le_two _ _).trans
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add (leftProduct.sample_bounded index)
              (rightProduct.sample_bounded index))
            (by decide)) }

@[simp] theorem sampledLeftDistributiveApproximation_sample
    (left middle right : Named) (index : Nat) :
    (sampledLeftDistributiveApproximation left middle right).sample index =
      (CCL.ProgressiveSampling.approximation left).sample index *
          (CCL.ProgressiveSampling.approximation middle).sample
            index +
        (CCL.ProgressiveSampling.approximation left).sample index *
          (CCL.ProgressiveSampling.approximation right).sample
            index := by
  rfl

/-- Actual stateful addition is operationally commutative. -/
def coherentAdd_comm (left right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add left.name right.name)
      (CCL.ProgressiveTransducer.Named.add right.name left.name) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentAdd_toNamed left right)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (approximationEquivalent_toNamed
        (approximationEquivalentOfSamplesEq
          (sampledSumApproximation left.name right.name)
          (sampledSumApproximation right.name left.name)
          (by
            intro index
            rw [sampledSumApproximation_sample,
              sampledSumApproximation_sample]
            exact RFAP.ConstructiveGaussian.Gaussian.add_comm _ _)))
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (coherentAdd_toNamed right left)))

/-- Actual stateful addition is operationally associative.  Both process
trees normalize to one explicit three-input equal-index sampler. -/
def coherentAdd_assoc (left middle right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (CCL.ProgressiveTransducer.Named.add
          left.name middle.name)
        right.name)
      (CCL.ProgressiveTransducer.Named.add
        left.name
        (CCL.ProgressiveTransducer.Named.add
          middle.name right.name)) := by
  let leftSource :=
    CCL.ProgressiveSampling.approximation left.name
  let rightSource :=
    CCL.ProgressiveSampling.approximation right.name
  let leftMiddle := sampledSumApproximation left.name middle.name
  let middleRight := sampledSumApproximation middle.name right.name
  let triple := sampledTripleSumApproximation left.name middle.name right.name
  let sampledLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      leftSource
  let sampledRight :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      rightSource
  let canonicalLeftMiddle :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      leftMiddle
  let canonicalMiddleRight :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      middleRight
  have normalizeLeft : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (CCL.ProgressiveTransducer.Named.add
          left.name middle.name)
        right.name)
      (CCL.ProgressiveTransducer.Named.add
        canonicalLeftMiddle.name sampledRight.name) :=
    coherentAdd_respects
      (CCL.ProgressiveCoherence.CoherentNamed.add left middle)
      canonicalLeftMiddle right sampledRight
      (coherentAdd_toNamed left middle)
      (named_toSamplingNamed right.name)
  have leftPointwise : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        canonicalLeftMiddle.name sampledRight.name)
      triple.toNamed :=
    addToNamed_equivalent_pointwise leftMiddle rightSource triple
      (by intro index; rfl)
  have normalizeRight : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        left.name
        (CCL.ProgressiveTransducer.Named.add
          middle.name right.name))
      (CCL.ProgressiveTransducer.Named.add
        sampledLeft.name canonicalMiddleRight.name) :=
    coherentAdd_respects left sampledLeft
      (CCL.ProgressiveCoherence.CoherentNamed.add middle right)
      canonicalMiddleRight
      (named_toSamplingNamed left.name)
      (coherentAdd_toNamed middle right)
  have rightPointwise : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        sampledLeft.name canonicalMiddleRight.name)
      triple.toNamed :=
    addToNamed_equivalent_pointwise leftSource middleRight triple (by
      intro index
      rw [sampledTripleSumApproximation_sample,
        sampledSumApproximation_sample]
      exact RFAP.ConstructiveGaussian.Gaussian.add_assoc _ _ _)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    normalizeLeft
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      leftPointwise
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          rightPointwise)
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          normalizeRight)))

/-- Actual stateful multiplication distributes over actual addition.  The
proof normalizes both expression trees to one explicit equal-index sampler. -/
def coherentMul_add_left (left middle right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul left.name
        (CCL.ProgressiveTransducer.Named.add
          middle.name right.name))
      (CCL.ProgressiveTransducer.Named.add
        (CCL.ProgressiveTransducer.Named.mul
          left.name middle.name)
        (CCL.ProgressiveTransducer.Named.mul
          left.name right.name)) := by
  let leftSource :=
    CCL.ProgressiveSampling.approximation left.name
  let middleRight := sampledSumApproximation middle.name right.name
  let leftMiddle := sampledProductApproximation left.name middle.name
  let leftRight := sampledProductApproximation left.name right.name
  let common :=
    sampledLeftDistributiveApproximation left.name middle.name right.name
  let sampledLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      leftSource
  let canonicalMiddleRight :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      middleRight
  let canonicalLeftMiddle :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      leftMiddle
  let canonicalLeftRight :=
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
      leftRight
  have normalizeProduct : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul left.name
        (CCL.ProgressiveTransducer.Named.add
          middle.name right.name))
      (CCL.ProgressiveTransducer.Named.mul
        sampledLeft.name canonicalMiddleRight.name) :=
    coherentMul_respects left sampledLeft
      (CCL.ProgressiveCoherence.CoherentNamed.add middle right)
      canonicalMiddleRight
      (named_toSamplingNamed left.name)
      (coherentAdd_toNamed middle right)
  have productPointwise : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        sampledLeft.name canonicalMiddleRight.name)
      common.toNamed :=
    mulToNamed_equivalent_pointwise leftSource middleRight common (by
      intro index
      rw [sampledLeftDistributiveApproximation_sample,
        sampledSumApproximation_sample]
      exact (RFAP.ConstructiveGaussian.Gaussian.left_distrib _ _ _).symm)
  have normalizeSum : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (CCL.ProgressiveTransducer.Named.mul
          left.name middle.name)
        (CCL.ProgressiveTransducer.Named.mul
          left.name right.name))
      (CCL.ProgressiveTransducer.Named.add
        canonicalLeftMiddle.name canonicalLeftRight.name) :=
    coherentAdd_respects
      (CCL.ProgressiveCoherence.CoherentNamed.mul left middle)
      canonicalLeftMiddle
      (CCL.ProgressiveCoherence.CoherentNamed.mul left right)
      canonicalLeftRight
      (coherentMul_toNamed left middle)
      (coherentMul_toNamed left right)
  have sumPointwise : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        canonicalLeftMiddle.name canonicalLeftRight.name)
      common.toNamed :=
    addToNamed_equivalent_pointwise leftMiddle leftRight common
      (by intro index; rfl)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    normalizeProduct
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      productPointwise
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          sumPointwise)
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          normalizeSum)))

/-- The symmetric right-distributive law follows through finite operational
commutativity and the proved left-distributive normalization. -/
def coherentAdd_mul_right (left middle right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveTransducer.Named.add
          left.name middle.name)
        right.name)
      (CCL.ProgressiveTransducer.Named.add
        (CCL.ProgressiveTransducer.Named.mul left.name right.name)
        (CCL.ProgressiveTransducer.Named.mul
          middle.name right.name)) := by
  let sum := CCL.ProgressiveCoherence.CoherentNamed.add left middle
  let rightLeft :=
    CCL.ProgressiveCoherence.CoherentNamed.mul right left
  let leftRight :=
    CCL.ProgressiveCoherence.CoherentNamed.mul left right
  let rightMiddle :=
    CCL.ProgressiveCoherence.CoherentNamed.mul right middle
  let middleRight :=
    CCL.ProgressiveCoherence.CoherentNamed.mul middle right
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentMul_comm sum right)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (coherentMul_add_left right left middle)
      (coherentAdd_respects rightLeft leftRight rightMiddle middleRight
        (coherentMul_comm right left)
        (coherentMul_comm right middle)))

/-- Adding the terminating exact zero on the right changes no finite
operational observation of a coherent CCL name. -/
def coherentAdd_zero_right (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add input.name
        (CCL.ProgressiveTransducer.Named.exact 0))
      input.name := by
  let zero := exactCoherent 0
  let inputApproximation :=
    CCL.ProgressiveSampling.approximation input.name
  have pointwise : NamedEquivalent
      (sampledSumApproximation input.name zero.name).toNamed
      inputApproximation.toNamed :=
    approximationEquivalent_toNamed
      (approximationEquivalentOfSamplesEq
        (sampledSumApproximation input.name zero.name)
        inputApproximation
        (by
          intro index
          rw [sampledSumApproximation_sample]
          change inputApproximation.sample index + 0 =
            inputApproximation.sample index
          exact RFAP.ConstructiveGaussian.Gaussian.add_zero _))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by
      simpa only [zero, exactCoherent,
        CCL.ProgressiveCoherence.CoherentNamed.exact] using
        coherentAdd_toNamed input zero)
    (CCL.OperationalEquivalence.NamedEquivalent.trans pointwise
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (named_toSamplingNamed input.name)))

/-- Adding the terminating exact zero on the left changes no finite
operational observation of a coherent CCL name. -/
def coherentAdd_zero_left (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (CCL.ProgressiveTransducer.Named.exact 0) input.name)
      input.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentAdd_comm (exactCoherent 0) input)
    (coherentAdd_zero_right input)

private theorem negStateAt
    (process : CCL.ProgressiveEnclosures.Process)
    (start : process.State) (index : Nat) :
    CCL.ProgressiveSampling.stateAt
        (CCL.ProgressiveEnclosures.Process.neg process) start index =
      CCL.ProgressiveSampling.stateAt process start index := by
  induction index with
  | zero => rfl
  | succ index induction =>
      rw [CCL.ProgressiveSampling.stateAt_succ,
        CCL.ProgressiveSampling.stateAt_succ, induction]
      change process.refine _ _ _ = process.refine _ _ _
      rfl

private theorem negSampling_sample (input : CoherentNamed) (index : Nat) :
    (CCL.ProgressiveSampling.approximation
      (CCL.ProgressiveTransducer.Named.neg input.name)).sample index =
      -(CCL.ProgressiveSampling.approximation input.name).sample
        index := by
  change
    CCL.ProgressiveSampling.witnessAt
        (CCL.ProgressiveEnclosures.Process.neg input.name.process)
        input.name.state index =
      -CCL.ProgressiveSampling.witnessAt
        input.name.process input.name.state index
  unfold CCL.ProgressiveSampling.witnessAt
  rw [negStateAt]
  rfl

/-- A coherent CCL name plus its actual stateful negation is operationally
the terminating exact zero name. -/
def coherentAdd_neg_right (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add input.name
        (CCL.ProgressiveTransducer.Named.neg input.name))
      (CCL.ProgressiveTransducer.Named.exact 0) := by
  let negative := CCL.ProgressiveCoherence.CoherentNamed.neg input
  let zeroApproximation :=
    CCL.ProgressiveSampling.approximation
      (CCL.ProgressiveTransducer.Named.exact 0)
  have pointwise : NamedEquivalent
      (sampledSumApproximation input.name negative.name).toNamed
      zeroApproximation.toNamed :=
    approximationEquivalent_toNamed
      (approximationEquivalentOfSamplesEq
        (sampledSumApproximation input.name negative.name)
        zeroApproximation
        (by
          intro index
          rw [sampledSumApproximation_sample,
            show
              (CCL.ProgressiveSampling.approximation
                negative.name).sample index =
                -(CCL.ProgressiveSampling.approximation
                    input.name).sample index by
              simpa only [negative,
                CCL.ProgressiveCoherence.CoherentNamed.neg] using
                negSampling_sample input index]
          change
            (CCL.ProgressiveSampling.approximation input.name).sample
                  index +
                -(CCL.ProgressiveSampling.approximation
                    input.name).sample index = 0
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [add_re, add_im, neg_re, neg_im, zero_re, zero_im] <;>
            ring1))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by
      simpa only [negative,
        CCL.ProgressiveCoherence.CoherentNamed.neg] using
        coherentAdd_toNamed input negative)
    (CCL.OperationalEquivalence.NamedEquivalent.trans pointwise
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (named_toSamplingNamed
          (CCL.ProgressiveTransducer.Named.exact 0))))

/-- Negation on the left gives the same operational zero law. -/
def coherentAdd_neg_left (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.add
        (CCL.ProgressiveTransducer.Named.neg input.name) input.name)
      (CCL.ProgressiveTransducer.Named.exact 0) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentAdd_comm
      (CCL.ProgressiveCoherence.CoherentNamed.neg input) input)
    (coherentAdd_neg_right input)

/-- Multiplication by the terminating exact unit on the right changes no
finite operational observation. -/
def coherentMul_one_right (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul input.name
        (CCL.ProgressiveTransducer.Named.exact 1))
      input.name := by
  let one := exactCoherent 1
  let inputApproximation :=
    CCL.ProgressiveSampling.approximation input.name
  have pointwise : NamedEquivalent
      (sampledProductApproximation input.name one.name).toNamed
      inputApproximation.toNamed :=
    approximationEquivalent_toNamed
      (approximationEquivalentOfSamplesEq
        (sampledProductApproximation input.name one.name)
        inputApproximation
        (by
          intro index
          rw [sampledProductApproximation_sample]
          change inputApproximation.sample index * 1 =
            inputApproximation.sample index
          exact RFAP.ConstructiveGaussian.Gaussian.mul_one _))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by
      simpa only [one, exactCoherent,
        CCL.ProgressiveCoherence.CoherentNamed.exact] using
        coherentMul_toNamed input one)
    (CCL.OperationalEquivalence.NamedEquivalent.trans pointwise
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (named_toSamplingNamed input.name)))

/-- Multiplication by the terminating exact unit on the left changes no
finite operational observation. -/
def coherentMul_one_left (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveTransducer.Named.exact 1) input.name)
      input.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentMul_comm (exactCoherent 1) input)
    (coherentMul_one_right input)

/-- Multiplication by the terminating exact zero on the right is
operationally the terminating exact zero. -/
def coherentMul_zero_right (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul input.name
        (CCL.ProgressiveTransducer.Named.exact 0))
      (CCL.ProgressiveTransducer.Named.exact 0) := by
  let zero := exactCoherent 0
  let zeroApproximation :=
    CCL.ProgressiveSampling.approximation
      (CCL.ProgressiveTransducer.Named.exact 0)
  have pointwise : NamedEquivalent
      (sampledProductApproximation input.name zero.name).toNamed
      zeroApproximation.toNamed :=
    approximationEquivalent_toNamed
      (approximationEquivalentOfSamplesEq
        (sampledProductApproximation input.name zero.name)
        zeroApproximation
        (by
          intro index
          rw [sampledProductApproximation_sample]
          change
            (CCL.ProgressiveSampling.approximation input.name).sample
                index * 0 = 0
          exact RFAP.ConstructiveGaussian.Gaussian.mul_zero _))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by
      simpa only [zero, exactCoherent,
        CCL.ProgressiveCoherence.CoherentNamed.exact] using
        coherentMul_toNamed input zero)
    (CCL.OperationalEquivalence.NamedEquivalent.trans pointwise
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (named_toSamplingNamed
          (CCL.ProgressiveTransducer.Named.exact 0))))

/-- Multiplication by exact zero on the left has the symmetric law. -/
def coherentMul_zero_left (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveTransducer.Named.exact 0) input.name)
      (CCL.ProgressiveTransducer.Named.exact 0) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentMul_comm (exactCoherent 0) input)
    (coherentMul_zero_right input)

/-- The total CCL exponential of an additive inverse is a two-sided
operational multiplicative inverse: this statement only compares finite
process observations and names the exact rational `1` explicitly. -/
def automaticExp_neg_mul (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.named
          (CCL.ProgressiveTransducer.Named.neg input.name))
        (CCL.ProgressiveExpRange.named input.name))
      (CCL.ProgressiveTransducer.Named.exact 1) := by
  let negative := CCL.ProgressiveCoherence.CoherentNamed.neg input
  let sum := CCL.ProgressiveCoherence.CoherentNamed.add negative input
  let zero := exactCoherent 0
  have sumZero : NamedEquivalent sum.name zero.name := by
    simpa only [sum, negative, zero, exactCoherent,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      coherentAdd_neg_left input
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (automaticExp_add negative input)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (automaticExp_respects sum zero sumZero)
      automaticExp_zero)

/-- The symmetric product order is operationally one as well. -/
def automaticExp_mul_neg (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        (CCL.ProgressiveExpRange.named input.name)
        (CCL.ProgressiveExpRange.named
          (CCL.ProgressiveTransducer.Named.neg input.name)))
      (CCL.ProgressiveTransducer.Named.exact 1) := by
  let positiveExp := CCL.TranscendentalCoherence.exp input.name
  let negativeExp :=
    CCL.TranscendentalCoherence.exp
      (CCL.ProgressiveTransducer.Named.neg input.name)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by
      simpa only [positiveExp, negativeExp,
        CCL.TranscendentalCoherence.exp] using
        coherentMul_comm positiveExp negativeExp)
    (automaticExp_neg_mul input)

/-- Exact zero and exact one are not operationally equivalent.  The
separation is witnessed by one finite request at squared tolerance `1 / 2`;
there is no appeal to a completed value. -/
theorem exactZero_not_equivalent_exactOne :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.exact 0)
      (CCL.ProgressiveTransducer.Named.exact 1) → False := by
  intro equivalent
  let comparison := equivalent.compare 0 0 (1 / 2) (by decide)
  have impossible := comparison.close
    (Nat.le_refl comparison.leftIndex)
    (Nat.le_refl comparison.rightIndex)
  have one_lt_half : (1 : RFAP.ConstructiveFraction.Rational) < 1 / 2 := by
    simpa only [
      CCL.ProgressiveSampling.approximation,
      CCL.ProgressiveSampling.witnessAt,
      CCL.ProgressiveSampling.stateAt,
      CCL.ProgressiveEnclosures.Process.exact,
      CCL.ProgressiveTransducer.Named.exact,
      RFAP.ConstructiveGaussian.Gaussian.zero_sub,
      RFAP.ConstructiveGaussian.Gaussian.normSq_neg,
      RFAP.ConstructiveGaussian.Gaussian.normSq_one] using impossible
  exact (by decide : ¬ ((1 : RFAP.ConstructiveFraction.Rational) < 1 / 2))
    one_lt_half

/-- The total finite-request exponential cannot be operationally equivalent
to the terminating exact zero name.  If it were, multiplication by the
independently constructed `exp (-x)` process would make the exact finite names
`0` and `1` operationally equivalent. -/
theorem automaticExp_not_equivalent_zero (input : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveExpRange.named input.name)
      (CCL.ProgressiveTransducer.Named.exact 0) → False := by
  intro expZero
  let negative := CCL.ProgressiveCoherence.CoherentNamed.neg input
  let negativeExp := CCL.TranscendentalCoherence.exp negative.name
  let positiveExp := CCL.TranscendentalCoherence.exp input.name
  let zero := exactCoherent 0
  have productZero : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        negativeExp.name positiveExp.name)
      (CCL.ProgressiveTransducer.Named.exact 0) := by
    exact CCL.OperationalEquivalence.NamedEquivalent.trans
      (coherentMul_respects negativeExp negativeExp positiveExp zero
        (CCL.OperationalEquivalence.NamedEquivalent.refl
          negativeExp.name)
        (by
          simpa only [positiveExp, zero, exactCoherent,
            CCL.TranscendentalCoherence.exp,
            CCL.ProgressiveCoherence.CoherentNamed.exact] using
            expZero))
      (coherentMul_zero_right negativeExp)
  have productOne : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul
        negativeExp.name positiveExp.name)
      (CCL.ProgressiveTransducer.Named.exact 1) := by
    simpa only [negativeExp, positiveExp, negative,
      CCL.TranscendentalCoherence.exp,
      CCL.ProgressiveCoherence.CoherentNamed.neg] using
      automaticExp_neg_mul input
  exact exactZero_not_equivalent_exactOne
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm productZero)
      productOne)

end CCL.OperationalFieldLaws
