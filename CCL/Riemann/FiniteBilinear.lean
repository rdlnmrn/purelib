import CCL.Riemann.FiniteEnergy
import CCL.Riemann.FinitePolygonStokes
import CCL.Riemann.OperationalQuotients

/-!
# Finite boundary cancellation for the first Riemann bilinear relation

Cutting the finite surface model produces finitely many oriented edge pairs.
Each reverse edge carries its own persistent integral name and an operational
orientation-reversal certificate.  The boundary sum below cancels these pairs
constructively.  A finite Stokes certificate identifies the antisymmetric
period numerator with that boundary, yielding symmetry without a completed
surface, an infinite chain, or a global integration object.
-/

namespace CCL.Riemann.FiniteBilinear

open CCL.Riemann.AlgebraicDifferentials
open CCL.Riemann.PeriodMatrix
open CCL.Riemann.PeriodMatrix.ScaledInverseCertificate

abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram
abbrev ReversalModels :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram.ReversalModels

/-- Repackaging a coherent arithmetic name as a one-cell finite refinement
program preserves its operational value. -/
def ofCoherentNamed_output_equivalent (value : CoherentNamed) :
    NamedEquivalent value.name
      (CCL.ProgressiveGaussianIntegration.RefinementProgram.ofCoherentNamed
        value).output.name := by
  let source := CCL.ProgressiveSampling.approximation value.name
  let program :=
    CCL.ProgressiveGaussianIntegration.RefinementProgram.ofCoherentNamed value
  have rewrap : NamedEquivalent value.name source.toNamed := by
    exact CCL.OperationalEquivalence.Equivalent.symm
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling source)
  have samples : forall index,
      source.sample index = program.approximation.sample index := by
    intro index
    exact (CCL.ProgressiveGaussianIntegration.RefinementProgram.ofCoherentNamed_integralSample
      value index).symm
  exact CCL.OperationalEquivalence.NamedEquivalent.trans rewrap (by
    simpa only [program,
      CCL.ProgressiveGaussianIntegration.RefinementProgram.output,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      CCL.TranscendentalCoherence.approximationEquivalent_toNamed
        (CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq
          source program.approximation samples))

/-- The explicit finite product program computes the actual stateful product
of its two persistent integral outputs. -/
def multiplyProgram_output_equivalent (left right : RefinementProgram) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        left.output right.output).name
      (CCL.ProgressiveGaussianIntegration.RefinementProgram.multiply
        left right).output.name := by
  simpa only [CCL.ProgressiveCoherence.CoherentNamed.mul,
    CCL.ProgressiveGaussianIntegration.RefinementProgram.output,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.TranscendentalCoherence.mulToNamed_equivalent_pointwise
      left.approximation right.approximation
      (CCL.ProgressiveGaussianIntegration.RefinementProgram.multiply
        left right).approximation
      (fun index =>
        CCL.ProgressiveGaussianIntegration.RefinementProgram.multiply_integralSample
          left right index)

/-- Exact equality of the finite rational integral sample at every refinement
constructs operational equality of the two persistent program outputs. -/
def refinementProgram_output_equivalent_of_samples_eq
    (left right : RefinementProgram)
    (samples : forall index,
      (left.model index).integralSample =
        (right.model index).integralSample) :
    NamedEquivalent left.output.name right.output.name := by
  simpa only [CCL.ProgressiveGaussianIntegration.RefinementProgram.output,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.TranscendentalCoherence.approximationEquivalent_toNamed
      (CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq
        left.approximation right.approximation samples)

private theorem quarterRadius_weighted_sum
    (left middle right : RFAP.ConstructiveFraction.Rational) (index : Nat) :
    2 * (CCL.FiniteGeometric.quarterRadius left index +
      2 * (CCL.FiniteGeometric.quarterRadius middle index +
        CCL.FiniteGeometric.quarterRadius right index)) =
      CCL.FiniteGeometric.quarterRadius
        (2 * (left + 2 * (middle + right))) index := by
  simp only [CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  ring1

private theorem normSq_sub_symm
    (left right : RFAP.ConstructiveGaussian.Gaussian) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (left - right) =
      RFAP.ConstructiveGaussian.Gaussian.normSq (right - left) := by
  rw [show left - right = -(right - left) by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
        RFAP.ConstructiveGaussian.Gaussian.sub_im,
        RFAP.ConstructiveGaussian.Gaussian.neg_re,
        RFAP.ConstructiveGaussian.Gaussian.neg_im] <;> ring1,
    RFAP.ConstructiveGaussian.Gaussian.normSq_neg]

private theorem normSq_sub_le_weighted_sum
    (first second third fourth : RFAP.ConstructiveGaussian.Gaussian)
    (firstBound middleBound lastBound :
      RFAP.ConstructiveFraction.Rational)
    (firstClose :
      RFAP.ConstructiveGaussian.Gaussian.normSq (first - second) <=
        firstBound)
    (middleClose :
      RFAP.ConstructiveGaussian.Gaussian.normSq (second - third) <=
        middleBound)
    (lastClose :
      RFAP.ConstructiveGaussian.Gaussian.normSq (third - fourth) <=
        lastBound) :
    RFAP.ConstructiveGaussian.Gaussian.normSq (first - fourth) <=
      2 * (firstBound + 2 * (middleBound + lastBound)) := by
  have throughThird :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_via
      second third fourth
  have throughSecond :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_via
      first second fourth
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq (first - fourth) <=
        2 *
          (RFAP.ConstructiveGaussian.Gaussian.normSq (first - second) +
            RFAP.ConstructiveGaussian.Gaussian.normSq (second - fourth)) :=
      throughSecond
    _ <= 2 * (firstBound + 2 * (middleBound + lastBound)) := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      · apply add_le_add firstClose
        exact throughThird.trans
          (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add middleClose lastClose) (by decide))
      · decide

private theorem refinementProgram_samples_tail_close
    (left right : RefinementProgram)
    (bridgeScale : RFAP.ConstructiveFraction.Rational)
    (_bridgeScale_nonnegative : 0 <= bridgeScale)
    (samples : forall index,
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((left.model index).integralSample -
            (right.model index).integralSample) <=
        CCL.FiniteGeometric.quarterRadius bridgeScale index)
    {common leftLater rightLater : Nat}
    (leftOrder : common <= leftLater) (rightOrder : common <= rightLater) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((left.model leftLater).integralSample -
          (right.model rightLater).integralSample) <=
      CCL.FiniteGeometric.quarterRadius
        (2 * (left.errorScale + 2 * (bridgeScale + right.errorScale)))
          common := by
  let leftRadius := CCL.FiniteGeometric.quarterRadius
    left.errorScale common
  let bridgeRadius := CCL.FiniteGeometric.quarterRadius bridgeScale common
  let rightRadius := CCL.FiniteGeometric.quarterRadius
    right.errorScale common
  have leftClose :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((left.model leftLater).integralSample -
            (left.model common).integralSample) <= leftRadius :=
    left.later_close leftOrder
  have bridgeClose :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((left.model common).integralSample -
            (right.model common).integralSample) <= bridgeRadius :=
    samples common
  have rightCloseForward :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((right.model rightLater).integralSample -
            (right.model common).integralSample) <= rightRadius :=
    right.later_close rightOrder
  have rightClose :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((right.model common).integralSample -
            (right.model rightLater).integralSample) <= rightRadius := by
    rw [normSq_sub_symm]
    exact rightCloseForward
  calc
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((left.model leftLater).integralSample -
          (right.model rightLater).integralSample) <=
        2 * (leftRadius + 2 * (bridgeRadius + rightRadius)) :=
      normSq_sub_le_weighted_sum
        (left.model leftLater).integralSample
        (left.model common).integralSample
        (right.model common).integralSample
        (right.model rightLater).integralSample
        leftRadius bridgeRadius rightRadius leftClose bridgeClose rightClose
    _ = CCL.FiniteGeometric.quarterRadius
          (2 * (left.errorScale + 2 * (bridgeScale + right.errorScale)))
            common := by
      exact quarterRadius_weighted_sum left.errorScale bridgeScale
        right.errorScale common

/-- A geometrically shrinking rational comparison between two finite
integration programs is enough for operational equality; their displayed
quadrature centres need not be literally equal.  The comparison index is
computed from the three explicit Cauchy scales and the requested tolerance. -/
opaque refinementProgram_output_equivalent_of_samples_close
    (left right : RefinementProgram)
    (bridgeScale : RFAP.ConstructiveFraction.Rational)
    (bridgeScale_nonnegative : 0 <= bridgeScale)
    (samples : forall index,
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((left.model index).integralSample -
            (right.model index).integralSample) <=
        CCL.FiniteGeometric.quarterRadius bridgeScale index) :
    NamedEquivalent left.output.name right.output.name := by
  let totalScale : RFAP.ConstructiveFraction.Rational :=
    2 * (left.errorScale + 2 * (bridgeScale + right.errorScale))
  have totalScale_nonnegative : 0 <= totalScale := by
    exact RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg left.errorScale_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg bridgeScale_nonnegative right.errorScale_nonneg)))
  have equivalent : CCL.OperationalEquivalence.Equivalent
      left.approximation right.approximation := by
    refine { compare := ?_ }
    intro leftStart rightStart target positive
    let common := CCL.FiniteGeometric.firstQuarterBelow totalScale
      (max leftStart rightStart) target
    have common_ge_left : leftStart <= common :=
      (Nat.le_max_left leftStart rightStart).trans
        (CCL.FiniteGeometric.firstQuarterBelow_ge totalScale
          (max leftStart rightStart) target)
    have common_ge_right : rightStart <= common :=
      (Nat.le_max_right leftStart rightStart).trans
        (CCL.FiniteGeometric.firstQuarterBelow_ge totalScale
          (max leftStart rightStart) target)
    have totalSmall : CCL.FiniteGeometric.quarterRadius totalScale common <
        target :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate totalScale
        totalScale_nonnegative (max leftStart rightStart) target positive
    exact
      { leftIndex := common
        rightIndex := common
        left_ge := common_ge_left
        right_ge := common_ge_right
        close := by
          intro leftLater rightLater leftOrder rightOrder
          change RFAP.ConstructiveGaussian.Gaussian.normSq
              ((left.model leftLater).integralSample -
                (right.model rightLater).integralSample) < target
          exact (refinementProgram_samples_tail_close left right bridgeScale
            bridgeScale_nonnegative samples leftOrder rightOrder).trans_lt
              totalSmall }
  simpa only [CCL.ProgressiveGaussianIntegration.RefinementProgram.output,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.TranscendentalCoherence.approximationEquivalent_toNamed equivalent

/-- Repackage a synchronized geometric stream as an explicit one-cell
Gaussian refinement program without resampling it through a stateful name. -/
def geometricRefinementProgram
    (source : CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation) :
    RefinementProgram where
  model := fun index =>
    CCL.ProgressiveGaussianIntegration.RefinementProgram.exactSamplePath
      (source.sample index)
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  modelAllowance_le := by
    intro index
    rw [CCL.ProgressiveGaussianIntegration.RefinementProgram.exactSamplePath_aggregateAllowance]
    exact CCL.FiniteGeometric.quarterRadius_nonneg
      source.errorScale_nonneg index
  later_close := by
    intro earlier later order
    rw [CCL.ProgressiveGaussianIntegration.RefinementProgram.exactSamplePath_integralSample,
      CCL.ProgressiveGaussianIntegration.RefinementProgram.exactSamplePath_integralSample]
    exact source.later_close order
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [CCL.ProgressiveGaussianIntegration.RefinementProgram.exactSamplePath_integralSample]
    exact source.sample_bounded index

@[simp] theorem geometricRefinementProgram_integralSample
    (source : CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation)
    (index : Nat) :
    ((geometricRefinementProgram source).model index).integralSample =
      source.sample index :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram.exactSamplePath_integralSample
    _

/-- The explicit geometric refinement program has the same operational output
as the direct coherent wrapper of its synchronized stream. -/
def geometricNamed_equivalent_geometricRefinementProgram
    (source : CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation) :
    NamedEquivalent (geometricNamed source).name
      (geometricRefinementProgram source).output.name := by
  simpa only [geometricNamed,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation,
    CCL.ProgressiveGaussianIntegration.RefinementProgram.output] using
    CCL.TranscendentalCoherence.approximationEquivalent_toNamed
      (CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq
        source.toApproximation
        (geometricRefinementProgram source).approximation
        (by
          intro index
          rw [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.toApproximation_sample]
          exact (geometricRefinementProgram_integralSample source index).symm))

private theorem negStateAt
    (process : CCL.ProgressiveEnclosures.Process)
    (start : process.State) (index : Nat) :
    CCL.ProgressiveSampling.stateAt
        (CCL.ProgressiveEnclosures.Process.neg process) start index =
      CCL.ProgressiveSampling.stateAt process start index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      rw [CCL.ProgressiveSampling.stateAt_succ,
        CCL.ProgressiveSampling.stateAt_succ, inductionHypothesis]
      change process.refine _ _ _ = process.refine _ _ _
      rfl

private theorem negSampling_sample (input : CCL.ProgressiveTransducer.Named)
    (index : Nat) :
    (CCL.ProgressiveSampling.approximation
      (CCL.ProgressiveTransducer.Named.neg input)).sample index =
      -(CCL.ProgressiveSampling.approximation input).sample index := by
  change
    CCL.ProgressiveSampling.witnessAt
        (CCL.ProgressiveEnclosures.Process.neg input.process)
        input.state index =
      -CCL.ProgressiveSampling.witnessAt input.process input.state index
  unfold CCL.ProgressiveSampling.witnessAt
  rw [negStateAt]
  rfl

/-- Two displayed boundary-edge integrals with certified opposite
orientations.  The reverse contribution is retained as an independently
productive name rather than silently replaced by syntax. -/
structure BoundaryPair where
  forward : CoherentNamed
  reverse : CoherentNamed
  reverse_eq_neg : NamedEquivalent reverse.name
    (CCL.ProgressiveCoherence.CoherentNamed.neg forward).name

namespace BoundaryPair

/-- Contribution of one oriented edge pair to the finite polygon boundary. -/
def sum (pair : BoundaryPair) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add pair.forward pair.reverse

/-- Opposite orientations cancel at the operational finite-request layer. -/
def sum_zero (pair : BoundaryPair) :
    NamedEquivalent pair.sum.name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.TranscendentalCoherence.coherentAdd_respects
      pair.forward pair.forward pair.reverse
      (CCL.ProgressiveCoherence.CoherentNamed.neg pair.forward)
      (CCL.OperationalEquivalence.NamedEquivalent.refl pair.forward.name)
      pair.reverse_eq_neg)
    (CCL.OperationalFieldLaws.coherentAdd_neg_right pair.forward)

private theorem reverse_emittedSampleIndex (program : RefinementProgram)
    (models : ReversalModels program) (index : Nat) :
    CCL.OperationalEquivalence.emittedSampleIndex
        (CCL.ProgressiveGaussianIntegration.RefinementProgram.reverse
          program models).approximation index =
      CCL.OperationalEquivalence.emittedSampleIndex program.approximation
        index := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      unfold CCL.OperationalEquivalence.emittedSampleIndex
      rw [CCL.ProgressiveSampling.stateAt_succ,
        CCL.ProgressiveSampling.stateAt_succ]
      change CCL.FiniteGeometric.firstQuarterBelow program.errorScale
          (CCL.OperationalEquivalence.emittedSampleIndex
            (CCL.ProgressiveGaussianIntegration.RefinementProgram.reverse
              program models).approximation index)
          (CCL.ProgressiveSampling.refinementTarget (index + 1)) =
        CCL.FiniteGeometric.firstQuarterBelow program.errorScale
          (CCL.OperationalEquivalence.emittedSampleIndex
            program.approximation index)
          (CCL.ProgressiveSampling.refinementTarget (index + 1))
      rw [inductionHypothesis]

/-- An actual cellwise reversal of a finite Gaussian refinement program gives
one canonical oriented boundary pair. -/
def ofProgramReversal (program : RefinementProgram)
    (models : ReversalModels program) : BoundaryPair where
  forward := program.output
  reverse :=
    (CCL.ProgressiveGaussianIntegration.RefinementProgram.reverse
      program models).output
  reverse_eq_neg := by
    apply CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq
    intro index
    let reverseProgram :=
      CCL.ProgressiveGaussianIntegration.RefinementProgram.reverse
        program models
    rw [show
        (CCL.ProgressiveSampling.approximation
          reverseProgram.output.name).sample index =
          reverseProgram.approximation.sample
            (CCL.OperationalEquivalence.emittedSampleIndex
              reverseProgram.approximation index) by
        exact CCL.OperationalEquivalence.emittedSample_eq
          reverseProgram.approximation index]
    rw [show
        (CCL.ProgressiveCoherence.CoherentNamed.neg program.output).name =
          CCL.ProgressiveTransducer.Named.neg program.output.name by rfl,
      negSampling_sample]
    rw [show
        (CCL.ProgressiveSampling.approximation program.output.name).sample
            index =
          program.approximation.sample
            (CCL.OperationalEquivalence.emittedSampleIndex
              program.approximation index) by
        exact CCL.OperationalEquivalence.emittedSample_eq
          program.approximation index,
      reverse_emittedSampleIndex program models index]
    exact CCL.ProgressiveGaussianIntegration.RefinementProgram.reverse_integralSample
      program models
        (CCL.OperationalEquivalence.emittedSampleIndex
          program.approximation index)

end BoundaryPair

/-- One finite edge-integration program and explicit cellwise reversal data
for every displayed refinement. -/
structure ProgramBoundaryPair where
  forward : RefinementProgram
  reversal : ReversalModels forward

namespace ProgramBoundaryPair

/-- The operational edge pair derived from the finite reversal program. -/
def toBoundaryPair (pair : ProgramBoundaryPair) : BoundaryPair :=
  BoundaryPair.ofProgramReversal pair.forward pair.reversal

end ProgramBoundaryPair

/-- Recursive sum of all displayed oriented edge pairs. -/
def boundarySum : {count : Nat} -> (Fin count -> BoundaryPair) -> CoherentNamed
  | 0, _ => CCL.ProgressiveCoherence.CoherentNamed.exact 0
  | count + 1, pairs =>
      CCL.ProgressiveCoherence.CoherentNamed.add (pairs 0).sum
        (boundarySum fun index : Fin count => pairs index.succ)

/-- Every finite paired polygon boundary cancels operationally. -/
def boundarySum_zero {count : Nat} (pairs : Fin count -> BoundaryPair) :
    NamedEquivalent (boundarySum pairs).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  induction count with
  | zero =>
      exact CCL.OperationalEquivalence.NamedEquivalent.refl
        (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name
  | succ count inductionHypothesis =>
      let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
      let tail := boundarySum fun index : Fin count => pairs index.succ
      have cancelHead : NamedEquivalent (pairs 0).sum.name zero.name := by
        simpa only [zero] using (pairs 0).sum_zero
      have cancelTail : NamedEquivalent tail.name zero.name := by
        simpa only [tail, zero] using
          inductionHypothesis (fun index : Fin count => pairs index.succ)
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (by
          change NamedEquivalent
            (CCL.ProgressiveCoherence.CoherentNamed.add (pairs 0).sum tail).name
            (CCL.ProgressiveCoherence.CoherentNamed.add zero zero).name
          exact CCL.TranscendentalCoherence.coherentAdd_respects
            (pairs 0).sum zero tail zero cancelHead cancelTail)
        (CCL.OperationalFieldLaws.coherentAdd_zero_right zero)

/-- Operational cancellation of `left - right` proves that the two original
names are operationally equal. -/
def equivalent_of_sub_zero (left right : CoherentNamed)
    (zeroDifference : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add left
        (CCL.ProgressiveCoherence.CoherentNamed.neg right)).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name) :
    NamedEquivalent left.name right.name := by
  let negative := CCL.ProgressiveCoherence.CoherentNamed.neg right
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  let difference := CCL.ProgressiveCoherence.CoherentNamed.add left negative
  have begin : NamedEquivalent left.name
      (CCL.ProgressiveCoherence.CoherentNamed.add left zero).name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalFieldLaws.coherentAdd_zero_right left)
  have insertCancellation : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add left zero).name
      (CCL.ProgressiveCoherence.CoherentNamed.add left
        (CCL.ProgressiveCoherence.CoherentNamed.add negative right)).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects left left zero
      (CCL.ProgressiveCoherence.CoherentNamed.add negative right)
      (CCL.OperationalEquivalence.NamedEquivalent.refl left.name)
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (by
          simpa only [negative, zero,
            CCL.ProgressiveCoherence.CoherentNamed.neg,
            CCL.ProgressiveCoherence.CoherentNamed.exact,
            CCL.ProgressiveCoherence.CoherentNamed.add] using
            CCL.OperationalFieldLaws.coherentAdd_neg_left right))
  have reassociate : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add left
        (CCL.ProgressiveCoherence.CoherentNamed.add negative right)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add difference right).name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (by
        simpa only [difference,
          CCL.ProgressiveCoherence.CoherentNamed.add] using
          CCL.OperationalFieldLaws.coherentAdd_assoc left negative right)
  have differenceZero : NamedEquivalent difference.name zero.name := by
    simpa only [difference, negative, zero,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using zeroDifference
  have replaceDifference : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add difference right).name
      (CCL.ProgressiveCoherence.CoherentNamed.add zero right).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects difference zero right right
      differenceZero
      (CCL.OperationalEquivalence.NamedEquivalent.refl right.name)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans begin
    (CCL.OperationalEquivalence.NamedEquivalent.trans insertCancellation
      (CCL.OperationalEquivalence.NamedEquivalent.trans reassociate
        (CCL.OperationalEquivalence.NamedEquivalent.trans replaceDifference
          (CCL.OperationalFieldLaws.coherentAdd_zero_left right))))

/-- Four-term additive interchange, derived only from operational
commutativity and associativity. -/
def coherentAdd_interchange
    (first second third fourth : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.add first second)
        (CCL.ProgressiveCoherence.CoherentNamed.add third fourth)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.add first third)
        (CCL.ProgressiveCoherence.CoherentNamed.add second fourth)).name := by
  let thirdFourth :=
    CCL.ProgressiveCoherence.CoherentNamed.add third fourth
  let secondThird :=
    CCL.ProgressiveCoherence.CoherentNamed.add second third
  let thirdSecond :=
    CCL.ProgressiveCoherence.CoherentNamed.add third second
  let secondFourth :=
    CCL.ProgressiveCoherence.CoherentNamed.add second fourth
  have exposeMiddle : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add second thirdFourth).name
      (CCL.ProgressiveCoherence.CoherentNamed.add secondThird fourth).name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm (by
      simpa only [thirdFourth, secondThird,
        CCL.ProgressiveCoherence.CoherentNamed.add] using
        CCL.OperationalFieldLaws.coherentAdd_assoc second third fourth)
  have swapMiddle : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add secondThird fourth).name
      (CCL.ProgressiveCoherence.CoherentNamed.add thirdSecond fourth).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      secondThird thirdSecond fourth fourth
      (by simpa only [secondThird, thirdSecond,
        CCL.ProgressiveCoherence.CoherentNamed.add] using
        CCL.OperationalFieldLaws.coherentAdd_comm second third)
      (CCL.OperationalEquivalence.NamedEquivalent.refl fourth.name)
  have regroupMiddle : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add thirdSecond fourth).name
      (CCL.ProgressiveCoherence.CoherentNamed.add third secondFourth).name := by
    simpa only [thirdSecond, secondFourth,
      CCL.ProgressiveCoherence.CoherentNamed.add] using
      CCL.OperationalFieldLaws.coherentAdd_assoc third second fourth
  have middleInterchange : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add second thirdFourth).name
      (CCL.ProgressiveCoherence.CoherentNamed.add third secondFourth).name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans exposeMiddle
      (CCL.OperationalEquivalence.NamedEquivalent.trans swapMiddle
        regroupMiddle)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.OperationalFieldLaws.coherentAdd_assoc first second thirdFourth)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentAdd_respects first first
        (CCL.ProgressiveCoherence.CoherentNamed.add second thirdFourth)
        (CCL.ProgressiveCoherence.CoherentNamed.add third secondFourth)
        (CCL.OperationalEquivalence.NamedEquivalent.refl first.name)
        middleInterchange)
      (CCL.OperationalEquivalence.NamedEquivalent.symm (by
        simpa only [secondFourth,
          CCL.ProgressiveCoherence.CoherentNamed.add] using
          CCL.OperationalFieldLaws.coherentAdd_assoc
            first third secondFourth)))

/-- An operational right inverse of an additive value is equal to its actual
stateful negation. -/
def equivalent_neg_of_add_zero (value candidate : CoherentNamed)
    (cancel : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add value candidate).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name) :
    NamedEquivalent candidate.name
      (CCL.ProgressiveCoherence.CoherentNamed.neg value).name := by
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  let negative := CCL.ProgressiveCoherence.CoherentNamed.neg value
  let negativeValue :=
    CCL.ProgressiveCoherence.CoherentNamed.add negative value
  have begin : NamedEquivalent candidate.name
      (CCL.ProgressiveCoherence.CoherentNamed.add zero candidate).name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalFieldLaws.coherentAdd_zero_left candidate)
  have insertInverse : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add zero candidate).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        negativeValue candidate).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      zero negativeValue candidate candidate
      (CCL.OperationalEquivalence.NamedEquivalent.symm (by
        simpa only [zero, negative, negativeValue,
          CCL.ProgressiveCoherence.CoherentNamed.exact,
          CCL.ProgressiveCoherence.CoherentNamed.neg,
          CCL.ProgressiveCoherence.CoherentNamed.add] using
          CCL.OperationalFieldLaws.coherentAdd_neg_left value))
      (CCL.OperationalEquivalence.NamedEquivalent.refl candidate.name)
  have associate : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        negativeValue candidate).name
      (CCL.ProgressiveCoherence.CoherentNamed.add negative
        (CCL.ProgressiveCoherence.CoherentNamed.add value candidate)).name := by
    simpa only [negativeValue,
      CCL.ProgressiveCoherence.CoherentNamed.add] using
      CCL.OperationalFieldLaws.coherentAdd_assoc negative value candidate
  have replaceCancellation : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add negative
        (CCL.ProgressiveCoherence.CoherentNamed.add value candidate)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add negative zero).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects negative negative
      (CCL.ProgressiveCoherence.CoherentNamed.add value candidate) zero
      (CCL.OperationalEquivalence.NamedEquivalent.refl negative.name)
      (by simpa only [zero] using cancel)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans begin
    (CCL.OperationalEquivalence.NamedEquivalent.trans insertInverse
      (CCL.OperationalEquivalence.NamedEquivalent.trans associate
        (CCL.OperationalEquivalence.NamedEquivalent.trans replaceCancellation
          (CCL.OperationalFieldLaws.coherentAdd_zero_right negative))))

/-- Stateful negation respects operational equivalence. -/
def coherentNeg_respects (left right : CoherentNamed)
    (equivalent : NamedEquivalent left.name right.name) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.neg left).name
      (CCL.ProgressiveCoherence.CoherentNamed.neg right).name := by
  let negativeLeft := CCL.ProgressiveCoherence.CoherentNamed.neg left
  let negativeRight := CCL.ProgressiveCoherence.CoherentNamed.neg right
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  have replaceInput : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add right negativeLeft).name
      (CCL.ProgressiveCoherence.CoherentNamed.add left negativeLeft).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      right left negativeLeft negativeLeft
      (CCL.OperationalEquivalence.NamedEquivalent.symm equivalent)
      (CCL.OperationalEquivalence.NamedEquivalent.refl negativeLeft.name)
  have cancel : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add right negativeLeft).name
      zero.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans replaceInput (by
      simpa only [negativeLeft, zero,
        CCL.ProgressiveCoherence.CoherentNamed.add,
        CCL.ProgressiveCoherence.CoherentNamed.neg,
        CCL.ProgressiveCoherence.CoherentNamed.exact] using
        CCL.OperationalFieldLaws.coherentAdd_neg_right left)
  simpa only [negativeLeft, negativeRight] using
    equivalent_neg_of_add_zero right negativeLeft cancel

/-- Stateful negation distributes over a finite operational sum. -/
def coherentNeg_add (left right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.neg left)
        (CCL.ProgressiveCoherence.CoherentNamed.neg right)).name
      (CCL.ProgressiveCoherence.CoherentNamed.neg
        (CCL.ProgressiveCoherence.CoherentNamed.add left right)).name := by
  let negativeLeft := CCL.ProgressiveCoherence.CoherentNamed.neg left
  let negativeRight := CCL.ProgressiveCoherence.CoherentNamed.neg right
  let value := CCL.ProgressiveCoherence.CoherentNamed.add left right
  let candidate :=
    CCL.ProgressiveCoherence.CoherentNamed.add negativeLeft negativeRight
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  have separate : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add value candidate).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.add left negativeLeft)
        (CCL.ProgressiveCoherence.CoherentNamed.add right negativeRight)).name := by
    simpa only [value, candidate] using
      coherentAdd_interchange left right negativeLeft negativeRight
  have cancelBoth : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.add left negativeLeft)
        (CCL.ProgressiveCoherence.CoherentNamed.add right negativeRight)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add zero zero).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      (CCL.ProgressiveCoherence.CoherentNamed.add left negativeLeft) zero
      (CCL.ProgressiveCoherence.CoherentNamed.add right negativeRight) zero
      (by simpa only [negativeLeft, zero,
        CCL.ProgressiveCoherence.CoherentNamed.neg,
        CCL.ProgressiveCoherence.CoherentNamed.exact,
        CCL.ProgressiveCoherence.CoherentNamed.add] using
        CCL.OperationalFieldLaws.coherentAdd_neg_right left)
      (by simpa only [negativeRight, zero,
        CCL.ProgressiveCoherence.CoherentNamed.neg,
        CCL.ProgressiveCoherence.CoherentNamed.exact,
        CCL.ProgressiveCoherence.CoherentNamed.add] using
        CCL.OperationalFieldLaws.coherentAdd_neg_right right)
  have totalZero : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add value candidate).name
      zero.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans separate
      (CCL.OperationalEquivalence.NamedEquivalent.trans cancelBoth
        (CCL.OperationalFieldLaws.coherentAdd_zero_right zero))
  simpa only [value, candidate, negativeLeft, negativeRight,
    CCL.ProgressiveCoherence.CoherentNamed.add,
    CCL.ProgressiveCoherence.CoherentNamed.neg] using
    equivalent_neg_of_add_zero value candidate totalZero

/-- The actual negation of the terminating zero is operationally zero. -/
def zero_equivalent_neg_zero :
    NamedEquivalent (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name
      (CCL.ProgressiveCoherence.CoherentNamed.neg
        (CCL.ProgressiveCoherence.CoherentNamed.exact 0)).name := by
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  simpa only [zero] using equivalent_neg_of_add_zero zero zero
    (CCL.OperationalFieldLaws.coherentAdd_zero_right zero)

/-- Applying the actual stateful negation twice returns the original
operational value. -/
def coherent_doubleNeg (value : CoherentNamed) :
    NamedEquivalent value.name
      (CCL.ProgressiveCoherence.CoherentNamed.neg
        (CCL.ProgressiveCoherence.CoherentNamed.neg value)).name := by
  let negative := CCL.ProgressiveCoherence.CoherentNamed.neg value
  exact equivalent_neg_of_add_zero negative value (by
    simpa only [negative,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      CCL.OperationalFieldLaws.coherentAdd_neg_left value)

/-- Swapping the two entries of an operational difference negates it. -/
def coherentSub_swap (left right : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add right
        (CCL.ProgressiveCoherence.CoherentNamed.neg left)).name
      (CCL.ProgressiveCoherence.CoherentNamed.neg
        (CCL.ProgressiveCoherence.CoherentNamed.add left
          (CCL.ProgressiveCoherence.CoherentNamed.neg right))).name := by
  let negativeLeft := CCL.ProgressiveCoherence.CoherentNamed.neg left
  let negativeRight := CCL.ProgressiveCoherence.CoherentNamed.neg right
  let doubleNegativeRight :=
    CCL.ProgressiveCoherence.CoherentNamed.neg negativeRight
  have commute : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add right negativeLeft).name
      (CCL.ProgressiveCoherence.CoherentNamed.add negativeLeft right).name :=
    CCL.OperationalFieldLaws.coherentAdd_comm right negativeLeft
  have replaceRight : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add negativeLeft right).name
      (CCL.ProgressiveCoherence.CoherentNamed.add negativeLeft
        doubleNegativeRight).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      negativeLeft negativeLeft right doubleNegativeRight
      (CCL.OperationalEquivalence.NamedEquivalent.refl negativeLeft.name)
      (coherent_doubleNeg right)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans commute
    (CCL.OperationalEquivalence.NamedEquivalent.trans replaceRight (by
      simpa only [negativeLeft, negativeRight, doubleNegativeRight] using
        coherentNeg_add left negativeRight))

/-- Recursive finite sums distribute over pointwise operational addition. -/
def sumNamed_add {count : Nat}
    (left right : Fin count -> CoherentNamed) :
    NamedEquivalent
      (sumNamed fun entry =>
        CCL.ProgressiveCoherence.CoherentNamed.add
          (left entry) (right entry)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (sumNamed left) (sumNamed right)).name := by
  induction count with
  | zero =>
      exact CCL.OperationalEquivalence.NamedEquivalent.symm
        (CCL.OperationalFieldLaws.coherentAdd_zero_right
          (CCL.ProgressiveCoherence.CoherentNamed.exact 0))
  | succ count inductionHypothesis =>
      let leftTail := fun entry : Fin count => left entry.succ
      let rightTail := fun entry : Fin count => right entry.succ
      have replaceTail : NamedEquivalent
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (CCL.ProgressiveCoherence.CoherentNamed.add (left 0) (right 0))
            (sumNamed fun entry : Fin count =>
              CCL.ProgressiveCoherence.CoherentNamed.add
                (leftTail entry) (rightTail entry))).name
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (CCL.ProgressiveCoherence.CoherentNamed.add (left 0) (right 0))
            (CCL.ProgressiveCoherence.CoherentNamed.add
              (sumNamed leftTail) (sumNamed rightTail))).name :=
        CCL.TranscendentalCoherence.coherentAdd_respects
          (CCL.ProgressiveCoherence.CoherentNamed.add (left 0) (right 0))
          (CCL.ProgressiveCoherence.CoherentNamed.add (left 0) (right 0))
          (sumNamed fun entry : Fin count =>
            CCL.ProgressiveCoherence.CoherentNamed.add
              (leftTail entry) (rightTail entry))
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (sumNamed leftTail) (sumNamed rightTail))
          (CCL.OperationalEquivalence.NamedEquivalent.refl _)
          (inductionHypothesis leftTail rightTail)
      exact CCL.OperationalEquivalence.NamedEquivalent.trans replaceTail
        (coherentAdd_interchange (left 0) (right 0)
          (sumNamed leftTail) (sumNamed rightTail))

/-- Recursive finite sums commute with actual stateful negation. -/
def sumNamed_neg {count : Nat} (values : Fin count -> CoherentNamed) :
    NamedEquivalent
      (sumNamed fun entry =>
        CCL.ProgressiveCoherence.CoherentNamed.neg (values entry)).name
      (CCL.ProgressiveCoherence.CoherentNamed.neg
        (sumNamed values)).name := by
  induction count with
  | zero => exact zero_equivalent_neg_zero
  | succ count inductionHypothesis =>
      let tail := fun entry : Fin count => values entry.succ
      apply CCL.OperationalEquivalence.NamedEquivalent.trans
      · exact CCL.TranscendentalCoherence.coherentAdd_respects
          (CCL.ProgressiveCoherence.CoherentNamed.neg (values 0))
          (CCL.ProgressiveCoherence.CoherentNamed.neg (values 0))
          (sumNamed fun entry : Fin count =>
            CCL.ProgressiveCoherence.CoherentNamed.neg (tail entry))
          (CCL.ProgressiveCoherence.CoherentNamed.neg (sumNamed tail))
          (CCL.OperationalEquivalence.NamedEquivalent.refl _)
          (inductionHypothesis tail)
      · exact coherentNeg_add (values 0) (sumNamed tail)

/-- A synchronized constant geometric stream is operationally the ordinary
terminating coherent constant. -/
def geometricExact_equivalent_exact
    (value : RFAP.ConstructiveGaussian.Gaussian) :
    NamedEquivalent
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
          value)).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact value).name := by
  let geometric :=
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
      value
  let constant := CCL.TranscendentalLaws.constantApproximation
    value
  have toConstant : NamedEquivalent (geometricNamed geometric).name
      constant.toNamed := by
    simpa only [geometricNamed,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      CCL.TranscendentalCoherence.approximationEquivalent_toNamed
        (CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq
          geometric.toApproximation constant (by intro index; rfl))
  exact CCL.OperationalEquivalence.NamedEquivalent.trans toConstant
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.TranscendentalCoherence.exact_toConstantNamed value))

/-- The synchronized geometric zero used by `sumNamed` is operationally the
ordinary terminating coherent zero. -/
def geometricZero_equivalent_exact :
    NamedEquivalent
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
          0)).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  geometricExact_equivalent_exact 0

/-- Equal-index geometric negation is the operational additive inverse of
the geometric source, hence agrees with the actual stateful CCL negation. -/
def geometricNeg_equivalent_statefulNeg
    (source : CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation) :
    NamedEquivalent
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.neg
          source)).name
      (CCL.ProgressiveCoherence.CoherentNamed.neg
        (geometricNamed source)).name := by
  let value := geometricNamed source
  let candidate := geometricNamed
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.neg source)
  let geometricZero := geometricNamed
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 0)
  have cancelToGeometricZero : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add value candidate).name
      geometricZero.name := by
    simpa only [value, candidate, geometricZero, geometricNamed,
      CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      CCL.OperationalFieldLaws.addToNamed_equivalent_pointwise
        source.toApproximation
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.neg
          source).toApproximation
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
          0).toApproximation
        (by
          intro index
          simp only [
            CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.toApproximation_sample,
            CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact_sample,
            CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.neg_sample]
          exact (add_neg_cancel (source.sample index)).symm)
  have cancel : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add value candidate).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans cancelToGeometricZero
      geometricZero_equivalent_exact
  simpa only [value, candidate] using
    equivalent_neg_of_add_zero value candidate cancel

/-- Stateful negation of any realization of a synchronized geometric source
realizes the equal-index geometric negation. -/
def coherentNeg_equivalent_geometricNeg
    (value : CoherentNamed)
    (source : CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation)
    (equivalent : NamedEquivalent value.name
      (geometricNamed source).name) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.neg value).name
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.neg
          source)).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentNeg_respects value (geometricNamed source) equivalent)
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (geometricNeg_equivalent_statefulNeg source))

/-- Actual addition realizes equal-index geometric addition whenever both
operands realize their synchronized sources. -/
def coherentAdd_equivalent_geometricAdd
    (left right : CoherentNamed)
    (leftSource rightSource :
      CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation)
    (leftEquivalent : NamedEquivalent left.name
      (geometricNamed leftSource).name)
    (rightEquivalent : NamedEquivalent right.name
      (geometricNamed rightSource).name) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add left right).name
      (geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.add
          leftSource rightSource)).name := by
  let leftGeometric := geometricNamed leftSource
  let rightGeometric := geometricNamed rightSource
  have replaceOperands : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add left right).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        leftGeometric rightGeometric).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      left leftGeometric right rightGeometric
      leftEquivalent rightEquivalent
  apply CCL.OperationalEquivalence.NamedEquivalent.trans replaceOperands
  simpa only [leftGeometric, rightGeometric, geometricNamed,
    CCL.ProgressiveCoherence.CoherentNamed.add,
    CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
    CCL.OperationalFieldLaws.addToNamed_equivalent_pointwise
      leftSource.toApproximation rightSource.toApproximation
      (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.add
        leftSource rightSource).toApproximation
      (by intro index; rfl)

/-- A finite recursive sum vanishes when every displayed coherent summand
does.  The empty case explicitly bridges the synchronized geometric zero used
by `sumNamed` to the terminating coherent zero. -/
def sumNamed_zero : {count : Nat} ->
    (values : Fin count -> CoherentNamed) ->
    (forall index,
      NamedEquivalent (values index).name
        (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name) ->
    NamedEquivalent (sumNamed values).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name
  | 0, _values, _zero => geometricZero_equivalent_exact
  | count + 1, values, zeroValues => by
      let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
      let tail := fun index : Fin count => values index.succ
      have replaceBoth : NamedEquivalent
          (CCL.ProgressiveCoherence.CoherentNamed.add
            (values 0) (sumNamed tail)).name
          (CCL.ProgressiveCoherence.CoherentNamed.add zero zero).name :=
        CCL.TranscendentalCoherence.coherentAdd_respects
          (values 0) zero (sumNamed tail) zero
          (zeroValues 0)
          (sumNamed_zero tail (fun index => zeroValues index.succ))
      exact CCL.OperationalEquivalence.NamedEquivalent.trans replaceBoth
        (CCL.OperationalFieldLaws.coherentAdd_zero_right zero)

/-! ## Finite primitive boundaries -/

/-- Operational endpoint difference, oriented from `start` to `finish`. -/
def primitiveDifference (start finish : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.neg start) finish

/-- A zero-length primitive difference is operationally zero. -/
def primitiveDifference_self_zero (value : CoherentNamed) :
    NamedEquivalent (primitiveDifference value value).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  simpa only [primitiveDifference,
    CCL.ProgressiveCoherence.CoherentNamed.add,
    CCL.ProgressiveCoherence.CoherentNamed.neg,
    CCL.ProgressiveCoherence.CoherentNamed.exact] using
    CCL.OperationalFieldLaws.coherentAdd_neg_left value

/-- Consecutive operational primitive differences telescope through their
shared finite endpoint name. -/
def primitiveDifference_compose (start middle finish : CoherentNamed) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (primitiveDifference start middle)
        (primitiveDifference middle finish)).name
      (primitiveDifference start finish).name := by
  let negativeStart := CCL.ProgressiveCoherence.CoherentNamed.neg start
  let negativeMiddle := CCL.ProgressiveCoherence.CoherentNamed.neg middle
  let middleFinish := CCL.ProgressiveCoherence.CoherentNamed.add
    negativeMiddle finish
  have associate : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.add negativeStart middle)
        middleFinish).name
      (CCL.ProgressiveCoherence.CoherentNamed.add negativeStart
        (CCL.ProgressiveCoherence.CoherentNamed.add middle
          middleFinish)).name :=
    CCL.OperationalFieldLaws.coherentAdd_assoc
      negativeStart middle middleFinish
  have exposeCancellation : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add middle middleFinish).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.add middle negativeMiddle)
        finish).name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm (by
      simpa only [middleFinish,
        CCL.ProgressiveCoherence.CoherentNamed.add] using
        CCL.OperationalFieldLaws.coherentAdd_assoc
          middle negativeMiddle finish)
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  have cancellation : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add middle negativeMiddle).name
      zero.name := by
    simpa only [negativeMiddle, zero,
      CCL.ProgressiveCoherence.CoherentNamed.neg,
      CCL.ProgressiveCoherence.CoherentNamed.exact,
      CCL.ProgressiveCoherence.CoherentNamed.add] using
      CCL.OperationalFieldLaws.coherentAdd_neg_right middle
  have removeCancellation : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (CCL.ProgressiveCoherence.CoherentNamed.add middle negativeMiddle)
        finish).name
      finish.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.TranscendentalCoherence.coherentAdd_respects
        (CCL.ProgressiveCoherence.CoherentNamed.add middle negativeMiddle)
        zero finish finish cancellation
        (CCL.OperationalEquivalence.NamedEquivalent.refl finish.name))
      (CCL.OperationalFieldLaws.coherentAdd_zero_left finish)
  have reduceTail : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add middle middleFinish).name
      finish.name :=
    CCL.OperationalEquivalence.NamedEquivalent.trans exposeCancellation
      removeCancellation
  have reduceUnderStart : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add negativeStart
        (CCL.ProgressiveCoherence.CoherentNamed.add middle middleFinish)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        negativeStart finish).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      negativeStart negativeStart
      (CCL.ProgressiveCoherence.CoherentNamed.add middle middleFinish)
      finish
      (CCL.OperationalEquivalence.NamedEquivalent.refl negativeStart.name)
      reduceTail
  simpa only [primitiveDifference, negativeStart, negativeMiddle,
    middleFinish, CCL.ProgressiveCoherence.CoherentNamed.add,
    CCL.ProgressiveCoherence.CoherentNamed.neg] using
    CCL.OperationalEquivalence.NamedEquivalent.trans associate reduceUnderStart

/-- Advancing a displayed primitive value by one program output makes that
output exactly the next operational primitive difference. -/
def increment_eq_primitiveDifference (start increment : CoherentNamed) :
    NamedEquivalent increment.name
      (primitiveDifference start
        (CCL.ProgressiveCoherence.CoherentNamed.add start increment)).name := by
  let negativeStart := CCL.ProgressiveCoherence.CoherentNamed.neg start
  let zero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  let cancellation := CCL.ProgressiveCoherence.CoherentNamed.add
    negativeStart start
  have begin : NamedEquivalent increment.name
      (CCL.ProgressiveCoherence.CoherentNamed.add zero increment).name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalFieldLaws.coherentAdd_zero_left increment)
  have exposeCancellation : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add zero increment).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        cancellation increment).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      zero cancellation increment increment
      (CCL.OperationalEquivalence.NamedEquivalent.symm (by
        simpa only [zero, cancellation, negativeStart,
          CCL.ProgressiveCoherence.CoherentNamed.exact,
          CCL.ProgressiveCoherence.CoherentNamed.add,
          CCL.ProgressiveCoherence.CoherentNamed.neg] using
          CCL.OperationalFieldLaws.coherentAdd_neg_left start))
      (CCL.OperationalEquivalence.NamedEquivalent.refl increment.name)
  have associate : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        cancellation increment).name
      (CCL.ProgressiveCoherence.CoherentNamed.add negativeStart
        (CCL.ProgressiveCoherence.CoherentNamed.add start increment)).name := by
    simpa only [cancellation,
      CCL.ProgressiveCoherence.CoherentNamed.add] using
      CCL.OperationalFieldLaws.coherentAdd_assoc
        negativeStart start increment
  simpa only [primitiveDifference, negativeStart] using
    CCL.OperationalEquivalence.NamedEquivalent.trans begin
      (CCL.OperationalEquivalence.NamedEquivalent.trans exposeCancellation
        associate)

/-- One finite edge integral together with its operational fundamental-theorem
identity against two displayed primitive endpoint values. -/
structure PrimitiveEdge (start finish : CoherentNamed) where
  program : RefinementProgram
  integral_eq_difference : NamedEquivalent program.output.name
    (primitiveDifference start finish).name

/-- A finite composable path of primitive-certified integral programs. -/
inductive PrimitivePath : CoherentNamed -> CoherentNamed -> Type 2
  | nil (value : CoherentNamed) : PrimitivePath value value
  | cons {start middle finish : CoherentNamed}
      (head : PrimitiveEdge start middle)
      (tail : PrimitivePath middle finish) : PrimitivePath start finish

namespace PrimitivePath

/-- Recursive sum of the actual persistent integral outputs along a primitive
path. -/
def integralSum : {start finish : CoherentNamed} ->
    PrimitivePath start finish -> CoherentNamed
  | _, _, .nil _ => CCL.ProgressiveCoherence.CoherentNamed.exact 0
  | _, _, .cons head tail =>
      CCL.ProgressiveCoherence.CoherentNamed.add
        head.program.output tail.integralSum

/-- Finite operational fundamental theorem: all internal primitive endpoint
values cancel, leaving only the final value minus the initial value. -/
def integralSum_eq_difference : {start finish : CoherentNamed} ->
    (path : PrimitivePath start finish) ->
      NamedEquivalent path.integralSum.name
        (primitiveDifference start finish).name
  | _, _, .nil value =>
      CCL.OperationalEquivalence.NamedEquivalent.symm
        (primitiveDifference_self_zero value)
  | _, _, .cons head tail => by
      apply CCL.OperationalEquivalence.NamedEquivalent.trans
      · exact CCL.TranscendentalCoherence.coherentAdd_respects
          head.program.output (primitiveDifference _ _)
          tail.integralSum (primitiveDifference _ _)
          head.integral_eq_difference tail.integralSum_eq_difference
      · exact primitiveDifference_compose _ _ _

end PrimitivePath

/-- Primitive endpoint obtained by advancing through a finite indexed family
of refinement-program outputs. -/
def cumulativePrimitiveFinish : {count : Nat} -> CoherentNamed ->
    (Fin count -> RefinementProgram) -> CoherentNamed
  | 0, start, _programs => start
  | count + 1, start, programs =>
      cumulativePrimitiveFinish
        (CCL.ProgressiveCoherence.CoherentNamed.add start
          (programs 0).output)
        (fun index : Fin count => programs index.succ)

/-- Canonical primitive path through a finite indexed family of actual
refinement programs.  Every endpoint and every fundamental-theorem identity
is constructed rather than supplied. -/
def cumulativePrimitivePath : {count : Nat} ->
    (start : CoherentNamed) -> (programs : Fin count -> RefinementProgram) ->
      PrimitivePath start (cumulativePrimitiveFinish start programs)
  | 0, start, _programs => .nil start
  | count + 1, start, programs =>
      let finish := CCL.ProgressiveCoherence.CoherentNamed.add start
        (programs 0).output
      .cons
        { program := programs 0
          integral_eq_difference :=
            increment_eq_primitiveDifference start (programs 0).output }
        (cumulativePrimitivePath finish
          (fun index : Fin count => programs index.succ))

/-- The integral sum of the canonical primitive path is the ordinary finite
recursive sum of exactly the same program outputs. -/
def cumulativePrimitivePath_integralSum_equivalent_sumNamed :
    {count : Nat} -> (start : CoherentNamed) ->
      (programs : Fin count -> RefinementProgram) ->
        NamedEquivalent
          (cumulativePrimitivePath start programs).integralSum.name
          (sumNamed fun index => (programs index).output).name
  | 0, start, _programs => by
      change NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name
        (geometricNamed
          (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
            0)).name
      exact CCL.OperationalEquivalence.NamedEquivalent.symm
        geometricZero_equivalent_exact
  | count + 1, start, programs => by
      change NamedEquivalent
        (CCL.ProgressiveCoherence.CoherentNamed.add
          (programs 0).output
          (cumulativePrimitivePath
            (CCL.ProgressiveCoherence.CoherentNamed.add start
              (programs 0).output)
            (fun index : Fin count => programs index.succ)).integralSum).name
        (CCL.ProgressiveCoherence.CoherentNamed.add
          (programs 0).output
          (sumNamed fun index : Fin count =>
            (programs index.succ).output)).name
      exact CCL.TranscendentalCoherence.coherentAdd_respects
        (programs 0).output (programs 0).output
        (cumulativePrimitivePath
          (CCL.ProgressiveCoherence.CoherentNamed.add start
            (programs 0).output)
          (fun index : Fin count => programs index.succ)).integralSum
        (sumNamed fun index : Fin count => (programs index.succ).output)
        (CCL.OperationalEquivalence.NamedEquivalent.refl _)
        (cumulativePrimitivePath_integralSum_equivalent_sumNamed
          (CCL.ProgressiveCoherence.CoherentNamed.add start
            (programs 0).output)
          (fun index : Fin count => programs index.succ))

/-- The computed final primitive value is the initial value plus the finite
recursive program sum, up to operational associativity and the two concrete
zero representations. -/
def cumulativePrimitiveFinish_equivalent_add_sumNamed :
    {count : Nat} -> (start : CoherentNamed) ->
      (programs : Fin count -> RefinementProgram) ->
        NamedEquivalent
          (cumulativePrimitiveFinish start programs).name
          (CCL.ProgressiveCoherence.CoherentNamed.add start
            (sumNamed fun index => (programs index).output)).name
  | 0, start, _programs => by
      let exactZero := CCL.ProgressiveCoherence.CoherentNamed.exact 0
      let geometricZero := geometricNamed
        (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 0)
      have insertExact : NamedEquivalent start.name
          (CCL.ProgressiveCoherence.CoherentNamed.add start exactZero).name :=
        CCL.OperationalEquivalence.NamedEquivalent.symm
          (CCL.OperationalFieldLaws.coherentAdd_zero_right start)
      have replaceZero : NamedEquivalent
          (CCL.ProgressiveCoherence.CoherentNamed.add start exactZero).name
          (CCL.ProgressiveCoherence.CoherentNamed.add start geometricZero).name :=
        CCL.TranscendentalCoherence.coherentAdd_respects
          start start exactZero geometricZero
          (CCL.OperationalEquivalence.NamedEquivalent.refl start.name)
          (CCL.OperationalEquivalence.NamedEquivalent.symm
            geometricZero_equivalent_exact)
      simpa only [cumulativePrimitiveFinish, sumNamed, exactZero,
        geometricZero] using
        CCL.OperationalEquivalence.NamedEquivalent.trans insertExact
          replaceZero
  | count + 1, start, programs => by
      let nextStart := CCL.ProgressiveCoherence.CoherentNamed.add start
        (programs 0).output
      let tailPrograms := fun index : Fin count => programs index.succ
      have tailEquivalent :=
        cumulativePrimitiveFinish_equivalent_add_sumNamed nextStart
          tailPrograms
      have associate := CCL.OperationalFieldLaws.coherentAdd_assoc
        start (programs 0).output
          (sumNamed fun index : Fin count => (programs index.succ).output)
      simpa only [cumulativePrimitiveFinish, sumNamed, nextStart,
        tailPrograms, CCL.ProgressiveCoherence.CoherentNamed.add] using
        CCL.OperationalEquivalence.NamedEquivalent.trans tailEquivalent
          associate

/-- Starting at exact zero, the final cumulative primitive is operationally
the finite recursive sum of its edge programs. -/
def cumulativePrimitiveFinish_zero_equivalent_sumNamed {count : Nat}
    (programs : Fin count -> RefinementProgram) :
    NamedEquivalent
      (cumulativePrimitiveFinish
        (CCL.ProgressiveCoherence.CoherentNamed.exact 0) programs).name
      (sumNamed fun index => (programs index).output).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (cumulativePrimitiveFinish_equivalent_add_sumNamed
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0) programs)
    (CCL.OperationalFieldLaws.coherentAdd_zero_left
      (sumNamed fun index => (programs index).output))

/-- A finite primitive-certified boundary whose last displayed primitive
value is operationally the first. -/
structure ClosedPrimitiveBoundary where
  start : CoherentNamed
  finish : CoherentNamed
  path : PrimitivePath start finish
  closed : NamedEquivalent finish.name start.name

namespace ClosedPrimitiveBoundary

def integralSum (boundary : ClosedPrimitiveBoundary) : CoherentNamed :=
  boundary.path.integralSum

/-- The integral of a finite exact primitive path around its certified closed
boundary vanishes by explicit endpoint telescoping. -/
def integralSum_zero (boundary : ClosedPrimitiveBoundary) :
    NamedEquivalent boundary.integralSum.name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  let negativeStart :=
    CCL.ProgressiveCoherence.CoherentNamed.neg boundary.start
  have closeDifference : NamedEquivalent
      (primitiveDifference boundary.start boundary.finish).name
      (primitiveDifference boundary.start boundary.start).name := by
    simpa only [primitiveDifference, negativeStart,
      CCL.ProgressiveCoherence.CoherentNamed.add] using
      CCL.TranscendentalCoherence.coherentAdd_respects
        negativeStart negativeStart boundary.finish boundary.start
        (CCL.OperationalEquivalence.NamedEquivalent.refl negativeStart.name)
        boundary.closed
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    boundary.path.integralSum_eq_difference
    (CCL.OperationalEquivalence.NamedEquivalent.trans closeDifference
      (primitiveDifference_self_zero boundary.start))

end ClosedPrimitiveBoundary

/-- Fraction-free normalized-period numerator. -/
def numerator {genus : Nat} {curve : HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) (row column : Fin genus) :
    CoherentNamed :=
  matrixMul data.aInverse.adjugate data.toPeriodData.bMatrix row column

/-- Antisymmetric residual of the fraction-free numerator. -/
def numeratorResidual {genus : Nat} {curve : HyperellipticCurve genus}
    (data : NormalizedPeriodData curve) (row column : Fin genus) :
    CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (numerator data row column)
    (CCL.ProgressiveCoherence.CoherentNamed.neg
      (numerator data column row))

/-- The unnormalized first-bilinear-relation residual
`(A Bᵀ - B Aᵀ)ᵢⱼ`.  This is the quantity obtained directly by finite Stokes
edge cancellation before applying any inverse or adjugate. -/
def periodPairingResidual {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (matrixMul data.aMatrix (transpose data.bMatrix) row column)
    (CCL.ProgressiveCoherence.CoherentNamed.neg
      (matrixMul data.bMatrix (transpose data.aMatrix) row column))

/-- Equal-index geometric realization of the unnormalized first-bilinear
residual.  Its finite samples use one synchronized sample of every A- and
B-period entry, so they can be read literally as cut-polygon increments. -/
def synchronizedPeriodPairingResidual {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sub
    (geometricProductEntry
      (geometricMatrixOfNamed data.aMatrix)
      (geometricTranspose (geometricMatrixOfNamed data.bMatrix))
      row column)
    (geometricProductEntry
      (geometricMatrixOfNamed data.bMatrix)
      (geometricTranspose (geometricMatrixOfNamed data.aMatrix))
      row column)

/-- Every synchronized residual sample is exactly the finite symplectic
pairing of the displayed rational A- and B-period matrices. -/
@[simp] theorem synchronizedPeriodPairingResidual_sample {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) (index : Nat) :
    (synchronizedPeriodPairingResidual data row column).sample index =
      CCL.Riemann.FinitePolygonStokes.symplecticPairing
        (sampledMatrix data.aMatrix index)
        (sampledMatrix data.bMatrix index) row column := by
  unfold synchronizedPeriodPairingResidual
  rw [CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sub_sample,
    geometricProductEntry_sample, geometricProductEntry_sample,
    RFAP.ConstructiveFiniteMatrix.mul_apply,
    RFAP.ConstructiveFiniteMatrix.mul_apply,
    CCL.Riemann.FinitePolygonStokes.symplecticPairing,
    ← RFAP.ConstructiveFiniteMatrix.sumFin_sub]
  apply RFAP.ConstructiveFiniteMatrix.sumFin_congr
  intro cycle
  simp only [
    CCL.Riemann.FiniteMatrixApproximation.sampleMatrix_apply,
    geometricTranspose_apply, geometricMatrixOfNamed_apply,
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed_sample,
    sampledMatrix_apply]

/-- The actual stateful matrix expression realizes the synchronized finite
symplectic pairing stream.  This is the operational bridge from persistent
period programs to exact polygon algebra. -/
def periodPairingResidual_equivalent_synchronized {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    NamedEquivalent (periodPairingResidual data row column).name
      (geometricNamed
        (synchronizedPeriodPairingResidual data row column)).name := by
  let aSource := geometricMatrixOfNamed data.aMatrix
  let bSource := geometricMatrixOfNamed data.bMatrix
  let left := matrixMul data.aMatrix (transpose data.bMatrix) row column
  let right := matrixMul data.bMatrix (transpose data.aMatrix) row column
  let leftSource := geometricProductEntry aSource
    (geometricTranspose bSource) row column
  let rightSource := geometricProductEntry bSource
    (geometricTranspose aSource) row column
  have leftEquivalent : NamedEquivalent left.name
      (geometricNamed leftSource).name := by
    exact matrixMul_equivalent_geometricProduct
      data.aMatrix (transpose data.bMatrix)
      aSource (geometricTranspose bSource)
      (fun matrixRow matrixColumn => by
        simpa only [aSource, geometricMatrixOfNamed_apply] using
          named_equivalent_geometricOfNamed
            (data.aMatrix matrixRow matrixColumn))
      (fun matrixRow matrixColumn => by
        simpa only [transpose_apply, geometricTranspose_apply, bSource,
          geometricMatrixOfNamed_apply] using
          named_equivalent_geometricOfNamed
            (data.bMatrix matrixColumn matrixRow))
      row column
  have rightEquivalent : NamedEquivalent right.name
      (geometricNamed rightSource).name := by
    exact matrixMul_equivalent_geometricProduct
      data.bMatrix (transpose data.aMatrix)
      bSource (geometricTranspose aSource)
      (fun matrixRow matrixColumn => by
        simpa only [bSource, geometricMatrixOfNamed_apply] using
          named_equivalent_geometricOfNamed
            (data.bMatrix matrixRow matrixColumn))
      (fun matrixRow matrixColumn => by
        simpa only [transpose_apply, geometricTranspose_apply, aSource,
          geometricMatrixOfNamed_apply] using
          named_equivalent_geometricOfNamed
            (data.aMatrix matrixColumn matrixRow))
      row column
  have negativeEquivalent := coherentNeg_equivalent_geometricNeg
    right rightSource rightEquivalent
  simpa only [periodPairingResidual, synchronizedPeriodPairingResidual,
    left, right, leftSource, rightSource, aSource, bSource,
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.sub] using
    coherentAdd_equivalent_geometricAdd
      left (CCL.ProgressiveCoherence.CoherentNamed.neg right)
      leftSource
      (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.neg
        rightSource)
      leftEquivalent negativeEquivalent

/-- Synchronized doubled cut-polygon boundary stream.  The factor two keeps
all face and edge identities division-free. -/
def synchronizedPeriodPolygonBoundary {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 2)
    (synchronizedPeriodPairingResidual data row column)

/-- At every finite refinement, the synchronized boundary stream is the
literal exact boundary area of all displayed handle commutator polygons. -/
@[simp] theorem synchronizedPeriodPolygonBoundary_sample {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) (index : Nat) :
    (synchronizedPeriodPolygonBoundary data row column).sample index =
      CCL.Riemann.FinitePolygonStokes.symplecticBoundaryArea
        (sampledMatrix data.aMatrix index)
        (sampledMatrix data.bMatrix index) row column := by
  rw [synchronizedPeriodPolygonBoundary,
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul_sample,
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact_sample,
    synchronizedPeriodPairingResidual_sample,
    CCL.Riemann.FinitePolygonStokes.symplecticBoundaryArea_eq_two_mul_pairing]

/-- The stateful doubled residual and the exact synchronized polygon boundary
are the same operational finite object. -/
def doubledPeriodPairingResidual_equivalent_polygonBoundary {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (CCL.ProgressiveCoherence.CoherentNamed.exact 2)
        (periodPairingResidual data row column)).name
      (geometricNamed
        (synchronizedPeriodPolygonBoundary data row column)).name := by
  simpa only [synchronizedPeriodPolygonBoundary] using
    coherentMul_equivalent_geometricMul
      (CCL.ProgressiveCoherence.CoherentNamed.exact 2)
      (periodPairingResidual data row column)
      (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 2)
      (synchronizedPeriodPairingResidual data row column)
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (geometricExact_equivalent_exact 2))
      (periodPairingResidual_equivalent_synchronized data row column)

/-- One displayed symplectic-cycle contribution
`Aᵢₖ Bⱼₖ - Bᵢₖ Aⱼₖ` to the first bilinear relation. -/
def periodPairingCycleTerm {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (CCL.ProgressiveCoherence.CoherentNamed.mul
      (data.aMatrix row cycle) (data.bMatrix column cycle))
    (CCL.ProgressiveCoherence.CoherentNamed.neg
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.bMatrix row cycle) (data.aMatrix column cycle)))

/-- Synchronized finite program for the positive product
`Aᵢₖ Bⱼₖ` in one symplectic-cycle contribution. -/
def periodPairingLeftProductProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) : RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram.multiply
    (data.aProgram row cycle).integral
    (data.bProgram column cycle).integral

/-- Synchronized finite program for the negative-side product
`Bᵢₖ Aⱼₖ` in one symplectic-cycle contribution. -/
def periodPairingRightProductProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) : RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram.multiply
    (data.bProgram row cycle).integral
    (data.aProgram column cycle).integral

/-- Arithmetic value assembled from the two explicit synchronized product
programs. -/
def periodPairingCycleProgramValue {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add
    (periodPairingLeftProductProgram data row column cycle).output
    (CCL.ProgressiveCoherence.CoherentNamed.neg
      (periodPairingRightProductProgram data row column cycle).output)

/-- One actual finite refinement program for the antisymmetric cycle term.
Its samples come from the displayed arithmetic CCL rather than from an
unstructured convergence field. -/
def periodPairingCycleProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) : RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram.ofCoherentNamed
    (periodPairingCycleProgramValue data row column cycle)

def periodPairingLeftProduct_equivalent {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.aMatrix row cycle) (data.bMatrix column cycle)).name
      (periodPairingLeftProductProgram data row column cycle).output.name := by
  simpa only [periodPairingLeftProductProgram, PeriodData.aMatrix_apply,
    PeriodData.bMatrix_apply, CertifiedPeriodProgram.output,
    CertifiedPeriodProgram.toPeriodProgram,
    CCL.Riemann.LiftedPaths.PeriodProgram.output] using
    multiplyProgram_output_equivalent
      (data.aProgram row cycle).integral
      (data.bProgram column cycle).integral

def periodPairingRightProduct_equivalent {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (data.bMatrix row cycle) (data.aMatrix column cycle)).name
      (periodPairingRightProductProgram data row column cycle).output.name := by
  simpa only [periodPairingRightProductProgram, PeriodData.aMatrix_apply,
    PeriodData.bMatrix_apply, CertifiedPeriodProgram.output,
    CertifiedPeriodProgram.toPeriodProgram,
    CCL.Riemann.LiftedPaths.PeriodProgram.output] using
    multiplyProgram_output_equivalent
      (data.bProgram row cycle).integral
      (data.aProgram column cycle).integral

/-- The original period-matrix expression is operationally represented by
the arithmetic value built from its two explicit product programs. -/
def periodPairingCycleTerm_equivalent_programValue {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) :
    NamedEquivalent (periodPairingCycleTerm data row column cycle).name
      (periodPairingCycleProgramValue data row column cycle).name := by
  let leftOriginal := CCL.ProgressiveCoherence.CoherentNamed.mul
    (data.aMatrix row cycle) (data.bMatrix column cycle)
  let rightOriginal := CCL.ProgressiveCoherence.CoherentNamed.mul
    (data.bMatrix row cycle) (data.aMatrix column cycle)
  let leftProgram := periodPairingLeftProductProgram data row column cycle
  let rightProgram := periodPairingRightProductProgram data row column cycle
  have leftEquivalent : NamedEquivalent leftOriginal.name
      leftProgram.output.name := by
    simpa only [leftOriginal, leftProgram] using
      periodPairingLeftProduct_equivalent data row column cycle
  have rightEquivalent : NamedEquivalent rightOriginal.name
      rightProgram.output.name := by
    simpa only [rightOriginal, rightProgram] using
      periodPairingRightProduct_equivalent data row column cycle
  have negativeEquivalent := coherentNeg_respects rightOriginal
    rightProgram.output rightEquivalent
  simpa only [periodPairingCycleTerm, periodPairingCycleProgramValue,
    leftOriginal, rightOriginal, leftProgram, rightProgram,
    CCL.ProgressiveCoherence.CoherentNamed.add,
    CCL.ProgressiveCoherence.CoherentNamed.neg] using
    CCL.TranscendentalCoherence.coherentAdd_respects
      leftOriginal leftProgram.output
      (CCL.ProgressiveCoherence.CoherentNamed.neg rightOriginal)
      (CCL.ProgressiveCoherence.CoherentNamed.neg rightProgram.output)
      leftEquivalent negativeEquivalent

/-- Each antisymmetric cycle contribution is now backed by one explicit
finite refinement program suitable for primitive or paired Stokes boundaries. -/
def periodPairingCycleTerm_equivalent_program {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (row column cycle : Fin genus) :
    NamedEquivalent (periodPairingCycleTerm data row column cycle).name
      (periodPairingCycleProgram data row column cycle).output.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (periodPairingCycleTerm_equivalent_programValue data row column cycle)
    (ofCoherentNamed_output_equivalent
      (periodPairingCycleProgramValue data row column cycle))

/-- The direct finite sum of all symplectic-cycle contributions. -/
def periodPairingCycleSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    CoherentNamed :=
  sumNamed fun cycle => periodPairingCycleTerm data row column cycle

/-- Finite recursive sum of the explicit cycle-term program outputs. -/
def periodPairingCycleProgramSumValue {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) : CoherentNamed :=
  sumNamed fun cycle => (periodPairingCycleProgram data row column cycle).output

/-- One finite refinement program carrying the complete antisymmetric
symplectic-cycle sum. -/
def periodPairingCycleSumProgram {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) : RefinementProgram :=
  CCL.ProgressiveGaussianIntegration.RefinementProgram.ofCoherentNamed
    (periodPairingCycleProgramSumValue data row column)

/-- Termwise product-program correctness lifts through the finite recursive
cycle sum. -/
def periodPairingCycleSum_equivalent_programValue {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    NamedEquivalent (periodPairingCycleSum data row column).name
      (periodPairingCycleProgramSumValue data row column).name := by
  unfold periodPairingCycleSum periodPairingCycleProgramSumValue
  exact sumNamed_respects
    (fun cycle => periodPairingCycleTerm data row column cycle)
    (fun cycle => (periodPairingCycleProgram data row column cycle).output)
    (fun cycle =>
      periodPairingCycleTerm_equivalent_program data row column cycle)

/-- The complete first-relation cycle sum is represented by one actual finite
Gaussian refinement program. -/
def periodPairingCycleSum_equivalent_program {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    NamedEquivalent (periodPairingCycleSum data row column).name
      (periodPairingCycleSumProgram data row column).output.name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (periodPairingCycleSum_equivalent_programValue data row column)
    (ofCoherentNamed_output_equivalent
      (periodPairingCycleProgramSumValue data row column))

/-- Endpoint reached by cumulatively adjoining all explicit cycle-term
programs, starting from exact zero. -/
def periodPairingPrimitiveFinish {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) : CoherentNamed :=
  cumulativePrimitiveFinish
    (CCL.ProgressiveCoherence.CoherentNamed.exact 0)
    (fun cycle => periodPairingCycleProgram data row column cycle)

/-- Canonical primitive path whose edges are precisely the finite programs
for the antisymmetric symplectic-cycle terms. -/
def periodPairingPrimitivePath {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    PrimitivePath (CCL.ProgressiveCoherence.CoherentNamed.exact 0)
      (periodPairingPrimitiveFinish data row column) :=
  cumulativePrimitivePath
    (CCL.ProgressiveCoherence.CoherentNamed.exact 0)
    (fun cycle => periodPairingCycleProgram data row column cycle)

/-- The canonical accumulated primitive endpoint is represented by the one
explicit refinement program carrying the complete synchronized cycle sum. -/
def periodPairingPrimitiveFinish_equivalent_program {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    NamedEquivalent (periodPairingPrimitiveFinish data row column).name
      (periodPairingCycleSumProgram data row column).output.name := by
  apply CCL.OperationalEquivalence.NamedEquivalent.trans
    (cumulativePrimitiveFinish_zero_equivalent_sumNamed
      (fun cycle => periodPairingCycleProgram data row column cycle))
  simpa only [periodPairingCycleSumProgram,
    periodPairingCycleProgramSumValue] using
    ofCoherentNamed_output_equivalent
      (periodPairingCycleProgramSumValue data row column)

/-- The only closure datum needed by the canonical finite Stokes boundary:
the explicitly accumulated cycle-term primitive returns operationally to its
displayed starting zero.  Edge programs, endpoints, FTC identities, and the
comparison with the period matrix are all derived. -/
structure FiniteStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve) where
  closed : forall row column : Fin genus,
    NamedEquivalent (periodPairingPrimitiveFinish data row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name

namespace FiniteStokesClosure

/-- Materialize the canonical closed primitive boundary for one pair of
differentials. -/
def boundary {genus : Nat} {curve : HyperellipticCurve genus}
    {data : PeriodData curve} (closure : FiniteStokesClosure data)
    (row column : Fin genus) : ClosedPrimitiveBoundary where
  start := CCL.ProgressiveCoherence.CoherentNamed.exact 0
  finish := periodPairingPrimitiveFinish data row column
  path := periodPairingPrimitivePath data row column
  closed := closure.closed row column

/-- The original period-pairing cycle sum is automatically identified with
the integral sum of the canonical primitive boundary. -/
def cycleSum_eq_boundary {genus : Nat} {curve : HyperellipticCurve genus}
    {data : PeriodData curve} (closure : FiniteStokesClosure data)
    (row column : Fin genus) :
    NamedEquivalent (periodPairingCycleSum data row column).name
      (closure.boundary row column).integralSum.name := by
  apply CCL.OperationalEquivalence.NamedEquivalent.trans
    (periodPairingCycleSum_equivalent_programValue data row column)
  apply CCL.OperationalEquivalence.NamedEquivalent.symm
  change NamedEquivalent
    (cumulativePrimitivePath
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0)
      (fun cycle => periodPairingCycleProgram data row column cycle)).integralSum.name
    (sumNamed fun cycle =>
      (periodPairingCycleProgram data row column cycle).output).name
  exact cumulativePrimitivePath_integralSum_equivalent_sumNamed
    (CCL.ProgressiveCoherence.CoherentNamed.exact 0)
    (fun cycle => periodPairingCycleProgram data row column cycle)

end FiniteStokesClosure

/-- Matrix notation for `A Bᵀ - B Aᵀ` is operationally the explicit finite
sum of the displayed cycle-pairing terms. -/
def periodPairingResidual_equivalent_cycleSum {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    NamedEquivalent (periodPairingResidual data row column).name
      (periodPairingCycleSum data row column).name := by
  let leftTerms := fun cycle : Fin genus =>
    CCL.ProgressiveCoherence.CoherentNamed.mul
      (data.aMatrix row cycle) (data.bMatrix column cycle)
  let rightTerms := fun cycle : Fin genus =>
    CCL.ProgressiveCoherence.CoherentNamed.mul
      (data.bMatrix row cycle) (data.aMatrix column cycle)
  let negativeRightTerms := fun cycle : Fin genus =>
    CCL.ProgressiveCoherence.CoherentNamed.neg (rightTerms cycle)
  have splitTerms : NamedEquivalent
      (periodPairingCycleSum data row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (sumNamed leftTerms) (sumNamed negativeRightTerms)).name := by
    change NamedEquivalent
      (sumNamed fun cycle =>
        CCL.ProgressiveCoherence.CoherentNamed.add
          (leftTerms cycle) (negativeRightTerms cycle)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (sumNamed leftTerms) (sumNamed negativeRightTerms)).name
    exact sumNamed_add leftTerms negativeRightTerms
  have collectNegative : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (sumNamed leftTerms) (sumNamed negativeRightTerms)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (sumNamed leftTerms)
        (CCL.ProgressiveCoherence.CoherentNamed.neg
          (sumNamed rightTerms))).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      (sumNamed leftTerms) (sumNamed leftTerms)
      (sumNamed negativeRightTerms)
      (CCL.ProgressiveCoherence.CoherentNamed.neg (sumNamed rightTerms))
      (CCL.OperationalEquivalence.NamedEquivalent.refl _)
      (by
        change NamedEquivalent
          (sumNamed fun cycle =>
            CCL.ProgressiveCoherence.CoherentNamed.neg
              (rightTerms cycle)).name
          (CCL.ProgressiveCoherence.CoherentNamed.neg
            (sumNamed rightTerms)).name
        exact sumNamed_neg rightTerms)
  have leftEquivalent : NamedEquivalent
      (matrixMul data.aMatrix (transpose data.bMatrix) row column).name
      (sumNamed leftTerms).name := by
    rw [matrixMul_apply]
    apply sumNamed_respects
    intro cycle
    unfold leftTerms
    rw [transpose_apply]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  have rightEquivalent : NamedEquivalent
      (matrixMul data.bMatrix (transpose data.aMatrix) row column).name
      (sumNamed rightTerms).name := by
    rw [matrixMul_apply]
    apply sumNamed_respects
    intro cycle
    unfold rightTerms
    rw [transpose_apply]
    exact CCL.OperationalEquivalence.NamedEquivalent.refl _
  have residualEquivalent : NamedEquivalent
      (periodPairingResidual data row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.add
        (sumNamed leftTerms)
        (CCL.ProgressiveCoherence.CoherentNamed.neg
          (sumNamed rightTerms))).name := by
    unfold periodPairingResidual
    exact CCL.TranscendentalCoherence.coherentAdd_respects
      (matrixMul data.aMatrix (transpose data.bMatrix) row column)
      (sumNamed leftTerms)
      (CCL.ProgressiveCoherence.CoherentNamed.neg
        (matrixMul data.bMatrix (transpose data.aMatrix) row column))
      (CCL.ProgressiveCoherence.CoherentNamed.neg (sumNamed rightTerms))
      leftEquivalent
      (coherentNeg_respects
        (matrixMul data.bMatrix (transpose data.aMatrix) row column)
        (sumNamed rightTerms) rightEquivalent)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans residualEquivalent
    (CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.OperationalEquivalence.NamedEquivalent.trans splitTerms
        collectNegative))

/-- The unnormalized first-relation residual is operationally
skew-symmetric.  This is proved directly from the two finite matrix-product
sums and stateful commutativity of each displayed product. -/
def periodPairingResidual_swap {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    NamedEquivalent (periodPairingResidual data column row).name
      (CCL.ProgressiveCoherence.CoherentNamed.neg
        (periodPairingResidual data row column)).name := by
  let left := matrixMul data.aMatrix (transpose data.bMatrix) row column
  let right := matrixMul data.bMatrix (transpose data.aMatrix) row column
  let swappedLeft :=
    matrixMul data.aMatrix (transpose data.bMatrix) column row
  let swappedRight :=
    matrixMul data.bMatrix (transpose data.aMatrix) column row
  have swappedLeft_eq_right : NamedEquivalent swappedLeft.name right.name := by
    unfold swappedLeft right
    rw [matrixMul_apply, matrixMul_apply]
    apply sumNamed_respects
    intro cycle
    rw [transpose_apply, transpose_apply]
    exact CCL.TranscendentalCoherence.coherentMul_comm
      (data.aMatrix column cycle) (data.bMatrix row cycle)
  have swappedRight_eq_left : NamedEquivalent swappedRight.name left.name := by
    unfold swappedRight left
    rw [matrixMul_apply, matrixMul_apply]
    apply sumNamed_respects
    intro cycle
    rw [transpose_apply, transpose_apply]
    exact CCL.TranscendentalCoherence.coherentMul_comm
      (data.bMatrix column cycle) (data.aMatrix row cycle)
  have replaceBoth : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add swappedLeft
        (CCL.ProgressiveCoherence.CoherentNamed.neg swappedRight)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add right
        (CCL.ProgressiveCoherence.CoherentNamed.neg left)).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      swappedLeft right
      (CCL.ProgressiveCoherence.CoherentNamed.neg swappedRight)
      (CCL.ProgressiveCoherence.CoherentNamed.neg left)
      swappedLeft_eq_right
      (coherentNeg_respects swappedRight left swappedRight_eq_left)
  have residualReplace : NamedEquivalent
      (periodPairingResidual data column row).name
      (CCL.ProgressiveCoherence.CoherentNamed.add right
        (CCL.ProgressiveCoherence.CoherentNamed.neg left)).name := by
    unfold periodPairingResidual
    change NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add swappedLeft
        (CCL.ProgressiveCoherence.CoherentNamed.neg swappedRight)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add right
        (CCL.ProgressiveCoherence.CoherentNamed.neg left)).name
    exact replaceBoth
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    residualReplace
    (coherentSub_swap left right)

/-- The canonical primitive endpoint and the matrix-form first-relation
residual are two finite operational presentations of the same value. -/
def periodPairingPrimitiveFinish_equivalent_residual {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    NamedEquivalent (periodPairingPrimitiveFinish data row column).name
      (periodPairingResidual data row column).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (cumulativePrimitiveFinish_zero_equivalent_sumNamed
      (fun cycle => periodPairingCycleProgram data row column cycle))
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (periodPairingCycleSum_equivalent_programValue data row column))
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (periodPairingResidual_equivalent_cycleSum data row column)))

/-- Swapping the two differential indices negates the accumulated canonical
Stokes primitive. -/
def periodPairingPrimitiveFinish_swap {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    NamedEquivalent (periodPairingPrimitiveFinish data column row).name
      (CCL.ProgressiveCoherence.CoherentNamed.neg
        (periodPairingPrimitiveFinish data row column)).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (periodPairingPrimitiveFinish_equivalent_residual data column row)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (periodPairingResidual_swap data row column)
      (coherentNeg_respects
        (periodPairingResidual data row column)
        (periodPairingPrimitiveFinish data row column)
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          (periodPairingPrimitiveFinish_equivalent_residual data row column))))

namespace FiniteStokesClosure

/-- On the diagonal the two finite matrix-product sums agree term by term by
operational commutativity, so the unnormalized antisymmetric residual is
zero. -/
def periodPairingResidual_diagonal_zero {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row : Fin genus) :
    NamedEquivalent (periodPairingResidual data row row).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  let left := matrixMul data.aMatrix (transpose data.bMatrix) row row
  let right := matrixMul data.bMatrix (transpose data.aMatrix) row row
  have products : NamedEquivalent left.name right.name := by
    unfold left right
    rw [matrixMul_apply, matrixMul_apply]
    apply sumNamed_respects
    intro cycle
    rw [transpose_apply, transpose_apply]
    exact CCL.TranscendentalCoherence.coherentMul_comm
      (data.aMatrix row cycle) (data.bMatrix row cycle)
  have replaceLeft : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add left
        (CCL.ProgressiveCoherence.CoherentNamed.neg right)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add right
        (CCL.ProgressiveCoherence.CoherentNamed.neg right)).name :=
    CCL.TranscendentalCoherence.coherentAdd_respects
      left right
      (CCL.ProgressiveCoherence.CoherentNamed.neg right)
      (CCL.ProgressiveCoherence.CoherentNamed.neg right)
      products (CCL.OperationalEquivalence.NamedEquivalent.refl _)
  have cancelRight : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add right
        (CCL.ProgressiveCoherence.CoherentNamed.neg right)).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
    simpa only [CCL.ProgressiveCoherence.CoherentNamed.add,
      CCL.ProgressiveCoherence.CoherentNamed.neg,
      CCL.ProgressiveCoherence.CoherentNamed.exact] using
      CCL.OperationalFieldLaws.coherentAdd_neg_right right
  have residualReplace : NamedEquivalent
      (periodPairingResidual data row row).name
      (CCL.ProgressiveCoherence.CoherentNamed.add right
        (CCL.ProgressiveCoherence.CoherentNamed.neg right)).name := by
    unfold periodPairingResidual
    change NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.add left
        (CCL.ProgressiveCoherence.CoherentNamed.neg right)).name
      (CCL.ProgressiveCoherence.CoherentNamed.add right
        (CCL.ProgressiveCoherence.CoherentNamed.neg right)).name
    exact replaceLeft
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    residualReplace
    cancelRight

/-- The canonical primitive used by the finite Stokes interface therefore
closes automatically on every diagonal entry.  The proof passes through the
actual synchronized product programs, rather than replacing their outputs by
an untracked algebraic expression. -/
def periodPairingPrimitiveFinish_diagonal_zero {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) (row : Fin genus) :
    NamedEquivalent (periodPairingPrimitiveFinish data row row).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (cumulativePrimitiveFinish_zero_equivalent_sumNamed
      (fun cycle => periodPairingCycleProgram data row row cycle))
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (periodPairingCycleSum_equivalent_programValue data row row))
      (CCL.OperationalEquivalence.NamedEquivalent.trans
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          (periodPairingResidual_equivalent_cycleSum data row row))
        (periodPairingResidual_diagonal_zero data row)))

/-- If the finite differential index has at most one member, every entry is
diagonal and the complete finite Stokes closure is constructed without a
surface-boundary certificate. -/
def ofSubsingleton {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve)
    (allEqual : forall row column : Fin genus, row = column) :
    FiniteStokesClosure data where
  closed := by
    intro row column
    cases allEqual row column
    exact periodPairingPrimitiveFinish_diagonal_zero data row

/-- In genus one the first Riemann bilinear relation needs no separately
supplied Stokes datum: the sole matrix entry is diagonal. -/
def genusOne {curve : HyperellipticCurve 1} (data : PeriodData curve) :
    FiniteStokesClosure data :=
  ofSubsingleton data (fun row column => Subsingleton.elim row column)

end FiniteStokesClosure

/-- Minimal independent first-relation data: diagonal entries are automatic,
and skew-symmetry reconstructs the lower triangle, so only strict
upper-triangular primitive closures are supplied. -/
structure UpperTriangularStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve) where
  closed_of_lt : forall row column : Fin genus, row.val < column.val ->
    NamedEquivalent (periodPairingPrimitiveFinish data row column).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name

namespace UpperTriangularStokesClosure

/-- Reconstruct the complete finite Stokes closure from exactly its
independent upper-triangular entries. -/
def toFiniteStokesClosure {genus : Nat}
    {curve : HyperellipticCurve genus} {data : PeriodData curve}
    (upper : UpperTriangularStokesClosure data) :
    FiniteStokesClosure data where
  closed := by
    intro row column
    by_cases equal : row = column
    · subst column
      exact FiniteStokesClosure.periodPairingPrimitiveFinish_diagonal_zero
        data row
    · by_cases less : row.val < column.val
      · exact upper.closed_of_lt row column less
      · have reverseLess : column.val < row.val := by
          have differentValues : row.val ≠ column.val := by
            intro valuesEqual
            exact equal (Fin.ext valuesEqual)
          omega0
        have reverseZero := upper.closed_of_lt column row reverseLess
        exact CCL.OperationalEquivalence.NamedEquivalent.trans
          (periodPairingPrimitiveFinish_swap data column row)
          (CCL.OperationalEquivalence.NamedEquivalent.trans
            (coherentNeg_respects
              (periodPairingPrimitiveFinish data column row)
              (CCL.ProgressiveCoherence.CoherentNamed.exact 0)
              reverseZero)
            (CCL.OperationalEquivalence.NamedEquivalent.symm
              zero_equivalent_neg_zero))

/-- In genus two there is exactly one independent first-relation equation,
the `(0,1)` entry. -/
def genusTwo {curve : HyperellipticCurve 2} (data : PeriodData curve)
    (zeroOne : NamedEquivalent
      (periodPairingPrimitiveFinish data 0 1).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name) :
    UpperTriangularStokesClosure data where
  closed_of_lt := by
    intro row column less
    have rowZero : row = (0 : Fin 2) := by
      apply Fin.ext
      omega0
    have columnOne : column = (1 : Fin 2) := by
      apply Fin.ext
      omega0
    subst row
    subst column
    exact zeroOne

end UpperTriangularStokesClosure

namespace FiniteStokesClosure

/-- One off-diagonal surface calculation closes the complete genus-two first
bilinear relation. -/
def genusTwo_of_zeroOne {curve : HyperellipticCurve 2}
    (data : PeriodData curve)
    (zeroOne : NamedEquivalent
      (periodPairingPrimitiveFinish data 0 1).name
      (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name) :
    FiniteStokesClosure data :=
  (UpperTriangularStokesClosure.genusTwo data zeroOne).toFiniteStokesClosure

end FiniteStokesClosure

/-- The canonical adjugate turns the unnormalized first bilinear relation
`A Bᵀ = B Aᵀ` into symmetry of `adj(A) B`.  The argument is entirely finite:
the relation is sandwiched by `adj(A)` and its transpose, both scaled-inverse
identities are operational theorems, and the apart scalar is cancelled by its
productive reciprocal. -/
def numeratorMatrix_symmetric_of_periodRelation {size : Nat}
    (a b : NamedMatrix size) (inverse : ScaledInverseCertificate a)
    (periodRelation : MatrixEquivalent
      (matrixMul a (transpose b))
      (matrixMul b (transpose a))) :
    MatrixEquivalent (matrixMul inverse.adjugate b)
      (transpose (matrixMul inverse.adjugate b)) := by
  let c := inverse.adjugate
  let scalar := inverse.scalar
  let n := matrixMul c b
  let aBt := matrixMul a (transpose b)
  let bAt := matrixMul b (transpose a)
  let cTranspose := transpose c
  let leftSandwich := matrixMul (matrixMul c aBt) cTranspose
  let rightSandwich := matrixMul (matrixMul c bAt) cTranspose
  have cRefl : MatrixEquivalent c c := MatrixEquivalent.refl c
  have cTransposeRefl : MatrixEquivalent cTranspose cTranspose :=
    MatrixEquivalent.refl cTranspose
  have sandwichedRelation : MatrixEquivalent leftSandwich rightSandwich := by
    have leftMultiply : MatrixEquivalent
        (matrixMul c aBt) (matrixMul c bAt) :=
      matrixMul_respects c c aBt bAt cRefl (by
        simpa only [aBt, bAt] using periodRelation)
    exact matrixMul_respects
      (matrixMul c aBt) (matrixMul c bAt)
      cTranspose cTranspose leftMultiply cTransposeRefl
  have caScaled : MatrixEquivalent (matrixMul c a)
      (scaleIdentity scalar) := by
    intro row column
    simpa only [c, scalar] using inverse.left_identity row column
  have bTranspose_cTranspose : MatrixEquivalent
      (matrixMul (transpose b) cTranspose) (transpose n) := by
    exact MatrixEquivalent.symm (by
      simpa only [cTranspose, n, c] using matrixMul_transpose c b)
  have leftReduction : MatrixEquivalent leftSandwich
      (scalarMul scalar (transpose n)) := by
    have exposeCA : MatrixEquivalent
        (matrixMul c aBt)
        (matrixMul (matrixMul c a) (transpose b)) :=
      MatrixEquivalent.symm (by
        simpa only [aBt] using matrixMul_assoc c a (transpose b))
    have exposeCAInside : MatrixEquivalent leftSandwich
        (matrixMul (matrixMul (matrixMul c a) (transpose b))
          cTranspose) := by
      exact matrixMul_respects
        (matrixMul c aBt)
        (matrixMul (matrixMul c a) (transpose b))
        cTranspose cTranspose exposeCA cTransposeRefl
    have associateRight : MatrixEquivalent
        (matrixMul (matrixMul (matrixMul c a) (transpose b)) cTranspose)
        (matrixMul (matrixMul c a)
          (matrixMul (transpose b) cTranspose)) :=
      matrixMul_assoc (matrixMul c a) (transpose b) cTranspose
    have replaceFactors : MatrixEquivalent
        (matrixMul (matrixMul c a)
          (matrixMul (transpose b) cTranspose))
        (matrixMul (scaleIdentity scalar) (transpose n)) :=
      matrixMul_respects (matrixMul c a) (scaleIdentity scalar)
        (matrixMul (transpose b) cTranspose) (transpose n)
        caScaled bTranspose_cTranspose
    exact MatrixEquivalent.trans exposeCAInside
      (MatrixEquivalent.trans associateRight
        (MatrixEquivalent.trans replaceFactors
          (scaleIdentity_mul scalar (transpose n))))
  have aTranspose_cTranspose_scaled : MatrixEquivalent
      (matrixMul (transpose a) cTranspose) (scaleIdentity scalar) := by
    have toTransposeCA : MatrixEquivalent
        (matrixMul (transpose a) cTranspose) (transpose (matrixMul c a)) :=
      MatrixEquivalent.symm (by
        simpa only [cTranspose] using matrixMul_transpose c a)
    exact MatrixEquivalent.trans toTransposeCA
      (MatrixEquivalent.trans (transpose_respects caScaled)
        (transpose_scaleIdentity scalar))
  have rightReduction : MatrixEquivalent rightSandwich
      (scalarMul scalar n) := by
    have exposeCB : MatrixEquivalent
        (matrixMul c bAt)
        (matrixMul n (transpose a)) :=
      MatrixEquivalent.symm (by
        simpa only [bAt, n] using matrixMul_assoc c b (transpose a))
    have exposeCBInside : MatrixEquivalent rightSandwich
        (matrixMul (matrixMul n (transpose a)) cTranspose) := by
      exact matrixMul_respects
        (matrixMul c bAt) (matrixMul n (transpose a))
        cTranspose cTranspose exposeCB cTransposeRefl
    have associateRight : MatrixEquivalent
        (matrixMul (matrixMul n (transpose a)) cTranspose)
        (matrixMul n (matrixMul (transpose a) cTranspose)) :=
      matrixMul_assoc n (transpose a) cTranspose
    have replaceFactor : MatrixEquivalent
        (matrixMul n (matrixMul (transpose a) cTranspose))
        (matrixMul n (scaleIdentity scalar)) :=
      matrixMul_respects n n
        (matrixMul (transpose a) cTranspose) (scaleIdentity scalar)
        (MatrixEquivalent.refl n) aTranspose_cTranspose_scaled
    exact MatrixEquivalent.trans exposeCBInside
      (MatrixEquivalent.trans associateRight
        (MatrixEquivalent.trans replaceFactor
          (matrixMul_scaleIdentity n scalar)))
  have scaledSymmetry : MatrixEquivalent
      (scalarMul scalar (transpose n)) (scalarMul scalar n) :=
    MatrixEquivalent.trans (MatrixEquivalent.symm leftReduction)
      (MatrixEquivalent.trans sandwichedRelation rightReduction)
  intro row column
  have scaledEntry := scaledSymmetry row column
  rw [scalarMul_apply, scalarMul_apply, transpose_apply] at scaledEntry
  apply CCL.OperationalEquivalence.NamedEquivalent.symm
  simpa only [n, c, transpose_apply] using
    CCL.Riemann.OperationalQuotients.coherentMul_cancel_left
      scalar (n column row) (n row column) inverse.scalarApart scaledEntry

/-- Finite Stokes data for the first bilinear relation.  A certificate may
display either cellwise reversed edge pairs or a closed path of edge integrals
with explicit primitive endpoint differences.  Its analytic bridge starts
from the explicit finite cycle sum `Σₖ(AᵢₖBⱼₖ-BᵢₖAⱼₖ)`; matrix notation,
inverse identities, and adjugate symmetry are all derived theorems. -/
inductive StokesCertificate {genus : Nat}
    {curve : HyperellipticCurve genus}
    (data : PeriodData curve) : Type 2
  | pairedBoundary
      (edgePairCount : Nat)
      (edgePairs : Fin genus -> Fin genus ->
        Fin edgePairCount -> ProgramBoundaryPair)
      (cycleSum_eq_boundary : forall row column : Fin genus,
        NamedEquivalent (periodPairingCycleSum data row column).name
          (boundarySum (fun index =>
            (edgePairs row column index).toBoundaryPair)).name)
  | primitiveBoundary
      (boundaries : Fin genus -> Fin genus -> ClosedPrimitiveBoundary)
      (cycleSum_eq_boundary : forall row column : Fin genus,
        NamedEquivalent (periodPairingCycleSum data row column).name
          (boundaries row column).integralSum.name)

namespace FiniteStokesClosure

/-- The concrete closure of the canonical cycle-term primitive path supplies
the existing first-bilinear-relation interface without any separately chosen
edge family or cycle-sum comparison. -/
def toStokesCertificate {genus : Nat} {curve : HyperellipticCurve genus}
    {data : PeriodData curve} (closure : FiniteStokesClosure data) :
    StokesCertificate data :=
  .primitiveBoundary
    (fun row column => closure.boundary row column)
    (fun row column => closure.cycleSum_eq_boundary row column)

end FiniteStokesClosure

namespace StokesCertificate

/-- Finite edge cancellation or primitive endpoint telescoping makes the
direct unnormalized period-pairing residual operationally zero. -/
def pairingResidual_zero {genus : Nat} {curve : HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : StokesCertificate data)
    (row column : Fin genus) :
    NamedEquivalent (periodPairingResidual data row column).name
    (CCL.ProgressiveCoherence.CoherentNamed.exact 0).name := by
  cases certificate with
  | pairedBoundary edgePairCount edgePairs cycleSumEquivalent =>
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (periodPairingResidual_equivalent_cycleSum data row column)
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          (cycleSumEquivalent row column)
          (boundarySum_zero fun index =>
            (edgePairs row column index).toBoundaryPair))
  | primitiveBoundary boundaries cycleSumEquivalent =>
      exact CCL.OperationalEquivalence.NamedEquivalent.trans
        (periodPairingResidual_equivalent_cycleSum data row column)
        (CCL.OperationalEquivalence.NamedEquivalent.trans
          (cycleSumEquivalent row column)
          (boundaries row column).integralSum_zero)

/-- The paired finite boundary proves the natural matrix identity
`A Bᵀ = B Aᵀ` before normalization. -/
def periodRelation {genus : Nat} {curve : HyperellipticCurve genus}
    {data : PeriodData curve} (certificate : StokesCertificate data) :
    MatrixEquivalent
      (matrixMul data.aMatrix (transpose data.bMatrix))
      (matrixMul data.bMatrix (transpose data.aMatrix)) := by
  intro row column
  exact equivalent_of_sub_zero
    (matrixMul data.aMatrix (transpose data.bMatrix) row column)
    (matrixMul data.bMatrix (transpose data.aMatrix) row column)
    (by simpa only [periodPairingResidual] using
      certificate.pairingResidual_zero row column)

/-- The finite Stokes certificate implies the operational numerator symmetry
used by normalized period matrices. -/
def numeratorSymmetry {genus : Nat} {curve : HyperellipticCurve genus}
    {data : NormalizedPeriodData curve}
    (certificate : StokesCertificate data.toPeriodData) :
    NormalizedPeriodData.NumeratorSymmetryCertificate data where
  symmetric := by
    intro row column
    have symmetricMatrix := numeratorMatrix_symmetric_of_periodRelation
      data.toPeriodData.aMatrix data.toPeriodData.bMatrix data.aInverse
      certificate.periodRelation
    simpa only [transpose_apply] using symmetricMatrix row column

end StokesCertificate

/-- The bilinear input meaningful before A-period inversion: closure of the
canonical finite Stokes boundary for the first relation.  Positive energy is
requested only after a synchronized fraction-free inverse sample has supplied
the exact raw differential coefficients to be integrated. -/
structure PreNormalizationCertificate {genus : Nat}
    {curve : HyperellipticCurve genus} (data : PeriodData curve) where
  stokesClosure : FiniteStokesClosure data

namespace PreNormalizationCertificate

/-- The broad Stokes interface is derived from closure of the one canonical
finite primitive path, not accepted as independently chosen boundary data. -/
def stokes {genus : Nat} {curve : HyperellipticCurve genus}
    {data : PeriodData curve}
    (certificate : PreNormalizationCertificate data) : StokesCertificate data :=
  certificate.stokesClosure.toStokesCertificate

end PreNormalizationCertificate

/-- The pre-normalization bilinear data together with the derived normalized
pointwise energy comparison. -/
structure Certificate {genus : Nat}
    {curve : HyperellipticCurve genus} (data : NormalizedPeriodData curve) where
  preNormalization : PreNormalizationCertificate data.toPeriodData
  energy : CCL.Riemann.FiniteEnergy.Certificate data

namespace Certificate

/-- The first-relation Stokes certificate is retained from the explicitly
pre-normalized package. -/
def stokes {genus : Nat}
    {curve : HyperellipticCurve genus} {data : NormalizedPeriodData curve}
    (certificate : Certificate data) : StokesCertificate data.toPeriodData :=
  certificate.preNormalization.stokes

/-- Pointwise matrix positivity is a consequence of the finite cell-energy
certificate, not an independent field of the bilinear package. -/
def positivity {genus : Nat}
    {curve : HyperellipticCurve genus} {data : NormalizedPeriodData curve}
    (certificate : Certificate data) :
    CCL.Riemann.FinitePositivity.Certificate data :=
  certificate.energy.toPositivity

/-- Forget the explicit paired boundary only after deriving the public
bilinear-relations interface. -/
def toBilinearRelations {genus : Nat}
    {curve : HyperellipticCurve genus} {data : NormalizedPeriodData curve}
    (certificate : Certificate data) : BilinearRelationsCertificate data where
  numeratorSymmetry := certificate.stokes.numeratorSymmetry
  positivity := certificate.positivity.toPointwisePositivity

/-- Operational symmetry exposed directly from finite Stokes cancellation. -/
def symmetry {genus : Nat}
    {curve : HyperellipticCurve genus} {data : NormalizedPeriodData curve}
    (certificate : Certificate data) :
    NormalizedPeriodData.SymmetryCertificate data :=
  certificate.toBilinearRelations.symmetry

end Certificate

end CCL.Riemann.FiniteBilinear
