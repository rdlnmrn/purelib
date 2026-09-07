import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import FiniteMeasure.Probability
import FiniteMeasure.BoundSquare
import FiniteMeasure.Empirical
import FiniteMeasure.EmpiricalLp
import FiniteMeasure.Cover
import FiniteMeasure.Operational
import FiniteMeasure.EnclosureObservation
import FiniteMeasure.EnclosedExpectation
import FiniteMeasure.IntervalEventEnclosure
import FiniteMeasure.ThresholdEnclosure
import FiniteMeasure.Schedule
import FiniteMeasure.Gap
import FiniteMeasure.AlgebraicGap
import FiniteMeasure.Refinement
import FiniteMeasure.Measurement
import FiniteMeasure.IntegrationProcess
import FiniteMeasure.IntervalIntegration
import FiniteMeasure.Stochastic
import FiniteMeasure.DistributionEquivalence
import FiniteMeasure.LpEquivalence
import FiniteMeasure.EssentialMaximumEquivalence
import FiniteMeasure.ContentEquivalence
import FiniteMeasure.Consolidation
import FiniteMeasure.Tail
import FiniteMeasure.TailProcess
import FiniteMeasure.Valuation
import FiniteMeasure.ContentIntegral
import FiniteMeasure.Normalization
import FiniteMeasure.NormalizedOperations
import FiniteMeasure.Family
import FiniteMeasure.InclusionExclusion
import FiniteMeasure.OccurrenceCount
import FiniteMeasure.OccurrenceSecondMoment
import FiniteMeasure.EventChains
import FiniteMeasure.EventAlgebra
import FiniteMeasure.SimpleObservable
import FiniteMeasure.AtomicRepresentation
import FiniteMeasure.AlgebraObservable
import FiniteMeasure.IndependentSimpleObservable
import FiniteMeasure.Density
import FiniteMeasure.RadonNikodym
import FiniteMeasure.ChangeOfMeasure
import FiniteMeasure.AbsoluteContinuity
import FiniteMeasure.AtomicAbsoluteContinuity
import FiniteMeasure.RadonNikodymExistence
import FiniteMeasure.Atomicity
import FiniteMeasure.AbsoluteContinuityModulus
import FiniteMeasure.Conditioning
import FiniteMeasure.ConditioningChange
import FiniteMeasure.EssentialMaximumOperations
import FiniteMeasure.PartitionExpectation
import FiniteMeasure.PartitionRefinement
import FiniteMeasure.Filtration
import FiniteMeasure.MartingaleDifferences
import FiniteMeasure.MartingaleTransform
import FiniteMeasure.MaximalInequality
import FiniteMeasure.ConditionalJensen
import FiniteMeasure.ConditionalCauchySchwarz
import FiniteMeasure.ConditionalCovarianceAlgebra
import FiniteMeasure.TotalCovariance
import FiniteMeasure.TotalMoments
import FiniteMeasure.ConditionalMoments
import FiniteMeasure.ConditionalEssentialBound
import FiniteMeasure.ConditionalProjection
import FiniteMeasure.ConditionalExpectationCharacterization
import FiniteMeasure.ZeroWeight
import FiniteMeasure.AlmostEverywhere
import FiniteMeasure.Stability
import FiniteMeasure.Coupling
import FiniteMeasure.LawCoupling
import FiniteMeasure.L1
import FiniteMeasure.PoweredLp
import FiniteMeasure.NaturalLp
import FiniteMeasure.PureLp
import FiniteMeasure.L2Geometry
import FiniteMeasure.LpGeometry
import FiniteMeasure.LpAlmostEverywhere
import FiniteMeasure.RestrictedLp
import FiniteMeasure.EssentialBound
import FiniteMeasure.EssentialMaximum
import FiniteMeasure.PushforwardLp
import FiniteMeasure.ProductLp
import FiniteMeasure.ProductEssentialMaximum
import FiniteMeasure.LpComparison
import FiniteMeasure.FiniteConvergence
import FiniteMeasure.ConvergenceModes
import FiniteMeasure.FiniteUniformity
import FiniteMeasure.UniformIntegrability
import FiniteMeasure.Vitali
import FiniteMeasure.VitaliL2
import FiniteMeasure.SignedContent
import FiniteMeasure.Singularity
import FiniteMeasure.JordanDecomposition
import FiniteMeasure.LebesgueDecomposition
import FiniteMeasure.LebesgueDecompositionUniqueness
import FiniteMeasure.TotalVariationDistance
import FiniteMeasure.MaximalCoupling
import FiniteMeasure.ProductTotalVariation
import FiniteMeasure.ProductCoupling
import FiniteMeasure.Scheffe
import FiniteMeasure.Cumulative
import FiniteMeasure.CumulativeStability
import FiniteMeasure.FiniteKolmogorov
import FiniteMeasure.Quantile
import FiniteMeasure.QuantileLawStability
import FiniteMeasure.Median
import FiniteMeasure.LayerCake
import FiniteMeasure.Moments
import FiniteMeasure.Correlation
import FiniteMeasure.CovarianceAlgebra
import FiniteMeasure.LinearRegression
import FiniteMeasure.VarianceLp
import FiniteMeasure.VarianceStability
import FiniteMeasure.OneSidedMoments
import FiniteMeasure.Jensen
import FiniteMeasure.Mixture
import FiniteMeasure.MixtureLp
import FiniteMeasure.MixtureEssentialMaximum
import FiniteMeasure.KernelMoments
import FiniteMeasure.KernelLp
import FiniteMeasure.IndependentMoments
import FiniteMeasure.Independence
import FiniteMeasure.ConditionalIndependence
import FiniteMeasure.Convolution
import FiniteMeasure.Sampling
import FiniteMeasure.SamplingFamily
import FiniteMeasure.EmpiricalQuantile
import RFAP.Measure.BoxContent
import RFAP.Measure.BoxDistribution
import RFAP.Measure.BoxIntegration
import CCL.Measure.BoxedNames
import CCL.Measure.Cylinder
import CCL.Measure.CylinderConcentration
import CCL.Measure.PrefixWeight
import CCL.Measure.FiniteDepth
import CCL.Measure.FiniteDepthTruncation
import CCL.Measure.PrefixAlgebra
import CCL.Measure.PrefixProfile
import CCL.Measure.ProjectivePrefixProfile
import CCL.Measure.EncodedPrefix
import CCL.Measure.PrefixThreshold
import CCL.Measure.PrefixInterval
import CCL.Measure.PrefixQuantile
import CCL.Measure.PrefixCumulative
import CCL.Measure.PrefixProcess
import CCL.Measure.PrefixThresholdProcess
import CCL.Measure.PrefixLp
import CCL.Measure.PrefixStability
import CCL.Measure.PrefixSquaredStability
import CCL.Measure.ChordalProbe
import CCL.Measure.PrefixTransport
import CCL.Measure.EncodedTransport
import CCL.Measure.EncodedSquaredStability
import CCL.Measure.EncodedVarianceStability
import CCL.Measure.SquaredCylinderConcentration
import CCL.Measure.SquaredPrefixThreshold
import CCL.Measure.SquaredPrefixQuantile
import CCL.Measure.EncodedSampling
import CCL.Measure.EncodedEstimator
import CCL.Measure.EncodedThresholdSampling
import CCL.Measure.EncodedThresholdFamilySampling
import CCL.Measure.EncodedEmpiricalQuantile
import CCL.Measure.PrefixDeviation
import CCL.Measure.PrefixVariance
import CCL.Measure.PrefixCenteredVariance
import CCL.Measure.PrefixCenteredVarianceProcess
import CCL.Measure.PrefixCovariance
import CCL.Measure.PrefixCovarianceProcess
import CCL.Measure.PrefixTail
import CCL.Measure.PrefixEssentialMaximum
import CCL.Measure.PrefixEssentialMaximumProcess

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace FiniteMeasure.Examples

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Box := RFAP.Boxes.Box

def exactOneProcess : BoundProcess :=
  BoundProcess.exact 1

def unitInterval : Bound :=
  ⟨0, 1, by decide⟩

def unitIntervalRange : IntervalIntegrationCell where
  interval := unitInterval
  lower := 2
  upper := 5
  range_valid := by decide

example : Bound.Refines
    (integralBound
      (intervalCutSameRangeSplit unitIntervalRange (1 / 2) (by decide)).children)
    (integralBound [unitIntervalRange.toIntegrationCell]) :=
  intervalCutSameRange_integralBound_refines
    unitIntervalRange (1 / 2) (by decide)

example : ((exactOneProcess.add exactOneProcess).bound ((), ())).lower = 2 ∧
    ((exactOneProcess.add exactOneProcess).bound ((), ())).upper = 2 := by
  decide

example : ((exactOneProcess.scalePositive 3 (by decide)).bound ()).lower = 3 ∧
    ((exactOneProcess.scalePositive 3 (by decide)).bound ()).upper = 3 := by
  decide

example : ((exactOneProcess.sub exactOneProcess).bound ((), ())).lower = 0 ∧
    ((exactOneProcess.sub exactOneProcess).bound ((), ())).upper = 0 := by
  decide

example (epsilon : Coordinate) (positive : 0 < epsilon)
    {left right : Coordinate}
    (leftInside :
      (exactOneProcess.bound
        (exactOneProcess.request () epsilon positive)).Contains left)
    (rightInside :
      (exactOneProcess.bound
        (exactOneProcess.request () epsilon positive)).Contains right) :
    rationalSeparation left right < epsilon :=
  exactOneProcess.request_rationalSeparation_lt () epsilon positive
    leftInside rightInside

def halfRequest : AccuracyRequest := ⟨1 / 2, by decide⟩

def eighthRequest : AccuracyRequest := ⟨1 / 8, by decide⟩

def twoAccuracyRequests : List AccuracyRequest :=
  [halfRequest, eighthRequest]

example :
    (exactOneProcess.bound
      (exactOneProcess.runRequests () twoAccuracyRequests)).width < 1 / 2 := by
  apply exactOneProcess.runRequests_width_lt_of_mem () twoAccuracyRequests
    halfRequest
  exact List.mem_cons_self

example :
    (exactOneProcess.bound
      (exactOneProcess.runRequests () twoAccuracyRequests)).width < 1 / 8 := by
  apply exactOneProcess.runRequests_width_lt_of_mem () twoAccuracyRequests
    eighthRequest
  exact List.mem_cons_of_mem halfRequest List.mem_cons_self

example : OperationallyEquivalent exactOneProcess exactOneProcess :=
  operationallyEquivalent_refl exactOneProcess

example : OperationallyEquivalent exactOneProcess exactOneProcess := by
  apply operationallyEquivalent_trans
    (operationallyEquivalent_refl exactOneProcess)
    (operationallyEquivalent_refl exactOneProcess)
  exact BoundProcess.exact_coherent 1

example (gap : RationalGapProcess) (state : gap.process.State)
    (candidates : List Coordinate) (requests : List AccuracyRequest)
    (candidate : Coordinate) (candidateMember : candidate ∈ candidates)
    (request : AccuracyRequest) (requestMember : request ∈ requests) :
    (gap.process.bound (gap.inspect state candidates requests)).Excludes candidate ∧
      (gap.process.bound (gap.inspect state candidates requests)).width <
        request.tolerance :=
  ⟨gap.inspect_excludes_of_mem state candidates requests candidate
      candidateMember,
    gap.inspect_width_lt_of_mem state candidates requests request
      requestMember⟩

example (epsilon : Coordinate) (positive : 0 < epsilon) :
    (SqrtThree.process.bound
      (SqrtThree.process.request SqrtThree.process.initial epsilon positive)).width <
        epsilon :=
  SqrtThree.process.accurate SqrtThree.process.initial epsilon positive

example (state : SqrtThree.State) (candidate : Coordinate) :
    SqrtThree.process.bound state ≠ Bound.exact candidate :=
  SqrtThree.state_bound_ne_exact state candidate

example (candidate : Coordinate) :
    (SqrtThree.process.bound
      (SqrtThree.gapProcess.separate SqrtThree.process.initial candidate)).Excludes
        candidate :=
  SqrtThree.gapProcess.separate_excludes SqrtThree.process.initial candidate

def zeroObservation : Observation Coordinate (fun left right =>
    (left - right) ^ 2) where
  Possible value := value = 0
  witness := 0
  witness_possible := rfl
  spread := 0
  spread_nonnegative := le_rfl
  pairwise := by
    intro left right leftZero rightZero
    subst left
    subst right
    exact le_rfl

example : (zeroObservation.map
    (targetDistance := fun left right => (left - right) ^ 2)
    (fun value => value + 1) 1 (by decide)
    (by
      intro left right
      rw [show (left + 1 - (right + 1)) ^ 2 = (left - right) ^ 2 by ring1,
        one_mul])).Possible 1 :=
  ⟨0, rfl, by ring1⟩

/-! ## Exact finite probability -/

def observedRolls : List Nat := [1, 2, 2, 4]

def observedEven (value : Nat) : Bool := value % 2 == 0

example : (countingContent observedRolls).total = 4 := by
  decide

example : (countingContent observedRolls).measure observedEven = 3 := by
  decide

def doubleDensity (_ : Nat) : Coordinate := 2

theorem doubleDensity_nonnegative (item : Nat) :
    0 ≤ doubleDensity item := by
  unfold doubleDensity
  decide

def halfDensity (_ : Nat) : Coordinate := 1 / 2

theorem halfDensity_nonnegative (item : Nat) :
    0 ≤ halfDensity item := by
  unfold halfDensity
  decide

example :
    (((countingContent observedRolls).reweight doubleDensity
        doubleDensity_nonnegative).reweight halfDensity
          halfDensity_nonnegative).measure observedEven =
      ((countingContent observedRolls).reweight
        (fun item => doubleDensity item * halfDensity item)
        (fun item => RFAP.ConstructiveFraction.mul_nonneg_direct
          (doubleDensity_nonnegative item)
          (halfDensity_nonnegative item))).measure observedEven :=
  (countingContent observedRolls).reweight_reweight_measure
    doubleDensity halfDensity doubleDensity_nonnegative
      halfDensity_nonnegative observedEven

example :
    (((countingContent observedRolls).reweight doubleDensity
        doubleDensity_nonnegative).reweight halfDensity
          halfDensity_nonnegative).measure observedEven = 3 := by
  decide

def observedDistribution : Distribution Nat :=
  empiricalDistribution observedRolls (by decide)

def earlyRolls : List Nat := [1, 2]

def lateRolls : List Nat := [2, 4]

example : Distribution.EvaluationEquivalent observedDistribution
    ((empiricalDistribution earlyRolls (by decide)).mixture
      (empiricalDistribution lateRolls (by decide))
      (FiniteContent.appendMixingWeight
        (countingContent earlyRolls) (countingContent lateRolls)
        (by decide))) := by
  unfold observedDistribution observedRolls earlyRolls lateRolls
  exact empiricalDistribution_append_evaluationEquivalent
    [1, 2] [2, 4] (by decide) (by decide)

def consolidatedObservedDistribution : Distribution Nat :=
  observedDistribution.consolidate

def observedHistogram : Distribution Nat :=
  empiricalHistogram observedRolls (by decide)

example : observedHistogram.poweredL2
    (fun value : Nat => (value : Coordinate)) = 25 / 4 := by
  calc
    observedHistogram.poweredL2
        (fun value : Nat => (value : Coordinate)) =
      observedDistribution.poweredL2
        (fun value : Nat => (value : Coordinate)) :=
      Distribution.EvaluationEquivalent.poweredL2_eq
        (empiricalHistogram_evaluationEquivalent observedRolls (by decide))
        (fun value : Nat => (value : Coordinate))
    _ = 25 / 4 := by decide

example : observedHistogram.essentialMaximumMagnitude
    (fun value : Nat => (value : Coordinate)) = 4 := by
  unfold observedHistogram observedRolls
  rw [empiricalHistogram_essentialMaximumMagnitude]
  decide

example : consolidatedObservedDistribution.atoms.length = 3 := by
  decide

example : observedHistogram.atoms.length = 3 := by
  decide

example : NoRepeatedPayloads observedHistogram.atoms := by
  unfold observedHistogram
  exact empiricalHistogram_noRepeatedPayloads observedRolls (by decide)

example : observedDistribution.atomMass 2 = 1 / 2 := by
  decide

example : countItem observedRolls 2 = 2 := by
  decide

example (item : Nat) :
    SampleContains item observedRolls ∨ SampleAbsent item observedRolls :=
  sampleContains_or_sampleAbsent item observedRolls

example : 0 < observedDistribution.atomMass 2 := by
  unfold observedDistribution
  apply empiricalDistribution_atomMass_pos_of_sampleContains
  simp [observedRolls, SampleContains]

example : observedHistogram.atomMass 2 = 1 / 2 := by
  unfold observedHistogram
  rw [empiricalHistogram_atomMass_eq_countItem]
  decide

example : observedDistribution.atomMass 3 = 0 := by
  unfold observedDistribution
  exact empiricalDistribution_atomMass_eq_zero_of_sampleAbsent
    observedRolls (by decide) 3 (by
      simp [observedRolls, SampleAbsent])

example : consolidatedObservedDistribution.atomMass 2 = 1 / 2 := by
  decide

example : Distribution.EvaluationEquivalent
    consolidatedObservedDistribution observedDistribution := by
  unfold consolidatedObservedDistribution
  exact observedDistribution.consolidate_evaluationEquivalent

example : consolidatedObservedDistribution.variance
      (fun value : Nat => (value : Coordinate)) =
    observedDistribution.variance
      (fun value : Nat => (value : Coordinate)) :=
  observedDistribution.consolidate_evaluationEquivalent.variance_eq
    (fun value : Nat => (value : Coordinate))

example : observedDistribution.probability observedEven = 3 / 4 := by
  decide

example : observedDistribution.probability observedEven =
    Distribution.eventFrequency observedRolls.length observedEven
      observedRolls := by
  unfold observedDistribution
  exact empiricalDistribution_probability_eq_eventFrequency observedRolls
    (by decide) observedEven

example : observedDistribution.expectation
    (fun value => (value : Coordinate)) = 9 / 4 := by
  decide

example : observedDistribution.poweredL2
    (fun value : Nat => (value : Coordinate)) = 25 / 4 := by
  unfold observedDistribution observedRolls
  rw [empiricalDistribution_poweredL2]
  decide

example : observedDistribution.essentialMaximumMagnitude
    (fun value : Nat => (value : Coordinate)) = 4 := by
  unfold observedDistribution observedRolls
  rw [empiricalDistribution_essentialMaximumMagnitude]
  decide

example : observedDistribution.essentialMaximumDistance
    (fun value : Nat => (value : Coordinate)) (fun _ => 2) = 2 := by
  unfold observedDistribution observedRolls
  rw [empiricalDistribution_essentialMaximumDistance]
  decide

example : observedDistribution.expectation
      (fun value : Nat => (value : Coordinate)) =
    Distribution.sampleMean observedRolls.length
      (fun value : Nat => (value : Coordinate)) observedRolls :=
  empiricalDistribution_expectation_eq_sampleMean observedRolls
    (by decide) (fun value : Nat => (value : Coordinate))

example : Distribution.EvaluationEquivalent
    (observedDistribution.map observedEven)
    (empiricalDistribution (observedRolls.map observedEven) (by decide)) := by
  unfold observedDistribution
  exact empiricalDistribution_map_evaluationEquivalent
    observedRolls (by decide) observedEven

example : observedDistribution.variance
      (fun value : Nat => (value : Coordinate)) =
    Distribution.sampleMean observedRolls.length
      (fun value : Nat =>
        ((value : Coordinate) - 9 / 4) ^ 2) observedRolls := by
  unfold observedDistribution
  rw [empiricalDistribution_variance_eq_sampleMean]
  decide

example : observedDistribution.variance
    (fun value : Nat => (value : Coordinate)) = 19 / 16 := by
  decide

example : observedDistribution.variance
      (fun value : Nat => (value : Coordinate)) =
    let weight := empiricalAppendWeight earlyRolls lateRolls
      (by decide) (by decide)
    weight.coefficient *
        (empiricalDistribution earlyRolls (by decide)).variance
          (fun value : Nat => (value : Coordinate)) +
      weight.complement *
        (empiricalDistribution lateRolls (by decide)).variance
          (fun value : Nat => (value : Coordinate)) +
      weight.coefficient * weight.complement *
        ((empiricalDistribution earlyRolls (by decide)).expectation
            (fun value : Nat => (value : Coordinate)) -
          (empiricalDistribution lateRolls (by decide)).expectation
            (fun value : Nat => (value : Coordinate))) ^ 2 := by
  unfold observedDistribution observedRolls earlyRolls lateRolls
  exact empiricalDistribution_append_variance
    [1, 2] [2, 4] (by decide) (by decide)
      (fun value : Nat => (value : Coordinate))

def normalizedObservedContent : Distribution Nat :=
  (countingContent observedRolls).normalize (by decide)

example : Distribution.EvaluationEquivalent observedDistribution
    normalizedObservedContent := by
  unfold observedDistribution normalizedObservedContent
  exact empiricalDistribution_evaluationEquivalent_normalizedCounting
    observedRolls (by decide) (by decide)

example : Distribution.EvaluationEquivalent
    (((countingContent observedRolls).map observedEven).normalize (by decide))
    (normalizedObservedContent.map observedEven) := by
  unfold normalizedObservedContent
  exact (countingContent observedRolls).map_normalize_evaluationEquivalent
    (by decide) observedEven

example : Distribution.EvaluationEquivalent
    (((countingContent observedRolls).restrict observedEven).normalize
      (by decide))
    (normalizedObservedContent.conditioned observedEven (by decide)) := by
  unfold normalizedObservedContent
  exact FiniteContent.restrict_normalize_evaluationEquivalent
    (countingContent observedRolls) (by decide) observedEven (by decide)

example : Distribution.EvaluationEquivalent
    (((countingContent observedRolls).product
      (countingContent observedRolls)).normalize (by decide))
    (normalizedObservedContent.product normalizedObservedContent) := by
  unfold normalizedObservedContent
  exact FiniteContent.product_normalize_evaluationEquivalent
    (countingContent observedRolls) (countingContent observedRolls)
      (by decide) (by decide)

example :
    (FiniteContent.appendMixingWeight
      (countingContent observedRolls) (countingContent observedRolls)
      (by decide)).coefficient = 1 / 2 := by
  decide

example : Distribution.EvaluationEquivalent
    (((countingContent observedRolls).append
      (countingContent observedRolls)).normalize (by decide))
    (normalizedObservedContent.mixture normalizedObservedContent
      (FiniteContent.appendMixingWeight
        (countingContent observedRolls) (countingContent observedRolls)
        (by decide))) := by
  unfold normalizedObservedContent
  exact FiniteContent.append_normalize_evaluationEquivalent
    (countingContent observedRolls) (countingContent observedRolls)
      (by decide) (by decide)

example : normalizedObservedContent.probability observedEven = 3 / 4 := by
  decide

example : normalizedObservedContent.expectation
    (fun value => (value : Coordinate)) =
      (countingContent observedRolls).integral
          (fun value => (value : Coordinate)) /
        (countingContent observedRolls).total :=
  (countingContent observedRolls).normalize_expectation (by decide)
    (fun value => (value : Coordinate))

def fairCoin : Distribution Bool where
  atoms :=
    [⟨false, 1 / 2, by decide⟩,
      ⟨true, 1 / 2, by decide⟩]
  total_one := by decide

def coinNumber (outcome : Bool) : Coordinate :=
  if outcome then 1 else 0

def coinNumberLaw : Distribution Coordinate :=
  fairCoin.map coinNumber

example : coinNumberLaw.poweredLp 2 (fun value => value) =
    fairCoin.poweredLp 2 coinNumber := by
  unfold coinNumberLaw
  exact fairCoin.map_poweredLp coinNumber 2 (fun value => value)

example : coinNumberLaw.l1Distance (fun value => value) (fun _ => 0) =
    fairCoin.l1Distance coinNumber (fun _ => 0) := by
  unfold coinNumberLaw
  exact fairCoin.map_l1Distance coinNumber (fun value => value) (fun _ => 0)

example : coinNumberLaw.essentialMaximumMagnitude (fun value => value) =
    fairCoin.essentialMaximumMagnitude coinNumber := by
  unfold coinNumberLaw
  exact fairCoin.map_essentialMaximumMagnitude coinNumber (fun value => value)

example : coinNumberLaw.poweredLp 2 (fun value => value) = 1 / 2 ∧
    coinNumberLaw.essentialMaximumMagnitude (fun value => value) = 1 := by
  decide

example (left right : Coordinate → Coordinate) :
    coinNumberLaw.EqualAlmostEverywhere left right ↔
      fairCoin.EqualAlmostEverywhere
        (fun outcome => left (coinNumber outcome))
        (fun outcome => right (coinNumber outcome)) := by
  unfold coinNumberLaw
  exact fairCoin.map_equalAlmostEverywhere_iff coinNumber left right

theorem coinIncreasingEventChain : IncreasingEventChainOn fairCoin.atoms
    [fun _ => false, fun outcome => outcome, fun _ => true] := by
  constructor
  · intro atom member selected
    exact Bool.noConfusion selected
  · constructor
    · intro atom member selected
      rfl
    · trivial

example : fairCoin.probability
      (unionEvents [fun _ => false, fun outcome => outcome, fun _ => true]) =
    fairCoin.probability (fun _ => true) :=
  fairCoin.probability_unionEvents_eq_last_of_increasing
    (fun _ => false) [fun outcome => outcome, fun _ => true]
    coinIncreasingEventChain

theorem coinDecreasingEventChain : DecreasingEventChainOn fairCoin.atoms
    [fun _ => true, fun outcome => outcome, fun _ => false] := by
  constructor
  · intro atom member selected
    rfl
  · constructor
    · intro atom member selected
      exact Bool.noConfusion selected
    · trivial

example : fairCoin.probability
      (intersectionEvents (fun _ => true)
        [fun outcome => outcome, fun _ => false]) =
    fairCoin.probability (fun _ => false) :=
  fairCoin.probability_intersectionEvents_eq_last_of_decreasing
    (fun _ => true) [fun outcome => outcome, fun _ => false]
    coinDecreasingEventChain

def repeatedHeadsEvents : List (Bool → Bool) :=
  [fun outcome => outcome, fun outcome => outcome, fun outcome => outcome]

example : (inclusionExclusionTerms repeatedHeadsEvents).length = 7 := by
  rw [inclusionExclusionTerms_length]
  decide

example : inclusionExclusionValue fairCoin.toFiniteContent
      repeatedHeadsEvents =
    fairCoin.probability (unionEvents repeatedHeadsEvents) :=
  fairCoin.inclusionExclusionValue_eq_probability_unionEvents
    repeatedHeadsEvents

example : inclusionExclusionValue fairCoin.toFiniteContent
    repeatedHeadsEvents = 1 / 2 := by
  decide

example : occurrenceCount repeatedHeadsEvents false = 0 ∧
    occurrenceCount repeatedHeadsEvents true = 3 := by
  decide

example : fairCoin.expectation (fun outcome =>
      (occurrenceCount repeatedHeadsEvents outcome : Coordinate)) = 3 / 2 := by
  rw [fairCoin.expectation_occurrenceCount repeatedHeadsEvents]
  decide

example : fairCoin.probability
    (atLeastOccurrences 2 repeatedHeadsEvents) = 1 / 2 := by
  decide

example : fairCoin.probability
      (atLeastOccurrences 2 repeatedHeadsEvents) ≤ 3 / 4 := by
  have bound := fairCoin.probability_atLeastOccurrences_le_sum_div
    repeatedHeadsEvents 2 (by omega)
  have evaluated :
      (repeatedHeadsEvents.map fairCoin.probability).sum /
        ((2 : Nat) : Coordinate) = 3 / 4 := by
    decide
  rw [evaluated] at bound
  exact bound

example (outcome : Bool) :
    atLeastOccurrences 1 repeatedHeadsEvents outcome =
      unionEvents repeatedHeadsEvents outcome :=
  atLeastOccurrences_one_eq_unionEvents repeatedHeadsEvents outcome

example : fairCoin.pairIntersectionProbabilitySum repeatedHeadsEvents =
    3 / 2 := by
  decide

example : fairCoin.expectation (fun outcome =>
      (occurrenceCount repeatedHeadsEvents outcome : Coordinate) ^ 2) =
    9 / 2 := by
  rw [fairCoin.expectation_occurrenceCount_sq repeatedHeadsEvents]
  decide

example :
    (repeatedHeadsEvents.map fairCoin.probability).sum ^ 2 /
        ((repeatedHeadsEvents.map fairCoin.probability).sum +
          2 * fairCoin.pairIntersectionProbabilitySum repeatedHeadsEvents) ≤
      fairCoin.probability (unionEvents repeatedHeadsEvents) :=
  fairCoin.secondMoment_union_lower_bound repeatedHeadsEvents (by decide)

example :
    (repeatedHeadsEvents.map fairCoin.probability).sum ^ 2 /
          ((repeatedHeadsEvents.map fairCoin.probability).sum +
            2 * fairCoin.pairIntersectionProbabilitySum repeatedHeadsEvents) =
        1 / 2 ∧
      fairCoin.probability (unionEvents repeatedHeadsEvents) = 1 / 2 := by
  decide

def headsEventCode : boolEventAlgebra.Code :=
  (false, true)

def tailsEventCode : boolEventAlgebra.Code :=
  (true, false)

example : boolEventAlgebra.signature false =
    [false, false, true, true] := by
  decide

example : boolEventAlgebra.signature true =
    [false, true, false, true] := by
  decide

example : boolEventAlgebra.measure fairCoin.toFiniteContent headsEventCode =
    1 / 2 := by
  decide

example : fairCoin.probability (boolEventAlgebra.evaluate headsEventCode) =
    (boolEventAlgebra.signatureDistribution fairCoin).probability
      (boolEventAlgebra.signatureEvent headsEventCode) :=
  boolEventAlgebra.probability_eq_signatureDistribution_probability
    fairCoin headsEventCode

example : (boolEventAlgebra.atomDistribution fairCoin).atoms.length = 2 := by
  decide

example : fairCoin.probability (boolEventAlgebra.evaluate headsEventCode) =
    (boolEventAlgebra.atomDistribution fairCoin).probability
      (boolEventAlgebra.signatureEvent headsEventCode) :=
  boolEventAlgebra.probability_eq_atomDistribution_probability
    fairCoin headsEventCode

example :
    (boolEventAlgebra.atomContent fairCoin.toFiniteContent).atoms.length = 2 := by
  decide

example : boolEventAlgebra.measure fairCoin.toFiniteContent headsEventCode =
    (boolEventAlgebra.atomContent fairCoin.toFiniteContent).measure
      (boolEventAlgebra.signatureEvent headsEventCode) :=
  boolEventAlgebra.measure_eq_atomContent_measure fairCoin.toFiniteContent
    headsEventCode

example : boolEventAlgebra.measure fairCoin.toFiniteContent headsEventCode +
      boolEventAlgebra.measure fairCoin.toFiniteContent tailsEventCode =
    boolEventAlgebra.measure fairCoin.toFiniteContent
        (boolEventAlgebra.union headsEventCode tailsEventCode) +
      boolEventAlgebra.measure fairCoin.toFiniteContent
        (boolEventAlgebra.intersection headsEventCode tailsEventCode) :=
  boolEventAlgebra.measure_valuation fairCoin.toFiniteContent
    headsEventCode tailsEventCode

def coinSimpleObservable : SimpleObservable boolEventAlgebra :=
  [⟨tailsEventCode, 1⟩, ⟨headsEventCode, 3⟩]

example : coinSimpleObservable.evaluate false = 1 ∧
    coinSimpleObservable.evaluate true = 3 := by
  decide

example : coinSimpleObservable.expectation fairCoin = 2 := by
  decide

example : (coinSimpleObservable.scale 3).expectation fairCoin = 6 := by
  decide

example : (coinSimpleObservable.sub coinSimpleObservable).expectation
    fairCoin = 0 := by
  decide

example : (coinSimpleObservable.mul coinSimpleObservable).expectation
    fairCoin = 5 := by
  decide

example : coinSimpleObservable.expectation fairCoin =
    (coinSimpleObservable.map fun term =>
      fairCoin.probability (boolEventAlgebra.evaluate term.event) *
        term.coefficient).sum :=
  coinSimpleObservable.expectation_eq_sum fairCoin

example : coinSimpleObservable.expectation fairCoin =
    (boolEventAlgebra.signatureDistribution fairCoin).expectation
      coinSimpleObservable.signatureValue :=
  coinSimpleObservable.expectation_eq_signatureDistribution_expectation
    fairCoin

example : coinSimpleObservable.expectation fairCoin =
    (boolEventAlgebra.atomDistribution fairCoin).expectation
      coinSimpleObservable.signatureValue :=
  coinSimpleObservable.expectation_eq_atomDistribution_expectation fairCoin

def coinAlgebraObservable : AlgebraObservable boolEventAlgebra :=
  AlgebraObservable.ofSimple coinSimpleObservable

example : fairCoin.toFiniteContent.integral coinAlgebraObservable.evaluate =
    (boolEventAlgebra.atomContent fairCoin.toFiniteContent).integral
      coinAlgebraObservable.signatureValue :=
  coinAlgebraObservable.integral_eq_atomContent_integral
    fairCoin.toFiniteContent

example : coinAlgebraObservable.evaluate false = 1 ∧
    coinAlgebraObservable.evaluate true = 3 := by
  decide

example : fairCoin.toFiniteContent.integral coinSimpleObservable.evaluate =
    (boolEventAlgebra.atomContent fairCoin.toFiniteContent).integral
      coinSimpleObservable.signatureValue :=
  boolEventAlgebra.simpleObservable_integral_eq_atomContent_integral
    fairCoin.toFiniteContent coinSimpleObservable

def partialCoinStatus (outcome : Bool) : Status :=
  if outcome then .unresolved else .outside

theorem partialCoinStatus_sound :
    ClassificationSoundOn fairCoin.atoms partialCoinStatus
      (fun outcome => outcome) := by
  intro atom member
  cases atom.item <;> trivial

example : eventBound (fairCoin.classifiedEventFrontier partialCoinStatus) =
    ⟨0, 1 / 2, by decide⟩ := by
  apply Bound.ext <;> decide

example : (eventBound
      (fairCoin.classifiedEventFrontier partialCoinStatus)).width =
    fairCoin.probability (unresolvedStatusEvent partialCoinStatus) :=
  fairCoin.classifiedEventFrontier_width partialCoinStatus

example : (eventBound
      (fairCoin.classifiedEventFrontier partialCoinStatus)).Contains
    (fairCoin.probability fun outcome => outcome) :=
  fairCoin.probability_mem_classifiedEventFrontier partialCoinStatus
    (fun outcome => outcome) partialCoinStatus_sound

/-- The exact finite status table for the Boolean event itself. -/
def exactCoinStatus (outcome : Bool) : Status :=
  if outcome then .inside else .outside

/-- A two-state classifier: its initial state leaves heads unresolved, while
one finite request produces the exact status table. -/
def coinClassificationStatus (refined outcome : Bool) : Status :=
  if refined then exactCoinStatus outcome else partialCoinStatus outcome

def coinClassificationProcess :
    ClassificationProcess fairCoin (fun outcome => outcome) where
  State := Bool
  status := coinClassificationStatus
  initial := false
  request state epsilon positive := true
  sound state := by
    intro atom member
    cases state <;> cases atom.item <;>
      simp [coinClassificationStatus, exactCoinStatus, partialCoinStatus,
        Status.AdmitsSelection]
  request_refines state epsilon positive atom member := by
    cases state <;> cases atom.item <;>
      simp [coinClassificationStatus, exactCoinStatus, partialCoinStatus,
        Status.Refines]
  accurate state epsilon positive := by
    simpa [Distribution.probability, fairCoin, coinClassificationStatus,
      exactCoinStatus, unresolvedStatusEvent, eventWeight] using positive
  refinesInitial state atom member := by
    cases state <;> cases atom.item <;>
      simp [coinClassificationStatus, exactCoinStatus, partialCoinStatus,
        Status.Refines]

example : coinClassificationProcess.toBoundProcess.bound
      coinClassificationProcess.initial =
    ⟨0, 1 / 2, by decide⟩ := by
  apply Bound.ext <;> decide

example : coinClassificationProcess.toBoundProcess.bound
      (coinClassificationProcess.request
        coinClassificationProcess.initial 1 (by decide)) =
    Bound.exact (1 / 2) := by
  apply Bound.ext <;> decide

example (state : coinClassificationProcess.State) :
    (coinClassificationProcess.toBoundProcess.bound state).Contains
      (fairCoin.probability fun outcome => outcome) :=
  coinClassificationProcess.probability_mem_bound state

example (state : coinClassificationProcess.State)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    fairCoin.probability (fun outcome => outcome) -
          coinClassificationProcess.toBoundProcess.approximate
            state epsilon positive < epsilon ∧
      coinClassificationProcess.toBoundProcess.approximate
            state epsilon positive -
          fairCoin.probability (fun outcome => outcome) < epsilon :=
  coinClassificationProcess.probability_close_to_approximation
    state epsilon positive

example : coinClassificationProcess.toBoundProcess.approximate
    coinClassificationProcess.initial 1 (by decide) = 1 / 2 := by
  decide

example : fairCoin.probability
      (unresolvedStatusEvent
        (coinClassificationProcess.status
          (coinClassificationProcess.runRequests
            coinClassificationProcess.initial twoAccuracyRequests))) <
    eighthRequest.tolerance := by
  apply coinClassificationProcess.runRequests_unresolved_probability_lt_of_mem
    coinClassificationProcess.initial twoAccuracyRequests eighthRequest
  exact List.mem_cons_of_mem halfRequest List.mem_cons_self

example : coinClassificationProcess.runRequestsApproximation
    coinClassificationProcess.initial twoAccuracyRequests = 1 / 2 := by
  decide

example : fairCoin.probability (fun outcome => outcome) -
        coinClassificationProcess.runRequestsApproximation
          coinClassificationProcess.initial twoAccuracyRequests <
      eighthRequest.tolerance ∧
    coinClassificationProcess.runRequestsApproximation
          coinClassificationProcess.initial twoAccuracyRequests -
        fairCoin.probability (fun outcome => outcome) <
      eighthRequest.tolerance := by
  apply coinClassificationProcess
    |>.runRequests_probability_close_to_approximation_of_mem
      coinClassificationProcess.initial twoAccuracyRequests eighthRequest
  exact List.mem_cons_of_mem halfRequest List.mem_cons_self

/-- Deliberately coarse rational information about the two coin outcomes. -/
def coarseCoinRange : Bool → Bound
  | false => ⟨0, 1 / 2, by decide⟩
  | true => ⟨1 / 2, 1, by decide⟩

def exactCoinRange (outcome : Bool) : Bound :=
  Bound.exact (coinNumber outcome)

example : fairCoin.enclosedExpectation coarseCoinRange =
    ⟨1 / 4, 3 / 4, by decide⟩ := by
  apply Bound.ext <;> decide

example : (fairCoin.enclosedExpectation coarseCoinRange).width = 1 / 2 := by
  decide

example : (fairCoin.enclosedExpectation coarseCoinRange).Contains
    (fairCoin.expectation coinNumber) := by
  apply fairCoin.expectation_mem_enclosedExpectation
  intro atom member
  cases atom.item <;> decide

example : Bound.Refines
    (fairCoin.enclosedExpectation exactCoinRange)
    (fairCoin.enclosedExpectation coarseCoinRange) := by
  apply fairCoin.enclosedExpectation_refines
  intro atom member
  cases atom.item
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

example : fairCoin.enclosedExpectation exactCoinRange =
    Bound.exact (1 / 2) := by
  unfold exactCoinRange
  rw [fairCoin.enclosedExpectation_exact]
  apply Bound.ext <;> decide

def coinRangeState (refined outcome : Bool) : Bound :=
  if refined then exactCoinRange outcome else coarseCoinRange outcome

/-- A two-state, one-request illustration of lifting finite pointwise
enclosures through expectation. -/
def coinPointwiseProcess : PointwiseEnclosureProcess fairCoin where
  State := Bool
  ranges := coinRangeState
  initial := false
  request state epsilon positive := true
  request_refines state epsilon positive atom member := by
    cases state <;> cases atom.item
    all_goals exact ⟨by decide, by decide⟩
  accurate state epsilon positive atom member := by
    cases atom.item <;> simp [coinRangeState, exactCoinRange,
      coinNumber, Bound.exact_width, positive.le]
  refinesInitial state atom member := by
    cases state <;> cases atom.item
    all_goals exact ⟨by decide, by decide⟩

example : coinPointwiseProcess.toExpectationBoundProcess.bound false =
    fairCoin.enclosedExpectation coarseCoinRange := rfl

example : coinPointwiseProcess.toExpectationBoundProcess.bound
      (coinPointwiseProcess.toExpectationBoundProcess.request
        false 1 (by decide)) = Bound.exact (1 / 2) := by
  change fairCoin.enclosedExpectation exactCoinRange = Bound.exact (1 / 2)
  unfold exactCoinRange
  rw [fairCoin.enclosedExpectation_exact]
  apply Bound.ext <;> decide

example : coinPointwiseProcess.toExpectationBoundProcess.approximate
    false 1 (by decide) = 1 / 2 := by
  decide

example : eventBound
      (fairCoin.thresholdFrontier coarseCoinRange (1 / 2)) =
    ⟨1 / 2, 1, by decide⟩ := by
  apply Bound.ext <;> decide

example : (eventBound
      (fairCoin.thresholdFrontier coarseCoinRange (1 / 2))).Contains
    (fairCoin.probability (atLeastEvent (1 / 2) coinNumber)) := by
  apply fairCoin.probability_mem_thresholdFrontier
  intro atom member
  cases atom.item <;> decide

example : Bound.Refines
    (eventBound (fairCoin.thresholdFrontier exactCoinRange (1 / 2)))
    (eventBound (fairCoin.thresholdFrontier coarseCoinRange (1 / 2))) := by
  apply fairCoin.thresholdFrontier_eventBound_refines
  intro atom member
  cases atom.item
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

example : (eventBound
      (fairCoin.thresholdFrontier exactCoinRange (1 / 2))).width = 0 := by
  apply fairCoin.thresholdFrontier_width_eq_zero_of_resolved
  intro atom member
  cases atom.item
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)

theorem coinRequestResolvesHalfThreshold
    (state : coinPointwiseProcess.State) (epsilon : Coordinate)
    (positive : 0 < epsilon) (atom : Weighted Bool)
    (_member : atom ∈ fairCoin.atoms) :
    ThresholdResolved
      (coinPointwiseProcess.ranges
        (coinPointwiseProcess.request state epsilon positive) atom.item)
      (1 / 2) := by
  change ThresholdResolved (coinRangeState true atom.item) (1 / 2)
  cases atom.item
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)

def coinThresholdProcess : BoundProcess :=
  coinPointwiseProcess.toThresholdBoundProcess (1 / 2)
    coinRequestResolvesHalfThreshold

theorem coinRangesAdmitCoinNumber
    (state : coinPointwiseProcess.State) (atom : Weighted Bool)
    (_member : atom ∈ fairCoin.atoms) :
    (coinPointwiseProcess.ranges state atom.item).Contains
      (coinNumber atom.item) := by
  cases state <;> cases atom.item <;>
    simp [coinPointwiseProcess, coinRangeState, coarseCoinRange,
      exactCoinRange, coinNumber, Bound.Contains] <;> decide

def coinThresholdClassificationProcess :
    ClassificationProcess fairCoin (atLeastEvent (1 / 2) coinNumber) :=
  coinPointwiseProcess.toThresholdClassificationProcess
    (1 / 2) coinNumber coinRangesAdmitCoinNumber
    (by
      intro state epsilon positive
      change fairCoin.probability
        (unresolvedStatusEvent fun outcome =>
          thresholdStatus (coinRangeState true outcome) (1 / 2)) < epsilon
      have zero : fairCoin.probability
          (unresolvedStatusEvent fun outcome =>
            thresholdStatus (coinRangeState true outcome) (1 / 2)) = 0 := by
        decide
      rw [zero]
      exact positive)

example : coinThresholdProcess.bound coinThresholdProcess.initial =
    eventBound (fairCoin.thresholdFrontier coarseCoinRange (1 / 2)) := rfl

example : coinThresholdProcess.bound
      (coinThresholdProcess.request coinThresholdProcess.initial 1
        (by decide)) = Bound.exact (1 / 2) := by
  apply Bound.ext <;> decide

example : coinThresholdProcess.approximate
    coinThresholdProcess.initial 1 (by decide) = 1 / 2 := by
  decide

example : coinThresholdClassificationProcess.toBoundProcess.approximate
    coinThresholdClassificationProcess.initial 1 (by decide) = 1 / 2 := by
  decide

example (state : coinThresholdClassificationProcess.State) :
    (coinThresholdClassificationProcess.toBoundProcess.bound state).Contains
      (fairCoin.probability (atLeastEvent (1 / 2) coinNumber)) :=
  coinThresholdClassificationProcess.probability_mem_bound state

/-! A bounded rational target gives the analogous finite interval event. -/

def headsInterval : Bound :=
  ⟨3 / 4, 5 / 4, by decide⟩

def coinWithinBoundClassificationProcess :
    ClassificationProcess fairCoin
      (withinBoundEvent headsInterval coinNumber) :=
  coinPointwiseProcess.toWithinBoundClassificationProcess
    headsInterval coinNumber coinRangesAdmitCoinNumber
    (by
      intro state epsilon positive
      change fairCoin.probability
        (withinBoundUnresolvedEvent (coinRangeState true) headsInterval) <
          epsilon
      have zero : fairCoin.probability
          (withinBoundUnresolvedEvent (coinRangeState true) headsInterval) =
            0 := by
        decide
      rw [zero]
      exact positive)

example : eventBound
      (fairCoin.withinBoundFrontier coarseCoinRange headsInterval) =
    ⟨0, 1 / 2, by decide⟩ := by
  apply Bound.ext <;> decide

example : (eventBound
      (fairCoin.withinBoundFrontier coarseCoinRange headsInterval)).width =
    fairCoin.probability
      (withinBoundUnresolvedEvent coarseCoinRange headsInterval) :=
  fairCoin.withinBoundFrontier_width coarseCoinRange headsInterval

example : (eventBound
      (fairCoin.withinBoundFrontier coarseCoinRange headsInterval)).Contains
    (fairCoin.probability
      (withinBoundEvent headsInterval coinNumber)) := by
  apply fairCoin.probability_mem_withinBoundFrontier
  intro atom member
  cases atom.item <;> decide

example : Bound.Refines
    (eventBound
      (fairCoin.withinBoundFrontier exactCoinRange headsInterval))
    (eventBound
      (fairCoin.withinBoundFrontier coarseCoinRange headsInterval)) := by
  apply fairCoin.withinBoundFrontier_eventBound_refines
  intro atom member
  cases atom.item
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

example : (eventBound
      (fairCoin.withinBoundFrontier exactCoinRange headsInterval)).width = 0 := by
  apply fairCoin.withinBoundFrontier_width_eq_zero_of_resolved
  intro atom member
  cases atom.item
  · exact Or.inr (Or.inl (by decide))
  · exact Or.inl ⟨by decide, by decide⟩

example : coinWithinBoundClassificationProcess.toBoundProcess.approximate
    coinWithinBoundClassificationProcess.initial 1 (by decide) = 1 / 2 := by
  decide

def reverseCoinNumber (outcome : Bool) : Coordinate :=
  if outcome then 0 else 1

example : fairCoin.poweredL2 coinNumber = 1 / 2 := by
  decide

example : fairCoin.poweredL2 reverseCoinNumber = 1 / 2 := by
  decide

example : fairCoin.poweredL2
        (fun outcome => coinNumber outcome + reverseCoinNumber outcome) +
      fairCoin.poweredL2
        (fun outcome => coinNumber outcome - reverseCoinNumber outcome) =
    2 * (fairCoin.poweredL2 coinNumber +
      fairCoin.poweredL2 reverseCoinNumber) :=
  fairCoin.poweredL2_add_sub coinNumber reverseCoinNumber

example : fairCoin.poweredL2
        (fun outcome => coinNumber outcome + reverseCoinNumber outcome) +
      fairCoin.poweredL2
        (fun outcome => coinNumber outcome - reverseCoinNumber outcome) =
    2 := by
  decide

example : fairCoin.poweredL2Distance coinNumber (fun _ => 0) ≤
    2 * (fairCoin.poweredL2Distance coinNumber reverseCoinNumber +
      fairCoin.poweredL2Distance reverseCoinNumber (fun _ => 0)) :=
  fairCoin.poweredL2Distance_le_two_mul_add
    coinNumber reverseCoinNumber (fun _ => 0)

example : fairCoin.poweredLp 3
      (fun outcome => coinNumber outcome + reverseCoinNumber outcome) ≤
    (2 : Coordinate) ^ 3 *
      (fairCoin.poweredLp 3 coinNumber +
        fairCoin.poweredLp 3 reverseCoinNumber) :=
  fairCoin.poweredLp_add_le_two_pow_mul 3
    coinNumber reverseCoinNumber

example : fairCoin.poweredLpDistance 3 coinNumber (fun _ => 0) ≤
    (2 : Coordinate) ^ 3 *
      (fairCoin.poweredLpDistance 3 coinNumber reverseCoinNumber +
        fairCoin.poweredLpDistance 3 reverseCoinNumber (fun _ => 0)) :=
  fairCoin.poweredLpDistance_le_two_pow_mul 3
    coinNumber reverseCoinNumber (fun _ => 0)

example : fairCoin.poweredLp 0 coinNumber = 1 :=
  fairCoin.poweredLp_zero coinNumber

example : fairCoin.poweredLp 1 coinNumber = fairCoin.poweredL1 coinNumber :=
  fairCoin.poweredLp_one coinNumber

example : fairCoin.poweredLp 2 coinNumber = fairCoin.poweredL2 coinNumber :=
  fairCoin.poweredLp_two coinNumber

example : fairCoin.poweredL2 coinNumber ≤
    fairCoin.essentialMaximumMagnitude coinNumber *
      fairCoin.poweredL1 coinNumber :=
  fairCoin.poweredL2_le_essentialMaximum_mul_poweredL1 coinNumber

example : fairCoin.poweredL1 coinNumber ^ 2 ≤
    fairCoin.poweredL2 coinNumber :=
  fairCoin.poweredL1_sq_le_poweredL2 coinNumber

example : fairCoin.poweredL1 coinNumber ^ 2 = 1 / 4 ∧
    fairCoin.poweredL2 coinNumber = 1 / 2 := by
  decide

example : fairCoin.l1Distance coinNumber reverseCoinNumber ^ 2 ≤
    fairCoin.poweredL2Distance coinNumber reverseCoinNumber :=
  fairCoin.l1Distance_sq_le_poweredL2Distance
    coinNumber reverseCoinNumber

example : fairCoin.poweredL2 coinNumber = 1 / 2 ∧
    fairCoin.essentialMaximumMagnitude coinNumber *
      fairCoin.poweredL1 coinNumber = 1 / 2 := by
  decide

example : fairCoin.poweredL2Distance coinNumber reverseCoinNumber ≤
    fairCoin.essentialMaximumMagnitude
        (fun outcome => coinNumber outcome - reverseCoinNumber outcome) *
      fairCoin.l1Distance coinNumber reverseCoinNumber :=
  fairCoin.poweredL2Distance_le_essentialMaximumDifference_mul_l1Distance
    coinNumber reverseCoinNumber

example : fairCoin.poweredL2Distance coinNumber reverseCoinNumber = 1 ∧
    fairCoin.essentialMaximumMagnitude
        (fun outcome => coinNumber outcome - reverseCoinNumber outcome) *
      fairCoin.l1Distance coinNumber reverseCoinNumber = 1 := by
  decide

def coinL2FamilyBudget : Distribution.L2FamilyBudget fairCoin
    [coinNumber, reverseCoinNumber] where
  ceiling := 1 / 2
  ceiling_nonnegative := by decide
  poweredL2_le value member := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide

example : fairCoin.absoluteTailIntegral 1 coinNumber = 1 / 2 := by
  decide

example (value : Bool → Coordinate)
    (member : value ∈ [coinNumber, reverseCoinNumber]) :
    fairCoin.absoluteTailIntegral 1 value ≤ 1 / 2 := by
  have bound := coinL2FamilyBudget.absoluteTailIntegral_le value member 1
    (by decide)
  change fairCoin.absoluteTailIntegral 1 value ≤ (1 / 2 : Coordinate) / 1
    at bound
  have quotient : (1 / 2 : Coordinate) / 1 = 1 / 2 := by decide
  rw [quotient] at bound
  exact bound

example : fairCoin.poweredLp 2 coinNumber = 1 / 2 := by
  decide

example : fairCoin.poweredLpDistance 3
      (fun outcome => (-2 : Coordinate) * coinNumber outcome)
      (fun outcome => (-2 : Coordinate) * reverseCoinNumber outcome) =
    rationalSeparation (-2) 0 ^ 3 *
      fairCoin.poweredLpDistance 3 coinNumber reverseCoinNumber :=
  fairCoin.poweredLpDistance_scale 3 (-2)
    coinNumber reverseCoinNumber

example : fairCoin.poweredLpDistance 3
      (fun outcome => (-2 : Coordinate) * coinNumber outcome)
      (fun outcome => (-2 : Coordinate) * reverseCoinNumber outcome) = 8 := by
  decide

example : fairCoin.toFiniteContent.poweredLpDistance 2
      coinNumber reverseCoinNumber =
    fairCoin.toFiniteContent.poweredL2Distance
      coinNumber reverseCoinNumber :=
  fairCoin.toFiniteContent.poweredLpDistance_two
    coinNumber reverseCoinNumber

example : fairCoin.probability
      (separationAtLeast 1 coinNumber reverseCoinNumber) ≤
    fairCoin.poweredLpDistance 2 coinNumber reverseCoinNumber / 1 ^ 2 :=
  fairCoin.probability_separationAtLeast_le_poweredLpDistance
    2 1 (by decide) coinNumber reverseCoinNumber

def coinInMeasureBudget : Distribution.InMeasureBudget
    fairCoin coinNumber reverseCoinNumber :=
  Distribution.InMeasureBudget.ofL1 fairCoin coinNumber reverseCoinNumber
    1 (by decide)

def coinHalfInMeasureBudget : Distribution.InMeasureBudget
    fairCoin coinNumber reverseCoinNumber where
  threshold := 1 / 2
  threshold_positive := by decide
  failure := 1
  failure_nonnegative := by decide
  probability_le := by decide

def coinL2InMeasureBudget : Distribution.L2InMeasureBudget
    fairCoin coinNumber reverseCoinNumber where
  inMeasure := coinHalfInMeasureBudget
  ceiling := 1
  ceiling_nonnegative := by decide
  poweredL2Distance_le := by decide

example : coinHalfInMeasureBudget.l1Excess = 1 / 2 := by
  decide

example : coinHalfInMeasureBudget.l1Excess ^ 2 ≤
    coinL2InMeasureBudget.ceiling * coinHalfInMeasureBudget.failure :=
  coinL2InMeasureBudget.l1Excess_sq_le

example : fairCoin.probability
      (separationAtLeast coinInMeasureBudget.threshold
        coinNumber reverseCoinNumber) ≤
    coinInMeasureBudget.failure :=
  coinInMeasureBudget.probability_le

def coinSelfInMeasureBudget : Distribution.InMeasureBudget
    fairCoin coinNumber coinNumber :=
  Distribution.InMeasureBudget.ofEqualAlmostEverywhere fairCoin
    coinNumber coinNumber
    (EqualOffZeroWeightOn.refl fairCoin.atoms coinNumber) 1 (by decide)

example : coinSelfInMeasureBudget.failure = 0 := rfl

def coinUniformOutsideBudget : Distribution.UniformOutsideBudget fairCoin
    [coinNumber, reverseCoinNumber] (fun _ => 1 / 2) :=
  fairCoin.uniformOutsideBudget [coinNumber, reverseCoinNumber]
    (fun _ => 1 / 2) (3 / 4) (by decide)

example : coinUniformOutsideBudget.failure = 0 ∧
    fairCoin.probability coinUniformOutsideBudget.exceptional = 0 := by
  decide

example (approximation : Bool → Coordinate)
    (member : approximation ∈ [coinNumber, reverseCoinNumber])
    (atom : Weighted Bool) (atomMember : atom ∈ fairCoin.atoms) :
    rationalSeparation (approximation atom.item) (1 / 2) < 3 / 4 := by
  apply coinUniformOutsideBudget.outside approximation member atom atomMember
  cases selected : atom.item <;> decide

example : fairCoin.expectation (fun outcome =>
      coinNumber outcome * reverseCoinNumber outcome) ^ 2 ≤
    fairCoin.poweredL2 coinNumber *
      fairCoin.poweredL2 reverseCoinNumber :=
  fairCoin.productExpectation_sq_le_poweredL2_mul
    coinNumber reverseCoinNumber

example : fairCoin.toFiniteContent.poweredL2 (fun outcome =>
      coinNumber outcome + reverseCoinNumber outcome) ≤
    ((3 / 4 : Coordinate) + 3 / 4) ^ 2 := by
  apply fairCoin.toFiniteContent.poweredL2_add_le_radius_add_sq
    coinNumber reverseCoinNumber (3 / 4) (3 / 4)
      (by decide) (by decide) <;> decide

example : fairCoin.toFiniteContent.poweredL1 (fun outcome =>
      coinNumber outcome * reverseCoinNumber outcome) ≤
    1 * fairCoin.toFiniteContent.poweredL1 coinNumber := by
  apply fairCoin.toFiniteContent.poweredL1_mul_le_of_right_bounded
    coinNumber reverseCoinNumber 1 (by decide)
  intro atom member
  cases atom.item <;> decide

example : MonotoneCoordinateChain
    ([fun _ : Bool => (0 : Coordinate), coinNumber, fun _ => 1].map
      fairCoin.toFiniteContent.integral) := by
  apply fairCoin.toFiniteContent.integral_monotoneChain
  simp only [PointwiseMonotoneChainOn]
  constructor
  · intro atom member
    cases atom.item <;> decide
  · constructor
    · intro atom member
      cases atom.item <;> decide
    · trivial

example : fairCoin.toFiniteContent.integral
      (pointwiseMinimum coinNumber [reverseCoinNumber]) ≤
    fairCoin.toFiniteContent.integral coinNumber := by
  apply fairCoin.toFiniteContent.integral_pointwiseMinimum_le_of_mem
  exact List.mem_cons_self

def coinIntegralErrorBudget : FiniteContent.IntegralErrorBudget
    fairCoin.toFiniteContent coinNumber reverseCoinNumber where
  envelope _ := 1
  envelope_nonnegative atom member := by decide
  dominates atom member := by
    cases atom.item <;> decide

example : rationalSeparation
      (fairCoin.expectation coinNumber)
      (fairCoin.expectation reverseCoinNumber) ≤
    coinIntegralErrorBudget.error :=
  coinIntegralErrorBudget.integral_separation_le

def coinMonotoneIntegralBudget : FiniteContent.MonotoneIntegralBudget
    fairCoin.toFiniteContent (fun _ => 0) coinNumber where
  remainder := coinNumber
  remainder_nonnegative atom member := by
    cases atom.item <;> decide
  approximation_le atom member := by
    cases atom.item <;> decide
  gap_le_remainder atom member := by
    cases atom.item <;> decide

example : rationalSeparation
      (fairCoin.expectation fun _ => 0)
      (fairCoin.expectation coinNumber) < 3 / 4 := by
  apply coinMonotoneIntegralBudget.accurate (3 / 4)
  decide

/-- A displayed three-quarter/one-quarter rational mixing coefficient. -/
def mostlyFalseWeight : MixingWeight where
  coefficient := 3 / 4
  nonnegative := by decide
  atMostOne := by decide

/-- A biased coin built by concatenating two scaled one-atom tables. -/
def quarterCoin : Distribution Bool :=
  (Distribution.pure false).mixture (Distribution.pure true)
    mostlyFalseWeight

/-- Numeric pushforward of the quarter-heads coin. -/
def quarterCoinNumberLaw : Distribution Coordinate :=
  quarterCoin.map coinNumber

/-- A small rational perturbation of the fair coin, used to display global
finite-CDF and quantile stability calculations. -/
def twoFifthsHeadsCoin : Distribution Bool where
  atoms :=
    [⟨false, 3 / 5, by decide⟩,
      ⟨true, 2 / 5, by decide⟩]
  total_one := by decide

def twoFifthsHeadsNumberLaw : Distribution Coordinate :=
  twoFifthsHeadsCoin.map coinNumber

theorem mostlyFalseWeight_coefficient_positive :
    0 < mostlyFalseWeight.coefficient := by
  decide

theorem mostlyFalseWeight_complement_positive :
    0 < mostlyFalseWeight.complement := by
  decide

example : (Distribution.pure true).poweredLp 3 coinNumber = 1 := by
  rw [Distribution.pure_poweredLp]
  decide

example : (Distribution.pure false).essentialMaximumMagnitude coinNumber =
    0 := by
  rw [Distribution.pure_essentialMaximumMagnitude]
  decide

example : quarterCoin.atoms.length = 2 := by
  decide

example : quarterCoin.probability (fun outcome => outcome) = 1 / 4 := by
  decide

theorem coinNumberLaw_finiteKolmogorovDistance_quarterCoinNumberLaw :
    coinNumberLaw.finiteKolmogorovDistance quarterCoinNumberLaw =
    1 / 4 := by
  decide

example : coinNumberLaw.comparisonSupportCardinality quarterCoinNumberLaw =
    2 := by
  decide

example : coinNumberLaw.totalVariationDistance quarterCoinNumberLaw ≤
    1 / 2 := by
  have bound :=
    coinNumberLaw
      |>.totalVariationDistance_le_supportCardinality_mul_finiteKolmogorovDistance
        quarterCoinNumberLaw
  rw [show coinNumberLaw.comparisonSupportCardinality
      quarterCoinNumberLaw = 2 by decide,
    coinNumberLaw_finiteKolmogorovDistance_quarterCoinNumberLaw] at bound
  calc
    coinNumberLaw.totalVariationDistance quarterCoinNumberLaw ≤
        (2 : Coordinate) * (1 / 4) := bound
    _ = 1 / 2 := by decide

example (cut : Coordinate) :
    rationalSeparation (coinNumberLaw.cumulative cut)
        (quarterCoinNumberLaw.cumulative cut) ≤ 1 / 4 := by
  have global : coinNumberLaw.finiteKolmogorovDistance
      quarterCoinNumberLaw ≤ 1 / 4 :=
    coinNumberLaw_finiteKolmogorovDistance_quarterCoinNumberLaw.le
  exact (coinNumberLaw.cumulative_separation_le_finiteKolmogorovDistance
    quarterCoinNumberLaw cut).trans global

example : twoFifthsHeadsNumberLaw.finiteKolmogorovDistance coinNumberLaw =
    1 / 10 := by
  decide

example :
    0 < twoFifthsHeadsNumberLaw.lowerQuantile
          (3 / 4) (by decide) (by decide) ∧
      twoFifthsHeadsNumberLaw.lowerQuantile
          (3 / 4) (by decide) (by decide) ≤ 1 :=
  twoFifthsHeadsNumberLaw
    |>.lowerQuantile_mem_bracket_of_finiteKolmogorovDistance_lt
      coinNumberLaw (3 / 4) (by decide) (by decide) 0 1 (1 / 8)
        (by decide) (by decide) (by decide)

example : quarterCoin.expectation coinNumber = 1 / 4 := by
  decide

example : quarterCoin.essentialMaximumMagnitude coinNumber =
    max ((Distribution.pure false).essentialMaximumMagnitude coinNumber)
      ((Distribution.pure true).essentialMaximumMagnitude coinNumber) := by
  unfold quarterCoin
  exact (Distribution.pure false).mixture_essentialMaximumMagnitude_eq_max
    (Distribution.pure true) mostlyFalseWeight
    mostlyFalseWeight_coefficient_positive
    mostlyFalseWeight_complement_positive coinNumber

example : quarterCoin.essentialMaximumMagnitude coinNumber = 1 := by
  decide

example : quarterCoin.poweredLp 3 coinNumber =
    mostlyFalseWeight.coefficient *
        (Distribution.pure false).poweredLp 3 coinNumber +
      mostlyFalseWeight.complement *
        (Distribution.pure true).poweredLp 3 coinNumber := by
  unfold quarterCoin
  exact (Distribution.pure false).mixture_poweredLp
    (Distribution.pure true) mostlyFalseWeight 3 coinNumber

example : quarterCoin.poweredLp 3 coinNumber = 1 / 4 := by
  decide

example : quarterCoin.l1Distance coinNumber reverseCoinNumber =
    mostlyFalseWeight.coefficient *
        (Distribution.pure false).l1Distance coinNumber reverseCoinNumber +
      mostlyFalseWeight.complement *
        (Distribution.pure true).l1Distance
          coinNumber reverseCoinNumber := by
  unfold quarterCoin
  exact (Distribution.pure false).mixture_l1Distance
    (Distribution.pure true) mostlyFalseWeight
      coinNumber reverseCoinNumber

example : quarterCoin.variance coinNumber = 3 / 16 := by
  decide

example : fairCoin.variance coinNumber =
    fairCoin.poweredL2Distance coinNumber
      (fun _ => fairCoin.expectation coinNumber) :=
  fairCoin.variance_eq_poweredL2Distance_expectation coinNumber

example : fairCoin.variance coinNumber ≤ fairCoin.poweredL2 coinNumber :=
  fairCoin.variance_le_poweredL2 coinNumber

example : fairCoin.variance coinNumber = 0 ↔
    fairCoin.EqualAlmostEverywhere coinNumber
      (fun _ => fairCoin.expectation coinNumber) :=
  fairCoin.variance_eq_zero_iff_equalAlmostEverywhere_expectation coinNumber

example (center : Coordinate) :
    fairCoin.varianceAround coinNumber center =
      fairCoin.variance coinNumber +
        (fairCoin.expectation coinNumber - center) ^ 2 :=
  fairCoin.varianceAround_eq_variance_add_mean_sub_sq coinNumber center

example (center : Coordinate) :
    fairCoin.varianceAround coinNumber center = fairCoin.variance coinNumber ↔
      center = fairCoin.expectation coinNumber :=
  fairCoin.varianceAround_eq_variance_iff_center_eq_expectation
    coinNumber center

example : quarterCoin.variance coinNumber =
    mostlyFalseWeight.coefficient *
        (Distribution.pure false).variance coinNumber +
      mostlyFalseWeight.complement *
        (Distribution.pure true).variance coinNumber +
      mostlyFalseWeight.coefficient * mostlyFalseWeight.complement *
        ((Distribution.pure false).expectation coinNumber -
          (Distribution.pure true).expectation coinNumber) ^ 2 :=
  (Distribution.pure false).mixture_variance
    (Distribution.pure true) mostlyFalseWeight coinNumber

example : fairCoin.covariance coinNumber reverseCoinNumber ^ 2 ≤
    fairCoin.variance coinNumber * fairCoin.variance reverseCoinNumber :=
  fairCoin.covariance_sq_le_variance_mul coinNumber reverseCoinNumber

example : 0 ≤ fairCoin.squaredCorrelation coinNumber reverseCoinNumber ∧
    fairCoin.squaredCorrelation coinNumber reverseCoinNumber ≤ 1 :=
  fairCoin.squaredCorrelation_mem_unit coinNumber reverseCoinNumber (by decide)

example : fairCoin.squaredCorrelation coinNumber reverseCoinNumber = 1 := by
  decide

example : fairCoin.covariance
      (fun outcome => coinNumber outcome + 7) reverseCoinNumber =
    fairCoin.covariance coinNumber reverseCoinNumber :=
  fairCoin.covariance_add_constant_left coinNumber reverseCoinNumber 7

example : fairCoin.variance
      (fun outcome => coinNumber outcome + reverseCoinNumber outcome) +
        fairCoin.variance
          (fun outcome => coinNumber outcome - reverseCoinNumber outcome) =
    2 * fairCoin.variance coinNumber +
      2 * fairCoin.variance reverseCoinNumber :=
  fairCoin.variance_parallelogram coinNumber reverseCoinNumber

example : 2 * fairCoin.covariance coinNumber reverseCoinNumber ≤
    fairCoin.variance coinNumber + fairCoin.variance reverseCoinNumber :=
  fairCoin.two_mul_covariance_le_variance_add
    coinNumber reverseCoinNumber

example : fairCoin.expectation coinNumber ^ 2 ≤
    fairCoin.expectation (fun outcome => coinNumber outcome ^ 2) :=
  fairCoin.jensen_square coinNumber

example : rationalSeparation (fairCoin.expectation coinPayoff) 0 ≤
    fairCoin.expectation (fun outcome =>
      rationalSeparation (coinPayoff outcome) 0) :=
  fairCoin.jensen_rationalSeparation_zero coinPayoff

example : fairCoin.covariance coinNumber reverseCoinNumber ^ 2 =
    fairCoin.variance coinNumber * fairCoin.variance reverseCoinNumber := by
  decide

example : (fairCoin.iidSamples 4).atoms.length = 16 := by
  decide

example (count : Nat) :
    (fairCoin.iidSamples count).atoms.length = fairCoin.atoms.length ^ count :=
  fairCoin.iidSamples_atoms_length count

example (count : Nat) :
    (fairCoin.iidSamples count).probability
      (fun sample => decide (sample.length = count)) = 1 :=
  fairCoin.iidSamples_probability_sampleLength_eq count

example : (fairCoin.iidSamples 3).expectation (sampleSum coinNumber) =
    3 / 2 := by
  decide

example : (fairCoin.iidSamples 4).variance
    (Distribution.sampleMean 4 coinNumber) = 1 / 16 := by
  decide

example : (fairCoin.iidSamples 4).probability
    (fairCoin.sampleMeanDeviation 4 coinNumber (1 / 2)) = 1 / 8 := by
  simp only [Distribution.iidSamples_succ, Distribution.map_probability,
    Distribution.product_probability_iterated]
  decide

example : (fairCoin.iidSamples 4).probability
      (fairCoin.sampleMeanDeviation 4 coinNumber (1 / 2)) ≤
    (fairCoin.variance coinNumber / 4) / (1 / 2) ^ 2 :=
  fairCoin.iidSamples_sampleMean_chebyshev coinNumber 4 (by decide)
    (1 / 2) (by decide)

example : Distribution.requiredEventFrequencySampleCount
    (1 / 10) (1 / 20) = 501 := by decide

example : (fairCoin.iidSamples 4).expectation
    (Distribution.eventFrequency 4 (fun outcome => outcome)) = 1 / 2 := by
  rw [fairCoin.iidSamples_expectation_eventFrequency
    (fun outcome => outcome) 4 (by decide)]
  rfl

example : (fairCoin.iidSamples 4).variance
    (Distribution.eventFrequency 4 (fun outcome => outcome)) = 1 / 16 := by
  rw [fairCoin.iidSamples_variance_eventFrequency
    (fun outcome => outcome) 4 (by decide)]
  rfl

def coinFrequencyEvents : List (Bool → Bool) :=
  [fun outcome => outcome, fun outcome => !outcome]

example : Distribution.requiredEventFamilyFrequencySampleCount
    coinFrequencyEvents (1 / 10) (1 / 20) = 1501 := by decide

example :
    (fairCoin.iidSamples
      (Distribution.requiredEventFamilyFrequencySampleCount
        coinFrequencyEvents (1 / 10) (1 / 20))).probability
      (Distribution.simultaneousEventFrequencyDeviation fairCoin
        coinFrequencyEvents
        (Distribution.requiredEventFamilyFrequencySampleCount
          coinFrequencyEvents (1 / 10) (1 / 20))
        (1 / 10)) < 1 / 20 :=
  fairCoin.iidSamples_simultaneousEventFrequency_deviationProbability_lt_requested
    coinFrequencyEvents (1 / 10) (by decide) (1 / 20) (by decide)

def coinCumulativeThresholdGrid : List Coordinate := [0, 1]

example : Distribution.requiredCumulativeGridSampleCount
    coinCumulativeThresholdGrid (1 / 10) (1 / 20) = 1501 := by decide

example : Distribution.requiredFiniteKolmogorovSampleCount coinNumberLaw
    (1 / 10) (1 / 20) = 1501 := by decide

example :
    (coinNumberLaw.iidSamples
      (Distribution.requiredFiniteKolmogorovSampleCount coinNumberLaw
        (1 / 10) (1 / 20))).probability
      (Distribution.empiricalFiniteKolmogorovDistanceDeviation coinNumberLaw
        (Distribution.requiredFiniteKolmogorovSampleCount coinNumberLaw
          (1 / 10) (1 / 20))
        (1 / 10)) < 1 / 20 :=
  coinNumberLaw
    |>.iidSamples_empiricalFiniteKolmogorovDistanceDeviation_lt_requested
      (1 / 10) (by decide) (1 / 20) (by decide)

example :
    (coinNumberLaw.iidSamples
      (Distribution.requiredCumulativeGridSampleCount
        coinCumulativeThresholdGrid (1 / 10) (1 / 20))).probability
      (Distribution.empiricalCumulativeGridDeviation coinNumberLaw
        coinCumulativeThresholdGrid
        (Distribution.requiredCumulativeGridSampleCount
          coinCumulativeThresholdGrid (1 / 10) (1 / 20))
        (1 / 10)) < 1 / 20 :=
  coinNumberLaw.iidSamples_empiricalCumulativeGrid_deviationProbability_lt_requested
    coinCumulativeThresholdGrid (1 / 10) (by decide) (1 / 20) (by decide)

example (sample : List Coordinate)
    (outside : Distribution.empiricalCumulativeGridDeviation coinNumberLaw
      coinCumulativeThresholdGrid 1501 (1 / 10) sample = false) :
    Distribution.EmpiricalCumulativeGridAccurate coinNumberLaw
      coinCumulativeThresholdGrid 1501 (1 / 10) sample :=
  coinNumberLaw.empiricalCumulativeGridAccurate_of_outside
    coinCumulativeThresholdGrid 1501 (1 / 10) sample outside

example :
    (coinNumberLaw.iidSamples
      (Distribution.requiredCumulativeGridSampleCount
        coinCumulativeThresholdGrid (1 / 10) (1 / 20))).probability
      (Distribution.empiricalLowerQuantileBracketDeviation
        (Distribution.requiredCumulativeGridSampleCount
          coinCumulativeThresholdGrid (1 / 10) (1 / 20))
        (3 / 4) (by decide) (by decide) 0 1) < 1 / 20 := by
  apply coinNumberLaw
    |>.iidSamples_empiricalLowerQuantileBracketDeviation_lt_requested
      coinCumulativeThresholdGrid (1 / 10) (by decide)
        (1 / 20) (by decide) (3 / 4) (by decide) (by decide) 0 1
  · decide
  · decide
  · decide
  · decide

example (approximation : Distribution Coordinate)
    (close : approximation.totalVariationDistance coinNumberLaw < 1 / 10) :
    Distribution.CumulativeGridClose approximation coinNumberLaw
      coinCumulativeThresholdGrid (1 / 10) :=
  approximation.cumulativeGridClose_of_totalVariationDistance_lt
    coinNumberLaw coinCumulativeThresholdGrid (1 / 10) close

/-- Couple a fair coin to a deterministic false output.  The joint table is
still obtained by an explicit finite pushforward. -/
def coinToFalseCoupling : Coupling Bool Bool where
  joint := (Coupling.graph fairCoin fun _ => false).joint

def sameBool (left right : Bool) : Bool := left == right

def boolMismatchCost (left right : Bool) : Coordinate :=
  if sameBool left right then 0 else 1

def flipRelation (left right : Bool) : Bool :=
  right == !left

def fairFlipLawCoupling :
    LawCoupling fairCoin (fairCoin.map fun outcome => !outcome) :=
  LawCoupling.graph fairCoin fun outcome => !outcome

example : LawCoupling (fairCoin.map fun outcome => !outcome) fairCoin :=
  fairFlipLawCoupling.symm

example : fairFlipLawCoupling.mismatchProbability flipRelation = 0 := by
  decide

example :
    (fairCoin.map fun outcome => !outcome).probability
          (fun outcome => !outcome) -
        fairCoin.probability (fun outcome => outcome) ≤
          fairFlipLawCoupling.mismatchProbability flipRelation ∧
      fairCoin.probability (fun outcome => outcome) -
          (fairCoin.map fun outcome => !outcome).probability
            (fun outcome => !outcome) ≤
          fairFlipLawCoupling.mismatchProbability flipRelation := by
  apply fairFlipLawCoupling.probability_close_of_eventsAgree
    flipRelation (fun outcome => outcome) (fun outcome => !outcome)
  intro atom member related
  rcases atom with ⟨⟨left, right⟩, weight, nonnegative⟩
  change (right == !left) = true at related
  have rightEqual : right = !left := eq_of_beq related
  subst right
  cases left <;> rfl

example : coinToFalseCoupling.mismatchProbability sameBool = 1 / 2 := by
  decide

example : coinToFalseCoupling.transportCost boolMismatchCost = 1 / 2 := by
  decide

example : coinToFalseCoupling.leftMarginal.probability
    (fun outcome => outcome) = 1 / 2 := by
  decide

example : coinToFalseCoupling.rightMarginal.probability
    (fun outcome => outcome) = 0 := by
  decide

example : coinToFalseCoupling.leftMarginal.probability
    (fun outcome => outcome) = fairCoin.probability (fun outcome => outcome) := by
  exact Coupling.graph_leftMarginal_probability fairCoin
    (fun _ => false) (fun outcome => outcome)

example : coinToFalseCoupling.mismatchProbability
    (fun _ right => !right) = 0 := by
  apply Coupling.graph_mismatchProbability_eq_zero
  intro atom member
  rfl

example :
    coinToFalseCoupling.leftMarginal.probability (fun outcome => outcome) -
        coinToFalseCoupling.rightMarginal.probability (fun outcome => outcome) =
      coinToFalseCoupling.mismatchProbability sameBool := by
  decide

example :
    coinToFalseCoupling.rightMarginal.probability (fun outcome => outcome) -
          coinToFalseCoupling.leftMarginal.probability (fun outcome => outcome) ≤
        coinToFalseCoupling.mismatchProbability sameBool ∧
      coinToFalseCoupling.leftMarginal.probability (fun outcome => outcome) -
          coinToFalseCoupling.rightMarginal.probability (fun outcome => outcome) ≤
        coinToFalseCoupling.mismatchProbability sameBool := by
  apply coinToFalseCoupling.probability_close_of_eventsAgree sameBool
  intro atom member related
  exact eq_of_beq related

example :
    coinToFalseCoupling.rightMarginal.expectation
          (Distribution.indicator fun outcome => outcome) -
        coinToFalseCoupling.leftMarginal.expectation
          (Distribution.indicator fun outcome => outcome) ≤
      coinToFalseCoupling.transportCost boolMismatchCost ∧
    coinToFalseCoupling.leftMarginal.expectation
          (Distribution.indicator fun outcome => outcome) -
        coinToFalseCoupling.rightMarginal.expectation
          (Distribution.indicator fun outcome => outcome) ≤
      coinToFalseCoupling.transportCost boolMismatchCost := by
  apply coinToFalseCoupling.expectation_close_of_transportCost
  intro atom member
  rcases atom.item with ⟨left, right⟩
  cases left <;> cases right <;> decide

example : fairCoin.probability (fun outcome => outcome) = 1 / 2 := by
  decide

def neverEvent (_ : Bool) : Bool := false

example : fairCoin.l1Distance
      (Distribution.indicator (fun outcome => outcome))
      (Distribution.indicator neverEvent) = 1 / 2 := by
  decide

example : fairCoin.probability
    (symmetricDifferenceEvent (fun outcome => outcome) neverEvent) = 1 / 2 := by
  decide

example :
    fairCoin.probability neverEvent -
          fairCoin.probability (fun outcome => outcome) ≤
        fairCoin.probability
          (symmetricDifferenceEvent (fun outcome => outcome) neverEvent) ∧
      fairCoin.probability (fun outcome => outcome) -
          fairCoin.probability neverEvent ≤
        fairCoin.probability
          (symmetricDifferenceEvent (fun outcome => outcome) neverEvent) :=
  fairCoin.probability_close_symmetricDifference
    (fun outcome => outcome) neverEvent

def twoOnHeads (outcome : Bool) : Coordinate :=
  if outcome then 2 else 0

def twoOnHeadsBoundedInMeasure : Distribution.BoundedInMeasureBudget
    fairCoin twoOnHeads (fun _ => 0) where
  inMeasure :=
    { threshold := 1
      threshold_positive := by decide
      failure := 1 / 2
      failure_nonnegative := by decide
      probability_le := by decide }
  ceiling := 2
  threshold_le_ceiling := by decide
  error_le := by
    intro atom member
    cases atom.item <;> decide

example : fairCoin.l1Distance twoOnHeads (fun _ => 0) = 1 := by
  decide

example : twoOnHeadsBoundedInMeasure.l1Bound = 3 / 2 := by
  decide

example : fairCoin.l1Distance twoOnHeads (fun _ => 0) ≤
    twoOnHeadsBoundedInMeasure.l1Bound :=
  twoOnHeadsBoundedInMeasure.l1Distance_le

example : fairCoin.probability
    (separationAtLeast 2 twoOnHeads (fun _ => 0)) = 1 / 2 := by
  decide

example : fairCoin.probability
      (separationAtLeast 2 twoOnHeads (fun _ => 0)) ≤
    fairCoin.l1Distance twoOnHeads (fun _ => 0) / 2 :=
  fairCoin.probability_separationAtLeast_le_l1
    2 (by decide) twoOnHeads (fun _ => 0)

example : fairCoin.expectation twoOnHeads -
      fairCoin.expectation (fun _ => 0) =
    fairCoin.l1Distance twoOnHeads (fun _ => 0) := by
  decide

def signedCoinDifference : SignedContent Bool where
  atoms := [⟨false, 1⟩, ⟨true, -1⟩]

example : FiniteContent.EvaluationEquivalent
    fairCoin.toFiniteContent.consolidate fairCoin.toFiniteContent :=
  fairCoin.toFiniteContent.consolidate_evaluationEquivalent

example : FiniteContent.EvaluationEquivalent
      fairCoin.toFiniteContent.consolidate fairCoin.toFiniteContent ↔
    ∀ outcome : Bool,
      fairCoin.toFiniteContent.consolidate.measure (atomEvent outcome) =
        fairCoin.toFiniteContent.measure (atomEvent outcome) :=
  FiniteContent.evaluationEquivalent_iff_atom_measure_eq _ _

def signedCoinHahnCertificate :
    SignedContent.HahnCertificate signedCoinDifference where
  positiveEvent := fun outcome => !outcome
  selected_nonnegative := by
    intro atom member selected
    simp only [signedCoinDifference, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    · decide
    · have impossible : false = true := by
        simpa only [Bool.not_true] using selected
      exact Bool.noConfusion impossible
  unselected_nonpositive := by
    intro atom member selected
    simp only [signedCoinDifference, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl
    · have impossible : true = false := by
        simpa only [Bool.not_false] using selected
      exact Bool.noConfusion impossible
    · decide

example : signedCoinDifference.total = 0 := by
  decide

example : signedCoinDifference.measure (fun outcome => !outcome) = 1 := by
  decide

example : signedCoinDifference.measure (fun outcome => outcome) = -1 := by
  decide

example (event : Bool → Bool) :
    signedCoinDifference.measure event ≤
      signedCoinDifference.measure
        signedCoinHahnCertificate.positiveEvent :=
  signedCoinHahnCertificate.measure_le_positiveEvent event

example : signedCoinDifference.variationContent.total =
    signedCoinDifference.measure signedCoinHahnCertificate.positiveEvent -
      signedCoinDifference.measure
        (fun outcome => !(signedCoinHahnCertificate.positiveEvent outcome)) :=
  signedCoinHahnCertificate.variationTotal_eq_measure_sub_complement

example : signedCoinDifference.integral
      signedCoinHahnCertificate.signObservable = 2 := by
  decide

example : signedCoinDifference.integral
      signedCoinHahnCertificate.signObservable =
    signedCoinDifference.variationContent.total :=
  signedCoinHahnCertificate.integral_signObservable_eq_variationTotal

example : signedCoinDifference.positiveContent.total = 1 ∧
    signedCoinDifference.negativeContent.total = 1 ∧
    signedCoinDifference.variationContent.total = 2 := by
  decide

example : FiniteContent.MutuallySingular
    signedCoinDifference.positiveContent
      signedCoinDifference.negativeContent :=
  signedCoinHahnCertificate.positiveContent_mutuallySingular_negativeContent

example (other : SignedContent.JordanDecomposition signedCoinDifference)
    (event : Bool → Bool) :
    other.positive.measure event =
      signedCoinDifference.positiveContent.measure event :=
  other.positive_measure_eq_canonical signedCoinHahnCertificate event

example (other : SignedContent.JordanDecomposition signedCoinDifference)
    (event : Bool → Bool) :
    other.negative.measure event =
      signedCoinDifference.negativeContent.measure event :=
  other.negative_measure_eq_canonical signedCoinHahnCertificate event

example : signedCoinDifference.measure (fun outcome => outcome) =
    signedCoinDifference.positiveContent.measure (fun outcome => outcome) -
      signedCoinDifference.negativeContent.measure (fun outcome => outcome) :=
  signedCoinDifference.measure_eq_positive_sub_negative
    (fun outcome => outcome)

example :
    signedCoinDifference.measure (fun outcome => outcome) ≤
        signedCoinDifference.variationContent.measure
          (fun outcome => outcome) ∧
      -signedCoinDifference.measure (fun outcome => outcome) ≤
        signedCoinDifference.variationContent.measure
          (fun outcome => outcome) :=
  signedCoinDifference.measure_bounded_by_variation
    (fun outcome => outcome)

def signedCoinObservable (outcome : Bool) : Coordinate :=
  if outcome then 2 else 3

example : signedCoinDifference.integral signedCoinObservable = 1 := by
  decide

example : signedCoinDifference.variationIntegral signedCoinObservable = 5 := by
  decide

example : rationalSeparation
      (signedCoinDifference.integral signedCoinObservable) 0 ≤
    signedCoinDifference.variationIntegral signedCoinObservable :=
  signedCoinDifference.integral_bounded_by_variationIntegral
    signedCoinObservable

example : fairCoin.toFiniteContent.measure (fun outcome => outcome) =
    1 / 2 := by
  decide

example :
    (fairCoin.toFiniteContent.restrict (fun outcome => outcome)).total =
      1 / 2 := by
  decide

example : fairCoin.toFiniteContent.integral
    (fun outcome => if outcome then 3 else 1) = 2 := by
  decide

example :
    (fairCoin.toFiniteContent.product fairCoin.toFiniteContent).measure
        (fun pair => pair.1 && pair.2) = 1 / 4 := by
  decide

example : fairCoin.expectation (fun outcome => if outcome then 1 else 0) =
    1 / 2 := by
  decide

def coinDensity (outcome : Bool) : Coordinate :=
  if outcome then 3 / 2 else 1 / 2

theorem coinDensity_nonnegative (outcome : Bool) :
    0 ≤ coinDensity outcome := by
  cases outcome <;> decide

theorem coinDensity_normalizes : fairCoin.expectation coinDensity = 1 := by
  decide

def biasedCoin : Distribution Bool :=
  fairCoin.reweight coinDensity coinDensity_nonnegative
    coinDensity_normalizes

example : biasedCoin.probability (fun outcome => outcome) = 3 / 4 := by
  decide

example : biasedCoin.probability (fun outcome => outcome) =
    fairCoin.expectation (fun outcome =>
      coinDensity outcome * Distribution.indicator (fun value => value) outcome) :=
  Distribution.reweight_probability fairCoin coinDensity
    coinDensity_nonnegative coinDensity_normalizes (fun outcome => outcome)

def coinAtomicChange : AtomicChange Bool where
  rows :=
    [{ item := false
       sourceWeight := 1 / 4
       targetWeight := 1 / 2
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide },
     { item := true
       sourceWeight := 3 / 4
       targetWeight := 1 / 2
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide }]
  noRepeated := by
    simp [NoRepeatedAtomicRows, AtomicRowPayloadAbsent]

def coinAtomicReverseChange : AtomicChange Bool where
  rows :=
    [{ item := false
       sourceWeight := 1 / 2
       targetWeight := 1 / 4
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide },
     { item := true
       sourceWeight := 1 / 2
       targetWeight := 3 / 4
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide }]
  noRepeated := by
    simp [NoRepeatedAtomicRows, AtomicRowPayloadAbsent]

example : coinAtomicChange.density false = 2 := by
  decide

example : coinAtomicChange.density true = 2 / 3 := by
  decide

example : coinAtomicReverseChange.density false = 1 / 2 ∧
    coinAtomicReverseChange.density true = 3 / 2 := by
  decide

example : coinAtomicChange.source.EqualAlmostEverywhere
    (fun outcome => coinAtomicChange.witness.density outcome *
      coinAtomicReverseChange.witness.density outcome)
    (fun _ => 1) :=
  coinAtomicChange.witness.density_mul_reverse_eq_one_almostEverywhere
    coinAtomicReverseChange.witness

example : coinAtomicChange.target.AbsolutelyContinuous
    coinAtomicChange.source :=
  coinAtomicChange.target_absolutelyContinuous_source

example : coinAtomicChange.target.SameNullEvents coinAtomicChange.source :=
  coinAtomicChange.witness.sameNullEvents_of_reverse
    coinAtomicReverseChange.witness

example : coinAtomicChange.source.measure (fun outcome => outcome) =
    3 / 4 := by
  decide

example : coinAtomicChange.target.measure (fun outcome => outcome) =
    1 / 2 := by
  decide

example : coinAtomicChange.target.integral coinNumber =
    coinAtomicChange.source.integral (fun outcome =>
      coinAtomicChange.density outcome * coinNumber outcome) :=
  coinAtomicChange.witness.integral_eq coinNumber

example (other : AtomicChange.Witness coinAtomicChange.source
    coinAtomicChange.target) :
    coinAtomicChange.witness.density true = other.density true :=
  coinAtomicChange.witness.density_eq_of_positive_atom other true (by decide)

example :
    (coinAtomicChange.source.reweight coinAtomicChange.density
      coinAtomicChange.density_nonnegative).measure
        (fun outcome => outcome) =
      coinAtomicChange.target.measure (fun outcome => outcome) :=
  coinAtomicChange.reweight_measure_eq_target (fun outcome => outcome)

def zeroRowAtomicChange : AtomicChange Bool where
  rows :=
    [{ item := false
       sourceWeight := 0
       targetWeight := 0
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide },
     { item := true
       sourceWeight := 1
       targetWeight := 1
       source_nonnegative := by decide
       target_nonnegative := by decide
       target_zero_of_source_zero := by decide }]
  noRepeated := by
    simp [NoRepeatedAtomicRows, AtomicRowPayloadAbsent]

example : zeroRowAtomicChange.density false = 0 := by
  decide

example : zeroRowAtomicChange.target.measure (fun outcome => !outcome) = 0 :=
  zeroRowAtomicChange.target_measure_eq_zero_of_source_measure_eq_zero
    (fun outcome => !outcome) (by decide)

def zeroMassContent : FiniteContent Bool where
  atoms :=
    [⟨false, 0, by decide⟩,
      ⟨true, 1, by decide⟩]

def zeroMassLeft (outcome : Bool) : Coordinate :=
  if outcome then 3 else 7

def zeroMassRight (outcome : Bool) : Coordinate :=
  if outcome then 3 else 9

theorem zeroMassObservables_equalAlmostEverywhere :
    zeroMassContent.EqualAlmostEverywhere zeroMassLeft zeroMassRight := by
  intro atom member
  simp only [zeroMassContent, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl
  · exact Or.inl rfl
  · right
    change (3 : Coordinate) = 3
    rfl

theorem zeroMassRight_essentiallyBounded :
    zeroMassContent.EssentiallyBoundedBy zeroMassRight 3 := by
  intro atom member
  simp only [zeroMassContent, List.mem_cons, List.not_mem_nil, or_false]
    at member
  rcases member with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (by decide)

example : zeroMassContent.essentialMaximumMagnitude zeroMassLeft = 3 := by
  decide

example : zeroMassContent.essentialMaximumMagnitude zeroMassRight = 3 := by
  decide

example : zeroMassContent.essentialMaximumMagnitude zeroMassLeft =
    zeroMassContent.essentialMaximumMagnitude zeroMassRight :=
  zeroMassContent.essentialMaximumMagnitude_congr_almostEverywhere
    zeroMassLeft zeroMassRight zeroMassObservables_equalAlmostEverywhere

example : zeroMassContent.l1Distance zeroMassLeft zeroMassRight = 0 :=
  zeroMassContent.l1Distance_eq_zero_of_equalAlmostEverywhere
    zeroMassLeft zeroMassRight zeroMassObservables_equalAlmostEverywhere

example : zeroMassContent.poweredLp 4 zeroMassLeft =
    zeroMassContent.poweredLp 4 zeroMassRight :=
  zeroMassContent.poweredLp_congr_almostEverywhere 4
    zeroMassLeft zeroMassRight zeroMassObservables_equalAlmostEverywhere

example : zeroMassContent.poweredLpDistance 3
      zeroMassLeft zeroMassRight = 0 :=
  (zeroMassContent.poweredLpDistance_eq_zero_iff 2
    zeroMassLeft zeroMassRight).mpr
      zeroMassObservables_equalAlmostEverywhere

example : zeroMassContent.poweredL2Distance
      zeroMassLeft zeroMassRight = 0 ↔
    zeroMassContent.EqualAlmostEverywhere zeroMassLeft zeroMassRight :=
  zeroMassContent.poweredL2Distance_eq_zero_iff
    zeroMassLeft zeroMassRight

example : zeroMassContent.integral zeroMassLeft =
    zeroMassContent.integral zeroMassRight :=
  zeroMassContent.integral_congr_almostEverywhere
    zeroMassLeft zeroMassRight zeroMassObservables_equalAlmostEverywhere

example : zeroMassContent.poweredLp 2 zeroMassRight ≤
    zeroMassContent.total * 3 ^ 2 :=
  zeroMassContent.poweredLp_le_of_essentialBound 2 zeroMassRight 3
    zeroMassRight_essentiallyBounded

theorem fairCoin_true_positive :
    0 < fairCoin.probability (fun outcome => outcome) := by
  decide

example : (fairCoin.toFiniteContent.restrict
      (fun outcome => outcome)).poweredL2 coinNumber ≤
    fairCoin.toFiniteContent.poweredL2 coinNumber :=
  fairCoin.toFiniteContent.restrict_poweredL2_le
    (fun outcome => outcome) coinNumber

example : (fairCoin.toFiniteContent.restrict
      (fun outcome => outcome)).poweredL2 coinNumber = 1 / 2 ∧
    fairCoin.toFiniteContent.poweredL2 coinNumber = 1 / 2 := by
  decide

def trueCoin : Distribution Bool :=
  fairCoin.conditioned (fun outcome => outcome) fairCoin_true_positive

example : trueCoin.essentialMaximumMagnitude reverseCoinNumber ≤
    fairCoin.essentialMaximumMagnitude reverseCoinNumber := by
  unfold trueCoin
  exact fairCoin.conditioned_essentialMaximumMagnitude_le
    (fun outcome => outcome) fairCoin_true_positive reverseCoinNumber

example : trueCoin.essentialMaximumMagnitude reverseCoinNumber = 0 ∧
    fairCoin.essentialMaximumMagnitude reverseCoinNumber = 1 := by
  decide

example : trueCoin.essentialMaximumDistance
      coinNumber reverseCoinNumber ≤
    fairCoin.essentialMaximumDistance coinNumber reverseCoinNumber := by
  unfold trueCoin
  exact fairCoin.conditioned_essentialMaximumDistance_le
    (fun outcome => outcome) fairCoin_true_positive
    coinNumber reverseCoinNumber

example : trueCoin.poweredLp 3 coinNumber =
    fairCoin.conditionalMean (fun outcome => outcome) (fun outcome =>
      rationalSeparation (coinNumber outcome) 0 ^ 3) := by
  unfold trueCoin
  exact fairCoin.conditioned_poweredLp_eq_conditionalMean
    (fun outcome => outcome) fairCoin_true_positive 3 coinNumber

example : trueCoin.poweredLp 3 coinNumber = 1 := by
  decide

def fairCoinDensity (_ : Bool) : Coordinate := 1

def trueCoinDensity (outcome : Bool) : Coordinate :=
  if outcome then 2 else 0

theorem fairCoinDensity_nonnegative :
    ∀ outcome, 0 ≤ fairCoinDensity outcome := by
  intro outcome
  unfold fairCoinDensity
  decide

theorem trueCoinDensity_nonnegative :
    ∀ outcome, 0 ≤ trueCoinDensity outcome := by
  intro outcome
  cases outcome <;> decide

theorem fairCoinDensity_normalizes :
    fairCoin.expectation fairCoinDensity = 1 := by
  decide

theorem trueCoinDensity_normalizes :
    fairCoin.expectation trueCoinDensity = 1 := by
  decide

def fairCoinFromDensity : Distribution Bool :=
  fairCoin.reweight fairCoinDensity fairCoinDensity_nonnegative
    fairCoinDensity_normalizes

def trueCoinFromDensity : Distribution Bool :=
  fairCoin.reweight trueCoinDensity trueCoinDensity_nonnegative
    trueCoinDensity_normalizes

def trueCoinRadonNikodymWitness : AtomicChange.Witness
    fairCoin.toFiniteContent trueCoin.toFiniteContent :=
  AtomicChange.Witness.ofAbsolutelyContinuous fairCoin.toFiniteContent
    trueCoin.toFiniteContent
    (fairCoin.conditioned_absolutelyContinuous
      (fun outcome => outcome) fairCoin_true_positive)

def trueCoinAbsoluteContinuityModulus :
    FiniteContent.AbsoluteContinuityModulus
      trueCoin.toFiniteContent fairCoin.toFiniteContent :=
  (fairCoin.conditioned_absolutelyContinuous
    (fun outcome => outcome) fairCoin_true_positive).modulus

def coinLebesgueDecomposition : FiniteContent.LebesgueDecomposition
    fairCoin.toFiniteContent trueCoin.toFiniteContent :=
  fairCoin.toFiniteContent.lebesgueDecomposition trueCoin.toFiniteContent

example : trueCoin.probability (fun outcome => outcome) = 1 := by
  decide

example : fairCoin.totalVariationDistance trueCoin = 1 / 2 := by
  decide

example : (fairCoin.product fairCoin).totalVariationDistance
      (trueCoin.product fairCoin) = 1 / 2 := by
  rw [fairCoin.totalVariationDistance_product_common_right_eq
    trueCoin fairCoin]
  decide

example : (fairCoin.product fairCoin).totalVariationDistance
      (trueCoin.product trueCoin) ≤
    fairCoin.totalVariationDistance trueCoin +
      fairCoin.totalVariationDistance trueCoin :=
  fairCoin.totalVariationDistance_product_le_add trueCoin fairCoin trueCoin

example : (fairCoin.product fairCoin).totalVariationDistance
      (trueCoin.product trueCoin) ≤
    1 - (1 - fairCoin.totalVariationDistance trueCoin) *
      (1 - fairCoin.totalVariationDistance trueCoin) :=
  fairCoin.totalVariationDistance_product_le_one_sub_mul
    trueCoin fairCoin trueCoin

example : (fairCoin.iidSamples 2).totalVariationDistance
    (trueCoin.iidSamples 2) = 3 / 4 := by
  decide

example : (fairCoin.iidSamples 2).totalVariationDistance
      (trueCoin.iidSamples 2) ≤
    (2 : Coordinate) * fairCoin.totalVariationDistance trueCoin :=
  fairCoin.iidSamples_totalVariationDistance_le trueCoin 2

example : (fairCoin.iidSamples 2).totalVariationDistance
      (trueCoin.iidSamples 2) ≤
    1 - (1 - fairCoin.totalVariationDistance trueCoin) ^ 2 :=
  fairCoin.iidSamples_totalVariationDistance_le_one_sub_pow trueCoin 2

example : fairCoin.l1Distance fairCoinDensity trueCoinDensity = 1 := by
  decide

example : fairCoin.l1Distance fairCoinDensity trueCoinDensity =
    2 * fairCoinFromDensity.totalVariationDistance trueCoinFromDensity :=
  fairCoin.l1Distance_eq_two_mul_totalVariationDistance_reweight
    fairCoinDensity trueCoinDensity fairCoinDensity_nonnegative
    trueCoinDensity_nonnegative fairCoinDensity_normalizes
    trueCoinDensity_normalizes

example : fairCoinFromDensity.totalVariationDistance
    trueCoinFromDensity = 1 / 2 := by
  decide

example : fairCoin.atomMassL1Distance trueCoin = 1 := by
  decide

example (event : Bool → Bool) :
    rationalSeparation (fairCoin.probability event)
        (trueCoin.probability event) ≤
      fairCoin.totalVariationDistance trueCoin :=
  fairCoin.probability_separation_le_totalVariationDistance trueCoin event

example : rationalSeparation (fairCoin.expectation coinNumber)
      (trueCoin.expectation coinNumber) ≤
    fairCoin.totalVariationDistance trueCoin := by
  apply fairCoin.expectation_separation_le_totalVariationDistance_of_unitInterval
    trueCoin coinNumber
  · intro outcome
    cases outcome <;> decide
  · intro outcome
    cases outcome <;> decide

example : rationalSeparation (fairCoin.expectation coinNumber)
    (trueCoin.expectation coinNumber) = 1 / 2 := by
  decide

example : (fairCoin.maximalLawCoupling trueCoin).mismatchProbability
      LawCoupling.equalityRelation = 1 / 2 := by
  rw [fairCoin.maximalLawCoupling_mismatchProbability]
  decide

example : trueCoin.toFiniteContent.integral coinNumber =
    fairCoin.toFiniteContent.integral (fun outcome =>
      trueCoinRadonNikodymWitness.density outcome * coinNumber outcome) :=
  trueCoinRadonNikodymWitness.integral_eq coinNumber

example (epsilon : Coordinate) (positive : 0 < epsilon)
    (event : Bool → Bool)
    (small : fairCoin.probability event <
      trueCoinAbsoluteContinuityModulus.request epsilon positive) :
    trueCoin.probability event < epsilon :=
  trueCoinAbsoluteContinuityModulus.controls epsilon positive event small

example (event : Bool → Bool) : fairCoin.toFiniteContent.measure event =
    coinLebesgueDecomposition.regular.measure event +
      coinLebesgueDecomposition.singular.measure event :=
  coinLebesgueDecomposition.measure_eq event

example : FiniteContent.AbsolutelyContinuous
    coinLebesgueDecomposition.regular trueCoin.toFiniteContent :=
  coinLebesgueDecomposition.regular_absolutelyContinuous

example : FiniteContent.MutuallySingular trueCoin.toFiniteContent
    coinLebesgueDecomposition.singular :=
  coinLebesgueDecomposition.source_mutuallySingular_singular

example (other : FiniteContent.LebesgueDecomposition
      fairCoin.toFiniteContent trueCoin.toFiniteContent)
    (event : Bool → Bool) :
    other.regular.measure event =
      coinLebesgueDecomposition.regular.measure event :=
  other.regular_measure_eq coinLebesgueDecomposition event

example (other : FiniteContent.LebesgueDecomposition
      fairCoin.toFiniteContent trueCoin.toFiniteContent)
    (event : Bool → Bool) :
    other.singular.measure event =
      coinLebesgueDecomposition.singular.measure event :=
  other.singular_measure_eq coinLebesgueDecomposition event

example : trueCoin.expectation coinNumber =
    fairCoin.conditionalMean (fun outcome => outcome) coinNumber :=
  fairCoin.conditioned_expectation_eq_conditionalMean
    (fun outcome => outcome) fairCoin_true_positive coinNumber

example : fairCoin.conditionalMean (fun outcome => outcome) coinPayoff ^ 2 ≤
    fairCoin.conditionalMean (fun outcome => outcome)
      (fun outcome => coinPayoff outcome ^ 2) :=
  fairCoin.conditionalMean_sq_le (fun outcome => outcome)
    fairCoin_true_positive coinPayoff

example : rationalSeparation
      (fairCoin.conditionalMean (fun outcome => outcome) coinPayoff) 0 ≤
    fairCoin.conditionalMean (fun outcome => outcome) (fun item =>
      rationalSeparation (coinPayoff item) 0) :=
  fairCoin.conditionalMean_rationalSeparation_zero_le
    (fun outcome => outcome) fairCoin_true_positive coinPayoff

example : trueCoin.atoms.length = fairCoin.atoms.length :=
  fairCoin.conditioned_atoms_length
    (fun outcome => outcome) fairCoin_true_positive

example : trueCoin.probability
    (complementEvent fun outcome => outcome) = 0 :=
  fairCoin.conditioned_probability_complement
    (fun outcome => outcome) fairCoin_true_positive

example : FiniteContent.AbsolutelyContinuous trueCoin.toFiniteContent
    fairCoin.toFiniteContent :=
  fairCoin.conditioned_absolutelyContinuous
    (fun outcome => outcome) fairCoin_true_positive

example : FiniteContent.AbsolutelyContinuous trueCoin.toFiniteContent
      fairCoin.toFiniteContent ↔
    ∀ outcome : Bool,
      fairCoin.toFiniteContent.measure (atomEvent outcome) = 0 →
        trueCoin.toFiniteContent.measure (atomEvent outcome) = 0 :=
  FiniteContent.absolutelyContinuous_iff_atom_zero _ _

example (event : Bool → Bool) : trueCoin.probability event ≤
    (fairCoin.probability (fun outcome => outcome))⁻¹ *
      fairCoin.probability event :=
  fairCoin.conditioned_probability_le_inverse_mul
    (fun outcome => outcome) event fairCoin_true_positive

example : fairCoin.conditionalProbability (fun _ => true)
      (fun outcome => outcome) fairCoin_true_positive =
    fairCoin.toFiniteContent.integral (fun item =>
      fairCoin.conditioningDensity (fun outcome => outcome)
          fairCoin_true_positive item *
        Distribution.indicator (fun _ => true) item) :=
  fairCoin.conditionalProbability_eq_density_integral
    (fun outcome => outcome) (fun _ => true) fairCoin_true_positive

example : Distribution.EvaluationEquivalent
    (fairCoin.conditioned (fun _ => true) (by decide)) fairCoin :=
  fairCoin.conditioned_true_evaluationEquivalent (by decide)

example :
    fairCoin.conditionalProbability (fun _ => true) (fun outcome => outcome)
      fairCoin_true_positive = 1 := by
  decide

def coinPartition : EventPartition fairCoin where
  events := [fun outcome => !outcome, fun outcome => outcome]
  disjoint := by
    refine ⟨?_, ⟨?_, trivial⟩⟩
    · intro atom member both
      have itemTrue : atom.item = true := by
        simpa only [unionEvents, unionEvent, Bool.or_false] using both.2
      have impossible : false = true := by
        simpa only [itemTrue, Bool.not_true] using both.1
      exact Bool.noConfusion impossible
    · intro atom member both
      have impossible : false = true := by
        simpa only [unionEvents] using both.2
      exact Bool.noConfusion impossible
  covers := by
    intro atom member
    cases atom.item <;> rfl

example : (coinPartition.events.map fairCoin.probability).sum = 1 :=
  coinPartition.probabilities_sum_one

def positiveCoinPartition : PositiveEventPartition fairCoin where
  events := coinPartition.events
  disjoint := coinPartition.disjoint
  covers := coinPartition.covers
  positive := by
    intro event member
    simp only [coinPartition, List.mem_cons, List.not_mem_nil, or_false]
      at member
    rcases member with rfl | rfl <;> decide

def wholeCoinPartition : PositiveEventPartition fairCoin where
  events := [fun _ => true]
  disjoint := by
    constructor
    · intro atom member both
      have impossible : false = true := by
        simpa only [unionEvents] using both.2
      exact Bool.noConfusion impossible
    · trivial
  covers := by
    intro atom member
    rfl
  positive := by
    intro event member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst event
    decide

theorem coinSingletonConditionalIndependence :
    positiveCoinPartition.ConditionallyIndependentEvents
      (fun outcome => outcome) (fun outcome => outcome) := by
  intro condition member
  simp only [positiveCoinPartition, coinPartition, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · rw [fairCoin.conditionallyIndependentEvents_iff]
    unfold Distribution.conditionalProbability
    decide
  · rw [fairCoin.conditionallyIndependentEvents_iff]
    unfold Distribution.conditionalProbability
    decide

example : fairCoin.conditionalProbability
      (intersectionEvent (fun outcome => outcome) (fun outcome => outcome))
      (fun outcome => outcome) fairCoin_true_positive =
    fairCoin.conditionalProbability (fun outcome => outcome)
        (fun outcome => outcome) fairCoin_true_positive *
      fairCoin.conditionalProbability (fun outcome => outcome)
        (fun outcome => outcome) fairCoin_true_positive := by
  unfold Distribution.conditionalProbability
  decide

/-- The two singleton coin cells explicitly group into the one-cell coarse
partition. -/
def coinPartitionRefinesWhole : PositivePartitionRefinement
    positiveCoinPartition wholeCoinPartition where
  cellsFor := fun _ => positiveCoinPartition.events
  cells_mem := by
    intro coarseEvent coarseMember fineEvent fineMember
    exact fineMember
  cells_disjoint := by
    intro coarseEvent coarseMember
    exact positiveCoinPartition.disjoint
  agrees_on_atoms := by
    intro coarseEvent coarseMember atom atomMember
    simp only [wholeCoinPartition, List.mem_cons, List.not_mem_nil, or_false]
      at coarseMember
    subst coarseEvent
    exact positiveCoinPartition.covers atom atomMember

def coinFiltration : FiniteFiltration fairCoin positiveCoinPartition :=
  .extend (.base wholeCoinPartition) positiveCoinPartition
    coinPartitionRefinesWhole

/-- The singleton coin cells visibly retain every observable which is
constant on the one-cell coarse partition. -/
theorem coinFiltrationCellwiseCompatible :
    coinFiltration.CellwiseCompatible := by
  constructor
  · trivial
  · intro value represented
    rcases represented with ⟨represented⟩
    refine ⟨{
      cellValue := fun _ => represented.cellValue (fun _ : Bool => true)
      agrees := ?_ }⟩
    intro fineEvent fineMember atom atomMember selected
    exact represented.agrees (fun _ : Bool => true) List.mem_cons_self
      atom atomMember rfl

example : coinFiltration.depth = 2 := by
  decide

def coinPayoff (outcome : Bool) : Coordinate :=
  if outcome then 3 else 1

example : fairCoin.regressionSlope coinNumber coinPayoff = 2 := by
  decide

example : fairCoin.linearPrediction coinNumber coinPayoff = coinPayoff := by
  funext outcome
  cases outcome <;> decide

example : fairCoin.variance coinPayoff =
    fairCoin.variance (fairCoin.linearPrediction coinNumber coinPayoff) +
      fairCoin.variance (fairCoin.regressionResidual coinNumber coinPayoff) :=
  fairCoin.variance_eq_linearPrediction_add_regressionResidual
    coinNumber coinPayoff (by decide)

/-- Two explicitly independent fair coins for executable product-Lp checks. -/
def independentCoinPair : Distribution (Bool × Bool) :=
  fairCoin.product fairCoin

example : independentCoinPair.poweredLp 2
      (fun pair => coinNumber pair.1 * coinPayoff pair.2) =
    fairCoin.poweredLp 2 coinNumber * fairCoin.poweredLp 2 coinPayoff := by
  unfold independentCoinPair
  exact fairCoin.product_poweredLp_mul fairCoin 2 coinNumber coinPayoff

example : independentCoinPair.poweredLp 2
    (fun pair => coinNumber pair.1 * coinPayoff pair.2) = 5 / 2 := by
  decide

example : independentCoinPair.poweredLpDistance 3
      (fun pair => coinNumber pair.1)
      (fun pair => reverseCoinNumber pair.1) =
    fairCoin.poweredLpDistance 3 coinNumber reverseCoinNumber := by
  unfold independentCoinPair
  exact fairCoin.product_poweredLpDistance_left fairCoin 3
    coinNumber reverseCoinNumber

example : independentCoinPair.poweredLpDistance 3
      (fun pair => coinNumber pair.1)
      (fun pair => reverseCoinNumber pair.1) = 1 := by
  decide

example : independentCoinPair.poweredL2 (fun pair => coinPayoff pair.2) =
    fairCoin.poweredL2 coinPayoff := by
  unfold independentCoinPair
  exact fairCoin.product_poweredL2_right fairCoin coinPayoff

example : independentCoinPair.poweredL2
    (fun pair => coinPayoff pair.2) = 5 := by
  decide

example : independentCoinPair.essentialMaximumMagnitude
      (fun pair => coinNumber pair.1 * coinPayoff pair.2) =
    fairCoin.essentialMaximumMagnitude coinNumber *
      fairCoin.essentialMaximumMagnitude coinPayoff := by
  unfold independentCoinPair
  exact fairCoin.product_essentialMaximumMagnitude_mul fairCoin
    coinNumber coinPayoff

example : independentCoinPair.essentialMaximumMagnitude
    (fun pair => coinNumber pair.1 * coinPayoff pair.2) = 3 := by
  decide

example : independentCoinPair.essentialMaximumDistance
      (fun pair => coinNumber pair.1)
      (fun pair => reverseCoinNumber pair.1) =
    fairCoin.essentialMaximumDistance coinNumber reverseCoinNumber := by
  unfold independentCoinPair
  exact fairCoin.product_essentialMaximumDistance_left fairCoin
    coinNumber reverseCoinNumber

example : rationalSeparation (fairCoin.poweredL1 coinPayoff)
      (fairCoin.poweredL1 coinNumber) ≤
    fairCoin.l1Distance coinPayoff coinNumber :=
  fairCoin.poweredL1_separation_le_l1Distance coinPayoff coinNumber

example : rationalSeparation (fairCoin.poweredL1 coinPayoff)
        (fairCoin.poweredL1 coinNumber) = 3 / 2 ∧
    fairCoin.l1Distance coinPayoff coinNumber = 3 / 2 := by
  decide

example : fairCoin.poweredL1
      (fun outcome => coinNumber outcome + reverseCoinNumber outcome) ≤
    fairCoin.poweredL1 coinNumber +
      fairCoin.poweredL1 reverseCoinNumber :=
  fairCoin.poweredL1_add_le coinNumber reverseCoinNumber

example : fairCoin.poweredL1
        (fun outcome => coinNumber outcome + reverseCoinNumber outcome) = 1 ∧
    fairCoin.poweredL1 coinNumber +
        fairCoin.poweredL1 reverseCoinNumber = 1 := by
  decide

example : fairCoin.l1Distance
      (fun outcome => coinPayoff outcome * coinNumber outcome)
      (fun outcome => coinNumber outcome * reverseCoinNumber outcome) ≤
    fairCoin.essentialMaximumMagnitude coinNumber *
        fairCoin.l1Distance coinPayoff coinNumber +
      fairCoin.essentialMaximumMagnitude coinNumber *
        fairCoin.l1Distance coinNumber reverseCoinNumber :=
  fairCoin.l1Distance_mul_le coinPayoff coinNumber
    coinNumber reverseCoinNumber

example : fairCoin.l1Distance
        (fun outcome => coinPayoff outcome * coinNumber outcome)
        (fun outcome => coinNumber outcome * reverseCoinNumber outcome) =
      3 / 2 ∧
    fairCoin.essentialMaximumMagnitude coinNumber *
          fairCoin.l1Distance coinPayoff coinNumber +
        fairCoin.essentialMaximumMagnitude coinNumber *
          fairCoin.l1Distance coinNumber reverseCoinNumber = 5 / 2 := by
  decide

example : fairCoin.essentialMaximumMagnitude (fun _ => 0) = 0 :=
  fairCoin.essentialMaximumMagnitude_zero

example : rationalSeparation
      (fairCoin.essentialMaximumMagnitude coinPayoff)
      (fairCoin.essentialMaximumMagnitude coinNumber) ≤
    fairCoin.essentialMaximumDistance coinPayoff coinNumber :=
  fairCoin.essentialMaximumMagnitude_separation_le_distance
    coinPayoff coinNumber

example : rationalSeparation
        (fairCoin.essentialMaximumMagnitude coinPayoff)
        (fairCoin.essentialMaximumMagnitude coinNumber) = 2 ∧
    fairCoin.essentialMaximumDistance coinPayoff coinNumber = 2 := by
  decide

example : fairCoin.essentialMaximumMagnitude (fun _ => (-3)) = 3 := by
  calc
    fairCoin.essentialMaximumMagnitude (fun _ => (-3)) =
        rationalSeparation (-3) 0 :=
      fairCoin.essentialMaximumMagnitude_constant (-3)
    _ = 3 := by decide

example (value : Bool → Coordinate) :
    fairCoin.essentialMaximumMagnitude value = 0 ↔
      fairCoin.EqualAlmostEverywhere value (fun _ => 0) :=
  fairCoin.essentialMaximumMagnitude_eq_zero_iff value

example : fairCoin.essentialMaximumMagnitude
      (fun outcome => coinNumber outcome + coinPayoff outcome) ≤
    fairCoin.essentialMaximumMagnitude coinNumber +
      fairCoin.essentialMaximumMagnitude coinPayoff :=
  fairCoin.essentialMaximumMagnitude_add_le coinNumber coinPayoff

example : fairCoin.essentialMaximumMagnitude
      (fun outcome => coinNumber outcome + coinPayoff outcome) = 4 ∧
    fairCoin.essentialMaximumMagnitude coinNumber +
        fairCoin.essentialMaximumMagnitude coinPayoff = 4 := by
  decide

example : fairCoin.essentialMaximumMagnitude
      (fun outcome => (-2 : Coordinate) * coinPayoff outcome) =
    rationalSeparation (-2) 0 *
      fairCoin.essentialMaximumMagnitude coinPayoff :=
  fairCoin.essentialMaximumMagnitude_scale (-2) coinPayoff

example : fairCoin.essentialMaximumMagnitude
      (fun outcome => (-2 : Coordinate) * coinPayoff outcome) = 6 := by
  decide

example : fairCoin.essentialMaximumMagnitude
      (fun outcome => -coinPayoff outcome) =
    fairCoin.essentialMaximumMagnitude coinPayoff :=
  fairCoin.essentialMaximumMagnitude_neg coinPayoff

example : fairCoin.essentialMaximumMagnitude
      (fun outcome => coinPayoff outcome - coinNumber outcome) ≤
    fairCoin.essentialMaximumMagnitude coinPayoff +
      fairCoin.essentialMaximumMagnitude coinNumber :=
  fairCoin.essentialMaximumMagnitude_sub_le coinPayoff coinNumber

example : fairCoin.essentialMaximumMagnitude
      (fun outcome => coinNumber outcome * coinPayoff outcome) ≤
    fairCoin.essentialMaximumMagnitude coinNumber *
      fairCoin.essentialMaximumMagnitude coinPayoff :=
  fairCoin.essentialMaximumMagnitude_mul_le coinNumber coinPayoff

example : fairCoin.essentialMaximumMagnitude
      (fun outcome => coinNumber outcome * coinPayoff outcome) = 3 ∧
    fairCoin.essentialMaximumMagnitude coinNumber *
        fairCoin.essentialMaximumMagnitude coinPayoff = 3 := by
  decide

example : fairCoin.essentialMaximumDistance coinNumber reverseCoinNumber = 1 := by
  decide

example : fairCoin.essentialMaximumDistance coinNumber coinPayoff =
    fairCoin.essentialMaximumDistance coinPayoff coinNumber :=
  fairCoin.essentialMaximumDistance_symm coinNumber coinPayoff

example (third : Bool → Coordinate) :
    fairCoin.essentialMaximumDistance coinNumber coinPayoff ≤
      fairCoin.essentialMaximumDistance coinNumber third +
        fairCoin.essentialMaximumDistance third coinPayoff :=
  fairCoin.essentialMaximumDistance_triangle coinNumber third coinPayoff

example (left right : Bool → Coordinate) :
    fairCoin.essentialMaximumDistance left right = 0 ↔
      fairCoin.EqualAlmostEverywhere left right :=
  fairCoin.essentialMaximumDistance_eq_zero_iff left right

example : fairCoin.poweredLpDistance 3 coinNumber reverseCoinNumber ≤
    fairCoin.essentialMaximumDistance coinNumber reverseCoinNumber ^ 3 :=
  fairCoin.poweredLpDistance_le_essentialMaximumDistance
    3 coinNumber reverseCoinNumber

example : fairCoin.l1Distance coinNumber reverseCoinNumber ≤
    fairCoin.essentialMaximumDistance coinNumber reverseCoinNumber :=
  fairCoin.l1Distance_le_essentialMaximumDistance
    coinNumber reverseCoinNumber

example : rationalSeparation (fairCoin.expectation coinPayoff)
      (fairCoin.expectation coinNumber) ≤
    fairCoin.l1Distance coinPayoff coinNumber :=
  fairCoin.expectation_separation_le_l1Distance coinPayoff coinNumber

example : rationalSeparation (fairCoin.expectation coinPayoff)
      (fairCoin.expectation coinNumber) ≤
    fairCoin.essentialMaximumDistance coinPayoff coinNumber :=
  fairCoin.expectation_separation_le_essentialMaximumDistance
    coinPayoff coinNumber

example : rationalSeparation (fairCoin.expectation coinPayoff)
      (fairCoin.expectation coinNumber) = 3 / 2 ∧
    fairCoin.essentialMaximumDistance coinPayoff coinNumber = 2 := by
  decide

example : rationalSeparation
      (fairCoin.eventIntegral (fun outcome => outcome) coinPayoff)
      (fairCoin.eventIntegral (fun outcome => outcome) coinNumber) ≤
    fairCoin.probability (fun outcome => outcome) *
      fairCoin.essentialMaximumDistance coinPayoff coinNumber :=
  fairCoin.eventIntegral_separation_le_probability_mul_essentialMaximumDistance
    (fun outcome => outcome) coinPayoff coinNumber

example : rationalSeparation
      (fairCoin.eventIntegral (fun outcome => outcome) coinPayoff)
      (fairCoin.eventIntegral (fun outcome => outcome) coinNumber) = 1 ∧
    fairCoin.probability (fun outcome => outcome) *
        fairCoin.essentialMaximumDistance coinPayoff coinNumber = 1 := by
  decide

example : rationalSeparation
      (fairCoin.conditionalMean (fun outcome => outcome) coinPayoff)
      (fairCoin.conditionalMean (fun outcome => outcome) coinNumber) ≤
    fairCoin.essentialMaximumDistance coinPayoff coinNumber :=
  fairCoin.conditionalMean_separation_le_essentialMaximumDistance
    (fun outcome => outcome) fairCoin_true_positive coinPayoff coinNumber

example : rationalSeparation
      (fairCoin.conditionalMean (fun outcome => outcome) coinPayoff)
      (fairCoin.conditionalMean (fun outcome => outcome) coinNumber) = 2 ∧
    fairCoin.essentialMaximumDistance coinPayoff coinNumber = 2 := by
  decide

example : fairCoin.poweredL2Distance coinNumber reverseCoinNumber ≤
    fairCoin.essentialMaximumDistance coinNumber reverseCoinNumber ^ 2 :=
  fairCoin.poweredL2Distance_le_essentialMaximumDistance_sq
    coinNumber reverseCoinNumber

example : fairCoin.poweredLpDistance 3 coinNumber reverseCoinNumber = 1 ∧
    fairCoin.essentialMaximumDistance coinNumber reverseCoinNumber ^ 3 = 1 := by
  decide

example : fairCoin.poweredLp 3 coinPayoff ≤
    fairCoin.essentialMaximumMagnitude coinPayoff ^ 2 *
      fairCoin.poweredLp 1 coinPayoff := by
  have bound := fairCoin.poweredLp_add_le_essentialMaximum 1 2 coinPayoff
  simpa only using bound

example : fairCoin.poweredLp 3 coinPayoff = 14 ∧
    fairCoin.essentialMaximumMagnitude coinPayoff ^ 2 *
      fairCoin.poweredLp 1 coinPayoff = 18 := by
  decide

example : fairCoin.conditionalMean (fun outcome => outcome) coinPayoff = 3 := by
  decide

example : fairCoin.conditionalMean (fun _ => true)
        (fun outcome => coinNumber outcome * coinPayoff outcome) ^ 2 ≤
      fairCoin.conditionalMean (fun _ => true)
          (fun outcome => coinNumber outcome ^ 2) *
        fairCoin.conditionalMean (fun _ => true)
          (fun outcome => coinPayoff outcome ^ 2) :=
  fairCoin.conditionalMean_mul_sq_le (fun _ => true) (by decide)
    coinNumber coinPayoff

example : fairCoin.conditionalMean (fun _ => true)
        (fun outcome => coinNumber outcome * coinPayoff outcome) ^ 2 = 9 / 4 ∧
      fairCoin.conditionalMean (fun _ => true)
          (fun outcome => coinNumber outcome ^ 2) *
        fairCoin.conditionalMean (fun _ => true)
          (fun outcome => coinPayoff outcome ^ 2) = 5 / 2 := by
  decide

example : fairCoin.conditionalCovariance (fun _ => true)
        coinNumber coinPayoff ^ 2 ≤
      fairCoin.conditionalVariance (fun _ => true) coinNumber *
        fairCoin.conditionalVariance (fun _ => true) coinPayoff :=
  fairCoin.conditionalCovariance_sq_le_variance_mul
    (fun _ => true) (by decide) coinNumber coinPayoff

example : fairCoin.conditionalCovariance (fun _ => true)
        coinNumber coinPayoff = 1 / 2 ∧
      fairCoin.conditionalVariance (fun _ => true) coinNumber = 1 / 4 ∧
        fairCoin.conditionalVariance (fun _ => true) coinPayoff = 1 := by
  decide

example : fairCoin.conditionalCovariance (fun _ => true)
      (fun outcome => coinNumber outcome + 7) coinPayoff =
    fairCoin.conditionalCovariance (fun _ => true) coinNumber coinPayoff :=
  fairCoin.conditionalCovariance_add_constant_left
    (fun _ => true) (by decide) coinNumber coinPayoff 7

example : fairCoin.conditionalCovariance (fun _ => true)
      coinNumber coinPayoff =
    fairCoin.conditionalCovariance (fun _ => true)
      coinPayoff coinNumber :=
  fairCoin.conditionalCovariance_symm (fun _ => true) coinNumber coinPayoff

example : fairCoin.conditionalProbability (fun outcome => outcome)
        (fun _ => true) (by decide) ≤
      fairCoin.conditionalMean (fun _ => true) coinPayoff / 3 :=
  fairCoin.conditionalMarkov_bound (fun outcome => outcome)
    (fun _ => true) (by decide) coinPayoff 3 (by decide)
    (by intro item; cases item <;> decide)
    (by
      intro item selected
      cases item
      · exact Bool.noConfusion selected
      · decide)

example : fairCoin.conditionalProbability (fun _ => true)
        (fun _ => true) (by decide) ≤
      fairCoin.conditionalVariance (fun _ => true) coinPayoff / 1 ^ 2 :=
  fairCoin.conditionalChebyshev_bound (fun _ => true) (fun _ => true)
    (by decide) coinPayoff 1 (by decide) (by
      intro item selected
      cases item <;> decide)

example : fairCoin.conditionalProbability (fun outcome => outcome)
        (fun _ => true) (by decide) ≤
      fairCoin.conditionalVariance (fun _ => true) coinPayoff /
        (fairCoin.conditionalVariance (fun _ => true) coinPayoff + 1 ^ 2) :=
  fairCoin.conditionalCantelli_bound (fun outcome => outcome)
    (fun _ => true) (by decide) coinPayoff 1 (by decide) (by
      intro item selected
      cases item
      · exact Bool.noConfusion selected
      · decide)

example : fairCoin.conditionalProbability (fun outcome => !outcome)
        (fun _ => true) (by decide) ≤
      fairCoin.conditionalVariance (fun _ => true) coinPayoff /
        (fairCoin.conditionalVariance (fun _ => true) coinPayoff + 1 ^ 2) :=
  fairCoin.conditionalCantelli_lower_bound (fun outcome => !outcome)
    (fun _ => true) (by decide) coinPayoff 1 (by decide) (by
      intro item selected
      cases item
      · decide
      · exact Bool.noConfusion selected)

example : fairCoin.conditionalProbability (fun outcome => outcome)
          (fun _ => true) (by decide) = 1 / 2 ∧
      fairCoin.conditionalMean (fun _ => true) coinPayoff / 3 = 2 / 3 ∧
        fairCoin.conditionalVariance (fun _ => true) coinPayoff /
          (fairCoin.conditionalVariance (fun _ => true) coinPayoff + 1 ^ 2) =
            1 / 2 := by
  decide

example (atom : Weighted Bool) (member : atom ∈ fairCoin.atoms) :
    wholeCoinPartition.conditionalExpectation
          (fun outcome => coinNumber outcome * coinPayoff outcome)
          atom.item ^ 2 ≤
      wholeCoinPartition.conditionalExpectation
          (fun outcome => coinNumber outcome ^ 2) atom.item *
        wholeCoinPartition.conditionalExpectation
          (fun outcome => coinPayoff outcome ^ 2) atom.item :=
  wholeCoinPartition.conditionalExpectation_mul_sq_le
    coinNumber coinPayoff atom member

example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          fairCoin.conditionalMean event coinPayoff).sum =
      fairCoin.expectation coinPayoff :=
  positiveCoinPartition.total_expectation coinPayoff

example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          fairCoin.conditionalMean event coinPayoff).sum = 2 := by
  decide

def partitionCoinPayoff : Bool → Coordinate :=
  positiveCoinPartition.conditionalExpectation coinPayoff

def wholeCoinPayoff : Bool → Coordinate :=
  wholeCoinPartition.conditionalExpectation coinPayoff

example : (5 / 2 : Coordinate) * fairCoin.probability
      (unionEvents ([wholeCoinPayoff, coinPayoff].map
        (atLeastObservableEvent (5 / 2)))) ≤
    fairCoin.expectation coinPayoff := by
  apply fairCoin.twoStage_l1_maximal (5 / 2) (by decide)
  · intro atom member
    cases atom.item <;> decide
  · decide

example : (5 / 2 : Coordinate) * fairCoin.probability
      (unionEvents
        ([wholeCoinPartition.conditionalExpectation coinPayoff,
          coinPayoff].map (atLeastObservableEvent (5 / 2)))) ≤
    fairCoin.expectation coinPayoff :=
  fairCoin.conditionalExpectation_twoStage_l1_maximal
    (5 / 2) (by decide) wholeCoinPartition coinPayoff (by
      intro atom member
      cases atom.item <;> decide)

example : (5 / 2 : Coordinate) * fairCoin.probability
      (unionEvents
        ((coinFiltration.conditionalExpectationValues coinPayoff).map
          (atLeastObservableEvent (5 / 2)))) ≤
    fairCoin.expectation coinPayoff :=
  coinFiltration.conditionalExpectation_l1_maximal
    coinFiltrationCellwiseCompatible coinPayoff (5 / 2) (by decide) (by
      intro atom member
      cases atom.item <;> decide)

example : fairCoin.probability
      (unionEvents
        ((coinFiltration.conditionalExpectationValues coinPayoff).map
          (atLeastObservableEvent (5 / 2)))) = 1 / 2 ∧
    fairCoin.expectation coinPayoff = 2 := by
  decide

example : (5 : Coordinate) * fairCoin.probability
      (coinFiltration.conditionalSquareMaximumEvent coinPayoff 5) ≤
    fairCoin.expectation (fun outcome => coinPayoff outcome ^ 2) :=
  coinFiltration.conditionalExpectation_poweredL2_maximal
    coinFiltrationCellwiseCompatible coinPayoff 5 (by decide)

example : fairCoin.probability
        (coinFiltration.conditionalSquareMaximumEvent coinPayoff 5) = 1 / 2 ∧
      fairCoin.expectation (fun outcome => coinPayoff outcome ^ 2) = 5 := by
  decide

example : fairCoin.probability
      (unionEvents ([wholeCoinPayoff, coinPayoff].map
        (atLeastObservableEvent (5 / 2)))) = 1 / 2 ∧
    fairCoin.expectation coinPayoff = 2 := by
  decide

/-- The zero payoff is explicitly constant on the sole coarse coin cell. -/
def zeroCoinPayoffCellwise :
    PositiveEventPartition.CellwiseObservable wholeCoinPartition
      (fun _ : Bool => (0 : Coordinate)) where
  cellValue := fun _ => 0
  agrees := by
    intro event eventMember atom atomMember selected
    rfl

example : partitionCoinPayoff false = 1 ∧ partitionCoinPayoff true = 3 := by
  decide

example (outcome : Bool) :
    positiveCoinPartition.conditionalExpectation partitionCoinPayoff outcome =
      partitionCoinPayoff outcome :=
  positiveCoinPartition.conditionalExpectation_idempotent coinPayoff outcome

example (outcome : Bool) :
    wholeCoinPartition.conditionalExpectation partitionCoinPayoff outcome =
      wholeCoinPayoff outcome :=
  coinPartitionRefinesWhole.conditionalExpectation_tower coinPayoff outcome

example (outcome : Bool) :
    coinFiltration.coarsest.conditionalExpectation
        (positiveCoinPartition.conditionalExpectation coinPayoff) outcome =
      coinFiltration.coarsest.conditionalExpectation coinPayoff outcome :=
  coinFiltration.conditionalExpectation_tower coinPayoff outcome

example : fairCoin.expectation
      (positiveCoinPartition.conditionalExpectation coinPayoff) =
    fairCoin.expectation
      (coinFiltration.canonicalMartingale coinPayoff).initialValue :=
  (coinFiltration.canonicalMartingale coinPayoff)
    |>.expectation_terminal_eq_initial

example : ((coinFiltration.canonicalMartingale coinPayoff)
    |>.expectedQuadraticVariation) = 1 := by
  decide

example : fairCoin.poweredL2 partitionCoinPayoff =
    fairCoin.poweredL2 wholeCoinPayoff + 1 := by
  have identity := (coinFiltration.canonicalMartingale coinPayoff)
    |>.poweredL2_terminal_eq_initial_add_expectedQuadraticVariation
  have variation : ((coinFiltration.canonicalMartingale coinPayoff)
      |>.expectedQuadraticVariation) = 1 := by
    decide
  rw [variation] at identity
  simpa only [partitionCoinPayoff, wholeCoinPayoff,
    FiniteFiltration.canonicalMartingale_initialValue, coinFiltration,
    FiniteFiltration.coarsest] using identity

example : fairCoin.variance partitionCoinPayoff =
    fairCoin.variance wholeCoinPayoff + 1 := by
  have identity := (coinFiltration.canonicalMartingale coinPayoff)
    |>.variance_terminal_eq_initial_add_expectedQuadraticVariation
  have variation : ((coinFiltration.canonicalMartingale coinPayoff)
      |>.expectedQuadraticVariation) = 1 := by
    decide
  rw [variation] at identity
  simpa only [partitionCoinPayoff, wholeCoinPayoff,
    FiniteFiltration.canonicalMartingale_initialValue, coinFiltration,
    FiniteFiltration.coarsest] using identity

example : fairCoin.variance wholeCoinPayoff ≤
    fairCoin.variance partitionCoinPayoff := by
  simpa only [partitionCoinPayoff, wholeCoinPayoff,
    FiniteFiltration.canonicalMartingale_initialValue, coinFiltration,
    FiniteFiltration.coarsest] using
    (coinFiltration.canonicalMartingale coinPayoff)
      |>.variance_initial_le_terminal

example (outcome : Bool) :
    (((coinFiltration.canonicalMartingale coinPayoff).stopImmediately)
      |>.stoppedValue) outcome = wholeCoinPayoff outcome := by
  simpa only [wholeCoinPayoff,
    FiniteFiltration.canonicalMartingale_initialValue, coinFiltration,
    FiniteFiltration.coarsest] using
      FiniteFiltration.Martingale.StoppingStrategy.stoppedValue_stopImmediately
        (coinFiltration.canonicalMartingale coinPayoff) outcome

example (outcome : Bool) :
    (((coinFiltration.canonicalMartingale coinPayoff).continueToEnd)
      |>.stoppedValue) outcome = partitionCoinPayoff outcome := by
  simpa only [partitionCoinPayoff] using
    FiniteFiltration.Martingale.StoppingStrategy.stoppedValue_continueToEnd
      (coinFiltration.canonicalMartingale coinPayoff) outcome

example : fairCoin.expectation
      ((coinFiltration.canonicalMartingale coinPayoff).stopImmediately
        |>.stoppedValue) = fairCoin.expectation wholeCoinPayoff := by
  simpa only [wholeCoinPayoff,
    FiniteFiltration.canonicalMartingale_initialValue, coinFiltration,
    FiniteFiltration.coarsest] using
      (coinFiltration.canonicalMartingale coinPayoff).stopImmediately
        |>.expectation_stoppedValue_eq_initial

example : fairCoin.variance wholeCoinPayoff ≤
    fairCoin.variance partitionCoinPayoff :=
  coinPartitionRefinesWhole.variance_conditionalExpectation_mono coinPayoff

example : wholeCoinPayoff false = 2 ∧ wholeCoinPayoff true = 2 := by
  decide

example : fairCoin.poweredL2Distance coinPayoff (fun _ => 0) =
    fairCoin.poweredL2Distance coinPayoff wholeCoinPayoff +
      fairCoin.poweredL2Distance wholeCoinPayoff (fun _ => 0) :=
  wholeCoinPartition.poweredL2Distance_pythagorean coinPayoff
    (fun _ => 0) zeroCoinPayoffCellwise

example : fairCoin.poweredL2Distance coinPayoff wholeCoinPayoff ≤
    fairCoin.poweredL2Distance coinPayoff (fun _ => 0) :=
  wholeCoinPartition.poweredL2Distance_conditionalExpectation_le coinPayoff
    (fun _ => 0) zeroCoinPayoffCellwise

example : fairCoin.poweredL2Distance coinPayoff (fun _ => 0) = 5 ∧
    fairCoin.poweredL2Distance coinPayoff wholeCoinPayoff = 1 ∧
      fairCoin.poweredL2Distance wholeCoinPayoff (fun _ => 0) = 4 := by
  decide

example (candidate : Bool → Coordinate)
    (cellwise : PositiveEventPartition.CellwiseObservable
      wholeCoinPartition candidate)
    (preserves : ∀ event, event ∈ wholeCoinPartition.events →
      fairCoin.eventIntegral event candidate =
        fairCoin.eventIntegral event coinPayoff) :
    ∀ atom, atom ∈ fairCoin.atoms →
      candidate atom.item = wholeCoinPayoff atom.item :=
  wholeCoinPartition.candidate_eq_conditionalExpectation_on_atoms
    coinPayoff candidate cellwise preserves

example : fairCoin.variance wholeCoinPayoff ≤
    fairCoin.variance coinPayoff :=
  wholeCoinPartition.variance_conditionalExpectation_le coinPayoff

example : fairCoin.poweredL1
      (wholeCoinPartition.conditionalExpectation fun outcome =>
        coinPayoff outcome - 2) ≤
    fairCoin.poweredL1 (fun outcome => coinPayoff outcome - 2) :=
  wholeCoinPartition.poweredL1_conditionalExpectation_le
    (fun outcome => coinPayoff outcome - 2)

example : fairCoin.poweredL1
      (wholeCoinPartition.conditionalExpectation fun outcome =>
        coinPayoff outcome - 2) = 0 ∧
    fairCoin.poweredL1 (fun outcome => coinPayoff outcome - 2) = 1 := by
  decide

example : fairCoin.l1Distance
      (wholeCoinPartition.conditionalExpectation coinNumber)
      (wholeCoinPartition.conditionalExpectation reverseCoinNumber) ≤
    fairCoin.l1Distance coinNumber reverseCoinNumber :=
  wholeCoinPartition.l1Distance_conditionalExpectation_le
    coinNumber reverseCoinNumber

example : fairCoin.l1Distance
      (wholeCoinPartition.conditionalExpectation coinNumber)
      (wholeCoinPartition.conditionalExpectation reverseCoinNumber) = 0 ∧
    fairCoin.l1Distance coinNumber reverseCoinNumber = 1 := by
  decide

example (atom : Weighted Bool) (member : atom ∈ fairCoin.atoms) :
    0 ≤ wholeCoinPartition.conditionalExpectation coinNumber atom.item :=
  wholeCoinPartition.conditionalExpectation_nonneg_on_atoms coinNumber
    (by
      intro candidate candidateMember
      cases candidate.item <;> decide)
    atom member

example (atom : Weighted Bool) (member : atom ∈ fairCoin.atoms) :
    wholeCoinPartition.conditionalExpectation coinNumber atom.item ≤
      wholeCoinPartition.conditionalExpectation coinPayoff atom.item :=
  wholeCoinPartition.conditionalExpectation_mono_on_atoms
    coinNumber coinPayoff (by
      intro candidate candidateMember
      cases candidate.item <;> decide)
    atom member

example : fairCoin.essentialMaximumMagnitude
      (wholeCoinPartition.conditionalExpectation coinNumber) ≤
    fairCoin.essentialMaximumMagnitude coinNumber :=
  wholeCoinPartition.essentialMaximumMagnitude_conditionalExpectation_le
    coinNumber

example : fairCoin.essentialMaximumMagnitude
      (wholeCoinPartition.conditionalExpectation coinNumber) = 1 / 2 ∧
    fairCoin.essentialMaximumMagnitude coinNumber = 1 := by
  decide

example : fairCoin.essentialMaximumDistance
      (wholeCoinPartition.conditionalExpectation coinNumber)
      (wholeCoinPartition.conditionalExpectation reverseCoinNumber) ≤
    fairCoin.essentialMaximumDistance coinNumber reverseCoinNumber :=
  wholeCoinPartition.essentialMaximumDistance_conditionalExpectation_le
    coinNumber reverseCoinNumber

example : fairCoin.essentialMaximumDistance
      (wholeCoinPartition.conditionalExpectation coinNumber)
      (wholeCoinPartition.conditionalExpectation reverseCoinNumber) = 0 ∧
    fairCoin.essentialMaximumDistance coinNumber reverseCoinNumber = 1 := by
  decide

example : fairCoin.variance wholeCoinPayoff = 0 ∧
    fairCoin.variance coinPayoff = 1 := by
  decide

example (outcome : Bool) :
    positiveCoinPartition.conditionalExpectation
        (fun candidate => coinPayoff candidate + coinPayoff candidate) outcome =
      partitionCoinPayoff outcome + partitionCoinPayoff outcome :=
  positiveCoinPartition.conditionalExpectation_add coinPayoff coinPayoff
    outcome

example : fairCoin.expectation partitionCoinPayoff =
    fairCoin.expectation coinPayoff :=
  positiveCoinPartition.expectation_conditionalExpectation coinPayoff

example : fairCoin.eventIntegral (fun outcome => outcome)
      partitionCoinPayoff =
    fairCoin.eventIntegral (fun outcome => outcome) coinPayoff := by
  apply positiveCoinPartition.eventIntegral_conditionalExpectation
  change (fun outcome : Bool => outcome) ∈
    [(fun outcome => !outcome), (fun outcome => outcome)]
  exact List.mem_cons_of_mem _ List.mem_cons_self

example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalVariance event coinPayoff +
            (fairCoin.conditionalMean event coinPayoff -
              fairCoin.expectation coinPayoff) ^ 2)).sum =
      fairCoin.variance coinPayoff :=
  positiveCoinPartition.total_variance coinPayoff

example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          fairCoin.conditionalVariance event coinPayoff).sum +
      fairCoin.variance
        (positiveCoinPartition.conditionalExpectation coinPayoff) =
      fairCoin.variance coinPayoff :=
  positiveCoinPartition.total_variance_decomposition coinPayoff

example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalVariance event coinPayoff +
            fairCoin.conditionalMean event coinPayoff ^ 2)).sum =
      fairCoin.expectation (fun outcome => coinPayoff outcome ^ 2) :=
  positiveCoinPartition.total_secondMoment coinPayoff

example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalVariance event coinPayoff +
            fairCoin.conditionalMean event coinPayoff ^ 2)).sum = 5 := by
  decide

example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalCovariance event
              coinNumber reverseCoinNumber +
            (fairCoin.conditionalMean event coinNumber -
              fairCoin.expectation coinNumber) *
            (fairCoin.conditionalMean event reverseCoinNumber -
              fairCoin.expectation reverseCoinNumber))).sum =
      fairCoin.covariance coinNumber reverseCoinNumber :=
  positiveCoinPartition.total_covariance coinNumber reverseCoinNumber

example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          fairCoin.conditionalCovariance event
            coinNumber reverseCoinNumber).sum +
      fairCoin.covariance
        (positiveCoinPartition.conditionalExpectation coinNumber)
        (positiveCoinPartition.conditionalExpectation reverseCoinNumber) =
      fairCoin.covariance coinNumber reverseCoinNumber :=
  positiveCoinPartition.total_covariance_decomposition
    coinNumber reverseCoinNumber

example : fairCoin.covariance
      (positiveCoinPartition.conditionalExpectation coinNumber)
      (positiveCoinPartition.conditionalExpectation reverseCoinNumber) =
    -1 / 4 := by
  decide

example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalCovariance event
              coinNumber reverseCoinNumber +
            (fairCoin.conditionalMean event coinNumber -
              fairCoin.expectation coinNumber) *
            (fairCoin.conditionalMean event reverseCoinNumber -
              fairCoin.expectation reverseCoinNumber))).sum = -1 / 4 := by
  decide

example :
    (positiveCoinPartition.events.map fun event =>
        fairCoin.probability event *
          (fairCoin.conditionalVariance event coinPayoff +
            (fairCoin.conditionalMean event coinPayoff -
              fairCoin.expectation coinPayoff) ^ 2)).sum = 1 := by
  decide

example (left right : Bool → Coordinate) (epsilon : Coordinate)
    (bounded : SymmetricErrorOn fairCoin.atoms
      (fun _ => epsilon) left right) :
    fairCoin.expectation right - fairCoin.expectation left ≤ epsilon ∧
      fairCoin.expectation left - fairCoin.expectation right ≤ epsilon :=
  fairCoin.expectation_close_of_uniform epsilon left right bounded

def fairDie : Distribution Nat where
  atoms :=
    [⟨1, 1 / 6, by decide⟩,
      ⟨2, 1 / 6, by decide⟩,
      ⟨3, 1 / 6, by decide⟩,
      ⟨4, 1 / 6, by decide⟩,
      ⟨5, 1 / 6, by decide⟩,
      ⟨6, 1 / 6, by decide⟩]
  total_one := by decide

def rationalFairDie : Distribution Coordinate :=
  fairDie.map fun face => (face : Coordinate)

theorem fairDie_coordinate_expectation :
    fairDie.expectation (fun face => (face : Coordinate)) = 7 / 2 := by
  decide

theorem fairDie_coordinate_secondMoment :
    fairDie.expectation (fun face => (face : Coordinate) ^ 2) = 91 / 6 := by
  change
    (1 / 6 : Coordinate) * 1 ^ 2 +
      ((1 / 6 : Coordinate) * 2 ^ 2 +
      ((1 / 6 : Coordinate) * 3 ^ 2 +
      ((1 / 6 : Coordinate) * 4 ^ 2 +
      ((1 / 6 : Coordinate) * 5 ^ 2 +
      ((1 / 6 : Coordinate) * 6 ^ 2 + 0))))) = 91 / 6
  rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
    RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
  ring1

theorem fairDie_coordinate_variance :
    fairDie.variance (fun face => (face : Coordinate)) = 35 / 12 := by
  rw [fairDie.variance_eq_secondMoment_sub_sq,
    fairDie_coordinate_secondMoment, fairDie_coordinate_expectation]
  rw [pow_two, RFAP.ConstructiveFraction.div_mul_div_direct,
    RFAP.ConstructiveFraction.div_sub_div_direct]
  · apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
    · exact RFAP.ConstructiveFraction.mul_ne_zero_direct
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 6) (by decide)).ne'
        (RFAP.ConstructiveFraction.mul_ne_zero_direct
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 2) (by decide)).ne'
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 2) (by decide)).ne')
    · exact (RFAP.ConstructiveFraction.natCast_pos_direct
        (n := 12) (by decide)).ne'
    · ring1
  · exact (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 6) (by decide)).ne'
  · exact (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 4) (by decide)).ne'

theorem rationalFairDie_coordinate_variance :
    rationalFairDie.variance (fun value => value) = 35 / 12 := by
  unfold rationalFairDie
  rw [Distribution.map_variance]
  exact fairDie_coordinate_variance

example : ∃ face : Nat, 0 < fairDie.probability (atomEvent face) :=
  fairDie.exists_positive_singleton

example : ¬fairDie.toFiniteContent.Atomless :=
  fairDie.not_atomless

example : fairDie.expectation (fun face => (face : Coordinate)) =
    fairDie.natTailProbabilitySum (fun face => face) 6 :=
  fairDie.expectation_nat_eq_natTailProbabilitySum_of_bounded
    (fun face => face) 6 (by decide)

example : fairDie.natTailProbabilitySum (fun face => face) 6 = 7 / 2 := by
  decide

example : rationalFairDie.cumulative 3 = 1 / 2 := by
  decide

example : rationalFairDie.cumulative 0 = 0 :=
  rationalFairDie.cumulative_eq_zero_of_cut_lt_all_atoms 0 (by decide)

example : rationalFairDie.cumulative 7 = 1 :=
  rationalFairDie.cumulative_eq_one_of_all_atoms_le_cut 7 (by decide)

example : rationalFairDie.cumulative 3 =
    rationalFairDie.cumulative (7 / 2) :=
  rationalFairDie.cumulative_eq_of_atom_gap (by decide) (by decide)

example : rationalFairDie.median = 3 := by
  decide

example : rationalFairDie.lowerQuantile (3 / 4) (by decide) (by decide) = 5 := by
  decide

example : rationalFairDie.lowerQuantile (3 / 4) (by decide) (by decide) = 5 :=
  rationalFairDie.lowerQuantile_eq_of_atom_gap_crossing
    (3 / 4) (by decide) (by decide) 4 5
      (by decide) (by decide) (by decide)

example :
    4 < rationalFairDie.lowerQuantile (3 / 4) (by decide) (by decide) ∧
      rationalFairDie.lowerQuantile (3 / 4) (by decide) (by decide) ≤ 5 :=
  rationalFairDie.lowerQuantile_mem_bracket_of_totalVariation_margins
    rationalFairDie (3 / 4) (by decide) (by decide) 4 5
      (by decide) (by decide)

example : rationalFairDie.probability
      (strictlyBelowEvent rationalFairDie.median) < 1 / 2 :=
  rationalFairDie.probability_strictlyBelow_median_lt_half

example : 1 / 2 < rationalFairDie.probability
      (atLeastCoordinateEvent rationalFairDie.median) :=
  rationalFairDie.half_lt_probability_atLeast_median

example : rationalFairDie.absoluteDeviation rationalFairDie.median = 3 / 2 := by
  decide

example : rationalFairDie.absoluteDeviation rationalFairDie.median ≤
    rationalFairDie.absoluteDeviation 7 :=
  rationalFairDie.absoluteDeviation_median_le 7

example : rationalFairDie.absoluteDeviation 7 = 7 / 2 := by
  decide

example :
    (rationalFairDie.quantileCertificate
        (1 / 2) (by decide) (by decide)).threshold ≤
      (rationalFairDie.quantileCertificate
        (3 / 4) (by decide) (by decide)).threshold :=
  QuantileCertificate.threshold_mono
    (rationalFairDie.quantileCertificate (1 / 2) (by decide) (by decide))
    (rationalFairDie.quantileCertificate (3 / 4) (by decide) (by decide))
    (by decide)

example : rationalFairDie.probability
    (openClosedIntervalEvent 2 5) = 1 / 2 := by
  decide

example : rationalFairDie.probability
      (openClosedIntervalEvent 2 5) =
    rationalFairDie.cumulative 5 - rationalFairDie.cumulative 2 :=
  rationalFairDie.probability_openClosedInterval (by decide)

example : rationalFairDie.probability
      (fun value => decide (value = 5)) =
    rationalFairDie.cumulative 5 - rationalFairDie.cumulative 4 :=
  rationalFairDie.probability_eqValue_eq_cumulative_sub_of_atom_gap
    (by decide) (by decide)

example : (rationalFairDie.cumulativeJumpCertificate 5).lower = 4 := by
  decide

example : rationalFairDie.atomMass 5 =
    rationalFairDie.cumulative 5 -
      rationalFairDie.cumulative
        (rationalFairDie.cumulativeJumpCertificate 5).lower :=
  rationalFairDie.atomMass_eq_cumulative_sub_jumpCertificate 5

def twoDieSum : Distribution Coordinate :=
  rationalFairDie.convolve rationalFairDie

example : Distribution.EvaluationEquivalent
    (coinNumberLaw.convolve rationalFairDie)
    (rationalFairDie.convolve coinNumberLaw) :=
  coinNumberLaw.convolve_comm_evaluationEquivalent rationalFairDie

example (noise : Distribution Coordinate) :
    (noise.convolve coinNumberLaw).finiteKolmogorovDistance
        (noise.convolve quarterCoinNumberLaw) ≤ 1 / 4 := by
  calc
    (noise.convolve coinNumberLaw).finiteKolmogorovDistance
          (noise.convolve quarterCoinNumberLaw) ≤
        coinNumberLaw.finiteKolmogorovDistance quarterCoinNumberLaw :=
      Distribution.finiteKolmogorovDistance_convolve_left_le
        noise coinNumberLaw quarterCoinNumberLaw
    _ = 1 / 4 :=
      coinNumberLaw_finiteKolmogorovDistance_quarterCoinNumberLaw

example (noise : Distribution Coordinate) :
    (coinNumberLaw.convolve noise).finiteKolmogorovDistance
        (quarterCoinNumberLaw.convolve noise) ≤ 1 / 4 := by
  calc
    (coinNumberLaw.convolve noise).finiteKolmogorovDistance
          (quarterCoinNumberLaw.convolve noise) ≤
        coinNumberLaw.finiteKolmogorovDistance quarterCoinNumberLaw :=
      Distribution.finiteKolmogorovDistance_convolve_right_le
        coinNumberLaw quarterCoinNumberLaw noise
    _ = 1 / 4 :=
      coinNumberLaw_finiteKolmogorovDistance_quarterCoinNumberLaw

example : twoDieSum.cumulative 7 = 7 / 12 := by
  unfold twoDieSum
  rw [rationalFairDie.cumulative_convolve rationalFairDie 7]
  decide

example : twoDieSum.cumulative 7 =
    rationalFairDie.expectation (fun first =>
      rationalFairDie.cumulative (7 - first)) :=
  rationalFairDie.cumulative_convolve rationalFairDie 7

def equalsSeven (value : Coordinate) : Bool := decide (value = 7)

example : twoDieSum.probability equalsSeven = 1 / 6 := by
  unfold twoDieSum
  rw [rationalFairDie.convolve_probability rationalFairDie equalsSeven]
  decide

example : twoDieSum.expectation (fun value => value) = 7 := by
  unfold twoDieSum
  rw [rationalFairDie.convolve_expectation rationalFairDie]
  decide

example : twoDieSum.expectation (fun value => value) =
    rationalFairDie.expectation (fun value => value) +
      rationalFairDie.expectation (fun value => value) :=
  rationalFairDie.convolve_expectation rationalFairDie

example : twoDieSum.variance (fun value => value) = 35 / 6 := by
  unfold twoDieSum
  rw [rationalFairDie.convolve_variance rationalFairDie,
    rationalFairDie_coordinate_variance]
  rw [← two_mul]
  calc
    2 * (35 / 12 : Coordinate) = 70 / 12 := by
      rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
        RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
      ring1
    _ = 35 / 6 := by
      apply RFAP.ConstructiveFraction.div_eq_div_of_cross_mul
      · exact (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 12) (by decide)).ne'
      · exact (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 6) (by decide)).ne'
      · ring1

example : twoDieSum.variance (fun value => value) =
    rationalFairDie.variance (fun value => value) +
      rationalFairDie.variance (fun value => value) :=
  rationalFairDie.convolve_variance rationalFairDie

def evenFace (face : Nat) : Bool :=
  face % 2 == 0

example : fairDie.probability evenFace = 1 / 2 := by
  decide

def lowFace (face : Nat) : Bool := face == 1

def middleFace (face : Nat) : Bool := face == 2

example : fairDie.probability (unionEvents [lowFace, middleFace]) = 1 / 3 := by
  decide

example : fairDie.probability (unionEvents [lowFace, middleFace]) =
    fairDie.probability lowFace + fairDie.probability middleFace := by
  apply fairDie.probability_unionEvents_of_disjoint
  constructor
  · intro atom member overlap
    simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [lowFace, middleFace, unionEvents, unionEvent]
  · constructor
    · intro atom member overlap
      simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [middleFace, unionEvents]
    · trivial

def highFace (face : Nat) : Bool :=
  3 < face

theorem highFacePositive : 0 < fairDie.probability highFace := by
  decide

example : fairDie.conditionalProbability evenFace highFace
    highFacePositive = 2 / 3 := by
  decide

example : (fairDie.conditioned highFace highFacePositive).probability
    highFace = 1 :=
  fairDie.conditioned_probability_condition highFace highFacePositive

example : fairDie.expectation (fun face => (face : Coordinate)) = 7 / 2 := by
  exact fairDie_coordinate_expectation

example : integralBound
      (fairDie.expectationCells fun face => (face : Coordinate)) =
    Bound.exact (7 / 2) := by
  rw [fairDie.integralBound_expectationCells]
  apply Bound.ext <;> decide

example : fairDie.variance (fun face => (face : Coordinate)) = 35 / 12 := by
  exact fairDie_coordinate_variance

example : fairDie.expectation (fun face => (face : Coordinate)) ^ 2 ≤
    fairDie.expectation (fun face => (face : Coordinate) ^ 2) :=
  fairDie.expectation_sq_le_secondMoment
    (fun face => (face : Coordinate))

example :
    (1 - (1 / 2 : Coordinate)) ^ 2 *
          fairDie.expectation (fun face => (face : Coordinate)) ^ 2 /
        fairDie.expectation (fun face => (face : Coordinate) ^ 2) ≤
      fairDie.probability (fairDie.aboveFractionOfMeanEvent
        (fun face => (face : Coordinate)) (1 / 2)) := by
  apply fairDie.paleyZygmund_bound (fun face => (face : Coordinate))
    (1 / 2) (by decide) (by decide)
  · intro atom member
    simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · decide

example : fairCoin.covariance coinPayoff coinPayoff =
    fairCoin.variance coinPayoff :=
  fairCoin.covariance_self coinPayoff

example : fairCoin.variance (fun outcome => coinPayoff outcome + 5) =
    fairCoin.variance coinPayoff :=
  fairCoin.variance_add_constant coinPayoff 5

example : fairDie.probability highFace ≤
    fairDie.expectation (fun face => (face : Coordinate)) / 4 := by
  apply fairDie.markov_bound highFace (fun face => (face : Coordinate)) 4
    (by decide)
  · intro atom member
    simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · intro atom member selected
    simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp_all [highFace] <;> decide

example : fairDie.probability highFace ≤
    fairDie.variance (fun face => (face : Coordinate)) /
      (fairDie.variance (fun face => (face : Coordinate)) + (1 / 2) ^ 2) := by
  apply fairDie.cantelli_bound highFace
    (fun face => (face : Coordinate)) (1 / 2) (by decide)
  intro atom member selected
  simp only [fairDie, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp_all [highFace] <;> decide

example : (eventBound (fairDie.eventFrontier evenFace)).width = 0 :=
  fairDie.eventFrontier_bound_exact evenFace

example (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((fairDie.exactEventProcess evenFace).toBoundProcess.bound ()).width <
      epsilon := by
  simpa only [EventProcess.toBoundProcess,
    Distribution.exactEventProcess] using
      (fairDie.exactEventProcess evenFace).request_width_lt () epsilon positive

example (request : AccuracyRequest) (requests : List AccuracyRequest)
    (member : request ∈ requests) :
    unresolvedWeight ((fairDie.exactEventProcess evenFace).frontier
      ((fairDie.exactEventProcess evenFace).runRequests () requests)) <
        request.tolerance :=
  (fairDie.exactEventProcess evenFace).runRequests_unresolved_lt_of_mem
    () requests request member

/-! ## Bounded finite stochastic processes -/

def toggleTransition (state : Bool) : Distribution Bool :=
  Distribution.pure (!state)

def startsFalse : Distribution Bool :=
  Distribution.pure false

def stayTransition (state : Bool) : Distribution Bool :=
  Distribution.pure state

def collapseToFalseTransition (_ : Bool) : Distribution Bool :=
  Distribution.pure false

/-- From `false`, toss a fresh fair coin; from `true`, stay at `true`. -/
def revealOrRandomTransition (state : Bool) : Distribution Bool :=
  if state then Distribution.pure true else fairCoin

example : (fairCoin.bind revealOrRandomTransition).poweredL2 coinPayoff =
    fairCoin.expectation (fun state =>
      (revealOrRandomTransition state).poweredL2 coinPayoff) :=
  fairCoin.bind_poweredL2 revealOrRandomTransition coinPayoff

example : (fairCoin.bind revealOrRandomTransition).poweredL2 coinPayoff = 7 ∧
    fairCoin.expectation (fun state =>
      (revealOrRandomTransition state).poweredL2 coinPayoff) = 7 := by
  decide

example : (fairCoin.bind revealOrRandomTransition).poweredLpDistance 3
      coinNumber reverseCoinNumber =
    fairCoin.expectation (fun state =>
      (revealOrRandomTransition state).poweredLpDistance 3
        coinNumber reverseCoinNumber) :=
  fairCoin.bind_poweredLpDistance revealOrRandomTransition 3
    coinNumber reverseCoinNumber

theorem collapseToFalse_superharmonic (state : Bool) :
    (collapseToFalseTransition state).expectation coinNumber ≤
      coinNumber state := by
  cases state <;> decide

example : (fairCoin.bind Distribution.pure).probability
    (fun outcome => outcome) = fairCoin.probability (fun outcome => outcome) :=
  fairCoin.bind_pure_probability (fun outcome => outcome)

example : ((Distribution.pure false).bind toggleTransition).probability
    (fun state => state) = (toggleTransition false).probability
      (fun state => state) :=
  Distribution.pure_bind_probability false toggleTransition
    (fun state => state)

example {α β γ : Type} (source : Distribution α)
    (first : α → Distribution β) (second : β → Distribution γ)
    (event : γ → Bool) :
    ((source.bind first).bind second).probability event =
      (source.bind fun item => (first item).bind second).probability event :=
  source.bind_bind_probability first second event

example : Distribution.EvaluationEquivalent
    ((fairCoin.map fun outcome => !outcome).map fun outcome => !outcome)
    (fairCoin.map fun outcome => outcome) :=
  fairCoin.map_map_evaluationEquivalent
    (fun outcome => !outcome) (fun outcome => !outcome)

example : Distribution.EvaluationEquivalent
    ((Distribution.pure false).mixture (Distribution.pure true)
      mostlyFalseWeight)
    ((Distribution.pure true).mixture (Distribution.pure false)
      mostlyFalseWeight.swap) :=
  (Distribution.pure false).mixture_swap_evaluationEquivalent
    (Distribution.pure true) mostlyFalseWeight

example : (fairCoin.bind revealOrRandomTransition).variance coinNumber =
    fairCoin.expectation (fun state =>
        (revealOrRandomTransition state).variance coinNumber) +
      fairCoin.variance (fun state =>
        (revealOrRandomTransition state).expectation coinNumber) :=
  fairCoin.bind_variance revealOrRandomTransition coinNumber

example : fairCoin.expectation (fun state =>
    (revealOrRandomTransition state).variance coinNumber) = 1 / 8 := by
  decide

example : fairCoin.variance (fun state =>
    (revealOrRandomTransition state).expectation coinNumber) = 1 / 16 := by
  decide

example : (fairCoin.bind revealOrRandomTransition).variance coinNumber =
    3 / 16 := by
  decide

example : (fairCoin.bind revealOrRandomTransition).enclosedExpectation
      coarseCoinRange =
    fairCoin.enclosedExpectation (fun state =>
      (revealOrRandomTransition state).enclosedExpectation
        coarseCoinRange) :=
  fairCoin.enclosedExpectation_bind revealOrRandomTransition
    coarseCoinRange

example : ((fairCoin.bind revealOrRandomTransition).enclosedExpectation
      coarseCoinRange).width =
    fairCoin.expectation (fun state =>
      ((revealOrRandomTransition state).enclosedExpectation
        coarseCoinRange).width) :=
  fairCoin.enclosedExpectation_bind_width revealOrRandomTransition
    coarseCoinRange

example : ((Distribution.pure false).mixture
      (Distribution.pure true) mostlyFalseWeight).enclosedExpectation
        coarseCoinRange =
    (((Distribution.pure false).enclosedExpectation coarseCoinRange).scale
      mostlyFalseWeight.coefficient mostlyFalseWeight.nonnegative).add
    (((Distribution.pure true).enclosedExpectation coarseCoinRange).scale
      mostlyFalseWeight.complement
      mostlyFalseWeight.complement_nonnegative) :=
  (Distribution.pure false).enclosedExpectation_mixture
    (Distribution.pure true) mostlyFalseWeight coarseCoinRange

example :
    (fairCoin.bind revealOrRandomTransition).covariance
        coinNumber reverseCoinNumber =
      fairCoin.expectation (fun state =>
          (revealOrRandomTransition state).covariance
            coinNumber reverseCoinNumber) +
        fairCoin.covariance
          (fun state =>
            (revealOrRandomTransition state).expectation coinNumber)
          (fun state =>
            (revealOrRandomTransition state).expectation
              reverseCoinNumber) :=
  fairCoin.bind_covariance revealOrRandomTransition
    coinNumber reverseCoinNumber

example : (Distribution.iterate toggleTransition 3 startsFalse).probability
    (fun state => state) = 1 := by
  decide

example : (Distribution.iterate toggleTransition 4 startsFalse).probability
    (fun state => state) = 0 := by
  decide

example (count : Nat) :
    (Distribution.iterate collapseToFalseTransition count fairCoin).expectation
        coinNumber ≤ fairCoin.expectation coinNumber :=
  Distribution.iterate_expectation_le_of_superharmonic
    collapseToFalseTransition coinNumber collapseToFalse_superharmonic
      count fairCoin

example (event : Bool → Bool) (count : Nat) :
    (Distribution.iterate stayTransition count fairCoin).probability event =
      fairCoin.probability event := by
  apply Distribution.iterate_probability_of_harmonic_event
  intro item
  exact Distribution.pure_probability item event

def twoCoins : Distribution (Bool × Bool) :=
  fairCoin.product fairCoin

def twoCoinHeadEvents : List (Bool × Bool → Bool) :=
  [fun outcome => outcome.1, fun outcome => outcome.2]

theorem twoCoinHeadEvents_pairwiseIndependent :
    twoCoins.PairwiseIndependentEventList twoCoinHeadEvents := by
  unfold twoCoinHeadEvents Distribution.PairwiseIndependentEventList
  constructor
  · intro candidate member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst candidate
    exact fairCoin.product_independentEvents_coordinates fairCoin
      (fun outcome => outcome) (fun outcome => outcome)
  · constructor
    · intro candidate member
      cases member
    · trivial

example : twoCoins.expectation (fun outcome =>
      (pairOccurrenceCount twoCoinHeadEvents outcome : Coordinate)) =
    twoCoins.pairIntersectionProbabilitySum twoCoinHeadEvents :=
  twoCoins.expectation_pairOccurrenceCount twoCoinHeadEvents

example : (twoCoinHeadEvents.map twoCoins.probability).sum -
        twoCoins.pairIntersectionProbabilitySum twoCoinHeadEvents ≤
      twoCoins.probability (unionEvents twoCoinHeadEvents) :=
  twoCoins.probability_unionEvents_lower_bonferroni_two twoCoinHeadEvents

example : (twoCoinHeadEvents.map twoCoins.probability).sum -
          twoCoins.pairIntersectionProbabilitySum twoCoinHeadEvents = 3 / 4 ∧
      twoCoins.probability (unionEvents twoCoinHeadEvents) = 3 / 4 := by
  decide

example : twoCoins.variance (fun outcome =>
      (occurrenceCount twoCoinHeadEvents outcome : Coordinate)) =
    (twoCoinHeadEvents.map fun event => twoCoins.probability event *
      (1 - twoCoins.probability event)).sum :=
  twoCoins.variance_occurrenceCount_of_pairwiseIndependentEventList
    twoCoinHeadEvents twoCoinHeadEvents_pairwiseIndependent

example : twoCoins.variance (fun outcome =>
    (occurrenceCount twoCoinHeadEvents outcome : Coordinate)) = 1 / 2 := by
  rw [twoCoins.variance_occurrenceCount_of_pairwiseIndependentEventList
    twoCoinHeadEvents twoCoinHeadEvents_pairwiseIndependent]
  decide

example : twoCoins.expectation (fun outcome =>
        (occurrenceCount twoCoinHeadEvents outcome : Coordinate) ^ 2) ≤
      (twoCoinHeadEvents.map twoCoins.probability).sum +
        (twoCoinHeadEvents.map twoCoins.probability).sum ^ 2 :=
  twoCoins
    |>.expectation_occurrenceCount_sq_le_sum_add_sq_of_pairwiseIndependent
      twoCoinHeadEvents twoCoinHeadEvents_pairwiseIndependent

example : (twoCoinHeadEvents.map twoCoins.probability).sum /
        (1 + (twoCoinHeadEvents.map twoCoins.probability).sum) ≤
      twoCoins.probability (unionEvents twoCoinHeadEvents) :=
  twoCoins.pairwiseIndependent_union_lower_bound twoCoinHeadEvents
    twoCoinHeadEvents_pairwiseIndependent (by decide)

example : (twoCoinHeadEvents.map twoCoins.probability).sum /
          (1 + (twoCoinHeadEvents.map twoCoins.probability).sum) = 1 / 2 ∧
      twoCoins.probability (unionEvents twoCoinHeadEvents) = 3 / 4 := by
  decide

def firstCoinSimpleObservable : SimpleObservable
    (boolEventAlgebra.comap fun outcome : Bool × Bool => outcome.1) :=
  coinSimpleObservable.map fun term =>
    { event := term.event, coefficient := term.coefficient }

def secondCoinSimpleObservable : SimpleObservable
    (boolEventAlgebra.comap fun outcome : Bool × Bool => outcome.2) :=
  coinSimpleObservable.map fun term =>
    { event := term.event, coefficient := term.coefficient }

def exactlyOneTrue (outcome : Bool × Bool) : Bool :=
  (outcome.1 && !outcome.2) || (!outcome.1 && outcome.2)

example : twoCoins.probability (fun outcome => outcome.1 && outcome.2) =
    1 / 4 := by
  decide

example : twoCoins.probability (fun outcome => outcome.1 && outcome.2) =
    fairCoin.probability (fun outcome => outcome) *
      fairCoin.probability (fun outcome => outcome) :=
  Distribution.product_probability_rectangle fairCoin fairCoin
    (fun outcome => outcome) (fun outcome => outcome)

example : twoCoins.IndependentEvents
    (fun outcome => outcome.1) (fun outcome => outcome.2) :=
  fairCoin.product_independentEvents_coordinates fairCoin
    (fun outcome => outcome) (fun outcome => outcome)

example : twoCoins.IndependentEventAlgebras
    (boolEventAlgebra.comap fun outcome : Bool × Bool => outcome.1)
    (boolEventAlgebra.comap fun outcome : Bool × Bool => outcome.2) :=
  fairCoin.product_independentEventAlgebras fairCoin
    boolEventAlgebra boolEventAlgebra

example : twoCoins.expectation (fun outcome =>
      firstCoinSimpleObservable.evaluate outcome *
        secondCoinSimpleObservable.evaluate outcome) =
    firstCoinSimpleObservable.expectation twoCoins *
      secondCoinSimpleObservable.expectation twoCoins :=
  SimpleObservable.expectation_mul_eq_mul_expectation_of_independent twoCoins
    (fairCoin.product_independentEventAlgebras fairCoin
      boolEventAlgebra boolEventAlgebra)
    firstCoinSimpleObservable secondCoinSimpleObservable

example : twoCoins.expectation (fun outcome =>
      firstCoinSimpleObservable.evaluate outcome *
        secondCoinSimpleObservable.evaluate outcome) = 4 := by
  unfold twoCoins firstCoinSimpleObservable secondCoinSimpleObservable
    coinSimpleObservable headsEventCode tailsEventCode
  decide

example : twoCoins.covariance firstCoinSimpleObservable.evaluate
    secondCoinSimpleObservable.evaluate = 0 :=
  SimpleObservable.covariance_eq_zero_of_independent twoCoins
    (fairCoin.product_independentEventAlgebras fairCoin
      boolEventAlgebra boolEventAlgebra)
    firstCoinSimpleObservable secondCoinSimpleObservable

example : twoCoins.IndependentEvents
    (fun outcome => !outcome.1) (fun outcome => !outcome.2) :=
  twoCoins.independentEvents_complements
    (fairCoin.product_independentEvents_coordinates fairCoin
      (fun outcome => outcome) (fun outcome => outcome))

example : twoCoins.conditionalProbability
    (fun outcome => outcome.1) (fun outcome => outcome.2) (by decide) =
      1 / 2 := by
  rw [twoCoins.conditionalProbability_eq_of_independent (by decide)
    (fairCoin.product_independentEvents_coordinates fairCoin
      (fun outcome => outcome) (fun outcome => outcome))]
  decide

example : twoCoins.covariance
    (Distribution.indicator fun outcome => outcome.1)
    (Distribution.indicator fun outcome => outcome.2) = 0 :=
  twoCoins.covariance_indicators_eq_zero_of_independent
    (fairCoin.product_independentEvents_coordinates fairCoin
      (fun outcome => outcome) (fun outcome => outcome))

example : twoCoins.probability exactlyOneTrue = 1 / 2 := by
  decide

example : twoCoins.probability exactlyOneTrue =
    fairCoin.expectation (fun left =>
      fairCoin.probability (fun right => exactlyOneTrue (left, right))) :=
  fairCoin.product_probability_iterated fairCoin exactlyOneTrue

example : twoCoins.expectation
      (fun outcome => Distribution.indicator (fun value => value) outcome.1 *
        Distribution.indicator (fun value => value) outcome.2) = 1 / 4 := by
  unfold twoCoins
  rw [Distribution.product_expectation_mul,
    Distribution.expectation_indicator]
  decide

example : twoCoins.expectation
      (fun outcome => if exactlyOneTrue outcome then 7 else 1) =
    fairCoin.expectation (fun left =>
      fairCoin.expectation (fun right =>
        if exactlyOneTrue (left, right) then 7 else 1)) :=
  fairCoin.product_expectation_iterated fairCoin
    (fun outcome => if exactlyOneTrue outcome then 7 else 1)

def coinNumeric (outcome : Bool) : Coordinate :=
  if outcome then 1 else 0

example : twoCoins.covariance
    (fun outcome => coinNumeric outcome.1)
    (fun outcome => coinNumeric outcome.2) = 0 :=
  fairCoin.product_covariance_coordinates_zero fairCoin
    coinNumeric coinNumeric

example : twoCoins.variance
    (fun outcome => coinNumeric outcome.1 + coinNumeric outcome.2) = 1 / 2 := by
  decide

example : twoCoins.variance
      (fun outcome => coinNumeric outcome.1 + coinNumeric outcome.2) =
    fairCoin.variance coinNumeric + fairCoin.variance coinNumeric :=
  fairCoin.product_variance_add_coordinates fairCoin coinNumeric coinNumeric

/-! ## Unresolved event mass and certified refinement -/

def unresolvedFrontier : List (Classified Nat) :=
  [⟨⟨0, 1 / 4, by decide⟩, .inside⟩,
    ⟨⟨1, 1 / 2, by decide⟩, .unresolved⟩,
    ⟨⟨2, 1 / 4, by decide⟩, .outside⟩]

example : (eventBound unresolvedFrontier).lower = 1 / 4 := by
  decide

example : (eventBound unresolvedFrontier).upper = 3 / 4 := by
  decide

example : (eventBound unresolvedFrontier).width = 1 / 2 := by
  decide

def unresolvedParent : Classified Unit :=
  ⟨⟨(), 1, by decide⟩, .unresolved⟩

def resolvedChildren : List (Classified Bool) :=
  [⟨⟨false, 1 / 2, by decide⟩, .inside⟩,
    ⟨⟨true, 1 / 2, by decide⟩, .outside⟩]

def binaryResolution : Split (β := Bool) unresolvedParent where
  children := resolvedChildren
  conserved := by decide
  statuses := by
    intro child member
    trivial

example : Bound.Refines (eventBound resolvedChildren)
    (eventBound [unresolvedParent]) :=
  binaryResolution.eventBound_refines

example : (eventBound resolvedChildren).lower = 1 / 2 ∧
    (eventBound resolvedChildren).upper = 1 / 2 := by
  decide

def coarseFrontier : List (Classified Unit) :=
  [unresolvedParent]

def refinedFrontier : List (Classified Unit) :=
  [⟨⟨(), 1 / 2, by decide⟩, .inside⟩,
    ⟨⟨(), 1 / 2, by decide⟩, .outside⟩]

def unitResolution : Split (β := Unit) unresolvedParent where
  children := refinedFrontier
  conserved := by decide
  statuses := by
    intro child member
    trivial

example : FrontierRefines refinedFrontier coarseFrontier := by
  change FrontierRefines unitResolution.children [unresolvedParent]
  simpa only [List.nil_append, List.append_nil] using
    (FrontierRefines.split [] [] unresolvedParent unitResolution)

example : unresolvedWeight refinedFrontier ≤
    unresolvedWeight coarseFrontier := by
  have relation : FrontierRefines unitResolution.children [unresolvedParent] :=
    by
      simpa only [List.nil_append, List.append_nil] using
        (FrontierRefines.split [] [] unresolvedParent unitResolution)
  exact relation.unresolved_le

/-! ## Finite lower and upper integration -/

def rangedCells : List (IntegrationCell Nat) :=
  [⟨0, 1 / 2, by decide, 0, 1 / 4, by decide⟩,
    ⟨1, 1 / 2, by decide, 1 / 2, 3 / 4, by decide⟩]

example : (integralBound rangedCells).lower = 1 / 4 := by
  decide

example : (integralBound rangedCells).upper = 1 / 2 := by
  decide

example : (integralBound rangedCells).width = 1 / 4 := by
  decide

def sampledValue (index : Nat) : Coordinate :=
  if index == 0 then 1 / 8 else 5 / 8

example : (integralBound rangedCells).Contains
    (weightedEvaluation sampledValue rangedCells) := by
  apply weightedEvaluation_mem_integralBound
  intro cell member
  simp only [rangedCells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> decide

def integrationParent : IntegrationCell Unit :=
  ⟨(), 1, by decide, 0, 1, by decide⟩

def integrationChildren : List (IntegrationCell Unit) :=
  [⟨(), 1 / 2, by decide, 0, 1 / 4, by decide⟩,
    ⟨(), 1 / 2, by decide, 3 / 4, 1, by decide⟩]

def integrationResolution : IntegrationSplit integrationParent where
  children := integrationChildren
  weight_conserved := by decide
  lower_refines := by
    intro child member
    simp only [integrationChildren, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl <;> decide
  upper_refines := by
    intro child member
    simp only [integrationChildren, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl <;> decide

example : Bound.Refines (integralBound integrationChildren)
    (integralBound [integrationParent]) :=
  integrationResolution.integralBound_refines

theorem integrationFrontierRefinement :
    IntegrationFrontierRefines integrationChildren [integrationParent] := by
  change IntegrationFrontierRefines integrationResolution.children
    [integrationParent]
  simpa only [List.nil_append, List.append_nil] using
    (IntegrationFrontierRefines.split [] [] integrationParent
      integrationResolution)

example : integralOscillation integrationChildren ≤
    integralOscillation [integrationParent] :=
  integrationFrontierRefinement.oscillation_le

example : integrationWeight integrationChildren =
    integrationWeight [integrationParent] :=
  integrationFrontierRefinement.weight_conserved

example : (integralBound integrationChildren).lower = 3 / 8 ∧
    (integralBound integrationChildren).upper = 5 / 8 := by
  decide

def exactSimpleEntries : List (Weighted (Bool × Coordinate)) :=
  [⟨(false, 1 / 4), 1 / 2, by decide⟩,
    ⟨(true, 3 / 4), 1 / 2, by decide⟩]

example (request : AccuracyRequest) (requests : List AccuracyRequest)
    (member : request ∈ requests) :
    integralOscillation
      ((IntegrationProcess.exactSimple exactSimpleEntries).frontier
        ((IntegrationProcess.exactSimple exactSimpleEntries).runRequests
          () requests)) < request.tolerance :=
  IntegrationProcess.runRequests_oscillation_lt_of_mem
    (IntegrationProcess.exactSimple exactSimpleEntries)
      () requests request member

/-! ## Finite tail budgets -/

def geometricBudget : TailBudget where
  amount := 3 / 4
  remainder := 1 / 4
  remainder_nonnegative := by decide

example : geometricBudget.bound.lower = 3 / 4 ∧
    geometricBudget.bound.upper = 1 := by
  decide

example : geometricBudget.Resolves (1 / 2) := by
  unfold TailBudget.Resolves geometricBudget
  decide

example : Bound.Refines
    (geometricBudget.advance (1 / 8) (1 / 8) (by decide)).bound
    geometricBudget.bound := by
  apply geometricBudget.advance_bound_refines
  · decide
  · unfold TailBudget.Conserves geometricBudget
    decide

def exactGeometricBudget : TailBudget where
  amount := 1
  remainder := 0
  remainder_nonnegative := le_rfl

def exactGeometric_refines :
    TailBudget.Refines exactGeometricBudget geometricBudget where
  added := 1 / 4
  added_nonnegative := by decide
  amount_eq := by decide
  remainder_eq := by decide

def terminatingTailProcess : TailProcess where
  State := Bool
  budget finished := if finished then exactGeometricBudget else geometricBudget
  initial := false
  request _ _ _ := true
  request_refines state epsilon positive := by
    cases state
    · exact exactGeometric_refines
    · exact TailBudget.Refines.refl exactGeometricBudget
  accurate state epsilon positive := by
    unfold TailBudget.Resolves exactGeometricBudget
    exact positive
  refinesInitial state := by
    cases state
    · exact TailBudget.Refines.refl geometricBudget
    · exact exactGeometric_refines

example (epsilon : Coordinate) (positive : 0 < epsilon) :
    (terminatingTailProcess.budget
      (terminatingTailProcess.request false epsilon positive)).bound.width <
        epsilon :=
  terminatingTailProcess.request_bound_width_lt false epsilon positive

/-! ## Exact rational box content -/

def rectangle : Box where
  xLower := 0
  xUpper := 2
  yLower := 0
  yUpper := 3
  x_valid := by decide
  y_valid := by decide

example : RFAP.FiniteMeasure.boxContent rectangle = 6 := by
  decide

def rectangleVerticalLaw : Distribution Box :=
  RFAP.FiniteMeasure.verticalSplitDistribution rectangle 1
    (by decide) (by decide)

example : rectangleVerticalLaw.atoms.length = 2 := by
  decide

example : rectangleVerticalLaw.expectation
    RFAP.FiniteMeasure.boxContent = 3 := by
  decide

def coarseRectangleChildContentRange (_ : Box) : Bound :=
  ⟨2, 4, by decide⟩

def exactRectangleChildContentRange (box : Box) : Bound :=
  Bound.exact (RFAP.FiniteMeasure.boxContent box)

example : rectangleVerticalLaw.enclosedExpectation
      coarseRectangleChildContentRange =
    ⟨2, 4, by decide⟩ := by
  apply Bound.ext <;> decide

example : (rectangleVerticalLaw.enclosedExpectation
      coarseRectangleChildContentRange).Contains
    (rectangleVerticalLaw.expectation RFAP.FiniteMeasure.boxContent) := by
  decide

example : Bound.Refines
    (rectangleVerticalLaw.enclosedExpectation
      exactRectangleChildContentRange)
    (rectangleVerticalLaw.enclosedExpectation
      coarseRectangleChildContentRange) := by
  unfold exactRectangleChildContentRange
  rw [rectangleVerticalLaw.enclosedExpectation_exact]
  exact ⟨by decide, by decide⟩

example : rectangleVerticalLaw.probability
    (fun child => decide (child.xUpper ≤ 1)) = 1 / 2 := by
  decide

example : (RFAP.FiniteMeasure.verticalSplitParentLawCoupling
    rectangle 1 (by decide) (by decide)).coupling.joint.atoms.length = 2 := by
  decide

example :
    RFAP.FiniteMeasure.boxContent
        (rectangle.verticalLeft 1 (by decide)) +
      RFAP.FiniteMeasure.boxContent
        (rectangle.verticalRight 1 (by decide)) =
      RFAP.FiniteMeasure.boxContent rectangle :=
  RFAP.FiniteMeasure.vertical_content_add rectangle 1 (by decide)

def rectangleRangeCell : RFAP.FiniteMeasure.BoxIntegrationCell where
  box := rectangle
  lower := 1
  upper := 3
  range_valid := by decide

example : Bound.Refines
    (integralBound (RFAP.FiniteMeasure.boxIntegrationCells
      (RFAP.FiniteMeasure.verticalSameRangeSplit
        rectangleRangeCell 1 (by decide)).children))
    (integralBound [rectangleRangeCell.toIntegrationCell]) :=
  RFAP.FiniteMeasure.verticalSameRange_integralBound_refines
    rectangleRangeCell 1 (by decide)

def displayedPoint : Gaussian :=
  ⟨2, -3⟩

example (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((RFAP.FiniteMeasure.singletonNull displayedPoint).request epsilon
      positive).content = 0 := by
  simp only [RFAP.FiniteMeasure.singletonNull,
    RFAP.FiniteMeasure.BoxCover.content, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, RFAP.FiniteMeasure.pointBox_content,
    add_zero]

def displayedPointGenericNull :
    EffectiveNull RFAP.FiniteMeasure.boxCoverScheme
      (fun candidate => candidate = displayedPoint) :=
  (RFAP.FiniteMeasure.singletonNull displayedPoint).toGeneric

example (epsilon : Coordinate) (positive : 0 < epsilon) :
    (displayedPointGenericNull.request epsilon positive).content = 0 := by
  simp only [displayedPointGenericNull,
    RFAP.FiniteMeasure.EffectiveNull.toGeneric,
    RFAP.FiniteMeasure.singletonNull,
    RFAP.FiniteMeasure.BoxCover.toFiniteCover_content,
    RFAP.FiniteMeasure.BoxCover.content, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, RFAP.FiniteMeasure.pointBox_content,
    add_zero]

example (epsilon : Coordinate) (positive : 0 < epsilon) :
    upperIntegral
      (RFAP.FiniteMeasure.boxIntegrationCells
        ((RFAP.FiniteMeasure.singletonNull displayedPoint).requestedBoundedCells
          1 (by decide) epsilon positive)) < epsilon :=
  RFAP.FiniteMeasure.EffectiveNull.requestedBoundedCells_upper_lt
    (RFAP.FiniteMeasure.singletonNull displayedPoint) 1 (by decide)
      epsilon positive

example (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((RFAP.FiniteMeasure.finitePointsNull
      [displayedPoint, ⟨0, 0⟩]).request epsilon positive).content < epsilon :=
  (RFAP.FiniteMeasure.finitePointsNull
    [displayedPoint, ⟨0, 0⟩]).small epsilon positive

def twoNullPredicates : List RFAP.FiniteMeasure.NullPredicate :=
  [⟨fun point => point = displayedPoint,
      RFAP.FiniteMeasure.singletonNull displayedPoint⟩,
    ⟨fun point => point = ⟨0, 0⟩,
      RFAP.FiniteMeasure.singletonNull ⟨0, 0⟩⟩]

example (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((RFAP.FiniteMeasure.NullPredicate.finiteUnion twoNullPredicates).request
      epsilon positive).content < epsilon :=
  (RFAP.FiniteMeasure.NullPredicate.finiteUnion twoNullPredicates).small
    epsilon positive

def rationalSpike (point : Gaussian) : Coordinate :=
  if point = displayedPoint then 1 else 0

def rationalSpike_equalExceptNull :
    RFAP.FiniteMeasure.EqualExceptNull rationalSpike (fun _ => 0) :=
  RFAP.FiniteMeasure.EffectiveNull.mono
    (RFAP.FiniteMeasure.singletonNull displayedPoint)
    (by
      intro point different
      by_cases equal : point = displayedPoint
      · exact equal
      · have spikeZero : rationalSpike point = 0 := by
          simp only [rationalSpike, equal, ↓reduceIte]
        exact (different spikeZero).elim)

/-! ## CCL finite area observations -/

example (name : CCL.BoxedNames.ProgressiveName)
    (target : Coordinate) (positive : 0 < target) :
    RFAP.FiniteMeasure.boxContent
      (CCL.FiniteMeasure.ProgressiveName.areaCertificate
        name name.initial target positive).box < target :=
  CCL.FiniteMeasure.ProgressiveName.areaCertificate_content_lt
    name name.initial target positive

example (name : CCL.BoxedNames.ProgressiveName) :
    OperationallyEquivalent
      ((CCL.FiniteMeasure.ProgressiveName.toAreaProcess name).add
        (CCL.FiniteMeasure.ProgressiveName.toAreaProcess name))
      ((BoundProcess.exact 0).add (BoundProcess.exact 0)) :=
  operationallyEquivalent_add
    (CCL.FiniteMeasure.ProgressiveName.toAreaProcess_operationallyEquivalent_zero
      name)
    (CCL.FiniteMeasure.ProgressiveName.toAreaProcess_operationallyEquivalent_zero
      name)

example (name : CCL.BoxedNames.ProgressiveName) :
    OperationallyEquivalent
      ((CCL.FiniteMeasure.ProgressiveName.toAreaProcess name).add
        (CCL.FiniteMeasure.ProgressiveName.toAreaProcess name))
      (BoundProcess.exact 0) := by
  apply operationallyEquivalent_exact_of_anchoredAt
  simpa only [zero_add] using
    BoundProcess.anchoredAt_add
      (CCL.FiniteMeasure.ProgressiveName.toAreaProcess name)
      (CCL.FiniteMeasure.ProgressiveName.toAreaProcess name)
      0 0
      (CCL.FiniteMeasure.ProgressiveName.toAreaProcess_anchored name)
      (CCL.FiniteMeasure.ProgressiveName.toAreaProcess_anchored name)

example (name : CCL.BoxedNames.ProgressiveName)
    (requests : List AccuracyRequest) (request : AccuracyRequest)
    (member : request ∈ requests) {left right : Gaussian}
    (leftPossible :
      (name.certificate
        (CCL.FiniteMeasure.ProgressiveName.runAccuracyRequests
          name name.initial requests)).Possible left)
    (rightPossible :
      (name.certificate
        (CCL.FiniteMeasure.ProgressiveName.runAccuracyRequests
          name name.initial requests)).Possible right) :
    CCL.FiniteMeasure.Certificate.affineDistance left right <
      request.tolerance :=
  CCL.FiniteMeasure.ProgressiveName.runAccuracyRequests_pairwise_lt_of_mem
    name name.initial requests request member leftPossible rightPossible

example (left right : CCL.BoxedNames.ProgressiveName)
    (target : Coordinate) (positive : 0 < target) :
    CCL.FiniteMeasure.familyContent
        (CCL.FiniteMeasure.familyCertificates [left, right] target positive) <
      target :=
  CCL.FiniteMeasure.familyCertificates_content_lt [left, right]
    target positive

example (target : Coordinate) (positive : 0 < target) :
    (1 / 2 : Coordinate) ^ CCL.FiniteMeasure.requiredBlockCount target <
      target :=
  CCL.FiniteMeasure.requiredBlockCount_spread_lt positive

example : CCL.FiniteMeasure.rawPrefixWeight [true, false, true] = 1 / 8 := by
  decide

example : (CCL.FiniteMeasure.rawExtensions [true] 3).length = 8 := by
  decide

def thirdRawBitTrue : CCL.FiniteMeasure.Word → Bool
  | _ :: _ :: true :: _ => true
  | _ => false

def rawTrueCount : CCL.FiniteMeasure.Word → Coordinate
  | [] => 0
  | bit :: remaining =>
      (if bit then 1 else 0) + rawTrueCount remaining

example :
    (CCL.FiniteMeasure.rawExtensionDistribution [true, false] 3).atoms.length =
      8 := by
  decide

example :
    (CCL.FiniteMeasure.rawExtensionDistribution [true, false] 3).probability
      thirdRawBitTrue = 1 / 2 := by
  decide

example (stem : CCL.FiniteMeasure.Word) (depth : Nat)
    (event : CCL.FiniteMeasure.Word → Bool) :
    (CCL.FiniteMeasure.rawExtensionDistribution stem depth).probability event =
      (CCL.FiniteMeasure.rawExtensionContent stem depth).measure event /
        CCL.FiniteMeasure.rawPrefixWeight stem :=
  CCL.FiniteMeasure.rawExtensionDistribution_probability stem depth event

example (stem : CCL.FiniteMeasure.Word) (depth : Nat)
    (event : CCL.FiniteMeasure.Word → Bool) :
    (CCL.FiniteMeasure.rawExtensionDistribution stem depth).probability event =
      (CCL.FiniteMeasure.rawFrontierEventCount
          (CCL.FiniteMeasure.rawExtensions stem depth) event : Coordinate) *
        (1 / 2 : Coordinate) ^ depth :=
  CCL.FiniteMeasure.rawExtensionDistribution_probability_eq_count_mul
    stem depth event

example (stem : CCL.FiniteMeasure.Word) (depth : Nat)
    (event : CCL.FiniteMeasure.Proj → Bool) :
    (CCL.FiniteMeasure.rawTruncationDistribution stem depth).probability event =
      (CCL.FiniteMeasure.rawFrontierEventCount
          (CCL.FiniteMeasure.rawExtensions stem depth)
          (fun word => event (CCL.FiniteMeasure.rawTruncation word)) :
        Coordinate) * (1 / 2 : Coordinate) ^ depth :=
  CCL.FiniteMeasure.rawTruncationDistribution_probability_eq_count_mul
    stem depth event

example (stem : CCL.FiniteMeasure.Word) (depth extra : Nat)
    (probe : CCL.FiniteMeasure.Proj → Coordinate) :
    (CCL.FiniteMeasure.rawTruncationDistribution
        stem (depth + extra)).variance probe =
      (CCL.FiniteMeasure.rawExtensionDistribution stem depth).expectation
          (CCL.FiniteMeasure.rawBackwardVariance extra
            (fun word => probe (CCL.FiniteMeasure.rawTruncation word))) +
        (CCL.FiniteMeasure.rawExtensionDistribution stem depth).variance
          (CCL.FiniteMeasure.rawBackwardMean extra
            (fun word => probe (CCL.FiniteMeasure.rawTruncation word))) :=
  CCL.FiniteMeasure.rawTruncationDistribution_totalVariance_backward
    stem depth extra probe

example (stem : CCL.FiniteMeasure.Word) (depth : Nat)
    (event : CCL.FiniteMeasure.Word → Bool) :
    (CCL.FiniteMeasure.rawExtensionDistribution stem (depth + 1)).probability
        (fun word => event (CCL.FiniteMeasure.rawParent word)) =
      (CCL.FiniteMeasure.rawExtensionDistribution stem depth).probability
        event :=
  CCL.FiniteMeasure.rawExtensionDistribution_probability_parent
    stem depth event

example (stem : CCL.FiniteMeasure.Word) (depth : Nat)
    (event : CCL.FiniteMeasure.Word → Bool) :
    (CCL.FiniteMeasure.rawExtensionDistribution stem (depth + 1)).probability
        (fun word => CCL.FiniteMeasure.rawLastBit word &&
          event (CCL.FiniteMeasure.rawParent word)) =
      (1 / 2 : Coordinate) *
        (CCL.FiniteMeasure.rawExtensionDistribution stem depth).probability
          event :=
  CCL.FiniteMeasure.rawExtensionDistribution_probability_lastTrue_and_parent
    stem depth event

example (stem : CCL.FiniteMeasure.Word) (depth : Nat) :
    (CCL.FiniteMeasure.rawExtensionDistribution stem (depth + 1)).probability
        CCL.FiniteMeasure.rawLastBit = 1 / 2 :=
  CCL.FiniteMeasure.rawExtensionDistribution_probability_lastBit_true
    stem depth

example (stem : CCL.FiniteMeasure.Word) (depth extra : Nat)
    (value : CCL.FiniteMeasure.Word → Coordinate) :
    (CCL.FiniteMeasure.rawExtensionDistribution stem depth).expectation
        (CCL.FiniteMeasure.rawBackwardMean extra value) =
      (CCL.FiniteMeasure.rawExtensionDistribution
        stem (depth + extra)).expectation value :=
  CCL.FiniteMeasure.rawExtensionDistribution_expectation_backward
    stem depth value extra

example :
    (CCL.FiniteMeasure.rawExtensionDistribution [] 1).expectation
        (CCL.FiniteMeasure.rawBackwardMean 2 rawTrueCount) = 3 / 2 := by
  rw [CCL.FiniteMeasure.rawExtensionDistribution_expectation_backward]
  decide

example :
    (CCL.FiniteMeasure.rawExtensionDistribution [] 1).variance
        (CCL.FiniteMeasure.rawBackwardMean 2 rawTrueCount) = 1 / 4 := by
  decide

example :
    (CCL.FiniteMeasure.rawExtensionDistribution [] 3).variance
        rawTrueCount = 3 / 4 := by
  decide

example :
    (CCL.FiniteMeasure.rawExtensionDistribution [] 1).expectation
        (CCL.FiniteMeasure.rawBackwardVariance 2 rawTrueCount) = 1 / 2 := by
  decide

example : (3 / 4 : Coordinate) = 1 / 2 + 1 / 4 := by
  decide

example (stem : CCL.FiniteMeasure.Word) (depth extra : Nat)
    (value : CCL.FiniteMeasure.Word → Coordinate) :
    (CCL.FiniteMeasure.rawExtensionDistribution stem depth).variance
        (CCL.FiniteMeasure.rawBackwardMean extra value) ≤
      (CCL.FiniteMeasure.rawExtensionDistribution
        stem (depth + extra)).variance value :=
  CCL.FiniteMeasure.rawExtensionDistribution_variance_backward
    stem depth value extra

example (stem : CCL.FiniteMeasure.Word) (depth extra : Nat)
    (value : CCL.FiniteMeasure.Word → Coordinate) :
    (CCL.FiniteMeasure.rawExtensionDistribution
        stem (depth + extra)).variance value =
      (CCL.FiniteMeasure.rawExtensionDistribution stem depth).expectation
          (CCL.FiniteMeasure.rawBackwardVariance extra value) +
        (CCL.FiniteMeasure.rawExtensionDistribution stem depth).variance
          (CCL.FiniteMeasure.rawBackwardMean extra value) :=
  CCL.FiniteMeasure.rawExtensionDistribution_totalVariance_backward
    stem depth value extra

example : CCL.FiniteMeasure.rawParent [true, false, true] =
    [true, false] := by
  decide

example : CCL.FiniteMeasure.rawAncestor 2 [true, false, true] = [true] := by
  decide

example (stem : CCL.FiniteMeasure.Word) (depth extra : Nat)
    (event : CCL.FiniteMeasure.Word → Bool) :
    (CCL.FiniteMeasure.rawExtensionDistribution
        stem (depth + extra)).probability
          (fun word => event (CCL.FiniteMeasure.rawAncestor extra word)) =
      (CCL.FiniteMeasure.rawExtensionDistribution stem depth).probability
        event :=
  CCL.FiniteMeasure.rawExtensionDistribution_probability_ancestor
    stem depth event extra

example (stem : CCL.FiniteMeasure.Word) (depth extra : Nat) :
    (CCL.FiniteMeasure.rawExtensionAncestorLawCoupling
      stem depth extra).mismatchProbability
        (CCL.FiniteMeasure.rawAncestorRelation extra) = 0 :=
  CCL.FiniteMeasure.rawExtensionAncestorLawCoupling_mismatchProbability
    stem depth extra

example : (CCL.FiniteMeasure.rawExtensionAncestorLawCoupling [] 1 2).coupling.joint.atoms.length = 8 := by
  decide

example :
    (CCL.FiniteMeasure.rawExtensionContent [true, false] 4).total = 1 / 4 :=
  CCL.FiniteMeasure.rawExtensionContent_total [true, false] 4

example : (CCL.FiniteMeasure.fairDepthDistribution 3).atoms.length = 8 :=
  CCL.FiniteMeasure.fairDepthDistribution_atoms_length 3

def startsWithTrue : CCL.FiniteMeasure.Word → Bool
  | true :: _ => true
  | _ => false

example : (CCL.FiniteMeasure.fairDepthDistribution 3).probability
    startsWithTrue = 1 / 2 := by
  decide

example :
    CCL.FiniteMeasure.rawPrefixWeight [true, false] +
        CCL.FiniteMeasure.rawPrefixWeight [true, true] =
      CCL.FiniteMeasure.rawPrefixWeight [true] :=
  CCL.FiniteMeasure.rawPrefixWeight_children_add [true]

def resolvedRawRoot : List (Classified CCL.FiniteMeasure.Word) :=
  CCL.FiniteMeasure.rawBinaryChildren [] .inside .outside

example : Bound.Refines (eventBound resolvedRawRoot)
    (eventBound [CCL.FiniteMeasure.rawClassified [] .unresolved]) :=
  CCL.FiniteMeasure.rawUnresolvedSplit_eventBound_refines
    [] .inside .outside

example : (eventBound resolvedRawRoot).lower = 1 / 2 ∧
    (eventBound resolvedRawRoot).upper = 1 / 2 := by
  decide

def firstBitTrueEvent : CCL.FiniteMeasure.RawEvent :=
  .branch .empty .full

example : firstBitTrueEvent.weight = 1 / 2 := by
  decide

example :
    eventBound firstBitTrueEvent.terminalFrontier =
      Bound.exact firstBitTrueEvent.weight :=
  firstBitTrueEvent.terminalFrontier_eventBound

example :
    firstBitTrueEvent.terminalDistribution.probability
        CCL.FiniteMeasure.RawEvent.terminalInside =
      firstBitTrueEvent.weight :=
  firstBitTrueEvent.terminalDistribution_probability_inside

example (blocks suffix : List CCL.FiniteMeasure.Block) :
    (CCL.FiniteMeasure.prefixProfile (blocks ++ suffix)).symbolicWeight ≤
        (CCL.FiniteMeasure.prefixProfile blocks).symbolicWeight ∧
      (CCL.FiniteMeasure.prefixProfile (blocks ++ suffix)).geometricSpread ≤
        (CCL.FiniteMeasure.prefixProfile blocks).geometricSpread :=
  CCL.FiniteMeasure.prefixProfile_append_refines blocks suffix

example (blocks : List CCL.FiniteMeasure.Block)
    (target : Coordinate) (positive : 0 < target)
    (enough : CCL.FiniteMeasure.requiredBlockCount target ≤ blocks.length) :
    CCL.FiniteMeasure.completedPrefixWeight blocks < target ∧
      CCL.FiniteMeasure.cylinderSpread blocks < target :=
  CCL.FiniteMeasure.completedPrefixProfile_lt_requested positive enough

example (blocks : List CCL.FiniteMeasure.Block) (depth : Nat) :
    (CCL.FiniteMeasure.completedPrefixExtensionContent blocks depth).total =
      CCL.FiniteMeasure.completedPrefixWeight blocks :=
  CCL.FiniteMeasure.completedPrefixExtensionContent_total blocks depth

example (blocks : List CCL.FiniteMeasure.Block) (depth : Nat) :
    (CCL.FiniteMeasure.completedPrefixExtensionDistribution blocks depth).atoms.length =
      2 ^ depth :=
  CCL.FiniteMeasure.completedPrefixExtensionDistribution_atoms_length
    blocks depth

example (blocks : List CCL.FiniteMeasure.Block) (depth : Nat)
    (value : CCL.FiniteMeasure.Word → Coordinate) :
    (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks (depth + 1)).expectation
          (fun word => value (CCL.FiniteMeasure.rawParent word)) =
      (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks depth).expectation value :=
  CCL.FiniteMeasure.completedPrefixExtensionDistribution_expectation_parent
    blocks depth value

example (blocks : List CCL.FiniteMeasure.Block) (depth extra : Nat)
    (event : CCL.FiniteMeasure.Word → Bool) :
    (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks (depth + extra)).probability
          (fun word => event (CCL.FiniteMeasure.rawAncestor extra word)) =
      (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks depth).probability event :=
  CCL.FiniteMeasure.completedPrefixExtensionDistribution_probability_ancestor
    blocks depth event extra

example (blocks : List CCL.FiniteMeasure.Block) (depth extra : Nat) :
    (CCL.FiniteMeasure.completedPrefixExtensionAncestorLawCoupling
      blocks depth extra).mismatchProbability
        (CCL.FiniteMeasure.rawAncestorRelation extra) = 0 :=
  CCL.FiniteMeasure.completedPrefixExtensionAncestorLawCoupling_mismatchProbability
    blocks depth extra

example (blocks : List CCL.FiniteMeasure.Block) (depth extra : Nat)
    (value : CCL.FiniteMeasure.Word → Coordinate) :
    (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks depth).expectation
          (CCL.FiniteMeasure.rawBackwardMean extra value) =
      (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks (depth + extra)).expectation value :=
  CCL.FiniteMeasure.completedPrefixExtensionDistribution_expectation_backward
    blocks depth value extra

example (blocks : List CCL.FiniteMeasure.Block) (depth extra : Nat)
    (value : CCL.FiniteMeasure.Word → Coordinate) :
    (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks depth).variance
          (CCL.FiniteMeasure.rawBackwardMean extra value) ≤
      (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks (depth + extra)).variance value :=
  CCL.FiniteMeasure.completedPrefixExtensionDistribution_variance_backward
    blocks depth value extra

example (blocks : List CCL.FiniteMeasure.Block) (depth extra : Nat)
    (value : CCL.FiniteMeasure.Word → Coordinate) :
    (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks (depth + extra)).variance value =
      (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks depth).expectation
          (CCL.FiniteMeasure.rawBackwardVariance extra value) +
        (CCL.FiniteMeasure.completedPrefixExtensionDistribution
          blocks depth).variance
            (CCL.FiniteMeasure.rawBackwardMean extra value) :=
  CCL.FiniteMeasure.completedPrefixExtensionDistribution_totalVariance_backward
    blocks depth value extra

example (blocks : List CCL.FiniteMeasure.Block)
    (witness : CCL.FiniteMeasure.Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (CCL.FiniteMeasure.completedPrefixProbeBound blocks witness
      witnessRealizes probe factor factorNonnegative sensitive).width =
        2 * (factor * CCL.FiniteMeasure.cylinderSpread blocks) :=
  CCL.FiniteMeasure.completedPrefixProbeBound_width blocks witness
    witnessRealizes probe factor factorNonnegative sensitive

example (blocks : List CCL.FiniteMeasure.Block) (depth : Nat)
    (witness : CCL.FiniteMeasure.Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (CCL.FiniteMeasure.completedPrefixProbeExpectationBound
      blocks depth witness witnessRealizes probe factor factorNonnegative
        sensitive).width =
      2 * (factor * CCL.FiniteMeasure.cylinderSpread blocks) :=
  CCL.FiniteMeasure.completedPrefixProbeExpectationBound_width
    blocks depth witness witnessRealizes probe factor factorNonnegative sensitive

example (blocks : List CCL.FiniteMeasure.Block) (depth : Nat)
    (witness : CCL.FiniteMeasure.Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CCL.FiniteMeasure.Word → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom,
      atom ∈ (CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks depth).atoms →
        CCL.Cylinder.Realizes blocks (points atom.item)) :
    (CCL.FiniteMeasure.completedPrefixProbeExpectationBound
      blocks depth witness witnessRealizes probe factor factorNonnegative
        sensitive).Contains
      ((CCL.FiniteMeasure.completedPrefixExtensionDistribution
        blocks depth).expectation (fun word => probe (points word))) :=
  CCL.FiniteMeasure.completedPrefixProbeExpectationBound_contains
    blocks depth witness witnessRealizes probe factor factorNonnegative
      sensitive points pointsRealize

example (blocks : List CCL.FiniteMeasure.Block)
    (witness point : CCL.FiniteMeasure.Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (pointRealizes : CCL.Cylinder.Realizes blocks point)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (CCL.FiniteMeasure.completedPrefixProbeBound blocks witness
      witnessRealizes probe factor factorNonnegative sensitive).Contains
        (probe point) :=
  CCL.FiniteMeasure.completedPrefixProbeBound_contains blocks witness
    witnessRealizes probe factor factorNonnegative sensitive pointRealizes

example (stem suffix : List CCL.FiniteMeasure.Block)
    (witness : CCL.FiniteMeasure.Proj)
    (witnessRealizes : CCL.Cylinder.Realizes (stem ++ suffix) witness)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    Bound.Refines
      (CCL.FiniteMeasure.completedPrefixProbeBound
        (stem ++ suffix) witness witnessRealizes
        probe factor factorNonnegative sensitive)
      (CCL.FiniteMeasure.completedPrefixProbeBound stem witness
        (CCL.FiniteMeasure.realizesPrefix witnessRealizes)
        probe factor factorNonnegative sensitive) :=
  CCL.FiniteMeasure.completedPrefixProbeBound_append_refines
    stem suffix witness witnessRealizes probe factor factorNonnegative sensitive

example (blocks : List CCL.FiniteMeasure.Block)
    (witness : CCL.FiniteMeasure.Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : CCL.FiniteMeasure.requiredProbeBlockCount target factor ≤
      blocks.length) :
    (CCL.FiniteMeasure.completedPrefixProbeBound blocks witness
      witnessRealizes probe factor factorPositive.le sensitive).width < target :=
  CCL.FiniteMeasure.completedPrefixProbeBound_width_lt_requested
    witness witnessRealizes probe factor factorPositive sensitive
    target targetPositive enough

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (CCL.FiniteMeasure.prefixFamilyProbeExpectationBound distribution
      probe factor factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor *
          CCL.FiniteMeasure.cylinderSpread certificate.blocks) :=
  CCL.FiniteMeasure.prefixFamilyProbeExpectationBound_width
    distribution probe factor factorNonnegative sensitive

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (CCL.FiniteMeasure.prefixFamilyProbeExpectationBound distribution
      probe factor factorNonnegative sensitive).Contains
        (distribution.expectation fun certificate =>
          probe (points certificate)) :=
  CCL.FiniteMeasure.prefixFamilyProbeExpectationBound_contains
    distribution probe factor factorNonnegative sensitive
      points pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (suffix : CCL.FiniteMeasure.CompletedPrefixCertificate →
      List CCL.FiniteMeasure.Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    Bound.Refines
      (CCL.FiniteMeasure.extendedPrefixFamilyProbeExpectationBound
        distribution suffix extendedRealizes probe factor
          factorNonnegative sensitive)
      (CCL.FiniteMeasure.prefixFamilyProbeExpectationBound distribution
        probe factor factorNonnegative sensitive) :=
  CCL.FiniteMeasure.extendedPrefixFamilyProbeExpectationBound_refines
    distribution suffix extendedRealizes probe factor factorNonnegative
      sensitive

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      CCL.FiniteMeasure.requiredProbeBlockCount (target / 2) factor ≤
        atom.item.blocks.length) :
    (CCL.FiniteMeasure.prefixFamilyProbeExpectationBound distribution
      probe factor factorPositive.le sensitive).width < target :=
  CCL.FiniteMeasure.prefixFamilyProbeExpectationBound_width_lt_requested
    distribution probe factor factorPositive sensitive target
      targetPositive enough

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) :
    (CCL.FiniteMeasure.prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).width =
      distribution.probability
        (CCL.FiniteMeasure.prefixFamilyThresholdUnresolvedEvent probe factor
          factorNonnegative sensitive threshold) :=
  CCL.FiniteMeasure.prefixFamilyThresholdBound_width distribution probe
    factor factorNonnegative sensitive threshold

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate)
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (CCL.FiniteMeasure.prefixFamilyThresholdBound distribution probe factor
      factorNonnegative sensitive threshold).Contains
      (distribution.probability
        (atLeastEvent threshold fun certificate => probe (points certificate))) :=
  CCL.FiniteMeasure.prefixFamilyThresholdBound_contains distribution probe
    factor factorNonnegative sensitive threshold points pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Bound)
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (CCL.FiniteMeasure.prefixFamilyWithinBoundProbability distribution probe
      factor factorNonnegative sensitive target).Contains
      (distribution.probability
        (withinBoundEvent target fun certificate =>
          probe (points certificate))) :=
  CCL.FiniteMeasure.prefixFamilyWithinBoundProbability_contains distribution
    probe factor factorNonnegative sensitive target points pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate)
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (CCL.FiniteMeasure.prefixFamilyProbeCumulativeBound distribution probe
      factor factorNonnegative sensitive threshold).Contains
      ((distribution.map fun certificate => probe (points certificate))
        |>.cumulative threshold) :=
  CCL.FiniteMeasure.prefixFamilyProbeCumulativeBound_contains distribution
    probe factor factorNonnegative sensitive threshold points pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (lower upper : Coordinate) (order : lower ≤ upper)
    (lowerMass : (1 / 2 : Coordinate) <
      (CCL.FiniteMeasure.prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive lower).lower)
    (upperMass : (1 / 2 : Coordinate) ≤
      (CCL.FiniteMeasure.prefixFamilyThresholdBound distribution
        (CCL.FiniteMeasure.negProbe probe) factor factorNonnegative
        (CCL.FiniteMeasure.negProbe_sensitive probe factor sensitive)
        (-upper)).lower)
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (CCL.FiniteMeasure.quantileCutBound lower upper order).Contains
      ((distribution.map fun certificate => probe (points certificate))
        |>.median) :=
  CCL.FiniteMeasure.prefixFamilyProbeMedian_mem_quantileCutBound distribution
    probe factor factorNonnegative sensitive lower upper order lowerMass
    upperMass points pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (suffix : CCL.FiniteMeasure.CompletedPrefixCertificate →
      List CCL.FiniteMeasure.Block)
    (extendedRealizes : ∀ certificate,
      CCL.Cylinder.Realizes
        (certificate.blocks ++ suffix certificate) certificate.witness)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) :
    Bound.Refines
      (eventBound
        (CCL.FiniteMeasure.extendedPrefixFamilyThresholdFrontier
          distribution suffix extendedRealizes probe factor
            factorNonnegative sensitive threshold))
      (CCL.FiniteMeasure.prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive threshold) :=
  CCL.FiniteMeasure.extendedPrefixFamilyThresholdFrontier_refines
    distribution suffix extendedRealizes probe factor factorNonnegative
      sensitive threshold

example {ι : Type} (process : CCL.FiniteMeasure.PrefixFamilyProcess ι)
    (distribution : Distribution ι)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbeThresholdProcess distribution probe factor factorPositive
      sensitive threshold margin marginPositive separated).bound
      ((process.toProbeThresholdProcess distribution probe factor
        factorPositive sensitive threshold margin marginPositive separated)
        |>.request state epsilon positive)).width = 0 :=
  process.request_probeThreshold_width_eq_zero distribution probe factor
    factorPositive sensitive threshold margin marginPositive separated
    state epsilon positive

example {ι : Type} (process : CCL.FiniteMeasure.PrefixFamilyProcess ι)
    (distribution : Distribution ι)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ probe (process.witness atom.item) ∨
        probe (process.witness atom.item) + margin ≤ threshold)
    (state : process.State) (points : ι → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbeThresholdProcess distribution probe factor factorPositive
      sensitive threshold margin marginPositive separated).bound state).Contains
      (distribution.probability
        (atLeastEvent threshold fun item => probe (points item))) :=
  process.probability_mem_toProbeThresholdProcess_bound distribution probe
    factor factorPositive sensitive threshold margin marginPositive separated
    state points pointsRealize

example {ι : Type} (process : CCL.FiniteMeasure.PrefixFamilyProcess ι)
    (distribution : Distribution ι)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbeExpectationProcess distribution probe factor
      factorPositive sensitive).bound
      ((process.toProbeExpectationProcess distribution probe factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  process.request_probeExpectation_width_lt distribution probe factor
    factorPositive sensitive state epsilon positive

example {ι : Type} (process : CCL.FiniteMeasure.PrefixFamilyProcess ι)
    (distribution : Distribution ι)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (points : ι → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbeExpectationProcess distribution probe factor
      factorPositive sensitive).bound state).Contains
        (distribution.expectation fun item => probe (points item)) :=
  process.expectation_mem_probeExpectationProcess_bound distribution
    probe factor factorPositive sensitive state points pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation
          (CCL.FiniteMeasure.poweredProbe probe exponent left)
          (CCL.FiniteMeasure.poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (CCL.FiniteMeasure.prefixFamilyProbePoweredLpBound distribution
      probe exponent factor factorNonnegative sensitive).width =
      distribution.expectation fun certificate =>
        2 * (factor *
          CCL.FiniteMeasure.cylinderSpread certificate.blocks) :=
  CCL.FiniteMeasure.prefixFamilyProbePoweredLpBound_width distribution
    probe exponent factor factorNonnegative sensitive

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation
          (CCL.FiniteMeasure.poweredProbe probe exponent left)
          (CCL.FiniteMeasure.poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    distribution.probability
        (separationAtLeast threshold
          (fun certificate => probe (points certificate)) (fun _ => 0)) ≤
      (CCL.FiniteMeasure.prefixFamilyProbePoweredLpBound distribution probe
        exponent factor factorNonnegative sensitive).upper /
          threshold ^ exponent :=
  CCL.FiniteMeasure.prefixFamilyProbe_tailProbability_le_upper_div
    distribution probe exponent factor factorNonnegative sensitive threshold
    thresholdPositive points pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate) (center : Coordinate)
    (exponent : Nat) (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation
          (CCL.FiniteMeasure.poweredDeviationProbe probe center exponent left)
          (CCL.FiniteMeasure.poweredDeviationProbe probe center exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    distribution.probability
        (separationAtLeast threshold
          (fun certificate => probe (points certificate))
          (fun _ => center)) ≤
      (CCL.FiniteMeasure.prefixFamilyProbePoweredDeviationBound distribution
        probe center exponent factor factorNonnegative sensitive).upper /
          threshold ^ exponent :=
  CCL.FiniteMeasure.prefixFamilyProbe_deviationProbability_le_upper_div
    distribution probe center exponent factor factorNonnegative sensitive
    threshold thresholdPositive points pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (squareFactor : Coordinate) (squareFactorNonnegative : 0 ≤ squareFactor)
    (squareSensitive : ∀ left right,
      rationalSeparation
          (CCL.FiniteMeasure.squareProbe probe left)
          (CCL.FiniteMeasure.squareProbe probe right) ≤
        squareFactor * CCL.Chordal.chordalSq left right)
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (CCL.FiniteMeasure.prefixFamilyProbeVarianceBound distribution probe
      meanFactor meanFactorNonnegative meanSensitive squareFactor
      squareFactorNonnegative squareSensitive).Contains
      (distribution.variance fun certificate => probe (points certificate)) :=
  CCL.FiniteMeasure.prefixFamilyProbeVarianceBound_contains distribution probe
    meanFactor meanFactorNonnegative meanSensitive squareFactor
    squareFactorNonnegative squareSensitive points pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorNonnegative : 0 ≤ meanFactor)
    (meanSensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (deviationFactor : Coordinate)
    (deviationFactorNonnegative : 0 ≤ deviationFactor)
    (deviationSensitive : ∀ left right,
      rationalSeparation
          (CCL.FiniteMeasure.poweredDeviationProbe probe
            (CCL.FiniteMeasure.prefixFamilyProbeWitnessExpectation
              distribution probe) 2 left)
          (CCL.FiniteMeasure.poweredDeviationProbe probe
            (CCL.FiniteMeasure.prefixFamilyProbeWitnessExpectation
              distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (CCL.FiniteMeasure.prefixFamilyProbeCenteredVarianceBound distribution
      probe meanFactor deviationFactor deviationFactorNonnegative
      deviationSensitive).Contains
      (distribution.variance fun certificate => probe (points certificate)) :=
  CCL.FiniteMeasure.prefixFamilyProbeCenteredVarianceBound_contains
    distribution probe meanFactor meanFactorNonnegative meanSensitive
    deviationFactor deviationFactorNonnegative deviationSensitive points
    pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (leftPoints rightPoints :
      CCL.FiniteMeasure.CompletedPrefixCertificate →
        CCL.FiniteMeasure.Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    distribution.l1Distance
        (fun certificate => probe (leftPoints certificate))
        (fun certificate => probe (rightPoints certificate)) ≤
      distribution.expectation fun certificate =>
        factor * CCL.FiniteMeasure.cylinderSpread certificate.blocks :=
  CCL.FiniteMeasure.prefixFamilyProbe_l1Distance_le distribution probe factor
    factorNonnegative sensitive leftPoints rightPoints leftRealizes
    rightRealizes

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (leftPoints rightPoints :
      CCL.FiniteMeasure.CompletedPrefixCertificate →
        CCL.FiniteMeasure.Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (rightPoints atom.item)) :
    (CCL.FiniteMeasure.prefixFamilyProbeLawCoupling distribution probe
      leftPoints rightPoints).transportCost rationalSeparation ≤
        distribution.expectation fun certificate =>
          factor * CCL.FiniteMeasure.cylinderSpread certificate.blocks :=
  CCL.FiniteMeasure.prefixFamilyProbeLawCoupling_transportCost_le
    distribution probe factor factorNonnegative sensitive leftPoints
    rightPoints leftRealizes rightRealizes

example {ι : Type} (distribution : Distribution ι)
    (blocks : List CCL.FiniteMeasure.Block)
    (witness : CCL.FiniteMeasure.Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : ι → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    distribution.variance (fun item => probe (points item)) ≤
      (factor * CCL.FiniteMeasure.cylinderSpread blocks) ^ 2 :=
  CCL.FiniteMeasure.realizedProbeVariance_le_radius_sq distribution blocks
    witness witnessRealizes points pointsRealize probe factor
    factorNonnegative sensitive

example {ι : Type} (distribution : Distribution ι)
    (blocks : List CCL.FiniteMeasure.Block)
    (witness : CCL.FiniteMeasure.Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : ι → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : CCL.FiniteMeasure.requiredProbeBlockCount
      (CCL.FiniteMeasure.PrefixFamilyProcess.centeredVarianceMeanTarget target)
        factor ≤ blocks.length) :
    distribution.variance (fun item => probe (points item)) < target :=
  CCL.FiniteMeasure.realizedProbeVariance_lt_of_requested distribution blocks
    witness witnessRealizes points pointsRealize probe factor factorPositive
    sensitive target targetPositive enough

example {ι : Type} (distribution : Distribution ι)
    (blocks : List CCL.FiniteMeasure.Block)
    (witness : CCL.FiniteMeasure.Proj)
    (witnessRealizes : CCL.Cylinder.Realizes blocks witness)
    (points : ι → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes blocks (points atom.item))
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (enough : CCL.FiniteMeasure.requiredProbeBlockCount threshold factor ≤
      blocks.length) :
    distribution.probability
        (separationAtLeast threshold
          (fun item => probe (points item)) (fun _ => probe witness)) = 0 :=
  CCL.FiniteMeasure.realizedProbe_deviationProbability_eq_zero_of_requested
    distribution blocks witness witnessRealizes points pointsRealize probe
    factor factorPositive sensitive threshold thresholdPositive enough

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (left right : CCL.FiniteMeasure.Proj → Coordinate)
    (leftData : CCL.FiniteMeasure.ProbeVarianceData left)
    (rightData : CCL.FiniteMeasure.ProbeVarianceData right)
    (sumData : CCL.FiniteMeasure.ProbeVarianceData
      (CCL.FiniteMeasure.addProbe left right))
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (CCL.FiniteMeasure.prefixFamilyProbeCovarianceBound distribution left right
      leftData rightData sumData).Contains
      (distribution.covariance
        (fun certificate => left (points certificate))
        (fun certificate => right (points certificate))) :=
  CCL.FiniteMeasure.prefixFamilyProbeCovarianceBound_contains distribution
    left right leftData rightData sumData points pointsRealize

example {ι : Type} (process : CCL.FiniteMeasure.PrefixFamilyProcess ι)
    (distribution : Distribution ι)
    (probe : CCL.FiniteMeasure.Proj → Coordinate) (exponent : Nat)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation
          (CCL.FiniteMeasure.poweredProbe probe exponent left)
          (CCL.FiniteMeasure.poweredProbe probe exponent right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbePoweredLpProcess distribution probe exponent factor
      factorPositive sensitive).bound
      ((process.toProbePoweredLpProcess distribution probe exponent factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  process.request_probePoweredLp_width_lt distribution probe exponent
    factor factorPositive sensitive state epsilon positive

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate) (factor : Coordinate) :
    (CCL.FiniteMeasure.prefixFamilyProbeEssentialMaximumBound
      distribution probe factor).width =
        2 * CCL.FiniteMeasure.prefixFamilyProbeEssentialMaximumRadius
          distribution factor :=
  CCL.FiniteMeasure.prefixFamilyProbeEssentialMaximumBound_width
    distribution probe factor

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (points : CCL.FiniteMeasure.CompletedPrefixCertificate →
      CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (CCL.FiniteMeasure.prefixFamilyProbeEssentialMaximumBound
      distribution probe factor).Contains
        (distribution.essentialMaximumMagnitude fun certificate =>
          probe (points certificate)) :=
  CCL.FiniteMeasure.prefixFamilyProbeEssentialMaximumBound_contains
    distribution probe factor factorNonnegative sensitive
      points pointsRealize

example
    (distribution : Distribution
      CCL.FiniteMeasure.CompletedPrefixCertificate)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (target : Coordinate) (targetPositive : 0 < target)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      CCL.FiniteMeasure.requiredProbeBlockCount (target / 4) factor ≤
        atom.item.blocks.length) :
    (CCL.FiniteMeasure.prefixFamilyProbeEssentialMaximumBound
      distribution probe factor).width < target :=
  CCL.FiniteMeasure.prefixFamilyProbeEssentialMaximumBound_width_lt_requested
    distribution probe factor factorPositive sensitive target
      targetPositive enough

example {ι : Type} (process : CCL.FiniteMeasure.PrefixFamilyProcess ι)
    (distribution : Distribution ι)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (points : ι → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbeEssentialMaximumProcess distribution probe factor
      factorPositive sensitive).bound state).Contains
        (distribution.essentialMaximumMagnitude fun item =>
          probe (points item)) :=
  process.essentialMaximum_mem_toProbeEssentialMaximumProcess_bound
    distribution probe factor factorPositive sensitive state
      points pointsRealize

example {ι : Type} (process : CCL.FiniteMeasure.PrefixFamilyProcess ι)
    (distribution : Distribution ι)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbeEssentialMaximumProcess distribution probe factor
      factorPositive sensitive).bound
      ((process.toProbeEssentialMaximumProcess distribution probe factor
        factorPositive sensitive).request state epsilon positive)).width <
      epsilon :=
  process.request_probeEssentialMaximum_width_lt distribution probe factor
    factorPositive sensitive state epsilon positive

example {ι : Type} (process : CCL.FiniteMeasure.PrefixFamilyProcess ι)
    (distribution : Distribution ι)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (deviationFactor : Coordinate) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      rationalSeparation
          (CCL.FiniteMeasure.poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 left)
          (CCL.FiniteMeasure.poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (state : process.State) (points : ι → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbeCenteredVarianceProcess distribution probe meanFactor
      meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
      deviationSensitive).bound state).Contains
        (distribution.variance fun item => probe (points item)) :=
  process.variance_mem_toProbeCenteredVarianceProcess_bound distribution probe
    meanFactor meanFactorPositive meanSensitive deviationFactor
    deviationFactorPositive deviationSensitive state points pointsRealize

example {ι : Type} (process : CCL.FiniteMeasure.PrefixFamilyProcess ι)
    (distribution : Distribution ι)
    (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (deviationFactor : Coordinate) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      rationalSeparation
          (CCL.FiniteMeasure.poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 left)
          (CCL.FiniteMeasure.poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbeCenteredVarianceProcess distribution probe meanFactor
      meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
      deviationSensitive).bound
      ((process.toProbeCenteredVarianceProcess distribution probe meanFactor
        meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
        deviationSensitive).request state epsilon positive)).width < epsilon :=
  process.request_probeCenteredVariance_width_lt distribution probe meanFactor
    meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
    deviationSensitive state epsilon positive

example {ι : Type} (process : CCL.FiniteMeasure.PrefixFamilyProcess ι)
    (distribution : Distribution ι)
    (left right : CCL.FiniteMeasure.Proj → Coordinate)
    (leftData : CCL.FiniteMeasure.ProbeCenteredVarianceProcessData process
      distribution left)
    (rightData : CCL.FiniteMeasure.ProbeCenteredVarianceProcessData process
      distribution right)
    (sumData : CCL.FiniteMeasure.ProbeCenteredVarianceProcessData process
      distribution (CCL.FiniteMeasure.addProbe left right))
    (state : (process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).State)
    (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbeCovarianceProcess distribution left right leftData
      rightData sumData).bound
      ((process.toProbeCovarianceProcess distribution left right leftData
        rightData sumData).request state epsilon positive)).width < epsilon :=
  process.request_probeCovariance_width_lt distribution left right leftData
    rightData sumData state epsilon positive

/-! The concrete encoder-to-measure bridge retains the exact homogeneous
coordinates emitted by the executable integral encoder. -/

def encodedThreePlusFourIOverFive : CCL.Encoder.Frac :=
  ⟨⟨3, 4⟩, ⟨5, 0⟩, by decide⟩

theorem encodedThreePlusFourIOverFive_num_ne :
    encodedThreePlusFourIOverFive.num ≠ 0 := by decide

example :
    CCL.FiniteMeasure.chordalOmegaProbe
        (CCL.Encoder.encodeBlocks encodedThreePlusFourIOverFive
          encodedThreePlusFourIOverFive_num_ne).point =
      CCL.FiniteMeasure.chordalOmegaProbe
        (CCL.Proj.affine encodedThreePlusFourIOverFive.value) :=
  CCL.FiniteMeasure.encodedChordalOmegaProbe_eq_value
    encodedThreePlusFourIOverFive encodedThreePlusFourIOverFive_num_ne

example : Distribution.EvaluationEquivalent
    (fairCoin.map fun _ => CCL.FiniteMeasure.chordalOmegaProbe
      (CCL.Encoder.encodeBlocks encodedThreePlusFourIOverFive
        encodedThreePlusFourIOverFive_num_ne).point)
    (fairCoin.map fun _ => CCL.FiniteMeasure.chordalOmegaProbe
      (CCL.Proj.affine encodedThreePlusFourIOverFive.value)) :=
  CCL.FiniteMeasure.encodedChordalOmegaProbeLaw_evaluationEquivalent
    fairCoin (fun _ => encodedThreePlusFourIOverFive)
      (fun _ => encodedThreePlusFourIOverFive_num_ne)

example : CCL.FiniteMeasure.encodedChordalOmegaEstimatorBlockCount
    (1 / 2) = 8 := by decide

example : CCL.FiniteMeasure.encodedChordalOmegaEstimatorSampleCount
    (1 / 2) (1 / 10) = 161 := by decide

example (probe : CCL.FiniteMeasure.Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    (CCL.FiniteMeasure.encodedProjectivePrefixProbeBound
      encodedThreePlusFourIOverFive encodedThreePlusFourIOverFive_num_ne
      probe factor factorNonnegative sensitive).Contains
        (probe (CCL.Proj.affine encodedThreePlusFourIOverFive.value)) :=
  CCL.FiniteMeasure.encodedProjectivePrefixProbeBound_contains_value
    encodedThreePlusFourIOverFive encodedThreePlusFourIOverFive_num_ne
      probe factor factorNonnegative sensitive

example :
    rationalSeparation
        (fairCoin.expectation fun _ =>
          CCL.FiniteMeasure.chordalOmegaProbe
            (CCL.Encoder.encodeBlocks encodedThreePlusFourIOverFive
              encodedThreePlusFourIOverFive_num_ne).point)
        (fairCoin.expectation fun _ =>
          CCL.FiniteMeasure.chordalOmegaProbe
            (CCL.Proj.affine encodedThreePlusFourIOverFive.value)) ^ 2 ≤
      fairCoin.expectation fun _ =>
        2 * CCL.FiniteMeasure.cylinderSpread
          (CCL.Encoder.encodeBlocks encodedThreePlusFourIOverFive
            encodedThreePlusFourIOverFive_num_ne).blocks := by
  apply CCL.FiniteMeasure.encodedChordalOmegaProbe_expectation_separation_sq_le
    fairCoin (fun _ => encodedThreePlusFourIOverFive)
      (fun _ => encodedThreePlusFourIOverFive_num_ne)
      (fun _ => (CCL.Encoder.encodeBlocks encodedThreePlusFourIOverFive
        encodedThreePlusFourIOverFive_num_ne).point)
  intro atom member
  exact CCL.Encoder.encodeBlocks_realizes encodedThreePlusFourIOverFive
    encodedThreePlusFourIOverFive_num_ne

example {index : Type} (distribution : Distribution index)
    (points : index → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks encodedThreePlusFourIOverFive
          encodedThreePlusFourIOverFive_num_ne).blocks
        (points atom.item)) :
    distribution.variance
        (fun item => CCL.FiniteMeasure.chordalOmegaProbe (points item)) ≤
      2 * CCL.FiniteMeasure.cylinderSpread
        (CCL.Encoder.encodeBlocks encodedThreePlusFourIOverFive
          encodedThreePlusFourIOverFive_num_ne).blocks :=
  CCL.FiniteMeasure.encodedChordalOmegaProbeVariance_le
    encodedThreePlusFourIOverFive encodedThreePlusFourIOverFive_num_ne
    distribution points pointsRealize

example {index : Type} (distribution : Distribution index)
    (points : index → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks encodedThreePlusFourIOverFive
          encodedThreePlusFourIOverFive_num_ne).blocks
        (points atom.item))
    (threshold : Coordinate) (thresholdPositive : 0 < threshold)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (Distribution.requiredChebyshevSampleCount
          (CCL.FiniteMeasure.encodedProbeVarianceBudget
            encodedThreePlusFourIOverFive
            encodedThreePlusFourIOverFive_num_ne 2)
          threshold failure)).probability
      (distribution.sampleMeanDeviation
        (Distribution.requiredChebyshevSampleCount
          (CCL.FiniteMeasure.encodedProbeVarianceBudget
            encodedThreePlusFourIOverFive
            encodedThreePlusFourIOverFive_num_ne 2)
          threshold failure)
        (fun item => CCL.FiniteMeasure.chordalOmegaProbe (points item))
        threshold) < failure :=
  CCL.FiniteMeasure.encodedChordalOmegaProbe_iidSamples_sampleMean_deviationProbability_lt_requested
    encodedThreePlusFourIOverFive encodedThreePlusFourIOverFive_num_ne
    distribution points pointsRealize threshold thresholdPositive failure
    failurePositive

example {index : Type} (distribution : Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (threshold margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ atom, atom ∈ distribution.atoms →
      threshold + margin ≤ CCL.FiniteMeasure.chordalOmegaProbe
          (CCL.Proj.affine (fraction atom.item).value) ∨
        CCL.FiniteMeasure.chordalOmegaProbe
            (CCL.Proj.affine (fraction atom.item).value) + margin ≤ threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      CCL.FiniteMeasure.requiredSquaredThresholdBlockCount margin 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (leftPoints rightPoints : index → CCL.FiniteMeasure.Proj)
    (leftRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (leftPoints atom.item))
    (rightRealizes : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (rightPoints atom.item)) :
    distribution.probability
        (atLeastEvent threshold fun item =>
          CCL.FiniteMeasure.chordalOmegaProbe (leftPoints item)) =
      distribution.probability
        (atLeastEvent threshold fun item =>
          CCL.FiniteMeasure.chordalOmegaProbe (rightPoints item)) :=
  CCL.FiniteMeasure.encodedChordalOmegaProbe_thresholdProbabilities_eq_of_margin
    distribution fraction numeratorNonzero threshold margin marginPositive
    separated enough leftPoints rightPoints leftRealizes rightRealizes

example {index : Type} (distribution : Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      CCL.FiniteMeasure.requiredSquaredProbeBlockCount epsilon 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) :
    rationalSeparation
        ((distribution.map fun item =>
          CCL.FiniteMeasure.chordalOmegaProbe (points item)).lowerQuantile
            level levelPositive levelAtMostOne)
        ((distribution.map fun item => CCL.FiniteMeasure.chordalOmegaProbe
          (CCL.Proj.affine (fraction item).value)).lowerQuantile
            level levelPositive levelAtMostOne) ≤ epsilon :=
  CCL.FiniteMeasure.encodedChordalOmegaProbe_lowerQuantile_separation_le_requested
    distribution fraction numeratorNonzero epsilon epsilonPositive enough
    points pointsRealize level levelPositive levelAtMostOne

example {index : Type} (distribution : Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      CCL.FiniteMeasure.requiredSquaredProbeBlockCount epsilon 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    rationalSeparation
        (distribution.variance fun item =>
          CCL.FiniteMeasure.chordalOmegaProbe (points item))
        (distribution.variance fun item =>
          CCL.FiniteMeasure.chordalOmegaProbe
            (CCL.Proj.affine (fraction item).value)) ≤ 4 * epsilon :=
  CCL.FiniteMeasure.encodedChordalOmegaProbe_variance_separation_le_requested
    distribution fraction numeratorNonzero epsilon epsilonPositive enough
    points pointsRealize

example {index : Type} (distribution : Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      CCL.FiniteMeasure.requiredSquaredProbeBlockCount epsilon 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (points : index → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item)) :
    (CCL.FiniteMeasure.encodedProbeLawCoupling distribution fraction
      CCL.FiniteMeasure.chordalOmegaProbe points).transportCost
        (fun left right => rationalSeparation left right ^ 2) < epsilon ^ 2 :=
  CCL.FiniteMeasure.encodedChordalOmegaProbeLawCoupling_squaredTransportCost_lt_requested
    distribution fraction numeratorNonzero epsilon epsilonPositive enough
    points pointsRealize

example {index : Type} (distribution : Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (points : index → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (epsilon : Coordinate) (epsilonPositive : 0 < epsilon)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      CCL.FiniteMeasure.encodedChordalOmegaEstimatorBlockCount epsilon ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (failure : Coordinate) (failurePositive : 0 < failure) :
    (distribution.iidSamples
        (CCL.FiniteMeasure.encodedChordalOmegaEstimatorSampleCount
          epsilon failure)).probability
      (CCL.FiniteMeasure.encodedChordalOmegaSampleMeanTargetDeviation
        distribution fraction
        (CCL.FiniteMeasure.encodedChordalOmegaEstimatorSampleCount
          epsilon failure)
        points epsilon) < failure :=
  CCL.FiniteMeasure.encodedChordalOmegaSampleMean_targetDeviationProbability_lt_requested
    distribution fraction numeratorNonzero points pointsRealize epsilon
    epsilonPositive enough failure failurePositive

example :
    CCL.FiniteMeasure.requiredEncodedChordalOmegaThresholdGridSampleCount
      (fun _ : Bool =>
        (CCL.Encoder.encodeBlocks encodedThreePlusFourIOverFive
          encodedThreePlusFourIOverFive_num_ne).point)
      [0, 1] (1 / 10) (1 / 20) = 1501 := by decide

example {index : Type} (distribution : Distribution index)
    (fraction : index → CCL.Encoder.Frac)
    (numeratorNonzero : ∀ item, (fraction item).num ≠ 0)
    (points : index → CCL.FiniteMeasure.Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.ProjectiveRealizes
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks
        (points atom.item))
    (thresholds : List Coordinate)
    (margin : Coordinate) (marginPositive : 0 < margin)
    (separated : ∀ threshold, threshold ∈ thresholds →
      ∀ atom, atom ∈ distribution.atoms →
        threshold + margin ≤ CCL.FiniteMeasure.chordalOmegaProbe
            (CCL.Proj.affine (fraction atom.item).value) ∨
          CCL.FiniteMeasure.chordalOmegaProbe
              (CCL.Proj.affine (fraction atom.item).value) + margin ≤
            threshold)
    (enough : ∀ atom, atom ∈ distribution.atoms →
      CCL.FiniteMeasure.requiredSquaredThresholdBlockCount margin 2 ≤
        (CCL.Encoder.encodeBlocks (fraction atom.item)
          (numeratorNonzero atom.item)).blocks.length)
    (count : Nat) (tolerance : Coordinate) (tolerancePositive : 0 < tolerance)
    (sample : List index)
    (outside :
      CCL.FiniteMeasure.encodedChordalOmegaThresholdGridDeviation
        distribution points thresholds count tolerance sample = false) :
    CCL.FiniteMeasure.EncodedChordalOmegaThresholdGridTargetWithin
      distribution fraction points thresholds count tolerance sample :=
  CCL.FiniteMeasure.encodedChordalOmegaThresholdGridTargetWithin_of_outside
    distribution fraction numeratorNonzero points pointsRealize thresholds
    margin marginPositive separated enough count tolerance tolerancePositive
    sample outside

end FiniteMeasure.Examples
