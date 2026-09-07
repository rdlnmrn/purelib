import CCL.Riemann.ExplicitLegendrePreparedPeriods
import CCL.Riemann.LegendrePeriodMonodromy

/-!
# Retryable normalization of the explicit Legendre periods

Normalization is staged behind the exact finite check it genuinely needs.
A bounded scan either returns a proof-bearing tail separation for the
canonical one-by-one inverse scalar or ordinary finite failure.  A successful
result constructs normalized period data without requiring nonvanishing of
discarded coarse centres.  The explicit standard-loop facade lives in the
downstream `ExplicitLegendreNormalizedMonodromy` module, so importing this
acquisition layer does not initialize the much larger loop geometry.
-/

namespace CCL.Riemann.ExplicitLegendreNormalizedAcquisition

open CCL.Riemann.PeriodMatrix

abbrev Coordinate := RFAP.ConstructiveFraction.Rational

/-- Internal refinement-program index selected by the canonical public
sampler for one A-period request.  This can be much larger than the public
index: for the displayed Legendre preflight, public sample zero starts at
internal refinement twenty-five. -/
def aPeriodInternalIndex
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (sampleIndex : Nat) : Nat :=
  CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodModelIndex context
    sampleIndex

/-- Number of direct refinement states sufficient for every public A-period
sample strictly below `sampleBound`.  The empty public prefix allocates no
states; a nonempty prefix retains every state through the internal index of
its final public sample. -/
def requiredAPeriodCacheCount
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext) :
    Nat -> Nat
  | 0 => 0
  | sampleBound + 1 => aPeriodInternalIndex context sampleBound + 1

/-- The originating refinement indices selected by successive public samples
are monotone. -/
theorem aPeriodInternalIndex_step_le
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (sampleIndex : Nat) :
    aPeriodInternalIndex context sampleIndex <=
      aPeriodInternalIndex context (sampleIndex + 1) := by
  unfold aPeriodInternalIndex
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodModelIndex
  rw [CCL.ProgressiveSampling.stateAt_succ]
  simpa only [CCL.ProgressiveApproximation.Approximation.toProcess] using
    (CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfContext
      context).integral.approximation.refineIndex_ge _ _
      (CCL.ProgressiveSampling.refinementTarget_pos (sampleIndex + 1))

theorem aPeriodInternalIndex_mono
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    {earlier later : Nat} (order : earlier <= later) :
    aPeriodInternalIndex context earlier <=
      aPeriodInternalIndex context later := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  induction extra with
  | zero => rw [Nat.add_zero]
  | succ extra inductionHypothesis =>
      have step := aPeriodInternalIndex_step_le context (earlier + extra)
      have previous := inductionHypothesis (Nat.le_add_right earlier extra)
      rw [show earlier + (extra + 1) = earlier + extra + 1 by ring1]
      exact previous.trans step

/-- Every public sample in the advertised prefix maps strictly inside the
direct-state cache count. -/
theorem aPeriodInternalIndex_lt_required
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    {sampleIndex sampleBound : Nat} (within : sampleIndex < sampleBound) :
    aPeriodInternalIndex context sampleIndex <
      requiredAPeriodCacheCount context sampleBound := by
  cases sampleBound with
  | zero => exact (Nat.not_lt_zero sampleIndex within).elim
  | succ finalIndex =>
      change aPeriodInternalIndex context sampleIndex <
        aPeriodInternalIndex context finalIndex + 1
      exact Nat.lt_succ_of_le
        (aPeriodInternalIndex_mono context (Nat.le_of_lt_succ within))

/-- Existentially sized A-state cache.  Separating its internal refinement
count from the public normalization bound prevents the nested CCL sampler
from falling through a cache sized only by public sample indices. -/
structure RetainedAPeriodCache
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext) where
  count : Nat
  value :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.APeriodCache context count

namespace RetainedAPeriodCache

def canonical
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (count : Nat) : RetainedAPeriodCache context where
  count := count
  value :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodCacheOfContext context
      count

/-- Extend the direct-state prefix while retaining every old thunk. -/
def extend
    {context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext}
    (cache : RetainedAPeriodCache context) (extra : Nat) :
    RetainedAPeriodCache context where
  count := cache.count + extra
  value := cache.value.extend extra

/-- An extension reads every old direct model through the identical stored
thunk. -/
theorem extend_model_of_lt
    {context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext}
    (cache : RetainedAPeriodCache context) (extra index : Nat)
    (within : index < cache.count) :
    (cache.extend extra).value.model index = cache.value.model index :=
  cache.value.extend_model_of_lt extra index within

end RetainedAPeriodCache

/-! Keep the large prepared A-cycle behind an explicit retained cache.  A
closed global matrix value is initialized eagerly by compiled clients, even
when no normalization request is made. -/
def normalizationMatrix
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) :=
  CCL.Riemann.ExplicitLegendrePreparedPeriods.aMatrixOfContextWithCache
    context cache.value

/-- Replacing the direct models by a retained cache leaves the public
sampler's originating refinement index unchanged. -/
theorem cachedAPeriodInternalIndex_eq
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) (sampleIndex : Nat) :
    let program :=
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
        context cache.value
    CCL.ProgressiveSampling.stateAt program.integral.approximation.toProcess
        (show program.integral.approximation.toProcess.State from (0 : Nat))
          sampleIndex =
      aPeriodInternalIndex context sampleIndex := by
  dsimp only
  unfold aPeriodInternalIndex
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodModelIndex
  induction sampleIndex with
  | zero => rfl
  | succ sampleIndex inductionHypothesis =>
      rw [CCL.ProgressiveSampling.stateAt_succ,
        CCL.ProgressiveSampling.stateAt_succ, inductionHypothesis]
      rfl

/-- The real lower endpoint read through a retained A cache bounds exactly
the public coherent sample selected by the same request. -/
theorem cachedAPeriodSampleRealLower_le
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) (sampleIndex : Nat) :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleRealLowerOfCache
        context cache.value sampleIndex <=
      ((CCL.ProgressiveSampling.approximation
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
          context cache.value).output.name).sample sampleIndex).re := by
  let program :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
      context cache.value
  change
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleRealLowerOfCache
        context cache.value sampleIndex <=
      (cache.value.model
        (CCL.ProgressiveSampling.stateAt
          program.integral.approximation.toProcess
          (show program.integral.approximation.toProcess.State from (0 : Nat))
          sampleIndex)).integralSample.re
  rw [cachedAPeriodInternalIndex_eq context cache sampleIndex]
  exact
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleRealLowerOfCache_le_model
      context cache.value sampleIndex

/-- The sharp process-ball endpoint read through a retained A cache bounds
the exact public coherent sample selected by the same request. -/
theorem cachedAPeriodSampleBallRealLower_le
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) (sampleIndex : Nat) :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
        context cache.value sampleIndex <=
      ((CCL.ProgressiveSampling.approximation
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
          context cache.value).output.name).sample sampleIndex).re := by
  let program :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
      context cache.value
  change
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
        context cache.value sampleIndex <=
      (cache.value.model
        (CCL.ProgressiveSampling.stateAt
          program.integral.approximation.toProcess
          (show program.integral.approximation.toProcess.State from (0 : Nat))
          sampleIndex)).integralSample.re
  rw [cachedAPeriodInternalIndex_eq context cache sampleIndex]
  exact
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache_le_model
      context cache.value sampleIndex

/-- A theorem-facing literal certificate bounds the public sample read
through any retained cache for the same explicit context.  The cache equality
changes only runtime sharing; it does not rebase the certificate's direct
refinement index. -/
theorem cachedAPeriodPositiveLiteralRealLower_le
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) (sampleIndex : Nat)
    (certificate :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.APeriodPositiveLiteralRealLowerCertificate
        context sampleIndex) :
    certificate.lower <=
      ((CCL.ProgressiveSampling.approximation
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
          context cache.value).output.name).sample sampleIndex).re := by
  let program :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
      context cache.value
  change certificate.lower <=
    (cache.value.model
      (CCL.ProgressiveSampling.stateAt
        program.integral.approximation.toProcess
        (show program.integral.approximation.toProcess.State from (0 : Nat))
        sampleIndex)).integralSample.re
  rw [cachedAPeriodInternalIndex_eq context cache sampleIndex,
    cache.value.model_eq_compactSourceModel]
  exact certificate.lower_le_model

/-- A directional endpoint read through the retained cache bounds exactly the
same projection of the public coherent sample. -/
theorem cachedAPeriodSampleDirectionalLower_le
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context)
    (direction : RFAP.ConstructiveGaussian.Gaussian)
    (sampleIndex : Nat) :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleDirectionalLowerOfCache
        context cache.value direction sampleIndex <=
      direction.re *
          ((CCL.ProgressiveSampling.approximation
            (CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
              context cache.value).output.name).sample sampleIndex).re +
        direction.im *
          ((CCL.ProgressiveSampling.approximation
            (CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
              context cache.value).output.name).sample sampleIndex).im := by
  let program :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
      context cache.value
  change
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleDirectionalLowerOfCache
        context cache.value direction sampleIndex <=
      direction.re *
          (cache.value.model
            (CCL.ProgressiveSampling.stateAt
              program.integral.approximation.toProcess
              (show program.integral.approximation.toProcess.State from
                (0 : Nat)) sampleIndex)).integralSample.re +
        direction.im *
          (cache.value.model
            (CCL.ProgressiveSampling.stateAt
              program.integral.approximation.toProcess
              (show program.integral.approximation.toProcess.State from
                (0 : Nat)) sampleIndex)).integralSample.im
  rw [cachedAPeriodInternalIndex_eq context cache sampleIndex]
  exact
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleDirectionalLowerOfCache_le_model
      context cache.value direction sampleIndex

/-- Conservative inverse-tail clearance obtained from the sign-aware real
endpoint rather than by first evaluating the complete Gaussian sample. -/
def aPeriodRealTailClearance
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) (anchor : Nat) : Coordinate :=
  let lower :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleRealLowerOfCache
      context cache.value anchor
  (lower ^ 2) ^ 4 / 2 -
    CCL.FiniteGeometric.quarterRadius
      (canonicalScaledInverse (normalizationMatrix context cache)).scalar.errorScale
      anchor

/-- Positivity of the real endpoint makes the conservative clearance no
larger than the exact genus-one inverse-tail clearance. -/
theorem aPeriodRealTailClearance_le_oneByOneEntryTailClearanceAt
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) (anchor : Nat)
    (positive : 0 <
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleRealLowerOfCache
        context cache.value anchor) :
    aPeriodRealTailClearance context cache anchor <=
      oneByOneEntryTailClearanceAt (normalizationMatrix context cache)
        anchor := by
  let lower :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleRealLowerOfCache
      context cache.value anchor
  let sample :=
    (CCL.ProgressiveSampling.approximation
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
        context cache.value).output.name).sample anchor
  have lowerLeReal : lower <= sample.re :=
    cachedAPeriodSampleRealLower_le context cache anchor
  have lowerSqLe : lower ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq sample := by
    calc
      lower ^ 2 <= sample.re ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct positive.le lowerLeReal 2
      _ <= RFAP.ConstructiveGaussian.Gaussian.normSq sample := by
        unfold RFAP.ConstructiveGaussian.Gaussian.normSq
        exact le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct sample.im)
  have fourthPowerLe : (lower ^ 2) ^ 4 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq sample ^ 4 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct lower) lowerSqLe 4
  have halfLe : (lower ^ 2) ^ 4 / 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq sample ^ 4 / 2 := by
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      fourthPowerLe
        (RFAP.ConstructiveFraction.inv_pos_direct (by decide)).le
  change
    (lower ^ 2) ^ 4 / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse (normalizationMatrix context cache)).scalar.errorScale
          anchor <=
      RFAP.ConstructiveGaussian.Gaussian.normSq sample ^ 4 / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse (normalizationMatrix context cache)).scalar.errorScale
          anchor
  exact RFAP.ConstructiveFraction.sub_le_sub_right_direct halfLe _

/-- One positive rational lower-clearance check constructs the exact bounded
tail separation consumed by normalization.  No sample, bank, or inverse
matrix is recomputed in this proof. -/
def boundedSeparationOfAPeriodRealLower
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) {bound : Nat}
    (anchor : Nat) (within : anchor < bound)
    (lowerPositive : 0 <
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleRealLowerOfCache
        context cache.value anchor)
    (clearancePositive : 0 < aPeriodRealTailClearance context cache anchor) :
    BoundedScalarTailSeparationCertificate
      (normalizationMatrix context cache) bound where
  certificate :=
    { anchor := anchor
      tailPositive := by
        rw [← oneByOneEntryTailClearanceAt_eq_scalarTailClearanceAt]
        exact clearancePositive.trans_le
          (aPeriodRealTailClearance_le_oneByOneEntryTailClearanceAt
            context cache anchor lowerPositive) }
  anchor_lt := within

/-- Conservative inverse-tail clearance obtained from the sharper retained
coefficient process balls. -/
def aPeriodBallRealTailClearance
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) (anchor : Nat) : Coordinate :=
  let lower :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
      context cache.value anchor
  (lower ^ 2) ^ 4 / 2 -
    CCL.FiniteGeometric.quarterRadius
      (canonicalScaledInverse (normalizationMatrix context cache)).scalar.errorScale
      anchor

theorem aPeriodBallRealTailClearance_le_oneByOneEntryTailClearanceAt
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) (anchor : Nat)
    (positive : 0 <
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
        context cache.value anchor) :
    aPeriodBallRealTailClearance context cache anchor <=
      oneByOneEntryTailClearanceAt (normalizationMatrix context cache)
        anchor := by
  let lower :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
      context cache.value anchor
  let sample :=
    (CCL.ProgressiveSampling.approximation
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
        context cache.value).output.name).sample anchor
  have lowerLeReal : lower <= sample.re :=
    cachedAPeriodSampleBallRealLower_le context cache anchor
  have lowerSqLe : lower ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq sample := by
    calc
      lower ^ 2 <= sample.re ^ 2 :=
        RFAP.ConstructiveFraction.pow_le_pow_direct positive.le lowerLeReal 2
      _ <= RFAP.ConstructiveGaussian.Gaussian.normSq sample := by
        unfold RFAP.ConstructiveGaussian.Gaussian.normSq
        exact le_add_of_nonneg_right
          (RFAP.ConstructiveFraction.sq_nonneg_direct sample.im)
  have fourthPowerLe : (lower ^ 2) ^ 4 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq sample ^ 4 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct lower) lowerSqLe 4
  have halfLe : (lower ^ 2) ^ 4 / 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq sample ^ 4 / 2 := by
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      fourthPowerLe
        (RFAP.ConstructiveFraction.inv_pos_direct (by decide)).le
  change
    (lower ^ 2) ^ 4 / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse (normalizationMatrix context cache)).scalar.errorScale
          anchor <=
      RFAP.ConstructiveGaussian.Gaussian.normSq sample ^ 4 / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse (normalizationMatrix context cache)).scalar.errorScale
          anchor
  exact RFAP.ConstructiveFraction.sub_le_sub_right_direct halfLe _

/-- A positive sharp endpoint and one rational clearance check construct the
exact bounded separation consumed by normalization. -/
def boundedSeparationOfAPeriodBallRealLower
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) {bound : Nat}
    (anchor : Nat) (within : anchor < bound)
    (lowerPositive : 0 <
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
        context cache.value anchor)
    (clearancePositive : 0 <
      aPeriodBallRealTailClearance context cache anchor) :
    BoundedScalarTailSeparationCertificate
      (normalizationMatrix context cache) bound where
  certificate :=
    { anchor := anchor
      tailPositive := by
        rw [← oneByOneEntryTailClearanceAt_eq_scalarTailClearanceAt]
        exact clearancePositive.trans_le
          (aPeriodBallRealTailClearance_le_oneByOneEntryTailClearanceAt
            context cache anchor lowerPositive) }
  anchor_lt := within

/-- Entry-level anchor-zero clearance for the sharp real endpoint.  Unlike
the inverse-tail clearance, this is the exact finite obligation that promotes
one public A sample to a uniform lower bound for every public sample. -/
def aPeriodBallRealEntryTailClearanceAtZero
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) : Coordinate :=
  let lower :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
      context cache.value 0
  lower ^ 2 / 2 -
    CCL.FiniteGeometric.quarterRadius
      (oneByOneEntryApproximation
        (normalizationMatrix context cache)).errorScale 0

/-- Entry-level anchor-zero clearance for an arbitrary displayed rational
real lower endpoint.  This separates the generic normalization bridge from
the particular finite certificate that supplied the endpoint. -/
def aPeriodDisplayedRealEntryTailClearanceAtZero
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context) (lower : Coordinate) : Coordinate :=
  lower ^ 2 / 2 -
    CCL.FiniteGeometric.quarterRadius
      (oneByOneEntryApproximation
        (normalizationMatrix context cache)).errorScale 0

/-- One displayed positive real endpoint at public anchor zero constructs the
complete finite A-entry separation certificate.  The endpoint proof is a
named theorem input, so this adapter performs no bank, model, or coefficient
search. -/
def finiteAPeriodSeparationOfDisplayedRealLowerAtZero
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context)
    (lower : Coordinate) (lowerPositive : 0 < lower)
    (sampleLower : lower <=
      ((CCL.ProgressiveSampling.approximation
        (CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
          context cache.value).output.name).sample 0).re)
    (clearancePositive : 0 <
      aPeriodDisplayedRealEntryTailClearanceAtZero context cache lower) :
    FiniteOneByOneEntrySeparationCertificate
      (normalizationMatrix context cache) := by
  let direction : RFAP.ConstructiveGaussian.Gaussian := ⟨1, 0⟩
  apply FiniteOneByOneEntrySeparationCertificate.ofAnchorZeroDirectional
    direction (by decide) lower lowerPositive
  · simp only [direction, RFAP.ConstructiveGaussian.Gaussian.re,
      RFAP.ConstructiveGaussian.Gaussian.im, one_mul, zero_mul, add_zero]
    unfold oneByOneEntryApproximation normalizationMatrix
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aMatrixOfContextWithCache
    simp only [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
      CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed_sample]
    exact sampleLower
  · rw [show RFAP.ConstructiveGaussian.Gaussian.normSq direction = 1 by
      decide]
    change 0 < lower ^ 2 / 2 -
      CCL.FiniteGeometric.quarterRadius
        (oneByOneEntryApproximation
          (normalizationMatrix context cache)).errorScale 0 at clearancePositive
    simpa only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      show (1 : Coordinate)⁻¹ = 1 by decide,
      RFAP.ConstructiveFraction.mul_one_direct] using clearancePositive

/-- Specialization of the displayed-lower bridge to a checked, chunkable
literal coefficient certificate for public sample zero. -/
def finiteAPeriodSeparationOfPositiveLiteralRealLowerAtZero
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context)
    (certificate :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.APeriodPositiveLiteralRealLowerCertificate
        context 0)
    (clearancePositive : 0 <
      aPeriodDisplayedRealEntryTailClearanceAtZero context cache
        certificate.lower) :
    FiniteOneByOneEntrySeparationCertificate
      (normalizationMatrix context cache) :=
  finiteAPeriodSeparationOfDisplayedRealLowerAtZero context cache
    certificate.lower certificate.lowerPositive
      (cachedAPeriodPositiveLiteralRealLower_le context cache 0 certificate)
        clearancePositive

/-- One sharp process-ball endpoint at public anchor zero constructs the
complete finite A-entry separation certificate.  The public sampler's
geometric tail controls every later sample, so no prefix scan or prepared
bank execution occurs in this proof. -/
def finiteAPeriodSeparationOfBallRealLowerAtZero
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context)
    (lowerPositive : 0 <
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
        context cache.value 0)
    (clearancePositive : 0 <
      aPeriodBallRealEntryTailClearanceAtZero context cache) :
    FiniteOneByOneEntrySeparationCertificate
      (normalizationMatrix context cache) := by
  let direction : RFAP.ConstructiveGaussian.Gaussian := ⟨1, 0⟩
  let lower :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
      context cache.value 0
  apply FiniteOneByOneEntrySeparationCertificate.ofAnchorZeroDirectional
    direction (by decide) lower lowerPositive
  · simp only [direction, RFAP.ConstructiveGaussian.Gaussian.re,
      RFAP.ConstructiveGaussian.Gaussian.im, one_mul, zero_mul, add_zero]
    unfold oneByOneEntryApproximation normalizationMatrix
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aMatrixOfContextWithCache
    simp only [RFAP.ConstructiveFiniteMatrix.matrixOfFn_apply,
      CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed_sample]
    exact
      (cachedAPeriodSampleBallRealLower_le context cache 0)
  · rw [show RFAP.ConstructiveGaussian.Gaussian.normSq direction = 1 by
      decide]
    change 0 < lower ^ 2 / 2 -
      CCL.FiniteGeometric.quarterRadius
        (oneByOneEntryApproximation
          (normalizationMatrix context cache)).errorScale 0 at clearancePositive
    simpa only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      show (1 : Coordinate)⁻¹ = 1 by decide,
      RFAP.ConstructiveFraction.mul_one_direct] using clearancePositive

/-- Conservative inverse-tail clearance from an arbitrary oriented endpoint.
The direction is kept unnormalized; its exact squared norm appears in the
projection-to-entry conversion before the one-by-one fourth power. -/
def aPeriodDirectionalTailClearance
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context)
    (direction : RFAP.ConstructiveGaussian.Gaussian)
    (anchor : Nat) : Coordinate :=
  let lower :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleDirectionalLowerOfCache
      context cache.value direction anchor
  let entryNormLower := lower ^ 2 /
    RFAP.ConstructiveGaussian.Gaussian.normSq direction
  entryNormLower ^ 4 / 2 -
    CCL.FiniteGeometric.quarterRadius
      (canonicalScaledInverse (normalizationMatrix context cache)).scalar.errorScale
      anchor

/-- Positivity of the oriented endpoint transports its conservative
projection-to-norm clearance to the exact genus-one inverse-tail clearance. -/
theorem aPeriodDirectionalTailClearance_le_oneByOneEntryTailClearanceAt
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context)
    (direction : RFAP.ConstructiveGaussian.Gaussian)
    (directionNormSqPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq direction)
    (anchor : Nat)
    (positive : 0 <
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleDirectionalLowerOfCache
        context cache.value direction anchor) :
    aPeriodDirectionalTailClearance context cache direction anchor <=
      oneByOneEntryTailClearanceAt (normalizationMatrix context cache)
        anchor := by
  let lower :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleDirectionalLowerOfCache
      context cache.value direction anchor
  let sample :=
    (CCL.ProgressiveSampling.approximation
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodProgramOfCache
        context cache.value).output.name).sample anchor
  let projection :=
    direction.re * sample.re + direction.im * sample.im
  have lowerLeProjection : lower <= projection :=
    cachedAPeriodSampleDirectionalLower_le context cache direction anchor
  have lowerSqLeProjectionSq : lower ^ 2 <= projection ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct positive.le
      lowerLeProjection 2
  have projectionSqLe : projection ^ 2 <=
      RFAP.ConstructiveGaussian.Gaussian.normSq direction *
        RFAP.ConstructiveGaussian.Gaussian.normSq sample :=
    RFAP.ConstructiveGaussian.Gaussian.projection_sq_le_normSq_mul
      direction sample
  have entryNormLowerLe :
      lower ^ 2 /
          RFAP.ConstructiveGaussian.Gaussian.normSq direction <=
        RFAP.ConstructiveGaussian.Gaussian.normSq sample := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      directionNormSqPositive).2
    exact (lowerSqLeProjectionSq.trans projectionSqLe).trans_eq (by ring1)
  have fourthPowerLe :
      (lower ^ 2 /
          RFAP.ConstructiveGaussian.Gaussian.normSq direction) ^ 4 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq sample ^ 4 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct
      (RFAP.ConstructiveFraction.div_nonneg_direct
        (RFAP.ConstructiveFraction.sq_nonneg_direct lower)
        directionNormSqPositive.le)
      entryNormLowerLe 4
  have halfLe :
      (lower ^ 2 /
          RFAP.ConstructiveGaussian.Gaussian.normSq direction) ^ 4 / 2 <=
        RFAP.ConstructiveGaussian.Gaussian.normSq sample ^ 4 / 2 := by
    simp only [RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      fourthPowerLe
      (RFAP.ConstructiveFraction.inv_pos_direct
        (by decide : (0 : Coordinate) < 2)).le
  change
    (lower ^ 2 /
          RFAP.ConstructiveGaussian.Gaussian.normSq direction) ^ 4 / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse (normalizationMatrix context cache)).scalar.errorScale
          anchor <=
      RFAP.ConstructiveGaussian.Gaussian.normSq sample ^ 4 / 2 -
        CCL.FiniteGeometric.quarterRadius
          (canonicalScaledInverse (normalizationMatrix context cache)).scalar.errorScale
          anchor
  exact RFAP.ConstructiveFraction.sub_le_sub_right_direct halfLe _

/-- One positive directional endpoint and one rational clearance comparison
construct the exact bounded separation consumed by normalization. -/
def boundedSeparationOfAPeriodDirectionalLower
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (cache : RetainedAPeriodCache context)
    (direction : RFAP.ConstructiveGaussian.Gaussian)
    (directionNormSqPositive :
      0 < RFAP.ConstructiveGaussian.Gaussian.normSq direction)
    {bound : Nat} (anchor : Nat) (within : anchor < bound)
    (lowerPositive : 0 <
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleDirectionalLowerOfCache
        context cache.value direction anchor)
    (clearancePositive :
      0 < aPeriodDirectionalTailClearance context cache direction anchor) :
    BoundedScalarTailSeparationCertificate
      (normalizationMatrix context cache) bound where
  certificate :=
    { anchor := anchor
      tailPositive := by
        rw [← oneByOneEntryTailClearanceAt_eq_scalarTailClearanceAt]
        exact clearancePositive.trans_le
          (aPeriodDirectionalTailClearance_le_oneByOneEntryTailClearanceAt
            context cache direction directionNormSqPositive anchor
              lowerPositive) }
  anchor_lt := within

/-- Retained finite normalization state.  An exhausted caller can extend this
value, preserving all already allocated A-state thunks. -/
structure RetryState (bound : Nat) where
  context :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext
  aCache : RetainedAPeriodCache context
  cache_covers : requiredAPeriodCacheCount context bound <= aCache.count

namespace RetryState

/-- Extend only the finite A-state prefix; the measured bank context and old
thunks are retained. -/
def extend {bound : Nat} (state : RetryState bound) (extra : Nat) :
    RetryState (bound + extra) := by
  let needed := requiredAPeriodCacheCount state.context (bound + extra)
  let added := needed - state.aCache.count
  let extended := state.aCache.extend added
  have covered : needed <= state.aCache.count + added := by
    rcases Nat.le_total needed state.aCache.count with enough | short
    · exact enough.trans (Nat.le_add_right state.aCache.count added)
    · rw [show state.aCache.count + added = needed by
        exact Nat.add_sub_of_le short]
  exact
    { context := state.context
      aCache := extended
      cache_covers := covered }

/-- Every model from the old prefix is backed by the identical thunk after a
retry-state extension. -/
theorem extend_cache_model_of_lt {bound : Nat} (state : RetryState bound)
    (extra index : Nat) (within : index < state.aCache.count) :
    (state.extend extra).aCache.value.model index =
      state.aCache.value.model index := by
  exact state.aCache.extend_model_of_lt _ index within

end RetryState

/-- Proof-bearing success from a bounded normalization scan. -/
structure Ready (bound : Nat) where
  context :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext
  aCache : RetainedAPeriodCache context
  cache_covers : requiredAPeriodCacheCount context bound <= aCache.count
  separation : BoundedScalarTailSeparationCertificate
    (normalizationMatrix context aCache) bound
  inverse : ScaledInverseCertificate (normalizationMatrix context aCache)
  inverse_eq : inverse =
    separation.certificate.toScaledInverseCertificate
  normalized : NormalizedPeriodData
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
  normalized_eq : normalized =
    NormalizedPeriodData.ofScaledInverse
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodDataOfContextWithACache
        context aCache.value)
      inverse

/-- The theorem-facing normalization payload.  Unlike `Ready`, this record
does not retain a bounded-search provenance: a uniform finite A-period lower
certificate constructs the canonical scaled inverse directly.  This is the
small boundary consumed by an intrinsic surface theorem, while executable
clients may continue to use `RetryState.evaluate`. -/
structure ExplicitNormalizationCertificate where
  context :
    CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext
  aCache : RetainedAPeriodCache context
  aLower : OneByOneEntryCandidateLowerCertificate
    (normalizationMatrix context aCache)
  scaledInverse : ScaledInverseCertificate
    (normalizationMatrix context aCache)
  scaledInverse_eq : scaledInverse =
    aLower.toScalarCandidateLowerCertificate.toScaledInverseCertificate
  normalized : NormalizedPeriodData
    CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
  normalized_eq : normalized =
    NormalizedPeriodData.ofScaledInverse
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodDataOfContextWithACache
        context aCache.value)
      scaledInverse

namespace ExplicitNormalizationCertificate

/-- Assemble theorem-facing normalized data without executing a tail scan.
The supplied lower theorem is retained verbatim next to the inverse and
normalized payload that it constructs. -/
def ofAPeriodLower
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (aCache : RetainedAPeriodCache context)
    (aLower : OneByOneEntryCandidateLowerCertificate
      (normalizationMatrix context aCache)) :
    ExplicitNormalizationCertificate :=
  let scaledInverse :=
    aLower.toScalarCandidateLowerCertificate.toScaledInverseCertificate
  let normalized :=
    NormalizedPeriodData.ofScaledInverse
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodDataOfContextWithACache
        context aCache.value)
      scaledInverse
  { context := context
    aCache := aCache
    aLower := aLower
    scaledInverse := scaledInverse
    scaledInverse_eq := rfl
    normalized := normalized
    normalized_eq := rfl }

/-- Assemble theorem-facing normalization from one sharp real endpoint at
public anchor zero.  This is the compact bridge used by the explicit example:
the endpoint theorem constructs uniform A-entry separation, after which the
ordinary one-by-one normalization API supplies the scaled inverse. -/
def ofAPeriodBallRealLowerAtZero
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (aCache : RetainedAPeriodCache context)
    (lowerPositive : 0 <
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
        context aCache.value 0)
    (clearancePositive : 0 <
      aPeriodBallRealEntryTailClearanceAtZero context aCache) :
    ExplicitNormalizationCertificate :=
  ofAPeriodLower context aCache
    (finiteAPeriodSeparationOfBallRealLowerAtZero context aCache
      lowerPositive clearancePositive).toOneByOneEntryCandidateLowerCertificate

/-- Assemble theorem-facing normalization from a checked literal A-period
lower certificate.  Only its small displayed clearance inequality remains as
a rational side condition; no prepared-bank execution or retry scan is part
of this constructor. -/
def ofPositiveLiteralAPeriodRealLowerAtZero
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (aCache : RetainedAPeriodCache context)
    (certificate :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.APeriodPositiveLiteralRealLowerCertificate
        context 0)
    (clearancePositive : 0 <
      aPeriodDisplayedRealEntryTailClearanceAtZero context aCache
        certificate.lower) :
    ExplicitNormalizationCertificate :=
  ofAPeriodLower context aCache
    (finiteAPeriodSeparationOfPositiveLiteralRealLowerAtZero context aCache
      certificate clearancePositive).toOneByOneEntryCandidateLowerCertificate

/-- The minimal genus-one surface inequality supplies the retained A-period
lower theorem and therefore the complete explicit normalization payload.  No
selected-anchor evaluation, bank replay, or bounded scalar scan occurs in
this constructor. -/
def ofUnitSurfaceLower
    (context :
      CCL.Riemann.ExplicitLegendrePreparedPeriods.PreparedLegendreContext)
    (aCache : RetainedAPeriodCache context)
    (surface : CCL.Riemann.PreparedEnergy.GenusOneUnitSurfaceLowerCertificate
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodDataOfContextWithACache
        context aCache.value)) :
    ExplicitNormalizationCertificate :=
  ofAPeriodLower context aCache
    surface.toOneByOneEntryCandidateLowerCertificate

/-- The normalized ratio is a projection from the retained theorem-facing
payload; requesting it performs no period acquisition or inverse search. -/
def ratio (certificate : ExplicitNormalizationCertificate) :=
  certificate.normalized.omega 0 0

def ratioCenter (certificate : ExplicitNormalizationCertificate)
    (target : Coordinate) (positive : 0 < target) :=
  certificate.normalized.omegaCenter target positive 0 0

def ratioRadiusSq (certificate : ExplicitNormalizationCertificate)
    (target : Coordinate) (positive : 0 < target) :=
  certificate.normalized.omegaRadiusSq target positive 0 0

theorem ratioRadiusSq_lt (certificate : ExplicitNormalizationCertificate)
    (target : Coordinate) (positive : 0 < target) :
    certificate.ratioRadiusSq target positive < target :=
  certificate.normalized.omegaRadiusSq_lt_target target positive 0 0

/-- Bounded typed acquisition of the dual one-loop denominator from the
retained theorem-facing ratio. -/
def attemptOneDenominator (certificate : ExplicitNormalizationCertificate)
    (fuel : Nat) :=
  CCL.Riemann.LegendrePeriodMonodromy.attemptStandardOne certificate.ratio fuel

/-- Bounded typed acquisition of the dual infinity-loop denominator from the
same retained ratio. -/
def attemptInfinityDenominator
    (certificate : ExplicitNormalizationCertificate) (fuel : Nat) :=
  CCL.Riemann.LegendrePeriodMonodromy.attemptStandardInfinity
    certificate.ratio fuel

end ExplicitNormalizationCertificate

namespace Ready

/-- The ratio is a cheap projection from the retained normalized payload, so
dependent denominator types remain definitionally aligned with monodromy
data. -/
def ratio {bound : Nat} (ready : Ready bound) :=
  ready.normalized.omega 0 0

/-- Displayed rational centre of the normalized ratio at a caller-selected
finite request. -/
def ratioCenter {bound : Nat} (ready : Ready bound)
    (target : Coordinate) (positive : 0 < target) :=
  ready.normalized.omegaCenter target positive 0 0

def ratioRadiusSq {bound : Nat} (ready : Ready bound)
    (target : Coordinate) (positive : 0 < target) :=
  ready.normalized.omegaRadiusSq target positive 0 0

theorem ratioRadiusSq_lt {bound : Nat} (ready : Ready bound)
    (target : Coordinate) (positive : 0 < target) :
    ready.ratioRadiusSq target positive < target :=
  ready.normalized.omegaRadiusSq_lt_target target positive 0 0

/-- Bounded retryable preparation of the dual one-loop denominator after
normalization has become ready. -/
def attemptOneDenominator {bound : Nat} (ready : Ready bound) (fuel : Nat) :=
  CCL.Riemann.LegendrePeriodMonodromy.attemptStandardOne ready.ratio fuel

/-- Bounded retryable preparation of the dual infinity-loop denominator. -/
def attemptInfinityDenominator {bound : Nat} (ready : Ready bound)
    (fuel : Nat) :=
  CCL.Riemann.LegendrePeriodMonodromy.attemptStandardInfinity ready.ratio fuel

end Ready

/-- Exact outcome of the measured A-bank acquisition followed by the bounded
normalization scan.  A geometric bank failure is not conflated with an
exhausted scalar prefix. -/
inductive AttemptResult (bound : Nat)
  | aBankFailed
      (stage :
        CCL.Riemann.ExplicitLegendrePreparedPeriods.ABankFailureStage)
  | separationExhausted (state : RetryState bound)
  | ready (value : Ready bound)

namespace AttemptResult

def toOption {bound : Nat} : AttemptResult bound -> Option (Ready bound)
  | .aBankFailed _stage => none
  | .separationExhausted _state => none
  | .ready value => some value

end AttemptResult

namespace RetryState

/-- Assemble the retained inverse and normalized data exactly once after a
successful tail check. -/
private def readyOfSeparation {bound : Nat} (state : RetryState bound)
    (separation : BoundedScalarTailSeparationCertificate
      (normalizationMatrix state.context state.aCache) bound) : Ready bound :=
  let inverse := separation.certificate.toScaledInverseCertificate
  let normalized :=
    NormalizedPeriodData.ofScaledInverse
      (CCL.Riemann.ExplicitLegendrePreparedPeriods.periodDataOfContextWithACache
        state.context state.aCache.value)
      inverse
  { context := state.context
    aCache := state.aCache
    cache_covers := state.cache_covers
    separation := separation
    inverse := inverse
    inverse_eq := rfl
    normalized := normalized
    normalized_eq := rfl }

/-- The theorem-facing normalization route: a positive sign-aware A-period
endpoint and its conservative rational tail clearance construct `Ready`
directly, without asking Lean to execute the bounded search. -/
def readyOfAPeriodRealLower {bound : Nat} (state : RetryState bound)
    (anchor : Nat) (within : anchor < bound)
    (lowerPositive : 0 <
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleRealLowerOfCache
        state.context state.aCache.value anchor)
    (clearancePositive : 0 <
      aPeriodRealTailClearance state.context state.aCache anchor) :
    Ready bound :=
  state.readyOfSeparation
    (boundedSeparationOfAPeriodRealLower state.context state.aCache anchor
      within lowerPositive clearancePositive)

/-- Sharp process-ball counterpart of `readyOfAPeriodRealLower`.  It tests
one displayed anchor and constructs `Ready` without scanning any prefix. -/
def readyOfAPeriodBallRealLower {bound : Nat} (state : RetryState bound)
    (anchor : Nat) (within : anchor < bound)
    (lowerPositive : 0 <
      CCL.Riemann.ExplicitLegendrePreparedPeriods.aPeriodSampleBallRealLowerOfCache
        state.context state.aCache.value anchor)
    (clearancePositive : 0 <
      aPeriodBallRealTailClearance state.context state.aCache anchor) :
    Ready bound :=
  state.readyOfSeparation
    (boundedSeparationOfAPeriodBallRealLower state.context state.aCache anchor
      within lowerPositive clearancePositive)

/-- Test the complete prefix represented by a retained state.  Failure
returns that same state so a caller may extend it without replaying prepared
geometry. -/
def evaluate {bound : Nat} (state : RetryState bound) :
    AttemptResult bound :=
  match scalarTailSeparationWithin?
      (normalizationMatrix state.context state.aCache) bound with
  | none => .separationExhausted state
  | some separation => .ready (readyOfSeparation state separation)

/-- Test one caller-selected anchor and no other sample.  The cache bound is
already part of `state`, so success has the same `Ready` type as a prefix
scan while failure retains the state for a later extension. -/
def evaluateAt {bound : Nat} (state : RetryState bound)
    (anchor : Nat) (within : anchor < bound) : AttemptResult bound :=
  match oneByOneEntryTailSeparationAtWithin?
      (normalizationMatrix state.context state.aCache) anchor within with
  | none => .separationExhausted state
  | some separation => .ready (readyOfSeparation state separation)

/-- Retry with `extra` additional anchors while physically preserving the
old state prefix. -/
def retry {bound : Nat} (state : RetryState bound) (extra : Nat) :
    AttemptResult (bound + extra) :=
  (state.extend extra).evaluate

end RetryState

/-- Run the measured A banks once, retaining their exact failure stage, and
only then scan the caller-selected normalization prefix.  The resulting
`Ready` keeps the same context so later A samples reuse all four banks and B
remains independently delayed. -/
def attemptDetailed (bound : Nat) : AttemptResult bound :=
  let context :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.preparedLegendreContext ()
  match context.measuredA with
  | .error stage => .aBankFailed stage
  | .ok _banks =>
      let state : RetryState bound :=
        let count := requiredAPeriodCacheCount context bound
        { context := context
          aCache := RetainedAPeriodCache.canonical context count
          cache_covers := Nat.le_refl count }
      state.evaluate

/-- Run the measured A banks once and test exactly the displayed anchor.
Unlike `attemptDetailed`, this entry point never scans a prefix. -/
def attemptAtDetailed (anchor : Nat) : AttemptResult (anchor + 1) :=
  let context :=
    CCL.Riemann.ExplicitLegendrePreparedPeriods.preparedLegendreContext ()
  match context.measuredA with
  | .error stage => .aBankFailed stage
  | .ok _banks =>
      let state : RetryState (anchor + 1) :=
        let count := requiredAPeriodCacheCount context (anchor + 1)
        { context := context
          aCache := RetainedAPeriodCache.canonical context count
          cache_covers := Nat.le_refl count }
      state.evaluateAt anchor (Nat.lt_succ_self anchor)

/-- Conventional option projection of the direct-anchor attempt. -/
def attemptAt (anchor : Nat) : Option (Ready (anchor + 1)) :=
  (attemptAtDetailed anchor).toOption

/-- Conventional option projection of `attemptDetailed`.  Use the detailed
form when a client needs to distinguish finite geometric failure from an
exhausted scalar scan. -/
def attempt (bound : Nat) : Option (Ready bound) :=
  (attemptDetailed bound).toOption

theorem attempt_isSome_iff (bound : Nat) :
    (attempt bound).isSome = true ↔
      (attemptDetailed bound).toOption.isSome = true := by
  rfl

/-! ## Unified productive acquisition -/

/-- Lightweight dependent carrier which prevents elaboration from expanding
the two large exact denominator-process indices while generating the public
record. -/
structure ProductiveReadyPayload.{u, v, w}
    (normalizationType : Type u)
    (oneType : normalizationType -> Type v)
    (infinityType : normalizationType -> Type w) where
  normalization : normalizationType
  onePreparation : oneType normalization
  infinityPreparation : infinityType normalization

/-- A completed explicit normalization together with the two exactly indexed
denominator preparations required by dual period monodromy. -/
def ProductiveReady (bound : Nat) : Type 2 :=
  ProductiveReadyPayload (Ready bound)
    (fun normalization =>
      CCL.Riemann.LegendrePeriodMonodromy.OnePreparation
        normalization.ratio)
    (fun normalization =>
      CCL.Riemann.LegendrePeriodMonodromy.InfinityPreparation
        normalization.ratio)

/-- A theorem-produced normalization together with the two precisely
indexed productive denominator preparations. -/
def ProductiveExplicitNormalizationCertificate : Type 2 :=
  ProductiveReadyPayload ExplicitNormalizationCertificate
    (fun normalization =>
      CCL.Riemann.LegendrePeriodMonodromy.OnePreparation
        normalization.ratio)
    (fun normalization =>
      CCL.Riemann.LegendrePeriodMonodromy.InfinityPreparation
        normalization.ratio)

namespace ProductiveExplicitNormalizationCertificate

def oneOutput (certificate : ProductiveExplicitNormalizationCertificate) :=
  CCL.Riemann.LegendrePeriodMonodromy.oneTransform certificate.onePreparation

def infinityOutput
    (certificate : ProductiveExplicitNormalizationCertificate) :=
  CCL.Riemann.LegendrePeriodMonodromy.infinityTransform
    certificate.infinityPreparation

theorem oneOutput_productive
    (certificate : ProductiveExplicitNormalizationCertificate)
    (count : Nat) :
    certificate.oneOutput.name.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          certificate.oneOutput.name.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        certificate.oneOutput.name.machine count).emitted.length = count :=
  certificate.oneOutput.name.productive count

theorem infinityOutput_productive
    (certificate : ProductiveExplicitNormalizationCertificate)
    (count : Nat) :
    certificate.infinityOutput.name.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          certificate.infinityOutput.name.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        certificate.infinityOutput.name.machine count).emitted.length = count :=
  certificate.infinityOutput.name.productive count

end ProductiveExplicitNormalizationCertificate

namespace ProductiveReady

/-- Productive normalized output for the standard dual one-loop action. -/
def oneOutput {bound : Nat} (ready : ProductiveReady bound) :=
  CCL.Riemann.LegendrePeriodMonodromy.oneTransform ready.onePreparation

/-- Productive normalized output for the standard dual infinity-loop action. -/
def infinityOutput {bound : Nat} (ready : ProductiveReady bound) :=
  CCL.Riemann.LegendrePeriodMonodromy.infinityTransform
    ready.infinityPreparation

theorem oneOutput_productive {bound : Nat} (ready : ProductiveReady bound)
    (count : Nat) :
    ready.oneOutput.name.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance ready.oneOutput.name.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        ready.oneOutput.name.machine count).emitted.length = count :=
  ready.oneOutput.name.productive count

theorem infinityOutput_productive {bound : Nat}
    (ready : ProductiveReady bound) (count : Nat) :
    ready.infinityOutput.name.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          ready.infinityOutput.name.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
        ready.infinityOutput.name.machine count).emitted.length = count :=
  ready.infinityOutput.name.productive count

end ProductiveReady

/-- Lightweight carrier for the combined acquisition outcome.  Callers which
need the exact retained exhaustion state use `Ready.attemptOneDenominator` or
`Ready.attemptInfinityDenominator`, whose `RunResult` already preserves it. -/
inductive ProductiveAttemptResultPayload.{u} (readyType : Type u) : Type u
  | normalizationExhausted
  | oneExhausted
  | infinityExhausted
  | ready (value : readyType)

/-- Denominator-only outcome for a theorem-produced normalization.  The two
fuel values remain in the type for auditability, while failure is ordinary
finite exhaustion rather than a zero-denominator conclusion. -/
def ProductiveExplicitAttemptResult
    (_oneFuel _infinityFuel : Nat) : Type 2 :=
  ProductiveAttemptResultPayload ProductiveExplicitNormalizationCertificate

/-- Add the two productive denominator preparations to an already proved
normalization, preserving the exact preparation objects returned by each
bounded runner. -/
def attemptProductiveOfCertificate
    (normalization : ExplicitNormalizationCertificate)
    (oneFuel infinityFuel : Nat) :
    ProductiveExplicitAttemptResult oneFuel infinityFuel :=
  match normalization.attemptOneDenominator oneFuel with
  | .exhausted _final _reachable => .oneExhausted
  | .ready _final _reachable onePreparation =>
      match normalization.attemptInfinityDenominator infinityFuel with
      | .exhausted _final _reachable => .infinityExhausted
      | .ready _final _reachable infinityPreparation =>
          .ready
            (ProductiveReadyPayload.mk normalization onePreparation
              infinityPreparation)

namespace ProductiveExplicitAttemptResult

def toOption {oneFuel infinityFuel : Nat} :
    ProductiveExplicitAttemptResult oneFuel infinityFuel ->
      Option ProductiveExplicitNormalizationCertificate
  | .normalizationExhausted => none
  | .oneExhausted => none
  | .infinityExhausted => none
  | .ready value => some value

end ProductiveExplicitAttemptResult

/-- The three caller-selected bounds remain visible in the combined result
type without expanding the dependent denominator processes. -/
def ProductiveAttemptResult
    (bound _oneFuel _infinityFuel : Nat) : Type 2 :=
  ProductiveAttemptResultPayload (ProductiveReady bound)

/-- Run normalization, dual one-denominator acquisition, and dual
infinity-denominator acquisition in order, each under the caller's finite
bound.  Every unsuccessful branch retains exactly the evidence available at
that stopping point. -/
def attemptProductive (bound oneFuel infinityFuel : Nat) :
    ProductiveAttemptResult bound oneFuel infinityFuel :=
  match attempt bound with
  | none => .normalizationExhausted
  | some normalization =>
      match normalization.attemptOneDenominator oneFuel with
      | .exhausted _final _reachable => .oneExhausted
      | .ready _final _reachable onePreparation =>
          match normalization.attemptInfinityDenominator infinityFuel with
          | .exhausted _final _reachable => .infinityExhausted
          | .ready _final _reachable infinityPreparation =>
              .ready
                (ProductiveReadyPayload.mk normalization onePreparation
                  infinityPreparation)

namespace ProductiveAttemptResult

/-- Forget retained exhaustion states when a caller needs only a conventional
success option. -/
def toOption {bound oneFuel infinityFuel : Nat} :
    ProductiveAttemptResult bound oneFuel infinityFuel ->
      Option (ProductiveReady bound)
  | .normalizationExhausted => none
  | .oneExhausted => none
  | .infinityExhausted => none
  | .ready value => some value

end ProductiveAttemptResult

end CCL.Riemann.ExplicitLegendreNormalizedAcquisition
