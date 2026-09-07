import CCL.Riemann.FiniteEnergy
import CCL.Riemann.OperationalQuotients

/-!
# Operational realization of synchronized period normalization

The persistent normalized period entries use stateful CCL arithmetic, while
the finite energy argument uses one equal-index Gaussian-rational calculation
of `A⁻¹B`.  This module connects those two presentations without introducing
a completed matrix.  Its basic tool is an equal-index geometric quotient with
an explicit positive lower bound on every displayed denominator sample.
-/

namespace CCL.Riemann.SynchronizedNormalization

open CCL.Riemann.PeriodMatrix
open CCL.Riemann.PeriodMatrix.ScaledInverseCertificate

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev Equivalent := CCL.OperationalEquivalence.Equivalent
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev GeometricApproximation :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation

open RFAP.ConstructiveGaussian.Gaussian

/-- A positive rational lower bound for every displayed sample of one
geometric approximation.  It is weaker than whole-ball apartness and is
exactly what equal-index finite division requires. -/
structure SampleLower (source : GeometricApproximation) where
  lowerSq : Coordinate
  positive : 0 < lowerSq
  sample_lower : forall index, lowerSq <= normSq (source.sample index)

namespace SampleLower

theorem sample_nonzero {source : GeometricApproximation}
    (lower : SampleLower source) (index : Nat) : source.sample index ≠ 0 := by
  intro zero
  have positive := lower.positive.trans_le (lower.sample_lower index)
  rw [zero, normSq_zero] at positive
  exact (lt_irrefl _ positive).elim

end SampleLower

/-- Geometric error scale for an equal-index quotient of arbitrary geometric
sources. -/
def quotientErrorScale (numerator denominator : GeometricApproximation)
    (lower : SampleLower denominator) : Coordinate :=
  (2 * (numerator.errorScale * denominator.centerBound +
    numerator.centerBound * denominator.errorScale)) /
      (lower.lowerSq * lower.lowerSq)

theorem quotientErrorScale_nonnegative
    (numerator denominator : GeometricApproximation)
    (lower : SampleLower denominator) :
    0 <= quotientErrorScale numerator denominator lower := by
  unfold quotientErrorScale
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          numerator.errorScale_nonneg denominator.centerBound_nonneg)
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          numerator.centerBound_nonneg denominator.errorScale_nonneg)))
    (RFAP.ConstructiveFraction.mul_nonneg_direct lower.positive.le
      lower.positive.le)

/-- Equal-index finite quotients of geometric Gaussian-rational samples. -/
def quotientApproximation (numerator denominator : GeometricApproximation)
    (lower : SampleLower denominator) : GeometricApproximation where
  sample index := numerator.sample index / denominator.sample index
  errorScale := quotientErrorScale numerator denominator lower
  errorScale_nonneg := quotientErrorScale_nonnegative numerator denominator lower
  later_close := by
    intro earlier later order
    have numeratorMovement := numerator.later_close order
    have denominatorMovementForward := denominator.later_close order
    have denominatorMovement :
        normSq (denominator.sample earlier - denominator.sample later) <=
          CCL.FiniteGeometric.quarterRadius denominator.errorScale earlier := by
      have identity : denominator.sample earlier - denominator.sample later =
          -(denominator.sample later - denominator.sample earlier) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
      rw [identity, normSq_neg]
      exact denominatorMovementForward
    have quotientBound :=
      CCL.Riemann.FiniteQuotientVariation.normSq_div_sub_div_le
        lower.positive
        (leftNumerator := numerator.sample later)
        (rightNumerator := numerator.sample earlier)
        (leftDenominator := denominator.sample later)
        (rightDenominator := denominator.sample earlier)
        (numeratorSlope := (1 : Coordinate))
        (numeratorBound := numerator.centerBound)
        (denominatorBound := denominator.centerBound)
        (pointMovement :=
          CCL.FiniteGeometric.quarterRadius numerator.errorScale earlier)
        (rootMovement :=
          CCL.FiniteGeometric.quarterRadius denominator.errorScale earlier)
        (by simpa only [RFAP.ConstructiveFraction.one_mul] using
          numeratorMovement)
        (numerator.sample_bounded earlier)
        (denominator.sample_bounded earlier)
        denominatorMovement
        (lower.sample_lower later) (lower.sample_lower earlier)
    calc
      normSq (numerator.sample later / denominator.sample later -
          numerator.sample earlier / denominator.sample earlier) <=
        CCL.Riemann.FiniteQuotientVariation.quotientBound
          1 numerator.centerBound denominator.centerBound lower.lowerSq
          (CCL.FiniteGeometric.quarterRadius numerator.errorScale earlier)
          (CCL.FiniteGeometric.quarterRadius denominator.errorScale earlier) :=
        quotientBound
      _ = CCL.FiniteGeometric.quarterRadius
          (quotientErrorScale numerator denominator lower) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        unfold CCL.Riemann.FiniteQuotientVariation.quotientBound
          quotientErrorScale
        let geometric : Coordinate := (1 / 4 : Coordinate) ^ earlier
        change
          (2 * (1 * (numerator.errorScale * geometric) *
              denominator.centerBound +
            numerator.centerBound * (denominator.errorScale * geometric))) /
              (lower.lowerSq * lower.lowerSq) =
            ((2 * (numerator.errorScale * denominator.centerBound +
                numerator.centerBound * denominator.errorScale)) /
              (lower.lowerSq * lower.lowerSq)) * geometric
        rw [RFAP.ExplicitField.div_eq_mul_inv,
          RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  centerBound := numerator.centerBound / lower.lowerSq
  centerBound_nonneg := RFAP.ConstructiveFraction.div_nonneg_direct
    numerator.centerBound_nonneg lower.positive.le
  sample_bounded := by
    intro index
    rw [normSq_div _ _ (lower.sample_nonzero index)]
    calc
      normSq (numerator.sample index) / normSq (denominator.sample index) <=
          normSq (numerator.sample index) / lower.lowerSq :=
        RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
          (normSq_nonneg _) lower.positive (lower.sample_lower index)
      _ <= numerator.centerBound / lower.lowerSq := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (numerator.sample_bounded index)
          (RFAP.ConstructiveFraction.inv_pos_direct lower.positive).le

@[simp] theorem quotientApproximation_sample
    (numerator denominator : GeometricApproximation)
    (lower : SampleLower denominator) (index : Nat) :
    (quotientApproximation numerator denominator lower).sample index =
      numerator.sample index / denominator.sample index :=
  rfl

/-- One positive lower bound shared by two equal-index denominator streams. -/
def commonLower {first second : GeometricApproximation}
    (firstLower : SampleLower first) (secondLower : SampleLower second) :
    Coordinate :=
  min firstLower.lowerSq secondLower.lowerSq

theorem commonLower_positive {first second : GeometricApproximation}
    (firstLower : SampleLower first) (secondLower : SampleLower second) :
    0 < commonLower firstLower secondLower :=
  lt_min firstLower.positive secondLower.positive

/-- Sensitivity coefficient for replacing both operands of a finite
equal-index quotient. -/
def quotientComparisonCoefficient
    (secondNumerator secondDenominator : GeometricApproximation)
    {firstDenominator : GeometricApproximation}
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator) : Coordinate :=
  (2 * (secondDenominator.centerBound + secondNumerator.centerBound)) /
    (commonLower firstLower secondLower *
      commonLower firstLower secondLower)

theorem quotientComparisonCoefficient_nonnegative
    (secondNumerator secondDenominator : GeometricApproximation)
    {firstDenominator : GeometricApproximation}
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator) :
    0 <= quotientComparisonCoefficient secondNumerator secondDenominator
      firstLower secondLower := by
  unfold quotientComparisonCoefficient
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg secondDenominator.centerBound_nonneg
        secondNumerator.centerBound_nonneg))
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (commonLower_positive firstLower secondLower).le
      (commonLower_positive firstLower secondLower).le)

def quotientComparisonTarget
    (secondNumerator secondDenominator : GeometricApproximation)
    {firstDenominator : GeometricApproximation}
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator)
    (target : Coordinate) : Coordinate :=
  target / (1 + quotientComparisonCoefficient secondNumerator
    secondDenominator firstLower secondLower)

theorem quotientComparisonTarget_positive
    (secondNumerator secondDenominator : GeometricApproximation)
    {firstDenominator : GeometricApproximation}
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator)
    {target : Coordinate} (positive : 0 < target) :
    0 < quotientComparisonTarget secondNumerator secondDenominator
      firstLower secondLower target :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (add_pos_of_pos_of_nonneg (by decide)
      (quotientComparisonCoefficient_nonnegative secondNumerator
        secondDenominator firstLower secondLower))

theorem quotientComparisonTarget_budget_lt
    (secondNumerator secondDenominator : GeometricApproximation)
    {firstDenominator : GeometricApproximation}
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator)
    {target : Coordinate} (positive : 0 < target) :
    quotientComparisonTarget secondNumerator secondDenominator
        firstLower secondLower target *
      quotientComparisonCoefficient secondNumerator secondDenominator
        firstLower secondLower < target := by
  let coefficient := quotientComparisonCoefficient secondNumerator
    secondDenominator firstLower secondLower
  have coefficientNonnegative : 0 <= coefficient :=
    quotientComparisonCoefficient_nonnegative secondNumerator
      secondDenominator firstLower secondLower
  have denominatorPositive : 0 < 1 + coefficient :=
    add_pos_of_pos_of_nonneg (by decide) coefficientNonnegative
  have fractionLt : coefficient / (1 + coefficient) < 1 := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos denominatorPositive).2
    calc
      coefficient = 0 + coefficient :=
        (RFAP.ConstructiveFraction.zero_add coefficient).symm
      _ < 1 + coefficient :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct (by decide) _
      _ = 1 * (1 + coefficient) := by ring1
  have scaled := RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
    positive fractionLt
  change target / (1 + coefficient) * coefficient < target
  calc
    target / (1 + coefficient) * coefficient =
        target * (coefficient / (1 + coefficient)) := by
      rw [RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ExplicitField.div_eq_mul_inv]
      ring1
    _ < target * 1 := scaled
    _ = target := RFAP.ConstructiveFraction.mul_one_direct _

/-- Equal-index geometric quotients respect operational equality of both
sources, using only a displayed positive sample lower bound on each
denominator. -/
def quotientApproximation_respects
    (firstNumerator secondNumerator firstDenominator secondDenominator :
      GeometricApproximation)
    (firstLower : SampleLower firstDenominator)
    (secondLower : SampleLower secondDenominator)
    (numeratorEquivalent : Equivalent firstNumerator.toApproximation
      secondNumerator.toApproximation)
    (denominatorEquivalent : Equivalent firstDenominator.toApproximation
      secondDenominator.toApproximation) :
    Equivalent
      (quotientApproximation firstNumerator firstDenominator firstLower).toApproximation
      (quotientApproximation secondNumerator secondDenominator secondLower).toApproximation where
  compare := by
    intro firstStart secondStart target positive
    let inputTarget := quotientComparisonTarget secondNumerator
      secondDenominator firstLower secondLower target
    have inputPositive : 0 < inputTarget :=
      quotientComparisonTarget_positive secondNumerator secondDenominator
        firstLower secondLower positive
    let numeratorComparison := numeratorEquivalent.compare firstStart
      secondStart inputTarget inputPositive
    let denominatorComparison := denominatorEquivalent.compare firstStart
      secondStart inputTarget inputPositive
    let firstIndex := max numeratorComparison.leftIndex
      denominatorComparison.leftIndex
    let secondIndex := max numeratorComparison.rightIndex
      denominatorComparison.rightIndex
    exact
      { leftIndex := firstIndex
        rightIndex := secondIndex
        left_ge := numeratorComparison.left_ge.trans (Nat.le_max_left _ _)
        right_ge := numeratorComparison.right_ge.trans (Nat.le_max_left _ _)
        close := by
          intro firstLater secondLater firstOrder secondOrder
          have numeratorClose := numeratorComparison.close
            ((Nat.le_max_left numeratorComparison.leftIndex
              denominatorComparison.leftIndex).trans firstOrder)
            ((Nat.le_max_left numeratorComparison.rightIndex
              denominatorComparison.rightIndex).trans secondOrder)
          have numeratorClose' :
              normSq (firstNumerator.sample firstLater -
                secondNumerator.sample secondLater) < inputTarget := by
            simpa only [
              CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.toApproximation_sample]
              using numeratorClose
          have denominatorCloseForward := denominatorComparison.close
            ((Nat.le_max_right numeratorComparison.leftIndex
              denominatorComparison.leftIndex).trans firstOrder)
            ((Nat.le_max_right numeratorComparison.rightIndex
              denominatorComparison.rightIndex).trans secondOrder)
          have denominatorCloseForward' :
              normSq (firstDenominator.sample firstLater -
                secondDenominator.sample secondLater) < inputTarget := by
            simpa only [
              CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.toApproximation_sample]
              using denominatorCloseForward
          have denominatorClose :
              normSq (secondDenominator.sample secondLater -
                  firstDenominator.sample firstLater) <= inputTarget := by
            have identity :
                secondDenominator.sample secondLater -
                    firstDenominator.sample firstLater =
                  -(firstDenominator.sample firstLater -
                    secondDenominator.sample secondLater) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [identity, normSq_neg]
            exact denominatorCloseForward'.le
          have commonFirst : commonLower firstLower secondLower <=
              normSq (firstDenominator.sample firstLater) :=
            (min_le_left _ _).trans (firstLower.sample_lower firstLater)
          have commonSecond : commonLower firstLower secondLower <=
              normSq (secondDenominator.sample secondLater) :=
            (min_le_right _ _).trans (secondLower.sample_lower secondLater)
          have quotientBound :=
            CCL.Riemann.FiniteQuotientVariation.normSq_div_sub_div_le
              (commonLower_positive firstLower secondLower)
              (leftNumerator := firstNumerator.sample firstLater)
              (rightNumerator := secondNumerator.sample secondLater)
              (leftDenominator := firstDenominator.sample firstLater)
              (rightDenominator := secondDenominator.sample secondLater)
              (numeratorSlope := (1 : Coordinate))
              (numeratorBound := secondNumerator.centerBound)
              (denominatorBound := secondDenominator.centerBound)
              (pointMovement := inputTarget)
              (rootMovement := inputTarget)
              (by simpa only [RFAP.ConstructiveFraction.one_mul] using
                numeratorClose'.le)
              (secondNumerator.sample_bounded secondLater)
              (secondDenominator.sample_bounded secondLater)
              denominatorClose commonFirst commonSecond
          change normSq
              (firstNumerator.sample firstLater /
                  firstDenominator.sample firstLater -
                secondNumerator.sample secondLater /
                  secondDenominator.sample secondLater) < target
          calc
            normSq
                (firstNumerator.sample firstLater /
                    firstDenominator.sample firstLater -
                  secondNumerator.sample secondLater /
                    secondDenominator.sample secondLater) <=
              CCL.Riemann.FiniteQuotientVariation.quotientBound
                1 secondNumerator.centerBound secondDenominator.centerBound
                (commonLower firstLower secondLower) inputTarget inputTarget :=
              quotientBound
            _ = inputTarget *
                quotientComparisonCoefficient secondNumerator
                  secondDenominator firstLower secondLower := by
              unfold CCL.Riemann.FiniteQuotientVariation.quotientBound
                quotientComparisonCoefficient
              rw [RFAP.ExplicitField.div_eq_mul_inv,
                RFAP.ExplicitField.div_eq_mul_inv]
              ring1
            _ < target := quotientComparisonTarget_budget_lt
              secondNumerator secondDenominator firstLower secondLower positive }

/-! ## Synchronized normalization sources -/

/-- Equal-index numerator `adj(A)B` underlying one normalized period entry. -/
def normalizationNumerator {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) (row column : Fin genus) :
    GeometricApproximation :=
  geometricProductEntry (canonicalScaledInverse data.aMatrix).inverse
    (geometricMatrixOfNamed data.bMatrix) row column

/-- Equal-index fraction-free inverse scalar underlying normalization. -/
def normalizationDenominator {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve) : GeometricApproximation :=
  (canonicalScaledInverse data.aMatrix).scalar

/-- The finite inverse-separation certificate is precisely a sample lower
bound for the synchronized denominator stream. -/
def normalizationDenominatorLower {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    SampleLower (normalizationDenominator data) where
  lowerSq := inverseLower.lowerSq
  positive := inverseLower.positive
  sample_lower := inverseLower.sample_lower

/-- One raw equal-index normalized period entry, now carrying its own
geometric refinement and boundedness data. -/
def synchronizedEntryApproximation {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) : GeometricApproximation :=
  quotientApproximation (normalizationNumerator data row column)
    (normalizationDenominator data)
    (normalizationDenominatorLower inverseLower)

/-- The geometric normalization source displays literally the raw matrix
entry used by the finite energy transport argument at every index. -/
theorem synchronizedEntryApproximation_sample {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) (index : Nat) :
    (synchronizedEntryApproximation data inverseLower row column).sample index =
      CCL.Riemann.FiniteEnergy.synchronizedNormalizedMatrix data index
        row column := by
  let aSource := geometricMatrixOfNamed data.aMatrix
  let bSource := geometricMatrixOfNamed data.bMatrix
  let computed := canonicalScaledInverse data.aMatrix
  let sampledA := sampledMatrix data.aMatrix index
  let inverse :=
    CCL.Riemann.PivotedScaledInverse.completeScaledInverse sampledA
  have inverseSamples :=
    CCL.Riemann.PivotedScaledInverse.completeApproximation_sample aSource index
  have aSourceSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix aSource index =
        sampledA := by
    exact sample_geometricMatrixOfNamed data.aMatrix index
  rw [aSourceSample] at inverseSamples
  have computedScalarSample : computed.scalar.sample index = inverse.scalar := by
    simpa only [computed, canonicalScaledInverse, aSource] using inverseSamples.1
  have computedInverseSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix computed.inverse
          index = inverse.inverse := by
    simpa only [computed, canonicalScaledInverse, aSource] using inverseSamples.2
  have bSourceSample :
      CCL.Riemann.FiniteMatrixApproximation.sampleMatrix bSource index =
        sampledMatrix data.bMatrix index := by
    exact sample_geometricMatrixOfNamed data.bMatrix index
  rw [show (synchronizedEntryApproximation data inverseLower row column).sample
      index =
        (normalizationNumerator data row column).sample index /
          (normalizationDenominator data).sample index by rfl]
  rw [show (normalizationNumerator data row column).sample index =
      RFAP.ConstructiveFiniteMatrix.mul inverse.inverse
        (sampledMatrix data.bMatrix index) row column by
    unfold normalizationNumerator
    rw [geometricProductEntry_sample]
    change RFAP.ConstructiveFiniteMatrix.mul
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix computed.inverse
          index)
        (CCL.Riemann.FiniteMatrixApproximation.sampleMatrix bSource index)
          row column = _
    rw [bSourceSample, computedInverseSample]]
  rw [show (normalizationDenominator data).sample index = inverse.scalar by
    exact computedScalarSample]
  unfold CCL.Riemann.FiniteEnergy.synchronizedNormalizedMatrix
    CCL.Riemann.FiniteEnergy.synchronizedScaledInverse
  rw [CCL.Riemann.FiniteEnergy.divideGaussianMatrix_apply]

/-! ## Operational equivalence with persistent normalization -/

@[simp] theorem geometricOfExact_sample (value : Gaussian) (index : Nat) :
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
      (CCL.ProgressiveCoherence.CoherentNamed.exact value).name).sample index =
      value := by
  rfl

/-- Canonical sampler of the prepared denominator used by stateful division. -/
def preparedDenominatorSource {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    GeometricApproximation :=
  CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
    inverseLower.toScaledInverseCertificate.scalar.name

/-- Whole-ball apartness of the prepared scalar supplies the weaker sample
lower bound needed by its equal-index quotient. -/
def preparedDenominatorLower {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    SampleLower (preparedDenominatorSource inverseLower) where
  lowerSq := inverseLower.toScaledInverseCertificate.scalarApart.certificate.lowerSq
  positive :=
    inverseLower.toScaledInverseCertificate.scalarApart.certificate.positive
  sample_lower := by
    intro index
    exact CCL.Riemann.OperationalQuotients.sampled_lower
      inverseLower.toScaledInverseCertificate.scalar
      inverseLower.toScaledInverseCertificate.scalarApart index

/-- Equal-index reciprocal using the canonical sampler of the prepared
stateful denominator. -/
def preparedReciprocalApproximation {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    GeometricApproximation :=
  quotientApproximation
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
      (CCL.ProgressiveCoherence.CoherentNamed.exact 1).name)
    (preparedDenominatorSource inverseLower)
    (preparedDenominatorLower inverseLower)

/-- Equal-index reciprocal using the unprepared raw scalar stream. -/
def rawReciprocalApproximation {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    GeometricApproximation :=
  quotientApproximation
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact 1)
    (normalizationDenominator data)
    (normalizationDenominatorLower inverseLower)

/-- Prepared scalar samples are operationally the raw fraction-free scalar
samples from which apartification was constructed. -/
def preparedDenominator_equivalent_raw {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    Equivalent (preparedDenominatorSource inverseLower).toApproximation
      (normalizationDenominator data).toApproximation := by
  let inverse := inverseLower.toScaledInverseCertificate
  let raw := normalizationDenominator data
  let prepared := preparedDenominatorSource inverseLower
  have preparedToSampler : Equivalent prepared.toApproximation
      (CCL.ProgressiveSampling.approximation inverse.scalar.name) :=
    CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq _ _
      (by intro index; rfl)
  have preparedToWrappedRaw : Equivalent
      (CCL.ProgressiveSampling.approximation inverse.scalar.name)
      (CCL.ProgressiveSampling.approximation
        (geometricNamed raw).name) := by
    change NamedEquivalent inverse.scalar.name (geometricNamed raw).name
    simpa only [inverse, raw, normalizationDenominator,
      canonicalInverseScalar] using
      CCL.OperationalEquivalence.NamedEquivalent.symm
        inverse.canonicalScalarEquivalent
  have wrappedRawToRaw : Equivalent
      (CCL.ProgressiveSampling.approximation (geometricNamed raw).name)
      raw.toApproximation := by
    simpa only [geometricNamed,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      CCL.OperationalEquivalence.Equivalent.toNamed_sampling
        raw.toApproximation
  change Equivalent prepared.toApproximation raw.toApproximation
  exact CCL.OperationalEquivalence.Equivalent.trans preparedToSampler
    (CCL.OperationalEquivalence.Equivalent.trans preparedToWrappedRaw
      wrappedRawToRaw)

/-- The exact-one sampler and the constant geometric one stream have the
same displayed rational sample at every index. -/
def preparedOne_equivalent_rawOne : Equivalent
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.ofNamed
      (CCL.ProgressiveCoherence.CoherentNamed.exact 1).name).toApproximation
    (CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.exact
      1).toApproximation :=
  CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq _ _
    (by intro index; exact geometricOfExact_sample 1 index)

/-- Replacing the apartified denominator sampler by its raw synchronized
source preserves the reciprocal's finite operational value. -/
def preparedReciprocal_equivalent_raw {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    Equivalent (preparedReciprocalApproximation inverseLower).toApproximation
      (rawReciprocalApproximation inverseLower).toApproximation := by
  exact quotientApproximation_respects _ _ _ _
    (preparedDenominatorLower inverseLower)
    (normalizationDenominatorLower inverseLower)
    preparedOne_equivalent_rawOne
    (preparedDenominator_equivalent_raw inverseLower)

/-- The stateful reciprocal used by persistent normalization is operationally
the equal-index reciprocal of the raw fraction-free scalar stream. -/
def inverseScalar_equivalent_rawReciprocal {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix) :
    NamedEquivalent
      (inverseScalar inverseLower.toScaledInverseCertificate).name
      (geometricNamed (rawReciprocalApproximation inverseLower)).name := by
  let inverse := inverseLower.toScaledInverseCertificate
  let one := CCL.ProgressiveCoherence.CoherentNamed.exact 1
  let sampled :=
    CCL.Riemann.OperationalQuotients.sampledQuotientApproximation one
      inverse.scalar inverse.scalarApart
  let prepared := preparedReciprocalApproximation inverseLower
  let raw := rawReciprocalApproximation inverseLower
  have actualToSampled : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.div one inverse.scalar
        inverse.scalarApart).name sampled.toNamed := by
    exact CCL.Riemann.OperationalQuotients.coherentDiv_toSampled
      one inverse.scalar inverse.scalarApart
  have sampledToPreparedApprox : Equivalent sampled prepared.toApproximation :=
    CCL.TranscendentalCoherence.approximationEquivalentOfSamplesEq _ _
      (by intro index; rfl)
  have sampledToPrepared : NamedEquivalent sampled.toNamed
      (geometricNamed prepared).name := by
    simpa only [geometricNamed,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      CCL.TranscendentalCoherence.approximationEquivalent_toNamed
        sampledToPreparedApprox
  have preparedToRaw : NamedEquivalent (geometricNamed prepared).name
      (geometricNamed raw).name := by
    simpa only [geometricNamed,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
      CCL.TranscendentalCoherence.approximationEquivalent_toNamed
        (preparedReciprocal_equivalent_raw inverseLower)
  change NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.div one inverse.scalar
      inverse.scalarApart).name (geometricNamed raw).name
  exact CCL.OperationalEquivalence.NamedEquivalent.trans actualToSampled
    (CCL.OperationalEquivalence.NamedEquivalent.trans sampledToPrepared
      preparedToRaw)

/-- Persistent fraction-free matrix multiplication realizes the same
equal-index `adj(A)B` numerator used by synchronized normalization. -/
def normalizationNumerator_equivalent {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    {data : PeriodData curve}
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) :
    NamedEquivalent
      (matrixMul inverseLower.toScaledInverseCertificate.adjugate
        data.bMatrix row column).name
      (geometricNamed (normalizationNumerator data row column)).name := by
  let inverse := inverseLower.toScaledInverseCertificate
  let computed := canonicalScaledInverse data.aMatrix
  let bSource := geometricMatrixOfNamed data.bMatrix
  have equivalent := matrixMul_equivalent_geometricProduct
    inverse.adjugate data.bMatrix computed.inverse bSource
    (fun leftRow leftColumn => by
      simpa only [inverse, ScaledInverseCertificate.adjugate,
        canonicalAdjugate_apply, computed] using
        CCL.OperationalEquivalence.NamedEquivalent.refl
          (geometricNamed (computed.inverse leftRow leftColumn)).name)
    (fun rightRow rightColumn => by
      simpa only [bSource, geometricMatrixOfNamed_apply] using
        named_equivalent_geometricOfNamed
          (data.bMatrix rightRow rightColumn))
    row column
  simpa only [inverse, computed, bSource, normalizationNumerator] using
    equivalent

/-- Every persistent normalized period entry is operationally equivalent to
the geometric approximation whose index-`n` sample is literally the raw
synchronized normalized matrix at index `n`. -/
def normalizedEntry_equivalent_synchronized {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) :
    NamedEquivalent
      ((CCL.Riemann.FiniteEnergy.normalizedData data inverseLower).omega
        row column).name
      (geometricNamed
        (synchronizedEntryApproximation data inverseLower row column)).name := by
  let inverse := inverseLower.toScaledInverseCertificate
  let numerator := matrixMul inverse.adjugate data.bMatrix row column
  let reciprocal := inverseScalar inverse
  let numeratorSource := normalizationNumerator data row column
  let reciprocalSource := rawReciprocalApproximation inverseLower
  let productSource :=
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.mul
      numeratorSource reciprocalSource
  let synchronizedSource :=
    synchronizedEntryApproximation data inverseLower row column
  have productEquivalent : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul numerator reciprocal).name
      (geometricNamed productSource).name := by
    exact coherentMul_equivalent_geometricMul numerator reciprocal
      numeratorSource reciprocalSource
      (by simpa only [numerator, inverse] using
        normalizationNumerator_equivalent inverseLower row column)
      (by simpa only [reciprocal, reciprocalSource, inverse] using
        inverseScalar_equivalent_rawReciprocal inverseLower)
  have productSamples : forall index, productSource.sample index =
      synchronizedSource.sample index := by
    intro index
    change
      (normalizationNumerator data row column).sample index *
          ((1 : Gaussian) /
            (normalizationDenominator data).sample index) =
        (normalizationNumerator data row column).sample index /
          (normalizationDenominator data).sample index
    rw [RFAP.ExplicitField.div_eq_mul_inv,
      RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  have productToSynchronized : NamedEquivalent
      (geometricNamed productSource).name
      (geometricNamed synchronizedSource).name :=
    geometricNamed_equivalent_of_samples productSource synchronizedSource
      productSamples
  have result := CCL.OperationalEquivalence.NamedEquivalent.trans
    productEquivalent productToSynchronized
  simpa only [CCL.Riemann.FiniteEnergy.normalizedData,
    NormalizedPeriodData.omega, normalize_apply, numerator, reciprocal,
    inverse, synchronizedSource] using result

/-- Approximation-level form, exposing the raw synchronized sample index on
the right rather than resampling its productive wrapper. -/
def normalizedEntry_equivalent_synchronizedApproximation {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (row column : Fin genus) :
    Equivalent
      (CCL.ProgressiveSampling.approximation
        ((CCL.Riemann.FiniteEnergy.normalizedData data inverseLower).omega
          row column).name)
      (synchronizedEntryApproximation data inverseLower row column).toApproximation :=
  CCL.OperationalEquivalence.Equivalent.trans
    (normalizedEntry_equivalent_synchronized data inverseLower row column)
    (by
      simpa only [geometricNamed,
        CCL.ProgressiveCoherence.CoherentNamed.ofApproximation] using
        CCL.OperationalEquivalence.Equivalent.toNamed_sampling
          (synchronizedEntryApproximation data inverseLower row column).toApproximation)

/-! ## One shared finite comparison index -/

/-- A deliberately conservative squared comparison allowance. -/
def comparisonTarget (radius : Coordinate) : Coordinate :=
  radius ^ 2 / 64

theorem comparisonTarget_positive {radius : Coordinate}
    (positive : 0 < radius) : 0 < comparisonTarget radius := by
  unfold comparisonTarget
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.pow_pos_direct positive 2)
    (RFAP.ConstructiveFraction.natCast_pos_direct (n := 64) (by omega))

theorem thirtyEight_comparisonTarget_lt_sq {radius : Coordinate}
    (positive : 0 < radius) : 38 * comparisonTarget radius < radius ^ 2 := by
  have squarePositive : 0 < radius ^ 2 :=
    RFAP.ConstructiveFraction.pow_pos_direct positive 2
  have sixtyFourPositive : (0 : Coordinate) < 64 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 64) (by omega)
  have fractionSmall : (38 : Coordinate) / 64 < 1 := by
    apply (RFAP.ConstructiveFraction.div_lt_iff_pos sixtyFourPositive).2
    calc
      (38 : Coordinate) < (64 : Coordinate) :=
        RFAP.ConstructiveFraction.natCast_lt_direct
          (m := 38) (n := 64) (by omega)
      _ = 1 * 64 := by ring1
  calc
    38 * comparisonTarget radius = radius ^ 2 * ((38 : Coordinate) / 64) := by
      unfold comparisonTarget
      rw [RFAP.ExplicitField.div_eq_mul_inv,
        RFAP.ExplicitField.div_eq_mul_inv]
      ring1
    _ < radius ^ 2 * 1 :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
        squarePositive fractionSmall
    _ = radius ^ 2 := RFAP.ConstructiveFraction.mul_one_direct _

/-- Constructive maximum of a visibly finite family of natural indices. -/
def finMax : {count : Nat} -> (Fin count -> Nat) -> Nat
  | 0, _ => 0
  | count + 1, values =>
      max (values 0) (finMax fun index : Fin count => values index.succ)

theorem le_finMax {count : Nat} (values : Fin count -> Nat)
    (index : Fin count) : values index <= finMax values := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count inductionHypothesis =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · exact Nat.le_max_left _ _
      · exact (inductionHypothesis
          (fun entry : Fin count => values entry.succ) tail).trans
            (Nat.le_max_right _ _)

/-- Constructive maximum over the finite square matrix of entry indices. -/
def matrixMax {size : Nat} (values : Fin size -> Fin size -> Nat) : Nat :=
  finMax fun row => finMax (values row)

theorem le_matrixMax {size : Nat} (values : Fin size -> Fin size -> Nat)
    (row column : Fin size) : values row column <= matrixMax values :=
  (le_finMax (values row) column).trans
    (le_finMax (fun entry => finMax (values entry)) row)

/-- First canonical sampler index at which one normalized entry has small
enough semantic allowance for the matrix comparison. -/
def entryComparisonStart {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (row column : Fin genus) : Nat :=
  let entry :=
    (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower).omega row column
  CCL.FiniteGeometric.firstQuarterBelow 1 0
    (entry.coherent.accuracyRequest (comparisonTarget radius))

/-- One entry's fully computed operational comparison with the raw
synchronized normalization stream. -/
def entryComparison {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    CCL.OperationalEquivalence.Comparison
      (CCL.ProgressiveSampling.approximation
        ((CCL.Riemann.FiniteEnergy.normalizedData data inverseLower).omega
          row column).name)
      (synchronizedEntryApproximation data inverseLower row column).toApproximation
      (entryComparisonStart data inverseLower radius row column) 0
      (comparisonTarget radius) :=
  (normalizedEntry_equivalent_synchronizedApproximation data inverseLower
    row column).compare
      (entryComparisonStart data inverseLower radius row column) 0
      (comparisonTarget radius) (comparisonTarget_positive positive)

/-- One later persistent sampler index shared by every matrix entry. -/
def persistentSampleIndex {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius) : Nat :=
  matrixMax fun row column =>
    (entryComparison data inverseLower radius positive row column).leftIndex

/-- One raw synchronized sample index shared by every matrix entry. -/
def synchronizedSampleIndex {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius) : Nat :=
  matrixMax fun row column =>
    (entryComparison data inverseLower radius positive row column).rightIndex

theorem entryComparison_left_le_persistentSampleIndex {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    (entryComparison data inverseLower radius positive row column).leftIndex <=
      persistentSampleIndex data inverseLower radius positive :=
  by
    simpa only [persistentSampleIndex] using
      (le_matrixMax (fun leftRow leftColumn =>
        (entryComparison data inverseLower radius positive
          leftRow leftColumn).leftIndex) row column)

theorem entryComparison_right_le_synchronizedSampleIndex {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    (entryComparison data inverseLower radius positive row column).rightIndex <=
      synchronizedSampleIndex data inverseLower radius positive :=
  by
    simpa only [synchronizedSampleIndex] using
      (le_matrixMax (fun leftRow leftColumn =>
        (entryComparison data inverseLower radius positive
          leftRow leftColumn).rightIndex) row column)

theorem entryComparisonStart_le_persistentSampleIndex {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    entryComparisonStart data inverseLower radius row column <=
      persistentSampleIndex data inverseLower radius positive :=
  (entryComparison data inverseLower radius positive row column).left_ge.trans
    (entryComparison_left_le_persistentSampleIndex data inverseLower radius
      positive row column)

/-- The shared persistent sampler index has the small semantic allowance
requested before the entrywise operational comparisons. -/
theorem persistentSampleAllowance_lt {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    let entry :=
      (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower).omega
        row column
    entry.coherent.allowance
        (CCL.ProgressiveSampling.stateAt entry.name.process entry.name.state
          (persistentSampleIndex data inverseLower radius positive)) <
      comparisonTarget radius := by
  let entry :=
    (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower).omega row column
  let start := entryComparisonStart data inverseLower radius row column
  let persistent := persistentSampleIndex data inverseLower radius positive
  have requestPositive :
      0 < entry.coherent.accuracyRequest (comparisonTarget radius) :=
    entry.coherent.accuracyRequest_pos (comparisonTarget_positive positive)
  have startAccurate :
      CCL.ProgressiveSampling.refinementTarget start <
        entry.coherent.accuracyRequest (comparisonTarget radius) := by
    exact CCL.FiniteGeometric.firstQuarterBelow_accurate 1 (by decide) 0
      (entry.coherent.accuracyRequest (comparisonTarget radius))
      requestPositive
  have startOrder : start <= persistent := by
    exact entryComparisonStart_le_persistentSampleIndex data inverseLower
      radius positive row column
  have persistentRequestSmall :
      CCL.ProgressiveSampling.refinementTarget persistent <
        entry.coherent.accuracyRequest (comparisonTarget radius) :=
    (CCL.FiniteGeometric.quarterRadius_antitone (by decide) startOrder).trans_lt
      startAccurate
  exact CCL.ProgressiveCoherence.Coherent.stateAt_allowance_lt entry.coherent
    entry.name.state persistent (comparisonTarget radius)
    (comparisonTarget_positive positive) persistentRequestSmall

/-- All entries can be evaluated at the one maximum raw index while retaining
the strict operational comparison bound. -/
theorem persistentSample_close_synchronized {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (radius : Coordinate) (positive : 0 < radius)
    (row column : Fin genus) :
    normSq
        ((CCL.ProgressiveSampling.approximation
            ((CCL.Riemann.FiniteEnergy.normalizedData data inverseLower).omega
              row column).name).sample
            (persistentSampleIndex data inverseLower radius positive) -
          CCL.Riemann.FiniteEnergy.synchronizedNormalizedMatrix data
            (synchronizedSampleIndex data inverseLower radius positive)
            row column) <
      comparisonTarget radius := by
  have close :=
    (entryComparison data inverseLower radius positive row column).close
      (entryComparison_left_le_persistentSampleIndex data inverseLower radius
        positive row column)
      (entryComparison_right_le_synchronizedSampleIndex data inverseLower
        radius positive row column)
  simpa only [
    CCL.Riemann.FiniteMatrixApproximation.GeometricApproximation.toApproximation_sample,
    synchronizedEntryApproximation_sample] using close

/-- A sufficiently fine shared persistent request is automatically close to
the one computed raw synchronized matrix.  The proof compares only finite
process witnesses, finite coherence allowances, and rational squared-error
budgets. -/
theorem centerMatrix_close_synchronized {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (comparisonRadius : Coordinate) (comparisonPositive : 0 < comparisonRadius)
    (centerTarget : Coordinate) (centerPositive : 0 < centerTarget)
    (centerSmall : centerTarget < comparisonTarget comparisonRadius)
    (row column : Fin genus) :
    normSq
        (CCL.Riemann.FinitePositivity.centerMatrix
            (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower)
            centerTarget centerPositive row column -
          CCL.Riemann.FiniteEnergy.synchronizedNormalizedMatrix data
            (synchronizedSampleIndex data inverseLower comparisonRadius
              comparisonPositive) row column) <
      comparisonRadius ^ 2 := by
  let normalized := CCL.Riemann.FiniteEnergy.normalizedData data inverseLower
  let entry := normalized.omega row column
  let refined := normalized.refinedOmegaEntry centerTarget centerPositive
    row column
  let center := (refined.process.ball refined.state).center
  let witness := (refined.process.witness refined.state).val
  let persistent :=
    persistentSampleIndex data inverseLower comparisonRadius comparisonPositive
  let persistentValue :=
    (CCL.ProgressiveSampling.approximation entry.name).sample persistent
  let rawIndex :=
    synchronizedSampleIndex data inverseLower comparisonRadius
      comparisonPositive
  let rawValue :=
    CCL.Riemann.FiniteEnergy.synchronizedNormalizedMatrix data rawIndex
      row column
  have ballRadiusLt :
      (refined.process.ball refined.state).radiusSq < centerTarget := by
    simpa only [refined, NormalizedPeriodData.omegaRadiusSq,
      NormalizedPeriodData.refinedOmegaEntry] using
      normalized.omegaRadiusSq_lt_target centerTarget centerPositive row column
  have centerAllowanceLt :
      entry.coherent.allowance refined.state < centerTarget := by
    have contract := normalized.omegaEntry_sharedRequest row column
      centerTarget centerPositive 0
    simpa only [entry, refined, NormalizedPeriodData.refinedOmegaEntry] using
      contract.2.1
  have persistentAllowanceLt :
      entry.coherent.allowance
          (CCL.ProgressiveSampling.stateAt entry.name.process entry.name.state
            persistent) < comparisonTarget comparisonRadius := by
    simpa only [entry, persistent, normalized] using
      persistentSampleAllowance_lt data inverseLower comparisonRadius
        comparisonPositive row column
  have refinedPossible : entry.name.process.Possible refined.state witness := by
    exact (refined.process.witness refined.state).property
  have persistentPossible : entry.name.process.Possible
      (CCL.ProgressiveSampling.stateAt entry.name.process entry.name.state
        persistent) persistentValue := by
    exact CCL.ProgressiveSampling.witnessAt_possible entry.name.process
      entry.name.state persistent
  have witnessInside := entry.name.process.possible_inside refinedPossible
  have centerWitness : normSq (center - witness) <=
      (refined.process.ball refined.state).radiusSq := by
    have identity : center - witness = -(witness - center) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
    rw [identity, normSq_neg]
    exact witnessInside
  have semanticClose : normSq (witness - persistentValue) <=
      4 * (entry.coherent.allowance refined.state +
        entry.coherent.allowance
          (CCL.ProgressiveSampling.stateAt entry.name.process entry.name.state
            persistent)) :=
    entry.coherent.possible_close refinedPossible persistentPossible
  have semanticSmall : normSq (witness - persistentValue) <
      4 * (centerTarget + comparisonTarget comparisonRadius) :=
    semanticClose.trans_lt
      (RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct (by decide)
        (RFAP.ConstructiveFraction.add_lt_add_direct centerAllowanceLt
          persistentAllowanceLt))
  have operationalSmall : normSq (persistentValue - rawValue) <
      comparisonTarget comparisonRadius := by
    simpa only [persistentValue, rawValue, persistent, rawIndex, entry,
      normalized] using
      persistentSample_close_synchronized data inverseLower comparisonRadius
        comparisonPositive row column
  have witnessRawSmall : normSq (witness - rawValue) <
      2 * (4 * (centerTarget + comparisonTarget comparisonRadius) +
        comparisonTarget comparisonRadius) := by
    calc
      normSq (witness - rawValue) <=
          2 * (normSq (witness - persistentValue) +
            normSq (persistentValue - rawValue)) :=
        normSq_sub_le_via witness persistentValue rawValue
      _ < 2 * (4 * (centerTarget + comparisonTarget comparisonRadius) +
          comparisonTarget comparisonRadius) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct (by decide)
          (RFAP.ConstructiveFraction.add_lt_add_direct semanticSmall
            operationalSmall)
  have centerRawSmall : normSq (center - rawValue) <
      18 * centerTarget + 20 * comparisonTarget comparisonRadius := by
    calc
      normSq (center - rawValue) <=
          2 * (normSq (center - witness) + normSq (witness - rawValue)) :=
        normSq_sub_le_via center witness rawValue
      _ < 2 * (centerTarget +
          2 * (4 * (centerTarget + comparisonTarget comparisonRadius) +
            comparisonTarget comparisonRadius)) :=
        RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct (by decide)
          (RFAP.ConstructiveFraction.add_lt_add_direct
            (centerWitness.trans_lt ballRadiusLt) witnessRawSmall)
      _ = 18 * centerTarget +
          20 * comparisonTarget comparisonRadius := by ring1
  have belowThirtyEight :
      18 * centerTarget + 20 * comparisonTarget comparisonRadius <
        38 * comparisonTarget comparisonRadius := by
    have scaledCenter : 18 * centerTarget <
        18 * comparisonTarget comparisonRadius :=
      RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct (by decide)
        centerSmall
    calc
      18 * centerTarget + 20 * comparisonTarget comparisonRadius <
          18 * comparisonTarget comparisonRadius +
            20 * comparisonTarget comparisonRadius :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct scaledCenter _
      _ = 38 * comparisonTarget comparisonRadius := by ring1
  have finalSmall := centerRawSmall.trans
    (belowThirtyEight.trans
      (thirtyEight_comparisonTarget_lt_sq comparisonPositive))
  simpa only [center, rawValue, rawIndex, refined, normalized,
    CCL.Riemann.FinitePositivity.centerMatrix_apply,
    NormalizedPeriodData.omegaCenter] using finalSmall

/-- Reindex the automatic comparison by a displayed equality, allowing
dependent certificate packages to keep the computed natural index opaque. -/
theorem centerMatrix_close_synchronized_of_index_eq {genus : Nat}
    {curve : CCL.Riemann.AlgebraicDifferentials.HyperellipticCurve genus}
    (data : PeriodData curve)
    (inverseLower : ScalarCandidateLowerCertificate data.aMatrix)
    (comparisonRadius : Coordinate) (comparisonPositive : 0 < comparisonRadius)
    (rawIndex : Nat)
    (rawIndex_eq : rawIndex =
      synchronizedSampleIndex data inverseLower comparisonRadius
        comparisonPositive)
    (centerTarget : Coordinate) (centerPositive : 0 < centerTarget)
    (centerSmall : centerTarget < comparisonTarget comparisonRadius)
    (row column : Fin genus) :
    normSq
        (CCL.Riemann.FinitePositivity.centerMatrix
            (CCL.Riemann.FiniteEnergy.normalizedData data inverseLower)
            centerTarget centerPositive row column -
          CCL.Riemann.FiniteEnergy.synchronizedNormalizedMatrix data
            rawIndex row column) <
      comparisonRadius ^ 2 := by
  subst rawIndex
  exact centerMatrix_close_synchronized data inverseLower comparisonRadius
    comparisonPositive centerTarget centerPositive centerSmall row column

end CCL.Riemann.SynchronizedNormalization
