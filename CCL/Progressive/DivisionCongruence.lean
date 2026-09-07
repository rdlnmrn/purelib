import CCL.Arithmetic.FiniteQuotientVariation
import CCL.Progressive.Coherence

/-!
# Core operational congruence for finite sampled quotients

Division is only continuous after a positive denominator lower bound has been
displayed.  This core file packages that constructive fact for the canonical
finite samplers of coherent CCL names.  It does not select completed values:
every quotient below is a quotient of two Gaussian rationals computed at one
finite index.
-/

namespace CCL.ProgressiveDivisionCongruence

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev Equivalent := CCL.OperationalEquivalence.Equivalent
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev Apart := CCL.ProgressiveTransducer.Named.Apart

open RFAP.ConstructiveGaussian.Gaussian

/-- Every canonical finite sample of an apart coherent name satisfies the
same displayed positive squared-norm lower bound. -/
theorem sampled_lower (value : CoherentNamed) (apart : Apart value.name)
    (index : Nat) :
    apart.certificate.lowerSq <=
      normSq ((CCL.ProgressiveSampling.approximation value.name).sample index) := by
  exact apart.certificate.lower _
    (value.name.process.possible_inside
      (CCL.ProgressiveSampling.witnessAt_possible value.name.process
        value.name.state index))

theorem sampled_nonzero (value : CoherentNamed) (apart : Apart value.name)
    (index : Nat) :
    (CCL.ProgressiveSampling.approximation value.name).sample index ≠ 0 := by
  intro zero
  have positive : 0 <
      normSq ((CCL.ProgressiveSampling.approximation value.name).sample index) :=
    apart.certificate.positive.trans_le (sampled_lower value apart index)
  rw [zero, normSq_zero] at positive
  exact (lt_irrefl _ positive).elim

/-- Geometric error scale for equal-index quotients.  The factor eight is the
finite Gaussian triangle cost combined with the canonical quarter-radius
movement of each operand sampler. -/
def sampledQuotientErrorScale (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) : Coordinate :=
  (8 *
      ((CCL.ProgressiveSampling.approximation denominator.name).centerBound +
        (CCL.ProgressiveSampling.approximation numerator.name).centerBound)) /
    (apart.certificate.lowerSq * apart.certificate.lowerSq)

theorem sampledQuotientErrorScale_nonnegative
    (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) :
    0 <= sampledQuotientErrorScale numerator denominator apart := by
  unfold sampledQuotientErrorScale
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (CCL.ProgressiveSampling.approximation
          denominator.name).centerBound_nonneg
        (CCL.ProgressiveSampling.approximation
          numerator.name).centerBound_nonneg))
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      apart.certificate.positive.le apart.certificate.positive.le)

/-- Equal-index finite Gaussian quotients of two canonical CCL samplers. -/
def sampledQuotientApproximation (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) : Approximation where
  sample index :=
    (CCL.ProgressiveSampling.approximation numerator.name).sample index /
      (CCL.ProgressiveSampling.approximation denominator.name).sample index
  radiusSq := CCL.FiniteGeometric.quarterRadius
    (sampledQuotientErrorScale numerator denominator apart)
  radiusSq_nonneg := CCL.FiniteGeometric.quarterRadius_nonneg
    (sampledQuotientErrorScale_nonnegative numerator denominator apart)
  later_close := by
    intro earlier later order
    let numeratorSource :=
      CCL.ProgressiveSampling.approximation numerator.name
    let denominatorSource :=
      CCL.ProgressiveSampling.approximation denominator.name
    have numeratorMovement :
        normSq (numeratorSource.sample later -
            numeratorSource.sample earlier) <=
          CCL.FiniteGeometric.quarterRadius 4 earlier := by
      simpa only [numeratorSource, CCL.ProgressiveSampling.approximation]
        using numeratorSource.later_close order
    have denominatorMovementForward :
        normSq (denominatorSource.sample later -
            denominatorSource.sample earlier) <=
          CCL.FiniteGeometric.quarterRadius 4 earlier := by
      simpa only [denominatorSource, CCL.ProgressiveSampling.approximation]
        using denominatorSource.later_close order
    have denominatorMovement :
        normSq (denominatorSource.sample earlier -
            denominatorSource.sample later) <=
          CCL.FiniteGeometric.quarterRadius 4 earlier := by
      have identity : denominatorSource.sample earlier -
          denominatorSource.sample later =
            -(denominatorSource.sample later -
              denominatorSource.sample earlier) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
      rw [identity, normSq_neg]
      exact denominatorMovementForward
    have quotientBound :=
      CCL.ArithmeticFiniteQuotientVariation.normSq_div_sub_div_le
        apart.certificate.positive
        (leftNumerator := numeratorSource.sample later)
        (rightNumerator := numeratorSource.sample earlier)
        (leftDenominator := denominatorSource.sample later)
        (rightDenominator := denominatorSource.sample earlier)
        (numeratorSlope := (1 : Coordinate))
        (numeratorBound := numeratorSource.centerBound)
        (denominatorBound := denominatorSource.centerBound)
        (pointMovement := CCL.FiniteGeometric.quarterRadius 4 earlier)
        (rootMovement := CCL.FiniteGeometric.quarterRadius 4 earlier)
        (by
          simpa only [RFAP.ConstructiveFraction.one_mul]
            using numeratorMovement)
        (numeratorSource.sample_bounded earlier)
        (denominatorSource.sample_bounded earlier)
        denominatorMovement
        (sampled_lower denominator apart later)
        (sampled_lower denominator apart earlier)
    change normSq
        (numeratorSource.sample later / denominatorSource.sample later -
          numeratorSource.sample earlier / denominatorSource.sample earlier) <=
      CCL.FiniteGeometric.quarterRadius
        (sampledQuotientErrorScale numerator denominator apart) earlier
    calc
      normSq
          (numeratorSource.sample later / denominatorSource.sample later -
            numeratorSource.sample earlier /
              denominatorSource.sample earlier) <=
        CCL.ArithmeticFiniteQuotientVariation.quotientBound
          1 numeratorSource.centerBound denominatorSource.centerBound
          apart.certificate.lowerSq
          (CCL.FiniteGeometric.quarterRadius 4 earlier)
          (CCL.FiniteGeometric.quarterRadius 4 earlier) := quotientBound
      _ = CCL.FiniteGeometric.quarterRadius
          (sampledQuotientErrorScale numerator denominator apart) earlier := by
        rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
          CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
        dsimp only [numeratorSource, denominatorSource]
        unfold CCL.ArithmeticFiniteQuotientVariation.quotientBound
          sampledQuotientErrorScale
        let geometric : Coordinate := (1 / 4 : Coordinate) ^ earlier
        change
          (2 *
              (1 * (4 * geometric) *
                  (CCL.ProgressiveSampling.approximation
                    denominator.name).centerBound +
                (CCL.ProgressiveSampling.approximation
                    numerator.name).centerBound * (4 * geometric))) /
              (apart.certificate.lowerSq * apart.certificate.lowerSq) =
            ((8 *
                ((CCL.ProgressiveSampling.approximation
                    denominator.name).centerBound +
                  (CCL.ProgressiveSampling.approximation
                    numerator.name).centerBound)) /
                (apart.certificate.lowerSq * apart.certificate.lowerSq)) *
              geometric
        rw [RFAP.ExplicitField.div_eq_mul_inv,
          RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  refineIndex current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow
      (sampledQuotientErrorScale numerator denominator apart) current target
  refineIndex_ge current target _ :=
    CCL.FiniteGeometric.firstQuarterBelow_ge
      (sampledQuotientErrorScale numerator denominator apart) current target
  refineIndex_accurate := CCL.FiniteGeometric.firstQuarterBelow_accurate
    (sampledQuotientErrorScale numerator denominator apart)
    (sampledQuotientErrorScale_nonnegative numerator denominator apart)
  centerBound :=
    (CCL.ProgressiveSampling.approximation numerator.name).centerBound /
      apart.certificate.lowerSq
  centerBound_nonneg := RFAP.ConstructiveFraction.div_nonneg_direct
    (CCL.ProgressiveSampling.approximation numerator.name).centerBound_nonneg
    apart.certificate.positive.le
  sample_bounded := by
    intro index
    let numeratorSource :=
      CCL.ProgressiveSampling.approximation numerator.name
    let denominatorSource :=
      CCL.ProgressiveSampling.approximation denominator.name
    have denominatorLower := sampled_lower denominator apart index
    have denominatorPositive : 0 < normSq (denominatorSource.sample index) :=
      apart.certificate.positive.trans_le denominatorLower
    have denominatorNonzero : denominatorSource.sample index ≠ 0 := by
      intro zero
      rw [zero, normSq_zero] at denominatorPositive
      exact (lt_irrefl _ denominatorPositive).elim
    rw [normSq_div _ _ denominatorNonzero]
    calc
      normSq (numeratorSource.sample index) /
          normSq (denominatorSource.sample index) <=
        normSq (numeratorSource.sample index) /
          apart.certificate.lowerSq :=
        RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
          (normSq_nonneg _) apart.certificate.positive denominatorLower
      _ <= numeratorSource.centerBound / apart.certificate.lowerSq := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (numeratorSource.sample_bounded index)
          (RFAP.ConstructiveFraction.inv_pos_direct
            apart.certificate.positive).le

@[simp] theorem sampledQuotientApproximation_sample
    (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) (index : Nat) :
    (sampledQuotientApproximation numerator denominator apart).sample index =
      (CCL.ProgressiveSampling.approximation numerator.name).sample index /
        (CCL.ProgressiveSampling.approximation denominator.name).sample index :=
  rfl

/-- One positive lower bound shared by two independently apart denominator
names. -/
def commonLower {first second : CoherentNamed}
    (firstApart : Apart first.name) (secondApart : Apart second.name) :
    Coordinate :=
  min firstApart.certificate.lowerSq secondApart.certificate.lowerSq

theorem commonLower_positive {first second : CoherentNamed}
    (firstApart : Apart first.name) (secondApart : Apart second.name) :
    0 < commonLower firstApart secondApart :=
  lt_min firstApart.certificate.positive secondApart.certificate.positive

/-- Sensitivity coefficient for comparing two quotients. -/
def quotientComparisonCoefficient
    (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Apart firstDenominator.name)
    (secondApart : Apart secondDenominator.name) : Coordinate :=
  (2 *
      ((CCL.ProgressiveSampling.approximation
          secondDenominator.name).centerBound +
        (CCL.ProgressiveSampling.approximation
          secondNumerator.name).centerBound)) /
    (commonLower firstApart secondApart *
      commonLower firstApart secondApart)

theorem quotientComparisonCoefficient_nonnegative
    (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Apart firstDenominator.name)
    (secondApart : Apart secondDenominator.name) :
    0 <= quotientComparisonCoefficient secondNumerator secondDenominator
      firstApart secondApart := by
  unfold quotientComparisonCoefficient
  exact RFAP.ConstructiveFraction.div_nonneg_direct
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg
        (CCL.ProgressiveSampling.approximation
          secondDenominator.name).centerBound_nonneg
        (CCL.ProgressiveSampling.approximation
          secondNumerator.name).centerBound_nonneg))
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (commonLower_positive firstApart secondApart).le
      (commonLower_positive firstApart secondApart).le)

def quotientComparisonTarget
    (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Apart firstDenominator.name)
    (secondApart : Apart secondDenominator.name)
    (target : Coordinate) : Coordinate :=
  target / (1 + quotientComparisonCoefficient secondNumerator
    secondDenominator firstApart secondApart)

theorem quotientComparisonTarget_positive
    (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Apart firstDenominator.name)
    (secondApart : Apart secondDenominator.name)
    {target : Coordinate} (positive : 0 < target) :
    0 < quotientComparisonTarget secondNumerator secondDenominator
      firstApart secondApart target :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (add_pos_of_pos_of_nonneg (by decide)
      (quotientComparisonCoefficient_nonnegative secondNumerator
        secondDenominator firstApart secondApart))

theorem quotientComparisonTarget_budget_lt
    (secondNumerator secondDenominator : CoherentNamed)
    {firstDenominator : CoherentNamed}
    (firstApart : Apart firstDenominator.name)
    (secondApart : Apart secondDenominator.name)
    {target : Coordinate} (positive : 0 < target) :
    quotientComparisonTarget secondNumerator secondDenominator
        firstApart secondApart target *
      quotientComparisonCoefficient secondNumerator secondDenominator
        firstApart secondApart < target := by
  let coefficient := quotientComparisonCoefficient secondNumerator
    secondDenominator firstApart secondApart
  have coefficientNonnegative : 0 <= coefficient :=
    quotientComparisonCoefficient_nonnegative secondNumerator
      secondDenominator firstApart secondApart
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

/-- Canonical finite quotient approximations respect operational equality in
both operands, provided each denominator carries its own explicit positive
lower bound. -/
def sampledQuotientApproximation_respects
    (firstNumerator secondNumerator firstDenominator secondDenominator :
      CoherentNamed)
    (firstApart : Apart firstDenominator.name)
    (secondApart : Apart secondDenominator.name)
    (numeratorEquivalent : NamedEquivalent firstNumerator.name
      secondNumerator.name)
    (denominatorEquivalent : NamedEquivalent firstDenominator.name
      secondDenominator.name) :
    Equivalent
      (sampledQuotientApproximation firstNumerator firstDenominator firstApart)
      (sampledQuotientApproximation secondNumerator secondDenominator
        secondApart) where
  compare := by
    intro firstStart secondStart target positive
    let inputTarget := quotientComparisonTarget secondNumerator
      secondDenominator firstApart secondApart target
    have inputPositive : 0 < inputTarget :=
      quotientComparisonTarget_positive secondNumerator secondDenominator
        firstApart secondApart positive
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
          let firstNumeratorSource :=
            CCL.ProgressiveSampling.approximation firstNumerator.name
          let secondNumeratorSource :=
            CCL.ProgressiveSampling.approximation secondNumerator.name
          let firstDenominatorSource :=
            CCL.ProgressiveSampling.approximation firstDenominator.name
          let secondDenominatorSource :=
            CCL.ProgressiveSampling.approximation secondDenominator.name
          have numeratorClose := numeratorComparison.close
            ((Nat.le_max_left numeratorComparison.leftIndex
              denominatorComparison.leftIndex).trans firstOrder)
            ((Nat.le_max_left numeratorComparison.rightIndex
              denominatorComparison.rightIndex).trans secondOrder)
          have denominatorCloseForward := denominatorComparison.close
            ((Nat.le_max_right numeratorComparison.leftIndex
              denominatorComparison.leftIndex).trans firstOrder)
            ((Nat.le_max_right numeratorComparison.rightIndex
              denominatorComparison.rightIndex).trans secondOrder)
          have denominatorClose :
              normSq (secondDenominatorSource.sample secondLater -
                  firstDenominatorSource.sample firstLater) <= inputTarget := by
            have identity :
                secondDenominatorSource.sample secondLater -
                    firstDenominatorSource.sample firstLater =
                  -(firstDenominatorSource.sample firstLater -
                    secondDenominatorSource.sample secondLater) := by
              apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
            rw [identity, normSq_neg]
            exact denominatorCloseForward.le
          have commonFirst : commonLower firstApart secondApart <=
              normSq (firstDenominatorSource.sample firstLater) :=
            (min_le_left _ _).trans
              (sampled_lower firstDenominator firstApart firstLater)
          have commonSecond : commonLower firstApart secondApart <=
              normSq (secondDenominatorSource.sample secondLater) :=
            (min_le_right _ _).trans
              (sampled_lower secondDenominator secondApart secondLater)
          have quotientBound :=
            CCL.ArithmeticFiniteQuotientVariation.normSq_div_sub_div_le
              (commonLower_positive firstApart secondApart)
              (leftNumerator := firstNumeratorSource.sample firstLater)
              (rightNumerator := secondNumeratorSource.sample secondLater)
              (leftDenominator := firstDenominatorSource.sample firstLater)
              (rightDenominator := secondDenominatorSource.sample secondLater)
              (numeratorSlope := (1 : Coordinate))
              (numeratorBound := secondNumeratorSource.centerBound)
              (denominatorBound := secondDenominatorSource.centerBound)
              (pointMovement := inputTarget)
              (rootMovement := inputTarget)
              (by
                simpa only [RFAP.ConstructiveFraction.one_mul]
                  using numeratorClose.le)
              (secondNumeratorSource.sample_bounded secondLater)
              (secondDenominatorSource.sample_bounded secondLater)
              denominatorClose commonFirst commonSecond
          change normSq
              (firstNumeratorSource.sample firstLater /
                  firstDenominatorSource.sample firstLater -
                secondNumeratorSource.sample secondLater /
                  secondDenominatorSource.sample secondLater) < target
          calc
            normSq
                (firstNumeratorSource.sample firstLater /
                    firstDenominatorSource.sample firstLater -
                  secondNumeratorSource.sample secondLater /
                    secondDenominatorSource.sample secondLater) <=
              CCL.ArithmeticFiniteQuotientVariation.quotientBound
                1 secondNumeratorSource.centerBound
                secondDenominatorSource.centerBound
                (commonLower firstApart secondApart) inputTarget inputTarget :=
              quotientBound
            _ = inputTarget *
                quotientComparisonCoefficient secondNumerator
                  secondDenominator firstApart secondApart := by
              dsimp only [firstNumeratorSource, secondNumeratorSource,
                firstDenominatorSource, secondDenominatorSource]
              unfold CCL.ArithmeticFiniteQuotientVariation.quotientBound
                quotientComparisonCoefficient
              rw [RFAP.ExplicitField.div_eq_mul_inv,
                RFAP.ExplicitField.div_eq_mul_inv]
              ring1
            _ < target := quotientComparisonTarget_budget_lt
              secondNumerator secondDenominator firstApart secondApart positive }

/-! ## The actual stateful division process -/

private theorem quotient_refine_component_allowance_lt
    {numeratorProcess denominatorProcess : CCL.ProgressiveEnclosures.Process}
    (numeratorCoherent : CCL.ProgressiveCoherence.Coherent numeratorProcess)
    (denominatorCoherent : CCL.ProgressiveCoherence.Coherent denominatorProcess)
    (apart : CCL.ProgressiveEnclosures.Process.Apart denominatorProcess)
    (state : numeratorProcess.State × denominatorProcess.State)
    (request : Coordinate) (requestPositive : 0 < request)
    (target : Coordinate) (targetPositive : 0 < target)
    (requestSmall : request <
      CCL.ProgressiveCoherence.Coherent.divisionOuterTarget
        numeratorProcess denominatorProcess apart.lowerSq
        (CCL.ProgressiveCoherence.Coherent.commonRequest
          (numeratorCoherent.accuracyRequest target)
          (denominatorCoherent.accuracyRequest target))) :
    let refined := (numeratorProcess.div denominatorProcess apart).refine
      state request requestPositive
    numeratorCoherent.allowance refined.1 < target ∧
      denominatorCoherent.allowance refined.2 < target := by
  let numeratorRequest := numeratorCoherent.accuracyRequest target
  let denominatorRequest := denominatorCoherent.accuracyRequest target
  have numeratorRequestPositive : 0 < numeratorRequest :=
    numeratorCoherent.accuracyRequest_pos targetPositive
  have denominatorRequestPositive : 0 < denominatorRequest :=
    denominatorCoherent.accuracyRequest_pos targetPositive
  let sharedRequest := CCL.ProgressiveCoherence.Coherent.commonRequest
    numeratorRequest denominatorRequest
  let numeratorName := CCL.ProgressiveEnclosures.Name.centerOnly
    (numeratorProcess.ball state.1).center numeratorProcess.centerBound
      numeratorProcess.centerBound_nonneg
        (numeratorProcess.center_bounded state.1)
  let denominatorName := CCL.ProgressiveEnclosures.Name.centerOnly
    (denominatorProcess.ball state.2).center denominatorProcess.centerBound
      denominatorProcess.centerBound_nonneg
        (denominatorProcess.center_bounded state.2)
  let inputRequest := CCL.ProgressiveEnclosures.Name.divisionInputTarget
    numeratorName denominatorName apart.lowerSq request
  have inputPositive : 0 < inputRequest :=
    CCL.ProgressiveEnclosures.Name.divisionInputTarget_pos
      numeratorName denominatorName apart.lowerSq apart.positive
        requestPositive
  have inputLtShared : inputRequest < sharedRequest :=
    CCL.ProgressiveCoherence.Coherent.processDivisionInputTarget_lt
      numeratorName denominatorName rfl rfl apart.positive requestSmall
  have inputLtNumerator : inputRequest < numeratorRequest :=
    inputLtShared.trans
      (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
        numeratorRequestPositive denominatorRequestPositive)
  have inputLtDenominator : inputRequest < denominatorRequest :=
    inputLtShared.trans
      (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
        numeratorRequestPositive denominatorRequestPositive)
  change
    numeratorCoherent.allowance
        (numeratorProcess.refine state.1 inputRequest inputPositive) < target ∧
      denominatorCoherent.allowance
        (denominatorProcess.refine state.2 inputRequest inputPositive) < target
  exact
    ⟨numeratorCoherent.refine_accurate state.1 target targetPositive
        inputRequest inputPositive inputLtNumerator,
      denominatorCoherent.refine_accurate state.2 target targetPositive
        inputRequest inputPositive inputLtDenominator⟩

private theorem quotient_stateAt_component_allowance_lt
    {numeratorProcess denominatorProcess : CCL.ProgressiveEnclosures.Process}
    (numeratorCoherent : CCL.ProgressiveCoherence.Coherent numeratorProcess)
    (denominatorCoherent : CCL.ProgressiveCoherence.Coherent denominatorProcess)
    (apart : CCL.ProgressiveEnclosures.Process.Apart denominatorProcess)
    (start : numeratorProcess.State × denominatorProcess.State)
    (index : Nat) (target : Coordinate) (targetPositive : 0 < target)
    (requestSmall : CCL.ProgressiveSampling.refinementTarget index <
      CCL.ProgressiveCoherence.Coherent.divisionOuterTarget
        numeratorProcess denominatorProcess apart.lowerSq
        (CCL.ProgressiveCoherence.Coherent.commonRequest
          (numeratorCoherent.accuracyRequest target)
          (denominatorCoherent.accuracyRequest target))) :
    let state := CCL.ProgressiveSampling.stateAt
      (numeratorProcess.div denominatorProcess apart) start index
    numeratorCoherent.allowance state.1 < target ∧
      denominatorCoherent.allowance state.2 < target := by
  cases index with
  | zero =>
      exact quotient_refine_component_allowance_lt numeratorCoherent
        denominatorCoherent apart start _ _ target targetPositive requestSmall
  | succ index =>
      exact quotient_refine_component_allowance_lt numeratorCoherent
        denominatorCoherent apart
          (CCL.ProgressiveSampling.stateAt
            (numeratorProcess.div denominatorProcess apart) start index)
          _ _ target targetPositive requestSmall

def coherentQuotientBridgeCoefficient
    (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) : Coordinate :=
  8 +
    (32 *
      (2 * (1 + numerator.name.process.centerBound) +
        2 * (1 + denominator.name.process.centerBound))) /
      (apart.certificate.lowerSq * apart.certificate.lowerSq)

theorem coherentQuotientBridgeCoefficient_positive
    (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) :
    0 < coherentQuotientBridgeCoefficient numerator denominator apart := by
  unfold coherentQuotientBridgeCoefficient
  apply add_pos_of_pos_of_nonneg (by decide)
  have numeratorTerm :
      0 <= 2 * (1 + numerator.name.process.centerBound) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg (by decide) numerator.name.process.centerBound_nonneg)
  have denominatorTerm :
      0 <= 2 * (1 + denominator.name.process.centerBound) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (add_nonneg (by decide) denominator.name.process.centerBound_nonneg)
  have sumTerm :
      0 <= 2 * (1 + numerator.name.process.centerBound) +
        2 * (1 + denominator.name.process.centerBound) :=
    add_nonneg numeratorTerm denominatorTerm
  have thirtyTwoNonnegative : (0 : Coordinate) <= 32 :=
    (RFAP.ConstructiveFraction.natCast_pos_direct
      (n := 32) (by omega)).le
  have bridgeNumerator :
      0 <= 32 *
        (2 * (1 + numerator.name.process.centerBound) +
          2 * (1 + denominator.name.process.centerBound)) :=
    RFAP.ConstructiveFraction.mul_nonneg_direct thirtyTwoNonnegative sumTerm
  have bridgeDenominator :
      0 <= apart.certificate.lowerSq * apart.certificate.lowerSq :=
    RFAP.ConstructiveFraction.mul_nonneg_direct
      apart.certificate.positive.le apart.certificate.positive.le
  exact RFAP.ConstructiveFraction.div_nonneg_direct bridgeNumerator
    bridgeDenominator

def coherentQuotientBridgeTarget
    (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) (target : Coordinate) : Coordinate :=
  target / (1 + coherentQuotientBridgeCoefficient numerator denominator apart)

theorem coherentQuotientBridgeTarget_positive
    (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) {target : Coordinate}
    (positive : 0 < target) :
    0 < coherentQuotientBridgeTarget numerator denominator apart target :=
  RFAP.ConstructiveFraction.div_pos_direct positive
    (add_pos (by decide)
      (coherentQuotientBridgeCoefficient_positive numerator denominator apart))

theorem coherentQuotientBridgeTarget_budget_lt
    (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) {target : Coordinate}
    (positive : 0 < target) :
    coherentQuotientBridgeTarget numerator denominator apart target *
        coherentQuotientBridgeCoefficient numerator denominator apart <
      target := by
  let coefficient :=
    coherentQuotientBridgeCoefficient numerator denominator apart
  have coefficientPositive : 0 < coefficient :=
    coherentQuotientBridgeCoefficient_positive numerator denominator apart
  have denominatorPositive : 0 < 1 + coefficient :=
    add_pos (by decide) coefficientPositive
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

private theorem quarterRadius_four_eq_four_refinementTarget (index : Nat) :
    CCL.FiniteGeometric.quarterRadius 4 index =
      4 * CCL.ProgressiveSampling.refinementTarget index := by
  rw [CCL.ProgressiveSampling.refinementTarget,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
  ring1

private theorem quarterRadius_index_antitone {scale : Coordinate}
    (scaleNonnegative : 0 <= scale) {earlier later : Nat}
    (order : earlier <= later) :
    CCL.FiniteGeometric.quarterRadius scale later <=
      CCL.FiniteGeometric.quarterRadius scale earlier := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le order
  rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
    CCL.FiniteGeometric.quarterRadius_eq_mul_pow, pow_add]
  have extraPowerLe : (1 / 4 : Coordinate) ^ extra <= 1 := by
    have powerOrder := RFAP.ConstructiveFraction.pow_le_pow_direct
      (show (0 : Coordinate) <= 1 / 4 by decide)
      (show (1 / 4 : Coordinate) <= 1 by decide) extra
    simpa only [one_pow] using powerOrder
  have earlierPowerNonnegative : 0 <= (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.pow_nonneg_direct (by decide) _
  have scaledNonnegative :
      0 <= scale * (1 / 4 : Coordinate) ^ earlier :=
    RFAP.ConstructiveFraction.mul_nonneg_direct scaleNonnegative
      earlierPowerNonnegative
  calc
    scale * ((1 / 4 : Coordinate) ^ earlier *
        (1 / 4 : Coordinate) ^ extra) =
      (scale * (1 / 4 : Coordinate) ^ earlier) *
        (1 / 4 : Coordinate) ^ extra := by ring1
    _ <= (scale * (1 / 4 : Coordinate) ^ earlier) * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        extraPowerLe scaledNonnegative
    _ = scale * (1 / 4 : Coordinate) ^ earlier := by ring1

/-- The actual stateful quotient is operationally equivalent to the
equal-index sampled quotient.  The proof refines both operand coherences only
to explicit rational requests and applies the finite quotient estimate. -/
def coherentDiv_toSampled (numerator denominator : CoherentNamed)
    (apart : Apart denominator.name) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.div numerator.name denominator.name apart)
      (sampledQuotientApproximation numerator denominator apart).toNamed := by
  let numeratorProcess := numerator.name.process
  let denominatorProcess := denominator.name.process
  let process := numeratorProcess.div denominatorProcess apart.certificate
  let start : process.State := (numerator.name.state, denominator.name.state)
  let quotient := sampledQuotientApproximation numerator denominator apart
  let bridge : Equivalent
      (CCL.ProgressiveSampling.approximation
        (CCL.ProgressiveTransducer.Named.div numerator.name denominator.name
          apart)) quotient :=
    { compare := by
        intro actualStart sampledStart target positive
        let semanticTarget := coherentQuotientBridgeTarget numerator
          denominator apart target
        have semanticPositive : 0 < semanticTarget :=
          coherentQuotientBridgeTarget_positive numerator denominator apart
            positive
        let numeratorRequest := numerator.coherent.accuracyRequest semanticTarget
        let denominatorRequest :=
          denominator.coherent.accuracyRequest semanticTarget
        have numeratorRequestPositive : 0 < numeratorRequest :=
          numerator.coherent.accuracyRequest_pos semanticPositive
        have denominatorRequestPositive : 0 < denominatorRequest :=
          denominator.coherent.accuracyRequest_pos semanticPositive
        let sharedRequest := CCL.ProgressiveCoherence.Coherent.commonRequest
          numeratorRequest denominatorRequest
        have sharedRequestPositive : 0 < sharedRequest :=
          CCL.ProgressiveCoherence.Coherent.commonRequest_pos
            numeratorRequestPositive denominatorRequestPositive
        let outerRequest :=
          CCL.ProgressiveCoherence.Coherent.divisionOuterTarget
            numeratorProcess denominatorProcess apart.certificate.lowerSq
              sharedRequest
        have outerRequestPositive : 0 < outerRequest :=
          CCL.ProgressiveCoherence.Coherent.divisionOuterTarget_pos
            numeratorProcess denominatorProcess apart.certificate.positive
              sharedRequestPositive
        let actualRequest := CCL.ProgressiveCharts.commonTarget
          outerRequest semanticTarget
        have actualRequestPositive : 0 < actualRequest :=
          CCL.ProgressiveCharts.commonTarget_pos outerRequestPositive
            semanticPositive
        let actualIndex := CCL.FiniteGeometric.firstQuarterBelow
          1 actualStart actualRequest
        have actualIndexGe : actualStart <= actualIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            1 actualStart actualRequest
        have actualRequestSmall :
            CCL.ProgressiveSampling.refinementTarget actualIndex <
              actualRequest :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            1 (by decide) actualStart actualRequest actualRequestPositive
        have actualRequestLtOuter :
            CCL.ProgressiveSampling.refinementTarget actualIndex <
              outerRequest :=
          actualRequestSmall.trans
            (CCL.ProgressiveCharts.commonTarget_lt_left outerRequestPositive
              semanticPositive)
        have actualRequestLtSemantic :
            CCL.ProgressiveSampling.refinementTarget actualIndex <
              semanticTarget :=
          actualRequestSmall.trans
            (CCL.ProgressiveCharts.commonTarget_lt_right outerRequestPositive
              semanticPositive)
        let sampledIndex := CCL.FiniteGeometric.firstQuarterBelow
          1 sampledStart sharedRequest
        have sampledIndexGe : sampledStart <= sampledIndex :=
          CCL.FiniteGeometric.firstQuarterBelow_ge
            1 sampledStart sharedRequest
        have sampledRequestSmall :
            CCL.ProgressiveSampling.refinementTarget sampledIndex <
              sharedRequest :=
          CCL.FiniteGeometric.firstQuarterBelow_accurate
            1 (by decide) sampledStart sharedRequest sharedRequestPositive
        let baseState := CCL.ProgressiveSampling.stateAt process start actualIndex
        have baseComponentSmall :
            numerator.coherent.allowance baseState.1 < semanticTarget ∧
              denominator.coherent.allowance baseState.2 < semanticTarget :=
          quotient_stateAt_component_allowance_lt numerator.coherent
            denominator.coherent apart.certificate start actualIndex
              semanticTarget semanticPositive actualRequestLtOuter
        exact
          { leftIndex := actualIndex
            rightIndex := sampledIndex
            left_ge := actualIndexGe
            right_ge := sampledIndexGe
            close := by
              intro actualLater sampledLater actualOrder sampledOrder
              have canonicalRequestSmall :
                  CCL.ProgressiveSampling.refinementTarget sampledLater <
                    sharedRequest :=
                (quarterRadius_index_antitone (by decide) sampledOrder).trans_lt
                  sampledRequestSmall
              have canonicalRequestLtNumerator :
                  CCL.ProgressiveSampling.refinementTarget sampledLater <
                    numeratorRequest :=
                canonicalRequestSmall.trans
                  (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
                    numeratorRequestPositive denominatorRequestPositive)
              have canonicalRequestLtDenominator :
                  CCL.ProgressiveSampling.refinementTarget sampledLater <
                    denominatorRequest :=
                canonicalRequestSmall.trans
                  (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
                    numeratorRequestPositive denominatorRequestPositive)
              have canonicalNumeratorSmall :
                  numerator.coherent.allowance
                      (CCL.ProgressiveSampling.stateAt numeratorProcess
                        numerator.name.state sampledLater) < semanticTarget :=
                CCL.ProgressiveCoherence.Coherent.stateAt_allowance_lt
                  numerator.coherent numerator.name.state sampledLater
                    semanticTarget semanticPositive canonicalRequestLtNumerator
              have canonicalDenominatorSmall :
                  denominator.coherent.allowance
                      (CCL.ProgressiveSampling.stateAt denominatorProcess
                        denominator.name.state sampledLater) < semanticTarget :=
                CCL.ProgressiveCoherence.Coherent.stateAt_allowance_lt
                  denominator.coherent denominator.name.state sampledLater
                    semanticTarget semanticPositive
                      canonicalRequestLtDenominator
              let numeratorReading := (numeratorProcess.witness baseState.1).val
              let denominatorReading :=
                (denominatorProcess.witness baseState.2).val
              let canonicalNumerator :=
                CCL.ProgressiveSampling.witnessAt numeratorProcess
                  numerator.name.state sampledLater
              let canonicalDenominator :=
                CCL.ProgressiveSampling.witnessAt denominatorProcess
                  denominator.name.state sampledLater
              have numeratorPossible :
                  numeratorProcess.Possible baseState.1 numeratorReading :=
                (numeratorProcess.witness baseState.1).property
              have denominatorPossible :
                  denominatorProcess.Possible baseState.2 denominatorReading :=
                (denominatorProcess.witness baseState.2).property
              have canonicalNumeratorPossible :
                  numeratorProcess.Possible
                    (CCL.ProgressiveSampling.stateAt numeratorProcess
                      numerator.name.state sampledLater) canonicalNumerator :=
                CCL.ProgressiveSampling.witnessAt_possible numeratorProcess
                  numerator.name.state sampledLater
              have canonicalDenominatorPossible :
                  denominatorProcess.Possible
                    (CCL.ProgressiveSampling.stateAt denominatorProcess
                      denominator.name.state sampledLater) canonicalDenominator :=
                CCL.ProgressiveSampling.witnessAt_possible denominatorProcess
                  denominator.name.state sampledLater
              have numeratorCloseRaw := numerator.coherent.possible_close
                numeratorPossible canonicalNumeratorPossible
              have denominatorCloseRaw := denominator.coherent.possible_close
                denominatorPossible canonicalDenominatorPossible
              have numeratorClose :
                  normSq (numeratorReading - canonicalNumerator) <=
                    8 * semanticTarget := by
                calc
                  normSq (numeratorReading - canonicalNumerator) <=
                      4 * (numerator.coherent.allowance baseState.1 +
                        numerator.coherent.allowance
                          (CCL.ProgressiveSampling.stateAt numeratorProcess
                            numerator.name.state sampledLater)) :=
                    numeratorCloseRaw
                  _ <= 4 * (semanticTarget + semanticTarget) :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      (add_le_add baseComponentSmall.1.le
                        canonicalNumeratorSmall.le) (by decide)
                  _ = 8 * semanticTarget := by ring1
              have denominatorCloseForward :
                  normSq (denominatorReading - canonicalDenominator) <=
                    8 * semanticTarget := by
                calc
                  normSq (denominatorReading - canonicalDenominator) <=
                      4 * (denominator.coherent.allowance baseState.2 +
                        denominator.coherent.allowance
                          (CCL.ProgressiveSampling.stateAt denominatorProcess
                            denominator.name.state sampledLater)) :=
                    denominatorCloseRaw
                  _ <= 4 * (semanticTarget + semanticTarget) :=
                    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                      (add_le_add baseComponentSmall.2.le
                        canonicalDenominatorSmall.le) (by decide)
                  _ = 8 * semanticTarget := by ring1
              have denominatorClose :
                  normSq (canonicalDenominator - denominatorReading) <=
                    8 * semanticTarget := by
                have identity : canonicalDenominator - denominatorReading =
                    -(denominatorReading - canonicalDenominator) := by
                  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
                    simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
                rw [identity, normSq_neg]
                exact denominatorCloseForward
              let numeratorBound := 2 * (1 + numeratorProcess.centerBound)
              let denominatorBound := 2 * (1 + denominatorProcess.centerBound)
              have canonicalNumeratorBound :
                  normSq canonicalNumerator <= numeratorBound :=
                CCL.ProgressiveSampling.witnessAt_bounded numeratorProcess
                  numerator.name.state sampledLater
              have canonicalDenominatorBound :
                  normSq canonicalDenominator <= denominatorBound :=
                CCL.ProgressiveSampling.witnessAt_bounded denominatorProcess
                  denominator.name.state sampledLater
              have denominatorReadingLower : apart.certificate.lowerSq <=
                  normSq denominatorReading :=
                apart.certificate.lower baseState.2
                  (denominatorProcess.possible_inside denominatorPossible)
              have canonicalDenominatorLower : apart.certificate.lowerSq <=
                  normSq canonicalDenominator :=
                apart.certificate.lower _
                  (denominatorProcess.possible_inside
                    canonicalDenominatorPossible)
              have quotientClose :=
                CCL.ArithmeticFiniteQuotientVariation.normSq_div_sub_div_le
                  apart.certificate.positive
                  (leftNumerator := numeratorReading)
                  (rightNumerator := canonicalNumerator)
                  (leftDenominator := denominatorReading)
                  (rightDenominator := canonicalDenominator)
                  (numeratorSlope := (8 : Coordinate))
                  (numeratorBound := numeratorBound)
                  (denominatorBound := denominatorBound)
                  (pointMovement := semanticTarget)
                  (rootMovement := 8 * semanticTarget)
                  numeratorClose canonicalNumeratorBound
                  canonicalDenominatorBound denominatorClose
                  denominatorReadingLower canonicalDenominatorLower
              have quotientCloseSimplified :
                  normSq (numeratorReading / denominatorReading -
                      canonicalNumerator / canonicalDenominator) <=
                    (16 * semanticTarget *
                      (numeratorBound + denominatorBound)) /
                        (apart.certificate.lowerSq *
                          apart.certificate.lowerSq) := by
                exact quotientClose.trans_eq (by
                  unfold CCL.ArithmeticFiniteQuotientVariation.quotientBound
                  rw [RFAP.ExplicitField.div_eq_mul_inv,
                    RFAP.ExplicitField.div_eq_mul_inv]
                  ring1)
              have actualTail :
                  normSq
                      (CCL.ProgressiveSampling.witnessAt process start
                          actualLater -
                        CCL.ProgressiveSampling.witnessAt process start
                          actualIndex) <=
                    4 * CCL.ProgressiveSampling.refinementTarget actualIndex := by
                rw [← quarterRadius_four_eq_four_refinementTarget]
                exact CCL.ProgressiveSampling.witnessAt_later_close
                  process start actualOrder
              have baseWitness :
                  CCL.ProgressiveSampling.witnessAt process start actualIndex =
                    numeratorReading / denominatorReading := rfl
              change normSq
                  (CCL.ProgressiveSampling.witnessAt process start actualLater -
                    quotient.sample sampledLater) < target
              rw [sampledQuotientApproximation_sample]
              calc
                normSq
                    (CCL.ProgressiveSampling.witnessAt process start actualLater -
                      canonicalNumerator / canonicalDenominator) <=
                  2 *
                    (normSq
                        (CCL.ProgressiveSampling.witnessAt process start
                            actualLater -
                          CCL.ProgressiveSampling.witnessAt process start
                            actualIndex) +
                      normSq
                        (CCL.ProgressiveSampling.witnessAt process start
                            actualIndex -
                          canonicalNumerator / canonicalDenominator)) :=
                  normSq_sub_le_via _ _ _
                _ <= 2 *
                    (4 * CCL.ProgressiveSampling.refinementTarget actualIndex +
                      (16 * semanticTarget *
                        (numeratorBound + denominatorBound)) /
                          (apart.certificate.lowerSq *
                            apart.certificate.lowerSq)) := by
                  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                  · apply add_le_add actualTail
                    rw [baseWitness]
                    exact quotientCloseSimplified
                  · decide
                _ <= 2 *
                    (4 * semanticTarget +
                      (16 * semanticTarget *
                        (numeratorBound + denominatorBound)) /
                          (apart.certificate.lowerSq *
                            apart.certificate.lowerSq)) :=
                  RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                    (add_le_add
                      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                        actualRequestLtSemantic.le (by decide)) le_rfl)
                    (by decide)
                _ = semanticTarget *
                    coherentQuotientBridgeCoefficient numerator denominator
                      apart := by
                  dsimp only [numeratorBound, denominatorBound]
                  unfold coherentQuotientBridgeCoefficient
                  rw [RFAP.ExplicitField.div_eq_mul_inv,
                    RFAP.ExplicitField.div_eq_mul_inv]
                  ring1
                _ < target := coherentQuotientBridgeTarget_budget_lt
                  numerator denominator apart positive } }
  exact CCL.OperationalEquivalence.Equivalent.trans bridge
    (CCL.OperationalEquivalence.Equivalent.symm
      (CCL.OperationalEquivalence.Equivalent.toNamed_sampling quotient))

/-- Stateful apartness-certified division respects operational equality in
both coherent operands. -/
def coherentDiv_respects
    (firstNumerator secondNumerator firstDenominator secondDenominator :
      CoherentNamed)
    (firstApart : Apart firstDenominator.name)
    (secondApart : Apart secondDenominator.name)
    (numeratorEquivalent : NamedEquivalent firstNumerator.name
      secondNumerator.name)
    (denominatorEquivalent : NamedEquivalent firstDenominator.name
      secondDenominator.name) :
    NamedEquivalent
      (CCL.ProgressiveTransducer.Named.div firstNumerator.name
        firstDenominator.name firstApart)
      (CCL.ProgressiveTransducer.Named.div secondNumerator.name
        secondDenominator.name secondApart) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (coherentDiv_toSampled firstNumerator firstDenominator firstApart)
    (CCL.OperationalEquivalence.NamedEquivalent.trans
      (CCL.OperationalEquivalence.Equivalent.toNamed
        (sampledQuotientApproximation_respects firstNumerator secondNumerator
          firstDenominator secondDenominator firstApart secondApart
            numeratorEquivalent denominatorEquivalent))
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (coherentDiv_toSampled secondNumerator secondDenominator secondApart)))


end CCL.ProgressiveDivisionCongruence

