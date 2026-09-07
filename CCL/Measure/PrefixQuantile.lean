import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixThreshold
import FiniteMeasure.Quantile

/-!
# Quantile enclosures from finite CCL prefixes

Two finite CCL threshold classifications certify a rational interval for an
exact lower quantile of every displayed realization family.  The lower cut
is justified by enough mass at or above it; the upper cut is justified by
enough mass at or below it, expressed as a lower-threshold test of the
negated probe.  No infimum or completed number is used.
-/

namespace CCL.FiniteMeasure

/-- Negation of a rational probe, used to express an upper-ray test as a
lower-threshold test. -/
def negProbe (probe : Proj → Coordinate) : Proj → Coordinate :=
  fun point => -probe point

theorem rationalSeparation_negProbe (probe : Proj → Coordinate)
    (left right : Proj) :
    _root_.FiniteMeasure.rationalSeparation
        (negProbe probe left) (negProbe probe right) =
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) := by
  unfold negProbe _root_.FiniteMeasure.rationalSeparation
  rw [max_comm]
  congr 1 <;> ring1

/-- A sensitivity certificate is preserved exactly by negating the probe. -/
theorem negProbe_sensitive
    (probe : Proj → Coordinate) (factor : Coordinate)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right) :
    ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (negProbe probe left) (negProbe probe right) ≤
        factor * CCL.Chordal.chordalSq left right := by
  intro left right
  rw [rationalSeparation_negProbe]
  exact sensitive left right

/-- A displayed ordered pair of rational cuts as a certified enclosure. -/
def quantileCutBound (lower upper : Coordinate) (order : lower ≤ upper) :
    _root_.FiniteMeasure.Bound :=
  ⟨lower, upper, order⟩

theorem complement_strictlyBelowProbe
    {α : Type} (value : α → Coordinate) (threshold : Coordinate) (item : α) :
    _root_.FiniteMeasure.complementEvent
        (fun candidate => decide (value candidate < threshold)) item =
      _root_.FiniteMeasure.atLeastEvent threshold value item := by
  by_cases below : value item < threshold
  · have notAtLeast : ¬threshold ≤ value item := below.2
    simp only [_root_.FiniteMeasure.complementEvent,
      _root_.FiniteMeasure.atLeastEvent, below, notAtLeast, decide_true,
      decide_false, Bool.not_true]
  · have atLeast : threshold ≤ value item :=
      RFAP.ConstructiveFraction.le_of_not_gt_direct below
    simp only [_root_.FiniteMeasure.complementEvent,
      _root_.FiniteMeasure.atLeastEvent, below, atLeast, decide_false,
      decide_true, Bool.not_false]

theorem atLeast_negProbe_negThreshold
    {α : Type} (probe : Proj → Coordinate) (points : α → Proj)
    (threshold : Coordinate) (item : α) :
    _root_.FiniteMeasure.atLeastEvent (-threshold)
        (fun candidate => negProbe probe (points candidate)) item =
      decide (probe (points item) ≤ threshold) := by
  by_cases order : probe (points item) ≤ threshold
  · have negated : -threshold ≤ -probe (points item) :=
      RFAP.ConstructiveFraction.neg_le_neg_direct order
    simp only [_root_.FiniteMeasure.atLeastEvent, negProbe, order, negated,
      decide_true]
  · have notNegated : ¬(-threshold ≤ -probe (points item)) := by
      intro negated
      apply order
      have reversed := RFAP.ConstructiveFraction.neg_le_neg_direct negated
      simpa only [neg_neg] using reversed
    simp only [_root_.FiniteMeasure.atLeastEvent, negProbe, order, notNegated,
      decide_false]

/-- Direct rational complement arithmetic used by the lower quantile cut. -/
theorem left_lt_of_add_eq_one_of_one_sub_lt_right
    (left right level : Coordinate) (sum : left + right = 1)
    (rightLarge : 1 - level < right) : left < level := by
  calc
    left = 1 - right := by
      rw [← sum]
      ring1
    _ < 1 - (1 - level) :=
      RFAP.ConstructiveFraction.sub_lt_sub_left_direct rightLarge 1
    _ = level := by ring1

/-- Complement arithmetic turns enough mass at or above a cut into too
little mass strictly below it. -/
theorem probability_strictlyBelow_lt_of_one_sub_lt_probability_atLeast
    {α : Type} (distribution : _root_.FiniteMeasure.Distribution α)
    (value : α → Coordinate) (level lower : Coordinate)
    (tailLarge : 1 - level < distribution.probability
      (_root_.FiniteMeasure.atLeastEvent lower value)) :
    distribution.probability (fun item => decide (value item < lower)) <
      level := by
  have tailComplement := distribution.probability_add_complement
    (fun item => decide (value item < lower))
  have complementProbability := distribution.probability_congr
    (_root_.FiniteMeasure.complementEvent
      (fun item => decide (value item < lower)))
    (_root_.FiniteMeasure.atLeastEvent lower value)
    (complement_strictlyBelowProbe value lower)
  rw [complementProbability] at tailComplement
  exact left_lt_of_add_eq_one_of_one_sub_lt_right
    (distribution.probability fun item => decide (value item < lower))
    (distribution.probability (_root_.FiniteMeasure.atLeastEvent lower value))
    level tailComplement tailLarge

/-- If less than the quantile level lies strictly below a cut, the cut is
below the executable finite lower quantile. -/
theorem lower_le_lowerQuantile_of_probability_strictlyBelow_lt
    (distribution : _root_.FiniteMeasure.Distribution Coordinate)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) (lower : Coordinate)
    (belowLowerLt : distribution.probability
      (_root_.FiniteMeasure.strictlyBelowEvent lower) < level) :
    lower ≤ distribution.lowerQuantile level levelPositive levelAtMostOne := by
  apply RFAP.ConstructiveFraction.le_of_not_gt_direct
  intro quantileLtLower
  have cumulativeLeBelow :
      distribution.cumulative
          (distribution.lowerQuantile level levelPositive levelAtMostOne) ≤
        distribution.probability
          (_root_.FiniteMeasure.strictlyBelowEvent lower) := by
    apply _root_.FiniteMeasure.eventWeight_mono
    intro atom member selected
    have valueLeQuantile : atom.item ≤
        distribution.lowerQuantile level levelPositive levelAtMostOne :=
      of_decide_eq_true selected
    exact decide_eq_true_eq.mpr
      (valueLeQuantile.trans_lt quantileLtLower)
  have levelLeBelow :=
    (distribution.level_le_cumulative_lowerQuantile level levelPositive
      levelAtMostOne).trans cumulativeLeBelow
  exact belowLowerLt.2 levelLeBelow

/-- A certified amount of mass at or above a rational cut puts that cut
below every admitted realization family's lower quantile. -/
theorem prefixFamilyProbeLowerCut_le_lowerQuantile
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) (lower : Coordinate)
    (lowerMass : 1 - level <
      (prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive lower).lower)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    lower ≤ ((distribution.map fun certificate => probe (points certificate))
      |>.lowerQuantile level levelPositive levelAtMostOne) := by
  let observed := distribution.map fun certificate => probe (points certificate)
  let quantile := observed.lowerQuantile level levelPositive levelAtMostOne
  change lower ≤ quantile
  have lowerTailInside := prefixFamilyThresholdBound_contains distribution
    probe factor factorNonnegative sensitive lower points pointsRealize
  have oneMinusLevelLtTail :
      1 - level < distribution.probability
        (_root_.FiniteMeasure.atLeastEvent lower fun certificate =>
          probe (points certificate)) :=
    lowerMass.trans_le lowerTailInside.1
  have belowLowerLt :
      distribution.probability
          (fun certificate => decide (probe (points certificate) < lower)) <
        level :=
    probability_strictlyBelow_lt_of_one_sub_lt_probability_atLeast
      distribution (fun certificate => probe (points certificate)) level
      lower oneMinusLevelLtTail
  have observedBelowLowerLt :
      observed.probability (_root_.FiniteMeasure.strictlyBelowEvent lower) <
        level := by
    dsimp only [observed]
    rw [distribution.map_probability]
    exact belowLowerLt
  exact lower_le_lowerQuantile_of_probability_strictlyBelow_lt observed
    level levelPositive levelAtMostOne lower observedBelowLowerLt

/-- A certified amount of mass at or below a rational cut puts every
admitted realization family's lower quantile below that cut. -/
theorem prefixFamilyProbeLowerQuantile_le_upperCut
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1) (upper : Coordinate)
    (upperMass : level ≤
      (prefixFamilyThresholdBound distribution (negProbe probe) factor
        factorNonnegative (negProbe_sensitive probe factor sensitive)
        (-upper)).lower)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    ((distribution.map fun certificate => probe (points certificate))
        |>.lowerQuantile level levelPositive levelAtMostOne) ≤ upper := by
  let observed := distribution.map fun certificate => probe (points certificate)
  change observed.lowerQuantile level levelPositive levelAtMostOne ≤ upper
  have upperTailInside := prefixFamilyThresholdBound_contains distribution
    (negProbe probe) factor factorNonnegative
    (negProbe_sensitive probe factor sensitive) (-upper) points pointsRealize
  have levelLeUpperTail : level ≤ distribution.probability
      (_root_.FiniteMeasure.atLeastEvent (-upper) fun certificate =>
        negProbe probe (points certificate)) :=
    upperMass.trans upperTailInside.1
  have cumulativeEqual : observed.cumulative upper =
      distribution.probability
        (_root_.FiniteMeasure.atLeastEvent (-upper) fun certificate =>
          negProbe probe (points certificate)) := by
    dsimp only [observed]
    unfold _root_.FiniteMeasure.Distribution.cumulative
    rw [distribution.map_probability]
    exact distribution.probability_congr _ _ (fun item =>
      (atLeast_negProbe_negThreshold probe points upper item).symm)
  have levelLeCumulative : level ≤ observed.cumulative upper := by
    rw [cumulativeEqual]
    exact levelLeUpperTail
  exact ((observed.quantileCertificate level levelPositive levelAtMostOne)
    |>.threshold_le_iff_level_le_cumulative upper).2 levelLeCumulative

/-- Two finite prefix threshold certificates enclose the exact executable
lower quantile of every displayed realization family. -/
theorem prefixFamilyProbeLowerQuantile_mem_quantileCutBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (level : Coordinate) (levelPositive : 0 < level)
    (levelAtMostOne : level ≤ 1)
    (lower upper : Coordinate) (order : lower ≤ upper)
    (lowerMass : 1 - level <
      (prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive lower).lower)
    (upperMass : level ≤
      (prefixFamilyThresholdBound distribution (negProbe probe) factor
        factorNonnegative (negProbe_sensitive probe factor sensitive)
        (-upper)).lower)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (quantileCutBound lower upper order).Contains
      ((distribution.map fun certificate => probe (points certificate))
        |>.lowerQuantile level levelPositive levelAtMostOne) := by
  constructor
  · exact prefixFamilyProbeLowerCut_le_lowerQuantile distribution probe
      factor factorNonnegative sensitive level levelPositive levelAtMostOne
      lower lowerMass points pointsRealize
  · exact prefixFamilyProbeLowerQuantile_le_upperCut distribution probe
      factor factorNonnegative sensitive level levelPositive levelAtMostOne
      upper upperMass points pointsRealize

/-- The median specialization: two half-mass prefix certificates enclose
the executable lower median of every displayed realization family. -/
theorem prefixFamilyProbeMedian_mem_quantileCutBound
    (distribution :
      _root_.FiniteMeasure.Distribution CompletedPrefixCertificate)
    (probe : Proj → Coordinate)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (lower upper : Coordinate) (order : lower ≤ upper)
    (lowerMass : (1 / 2 : Coordinate) <
      (prefixFamilyThresholdBound distribution probe factor
        factorNonnegative sensitive lower).lower)
    (upperMass : (1 / 2 : Coordinate) ≤
      (prefixFamilyThresholdBound distribution (negProbe probe) factor
        factorNonnegative (negProbe_sensitive probe factor sensitive)
        (-upper)).lower)
    (points : CompletedPrefixCertificate → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes atom.item.blocks (points atom.item)) :
    (quantileCutBound lower upper order).Contains
      ((distribution.map fun certificate => probe (points certificate))
        |>.median) := by
  unfold _root_.FiniteMeasure.Distribution.median
  apply prefixFamilyProbeLowerQuantile_mem_quantileCutBound distribution probe
    factor factorNonnegative sensitive (1 / 2) (by decide) (by decide)
    lower upper order
  · simpa only [show (1 : Coordinate) - 1 / 2 = 1 / 2 by decide] using
      lowerMass
  · exact upperMass
  · exact pointsRealize

end CCL.FiniteMeasure
