import mathlib.Tactic.QuotientFreeRing
import CCL.Measure.PrefixCenteredVariance

/-!
# Progressive witness-centred variance from finite CCL prefixes

This module turns the static witness-centred variance construction into a
finite-request process.  Its states remain ordinary finite prefix families.
One request computes a finite block count large enough for both the centred
second-deviation enclosure and the squared mean-radius correction.
-/

namespace CCL.FiniteMeasure

namespace PrefixFamilyProcess

/-- Fixed rational probe expectation of the process's displayed witnesses. -/
def witnessProbeExpectation {ι : Type} (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) : Coordinate :=
  distribution.expectation fun item => probe (process.witness item)

/-- Exact expected sensitivity-scaled prefix radius at one finite process
state. -/
def probeRadius {ι : Type} (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (factor : Coordinate) (state : process.State) : Coordinate :=
  distribution.expectation fun item =>
    factor * cylinderSpread (process.blocks state item)

theorem probeRadius_nonnegative {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    (state : process.State) :
    0 ≤ process.probeRadius distribution factor state := by
  apply distribution.expectation_nonneg
  intro atom member
  exact RFAP.ConstructiveFraction.mul_nonneg_direct factorNonnegative
    (cylinderSpread_nonneg (process.blocks state atom.item))

/-- Pointwise prefix extension cannot increase the expected probe radius. -/
theorem probeRadius_le_of_extends {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    {newer older : process.State}
    (extension : ∀ item, ∃ suffix,
      process.blocks newer item = process.blocks older item ++ suffix) :
    process.probeRadius distribution factor newer ≤
      process.probeRadius distribution factor older := by
  apply distribution.expectation_mono
  intro atom member
  rcases extension atom.item with ⟨suffix, equal⟩
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
  · rw [equal]
    exact cylinderSpread_le_of_append (process.blocks older atom.item) suffix
  · exact factorNonnegative

/-- Squared mean-error enclosure at one finite process state. -/
def probeMeanSquareErrorBound {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (factor : Coordinate) (state : process.State) :
    _root_.FiniteMeasure.Bound where
  lower := 0
  upper := process.probeRadius distribution factor state ^ 2
  valid := RFAP.ConstructiveFraction.sq_nonneg_direct _

/-- Prefix extension narrows the process's squared mean-error enclosure. -/
theorem probeMeanSquareErrorBound_refines_of_extends {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (factor : Coordinate) (factorNonnegative : 0 ≤ factor)
    {newer older : process.State}
    (extension : ∀ item, ∃ suffix,
      process.blocks newer item = process.blocks older item ++ suffix) :
    _root_.FiniteMeasure.Bound.Refines
      (process.probeMeanSquareErrorBound distribution factor newer)
      (process.probeMeanSquareErrorBound distribution factor older) := by
  constructor
  · exact le_rfl
  · exact RFAP.ConstructiveFraction.pow_le_pow_direct
      (process.probeRadius_nonnegative distribution factor factorNonnegative
        newer)
      (process.probeRadius_le_of_extends distribution factor factorNonnegative
        extension)
      2

/-- Every realization family admitted at one finite state has its squared
mean error inside the process radius-square enclosure. -/
theorem probeMeanSquareErrorBound_contains {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorNonnegative : 0 ≤ factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    (state : process.State) (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    (process.probeMeanSquareErrorBound distribution factor state).Contains
      (((distribution.expectation fun item => probe (points item)) -
        process.witnessProbeExpectation distribution probe) ^ 2) := by
  have l1Bound : distribution.l1Distance
      (fun item => probe (points item))
      (fun item => probe (process.witness item)) ≤
      process.probeRadius distribution factor state := by
    change distribution.expectation (fun item =>
        _root_.FiniteMeasure.rationalSeparation
          (probe (points item)) (probe (process.witness item))) ≤
      distribution.expectation fun item =>
        factor * cylinderSpread (process.blocks state item)
    apply distribution.expectation_mono
    intro atom member
    exact realized_probe_separation_le (pointsRealize atom member)
      (process.realizes state atom.item) probe factor factorNonnegative sensitive
  have separationLe :=
    (distribution.expectation_separation_le_l1Distance
      (fun item => probe (points item))
      (fun item => probe (process.witness item))).trans l1Bound
  have powered := RFAP.ConstructiveFraction.pow_le_pow_direct
    (_root_.FiniteMeasure.rationalSeparation_nonneg _ _) separationLe 2
  rw [_root_.FiniteMeasure.rationalSeparation_sq] at powered
  exact ⟨RFAP.ConstructiveFraction.sq_nonneg_direct _, powered⟩

/-- Witness-centred variance enclosure at one finite process state. -/
def probeCenteredVarianceBound {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (meanFactor : Coordinate)
    (deviationFactor : Coordinate) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (state : process.State) : _root_.FiniteMeasure.Bound :=
  ((process.toProbeExpectationProcess distribution
    (poweredDeviationProbe probe
      (process.witnessProbeExpectation distribution probe) 2)
    deviationFactor deviationFactorPositive deviationSensitive).bound state).sub
  (process.probeMeanSquareErrorBound distribution meanFactor state)

/-- The statewise process enclosure contains the exact variance of every
realization family admitted by that finite state. -/
theorem probeCenteredVarianceBound_contains {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (deviationFactor : Coordinate) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (state : process.State) (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    (process.probeCenteredVarianceBound distribution probe meanFactor
      deviationFactor deviationFactorPositive deviationSensitive state).Contains
      (distribution.variance fun item => probe (points item)) := by
  let center := process.witnessProbeExpectation distribution probe
  let value := fun item => probe (points item)
  have deviationInside :=
    process.expectation_mem_probeExpectationProcess_bound distribution
      (poweredDeviationProbe probe center 2) deviationFactor
      deviationFactorPositive deviationSensitive state points pointsRealize
  have varianceAroundInside :
      ((process.toProbeExpectationProcess distribution
        (poweredDeviationProbe probe center 2) deviationFactor
        deviationFactorPositive deviationSensitive).bound state).Contains
        (distribution.varianceAround value center) := by
    rw [distribution.varianceAround_eq_poweredL2Distance_constant,
      ← distribution.poweredLpDistance_two]
    exact deviationInside
  have meanErrorInside := process.probeMeanSquareErrorBound_contains
    distribution probe meanFactor meanFactorPositive.le meanSensitive state
    points pointsRealize
  have differenceInside := _root_.FiniteMeasure.Bound.sub_contains
    varianceAroundInside meanErrorInside
  have varianceIdentity :
      distribution.varianceAround value center -
          (distribution.expectation value - center) ^ 2 =
        distribution.variance value := by
    rw [distribution.varianceAround_eq_variance_add_mean_sub_sq]
    ring1
  rw [varianceIdentity] at differenceInside
  exact differenceInside

/-- Pointwise prefix extension narrows the complete probe-expectation
enclosure, for arbitrary pairs of process states. -/
theorem probeExpectationBound_refines_of_extends {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate) (factor : Coordinate)
    (factorPositive : 0 < factor)
    (sensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        factor * CCL.Chordal.chordalSq left right)
    {newer older : process.State}
    (extension : ∀ item, ∃ suffix,
      process.blocks newer item = process.blocks older item ++ suffix) :
    _root_.FiniteMeasure.Bound.Refines
      ((process.toProbeExpectationProcess distribution probe factor
        factorPositive sensitive).bound newer)
      ((process.toProbeExpectationProcess distribution probe factor
        factorPositive sensitive).bound older) := by
  apply distribution.enclosedExpectation_refines
  intro atom member
  rcases extension atom.item with ⟨suffix, equal⟩
  unfold toProbePointwiseProcess
  change _root_.FiniteMeasure.Bound.Refines
    (completedPrefixProbeBound (process.blocks newer atom.item)
      (process.witness atom.item) (process.realizes newer atom.item)
      probe factor factorPositive.le sensitive)
    (completedPrefixProbeBound (process.blocks older atom.item)
      (process.witness atom.item) (process.realizes older atom.item)
      probe factor factorPositive.le sensitive)
  have spreadLe :
      factor * cylinderSpread (process.blocks newer atom.item) ≤
        factor * cylinderSpread (process.blocks older atom.item) := by
    rw [equal]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      (cylinderSpread_le_of_append (process.blocks older atom.item) suffix)
      factorPositive.le
  constructor
  · exact RFAP.ConstructiveFraction.sub_le_sub_left_direct spreadLe (probe (process.witness atom.item))
  · exact RFAP.ConstructiveFraction.add_le_add_direct le_rfl spreadLe

/-- A computable positive half-power whose square is below half the supplied
positive variance tolerance. -/
def centeredVarianceMeanTarget (target : Coordinate) : Coordinate :=
  (1 / 2 : Coordinate) ^ requiredBlockCount (target / 2)

theorem centeredVarianceMeanTarget_positive
    {target : Coordinate} (_positive : 0 < target) :
    0 < centeredVarianceMeanTarget target :=
  RFAP.ConstructiveFraction.pow_pos_direct (by decide) _

theorem centeredVarianceMeanTarget_sq_lt_half
    {target : Coordinate} (positive : 0 < target) :
    centeredVarianceMeanTarget target ^ 2 < target / 2 := by
  have halfPositive : (0 : Coordinate) < target / 2 :=
    RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
  have targetSmall : centeredVarianceMeanTarget target < target / 2 :=
    requiredBlockCount_spread_lt halfPositive
  have targetNonnegative : 0 ≤ centeredVarianceMeanTarget target :=
    (centeredVarianceMeanTarget_positive positive).le
  have targetLeOne : centeredVarianceMeanTarget target ≤ 1 :=
    half_pow_le_one _
  calc
    centeredVarianceMeanTarget target ^ 2 =
        centeredVarianceMeanTarget target *
          centeredVarianceMeanTarget target := by ring1
    _ ≤ centeredVarianceMeanTarget target * 1 :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        targetLeOne targetNonnegative
    _ = centeredVarianceMeanTarget target := by ring1
    _ < target / 2 := targetSmall

private theorem quarter_add_quarter_eq_half (target : Coordinate) :
    target / 4 + target / 4 = target / 2 := by
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

private theorem quarter_lt_half {target : Coordinate} (positive : 0 < target) :
    target / 4 < target / 2 := by
  have quarterPositive : (0 : Coordinate) < target / 4 :=
    RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
  calc
    target / 4 = target / 4 + 0 := by ring1
    _ < target / 4 + target / 4 :=
      RFAP.ConstructiveFraction.add_lt_add_left_direct quarterPositive _
    _ = target / 2 := quarter_add_quarter_eq_half target

/-- Finite-request process for the exact variance of every realization
family admitted by its current CCL prefixes. -/
def toProbeCenteredVarianceProcess {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (deviationFactor : Coordinate) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right) :
    _root_.FiniteMeasure.BoundProcess where
  State := process.State
  bound state := process.probeCenteredVarianceBound distribution probe
    meanFactor deviationFactor deviationFactorPositive deviationSensitive state
  initial := process.initial
  request state epsilon positive :=
    process.request state (max
      (requiredProbeBlockCount (epsilon / 4) deviationFactor)
      (requiredProbeBlockCount (centeredVarianceMeanTarget epsilon) meanFactor))
  request_refines state epsilon positive := by
    apply _root_.FiniteMeasure.Bound.Refines.sub
    · apply process.probeExpectationBound_refines_of_extends distribution
        (poweredDeviationProbe probe
          (process.witnessProbeExpectation distribution probe) 2)
        deviationFactor deviationFactorPositive deviationSensitive
      intro item
      exact process.request_extends state _ item
    · apply process.probeMeanSquareErrorBound_refines_of_extends distribution
        meanFactor meanFactorPositive.le
      intro item
      exact process.request_extends state _ item
  accurate state epsilon positive := by
    let deviationCount :=
      requiredProbeBlockCount (epsilon / 4) deviationFactor
    let meanTarget := centeredVarianceMeanTarget epsilon
    let meanCount := requiredProbeBlockCount meanTarget meanFactor
    let count := max deviationCount meanCount
    let requested := process.request state count
    have quarterPositive : (0 : Coordinate) < epsilon / 4 :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    have halfPositive : (0 : Coordinate) < epsilon / 2 :=
      RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
    have deviationWidthSmall :
        ((process.toProbeExpectationProcess distribution
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2)
          deviationFactor deviationFactorPositive deviationSensitive).bound
          requested).width < epsilon / 2 := by
      apply distribution.enclosedExpectation_width_lt_of_uniform _
        (epsilon / 4) (epsilon / 2)
      · intro atom member
        exact (completedPrefixProbeBound_width_lt_requested
          (process.witness atom.item) (process.realizes requested atom.item)
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2)
          deviationFactor deviationFactorPositive deviationSensitive
          (epsilon / 4) quarterPositive
          ((show deviationCount ≤ count from le_max_left _ _).trans
            (process.request_length state count atom.item))).le
      · exact quarter_lt_half positive
    have meanRadiusLe :
        process.probeRadius distribution meanFactor requested ≤ meanTarget := by
      calc
        process.probeRadius distribution meanFactor requested =
            distribution.expectation (fun item =>
              meanFactor * cylinderSpread (process.blocks requested item)) :=
          rfl
        _ ≤ distribution.expectation (fun _ => meanTarget) := by
          apply distribution.expectation_mono
          intro atom member
          have widthSmall := completedPrefixProbeBound_width_lt_requested
            (process.witness atom.item) (process.realizes requested atom.item)
            probe meanFactor meanFactorPositive meanSensitive meanTarget
            (centeredVarianceMeanTarget_positive positive)
            ((show meanCount ≤ count from le_max_right _ _).trans
              (process.request_length state count atom.item))
          have radiusNonnegative : 0 ≤ meanFactor *
              cylinderSpread (process.blocks requested atom.item) :=
            RFAP.ConstructiveFraction.mul_nonneg_direct meanFactorPositive.le
              (cylinderSpread_nonneg _)
          calc
            meanFactor * cylinderSpread (process.blocks requested atom.item) ≤
                2 * (meanFactor *
                  cylinderSpread (process.blocks requested atom.item)) := by
              calc
                _ = 0 + meanFactor *
                    cylinderSpread (process.blocks requested atom.item) := by
                  ring1
                _ ≤ meanFactor * cylinderSpread
                      (process.blocks requested atom.item) +
                    meanFactor * cylinderSpread
                      (process.blocks requested atom.item) :=
                  RFAP.ConstructiveFraction.add_le_add_direct
                    radiusNonnegative le_rfl
                _ = _ := by ring1
            _ = (completedPrefixProbeBound
                (process.blocks requested atom.item) (process.witness atom.item)
                (process.realizes requested atom.item) probe meanFactor
                meanFactorPositive.le meanSensitive).width := by
              rw [completedPrefixProbeBound_width]
            _ ≤ meanTarget := widthSmall.le
        _ = meanTarget := distribution.expectation_constant meanTarget
    have meanSquareSmall :
        process.probeRadius distribution meanFactor requested ^ 2 <
          epsilon / 2 := by
      exact (RFAP.ConstructiveFraction.pow_le_pow_direct
        (process.probeRadius_nonnegative distribution meanFactor
          meanFactorPositive.le requested)
        meanRadiusLe 2).trans_lt
          (centeredVarianceMeanTarget_sq_lt_half positive)
    change (process.probeCenteredVarianceBound distribution probe meanFactor
      deviationFactor deviationFactorPositive deviationSensitive requested).width <
        epsilon
    unfold probeCenteredVarianceBound
    rw [_root_.FiniteMeasure.Bound.sub_width]
    change _ + (process.probeRadius distribution meanFactor requested ^ 2 - 0) < _
    calc
      _ = _ + process.probeRadius distribution meanFactor requested ^ 2 := by
        ring1
      _ < epsilon / 2 + epsilon / 2 :=
        RFAP.ConstructiveFraction.add_lt_add_direct deviationWidthSmall
          meanSquareSmall
      _ = (epsilon / 2) * 2 := by ring1
      _ = epsilon :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne epsilon 2 (by decide)
  refinesInitial state := by
    apply _root_.FiniteMeasure.Bound.Refines.sub
    · apply process.probeExpectationBound_refines_of_extends distribution
        (poweredDeviationProbe probe
          (process.witnessProbeExpectation distribution probe) 2)
        deviationFactor deviationFactorPositive deviationSensitive
      exact process.extendsInitial state
    · apply process.probeMeanSquareErrorBound_refines_of_extends distribution
        meanFactor meanFactorPositive.le
      exact process.extendsInitial state

/-- Every explicit realization family remains inside the current progressive
variance enclosure. -/
theorem variance_mem_toProbeCenteredVarianceProcess_bound {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (deviationFactor : Coordinate) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (state : process.State) (points : ι → Proj)
    (pointsRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes (process.blocks state atom.item)
        (points atom.item)) :
    ((process.toProbeCenteredVarianceProcess distribution probe meanFactor
      meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
      deviationSensitive).bound state).Contains
        (distribution.variance fun item => probe (points item)) :=
  process.probeCenteredVarianceBound_contains distribution probe meanFactor
    meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
    deviationSensitive state points pointsRealize

/-- One finite request makes the progressive variance enclosure narrower than
the supplied positive rational tolerance. -/
theorem request_probeCenteredVariance_width_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (deviationFactor : Coordinate) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon) :
    ((process.toProbeCenteredVarianceProcess distribution probe meanFactor
      meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
      deviationSensitive).bound
      ((process.toProbeCenteredVarianceProcess distribution probe meanFactor
        meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
        deviationSensitive).request state epsilon positive)).width < epsilon :=
  (process.toProbeCenteredVarianceProcess distribution probe meanFactor
    meanFactorPositive meanSensitive deviationFactor deviationFactorPositive
    deviationSensitive).accurate state epsilon positive

/-- After one computed finite request, every two realization families still
admitted by the returned CCL prefixes have variances within the requested
tolerance of one another, in both directed differences. -/
theorem request_realizedVariances_pairwise_difference_lt {ι : Type}
    (process : PrefixFamilyProcess ι)
    (distribution : _root_.FiniteMeasure.Distribution ι)
    (probe : Proj → Coordinate)
    (meanFactor : Coordinate) (meanFactorPositive : 0 < meanFactor)
    (meanSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation (probe left) (probe right) ≤
        meanFactor * CCL.Chordal.chordalSq left right)
    (deviationFactor : Coordinate) (deviationFactorPositive : 0 < deviationFactor)
    (deviationSensitive : ∀ left right,
      _root_.FiniteMeasure.rationalSeparation
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 left)
          (poweredDeviationProbe probe
            (process.witnessProbeExpectation distribution probe) 2 right) ≤
        deviationFactor * CCL.Chordal.chordalSq left right)
    (state : process.State) (epsilon : Coordinate) (positive : 0 < epsilon)
    (leftPoints rightPoints : ι → Proj)
    (leftRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          ((process.toProbeCenteredVarianceProcess distribution probe
            meanFactor meanFactorPositive meanSensitive deviationFactor
            deviationFactorPositive deviationSensitive).request state epsilon
              positive) atom.item)
        (leftPoints atom.item))
    (rightRealize : ∀ atom, atom ∈ distribution.atoms →
      CCL.Cylinder.Realizes
        (process.blocks
          ((process.toProbeCenteredVarianceProcess distribution probe
            meanFactor meanFactorPositive meanSensitive deviationFactor
            deviationFactorPositive deviationSensitive).request state epsilon
              positive) atom.item)
        (rightPoints atom.item)) :
    distribution.variance (fun item => probe (leftPoints item)) -
          distribution.variance (fun item => probe (rightPoints item)) < epsilon ∧
      distribution.variance (fun item => probe (rightPoints item)) -
          distribution.variance (fun item => probe (leftPoints item)) < epsilon := by
  let varianceProcess := process.toProbeCenteredVarianceProcess distribution
    probe meanFactor meanFactorPositive meanSensitive deviationFactor
      deviationFactorPositive deviationSensitive
  apply varianceProcess.request_pairwise_difference_lt state epsilon positive
  · exact process.variance_mem_toProbeCenteredVarianceProcess_bound
      distribution probe meanFactor meanFactorPositive meanSensitive
      deviationFactor deviationFactorPositive deviationSensitive
      (varianceProcess.request state epsilon positive) leftPoints leftRealize
  · exact process.variance_mem_toProbeCenteredVarianceProcess_bound
      distribution probe meanFactor meanFactorPositive meanSensitive
      deviationFactor deviationFactorPositive deviationSensitive
      (varianceProcess.request state epsilon positive) rightPoints rightRealize

end PrefixFamilyProcess

end CCL.FiniteMeasure
