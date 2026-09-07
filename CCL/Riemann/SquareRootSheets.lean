import CCL.Riemann.CoherentRoot
import CCL.Progressive.PowerMonodromy

/-!
# Two constructive coherent square-root sheets

For a displayed nonzero Gaussian rational `w`, the finite power-polynomial
isolator computes exactly two winding-one tracks for `Z^2 - w`.  This file
turns each track into an apart coherent CCL name and proves, by finite
operational comparison of its rational samples, that its square is `w`.
No completed algebraic root or choice of a field element is introduced.
-/

namespace CCL.Riemann.SquareRootSheets

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Approximation := CCL.ProgressiveApproximation.Approximation
abbrev CoherentNamed := CCL.ProgressiveCoherence.CoherentNamed
abbrev NamedEquivalent := CCL.OperationalEquivalence.NamedEquivalent

open RFAP.ConstructiveGaussian.Gaussian

/-- The explicit positive degree used throughout the square-root family. -/
def degreeTwo : CCL.RootPowers.RootDegree where
  value := 2
  positive := by decide

@[simp] theorem degreeTwo_value : degreeTwo.value = 2 := rfl

theorem degreeTwo_atLeastTwo : 2 <= degreeTwo.value := by decide

/-- The independently isolated winding-one track carrying one of the two
finite square-root owners. -/
def track {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) :=
  CCL.PowerMonodromy.isolatedTrack parameterNonzero degreeTwo
    degreeTwo_atLeastTwo sheet

/-- Drop a finite prefix of an approximation without changing its finite
value.  The `max` presentation keeps the state type executable and avoids a
subtraction-side proof in the refiner. -/
def tail (source : Approximation) (base : Nat) : Approximation where
  sample index := source.sample (max base index)
  radiusSq index := source.radiusSq (max base index)
  radiusSq_nonneg index := source.radiusSq_nonneg (max base index)
  later_close := by
    intro earlier later order
    exact source.later_close (by omega)
  refineIndex current target positive :=
    source.refineIndex (max base current) target positive
  refineIndex_ge := by
    intro current target positive
    exact (Nat.le_max_right base current).trans
      (source.refineIndex_ge (max base current) target positive)
  refineIndex_accurate := by
    intro current target positive
    have baseLe : base ≤ source.refineIndex (max base current) target positive :=
      (Nat.le_max_left base current).trans
        (source.refineIndex_ge (max base current) target positive)
    rw [max_eq_right baseLe]
    exact source.refineIndex_accurate (max base current) target positive
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded index := source.sample_bounded (max base index)

@[simp] theorem tail_sample (source : Approximation) (base index : Nat) :
    (tail source base).sample index = source.sample (max base index) := rfl

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
    _ = scale * (1 / 4 : Coordinate) ^ earlier :=
      RFAP.ConstructiveFraction.mul_one_direct _

/-- Positive rational residual threshold used before exposing a root as a
safe denominator. -/
def residualTarget (parameter : Gaussian) : Coordinate :=
  normSq parameter / 4

theorem residualTarget_positive {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) : 0 < residualTarget parameter :=
  RFAP.ConstructiveFraction.div_pos_direct (normSq_pos parameterNonzero)
    (by decide)

/-- A rational lower approximation to the ordinary magnitude of a Gaussian:
the larger absolute coordinate.  Unlike a square root of `normSq`, this datum
is directly executable on the constructive rational carrier. -/
def coordinateNormLower (parameter : Gaussian) : Coordinate :=
  max |parameter.re| |parameter.im|

private theorem abs_sq (value : Coordinate) : |value| ^ 2 = value ^ 2 := by
  by_cases nonnegative : 0 ≤ value
  · rw [abs_of_nonneg nonnegative]
  · have nonpositive : value ≤ 0 := le_of_not_ge nonnegative
    rw [abs_of_nonpos nonpositive]
    ring1

theorem coordinateNormLower_sq_le_normSq (parameter : Gaussian) :
    coordinateNormLower parameter ^ 2 ≤ normSq parameter := by
  unfold coordinateNormLower
  change max |parameter.re| |parameter.im| ^ 2 ≤
    parameter.re ^ 2 + parameter.im ^ 2
  by_cases order : |parameter.re| ≤ |parameter.im|
  · rw [max_eq_right order, abs_sq]
    exact le_add_of_nonneg_left
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter.re)
  · have reverse : |parameter.im| ≤ |parameter.re| :=
      le_of_not_ge order
    rw [max_eq_left reverse, abs_sq]
    exact le_add_of_nonneg_right
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter.im)

/-- The dominant rational coordinate also controls the Gaussian norm from
above, up to the explicit factor two.  Together with a positive norm-square
certificate this gives a finite dyadic lower approximation to the dominant
coordinate, without extracting a real square root. -/
theorem normSq_le_two_coordinateNormLower_sq (parameter : Gaussian) :
    normSq parameter <= 2 * coordinateNormLower parameter ^ 2 := by
  have absSq : forall value : Coordinate, |value| ^ 2 = value ^ 2 := by
    intro value
    by_cases nonnegative : 0 <= value
    · rw [abs_of_nonneg nonnegative]
    · rw [abs_of_nonpos (le_of_not_ge nonnegative)]
      ring1
  unfold coordinateNormLower normSq
  by_cases order : |parameter.re| <= |parameter.im|
  · rw [max_eq_right order, absSq]
    have reSqLe : parameter.re ^ 2 <= parameter.im ^ 2 := by
      rw [← absSq parameter.re, ← absSq parameter.im]
      exact RFAP.ConstructiveFraction.pow_le_pow_direct
        (RFAP.ConstructiveFraction.abs_nonneg_direct parameter.re) order 2
    calc
      parameter.re ^ 2 + parameter.im ^ 2 <=
          parameter.im ^ 2 + parameter.im ^ 2 := add_le_add reSqLe le_rfl
      _ = 2 * parameter.im ^ 2 := by ring1
  · have reverse : |parameter.im| <= |parameter.re| := le_of_not_ge order
    rw [max_eq_left reverse, absSq]
    have imSqLe : parameter.im ^ 2 <= parameter.re ^ 2 := by
      rw [← absSq parameter.im, ← absSq parameter.re]
      exact RFAP.ConstructiveFraction.pow_le_pow_direct
        (RFAP.ConstructiveFraction.abs_nonneg_direct parameter.im) reverse 2
    calc
      parameter.re ^ 2 + parameter.im ^ 2 <=
          parameter.re ^ 2 + parameter.re ^ 2 := add_le_add le_rfl imSqLe
      _ = 2 * parameter.re ^ 2 := by ring1

/-- A positive rational norm-square lower bound yields an executable dyadic
lower approximation to the dominant coordinate. -/
theorem dyadicSquareRadius_half_le_coordinateNormLower
    {parameter : Gaussian} {lower : Coordinate} (positive : 0 < lower)
    (lowerLe : lower <= normSq parameter) :
    CCL.FiniteGeometric.dyadicSquareRadius (lower / 2) <=
      coordinateNormLower parameter := by
  have halfPositive : 0 < lower / 2 :=
    RFAP.ConstructiveFraction.div_pos_direct positive (by decide)
  have normHalfLe : normSq parameter / 2 <=
      coordinateNormLower parameter ^ 2 := by
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (show (0 : Coordinate) < 2 by decide)).2
    simpa only [RFAP.ConstructiveFraction.mul_comm] using
      normSq_le_two_coordinateNormLower_sq parameter
  have lowerHalfLe : lower / 2 <= normSq parameter / 2 := by
    rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
      RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct lowerLe
      (by decide)
  have squareLe :
      CCL.FiniteGeometric.dyadicSquareRadius (lower / 2) ^ 2 <=
        coordinateNormLower parameter ^ 2 :=
    (CCL.FiniteGeometric.dyadicSquareRadius_sq_lt halfPositive).le.trans
      (lowerHalfLe.trans normHalfLe)
  exact RFAP.ConstructiveFraction.le_of_sq_le_sq_direct
    (by
      unfold coordinateNormLower
      exact
        (RFAP.ConstructiveFraction.abs_nonneg_direct parameter.re).trans
          (le_max_left _ _))
    squareLe

/-- The denominator lower bound exposed by a finite square-root sample.  The
first term preserves the former residual-only certificate.  The second uses
the dominant rational coordinate of the radicand and is of the correct
linear magnitude near a small nonzero radicand. -/
def sampleNormLower (parameter : Gaussian) : Coordinate :=
  max (min 1 (residualTarget parameter))
    (coordinateNormLower parameter / 2)

private theorem twice_quarter_eq_half (value : Coordinate) :
    2 * (value / 4) = value / 2 := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (4 : Coordinate) ≠ 0 by decide)
  calc
    (2 * (value / 4)) * 4 = 2 * ((value / 4) * 4) := by ring1
    _ = 2 * value := by
      rw [show (value / 4) * 4 = value from
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne value 4 (by decide)]
    _ = value * 2 := by ring1
    _ = ((value / 2) * 2) * 2 := by
      rw [show (value / 2) * 2 = value from
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne value 2 (by decide)]
    _ = (value / 2) * 4 := by ring1

private theorem half_add_half (value : Coordinate) :
    value / 2 + value / 2 = value := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    (show (2 : Coordinate) ≠ 0 by decide)
  calc
    (value / 2 + value / 2) * 2 =
        (value / 2) * 2 + (value / 2) * 2 := by rw [add_mul]
    _ = value + value := by
      rw [show (value / 2) * 2 = value from
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne value 2 (by decide)]
    _ = value * 2 := by ring1

/-- First explicit root-track index whose polynomial residual is below the
nonzero-radicand threshold. -/
def baseIndex {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : Nat :=
  CCL.FiniteGeometric.firstQuarterBelow
    (CCL.Riemann.CoherentRoot.residualScale
      (CCL.PowerMonodromy.polynomial parameter degreeTwo)
      (RFAP.GlobalWinding.largeSquareBox
        (CCL.PowerMonodromy.polynomial parameter degreeTwo))
      (track parameterNonzero sheet))
    0 (residualTarget parameter)

/-- The root approximation after its finite nonzero prefix has been
discarded. -/
def approximation {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : Approximation :=
  tail (CCL.Riemann.CoherentRoot.approximation
    (track parameterNonzero sheet)) (baseIndex parameterNonzero sheet)

theorem sample_residual_le {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) (index : Nat) :
    normSq
        ((approximation parameterNonzero sheet).sample index *
            (approximation parameterNonzero sheet).sample index - parameter) <=
      CCL.FiniteGeometric.quarterRadius
        (CCL.Riemann.CoherentRoot.residualScale
          (CCL.PowerMonodromy.polynomial parameter degreeTwo)
          (RFAP.GlobalWinding.largeSquareBox
            (CCL.PowerMonodromy.polynomial parameter degreeTwo))
          (track parameterNonzero sheet)) index := by
  let source := CCL.Riemann.CoherentRoot.approximation
    (track parameterNonzero sheet)
  let selected := max (baseIndex parameterNonzero sheet) index
  have raw := CCL.Riemann.CoherentRoot.sample_residual_le
    (track parameterNonzero sheet) (by
      rw [CCL.PowerMonodromy.polynomial_degree]
      exact degreeTwo.positive) selected
  rw [CCL.PowerMonodromy.polynomial_eval] at raw
  have selectedBound := quarterRadius_index_antitone
    (CCL.Riemann.CoherentRoot.residualScale_nonneg
      (CCL.PowerMonodromy.polynomial parameter degreeTwo)
      (RFAP.GlobalWinding.largeSquareBox
        (CCL.PowerMonodromy.polynomial parameter degreeTwo))
      (track parameterNonzero sheet))
    (Nat.le_max_right (baseIndex parameterNonzero sheet) index)
  simpa only [approximation, tail_sample, source, selected, degreeTwo_value,
    pow_two] using raw.trans selectedBound

theorem sample_residual_lt_target {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) (index : Nat) :
    normSq
        ((approximation parameterNonzero sheet).sample index *
            (approximation parameterNonzero sheet).sample index - parameter) <
      residualTarget parameter := by
  let scale := CCL.Riemann.CoherentRoot.residualScale
    (CCL.PowerMonodromy.polynomial parameter degreeTwo)
    (RFAP.GlobalWinding.largeSquareBox
      (CCL.PowerMonodromy.polynomial parameter degreeTwo))
    (track parameterNonzero sheet)
  have baseSmall : CCL.FiniteGeometric.quarterRadius scale
      (baseIndex parameterNonzero sheet) < residualTarget parameter := by
    exact CCL.FiniteGeometric.firstQuarterBelow_accurate scale
      (CCL.Riemann.CoherentRoot.residualScale_nonneg
        (CCL.PowerMonodromy.polynomial parameter degreeTwo)
        (RFAP.GlobalWinding.largeSquareBox
          (CCL.PowerMonodromy.polynomial parameter degreeTwo))
        (track parameterNonzero sheet))
      0 (residualTarget parameter) (residualTarget_positive parameterNonzero)
  let selected := max (baseIndex parameterNonzero sheet) index
  have raw := CCL.Riemann.CoherentRoot.sample_residual_le
    (track parameterNonzero sheet) (by
      rw [CCL.PowerMonodromy.polynomial_degree]
      exact degreeTwo.positive) selected
  rw [CCL.PowerMonodromy.polynomial_eval] at raw
  have selectedSmall : CCL.FiniteGeometric.quarterRadius scale selected <
      residualTarget parameter :=
    (quarterRadius_index_antitone
      (CCL.Riemann.CoherentRoot.residualScale_nonneg
        (CCL.PowerMonodromy.polynomial parameter degreeTwo)
        (RFAP.GlobalWinding.largeSquareBox
          (CCL.PowerMonodromy.polynomial parameter degreeTwo))
        (track parameterNonzero sheet))
      (Nat.le_max_left (baseIndex parameterNonzero sheet) index)).trans_lt
        baseSmall
  simpa only [approximation, tail_sample, selected, degreeTwo_value,
    pow_two] using raw.trans_lt selectedSmall

/-- A square whose residual from a nonzero radicand is below one quarter of
the radicand norm has a uniform positive norm lower bound. -/
theorem normSq_lower_of_square_residual
    {parameter value : Gaussian}
    (residual : normSq (value * value - parameter) <=
      residualTarget parameter) :
    sampleNormLower parameter <= normSq value := by
  let parameterNorm := normSq parameter
  let valueNorm := normSq value
  have parameterIdentity :
      parameter = (parameter - value * value) + value * value := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
  have reversedResidual :
      normSq (parameter - value * value) <= parameterNorm / 4 := by
    have negativeIdentity :
        parameter - value * value = -(value * value - parameter) := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [sub_re, sub_im, neg_re, neg_im, mul_re, mul_im] <;> ring1
    rw [negativeIdentity, normSq_neg]
    exact residual
  have parameterUpper :
      parameterNorm <= parameterNorm / 2 + 2 * valueNorm ^ 2 := by
    have triangle := normSq_add_le_two
      (parameter - value * value) (value * value)
    rw [normSq_mul] at triangle
    calc
      parameterNorm =
          normSq ((parameter - value * value) + value * value) := by
        rw [← parameterIdentity]
      _ <= 2 * (normSq (parameter - value * value) + valueNorm ^ 2) := by
        simpa only [valueNorm, pow_two] using triangle
      _ <= 2 * (parameterNorm / 4 + valueNorm ^ 2) :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
          (add_le_add reversedResidual (le_refl _)) (by decide)
      _ = parameterNorm / 2 + 2 * valueNorm ^ 2 := by
        rw [show 2 * (parameterNorm / 4 + valueNorm ^ 2) =
            2 * (parameterNorm / 4) + 2 * valueNorm ^ 2 by ring1,
          twice_quarter_eq_half]
  have quarterLeSquare : parameterNorm / 4 <= valueNorm ^ 2 := by
    apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
      (c := (4 : Coordinate)) _ (by decide)
    have halfLe : parameterNorm / 2 <= 2 * valueNorm ^ 2 := by
      apply RFAP.ConstructiveFraction.le_of_add_le_add_right_direct
        (c := parameterNorm / 2)
      calc
        parameterNorm / 2 + parameterNorm / 2 = parameterNorm :=
          half_add_half parameterNorm
        _ <= parameterNorm / 2 + 2 * valueNorm ^ 2 := parameterUpper
        _ = 2 * valueNorm ^ 2 + parameterNorm / 2 := by ring1
    calc
      (parameterNorm / 4) * 4 = parameterNorm :=
        RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 4 (by decide)
      _ = (parameterNorm / 2) * 2 := by
        exact (RFAP.ConstructiveFraction.div_mul_cancel_of_ne
          parameterNorm 2 (by decide)).symm
      _ <= (2 * valueNorm ^ 2) * 2 :=
        RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          halfLe (by decide)
      _ = valueNorm ^ 2 * 4 := by ring1
  have residualLower : min 1 (residualTarget parameter) <= valueNorm := by
    apply le_of_not_gt
    intro tooSmall
    have valueLtOne : valueNorm < 1 :=
      tooSmall.trans_le (min_le_left _ _)
    have valueLtTarget : valueNorm < parameterNorm / 4 :=
      tooSmall.trans_le (min_le_right _ _)
    have valueSquareLeValue : valueNorm ^ 2 <= valueNorm := by
      rw [pow_two]
      calc
        valueNorm * valueNorm <= 1 * valueNorm :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            valueLtOne.le (normSq_nonneg value)
        _ = valueNorm := by ring1
    exact (not_lt_of_ge quarterLeSquare)
      (valueSquareLeValue.trans_lt valueLtTarget)
  have coordinateQuarter :
      (coordinateNormLower parameter / 2) ^ 2 <= parameterNorm / 4 := by
    calc
      (coordinateNormLower parameter / 2) ^ 2 =
          coordinateNormLower parameter ^ 2 / 4 := by
        apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
          (show (4 : Coordinate) ≠ 0 by decide)
        calc
          (coordinateNormLower parameter / 2) ^ 2 * 4 =
              ((coordinateNormLower parameter / 2) * 2) ^ 2 := by ring1
          _ = coordinateNormLower parameter ^ 2 := by
            rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 2 (by decide)]
          _ = (coordinateNormLower parameter ^ 2 / 4) * 4 := by
            rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ 4 (by decide)]
      _ <= parameterNorm / 4 := by
        rw [RFAP.ConstructiveFraction.div_eq_mul_inv_direct,
          RFAP.ConstructiveFraction.div_eq_mul_inv_direct]
        exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
          (coordinateNormLower_sq_le_normSq parameter) (by decide)
  have coordinateLower : coordinateNormLower parameter / 2 <= valueNorm :=
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct (normSq_nonneg value)
      (coordinateQuarter.trans quarterLeSquare)
  exact max_le residualLower coordinateLower

/-- Every retained rational sample is uniformly apart from zero. -/
theorem sample_norm_lower {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) (index : Nat) :
    sampleNormLower parameter <=
      normSq ((approximation parameterNonzero sheet).sample index) :=
  normSq_lower_of_square_residual
    (sample_residual_lt_target parameterNonzero sheet index).le

theorem sampleLower_positive {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) :
    0 < sampleNormLower parameter :=
  (lt_min (by decide) (residualTarget_positive parameterNonzero)).trans_le
    (le_max_left _ _)

/-- Candidate apartness of the tailed root approximation, before its boxes
are tightened for safe division. -/
def possibleApart {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) :
    CCL.ProgressiveCharts.PossibleApart
      (approximation parameterNonzero sheet).toProcess where
  lowerSq := sampleNormLower parameter
  positive := sampleLower_positive parameterNonzero
  lower := by
    intro state value possible
    change (approximation parameterNonzero sheet).Possible state value at possible
    rcases possible with ⟨later, _order, rfl⟩
    exact sample_norm_lower parameterNonzero sheet later

/-- The coherent root before denominator preparation. -/
def rawRoot {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.ofApproximation
    (approximation parameterNonzero sheet)

/-- The division-ready coherent root on one explicitly indexed sheet. -/
def root {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.apartify
    (rawRoot parameterNonzero sheet)
    (possibleApart parameterNonzero sheet)

/-- Uniform whole-ball apartness exposed by the prepared root process. -/
def rootApart {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) : CCL.ProgressiveTransducer.Named.Apart
      (root parameterNonzero sheet).name where
  certificate := CCL.ProgressiveCharts.apartifyApart
    (possibleApart parameterNonzero sheet)

/-- Explicit sampled-square approximation attached to the tailed root. -/
def squareApproximation {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) : Approximation :=
  let source := approximation parameterNonzero sheet
  let scale := 4 * source.centerBound *
    CCL.Riemann.CoherentRoot.scale (track parameterNonzero sheet)
  { sample := fun index => source.sample index * source.sample index
    radiusSq := CCL.FiniteGeometric.quarterRadius scale
    radiusSq_nonneg := CCL.FiniteGeometric.quarterRadius_nonneg
      (RFAP.ConstructiveFraction.mul_nonneg_direct
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          source.centerBound_nonneg)
        (CCL.Riemann.CoherentRoot.scale_positive
          (track parameterNonzero sheet)).le)
    later_close := by
      intro earlier later order
      have movement := source.later_close order
      have sourceRadiusLe : source.radiusSq earlier <=
          CCL.FiniteGeometric.quarterRadius
            (CCL.Riemann.CoherentRoot.scale
              (track parameterNonzero sheet)) earlier :=
        quarterRadius_index_antitone
          (CCL.Riemann.CoherentRoot.scale_positive
            (track parameterNonzero sheet)).le
          (Nat.le_max_right (baseIndex parameterNonzero sheet) earlier)
      have firstTerm :
          normSq ((source.sample later - source.sample earlier) *
              source.sample later) <=
            CCL.FiniteGeometric.quarterRadius
                (CCL.Riemann.CoherentRoot.scale
                  (track parameterNonzero sheet)) earlier *
              source.centerBound := by
        rw [normSq_mul]
        exact RFAP.ConstructiveFraction.mul_le_mul_direct
          (movement.trans sourceRadiusLe) (source.sample_bounded later)
          (normSq_nonneg _) (CCL.FiniteGeometric.quarterRadius_nonneg
            (CCL.Riemann.CoherentRoot.scale_positive
              (track parameterNonzero sheet)).le earlier)
      have secondTerm :
          normSq (source.sample earlier *
              (source.sample later - source.sample earlier)) <=
            source.centerBound *
              CCL.FiniteGeometric.quarterRadius
                (CCL.Riemann.CoherentRoot.scale
                  (track parameterNonzero sheet)) earlier := by
        rw [normSq_mul]
        exact RFAP.ConstructiveFraction.mul_le_mul_direct
          (source.sample_bounded earlier) (movement.trans sourceRadiusLe)
          (normSq_nonneg _) source.centerBound_nonneg
      have identity :
          source.sample later * source.sample later -
              source.sample earlier * source.sample earlier =
            (source.sample later - source.sample earlier) *
                source.sample later +
              source.sample earlier *
                (source.sample later - source.sample earlier) := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im] <;> ring1
      rw [identity]
      calc
        normSq
            ((source.sample later - source.sample earlier) *
                source.sample later +
              source.sample earlier *
                (source.sample later - source.sample earlier)) <=
          2 *
            (normSq ((source.sample later - source.sample earlier) *
                source.sample later) +
              normSq (source.sample earlier *
                (source.sample later - source.sample earlier))) :=
          normSq_add_le_two _ _
        _ <= 2 *
            (CCL.FiniteGeometric.quarterRadius
                (CCL.Riemann.CoherentRoot.scale
                  (track parameterNonzero sheet)) earlier *
                source.centerBound +
              source.centerBound *
                CCL.FiniteGeometric.quarterRadius
                  (CCL.Riemann.CoherentRoot.scale
                    (track parameterNonzero sheet)) earlier) :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
            (add_le_add firstTerm secondTerm) (by decide)
        _ = CCL.FiniteGeometric.quarterRadius scale earlier := by
          rw [CCL.FiniteGeometric.quarterRadius_eq_mul_pow,
            CCL.FiniteGeometric.quarterRadius_eq_mul_pow]
          dsimp only [scale]
          ring1
    refineIndex current target _ :=
      CCL.FiniteGeometric.firstQuarterBelow scale current target
    refineIndex_ge current target _ :=
      CCL.FiniteGeometric.firstQuarterBelow_ge scale current target
    refineIndex_accurate :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate scale
        (RFAP.ConstructiveFraction.mul_nonneg_direct
          (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
            source.centerBound_nonneg)
          (CCL.Riemann.CoherentRoot.scale_positive
            (track parameterNonzero sheet)).le)
    centerBound := source.centerBound * source.centerBound
    centerBound_nonneg := RFAP.ConstructiveFraction.mul_nonneg_direct
      source.centerBound_nonneg source.centerBound_nonneg
    sample_bounded := by
      intro index
      rw [normSq_mul]
      exact RFAP.ConstructiveFraction.mul_le_mul_direct
        (source.sample_bounded index) (source.sample_bounded index)
        (normSq_nonneg _) source.centerBound_nonneg }

@[simp] theorem squareApproximation_sample {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) (index : Nat) :
    (squareApproximation parameterNonzero sheet).sample index =
      (approximation parameterNonzero sheet).sample index *
        (approximation parameterNonzero sheet).sample index := by
  simp [squareApproximation]

/-- The sampled squares and the exact radicand answer every finite equality
request after an explicitly computed refinement. -/
def squareApproximation_equivalent_parameter {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) :
    CCL.OperationalEquivalence.Equivalent
      (squareApproximation parameterNonzero sheet)
      (CCL.TranscendentalLaws.constantApproximation parameter) where
  compare := by
    intro leftStart rightStart target positive
    let start := max leftStart rightStart
    let scale := CCL.Riemann.CoherentRoot.residualScale
      (CCL.PowerMonodromy.polynomial parameter degreeTwo)
      (RFAP.GlobalWinding.largeSquareBox
        (CCL.PowerMonodromy.polynomial parameter degreeTwo))
      (track parameterNonzero sheet)
    let index := CCL.FiniteGeometric.firstQuarterBelow scale start target
    have radiusSmall : CCL.FiniteGeometric.quarterRadius scale index < target :=
      CCL.FiniteGeometric.firstQuarterBelow_accurate scale
        (CCL.Riemann.CoherentRoot.residualScale_nonneg
          (CCL.PowerMonodromy.polynomial parameter degreeTwo)
          (RFAP.GlobalWinding.largeSquareBox
            (CCL.PowerMonodromy.polynomial parameter degreeTwo))
          (track parameterNonzero sheet)) start target positive
    exact
      { leftIndex := index
        rightIndex := index
        left_ge := (Nat.le_max_left _ _).trans
          (CCL.FiniteGeometric.firstQuarterBelow_ge scale start target)
        right_ge := (Nat.le_max_right _ _).trans
          (CCL.FiniteGeometric.firstQuarterBelow_ge scale start target)
        close := by
          intro leftLater rightLater leftOrder _rightOrder
          have residualBound := sample_residual_le parameterNonzero sheet
            leftLater
          have radiusLater := quarterRadius_index_antitone
            (CCL.Riemann.CoherentRoot.residualScale_nonneg
              (CCL.PowerMonodromy.polynomial parameter degreeTwo)
              (RFAP.GlobalWinding.largeSquareBox
                (CCL.PowerMonodromy.polynomial parameter degreeTwo))
              (track parameterNonzero sheet)) leftOrder
          simpa only [squareApproximation_sample,
            CCL.TranscendentalLaws.constantApproximation] using
              residualBound.trans_lt (radiusLater.trans_lt radiusSmall) }

/-- Before denominator preparation, the actual CCL multiplication of a root
name by itself is operationally the exact radicand. -/
def rawRoot_square {parameter : Gaussian}
    (parameterNonzero : parameter ≠ 0) (sheet : Fin 2) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (rawRoot parameterNonzero sheet)
        (rawRoot parameterNonzero sheet)).name
      (CCL.ProgressiveTransducer.Named.exact parameter) := by
  let source := approximation parameterNonzero sheet
  let product := squareApproximation parameterNonzero sheet
  have actualToProduct : NamedEquivalent
      (CCL.ProgressiveTransducer.Named.mul source.toNamed source.toNamed)
      product.toNamed :=
    CCL.TranscendentalCoherence.mulToNamed_equivalent_pointwise
      source source product (by intro index; rfl)
  have productToConstant : NamedEquivalent product.toNamed
      (CCL.TranscendentalLaws.constantApproximation parameter).toNamed :=
    CCL.TranscendentalCoherence.approximationEquivalent_toNamed
      (squareApproximation_equivalent_parameter parameterNonzero sheet)
  exact CCL.OperationalEquivalence.NamedEquivalent.trans
    (by simpa only [rawRoot,
      CCL.ProgressiveCoherence.CoherentNamed.mul,
      CCL.ProgressiveCoherence.CoherentNamed.ofApproximation, source, product]
      using actualToProduct)
    (CCL.OperationalEquivalence.NamedEquivalent.trans productToConstant
      (CCL.OperationalEquivalence.NamedEquivalent.symm
        (CCL.TranscendentalCoherence.exact_toConstantNamed parameter)))

/-- The division-ready root still squares operationally to the displayed
radicand. -/
def root_square {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (sheet : Fin 2) :
    NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        (root parameterNonzero sheet)
        (root parameterNonzero sheet)).name
      (CCL.ProgressiveTransducer.Named.exact parameter) := by
  let raw := rawRoot parameterNonzero sheet
  let prepared := root parameterNonzero sheet
  have preparedToRaw : NamedEquivalent prepared.name raw.name :=
    CCL.OperationalEquivalence.NamedEquivalent.symm
      (CCL.ProgressiveCoherence.CoherentNamed.apartifyEquivalent raw
        (possibleApart parameterNonzero sheet))
  have products : NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul prepared prepared).name
      (CCL.ProgressiveCoherence.CoherentNamed.mul raw raw).name :=
    CCL.TranscendentalCoherence.coherentMul_respects
      prepared raw prepared raw preparedToRaw preparedToRaw
  exact CCL.OperationalEquivalence.NamedEquivalent.trans products
    (rawRoot_square parameterNonzero sheet)

/-- All data carried by one explicitly indexed square-root sheet. -/
structure Sheet (parameter : Gaussian) where
  index : Fin 2
  value : CoherentNamed
  apart : CCL.ProgressiveTransducer.Named.Apart value.name
  square : NamedEquivalent
    (CCL.ProgressiveCoherence.CoherentNamed.mul value value).name
    (CCL.ProgressiveTransducer.Named.exact parameter)

/-- Automatic construction of either sheet from its finite index. -/
def sheet {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (index : Fin 2) : Sheet parameter where
  index := index
  value := root parameterNonzero index
  apart := rootApart parameterNonzero index
  square := root_square parameterNonzero index

/-- The complete finite family of both indexed sheets. -/
def family {parameter : Gaussian} (parameterNonzero : parameter ≠ 0) :
    Fin 2 -> Sheet parameter :=
  sheet parameterNonzero

end CCL.Riemann.SquareRootSheets
