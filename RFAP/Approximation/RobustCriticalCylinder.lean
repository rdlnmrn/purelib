import mathlib.Data.ConstructiveList
import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.CriticalTwoWindowTower

/-!
# Finite coefficient reduction near transported critical sources

At the exact critical source, the two-parameter cylinder theorem controls
every integral coefficient pair.  After perturbing the source, a competitor
inside the displayed mixed cylinder might no longer be exterior by the same
exact identity.  This file proves the required finite reduction: inside an
explicit positive rational squared-distance budget, every such competitor
has both coefficient quadrances `< 32`.
-/

namespace RFAP.RobustCriticalCylinder

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt
abbrev Fraction := RFAP.HurwitzRational.Fraction
abbrev Pair := RFAP.HurwitzRational.ConvergentPair

open RFAP.BestApproximation
open RFAP.ConstructiveGaussianHeight.GaussianInt

/-- A conservative positive squared-distance budget under which an apparent
mixed-cylinder competitor has exact-source normalized error quadrance at
most five. -/
def coefficientCutoffDistanceSq
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage) : Coordinate :=
  RFAP.ConstructiveGaussian.Gaussian.normSq normal.lowerError /
    (6 * (denominatorQuadrance
      (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage) :
        Coordinate))

theorem coefficientCutoffDistanceSq_pos
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage) :
    0 < coefficientCutoffDistanceSq normal := by
  unfold coefficientCutoffDistanceSq
  apply RFAP.ConstructiveFraction.div_pos_direct normal.lowerErrorPositive
  apply RFAP.ConstructiveFraction.mul_pos_direct (by decide)
  apply RFAP.ConstructiveFraction.natCast_pos_direct
  exact normNat_pos
    (RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero
      targetStage)

private theorem error_perturbation_identity
    (center sample : Gaussian) (pair : Pair) :
    RFAP.HurwitzApproximation.error sample pair =
      RFAP.HurwitzApproximation.error center pair +
        (sample - center) * toGaussian pair.denominator := by
  unfold RFAP.HurwitzApproximation.error
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

private theorem exact_error_identity
    (center sample : Gaussian) (pair : Pair) :
    RFAP.HurwitzApproximation.error center pair =
      RFAP.HurwitzApproximation.error sample pair -
        (sample - center) * toGaussian pair.denominator := by
  calc
    RFAP.HurwitzApproximation.error center pair =
        (RFAP.HurwitzApproximation.error center pair +
            (sample - center) * toGaussian pair.denominator) -
          (sample - center) * toGaussian pair.denominator := by
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.sub_re,
          RFAP.ConstructiveGaussian.Gaussian.sub_im,
          RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im] <;>
        ring1
    _ = RFAP.HurwitzApproximation.error sample pair -
        (sample - center) * toGaussian pair.denominator := by
      exact (congrArg
        (fun value => value -
          (sample - center) * toGaussian pair.denominator)
        (error_perturbation_identity center sample pair)).symm

private theorem perturbation_normSq
    (center sample : Gaussian) (pair : Pair) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        ((sample - center) * toGaussian pair.denominator) =
      RFAP.ConstructiveGaussian.Gaussian.normSq (sample - center) *
        (denominatorQuadrance pair : Coordinate) := by
  rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul, normSq_toGaussian]
  rfl

/-- A denominator-bounded coefficient combination has normalized target
denominator quadrance at most one. -/
theorem normalizedDenominator_normSq_le_one
    (targetStage : Nat) (left right : GaussianInt)
    (denominatorBound :
      denominatorQuadrance
          (linearCombination
            (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
            (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)
            left right) ≤
        denominatorQuadrance
          (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (RFAP.TwoParameterCylinder.normalizedDenominator
          (RFAP.FiniteWindowSharpness.pellParameter targetStage)
          left right) ≤ 1 := by
  let upper := RFAP.FiniteWindowSharpness.criticalUpperPair targetStage
  let candidate := linearCombination
    (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage) upper left right
  have upperPositive :
      (0 : Coordinate) < denominatorQuadrance upper := by
    apply RFAP.ConstructiveFraction.natCast_pos_direct
    exact normNat_pos
      (RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero
        targetStage)
  have castBound :
      (denominatorQuadrance candidate : Coordinate) ≤
        (denominatorQuadrance upper : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_le_direct denominatorBound
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := (denominatorQuadrance upper : Coordinate))
  · calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.TwoParameterCylinder.normalizedDenominator
              (RFAP.FiniteWindowSharpness.pellParameter targetStage)
              left right) *
          (denominatorQuadrance upper : Coordinate) =
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (toGaussian upper.denominator *
            RFAP.TwoParameterCylinder.normalizedDenominator
              (RFAP.FiniteWindowSharpness.pellParameter targetStage)
              left right) := by
          rw [RFAP.ConstructiveGaussian.Gaussian.normSq_mul,
            normSq_toGaussian]
          unfold denominatorQuadrance
          ring1
      _ = RFAP.ConstructiveGaussian.Gaussian.normSq
          (toGaussian candidate.denominator) := by
        rw [RFAP.CriticalTwoWindowTower.target_denominator_linearCombination]
      _ = (denominatorQuadrance candidate : Coordinate) := by
        rw [normSq_toGaussian]
        rfl
      _ ≤ (denominatorQuadrance upper : Coordinate) := castBound
      _ = (1 : Coordinate) * denominatorQuadrance upper := by ring1
  · exact upperPositive

/-- Within the explicit cutoff budget, any candidate whose sampled error is
no larger than the sampled lower-basis error and whose denominator is no
larger than the upper-basis denominator has exact normalized error quadrance
at most five. -/
theorem normalizedError_normSq_le_five
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    (sample : Gaussian) (left right : GaussianInt)
    (sampleErrorBound :
      errorQuadrance sample
          (linearCombination
            (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
            (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)
            left right) ≤
        errorQuadrance sample
          (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage))
    (denominatorBound :
      denominatorQuadrance
          (linearCombination
            (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
            (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)
            left right) ≤
        denominatorQuadrance
          (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage))
    (distanceSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq (sample - source.value) ≤
        coefficientCutoffDistanceSq normal) :
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (RFAP.TwoParameterCylinder.normalizedError
          (RFAP.FiniteWindowSharpness.pellParameter errorStage)
          left right) ≤ 5 := by
  let lower := RFAP.FiniteWindowSharpness.criticalLowerPair targetStage
  let upper := RFAP.FiniteWindowSharpness.criticalUpperPair targetStage
  let candidate := linearCombination lower upper left right
  let distance :=
    RFAP.ConstructiveGaussian.Gaussian.normSq (sample - source.value)
  let lowerScale : Coordinate := denominatorQuadrance lower
  let upperScale : Coordinate := denominatorQuadrance upper
  let candidateScale : Coordinate := denominatorQuadrance candidate
  let exactScale :=
    RFAP.ConstructiveGaussian.Gaussian.normSq normal.lowerError
  have distanceNonnegative : 0 ≤ distance :=
    RFAP.ConstructiveGaussian.Gaussian.normSq_nonneg _
  have upperScalePositive : 0 < upperScale := by
    dsimp only [upperScale, upper]
    apply RFAP.ConstructiveFraction.natCast_pos_direct
    exact normNat_pos
      (RFAP.FiniteWindowSharpness.criticalUpper_denominator_ne_zero
        targetStage)
  have lowerScaleLeUpper : lowerScale ≤ upperScale := by
    dsimp only [lowerScale, upperScale, lower, upper]
    exact RFAP.ConstructiveFraction.natCast_le_direct
      (RFAP.FiniteWindowSharpness.critical_denominatorQuadrance_ordered
        targetStage).le
  have candidateScaleLeUpper : candidateScale ≤ upperScale := by
    dsimp only [candidateScale, upperScale, candidate, lower, upper]
    exact RFAP.ConstructiveFraction.natCast_le_direct denominatorBound
  have scaledDistanceLe : 6 * (distance * upperScale) ≤ exactScale := by
    have denominatorPositive : 0 < 6 * upperScale :=
      RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        upperScalePositive
    have divided :=
      (RFAP.ConstructiveFraction.le_div_iff_pos denominatorPositive).1
        (show distance ≤ exactScale / (6 * upperScale) by
          simpa only [distance, exactScale, upperScale,
            coefficientCutoffDistanceSq, upper] using distanceSmall)
    calc
      6 * (distance * upperScale) = distance * (6 * upperScale) := by ring1
      _ ≤ exactScale := divided
  have lowerPerturbationBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((sample - source.value) * toGaussian lower.denominator) ≤
        distance * upperScale := by
    rw [perturbation_normSq]
    dsimp only [distance, lowerScale]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      lowerScaleLeUpper distanceNonnegative
  have candidatePerturbationBound :
      RFAP.ConstructiveGaussian.Gaussian.normSq
          ((sample - source.value) * toGaussian candidate.denominator) ≤
        distance * upperScale := by
    rw [perturbation_normSq]
    dsimp only [distance, candidateScale]
    exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      candidateScaleLeUpper distanceNonnegative
  have sampleLowerBound :
      errorQuadrance sample lower ≤
        2 * (exactScale + distance * upperScale) := by
    unfold errorQuadrance
    rw [error_perturbation_identity source.value sample lower,
      normal.lowerIdentity]
    exact (RFAP.ConstructiveGaussian.Gaussian.normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (RFAP.ConstructiveFraction.add_le_add_direct (le_refl exactScale)
          lowerPerturbationBound) (by decide))
  have exactCandidateBound :
      errorQuadrance source.value candidate ≤ 5 * exactScale := by
    unfold errorQuadrance
    rw [exact_error_identity source.value sample candidate]
    calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (RFAP.HurwitzApproximation.error sample candidate -
            (sample - source.value) * toGaussian candidate.denominator) ≤
        2 *
          (RFAP.ConstructiveGaussian.Gaussian.normSq
              (RFAP.HurwitzApproximation.error sample candidate) +
            RFAP.ConstructiveGaussian.Gaussian.normSq
              ((sample - source.value) *
                toGaussian candidate.denominator)) :=
        RFAP.ConstructiveGaussian.Gaussian.normSq_sub_le_two _ _
      _ ≤ 2 * (errorQuadrance sample lower + distance * upperScale) := by
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        exact RFAP.ConstructiveFraction.add_le_add_direct sampleErrorBound
          candidatePerturbationBound
      _ ≤ 2 * (2 * (exactScale + distance * upperScale) +
          distance * upperScale) := by
        apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
          (by decide)
        exact RFAP.ConstructiveFraction.add_le_add_direct sampleLowerBound
          (le_refl _)
      _ = 4 * exactScale + 6 * (distance * upperScale) := by ring1
      _ ≤ 4 * exactScale + exactScale :=
        RFAP.ConstructiveFraction.add_le_add_direct (le_refl _)
          scaledDistanceLe
      _ = 5 * exactScale := by ring1
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := exactScale)
  · calc
      RFAP.ConstructiveGaussian.Gaussian.normSq
            (RFAP.TwoParameterCylinder.normalizedError
              (RFAP.FiniteWindowSharpness.pellParameter errorStage)
              left right) * exactScale =
        errorQuadrance source.value candidate := by
          unfold errorQuadrance
          rw [normal.error_linearCombination,
            RFAP.ConstructiveGaussian.Gaussian.normSq_mul]
          dsimp only [exactScale]
          ring1
      _ ≤ 5 * exactScale := exactCandidateBound
  · simpa only [exactScale] using normal.lowerErrorPositive

/-- The perturbative mixed-cylinder reduction: every sampled competitor in
the displayed closed cylinder comes from Gaussian-integral coefficient
quadrances `< 32`. -/
theorem coefficient_normNat_lt_thirtyTwo_of_nearby_competitor
    {source : Fraction} {errorStage targetStage : Nat}
    (normal : RFAP.CriticalTwoWindowTower.TransportedNormalForm
      source errorStage targetStage)
    (sample : Gaussian) (left right : GaussianInt)
    (sampleErrorBound :
      errorQuadrance sample
          (linearCombination
            (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
            (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)
            left right) ≤
        errorQuadrance sample
          (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage))
    (denominatorBound :
      denominatorQuadrance
          (linearCombination
            (RFAP.FiniteWindowSharpness.criticalLowerPair targetStage)
            (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage)
            left right) ≤
        denominatorQuadrance
          (RFAP.FiniteWindowSharpness.criticalUpperPair targetStage))
    (distanceSmall :
      RFAP.ConstructiveGaussian.Gaussian.normSq (sample - source.value) ≤
        coefficientCutoffDistanceSq normal) :
    normNat left < 32 ∧ normNat right < 32 := by
  apply RFAP.TwoParameterCylinder.coefficient_normNat_lt_thirtyTwo
    (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical errorStage)
    (RFAP.FiniteWindowSharpness.pellParameter_isFiniteCritical targetStage)
  · exact normalizedError_normSq_le_five normal sample left right
      sampleErrorBound denominatorBound distanceSmall
  · exact normalizedDenominator_normSq_le_one targetStage left right
      denominatorBound

/-! ## Executable bounded coefficient domain -/

/-- A small rectangular over-enumeration of every Gaussian integer with
quadrance `< 32`.  Component magnitude five is sufficient because magnitude
six alone already contributes quadrance thirty-six. -/
def boundedCoefficients : List GaussianInt :=
  componentSquare 5

@[simp] theorem boundedCoefficients_length :
    boundedCoefficients.length = 144 := by
  unfold boundedCoefficients
  rw [componentSquare_length]
  decide

private theorem realComponent_natAbs_le_five_of_normNat_lt_thirtyTwo
    (value : GaussianInt) (bounded : normNat value < 32) :
    value.re.natAbs ≤ 5 := by
  have squareStrict : value.re.natAbs ^ 2 < 32 := by
    calc
      value.re.natAbs ^ 2 ≤
          value.re.natAbs ^ 2 + value.im.natAbs ^ 2 :=
        Nat.le_add_right _ _
      _ = normNat value := (normNat_eq_component_squares value).symm
      _ < 32 := bounded
  by_contra tooLarge
  have sixLe : 6 ≤ value.re.natAbs := by omega
  have squareLower : 36 ≤ value.re.natAbs ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul sixLe sixLe
  omega

private theorem imaginaryComponent_natAbs_le_five_of_normNat_lt_thirtyTwo
    (value : GaussianInt) (bounded : normNat value < 32) :
    value.im.natAbs ≤ 5 := by
  have squareStrict : value.im.natAbs ^ 2 < 32 := by
    calc
      value.im.natAbs ^ 2 ≤
          value.re.natAbs ^ 2 + value.im.natAbs ^ 2 :=
        Nat.le_add_left _ _
      _ = normNat value := (normNat_eq_component_squares value).symm
      _ < 32 := bounded
  by_contra tooLarge
  have sixLe : 6 ≤ value.im.natAbs := by omega
  have squareLower : 36 ≤ value.im.natAbs ^ 2 := by
    simpa only [pow_two] using Nat.mul_le_mul sixLe sixLe
  omega

theorem mem_boundedCoefficients_of_normNat_lt_thirtyTwo
    {value : GaussianInt} (bounded : normNat value < 32) :
    value ∈ boundedCoefficients := by
  unfold boundedCoefficients componentSquare
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨value.re,
    mem_signedComponents
      (realComponent_natAbs_le_five_of_normNat_lt_thirtyTwo value bounded),
    ?_⟩
  apply QuotientFreeList.mem_map.mpr
  refine ⟨value.im,
    mem_signedComponents
      (imaginaryComponent_natAbs_le_five_of_normNat_lt_thirtyTwo
        value bounded), ?_⟩
  rfl

/-- The executable finite domain of all coefficient pairs requiring robust
error-comparison margins. -/
def boundedCoefficientPairs : List (GaussianInt × GaussianInt) :=
  boundedCoefficients.flatMap fun left =>
    boundedCoefficients.map fun right => (left, right)

private theorem length_flatMap_constant
    {Outer Inner Result : Type} (outer : List Outer) (inner : List Inner)
    (combine : Outer → Inner → Result) :
    (outer.flatMap fun left => inner.map (combine left)).length =
      outer.length * inner.length := by
  induction outer with
  | nil => simp only [List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head remaining inductionHypothesis =>
      simp only [List.flatMap_cons, List.length_append, List.length_map,
        List.length_cons, inductionHypothesis, Nat.add_mul, Nat.one_mul]
      exact Nat.add_comm _ _

@[simp] theorem boundedCoefficientPairs_length :
    boundedCoefficientPairs.length = 20736 := by
  unfold boundedCoefficientPairs
  rw [length_flatMap_constant, boundedCoefficients_length]

theorem mem_boundedCoefficientPairs_of_normNat_lt_thirtyTwo
    {left right : GaussianInt}
    (leftBounded : normNat left < 32)
    (rightBounded : normNat right < 32) :
    (left, right) ∈ boundedCoefficientPairs := by
  unfold boundedCoefficientPairs
  apply QuotientFreeList.mem_flatMap.mpr
  refine ⟨left,
    mem_boundedCoefficients_of_normNat_lt_thirtyTwo leftBounded, ?_⟩
  apply QuotientFreeList.mem_map.mpr
  exact ⟨right,
    mem_boundedCoefficients_of_normNat_lt_thirtyTwo rightBounded, rfl⟩

-- Keep the 20,736-entry executable value opaque to ordinary elaboration;
-- its exact length and completeness are exposed by the theorems above.
attribute [irreducible] boundedCoefficientPairs

end RFAP.RobustCriticalCylinder
