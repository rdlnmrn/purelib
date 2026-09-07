import CCL.Riemann.GeneratedLegendreCertificateData

/-!
# Semantic interpretation of generated Legendre certificate rows

The generated shards use an integer-only checker.  This module interprets a
successful row as ordinary rational Gaussian geometry.  Keeping this layer
separate means changes to theorem-facing proofs do not cause the thousands of
literal row checks to elaborate again.
-/

namespace CCL.Riemann.GeneratedLegendreCertificateData

open RFAP.ConstructiveGaussian.Gaussian

namespace Dyadic

theorem not_le_sound {left right : Dyadic} (checked : left.le right = false) :
    right.toCoordinate < left.toCoordinate := by
  apply lt_sound
  unfold Dyadic.lt
  apply decide_eq_true
  unfold Dyadic.le at checked
  have notAligned := of_decide_eq_false checked
  simpa only [max_comm] using lt_of_not_ge notAligned

theorem le_complete {left right : Dyadic}
    (ordered : left.toCoordinate <= right.toCoordinate) :
    left.le right = true := by
  cases checked : left.le right with
  | true => rfl
  | false =>
      exact (not_lt_of_ge ordered (not_le_sound checked)).elim

theorem min_toCoordinate_le_left (left right : Dyadic) :
    (left.min right).toCoordinate <= left.toCoordinate := by
  cases checked : left.le right with
  | true =>
      rw [min, checked, if_pos rfl]
  | false =>
      rw [min, checked, if_neg (by decide)]
      exact (not_le_sound checked).le

theorem min_toCoordinate_le_right (left right : Dyadic) :
    (left.min right).toCoordinate <= right.toCoordinate := by
  cases checked : left.le right with
  | true =>
      rw [min, checked, if_pos rfl]
      exact le_sound checked
  | false =>
      rw [min, checked, if_neg (by decide)]

/-- Reconstructing a dyadic from its stored numerator and a propositionally
equal bit count does not change its rational value. -/
theorem toCoordinate_reconstruct (value : Dyadic) (bits : Nat)
    (bits_eq : value.bits = bits) :
    (Dyadic.mk value.numerator bits).toCoordinate = value.toCoordinate := by
  cases value with
  | mk numerator valueBits =>
      change valueBits = bits at bits_eq
      subst bits
      rfl

@[simp] theorem toCoordinate_zero_numerator (bits : Nat) :
    (Dyadic.mk 0 bits).toCoordinate = 0 := by
  unfold Dyadic.toCoordinate Dyadic.toFraction
  rw [RFAP.ConstructiveFraction.ofFraction_eq_div]
  exact RFAP.ConstructiveFraction.zero_div_direct _

end Dyadic

namespace CompactCellData

/-- The generator's displayed parameter is definitionally the parameter of
the explicit Legendre loop-base curve. -/
@[simp] theorem lambda_eq_baseParameter :
    lambda = CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseParameter := rfl

/-- The factored cubic checked by the generator is exactly the polynomial of
the explicit loop-base curve, rather than a parallel numerical convention. -/
theorem radicand_eq_baseCurve_eval (point : Gaussian) :
    radicand point =
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
        point := by
  rw [CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve_polynomial,
    CCL.Riemann.LegendrePaths.polynomial_eval]
  rfl

def startValue (data : CompactCellData) : Gaussian := data.start.toGaussian

def finishValue (data : CompactCellData) : Gaussian := data.finish.toGaussian

def displacementValue (data : CompactCellData) : Gaussian :=
  data.finishValue - data.startValue

def parameterValue (data : CompactCellData) (parameter : Coordinate) : Gaussian :=
  data.startValue + CCL.FiniteExp.scale parameter data.displacementValue

@[simp] theorem parameterValue_zero (data : CompactCellData) :
    data.parameterValue 0 = data.startValue := by
  unfold parameterValue
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [CCL.FiniteExp.scale_re, add_re]
    ring1
  · simp only [CCL.FiniteExp.scale_im, add_im]
    ring1

@[simp] theorem parameterValue_one (data : CompactCellData) :
    data.parameterValue 1 = data.finishValue := by
  unfold parameterValue displacementValue
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · simp only [CCL.FiniteExp.scale_re, add_re, sub_re]
    ring1
  · simp only [CCL.FiniteExp.scale_im, add_im, sub_im]
    ring1

theorem halfWidthSq_toCoordinate (data : CompactCellData) :
    (Dyadic.mk 1 (2 * data.halfWidthBits)).toCoordinate =
      data.halfWidth ^ 2 := by
  unfold halfWidth
  rw [pow_two, <- Dyadic.toCoordinate_mul]
  congr 1
  simp only [Dyadic.mul]
  rw [two_mul]
  rfl

theorem twiceHalfWidthSq_toCoordinate (data : CompactCellData) :
    (Dyadic.mk 2 (2 * data.halfWidthBits)).toCoordinate =
      2 * data.halfWidth ^ 2 := by
  change ((Dyadic.mk 1 (2 * data.halfWidthBits)).scale 2).toCoordinate = _
  rw [Dyadic.toCoordinate_scale, halfWidthSq_toCoordinate]
  rfl

theorem halfWidthFourth_toCoordinate (data : CompactCellData) :
    (Dyadic.mk 1 (4 * data.halfWidthBits)).toCoordinate =
      data.halfWidth ^ 4 := by
  have bitsIdentity :
      4 * data.halfWidthBits =
        2 * data.halfWidthBits + 2 * data.halfWidthBits := by omega
  rw [bitsIdentity]
  change (((Dyadic.mk 1 (2 * data.halfWidthBits)).mul
    (Dyadic.mk 1 (2 * data.halfWidthBits))).toCoordinate) = _
  rw [Dyadic.toCoordinate_mul, halfWidthSq_toCoordinate]
  ring1

@[simp] theorem dyadicLambda_toGaussian : dyadicLambda.toGaussian = lambda := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [dyadicLambda, scaledPoint, DyadicGaussian.toGaussian,
      geometryBits, lambda, point]
  · decide +revert
  · decide +revert

@[simp] theorem dyadicGaussian_one_toGaussian :
    (1 : DyadicGaussian).toGaussian = 1 := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · exact Dyadic.toCoordinate_ofInt 1
  · exact Dyadic.toCoordinate_ofInt 0

@[simp] theorem radicandAt_toGaussian (data : CompactCellData) :
    data.radicandAt.toGaussian = radicand data.startValue := by
  unfold radicandAt radicand startValue
  rw [DyadicGaussian.toGaussian_mul, DyadicGaussian.toGaussian_mul,
    DyadicGaussian.toGaussian_sub, DyadicGaussian.toGaussian_sub,
    dyadicGaussian_one_toGaussian, dyadicLambda_toGaussian]

@[simp] theorem radicandAtNormSq_toCoordinate (data : CompactCellData) :
    data.radicandAt.normSq.toCoordinate = normSq (radicand data.startValue) := by
  rw [DyadicGaussian.normSq_toGaussian, radicandAt_toGaussian]

@[simp] theorem rootResidualSq_toCoordinate (rootBits : Nat)
    (data : CompactCellData) :
    (data.rootResidualSq rootBits).toCoordinate =
      normSq (data.rootCenterValue rootBits * data.rootCenterValue rootBits -
        radicand data.startValue) := by
  unfold rootResidualSq rootCenterValue
  rw [DyadicGaussian.normSq_toGaussian]
  change normSq (((data.rootCenter rootBits).mul
      (data.rootCenter rootBits)).sub data.radicandAt).toGaussian = _
  rw [DyadicGaussian.toGaussian_sub, DyadicGaussian.toGaussian_mul,
    radicandAt_toGaussian]

def variationLinear (data : CompactCellData) : Gaussian :=
  (data.startValue * CCL.FiniteExp.scale 3 data.startValue -
      CCL.FiniteExp.scale 2 data.startValue * (1 + lambda) + lambda) *
    data.displacementValue

def variationQuadratic (data : CompactCellData) : Gaussian :=
  (CCL.FiniteExp.scale 3 data.startValue - (1 + lambda)) *
    (data.displacementValue * data.displacementValue)

def variationCubic (data : CompactCellData) : Gaussian :=
  data.displacementValue * data.displacementValue * data.displacementValue

theorem scale_two (value : Gaussian) :
    CCL.FiniteExp.scale 2 value = value + value := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im, add_re,
      add_im] <;> ring1

theorem scale_three (value : Gaussian) :
    CCL.FiniteExp.scale 3 value = value + value + value := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im, add_re,
      add_im] <;> ring1

theorem scale_mul_scale (left right : Coordinate) (x y : Gaussian) :
    CCL.FiniteExp.scale left x * CCL.FiniteExp.scale right y =
      CCL.FiniteExp.scale (left * right) (x * y) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im, mul_re,
      mul_im] <;> ring1

theorem scale_mul_right (factor : Coordinate) (x y : Gaussian) :
    CCL.FiniteExp.scale factor x * y =
      CCL.FiniteExp.scale factor (x * y) := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [CCL.FiniteExp.scale_re, CCL.FiniteExp.scale_im, mul_re,
      mul_im] <;> ring1

@[simp] theorem radicandVariationSq_toCoordinate (data : CompactCellData) :
    data.radicandVariationSq.toCoordinate =
      2 * normSq data.variationLinear +
        4 * (normSq data.variationQuadratic +
          normSq data.variationCubic) := by
  unfold radicandVariationSq variationLinear variationQuadratic variationCubic
    displacementValue finishValue startValue
  rw [Dyadic.toCoordinate_add, Dyadic.toCoordinate_scale,
    Dyadic.toCoordinate_scale, Dyadic.toCoordinate_add,
    DyadicGaussian.normSq_toGaussian,
    DyadicGaussian.normSq_toGaussian, DyadicGaussian.normSq_toGaussian]
  change (2 : Coordinate) * normSq _ +
      (4 : Coordinate) * (normSq _ + normSq _) = _
  simp only [DyadicGaussian.toGaussian_mul,
    DyadicGaussian.toGaussian_mul,
    DyadicGaussian.toGaussian_mul, DyadicGaussian.toGaussian_mul,
    DyadicGaussian.toGaussian_mul, DyadicGaussian.toGaussian_mul,
    DyadicGaussian.toGaussian_mul, DyadicGaussian.toGaussian_sub,
    DyadicGaussian.toGaussian_sub, DyadicGaussian.toGaussian_sub,
    DyadicGaussian.toGaussian_add, DyadicGaussian.toGaussian_add,
    DyadicGaussian.toGaussian_scale, DyadicGaussian.toGaussian_scale,
    dyadicLambda_toGaussian]
  rfl

theorem radicand_parameter_sub_start (data : CompactCellData)
    (parameter : Coordinate) :
    radicand (data.parameterValue parameter) - radicand data.startValue =
      CCL.FiniteExp.scale parameter data.variationLinear +
        (CCL.FiniteExp.scale (parameter ^ 2) data.variationQuadratic +
          CCL.FiniteExp.scale (parameter ^ 3) data.variationCubic) := by
  let start := data.startValue
  let displacement := data.displacementValue
  let increment := CCL.FiniteExp.scale parameter displacement
  let linearCoefficient :=
    start * CCL.FiniteExp.scale 3 start -
      CCL.FiniteExp.scale 2 start * (1 + lambda) + lambda
  let quadraticCoefficient :=
    CCL.FiniteExp.scale 3 start - (1 + lambda)
  have expansion :
      radicand (start + increment) - radicand start =
        increment * linearCoefficient +
          (increment * increment) * quadraticCoefficient +
            increment * increment * increment := by
    dsimp only [linearCoefficient, quadraticCoefficient]
    rw [scale_two, scale_three]
    unfold radicand
    ring1
  have linearTerm :
      CCL.FiniteExp.scale parameter (displacement * linearCoefficient) =
        CCL.FiniteExp.scale parameter (linearCoefficient * displacement) := by
    rw [_root_.mul_comm displacement linearCoefficient]
  have quadraticTerm :
      CCL.FiniteExp.scale (parameter * parameter)
          ((displacement * displacement) * quadraticCoefficient) =
        CCL.FiniteExp.scale (parameter ^ 2)
          (quadraticCoefficient * (displacement * displacement)) := by
    rw [pow_two, _root_.mul_comm (displacement * displacement)
      quadraticCoefficient]
  have cubicTerm :
      CCL.FiniteExp.scale (parameter * parameter * parameter)
          ((displacement * displacement) * displacement) =
        CCL.FiniteExp.scale (parameter ^ 3)
          (displacement * displacement * displacement) := by
    rw [show parameter ^ 3 = parameter * parameter * parameter by ring1]
  change radicand (start + increment) - radicand start = _
  rw [expansion]
  dsimp only [increment]
  rw [scale_mul_right, scale_mul_scale, scale_mul_right,
    scale_mul_scale, linearTerm, quadraticTerm, cubicTerm]
  dsimp only [variationLinear, variationQuadratic, variationCubic,
    linearCoefficient, quadraticCoefficient, start, displacement]
  ring1

theorem normSq_scale_pow_le (parameter : Coordinate)
    (parameterNonnegative : 0 <= parameter) (parameterUpper : parameter <= 1)
    (exponent : Nat) (value : Gaussian) :
    normSq (CCL.FiniteExp.scale (parameter ^ exponent) value) <= normSq value := by
  rw [CCL.FiniteExp.normSq_scale]
  have powerNonnegative : 0 <= parameter ^ exponent :=
    RFAP.ConstructiveFraction.pow_nonneg_direct parameterNonnegative exponent
  have powerUpper : parameter ^ exponent <= (1 : Coordinate) ^ exponent :=
    RFAP.ConstructiveFraction.pow_le_pow_direct parameterNonnegative
      parameterUpper exponent
  have squareUpper : (parameter ^ exponent) ^ 2 <= (1 : Coordinate) ^ 2 :=
    RFAP.ConstructiveFraction.pow_le_pow_direct powerNonnegative
      (by simpa only [one_pow] using powerUpper) 2
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
    squareUpper (normSq_nonneg value)
  calc
    (parameter ^ exponent) ^ 2 * normSq value <= 1 * normSq value := by
      simpa only [one_pow] using scaled
    _ = normSq value := one_mul _

theorem add_three_sq_le (first second third : Coordinate) :
    (first + second + third) ^ 2 <=
      3 * (first ^ 2 + second ^ 2 + third ^ 2) := by
  apply sub_nonneg.mp
  calc
    0 <= (first - second) ^ 2 + (first - third) ^ 2 +
        (second - third) ^ 2 :=
      add_nonneg
        (add_nonneg
          (RFAP.ConstructiveFraction.sq_nonneg_direct (first - second))
          (RFAP.ConstructiveFraction.sq_nonneg_direct (first - third)))
        (RFAP.ConstructiveFraction.sq_nonneg_direct (second - third))
    _ = 3 * (first ^ 2 + second ^ 2 + third ^ 2) -
        (first + second + third) ^ 2 := by ring1

theorem normSq_add_add_le_three (first second third : Gaussian) :
    normSq (first + (second + third)) <=
      3 * (normSq first + normSq second + normSq third) := by
  have realBound := add_three_sq_le first.re second.re third.re
  have imaginaryBound := add_three_sq_le first.im second.im third.im
  unfold normSq
  simp only [add_re, add_im]
  calc
    (first.re + (second.re + third.re)) ^ 2 +
        (first.im + (second.im + third.im)) ^ 2 <=
      3 * (first.re ^ 2 + second.re ^ 2 + third.re ^ 2) +
        3 * (first.im ^ 2 + second.im ^ 2 + third.im ^ 2) := by
          simpa only [_root_.add_assoc] using add_le_add realBound imaginaryBound
    _ = 3 *
        (first.re ^ 2 + first.im ^ 2 +
          (second.re ^ 2 + second.im ^ 2) +
          (third.re ^ 2 + third.im ^ 2)) := by ring1

theorem parameterizedVariation_le (data : CompactCellData)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) :
    normSq
        (CCL.FiniteExp.scale parameter data.variationLinear +
          (CCL.FiniteExp.scale (parameter ^ 2) data.variationQuadratic +
            CCL.FiniteExp.scale (parameter ^ 3) data.variationCubic)) <=
      2 * normSq data.variationLinear +
        4 * (normSq data.variationQuadratic +
          normSq data.variationCubic) := by
  have linearBound :
      normSq (CCL.FiniteExp.scale parameter data.variationLinear) <=
        normSq data.variationLinear := by
    simpa only [pow_one] using
      (normSq_scale_pow_le parameter parameterNonnegative parameterUpper 1
        data.variationLinear)
  have quadraticBound :
      normSq (CCL.FiniteExp.scale (parameter ^ 2) data.variationQuadratic) <=
        normSq data.variationQuadratic :=
    normSq_scale_pow_le parameter parameterNonnegative parameterUpper 2
      data.variationQuadratic
  have cubicBound :
      normSq (CCL.FiniteExp.scale (parameter ^ 3) data.variationCubic) <=
        normSq data.variationCubic :=
    normSq_scale_pow_le parameter parameterNonnegative parameterUpper 3
      data.variationCubic
  have tailBound :
      normSq
          (CCL.FiniteExp.scale (parameter ^ 2) data.variationQuadratic +
            CCL.FiniteExp.scale (parameter ^ 3) data.variationCubic) <=
        2 * (normSq data.variationQuadratic +
          normSq data.variationCubic) :=
    (normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add quadraticBound cubicBound) (by decide))
  calc
    normSq
        (CCL.FiniteExp.scale parameter data.variationLinear +
          (CCL.FiniteExp.scale (parameter ^ 2) data.variationQuadratic +
            CCL.FiniteExp.scale (parameter ^ 3) data.variationCubic)) <=
      2 *
        (normSq (CCL.FiniteExp.scale parameter data.variationLinear) +
          normSq
            (CCL.FiniteExp.scale (parameter ^ 2) data.variationQuadratic +
              CCL.FiniteExp.scale (parameter ^ 3) data.variationCubic)) :=
      normSq_add_le_two _ _
    _ <= 2 *
        (normSq data.variationLinear +
          2 * (normSq data.variationQuadratic +
            normSq data.variationCubic)) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add linearBound tailBound) (by decide)
    _ = 2 * normSq data.variationLinear +
        4 * (normSq data.variationQuadratic +
          normSq data.variationCubic) := by ring1

/-- The exact cubic coefficient majorant emitted for a row bounds every
rational point of that cell, not merely its endpoints. -/
theorem radicand_variation_le (data : CompactCellData)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) :
    normSq (radicand (data.parameterValue parameter) -
      radicand data.startValue) <= data.radicandVariationSq.toCoordinate := by
  rw [radicand_parameter_sub_start]
  rw [radicandVariationSq_toCoordinate]
  exact parameterizedVariation_le data parameter parameterNonnegative
    parameterUpper

theorem radicand_parameter_nonzero
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) :
    radicand (data.parameterValue parameter) ≠ 0 := by
  intro zero
  have variation := data.radicand_variation_le parameter
    parameterNonnegative parameterUpper
  rw [zero, zero_sub, normSq_neg] at variation
  have separated := bounds.radicandSeparated
  rw [radicandAtNormSq_toCoordinate] at separated
  exact (not_lt_of_ge variation separated).elim

@[simp] theorem roucheLinearSq_toCoordinate (rootBits : Nat)
    (data : CompactCellData) :
    (data.roucheLinearSq rootBits).toCoordinate =
      4 * (normSq (data.rootCenterValue rootBits) * data.halfWidth ^ 2) := by
  unfold roucheLinearSq rootCenterValue
  rw [Dyadic.toCoordinate_scale, Dyadic.toCoordinate_mul,
    DyadicGaussian.normSq_toGaussian, halfWidthSq_toCoordinate]
  rfl

@[simp] theorem roucheRemainderSq_toCoordinate (rootBits : Nat)
    (data : CompactCellData) :
    (data.roucheRemainderSq rootBits).toCoordinate =
      3 * (normSq (data.rootCenterValue rootBits *
            data.rootCenterValue rootBits - radicand data.startValue) +
        (4 * data.halfWidth ^ 4 +
          data.radicandVariationSq.toCoordinate)) := by
  unfold roucheRemainderSq
  rw [Dyadic.toCoordinate_scale, Dyadic.toCoordinate_add,
    Dyadic.toCoordinate_add, Dyadic.toCoordinate_scale,
    halfWidthFourth_toCoordinate, rootResidualSq_toCoordinate]
  rfl

@[simp] theorem sourceRoucheRemainderSq_toCoordinate (rootBits : Nat)
    (data : CompactCellData) :
    (data.sourceRoucheRemainderSq rootBits).toCoordinate =
      3 * (normSq (data.rootCenterValue rootBits *
            data.rootCenterValue rootBits - radicand data.startValue) +
        4 * data.halfWidth ^ 4) := by
  unfold sourceRoucheRemainderSq
  rw [Dyadic.toCoordinate_scale, Dyadic.toCoordinate_add,
    Dyadic.toCoordinate_scale, halfWidthFourth_toCoordinate,
    rootResidualSq_toCoordinate]
  rfl

@[simp] theorem preparationClearanceFloor_toCoordinate :
    preparationClearanceFloor.toCoordinate =
      (1 / 2 : Coordinate) ^ 2 / (4 * 65536) := by
  unfold preparationClearanceFloor Dyadic.toCoordinate Dyadic.toFraction
  rw [RFAP.ConstructiveFraction.ofFraction_eq_div]
  change (1 : Coordinate) / (((2 : Int) ^ 20 : Int) : Coordinate) = _
  rw [show (((2 : Int) ^ 20 : Int) : Coordinate) = 1048576 by rfl]
  have denominatorPositive : (0 : Coordinate) < 1048576 :=
    RFAP.ConstructiveFraction.natCast_pos_direct (n := 1048576) (by decide)
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    denominatorPositive.ne'
  rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
    denominatorPositive.ne']
  calc
    (1 : Coordinate) = ((1 / 2 : Coordinate) ^ 2) * 4 := by decide
    _ = (((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) *
        (4 * 65536)) * 4 := by
      rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne]
      exact (RFAP.ConstructiveFraction.mul_ne_zero_direct
        (by decide)
        (RFAP.ConstructiveFraction.natCast_pos_direct
          (n := 65536) (by decide)).ne')
    _ = ((1 / 2 : Coordinate) ^ 2 / (4 * 65536)) * 1048576 := by
      ring1

@[simp] theorem sourceClearanceSq_toCoordinate (rootBits : Nat)
    (data : CompactCellData) :
    (data.sourceClearanceSq rootBits).toCoordinate =
      (data.roucheLinearSq rootBits).toCoordinate -
        (data.sourceRoucheRemainderSq rootBits).toCoordinate := by
  unfold sourceClearanceSq
  exact Dyadic.toCoordinate_sub _ _

theorem sourceRoucheRemainderSq_le_roucheRemainderSq
    (rootBits : Nat) (data : CompactCellData) :
    (data.sourceRoucheRemainderSq rootBits).toCoordinate <=
      (data.roucheRemainderSq rootBits).toCoordinate := by
  rw [sourceRoucheRemainderSq_toCoordinate,
    roucheRemainderSq_toCoordinate]
  apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
    (by decide)
  exact add_le_add le_rfl (le_add_of_nonneg_right (by
      rw [radicandVariationSq_toCoordinate]
      exact add_nonneg
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (normSq_nonneg _))
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (add_nonneg (normSq_nonneg _) (normSq_nonneg _)))))

theorem sourceRoucheRemainderSq_lt_linear
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    (data.sourceRoucheRemainderSq rootBits).toCoordinate <
      (data.roucheLinearSq rootBits).toCoordinate :=
  (sourceRoucheRemainderSq_le_roucheRemainderSq rootBits data).trans_lt
    bounds.rouche

abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial

def rootSlope (rootBits : Nat) (data : CompactCellData) : Gaussian :=
  CCL.FiniteExp.scale 2 (data.rootCenterValue rootBits)

def rootLinearPolynomial (rootBits : Nat)
    (data : CompactCellData) : GaussianPolynomial :=
  RFAP.AffineWinding.affineCoordinate (data.rootSlope rootBits)
    (data.rootCenterValue rootBits)

def rootTargetPolynomial (data : CompactCellData)
    (parameter : Coordinate) : GaussianPolynomial :=
  CCL.PowerMonodromy.polynomial (radicand (data.parameterValue parameter))
    CCL.Riemann.SquareRootSheets.degreeTwo

def rootPerturbation (rootBits : Nat) (data : CompactCellData)
    (parameter : Coordinate) : GaussianPolynomial :=
  data.rootTargetPolynomial parameter - data.rootLinearPolynomial rootBits

theorem rootPerturbation_eval (rootBits : Nat) (data : CompactCellData)
    (parameter : Coordinate) (value : Gaussian) :
    (data.rootPerturbation rootBits parameter).eval value =
      (value - data.rootCenterValue rootBits) *
          (value - data.rootCenterValue rootBits) +
        (data.rootCenterValue rootBits * data.rootCenterValue rootBits -
          radicand data.startValue) -
        (radicand (data.parameterValue parameter) -
          radicand data.startValue) := by
  unfold rootPerturbation rootTargetPolynomial rootLinearPolynomial rootSlope
  rw [RFAP.ComputablePolynomial.DensePolynomial.eval_sub,
    CCL.PowerMonodromy.polynomial_eval,
    CCL.Riemann.SquareRootSheets.degreeTwo_value, pow_two,
    RFAP.AffineWinding.affineCoordinate_eval]
  rw [scale_two]
  ring1

theorem normSq_mul_self_le_four {value : Gaussian} {radius : Coordinate}
    (bound : normSq value <= 2 * radius ^ 2) :
    normSq (value * value) <= 4 * radius ^ 4 := by
  rw [normSq_mul]
  have multiplied := RFAP.ConstructiveFraction.mul_le_mul_direct
    bound bound (normSq_nonneg value)
    (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
      (RFAP.ConstructiveFraction.sq_nonneg_direct radius))
  calc
    normSq value * normSq value <=
        (2 * radius ^ 2) * (2 * radius ^ 2) := multiplied
    _ = 4 * radius ^ 4 := by ring1

/-- Weighted two-term estimate used to retain a first-order root-box
clearance.  It is the sum of the two coordinate identities
`16 |u+r|² + 240 |r|² - 15 |u|² = |u+16r|²`. -/
theorem fifteen_normSq_le_sixteen_add (main residual : Gaussian) :
    15 * normSq main <=
      16 * normSq (main + residual) + 240 * normSq residual := by
  apply sub_nonneg.mp
  rw [show
    16 * normSq (main + residual) + 240 * normSq residual -
        15 * normSq main =
      (main.re + 16 * residual.re) ^ 2 +
        (main.im + 16 * residual.im) ^ 2 by
    simp only [normSq, add_re, add_im]
    ring1]
  exact add_nonneg
    (RFAP.ConstructiveFraction.sq_nonneg_direct _)
    (RFAP.ConstructiveFraction.sq_nonneg_direct _)

theorem rootPerturbation_threeTerm_upper (rootBits : Nat)
    (data : CompactCellData) (offset variation : Gaussian)
    (offsetSquareBound : normSq (offset * offset) <=
      4 * data.halfWidth ^ 4)
    (variationBound : normSq variation <=
      data.radicandVariationSq.toCoordinate) :
    normSq (offset * offset +
        ((data.rootCenterValue rootBits * data.rootCenterValue rootBits -
          radicand data.startValue) + -variation)) <=
      (data.roucheRemainderSq rootBits).toCoordinate := by
  let residual := data.rootCenterValue rootBits *
    data.rootCenterValue rootBits - radicand data.startValue
  have negVariationBound : normSq (-variation) <=
      data.radicandVariationSq.toCoordinate := by
    rw [normSq_neg]
    exact variationBound
  have termBound :
      normSq (offset * offset) + normSq residual + normSq (-variation) <=
        normSq residual +
          (4 * data.halfWidth ^ 4 +
            data.radicandVariationSq.toCoordinate) := by
    calc
      normSq (offset * offset) + normSq residual + normSq (-variation) <=
          4 * data.halfWidth ^ 4 + normSq residual +
            data.radicandVariationSq.toCoordinate :=
        add_le_add (add_le_add offsetSquareBound le_rfl) negVariationBound
      _ = normSq residual +
          (4 * data.halfWidth ^ 4 +
            data.radicandVariationSq.toCoordinate) := by ring1
  rw [roucheRemainderSq_toCoordinate]
  change normSq (offset * offset + (residual + -variation)) <=
    3 * (normSq residual +
      (4 * data.halfWidth ^ 4 + data.radicandVariationSq.toCoordinate))
  exact (normSq_add_add_le_three (offset * offset)
    residual (-variation)).trans
    (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
      termBound (by decide))

theorem rootOffsetSquare_boundary_upper (rootBits : Nat)
    (data : CompactCellData) (value : Gaussian)
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (data.rootBox rootBits) value) :
    normSq ((value - data.rootCenterValue rootBits) *
        (value - data.rootCenterValue rootBits)) <=
      4 * data.halfWidth ^ 4 := by
  apply normSq_mul_self_le_four
  exact RFAP.AffineWinding.centeredSquare_normSq_sub_center_le
    (data.rootCenterValue rootBits) data.halfWidth_positive.le boundary.1

theorem rootPerturbation_expanded_boundary_upper
    (rootBits : Nat) (data : CompactCellData)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (value : Gaussian)
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (data.rootBox rootBits) value) :
    normSq
        ((value - data.rootCenterValue rootBits) *
            (value - data.rootCenterValue rootBits) +
          ((data.rootCenterValue rootBits * data.rootCenterValue rootBits -
            radicand data.startValue) +
          -(radicand (data.parameterValue parameter) -
            radicand data.startValue))) <=
      (data.roucheRemainderSq rootBits).toCoordinate := by
  apply rootPerturbation_threeTerm_upper
  · exact rootOffsetSquare_boundary_upper rootBits data value boundary
  · exact data.radicand_variation_le parameter parameterNonnegative
      parameterUpper

theorem rootPerturbation_boundary_upper
    (rootBits : Nat) (data : CompactCellData)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (value : Gaussian)
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (data.rootBox rootBits) value) :
    normSq ((data.rootPerturbation rootBits parameter).eval value) <=
      (data.roucheRemainderSq rootBits).toCoordinate := by
  rw [rootPerturbation_eval]
  simpa only [sub_eq_add_neg, _root_.add_assoc] using
    (rootPerturbation_expanded_boundary_upper rootBits data parameter
      parameterNonnegative parameterUpper value boundary)

/-- At the row's source there is no path-parameter variation term.  Removing
that term exposes the stronger clearance needed to reuse a transport owner
on the actual prepared edge. -/
theorem rootPerturbation_source_boundary_upper
    (rootBits : Nat) (data : CompactCellData)
    (value : Gaussian)
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (data.rootBox rootBits) value) :
    normSq ((data.rootPerturbation rootBits 0).eval value) <=
      (data.sourceRoucheRemainderSq rootBits).toCoordinate := by
  let offset := value - data.rootCenterValue rootBits
  let residual := data.rootCenterValue rootBits *
    data.rootCenterValue rootBits - radicand data.startValue
  have offsetBound : normSq (offset * offset) <=
      4 * data.halfWidth ^ 4 := by
    exact rootOffsetSquare_boundary_upper rootBits data value boundary
  rw [rootPerturbation_eval, parameterValue_zero,
    sourceRoucheRemainderSq_toCoordinate]
  simp only [sub_self, sub_zero]
  change normSq (offset * offset + residual) <=
    3 * (normSq residual + 4 * data.halfWidth ^ 4)
  let total := normSq residual + 4 * data.halfWidth ^ 4
  have totalNonnegative : 0 <= total :=
    add_nonneg (normSq_nonneg _)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.pow_nonneg_direct
          data.halfWidth_positive.le 4))
  calc
    normSq (offset * offset + residual) <=
        2 * (normSq (offset * offset) + normSq residual) :=
      normSq_add_le_two _ _
    _ <= 2 * total := by
      apply RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct _
        (by decide)
      dsimp only [total]
      calc
        normSq (offset * offset) + normSq residual <=
            4 * data.halfWidth ^ 4 + normSq residual :=
          add_le_add offsetBound le_rfl
        _ = normSq residual + 4 * data.halfWidth ^ 4 := by ring1
    _ <= 3 * total :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (by decide) totalNonnegative

theorem intervalSquareLower_toCoordinate_le
    (lower upper : Dyadic) (value : Coordinate)
    (lowerBound : lower.toCoordinate <= value)
    (upperBound : value <= upper.toCoordinate) :
    (intervalSquareLower lower upper).toCoordinate <= value ^ 2 := by
  cases crosses : lower.le 0 && (0 : Dyadic).le upper with
  | true =>
      rw [intervalSquareLower, crosses, if_pos rfl]
      exact RFAP.ConstructiveFraction.sq_nonneg_direct value
  | false =>
      rw [intervalSquareLower, crosses, if_neg (by decide)]
      by_cases lowerNonnegative : (0 : Coordinate) <= lower.toCoordinate
      · exact (Dyadic.min_toCoordinate_le_left _ _).trans (by
          rw [Dyadic.square, Dyadic.toCoordinate_mul, pow_two]
          exact RFAP.ConstructiveFraction.mul_le_mul_direct lowerBound
            lowerBound lowerNonnegative (lowerNonnegative.trans lowerBound))
      · have lowerNonpositive : lower.toCoordinate <= 0 :=
          (lt_of_not_ge lowerNonnegative).le
        have upperNonpositive : upper.toCoordinate <= 0 := by
          by_cases upperNonpositive : upper.toCoordinate <= 0
          · exact upperNonpositive
          · have zeroLeUpper : (0 : Coordinate) <= upper.toCoordinate :=
              (lt_of_not_ge upperNonpositive).le
            have lowerChecked : lower.le 0 = true :=
              Dyadic.le_complete lowerNonpositive
            have upperChecked : (0 : Dyadic).le upper = true :=
              Dyadic.le_complete zeroLeUpper
            rw [lowerChecked, upperChecked] at crosses
            contradiction
        exact (Dyadic.min_toCoordinate_le_right _ _).trans (by
          rw [Dyadic.square, Dyadic.toCoordinate_mul, pow_two]
          have negated :=
            RFAP.ConstructiveFraction.neg_le_neg_direct upperBound
          have negUpperNonnegative : 0 <= -upper.toCoordinate :=
            neg_nonneg.mpr upperNonpositive
          have negValueNonnegative : 0 <= -value :=
            neg_nonneg.mpr (upperBound.trans upperNonpositive)
          have squares := RFAP.ConstructiveFraction.mul_le_mul_direct
            negated negated negUpperNonnegative negValueNonnegative
          simpa only [neg_mul_neg] using squares)

theorem intervalSquareLower_toCoordinate_nonneg (lower upper : Dyadic) :
    (intervalSquareLower lower upper).toCoordinate >= 0 := by
  unfold intervalSquareLower
  split
  · exact le_rfl
  · unfold Dyadic.min
    split
    · rw [Dyadic.square, Dyadic.toCoordinate_mul]
      simpa only [pow_two] using
        (RFAP.ConstructiveFraction.sq_nonneg_direct lower.toCoordinate)
    · rw [Dyadic.square, Dyadic.toCoordinate_mul]
      simpa only [pow_two] using
        (RFAP.ConstructiveFraction.sq_nonneg_direct upper.toCoordinate)

/-- The checked coordinatewise interval lower bound is valid throughout its
dyadic centred square. -/
theorem boxNormSqLower_le (center : DyadicGaussian) (halfWidthBits : Nat)
    {value : Gaussian}
    (inside : (RFAP.AffineWinding.centeredSquare center.toGaussian
      (Dyadic.mk 1 halfWidthBits).toCoordinate
        (CompactCellData.dyadicUnit_positive halfWidthBits).le).Contains value) :
    (boxNormSqLower center halfWidthBits).toCoordinate <= normSq value := by
  unfold boxNormSqLower
  rw [Dyadic.toCoordinate_add]
  unfold normSq
  apply add_le_add
  · apply intervalSquareLower_toCoordinate_le
    · rw [Dyadic.toCoordinate_sub]
      exact inside.1
    · rw [Dyadic.toCoordinate_add]
      exact inside.2.1
  · apply intervalSquareLower_toCoordinate_le
    · rw [Dyadic.toCoordinate_sub]
      exact inside.2.2.1
    · rw [Dyadic.toCoordinate_add]
      exact inside.2.2.2

/-- The row-specialized form of `boxNormSqLower_le`. -/
theorem rootNormSqLower_le (rootBits : Nat) (data : CompactCellData)
    {value : Gaussian} (inside : (data.rootBox rootBits).Contains value) :
    (data.rootNormSqLower rootBits).toCoordinate <= normSq value := by
  exact boxNormSqLower_le (data.rootCenter rootBits) data.halfWidthBits inside

theorem centeredSquare_add_center_contains (center value : Gaussian)
    (radius : Coordinate) (nonnegative : 0 <= radius)
    (inside : (RFAP.AffineWinding.centeredSquare center radius
      nonnegative).Contains value) :
    (RFAP.AffineWinding.centeredSquare (CCL.FiniteExp.scale 2 center)
      radius nonnegative).Contains (value + center) := by
  change
    2 * center.re - radius <= value.re + center.re ∧
      value.re + center.re <= 2 * center.re + radius ∧
      2 * center.im - radius <= value.im + center.im ∧
      value.im + center.im <= 2 * center.im + radius
  exact
    ⟨by
      calc
        2 * center.re - radius = (center.re - radius) + center.re := by ring1
        _ <= value.re + center.re :=
          RFAP.ConstructiveFraction.add_le_add_right_direct inside.1 _,
    by
      calc
        value.re + center.re <= (center.re + radius) + center.re :=
          RFAP.ConstructiveFraction.add_le_add_right_direct inside.2.1 _
        _ = 2 * center.re + radius := by ring1,
    by
      calc
        2 * center.im - radius = (center.im - radius) + center.im := by ring1
        _ <= value.im + center.im :=
          RFAP.ConstructiveFraction.add_le_add_right_direct inside.2.2.1 _,
    by
      calc
        value.im + center.im <= (center.im + radius) + center.im :=
          RFAP.ConstructiveFraction.add_le_add_right_direct inside.2.2.2 _
        _ = 2 * center.im + radius := by ring1⟩

/-- The checked coordinatewise lower bound for the second quadratic factor
is valid throughout the generated root square. -/
theorem rootSecondFactorNormSqLower_le (rootBits : Nat)
    (data : CompactCellData) {value : Gaussian}
    (inside : (data.rootBox rootBits).Contains value) :
    (data.rootSecondFactorNormSqLower rootBits).toCoordinate <=
      normSq (value + data.rootCenterValue rootBits) := by
  apply boxNormSqLower_le
  rw [DyadicGaussian.toGaussian_scale]
  exact centeredSquare_add_center_contains
    (data.rootCenterValue rootBits) value data.halfWidth
      data.halfWidth_positive.le inside

theorem rootSecondFactorNormSqLower_nonneg (rootBits : Nat)
    (data : CompactCellData) :
    0 <= (data.rootSecondFactorNormSqLower rootBits).toCoordinate := by
  unfold CompactCellData.rootSecondFactorNormSqLower boxNormSqLower
  rw [Dyadic.toCoordinate_add]
  exact add_nonneg
    (intervalSquareLower_toCoordinate_nonneg _ _)
    (intervalSquareLower_toCoordinate_nonneg _ _)

@[simp] theorem factorizedMainSq_toCoordinate (rootBits : Nat)
    (data : CompactCellData) :
    (data.factorizedMainSq rootBits).toCoordinate =
      data.halfWidth ^ 2 *
        (data.rootSecondFactorNormSqLower rootBits).toCoordinate := by
  unfold CompactCellData.factorizedMainSq Dyadic.square
  rw [Dyadic.toCoordinate_mul, Dyadic.toCoordinate_mul]
  unfold CompactCellData.halfWidth
  rw [pow_two]

@[simp] theorem factorizedClearanceNumerator_toCoordinate (rootBits : Nat)
    (data : CompactCellData) :
    (data.factorizedClearanceNumerator rootBits).toCoordinate =
      15 * (data.factorizedMainSq rootBits).toCoordinate -
        240 * (data.rootResidualSq rootBits).toCoordinate := by
  unfold CompactCellData.factorizedClearanceNumerator
  rw [Dyadic.toCoordinate_sub, Dyadic.toCoordinate_scale,
    Dyadic.toCoordinate_scale]
  rfl

theorem rootTargetPolynomial_zero_eval_factorized (rootBits : Nat)
    (data : CompactCellData) (value : Gaussian) :
    (data.rootTargetPolynomial 0).eval value =
      (value - data.rootCenterValue rootBits) *
          (value + data.rootCenterValue rootBits) +
        (data.rootCenterValue rootBits * data.rootCenterValue rootBits -
          radicand data.startValue) := by
  unfold rootTargetPolynomial
  rw [CCL.PowerMonodromy.polynomial_eval,
    CCL.Riemann.SquareRootSheets.degreeTwo_value,
    CompactCellData.parameterValue_zero]
  change value ^ 2 - radicand data.startValue = _
  rw [pow_two]
  ring1

theorem factorizedMain_boundary_lower (rootBits : Nat)
    (data : CompactCellData) (value : Gaussian)
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (data.rootBox rootBits) value) :
    (data.factorizedMainSq rootBits).toCoordinate <=
      normSq ((value - data.rootCenterValue rootBits) *
        (value + data.rootCenterValue rootBits)) := by
  rw [factorizedMainSq_toCoordinate, normSq_mul]
  let radial := RFAP.AffineWinding.translatedCoordinate_boundaryClearance
    (data.rootCenterValue rootBits) data.halfWidth_positive
  have firstLower : data.halfWidth ^ 2 <=
      normSq (value - data.rootCenterValue rootBits) := by
    have lower := radial.lower value boundary
    change data.halfWidth ^ 2 <=
      normSq ((RFAP.AffineWinding.translatedCoordinate
        (data.rootCenterValue rootBits)).eval value) at lower
    simpa only [RFAP.AffineWinding.translatedCoordinate_eval] using lower
  exact RFAP.ConstructiveFraction.mul_le_mul_direct firstLower
    (data.rootSecondFactorNormSqLower_le rootBits boundary.1)
    (data.rootSecondFactorNormSqLower_nonneg rootBits)
    (normSq_nonneg _)

/-- Direct boundary clearance for the source quadratic.  Factoring at the
cached approximate root avoids the extra Horner-majorant loss of the generic
Rouché-to-clearance conversion. -/
def rootFactorizedClearance
    (rootBits : Nat) (data : CompactCellData)
    (numeratorPositive :
      0 < (data.factorizedClearanceNumerator rootBits).toCoordinate) :
    RFAP.BoxClearance.BoundaryClearance
      (data.rootTargetPolynomial 0) (data.rootBox rootBits) where
  bound := (data.factorizedClearanceNumerator rootBits).toCoordinate / 16
  positive := RFAP.ConstructiveFraction.div_pos_direct numeratorPositive
    (by decide)
  lower := by
    intro value boundary
    let center := data.rootCenterValue rootBits
    let main := (value - center) * (value + center)
    let residual := center * center - radicand data.startValue
    have mainLower :
        (data.factorizedMainSq rootBits).toCoordinate <= normSq main := by
      exact data.factorizedMain_boundary_lower rootBits value boundary
    have scaledMain :
        15 * (data.factorizedMainSq rootBits).toCoordinate <=
          15 * normSq main :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct mainLower
        (by decide)
    have weighted : 15 * normSq main <=
        16 * normSq (main + residual) + 240 * normSq residual :=
      fifteen_normSq_le_sixteen_add main residual
    rw [factorizedClearanceNumerator_toCoordinate]
    apply (RFAP.ConstructiveFraction.div_le_iff_pos
      (show (0 : Coordinate) < 16 by decide)).2
    have combined := scaledMain.trans weighted
    calc
      (15 * (data.factorizedMainSq rootBits).toCoordinate -
          240 * (data.rootResidualSq rootBits).toCoordinate) <=
          (16 * normSq (main + residual) + 240 * normSq residual) -
            240 * normSq residual := by
        rw [rootResidualSq_toCoordinate]
        exact RFAP.ConstructiveFraction.sub_le_sub_right_direct combined _
      _ = normSq ((data.rootTargetPolynomial 0).eval value) * 16 := by
        rw [show main + residual =
            (data.rootTargetPolynomial 0).eval value by
          exact (data.rootTargetPolynomial_zero_eval_factorized rootBits
            value).symm]
        ring1

@[simp] theorem coefficientErrorClearedLeft_toCoordinate
    (rootBits allowanceBits : Nat) (data : CompactCellData) :
    (data.coefficientErrorClearedLeft rootBits allowanceBits).toCoordinate =
      (data.coefficientErrorSq allowanceBits).toCoordinate *
        (data.rootNormSqLower rootBits).toCoordinate *
          normSq (data.rootCenterValue rootBits) := by
  unfold coefficientErrorClearedLeft rootCenterValue
  rw [Dyadic.toCoordinate_mul, Dyadic.toCoordinate_mul,
    DyadicGaussian.normSq_toGaussian]

@[simp] theorem coefficientErrorClearedRight_toCoordinate
    (rootBits coefficientBits : Nat) (data : CompactCellData) :
    (data.coefficientErrorClearedRight rootBits coefficientBits).toCoordinate =
      2 *
        (normSq (data.coefficientValue coefficientBits *
            data.rootCenterValue rootBits - 1) *
          (data.rootNormSqLower rootBits).toCoordinate +
            2 * data.halfWidth ^ 2) := by
  unfold coefficientErrorClearedRight coefficientValue rootCenterValue
  rw [Dyadic.toCoordinate_scale, Dyadic.toCoordinate_add,
    Dyadic.toCoordinate_mul, twiceHalfWidthSq_toCoordinate,
    DyadicGaussian.normSq_toGaussian]
  change (2 : Coordinate) *
      (normSq (((data.coefficient coefficientBits).mul
        (data.rootCenter rootBits)).sub 1).toGaussian *
          (data.rootNormSqLower rootBits).toCoordinate +
        2 * data.halfWidth ^ 2) = _
  rw [DyadicGaussian.toGaussian_sub, DyadicGaussian.toGaussian_mul,
    dyadicGaussian_one_toGaussian]

theorem rootCenter_nonzero {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    data.rootCenterValue rootBits ≠ 0 := by
  intro zero
  have centerInside : (data.rootBox rootBits).Contains
      (data.rootCenterValue rootBits) := by
    unfold rootBox RFAP.AffineWinding.centeredSquare
    constructor
    · exact sub_le_self _ data.halfWidth_positive.le
    · constructor
      · exact le_add_of_nonneg_right data.halfWidth_positive.le
      · constructor
        · exact sub_le_self _ data.halfWidth_positive.le
        · exact le_add_of_nonneg_right data.halfWidth_positive.le
  have lower := data.rootNormSqLower_le rootBits centerInside
  rw [zero, normSq_zero] at lower
  exact (not_lt_of_ge lower bounds.rootNormSqLowerPositive).elim

theorem rootSlope_nonzero {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    data.rootSlope rootBits ≠ 0 := by
  intro zero
  have positive : 0 < normSq (data.rootSlope rootBits) := by
    rw [rootSlope, CCL.FiniteExp.normSq_scale]
    exact RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.pow_pos_direct (by decide) 2)
      (normSq_pos (data.rootCenter_nonzero bounds))
  rw [zero, normSq_zero] at positive
  exact (lt_irrefl _ positive).elim

theorem rootLinearBoundaryLower
    (rootBits : Nat) (data : CompactCellData)
    (value : Gaussian) (boundary : RFAP.BoxClearance.OnBoxBoundary
      (data.rootBox rootBits) value) :
    (data.roucheLinearSq rootBits).toCoordinate <=
      normSq ((data.rootLinearPolynomial rootBits).eval value) := by
  let center := data.rootCenterValue rootBits
  have radial :=
    (RFAP.AffineWinding.translatedCoordinate_boundaryClearance center
      data.halfWidth_positive).lower value boundary
  dsimp only [RFAP.AffineWinding.translatedCoordinate_boundaryClearance]
    at radial
  rw [RFAP.AffineWinding.translatedCoordinate_eval] at radial
  rw [rootLinearPolynomial, RFAP.AffineWinding.affineCoordinate_eval,
    normSq_mul, roucheLinearSq_toCoordinate, rootSlope,
    CCL.FiniteExp.normSq_scale]
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    radial
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct (2 : Coordinate))
      (normSq_nonneg center))
  exact (by
    dsimp only [center] at scaled ⊢
    convert scaled using 1
    all_goals ring1)

def rootLinearClearance
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    RFAP.BoxClearance.BoundaryClearance (data.rootLinearPolynomial rootBits)
      (data.rootBox rootBits) where
  bound := (data.roucheLinearSq rootBits).toCoordinate
  positive := by
    rw [roucheLinearSq_toCoordinate]
    exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.mul_pos_direct
        (normSq_pos (data.rootCenter_nonzero bounds))
        (RFAP.ConstructiveFraction.pow_pos_direct data.halfWidth_positive 2))
  lower := rootLinearBoundaryLower rootBits data

theorem rootTarget_eq_linear_add_perturbation (rootBits : Nat)
    (data : CompactCellData) (parameter : Coordinate) :
    data.rootTargetPolynomial parameter =
      data.rootLinearPolynomial rootBits +
        data.rootPerturbation rootBits parameter := by
  symm
  exact CCL.ProgressivePolynomialRoots.add_sub_left_eq_of_normalized _ _
    (CCL.PowerMonodromy.polynomial_normalized _ _)

def rootDominance
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (data.rootLinearPolynomial rootBits)
      (data.rootPerturbation rootBits parameter)
      (data.rootBox rootBits) where
  margin := (data.roucheLinearSq rootBits).toCoordinate -
    (data.roucheRemainderSq rootBits).toCoordinate
  positive := RFAP.ConstructiveFraction.sub_pos_direct bounds.rouche
  lower := by
    intro value boundary
    exact RFAP.ConstructiveFraction.sub_le_sub_direct
      (rootLinearBoundaryLower rootBits data value boundary)
      (data.rootPerturbation_boundary_upper rootBits parameter
        parameterNonnegative parameterUpper value boundary)

/-- Strong source-only dominance for the same winding-one square. -/
def rootSourceDominance
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (data.rootLinearPolynomial rootBits)
      (data.rootPerturbation rootBits 0)
      (data.rootBox rootBits) where
  margin := (data.roucheLinearSq rootBits).toCoordinate -
    (data.sourceRoucheRemainderSq rootBits).toCoordinate
  positive := RFAP.ConstructiveFraction.sub_pos_direct
    (data.sourceRoucheRemainderSq_lt_linear bounds)
  lower := by
    intro value boundary
    exact RFAP.ConstructiveFraction.sub_le_sub_direct
      (rootLinearBoundaryLower rootBits data value boundary)
      (data.rootPerturbation_source_boundary_upper rootBits value boundary)

/-- Boundary clearance at the left endpoint, before spending any margin on
motion across the row. -/
def rootSourceClearance
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    RFAP.BoxClearance.BoundaryClearance
      (data.rootTargetPolynomial 0) (data.rootBox rootBits) := by
  rw [data.rootTarget_eq_linear_add_perturbation rootBits 0]
  exact RFAP.WindingHomotopy.boundaryClearance_add_of_boundaryNormDominance
    (data.rootLinearPolynomial rootBits)
    (data.rootPerturbation rootBits 0) (data.rootBox rootBits)
    (data.rootBox_proper rootBits) (data.rootSourceDominance bounds)

def rootTargetClearance
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) :
    RFAP.BoxClearance.BoundaryClearance
      (data.rootTargetPolynomial parameter) (data.rootBox rootBits) := by
  rw [data.rootTarget_eq_linear_add_perturbation rootBits parameter]
  exact RFAP.WindingHomotopy.boundaryClearance_add_of_boundaryNormDominance
    (data.rootLinearPolynomial rootBits)
    (data.rootPerturbation rootBits parameter) (data.rootBox rootBits)
    (data.rootBox_proper rootBits)
    (data.rootDominance bounds parameter parameterNonnegative parameterUpper)

theorem rootLinearWindingFour
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    RFAP.Winding.quadrupledBoxWinding
      (data.rootLinearPolynomial rootBits) (data.rootBox rootBits) = 4 := by
  exact RFAP.AffineWinding.quadrupledBoxWinding_affineCoordinate_centeredSquare
    (data.rootSlope_nonzero bounds) (data.rootCenterValue rootBits)
    data.halfWidth_positive

theorem rootTargetWindingFour
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) :
    RFAP.Winding.quadrupledBoxWinding
      (data.rootTargetPolynomial parameter) (data.rootBox rootBits) = 4 := by
  rw [data.rootTarget_eq_linear_add_perturbation rootBits parameter]
  exact (RFAP.WindingHomotopy.quadrupledBoxWinding_add_of_boundaryNormDominance
    (data.rootLinearPolynomial rootBits)
    (data.rootPerturbation rootBits parameter) (data.rootBox rootBits)
    (data.rootBox_proper rootBits) (data.rootLinearClearance bounds)
    (data.rootDominance bounds parameter parameterNonnegative
      parameterUpper)).trans (data.rootLinearWindingFour bounds)

theorem rootSourceWindingFour
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    RFAP.Winding.quadrupledBoxWinding
      (data.rootTargetPolynomial 0) (data.rootBox rootBits) = 4 := by
  rw [data.rootTarget_eq_linear_add_perturbation rootBits 0]
  exact (RFAP.WindingHomotopy.quadrupledBoxWinding_add_of_boundaryNormDominance
    (data.rootLinearPolynomial rootBits)
    (data.rootPerturbation rootBits 0) (data.rootBox rootBits)
    (data.rootBox_proper rootBits) (data.rootLinearClearance bounds)
    (data.rootSourceDominance bounds)).trans
      (data.rootLinearWindingFour bounds)

def rootState
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) :
    RFAP.ShrinkingTrack.WindingOneState
      (data.rootTargetPolynomial parameter) (data.rootBox rootBits) := by
  let clearance := data.rootTargetClearance bounds parameter
    parameterNonnegative parameterUpper
  exact
    { box := data.rootBox rootBits
      refinesAmbient := RFAP.Boxes.Box.refines_refl _
      proper := data.rootBox_proper rootBits
      clearance := clearance
      rawWindingFour := data.rootTargetWindingFour bounds parameter
        parameterNonnegative parameterUpper
      ambientLeftClearance := RFAP.BoxClearance.leftOfBoundary clearance
      ambientRightClearance := RFAP.BoxClearance.rightOfBoundary clearance
      ambientBottomClearance := RFAP.BoxClearance.bottomOfBoundary clearance
      ambientTopClearance := RFAP.BoxClearance.topOfBoundary clearance }

/-- Winding-one state retaining the stronger source-only clearance. -/
def rootSourceState
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    RFAP.ShrinkingTrack.WindingOneState
      (data.rootTargetPolynomial 0) (data.rootBox rootBits) := by
  let clearance := data.rootSourceClearance bounds
  exact
    { box := data.rootBox rootBits
      refinesAmbient := RFAP.Boxes.Box.refines_refl _
      proper := data.rootBox_proper rootBits
      clearance := clearance
      rawWindingFour := data.rootSourceWindingFour bounds
      ambientLeftClearance := RFAP.BoxClearance.leftOfBoundary clearance
      ambientRightClearance := RFAP.BoxClearance.rightOfBoundary clearance
      ambientBottomClearance := RFAP.BoxClearance.bottomOfBoundary clearance
      ambientTopClearance := RFAP.BoxClearance.topOfBoundary clearance }

theorem TransportBounds.factorizedClearanceNumerator_positive
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (transport : data.TransportBounds rootBits coefficientBits allowanceBits) :
    0 < (data.transportView.factorizedClearanceNumerator rootBits).toCoordinate := by
  have floorPositive :
      0 < (preparationClearanceFloor.scale 16).toCoordinate := by
    rw [Dyadic.toCoordinate_scale, preparationClearanceFloor_toCoordinate]
    exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.div_pos_direct
        (RFAP.ConstructiveFraction.pow_pos_direct
          (RFAP.ConstructiveFraction.div_pos_direct (by decide) (by decide)) 2)
        (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
          (RFAP.ConstructiveFraction.natCast_pos_direct
            (n := 65536) (by decide))))
  exact floorPositive.trans_le transport.clearanceFloor

theorem TransportBounds.preparationClearanceFloor_le
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (transport : data.TransportBounds rootBits coefficientBits allowanceBits) :
    preparationClearanceFloor.toCoordinate <=
      (data.transportView.factorizedClearanceNumerator rootBits).toCoordinate /
        16 := by
  apply (RFAP.ConstructiveFraction.le_div_iff_pos
    (show (0 : Coordinate) < 16 by decide)).2
  rw [show preparationClearanceFloor.toCoordinate * 16 =
      (preparationClearanceFloor.scale 16).toCoordinate by
    rw [Dyadic.toCoordinate_scale]
    ring1]
  exact transport.clearanceFloor

/-- Source state with the sharper factorized quadratic clearance cached in
place of the generic Rouché side certificates. -/
def rootFactorizedSourceState
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (transport : data.TransportBounds rootBits coefficientBits allowanceBits) :
    RFAP.ShrinkingTrack.WindingOneState
      (data.transportView.rootTargetPolynomial 0)
      (data.transportRootBox rootBits) := by
  let clearance := data.transportView.rootFactorizedClearance rootBits
    transport.factorizedClearanceNumerator_positive
  exact
    { box := data.transportRootBox rootBits
      refinesAmbient := RFAP.Boxes.Box.refines_refl _
      proper := data.transportView.rootBox_proper rootBits
      clearance := clearance
      rawWindingFour :=
        data.transportView.rootSourceWindingFour transport.rootBounds
      ambientLeftClearance := RFAP.BoxClearance.leftOfBoundary clearance
      ambientRightClearance := RFAP.BoxClearance.rightOfBoundary clearance
      ambientBottomClearance := RFAP.BoxClearance.bottomOfBoundary clearance
      ambientTopClearance := RFAP.BoxClearance.topOfBoundary clearance }

/-- A checked generated row supplies a fully executable winding-one owner at
every rational parameter in its cell. -/
def rootOwner
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (radicand (data.parameterValue parameter)) := by
  exact CCL.Riemann.SquareRootContinuationChain.Owner.ofState
    (data.radicand_parameter_nonzero bounds parameter parameterNonnegative
      parameterUpper)
    (data.rootState bounds parameter parameterNonnegative parameterUpper)

/-- Source owner with the path-variation reserve still available. -/
def rootSourceOwner
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (radicand (data.parameterValue 0)) := by
  exact CCL.Riemann.SquareRootContinuationChain.Owner.ofState
    (data.radicand_parameter_nonzero bounds 0 (by decide) (by decide))
    (data.rootSourceState bounds)

/-- Wide source owner retaining the direct first-order factorized clearance. -/
def rootFactorizedSourceOwner
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (transport : data.TransportBounds rootBits coefficientBits allowanceBits) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (radicand (data.transportView.parameterValue 0)) := by
  exact CCL.Riemann.SquareRootContinuationChain.Owner.ofState
    (data.transportView.radicand_parameter_nonzero transport.rootBounds 0
      (by decide) (by decide))
    (data.rootFactorizedSourceState transport)

@[simp] theorem rootSourceOwner_initial_box
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    (data.rootSourceOwner bounds).track.initial.box =
      data.rootBox rootBits := rfl

@[simp] theorem rootFactorizedSourceOwner_initial_box
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (transport : data.TransportBounds rootBits coefficientBits allowanceBits) :
    (data.rootFactorizedSourceOwner transport).track.initial.box =
      data.transportRootBox rootBits := rfl

@[simp] theorem rootFactorizedSourceOwner_clearance_bound
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (transport : data.TransportBounds rootBits coefficientBits allowanceBits) :
    (data.rootFactorizedSourceOwner transport).track.initial.clearance.bound =
      (data.transportView.factorizedClearanceNumerator rootBits).toCoordinate /
        16 := by
  change
    (data.rootFactorizedSourceState transport).clearance.bound = _
  rfl

def startRootName
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :=
  let owner := data.rootOwner bounds 0 (by decide) (by decide)
  CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
    owner.parameterNonzero owner

def finishRootName
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :=
  let owner := data.rootOwner bounds 1 (by decide) (by decide)
  CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
    owner.parameterNonzero owner

@[simp] theorem rootOwner_initial_box
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) :
    (data.rootOwner bounds parameter parameterNonnegative
      parameterUpper).track.initial.box = data.rootBox rootBits := by
  rfl

/-- The checked cleared-denominator inequality bounds the emitted dyadic
coefficient against the reciprocal of every possible root in the square. -/
theorem coefficient_reciprocal_error_le
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    {value : Gaussian} (inside : (data.rootBox rootBits).Contains value) :
    normSq (data.coefficientValue coefficientBits - 1 / value) <=
      (data.coefficientErrorSq allowanceBits).toCoordinate := by
  let center := data.rootCenterValue rootBits
  let coefficient := data.coefficientValue coefficientBits
  let lower := (data.rootNormSqLower rootBits).toCoordinate
  let error := (data.coefficientErrorSq allowanceBits).toCoordinate
  let centerNorm := normSq center
  let productError := normSq (coefficient * center - 1)
  let radial := 2 * data.halfWidth ^ 2
  have lowerPositive : 0 < lower := bounds.rootNormSqLowerPositive
  have centerNonzero : center ≠ 0 := data.rootCenter_nonzero bounds
  have centerNormPositive : 0 < centerNorm := normSq_pos centerNonzero
  have valueLower : lower <= normSq value :=
    data.rootNormSqLower_le rootBits inside
  have valueNormPositive : 0 < normSq value :=
    lowerPositive.trans_le valueLower
  have valueNonzero : value ≠ 0 := by
    intro zero
    rw [zero, normSq_zero] at valueNormPositive
    exact (lt_irrefl _ valueNormPositive).elim
  have radialBound : normSq (value - center) <= radial := by
    exact RFAP.AffineWinding.centeredSquare_normSq_sub_center_le center
      data.halfWidth_positive.le inside
  have centerErrorIdentity :
      coefficient - 1 / center = (coefficient * center - 1) / center := by
    apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
      centerNonzero
    rw [RFAP.ExplicitField.div_mul_cancel _ centerNonzero]
    calc
      (coefficient - 1 / center) * center =
          coefficient * center - (1 / center) * center := by
        apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
          simp only [sub_re, sub_im, mul_re, mul_im] <;> ring1
      _ = coefficient * center - 1 := by
        rw [RFAP.ExplicitField.div_mul_cancel _ centerNonzero]
  have inverseDifferenceIdentity :
      1 / center - 1 / value = (value - center) / (center * value) :=
    by
      simpa only [_root_.one_mul] using
        (CCL.ArithmeticFiniteQuotientVariation.div_sub_div 1 1 center value
          centerNonzero valueNonzero)
  have centerErrorNorm :
      normSq (coefficient - 1 / center) = productError / centerNorm := by
    rw [centerErrorIdentity, normSq_div _ _ centerNonzero]
    rfl
  have inverseDifferenceNorm :
      normSq (1 / center - 1 / value) =
        normSq (value - center) / (centerNorm * normSq value) := by
    rw [inverseDifferenceIdentity,
      normSq_div _ _
        (RFAP.ConstructiveGaussian.Gaussian.mul_ne_zero_direct centerNonzero
          valueNonzero), normSq_mul]
    rfl
  have denominatorPositive : 0 < centerNorm * lower :=
    RFAP.ConstructiveFraction.mul_pos_direct centerNormPositive lowerPositive
  have denominatorOrder : centerNorm * lower <= centerNorm * normSq value :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct valueLower
      centerNormPositive.le
  have actualDenominatorPositive : 0 < centerNorm * normSq value :=
    RFAP.ConstructiveFraction.mul_pos_direct centerNormPositive
      valueNormPositive
  have inverseDifferenceBound :
      normSq (1 / center - 1 / value) <= radial / (centerNorm * lower) := by
    rw [inverseDifferenceNorm]
    exact (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      radialBound
        (RFAP.ConstructiveFraction.inv_pos_direct
          actualDenominatorPositive).le).trans
      (RFAP.ConstructiveFraction.div_le_div_of_nonneg_left_direct
        (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
          (RFAP.ConstructiveFraction.sq_nonneg_direct data.halfWidth))
        denominatorPositive denominatorOrder)
  have totalIdentity :
      coefficient - 1 / value =
        (coefficient - 1 / center) + (1 / center - 1 / value) := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im] <;> ring1
  have totalBound :
      normSq (coefficient - 1 / value) <=
        2 * (productError / centerNorm + radial / (centerNorm * lower)) := by
    rw [totalIdentity]
    exact (normSq_add_le_two _ _).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add centerErrorNorm.le inverseDifferenceBound) (by decide))
  have normalizedProduct :
      (2 * (productError / centerNorm + radial / (centerNorm * lower))) *
          (lower * centerNorm) =
        2 * (productError * lower + radial) := by
    calc
      (2 * (productError / centerNorm + radial / (centerNorm * lower))) *
          (lower * centerNorm) =
        2 * ((productError / centerNorm * centerNorm) * lower +
          (radial / (centerNorm * lower)) * (centerNorm * lower)) := by
            ring1
      _ = 2 * (productError * lower + radial) := by
        rw [RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
            centerNormPositive.ne',
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
            denominatorPositive.ne']
  have checked := bounds.coefficient
  rw [coefficientErrorClearedRight_toCoordinate,
    coefficientErrorClearedLeft_toCoordinate] at checked
  change 2 * (productError * lower + radial) <=
    error * lower * centerNorm at checked
  apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct
    (c := lower * centerNorm) _
    (RFAP.ConstructiveFraction.mul_pos_direct lowerPositive centerNormPositive)
  calc
    normSq (coefficient - 1 / value) * (lower * centerNorm) <=
        (2 * (productError / centerNorm +
          radial / (centerNorm * lower))) * (lower * centerNorm) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct totalBound
        (RFAP.ConstructiveFraction.mul_nonneg_direct lowerPositive.le
          centerNormPositive.le)
    _ = 2 * (productError * lower + radial) := normalizedProduct
    _ <= error * lower * centerNorm := checked
    _ = error * (lower * centerNorm) := by ring1

/-- Every emitted reciprocal allowance is genuinely positive.  This follows
from the already checked cleared inequality: its right-hand error expression
contains the strictly positive root-box radius term. -/
theorem coefficientError_positive
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    0 < (data.coefficientErrorSq allowanceBits).toCoordinate := by
  have centerNormPositive :
      0 < normSq (data.rootCenterValue rootBits) :=
    normSq_pos (data.rootCenter_nonzero bounds)
  have positiveFactors : 0 <
      (data.rootNormSqLower rootBits).toCoordinate *
        normSq (data.rootCenterValue rootBits) :=
    RFAP.ConstructiveFraction.mul_pos_direct
      bounds.rootNormSqLowerPositive centerNormPositive
  have clearedRightPositive : 0 <
      (data.coefficientErrorClearedRight rootBits coefficientBits).toCoordinate := by
    rw [coefficientErrorClearedRight_toCoordinate]
    apply RFAP.ConstructiveFraction.mul_pos_direct (by decide)
    exact add_pos_of_nonneg_of_pos
      (RFAP.ConstructiveFraction.mul_nonneg_direct (normSq_nonneg _)
        bounds.rootNormSqLowerPositive.le)
      (RFAP.ConstructiveFraction.mul_pos_direct (by decide)
        (RFAP.ConstructiveFraction.pow_pos_direct data.halfWidth_positive 2))
  have clearedLeftPositive : 0 <
      (data.coefficientErrorClearedLeft rootBits allowanceBits).toCoordinate :=
    clearedRightPositive.trans_le bounds.coefficient
  rw [coefficientErrorClearedLeft_toCoordinate] at clearedLeftPositive
  have reordered : 0 <
      ((data.rootNormSqLower rootBits).toCoordinate *
        normSq (data.rootCenterValue rootBits)) *
          (data.coefficientErrorSq allowanceBits).toCoordinate := by
    calc
      0 < (data.coefficientErrorSq allowanceBits).toCoordinate *
          (data.rootNormSqLower rootBits).toCoordinate *
            normSq (data.rootCenterValue rootBits) := clearedLeftPositive
      _ = ((data.rootNormSqLower rootBits).toCoordinate *
          normSq (data.rootCenterValue rootBits)) *
            (data.coefficientErrorSq allowanceBits).toCoordinate := by ring1
  exact RFAP.ConstructiveFraction.pos_of_mul_pos_right_direct reordered
    positiveFactors.le

/-- The generated winding-one owner interpreted as an algebraic value of the
explicit Legendre curve.  The sheet label is supplied separately; global
generated-link evidence is what certifies that these local labels describe
one continuous occurrence. -/
def algebraicSheetValue
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2) :
    CCL.Riemann.AlgebraicDifferentials.AlgebraicSheetValue
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      (data.parameterValue parameter) := by
  let owner := data.rootOwner bounds parameter parameterNonnegative
    parameterUpper
  let certificate := owner.certificate owner.parameterNonzero
  have square : CCL.OperationalEquivalence.NamedEquivalent
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        certificate.value certificate.value).name
      (CCL.ProgressiveTransducer.Named.exact
        (CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial.eval
          (data.parameterValue parameter))) := by
    simpa only [radicand_eq_baseCurve_eval] using certificate.square
  exact
    { value := certificate.value
      apart := certificate.apart
      sheet := sheet
      curveEquation := CCL.OperationalEquivalence.NamedEquivalent.trans square
        (CCL.OperationalEquivalence.NamedEquivalent.symm
          (CCL.ProjectiveRationalEvaluation.polynomialEval_exact
            CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve.polynomial
            (data.parameterValue parameter))) }

/-- Every candidate of the generated algebraic value remains in the literal
root box whose reciprocal error was checked by the external generator. -/
theorem algebraicSheetValue_candidate_in_rootBox
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2)
    (state : (algebraicSheetValue bounds parameter parameterNonnegative
      parameterUpper sheet).value.name.process.State)
    {candidate : Gaussian}
    (possible : (algebraicSheetValue bounds parameter parameterNonnegative
      parameterUpper sheet).value.name.process.Possible state candidate) :
    (data.rootBox rootBits).Contains candidate := by
  let owner := data.rootOwner bounds parameter parameterNonnegative
    parameterUpper
  have inside := owner.certificate_candidate_in_initial_box
    owner.parameterNonzero state possible
  simpa only [owner, rootOwner_initial_box] using inside

/-- The unique standard differential on the genus-one Legendre curve. -/
def legendreDifferential :
    CCL.Riemann.AlgebraicDifferentials.Differential 1 :=
  { index := 0 }

@[simp] theorem legendreDifferential_exponent :
    legendreDifferential.exponent = 0 := rfl

def liftedStart (data : CompactCellData) (sheet : Fin 2) :
    CCL.Riemann.LiftedPaths.LiftedPoint 2 :=
  { coordinate := data.startValue
    sheet := sheet }

def liftedFinish (data : CompactCellData) (sheet : Fin 2) :
    CCL.Riemann.LiftedPaths.LiftedPoint 2 :=
  { coordinate := data.finishValue
    sheet := sheet }

/-- A generated row does not cross a branch cut; its local sheet label is
therefore transported by the identity permutation. -/
def liftedCell (data : CompactCellData) (sheet : Fin 2) :
    CCL.Riemann.LiftedPaths.LiftedCell
      (liftedStart data sheet) (liftedFinish data sheet) :=
  { sheetTransport := CCL.FiniteMonodromy.FiniteBijection.identity 2
    finishSheet_eq := rfl }

/-- One generated dyadic coefficient as a constant finite integration cell.
The factor four leaves enough room for both the literal reciprocal error and
one freshly refined admitted quotient reading. -/
def literalCellModel
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    CCL.ProgressiveGaussianIntegration.CellModel :=
  { start := data.startValue
    finish := data.finishValue
    polynomial := CCL.FiniteGaussianPolynomial.constant
      (data.coefficientValue coefficientBits)
    localAllowance :=
      4 * (data.coefficientErrorSq allowanceBits).toCoordinate
    localAllowance_nonneg :=
      RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (coefficientError_positive bounds).le
    observations := [] }

@[simp] theorem literalCellModel_displacement
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    (literalCellModel bounds).displacement =
      data.displacementValue := rfl

@[simp] theorem literalCellModel_integralSample
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    (literalCellModel bounds).integralSample =
      data.displacementValue * data.coefficientValue coefficientBits := by
  unfold CCL.ProgressiveGaussianIntegration.CellModel.integralSample
  change data.displacementValue *
      CCL.FiniteGaussianPolynomial.definiteIntegral
        (CCL.FiniteGaussianPolynomial.constant
          (data.coefficientValue coefficientBits)) 0 1 = _
  rw [CCL.FiniteGaussianPolynomial.definiteIntegral_constant]
  rw [sub_zero, mul_one]

private theorem contribution_re_bits
    (coefficientBits : Nat) (data : CompactCellData) :
    (((data.finish.sub data.start).mul
      (data.coefficient coefficientBits)).re).bits =
        geometryBits + coefficientBits := by
  unfold finish start scaledPoint coefficient
  simp only [DyadicGaussian.mul, DyadicGaussian.sub, DyadicGaussian.add,
    DyadicGaussian.neg, Dyadic.sub, Dyadic.add, Dyadic.neg, Dyadic.mul,
    max_self]

private theorem contribution_im_bits
    (coefficientBits : Nat) (data : CompactCellData) :
    (((data.finish.sub data.start).mul
      (data.coefficient coefficientBits)).im).bits =
        geometryBits + coefficientBits := by
  unfold finish start scaledPoint coefficient
  simp only [DyadicGaussian.mul, DyadicGaussian.sub, DyadicGaussian.add,
    DyadicGaussian.neg, Dyadic.sub, Dyadic.add, Dyadic.neg, Dyadic.mul,
    max_self]

/-- The fixed-grid single-row total denotes exactly the integral sample of
the corresponding literal constant cell. -/
theorem totals_literalSample
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    (data.totals coefficientBits allowanceBits).literalSample coefficientBits =
      (literalCellModel bounds).integralSample := by
  rw [literalCellModel_integralSample bounds]
  let contribution := (data.finish.sub data.start).mul
    (data.coefficient coefficientBits)
  have reBits : contribution.re.bits = geometryBits + coefficientBits :=
    contribution_re_bits coefficientBits data
  have imBits : contribution.im.bits = geometryBits + coefficientBits :=
    contribution_im_bits coefficientBits data
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change (Dyadic.mk contribution.re.numerator
        (geometryBits + coefficientBits)).toCoordinate = _
    rw [Dyadic.toCoordinate_reconstruct contribution.re _ reBits]
    change contribution.toGaussian.re = _
    rw [DyadicGaussian.toGaussian_mul, DyadicGaussian.toGaussian_sub]
    rfl
  · change (Dyadic.mk contribution.im.numerator
        (geometryBits + coefficientBits)).toCoordinate = _
    rw [Dyadic.toCoordinate_reconstruct contribution.im _ imBits]
    change contribution.toGaussian.im = _
    rw [DyadicGaussian.toGaussian_mul, DyadicGaussian.toGaussian_sub]
    rfl

private theorem weightedAllowance_bits
    (allowanceBits : Nat) (data : CompactCellData) :
    ((((data.finish.sub data.start).normSq.mul
      (data.coefficientErrorSq allowanceBits)).scale 4).bits) =
        2 * geometryBits + allowanceBits := by
  unfold finish start scaledPoint coefficientErrorSq
  simp only [DyadicGaussian.normSq, DyadicGaussian.sub,
    DyadicGaussian.add, DyadicGaussian.neg, Dyadic.square,
    Dyadic.add, Dyadic.neg, Dyadic.mul, Dyadic.scale, max_self]
  omega

/-- The fixed-grid weighted allowance is exactly the semantic allowance of
the literal cell, including the factor four used by its uniform certificate. -/
theorem totals_weightedAllowanceValue
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    (data.totals coefficientBits allowanceBits).weightedAllowanceValue
        allowanceBits =
      (literalCellModel bounds).weightedAllowance := by
  let weighted := (((data.finish.sub data.start).normSq.mul
    (data.coefficientErrorSq allowanceBits)).scale 4)
  have bits : weighted.bits = 2 * geometryBits + allowanceBits :=
    weightedAllowance_bits allowanceBits data
  change (Dyadic.mk weighted.numerator
      (2 * geometryBits + allowanceBits)).toCoordinate = _
  rw [Dyadic.toCoordinate_reconstruct weighted _ bits]
  unfold weighted
  rw [Dyadic.toCoordinate_scale, Dyadic.toCoordinate_mul,
    DyadicGaussian.normSq_toGaussian, DyadicGaussian.toGaussian_sub]
  unfold CCL.ProgressiveGaussianIntegration.CellModel.weightedAllowance
  rw [literalCellModel_displacement bounds]
  change 4 * (normSq data.displacementValue *
      (data.coefficientErrorSq allowanceBits).toCoordinate) =
    normSq data.displacementValue *
      (4 * (data.coefficientErrorSq allowanceBits).toCoordinate)
  ring1

private theorem movementSq_bits (data : CompactCellData) :
    (data.finish.sub data.start).normSq.bits = 2 * geometryBits := by
  unfold finish start scaledPoint
  simp only [DyadicGaussian.normSq, DyadicGaussian.sub,
    DyadicGaussian.add, DyadicGaussian.neg, Dyadic.square,
    Dyadic.add, Dyadic.neg, Dyadic.mul, max_self]
  omega

/-- The cached movement-square numerator denotes the exact squared movement
of one generated row. -/
theorem totals_movementSqValue
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (_bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    (data.totals coefficientBits allowanceBits).movementSqValue =
      RFAP.ConstructiveGaussian.Gaussian.normSq data.displacementValue := by
  let movement := (data.finish.sub data.start).normSq
  have bits : movement.bits = 2 * geometryBits := movementSq_bits data
  change (Dyadic.mk movement.numerator
      (2 * geometryBits)).toCoordinate = _
  rw [Dyadic.toCoordinate_reconstruct movement _ bits]
  unfold movement
  rw [DyadicGaussian.normSq_toGaussian,
    DyadicGaussian.toGaussian_sub]
  rfl

private theorem transportWeightedError_bits
    (allowanceBits : Nat) (data : CompactCellData) :
    ((data.finish.sub data.start).normSq.mul
      (data.transportCoefficientErrorSq allowanceBits)).bits =
        2 * geometryBits + allowanceBits := by
  unfold finish start scaledPoint transportCoefficientErrorSq transportView
    coefficientErrorSq
  simp only [DyadicGaussian.normSq, DyadicGaussian.sub,
    DyadicGaussian.add, DyadicGaussian.neg, Dyadic.square,
    Dyadic.add, Dyadic.neg, Dyadic.mul, max_self]
  omega

/-- The second cached transport numerator is exactly movement squared times
the wider reciprocal enclosure error. -/
theorem totals_transportWeightedErrorValue
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (_bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    (data.totals coefficientBits allowanceBits
      ).transportWeightedErrorValue allowanceBits =
      RFAP.ConstructiveGaussian.Gaussian.normSq data.displacementValue *
        (data.transportCoefficientErrorSq allowanceBits).toCoordinate := by
  let weighted := (data.finish.sub data.start).normSq.mul
    (data.transportCoefficientErrorSq allowanceBits)
  have bits : weighted.bits = 2 * geometryBits + allowanceBits :=
    transportWeightedError_bits allowanceBits data
  change (Dyadic.mk weighted.numerator
      (2 * geometryBits + allowanceBits)).toCoordinate = _
  rw [Dyadic.toCoordinate_reconstruct weighted _ bits]
  unfold weighted
  rw [Dyadic.toCoordinate_mul, DyadicGaussian.normSq_toGaussian,
    DyadicGaussian.toGaussian_sub]
  rfl

theorem compactTotals_literalSample_add (coefficientBits : Nat)
    (left right : CompactTotals) :
    (left.add right).literalSample coefficientBits =
      left.literalSample coefficientBits +
        right.literalSample coefficientBits := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext
  · change (Dyadic.mk (left.sampleRe + right.sampleRe)
        (geometryBits + coefficientBits)).toCoordinate =
      (Dyadic.mk left.sampleRe
          (geometryBits + coefficientBits)).toCoordinate +
        (Dyadic.mk right.sampleRe
          (geometryBits + coefficientBits)).toCoordinate
    rw [← Dyadic.toCoordinate_add]
    congr 1
    unfold Dyadic.add
    simp only [max_self, Nat.sub_self, pow_zero, _root_.mul_one]
  · change (Dyadic.mk (left.sampleIm + right.sampleIm)
        (geometryBits + coefficientBits)).toCoordinate =
      (Dyadic.mk left.sampleIm
          (geometryBits + coefficientBits)).toCoordinate +
        (Dyadic.mk right.sampleIm
          (geometryBits + coefficientBits)).toCoordinate
    rw [← Dyadic.toCoordinate_add]
    congr 1
    unfold Dyadic.add
    simp only [max_self, Nat.sub_self, pow_zero, _root_.mul_one]

theorem compactTotals_weightedAllowanceValue_add (allowanceBits : Nat)
    (left right : CompactTotals) :
    (left.add right).weightedAllowanceValue allowanceBits =
      left.weightedAllowanceValue allowanceBits +
        right.weightedAllowanceValue allowanceBits := by
  change (Dyadic.mk (_ + _)
      (2 * geometryBits + allowanceBits)).toCoordinate =
    (Dyadic.mk left.weightedAllowance
        (2 * geometryBits + allowanceBits)).toCoordinate +
      (Dyadic.mk right.weightedAllowance
        (2 * geometryBits + allowanceBits)).toCoordinate
  rw [← Dyadic.toCoordinate_add]
  congr 1
  unfold Dyadic.add
  simp only [max_self, Nat.sub_self, pow_zero, _root_.mul_one]

theorem compactTotals_movementSqValue_add (left right : CompactTotals) :
    (left.add right).movementSqValue =
      left.movementSqValue + right.movementSqValue := by
  change (Dyadic.mk (left.movementSq + right.movementSq)
      (2 * geometryBits)).toCoordinate =
    (Dyadic.mk left.movementSq (2 * geometryBits)).toCoordinate +
      (Dyadic.mk right.movementSq (2 * geometryBits)).toCoordinate
  rw [← Dyadic.toCoordinate_add]
  congr 1
  unfold Dyadic.add
  simp only [max_self, Nat.sub_self, pow_zero, _root_.mul_one]

theorem compactTotals_transportWeightedErrorValue_add (allowanceBits : Nat)
    (left right : CompactTotals) :
    (left.add right).transportWeightedErrorValue allowanceBits =
      left.transportWeightedErrorValue allowanceBits +
        right.transportWeightedErrorValue allowanceBits := by
  change (Dyadic.mk (left.transportWeightedError +
        right.transportWeightedError)
      (2 * geometryBits + allowanceBits)).toCoordinate =
    (Dyadic.mk left.transportWeightedError
        (2 * geometryBits + allowanceBits)).toCoordinate +
      (Dyadic.mk right.transportWeightedError
        (2 * geometryBits + allowanceBits)).toCoordinate
  rw [← Dyadic.toCoordinate_add]
  congr 1
  unfold Dyadic.add
  simp only [max_self, Nat.sub_self, pow_zero, _root_.mul_one]

/-- The productive value of `dx/y` at one generated rational parameter. -/
def differentialCoefficient
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2) :=
  let sheetValue := algebraicSheetValue bounds parameter parameterNonnegative
    parameterUpper sheet
  CCL.Riemann.AlgebraicDifferentials.differentialValue
    legendreDifferential (data.parameterValue parameter)
      sheetValue.value sheetValue.apart

/-- One eighth of the checked reciprocal-error budget is reserved for the
fresh finite quotient reading. -/
def readingTarget
    {allowanceBits : Nat} (data : CompactCellData) : Coordinate :=
  (data.coefficientErrorSq allowanceBits).toCoordinate / 8

theorem readingTarget_positive
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits) :
    0 < readingTarget (allowanceBits := allowanceBits) data :=
  RFAP.ConstructiveFraction.div_pos_direct
    (coefficientError_positive bounds) (by decide)

def readingState
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2) :
    (differentialCoefficient bounds parameter parameterNonnegative
      parameterUpper sheet).name.process.State :=
  let coefficient := differentialCoefficient bounds parameter
    parameterNonnegative parameterUpper sheet
  coefficient.name.process.refine coefficient.name.state
    (readingTarget (allowanceBits := allowanceBits) data)
    (readingTarget_positive bounds)

def reading
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2) : Gaussian :=
  ((differentialCoefficient bounds parameter parameterNonnegative
    parameterUpper sheet).name.process.witness
      (readingState bounds parameter parameterNonnegative parameterUpper
        sheet)).val

theorem reading_possible
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2) :
    (differentialCoefficient bounds parameter parameterNonnegative
      parameterUpper sheet).name.process.Possible
        (readingState bounds parameter parameterNonnegative parameterUpper
          sheet)
        (reading bounds parameter parameterNonnegative parameterUpper sheet) :=
  ((differentialCoefficient bounds parameter parameterNonnegative
    parameterUpper sheet).name.process.witness
      (readingState bounds parameter parameterNonnegative parameterUpper
        sheet)).property

theorem reading_radius_lt
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2) :
    ((differentialCoefficient bounds parameter parameterNonnegative
      parameterUpper sheet).name.process.ball
        (readingState bounds parameter parameterNonnegative parameterUpper
          sheet)).radiusSq <
      readingTarget (allowanceBits := allowanceBits) data :=
  (differentialCoefficient bounds parameter parameterNonnegative
    parameterUpper sheet).name.process.accurate
      (differentialCoefficient bounds parameter parameterNonnegative
        parameterUpper sheet).name.state
      (readingTarget (allowanceBits := allowanceBits) data)
      (readingTarget_positive bounds)

/-- Every finite candidate of the generated differential coefficient is
close to the emitted dyadic coefficient.  The proof exposes its denominator
candidate and applies the checked uniform reciprocal bound on the literal
root box. -/
theorem differentialCoefficient_candidate_error_le
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2)
    (state : (differentialCoefficient bounds parameter parameterNonnegative
      parameterUpper sheet).name.process.State)
    {value : Gaussian}
    (possible : (differentialCoefficient bounds parameter parameterNonnegative
      parameterUpper sheet).name.process.Possible state value) :
    normSq (value - data.coefficientValue coefficientBits) <=
      (data.coefficientErrorSq allowanceBits).toCoordinate := by
  let sheetValue := algebraicSheetValue bounds parameter parameterNonnegative
    parameterUpper sheet
  rcases CCL.Riemann.AlgebraicDifferentials.differentialValue_possible_components
      legendreDifferential (data.parameterValue parameter)
        sheetValue.value sheetValue.apart state possible with
    ⟨denominator, denominatorPossible, value_eq⟩
  have denominatorInside :
      (data.rootBox rootBits).Contains denominator := by
    exact algebraicSheetValue_candidate_in_rootBox bounds parameter
      parameterNonnegative parameterUpper sheet state.2 denominatorPossible
  have reciprocalBound :=
    coefficient_reciprocal_error_le bounds denominatorInside
  have value_eq_reciprocal : value = 1 / denominator := by
    simpa only [legendreDifferential_exponent, pow_zero] using value_eq
  have errorIdentity :
      value - data.coefficientValue coefficientBits =
        -(data.coefficientValue coefficientBits - 1 / denominator) := by
    rw [value_eq_reciprocal]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, neg_re, neg_im] <;> ring1
  rw [errorIdentity, normSq_neg]
  exact reciprocalBound

/-- The canonical fresh quotient reading is close to the generated dyadic
coefficient. -/
theorem reading_error_le
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2) :
    normSq (reading bounds parameter parameterNonnegative parameterUpper
        sheet - data.coefficientValue coefficientBits) <=
      (data.coefficientErrorSq allowanceBits).toCoordinate :=
  differentialCoefficient_candidate_error_le bounds parameter
    parameterNonnegative parameterUpper sheet
      (readingState bounds parameter parameterNonnegative parameterUpper sheet)
      (reading_possible bounds parameter parameterNonnegative parameterUpper
        sheet)

/-- The literal coefficient together with a genuine refined quotient witness
forms the displayed diagnostic observation for the constant cell model. -/
def localObservation
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2) :
    CCL.ProgressiveGaussianIntegration.LocalObservation
      (literalCellModel bounds).polynomial
      (literalCellModel bounds).localAllowance :=
  { parameter := parameter
    integrandReading := reading bounds parameter parameterNonnegative
      parameterUpper sheet
    error := reading bounds parameter parameterNonnegative parameterUpper
      sheet - data.coefficientValue coefficientBits
    decomposition := by
      change reading bounds parameter parameterNonnegative parameterUpper
          sheet - CCL.FiniteGaussianPolynomial.eval
            (CCL.FiniteGaussianPolynomial.constant
              (data.coefficientValue coefficientBits)) ⟨parameter, 0⟩ = _
      rw [CCL.FiniteGaussianPolynomial.eval_constant]
    error_le := by
      have errorBound := reading_error_le bounds parameter
        parameterNonnegative parameterUpper sheet
      exact errorBound.trans (calc
        (data.coefficientErrorSq allowanceBits).toCoordinate =
            1 * (data.coefficientErrorSq allowanceBits).toCoordinate := by ring1
        _ <= 4 * (data.coefficientErrorSq allowanceBits).toCoordinate :=
          RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
            (by decide) (coefficientError_positive bounds).le) }

/-- Productive pointwise semantics for the generated constant model.  Each
query constructs a fresh algebraic root owner and a sufficiently accurate
finite quotient reading at the exact requested rational parameter. -/
def uniformObservation
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (parameter : Coordinate) (parameterNonnegative : 0 <= parameter)
    (parameterUpper : parameter <= 1) (sheet : Fin 2) :
    CCL.Riemann.AlgebraicDifferentials.UniformObservation
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      legendreDifferential (liftedCell data sheet)
      (literalCellModel bounds) parameter := by
  let sheetValue := algebraicSheetValue bounds parameter parameterNonnegative
    parameterUpper sheet
  let observation := localObservation bounds parameter parameterNonnegative
    parameterUpper sheet
  let state := readingState bounds parameter parameterNonnegative
    parameterUpper sheet
  let value := reading bounds parameter parameterNonnegative parameterUpper
    sheet
  let algebraic : CCL.Riemann.AlgebraicDifferentials.AlgebraicObservation
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      legendreDifferential (liftedCell data sheet)
      (literalCellModel bounds) observation :=
    { point := data.parameterValue parameter
      point_eq := by
        rfl
      sheetValue := sheetValue
      chosenSheet_eq := rfl
      readingState := state
      readingPossible := reading_possible bounds parameter
        parameterNonnegative parameterUpper sheet }
  exact
    { observation := observation
      parameter_eq := rfl
      algebraic := algebraic
      semantic_error_le := by
        let error := (data.coefficientErrorSq allowanceBits).toCoordinate
        let ball := (differentialCoefficient bounds parameter
          parameterNonnegative parameterUpper sheet).name.process.ball state
        have radiusBound : ball.radiusSq <= error / 8 :=
          (reading_radius_lt bounds parameter parameterNonnegative
            parameterUpper sheet).le
        have errorBound :
            normSq (value - data.coefficientValue coefficientBits) <= error :=
          reading_error_le bounds parameter parameterNonnegative
            parameterUpper sheet
        have targetCancellation : (error / 8) * 8 = error :=
          RFAP.ConstructiveFraction.div_mul_cancel_of_ne error 8 (by decide)
        change 2 * (4 * ball.radiusSq +
            normSq (value - data.coefficientValue coefficientBits)) <=
          4 * error
        calc
          2 * (4 * ball.radiusSq +
              normSq (value - data.coefficientValue coefficientBits)) <=
              2 * (4 * (error / 8) + error) :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
              (add_le_add
                (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
                  radiusBound (by decide)) errorBound) (by decide)
          _ = (error / 8) * 8 + 2 * error := by ring1
          _ = error + 2 * error := by rw [targetCancellation]
          _ = 3 * error := by ring1
          _ <= 4 * error :=
            RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
              (by decide) (coefficientError_positive bounds).le }

/-- Every checked generated row is therefore a genuine uniform algebraic
integration cell, rather than merely a table of plausible coefficients. -/
def uniformCellCertificate
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (sheet : Fin 2) :
    CCL.Riemann.AlgebraicDifferentials.UniformCellCertificate
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      legendreDifferential (liftedCell data sheet)
      (literalCellModel bounds) where
  query parameter parameterNonnegative parameterUpper :=
    uniformObservation bounds parameter parameterNonnegative parameterUpper
      sheet

def validCellCertificate
    {rootBits coefficientBits allowanceBits : Nat}
    {data : CompactCellData}
    (bounds : data.Bounds rootBits coefficientBits allowanceBits)
    (sheet : Fin 2) :
    CCL.Riemann.AlgebraicDifferentials.ValidCellCertificate
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      legendreDifferential (liftedCell data sheet)
      (literalCellModel bounds) :=
  .uniform (uniformCellCertificate bounds sheet)

end CompactCellData

namespace CompactCheckedCell

def literalModel
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : CompactCheckedCell rootBits coefficientBits allowanceBits) :=
  CompactCellData.literalCellModel cell.bounds

def uniformCertificate
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : CompactCheckedCell rootBits coefficientBits allowanceBits)
    (sheet : Fin 2) :=
  CompactCellData.uniformCellCertificate cell.bounds sheet

def validCertificate
    {rootBits coefficientBits allowanceBits : Nat}
    (cell : CompactCheckedCell rootBits coefficientBits allowanceBits)
    (sheet : Fin 2) :=
  CompactCellData.validCellCertificate cell.bounds sheet

end CompactCheckedCell

open CompactCellData

private theorem foldl_checked_literalSample
    {rootBits coefficientBits allowanceBits : Nat} :
    forall (entries : List
        (CompactCheckedCell rootBits coefficientBits allowanceBits))
      (initial : CompactTotals),
      ((entries.map CompactCheckedCell.data).foldl
          (fun total data => total.add
            (data.totals coefficientBits allowanceBits)) initial).literalSample
            coefficientBits =
        initial.literalSample coefficientBits +
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (entries.map CompactCheckedCell.literalModel)).integralSample
  | [], initial => by
      unfold CCL.ProgressiveGaussianIntegration.PathModel.integralSample
      simp only [List.map_nil, List.foldl_nil, List.foldr_nil]
      exact (RFAP.ConstructiveGaussian.Gaussian.add_zero _).symm
  | cell :: remaining, initial => by
      simp only [List.map_cons, List.foldl_cons]
      rw [foldl_checked_literalSample remaining
        (initial.add (cell.data.totals coefficientBits allowanceBits))]
      rw [CompactCellData.compactTotals_literalSample_add,
        CompactCellData.totals_literalSample cell.bounds]
      unfold CCL.ProgressiveGaussianIntegration.PathModel.integralSample
      simp only [List.foldr_cons, CompactCheckedCell.literalModel]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [RFAP.ConstructiveGaussian.Gaussian.add_re,
          RFAP.ConstructiveGaussian.Gaussian.add_im] <;> ring1

/-- A checked row list's compact sample is exactly the integral sample of
its assembled literal cell models. -/
theorem compactTotals_literalModels_integralSample
    {rootBits coefficientBits allowanceBits : Nat}
    (entries : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)) :
    (compactTotals coefficientBits allowanceBits
        (entries.map CompactCheckedCell.data)).literalSample coefficientBits =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (entries.map CompactCheckedCell.literalModel)).integralSample := by
  unfold compactTotals
  rw [foldl_checked_literalSample entries CompactTotals.zero]
  have zeroSample : (DyadicGaussian.mk
      (Dyadic.mk 0 (CompactCellData.geometryBits + coefficientBits))
      (Dyadic.mk 0
        (CompactCellData.geometryBits + coefficientBits))).toGaussian = 0 := by
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      exact Dyadic.toCoordinate_zero_numerator _
  change (DyadicGaussian.mk
      (Dyadic.mk 0 (CompactCellData.geometryBits + coefficientBits))
      (Dyadic.mk 0
        (CompactCellData.geometryBits + coefficientBits))).toGaussian + _ = _
  rw [zeroSample]
  exact RFAP.ConstructiveGaussian.Gaussian.zero_add _

private theorem foldl_checked_weightedAllowance
    {rootBits coefficientBits allowanceBits : Nat} :
    forall (entries : List
        (CompactCheckedCell rootBits coefficientBits allowanceBits))
      (initial : CompactTotals),
      CompactTotals.weightedAllowanceValue allowanceBits
        ((entries.map CompactCheckedCell.data).foldl
          (fun total data => total.add
            (data.totals coefficientBits allowanceBits)) initial) =
        initial.weightedAllowanceValue allowanceBits +
          (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (entries.map CompactCheckedCell.literalModel)).totalWeightedAllowance
  | [], initial => by
      unfold CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
      simp only [List.map_nil, List.foldl_nil, List.foldr_nil]
      exact (_root_.add_zero _).symm
  | cell :: remaining, initial => by
      simp only [List.map_cons, List.foldl_cons]
      rw [foldl_checked_weightedAllowance remaining
        (initial.add (cell.data.totals coefficientBits allowanceBits))]
      rw [CompactCellData.compactTotals_weightedAllowanceValue_add,
        CompactCellData.totals_weightedAllowanceValue cell.bounds]
      unfold CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
      simp only [List.foldr_cons, CompactCheckedCell.literalModel]
      ring1

theorem compactTotals_literalModels_totalWeightedAllowance
    {rootBits coefficientBits allowanceBits : Nat}
    (entries : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)) :
    (compactTotals coefficientBits allowanceBits
        (entries.map CompactCheckedCell.data)).weightedAllowanceValue
          allowanceBits =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (entries.map CompactCheckedCell.literalModel)).totalWeightedAllowance := by
  unfold compactTotals
  rw [foldl_checked_weightedAllowance entries CompactTotals.zero]
  change (Dyadic.mk 0
      (2 * CompactCellData.geometryBits + allowanceBits)).toCoordinate + _ = _
  rw [Dyadic.toCoordinate_zero_numerator,
    RFAP.ConstructiveFraction.zero_add]

private theorem foldl_compactTotals_count
    (coefficientBits allowanceBits : Nat) :
    forall (entries : List CompactCellData) (initial : CompactTotals),
      (entries.foldl
        (fun total data => total.add
          (data.totals coefficientBits allowanceBits)) initial).count =
        initial.count + entries.length
  | [], initial => by simp only [List.foldl_nil, List.length_nil, Nat.add_zero]
  | data :: remaining, initial => by
      simp only [List.foldl_cons, List.length_cons]
      rw [foldl_compactTotals_count coefficientBits allowanceBits remaining
        (initial.add (data.totals coefficientBits allowanceBits))]
      change (initial.count + 1) + remaining.length =
        initial.count + (remaining.length + 1)
      omega

theorem compactTotals_count (coefficientBits allowanceBits : Nat)
    (entries : List CompactCellData) :
    (compactTotals coefficientBits allowanceBits entries).count =
      entries.length := by
  unfold compactTotals
  rw [foldl_compactTotals_count coefficientBits allowanceBits entries
    CompactTotals.zero]
  exact Nat.zero_add entries.length

theorem CompactTotals.aggregateAllowance_eq_count_mul
    (allowanceBits : Nat) (totals : CompactTotals) :
    totals.aggregateAllowance allowanceBits =
      (totals.count : Coordinate) *
        totals.weightedAllowanceValue allowanceBits := by
  unfold CompactTotals.aggregateAllowance CompactTotals.weightedAllowanceValue
  change ((Dyadic.mk totals.weightedAllowance
      (2 * CompactCellData.geometryBits + allowanceBits)).scale
        (Int.ofNat totals.count)).toCoordinate = _
  rw [Dyadic.toCoordinate_scale]
  change (((totals.count : Int) : Coordinate) * _ =
    (totals.count : Coordinate) * _)
  rw [Int.cast_natCast]

theorem compactTotals_literalModels_aggregateAllowance
    {rootBits coefficientBits allowanceBits : Nat}
    (entries : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)) :
    (compactTotals coefficientBits allowanceBits
        (entries.map CompactCheckedCell.data)).aggregateAllowance
          allowanceBits =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk
        (entries.map CompactCheckedCell.literalModel)).aggregateAllowance := by
  rw [CompactTotals.aggregateAllowance_eq_count_mul]
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  change ((compactTotals coefficientBits allowanceBits
      (entries.map CompactCheckedCell.data)).count : Coordinate) * _ =
    ((entries.map CompactCheckedCell.literalModel).length : Coordinate) * _
  rw [compactTotals_count]
  simp only [List.length_map]
  rw [compactTotals_literalModels_totalWeightedAllowance]

/-- Consecutive checked rows carry a winding-one bridge at every internal
boundary.  This proposition forgets positions but retains exactly the
semantic evidence needed to assemble their lifted cells. -/
def CompactCheckedSequence
    {rootBits coefficientBits allowanceBits : Nat} :
    List (CompactCheckedCell rootBits coefficientBits allowanceBits) -> Prop
  | [] => True
  | [_] => True
  | left :: right :: remaining =>
      CompactCellData.BridgeBounds rootBits left.data right.data ∧
        CompactCheckedSequence (right :: remaining)

/-- Convert the shard checker's data-only sequence evidence back to the
corresponding list of individually checked cells. -/
theorem compactCheckedSequence_of_sequenceBounds
    {rootBits coefficientBits allowanceBits : Nat} :
    (entries : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)) ->
    (expected : Nat) ->
    CompactSequenceBounds rootBits expected none
      (entries.map CompactCheckedCell.data) ->
    CompactCheckedSequence entries
  | [], _expected, _bounds => True.intro
  | [_cell], _expected, _bounds => True.intro
  | left :: right :: remaining, expected, bounds => by
      change left.data.position = expected ∧ True ∧
        CompactSequenceBounds rootBits (expected + 1) (some left.data)
          (right.data :: remaining.map CompactCheckedCell.data) at bounds
      change CompactCellData.BridgeBounds rootBits left.data right.data ∧
        CompactCheckedSequence (right :: remaining)
      have rightBounds := bounds.2.2
      change right.data.position = expected + 1 ∧
        CompactCellData.BridgeBounds rootBits left.data right.data ∧
          CompactSequenceBounds rootBits (expected + 1 + 1)
            (some right.data)
            (remaining.map CompactCheckedCell.data) at rightBounds
      refine ⟨rightBounds.2.1, ?_⟩
      apply compactCheckedSequence_of_sequenceBounds
        (right :: remaining) (expected + 1)
      change right.data.position = expected + 1 ∧ True ∧
        CompactSequenceBounds rootBits (expected + 1 + 1)
          (some right.data) (remaining.map CompactCheckedCell.data)
      exact ⟨rightBounds.1, True.intro, rightBounds.2.2⟩

theorem CompactCheckedShard.checkedSequence
    {rootBits coefficientBits allowanceBits offset : Nat}
    (shard : CompactCheckedShard rootBits coefficientBits allowanceBits
      offset) :
    CompactCheckedSequence shard.checkedCells :=
  compactCheckedSequence_of_sequenceBounds shard.checkedCells offset
    shard.sequenceBounds

theorem liftedEndpoint_eq
    {rootBits : Nat} {left right : CompactCellData}
    (bridge : CompactCellData.BridgeBounds rootBits left right)
    (sheet : Fin 2) :
    liftedStart right sheet = liftedFinish left sheet := by
  exact congrArg
    (fun coordinate : Gaussian =>
      ({ coordinate := coordinate, sheet := sheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2))
    bridge.endpoint.symm

/-- A nonempty generated sequence assembled into one finite lifted path.
The type retains each inter-row winding-one bridge, while its projections
materialize the integration models and their uniform algebraic certificates. -/
inductive CompactLiteralPath
    {rootBits coefficientBits allowanceBits : Nat} (sheet : Fin 2) :
    List (CompactCheckedCell rootBits coefficientBits allowanceBits) ->
      CCL.Riemann.LiftedPaths.LiftedPoint 2 ->
      CCL.Riemann.LiftedPaths.LiftedPoint 2 -> Type 2
  | single (cell : CompactCheckedCell rootBits coefficientBits allowanceBits) :
      CompactLiteralPath sheet [cell]
        (liftedStart cell.data sheet) (liftedFinish cell.data sheet)
  | cons (left right :
        CompactCheckedCell rootBits coefficientBits allowanceBits)
      (remaining : List
        (CompactCheckedCell rootBits coefficientBits allowanceBits))
      {finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
      (bridge : CompactCellData.BridgeBounds rootBits left.data right.data)
      (tail : CompactLiteralPath sheet (right :: remaining)
        (liftedStart right.data sheet) finish) :
      CompactLiteralPath sheet (left :: right :: remaining)
        (liftedStart left.data sheet) finish

namespace CompactLiteralPath

def castStart
    {rootBits coefficientBits allowanceBits : Nat} {sheet : Fin 2}
    {cells : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)}
    {left right finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (equal : left = right)
    (path : CompactLiteralPath sheet cells left finish) :
    CompactLiteralPath sheet cells right finish := by
  subst right
  exact path

def castFinish
    {rootBits coefficientBits allowanceBits : Nat} {sheet : Fin 2}
    {cells : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)}
    {start left right : CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (equal : left = right)
    (path : CompactLiteralPath sheet cells start left) :
    CompactLiteralPath sheet cells start right := by
  subst right
  exact path

def ofSequence
    {rootBits coefficientBits allowanceBits : Nat} (sheet : Fin 2) :
    (cell : CompactCheckedCell rootBits coefficientBits allowanceBits) ->
    (remaining : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)) ->
    CompactCheckedSequence (cell :: remaining) ->
    CompactLiteralPath sheet (cell :: remaining)
      (liftedStart cell.data sheet)
      (liftedFinish
        ((cell :: remaining).getLast
          (by exact List.cons_ne_nil cell remaining)).data
        sheet)
  | cell, [], _sequence =>
      .single cell
  | cell, right :: remaining, sequence => by
      change CompactCellData.BridgeBounds rootBits cell.data right.data ∧
        CompactCheckedSequence (right :: remaining) at sequence
      exact .cons cell right remaining sequence.1
        (ofSequence sheet right remaining sequence.2)

def models
    {rootBits coefficientBits allowanceBits : Nat} {sheet : Fin 2} :
    {cells : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)} ->
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2} ->
    CompactLiteralPath sheet cells start finish ->
      List CCL.ProgressiveGaussianIntegration.CellModel
  | _, _, _, .single cell => [cell.literalModel]
  | _, _, _, .cons left _right _remaining _bridge tail =>
      left.literalModel :: tail.models

@[simp] theorem models_eq_map
    {rootBits coefficientBits allowanceBits : Nat} {sheet : Fin 2} :
    {cells : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)} ->
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2} ->
    (path : CompactLiteralPath sheet cells start finish) ->
    path.models = cells.map CompactCheckedCell.literalModel
  | _, _, _, .single _cell => rfl
  | _, _, _, .cons _left _right _remaining _bridge tail => by
      simp only [models, List.map_cons]
      rw [tail.models_eq_map]
      simp only [List.map_cons]

def liftedPath
    {rootBits coefficientBits allowanceBits : Nat} {sheet : Fin 2} :
    {cells : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)} ->
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2} ->
    (path : CompactLiteralPath sheet cells start finish) ->
      CCL.Riemann.LiftedPaths.LiftedPath 2 start finish
  | _, _, _, .single cell =>
      .cons (CompactCellData.liftedCell cell.data sheet) (.nil _)
  | _, _, _, .cons left _right _remaining bridge tail =>
      .cons (CompactCellData.liftedCell left.data sheet)
        (tail.liftedPath.castStart (liftedEndpoint_eq bridge sheet))

def certificates
    {rootBits coefficientBits allowanceBits : Nat} {sheet : Fin 2} :
    {cells : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)} ->
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2} ->
    (path : CompactLiteralPath sheet cells start finish) ->
      CCL.Riemann.AlgebraicDifferentials.UniformPathCertificates
        CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
        CompactCellData.legendreDifferential path.models path.liftedPath
  | _, _, _, .single cell =>
      .cons rfl rfl (cell.validCertificate sheet) (.nil _)
  | _, _, _, .cons left _right _remaining bridge tail =>
      .cons rfl rfl (left.validCertificate sheet)
        (tail.certificates.castStart (liftedEndpoint_eq bridge sheet))

end CompactLiteralPath

def CompactCheckedShard.literalPath
    {rootBits coefficientBits allowanceBits offset : Nat}
    (shard : CompactCheckedShard rootBits coefficientBits allowanceBits
      offset) (sheet : Fin 2) :
    CompactLiteralPath sheet shard.checkedCells
      (liftedStart shard.first sheet) (liftedFinish shard.last sheet) := by
  cases entries_eq : shard.checkedCells with
  | nil => exact (shard.nonempty entries_eq).elim
  | cons cell remaining =>
      have sequence : CompactCheckedSequence (cell :: remaining) := by
        rw [← entries_eq]
        exact shard.checkedSequence
      let path := CompactLiteralPath.ofSequence sheet cell remaining sequence
      have firstData : cell.data = shard.first := by
        have checked := shard.firstChecked
        simp only [entries_eq, List.head_cons] at checked
        exact checked
      have lastData :
          ((cell :: remaining).getLast
            (by exact List.cons_ne_nil cell remaining)).data = shard.last := by
        change ((cell :: remaining).getLast
            (by exact List.cons_ne_nil cell remaining)).data = shard.lastCell
        have checked := shard.lastChecked
        simpa only [entries_eq] using checked
      have start_eq : liftedStart cell.data sheet =
          liftedStart shard.first sheet := congrArg
        (fun data : CompactCellData => liftedStart data sheet) firstData
      have finish_eq :
          liftedFinish
              ((cell :: remaining).getLast
                (by exact List.cons_ne_nil cell remaining)).data sheet =
            liftedFinish shard.last sheet := congrArg
        (fun data : CompactCellData => liftedFinish data sheet) lastData
      exact (path.castStart start_eq).castFinish finish_eq

/-- A uniformly certified generated path with its concrete endpoints kept as
small indices.  Packages concatenate without unfolding their internal row
chains. -/
structure LiteralPathPackage
    (sheet : Fin 2)
    (start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2) where
  models : List CCL.ProgressiveGaussianIntegration.CellModel
  path : CCL.Riemann.LiftedPaths.LiftedPath 2 start finish
  certificates :
    CCL.Riemann.AlgebraicDifferentials.UniformPathCertificates
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential models path

theorem pathModel_integralSample_append
    (first second : List CCL.ProgressiveGaussianIntegration.CellModel) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (first ++ second)).integralSample =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk first).integralSample +
        (CCL.ProgressiveGaussianIntegration.PathModel.mk second).integralSample := by
  exact CCL.ProgressiveGaussianIntegration.PathModel.integralSample_concat
    (CCL.ProgressiveGaussianIntegration.PathModel.mk first)
    (CCL.ProgressiveGaussianIntegration.PathModel.mk second)

theorem pathModel_totalWeightedAllowance_append
    (first second : List CCL.ProgressiveGaussianIntegration.CellModel) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      (first ++ second)).totalWeightedAllowance =
      (CCL.ProgressiveGaussianIntegration.PathModel.mk first).totalWeightedAllowance +
        (CCL.ProgressiveGaussianIntegration.PathModel.mk second).totalWeightedAllowance := by
  induction first with
  | nil =>
      unfold CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
      simp only [List.nil_append, List.foldr_nil]
      exact (RFAP.ConstructiveFraction.zero_add _).symm
  | cons cell remaining induction =>
      unfold CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
        at induction ⊢
      simp only [List.cons_append, List.foldr_cons]
      rw [induction]
      ring1

def CompactLiteralPath.toPackage
    {rootBits coefficientBits allowanceBits : Nat} {sheet : Fin 2}
    {cells : List
      (CompactCheckedCell rootBits coefficientBits allowanceBits)}
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (path : CompactLiteralPath sheet cells start finish) :
    LiteralPathPackage sheet start finish :=
  { models := path.models
    path := path.liftedPath
    certificates := path.certificates }

def CompactCheckedShard.literalPackage
    {rootBits coefficientBits allowanceBits offset : Nat}
    (shard : CompactCheckedShard rootBits coefficientBits allowanceBits
      offset) (sheet : Fin 2) :
    LiteralPathPackage sheet (liftedStart shard.first sheet)
      (liftedFinish shard.last sheet) :=
  (shard.literalPath sheet).toPackage

namespace LiteralPathPackage

/-- Concatenate two certified literal packages whose endpoint sheets may
differ.  The sheet parameter of `LiteralPathPackage` records how a package
was constructed; the dependent lifted endpoints themselves enforce the
actual sheet continuity needed for concatenation. -/
def appendMixed
    {firstSheet secondSheet : Fin 2}
    {firstStart firstFinish secondStart secondFinish :
      CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (first : LiteralPathPackage firstSheet firstStart firstFinish)
    (second : LiteralPathPackage secondSheet secondStart secondFinish)
    (endpoint : firstFinish = secondStart) :
    LiteralPathPackage firstSheet firstStart secondFinish := by
  let secondPath := second.path.castStart endpoint.symm
  let secondCertificates := second.certificates.castStart endpoint.symm
  exact
    { models := first.models ++ second.models
      path := first.path.append secondPath
      certificates :=
        CCL.Riemann.AlgebraicDifferentials.UniformPathCertificates.append
          first.path first.certificates secondCertificates }

def append
    {sheet : Fin 2}
    {firstStart firstFinish secondStart secondFinish :
      CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (first : LiteralPathPackage sheet firstStart firstFinish)
    (second : LiteralPathPackage sheet secondStart secondFinish)
    (endpoint : firstFinish = secondStart) :
    LiteralPathPackage sheet firstStart secondFinish :=
  first.appendMixed second endpoint

/-- Exact zero model for one stationary sheet transition. -/
def stationaryModel (coordinate : Gaussian) :
    CCL.ProgressiveGaussianIntegration.CellModel :=
  CCL.ProgressiveGaussianIntegration.CellModel.exact coordinate coordinate
    (CCL.FiniteGaussianPolynomial.constant 0)

@[simp] theorem stationaryModel_integralSample (coordinate : Gaussian) :
    (stationaryModel coordinate).integralSample = 0 := by
  unfold stationaryModel
    CCL.ProgressiveGaussianIntegration.CellModel.integralSample
    CCL.ProgressiveGaussianIntegration.CellModel.displacement
    CCL.ProgressiveGaussianIntegration.CellModel.exact
  rw [RFAP.ConstructiveGaussian.Gaussian.sub_self]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.zero_re,
      RFAP.ConstructiveGaussian.Gaussian.zero_im] <;> ring1

@[simp] theorem stationaryModel_weightedAllowance (coordinate : Gaussian) :
    (stationaryModel coordinate).weightedAllowance = 0 := by
  unfold stationaryModel
    CCL.ProgressiveGaussianIntegration.CellModel.weightedAllowance
    CCL.ProgressiveGaussianIntegration.CellModel.exact
  rw [RFAP.ConstructiveFraction.mul_zero_direct]

/-- Certified one-cell package for an exact stationary sheet switch. -/
def stationary (coordinate : Gaussian) (sheet : Fin 2) :
    LiteralPathPackage sheet
      { coordinate := coordinate, sheet := sheet }
      { coordinate := coordinate,
        sheet := CCL.Riemann.BranchCutLifts.otherSheet sheet } := by
  let finish : CCL.Riemann.LiftedPaths.LiftedPoint 2 :=
    { coordinate := coordinate,
      sheet := CCL.Riemann.BranchCutLifts.otherSheet sheet }
  exact
    { models := [stationaryModel coordinate]
      path := .cons (CCL.Riemann.BranchCutLifts.switchCell coordinate sheet)
        (.nil finish)
      certificates := by
        simpa only [stationaryModel] using
          (CCL.Riemann.AlgebraicDifferentials.UniformPathCertificates.cons
            rfl rfl (.stationary rfl)
            (CCL.Riemann.AlgebraicDifferentials.UniformPathCertificates.nil
              finish)) }

end LiteralPathPackage

/-- A path package paired with the fixed-grid summary which exactly denotes
its model count, sample, and semantic weighted allowance. -/
structure SummarizedLiteralPathPackage
    (rootBits coefficientBits allowanceBits : Nat) (sheet : Fin 2)
    (start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2) where
  package : LiteralPathPackage sheet start finish
  totals : CompactTotals
  count_eq : package.models.length = totals.count
  integralSample_eq :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      package.models).integralSample = totals.literalSample coefficientBits
  totalWeightedAllowance_eq :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      package.models).totalWeightedAllowance =
        totals.weightedAllowanceValue allowanceBits

namespace SummarizedLiteralPathPackage

theorem aggregateAllowance_eq
    {rootBits coefficientBits allowanceBits : Nat} {sheet : Fin 2}
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (summary : SummarizedLiteralPathPackage rootBits coefficientBits
      allowanceBits sheet start finish) :
    (CCL.ProgressiveGaussianIntegration.PathModel.mk
      summary.package.models).aggregateAllowance =
        summary.totals.aggregateAllowance allowanceBits := by
  unfold CCL.ProgressiveGaussianIntegration.PathModel.aggregateAllowance
  rw [summary.count_eq, summary.totalWeightedAllowance_eq,
    CompactTotals.aggregateAllowance_eq_count_mul]

def append
    {rootBits coefficientBits allowanceBits : Nat} {sheet : Fin 2}
    {firstStart firstFinish secondStart secondFinish :
      CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (first : SummarizedLiteralPathPackage rootBits coefficientBits
      allowanceBits sheet firstStart firstFinish)
    (second : SummarizedLiteralPathPackage rootBits coefficientBits
      allowanceBits sheet secondStart secondFinish)
    (endpoint : firstFinish = secondStart) :
    SummarizedLiteralPathPackage rootBits coefficientBits allowanceBits
      sheet firstStart secondFinish := by
  let package := first.package.append second.package endpoint
  exact
    { package := package
      totals := first.totals.add second.totals
      count_eq := by
        change (first.package.models ++ second.package.models).length =
          first.totals.count + second.totals.count
        rw [List.length_append, first.count_eq, second.count_eq]
      integralSample_eq := by
        change (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (first.package.models ++ second.package.models)).integralSample = _
        rw [pathModel_integralSample_append, first.integralSample_eq,
          second.integralSample_eq,
          ← CompactCellData.compactTotals_literalSample_add]
      totalWeightedAllowance_eq := by
        change (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (first.package.models ++ second.package.models)).totalWeightedAllowance = _
        rw [pathModel_totalWeightedAllowance_append,
          first.totalWeightedAllowance_eq,
          second.totalWeightedAllowance_eq,
          ← CompactCellData.compactTotals_weightedAllowanceValue_add] }

/-- Summary-preserving concatenation across a certified sheet transition. -/
def appendMixed
    {rootBits coefficientBits allowanceBits : Nat}
    {firstSheet secondSheet : Fin 2}
    {firstStart firstFinish secondStart secondFinish :
      CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (first : SummarizedLiteralPathPackage rootBits coefficientBits
      allowanceBits firstSheet firstStart firstFinish)
    (second : SummarizedLiteralPathPackage rootBits coefficientBits
      allowanceBits secondSheet secondStart secondFinish)
    (endpoint : firstFinish = secondStart) :
    SummarizedLiteralPathPackage rootBits coefficientBits allowanceBits
      firstSheet firstStart secondFinish := by
  let package := first.package.appendMixed second.package endpoint
  exact
    { package := package
      totals := first.totals.add second.totals
      count_eq := by
        change (first.package.models ++ second.package.models).length =
          first.totals.count + second.totals.count
        rw [List.length_append, first.count_eq, second.count_eq]
      integralSample_eq := by
        change (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (first.package.models ++ second.package.models)).integralSample = _
        rw [pathModel_integralSample_append, first.integralSample_eq,
          second.integralSample_eq,
          ← CompactCellData.compactTotals_literalSample_add]
      totalWeightedAllowance_eq := by
        change (CCL.ProgressiveGaussianIntegration.PathModel.mk
            (first.package.models ++ second.package.models)).totalWeightedAllowance = _
        rw [pathModel_totalWeightedAllowance_append,
          first.totalWeightedAllowance_eq,
          second.totalWeightedAllowance_eq,
          ← CompactCellData.compactTotals_weightedAllowanceValue_add] }

/-- Exact summary of a stationary switch: one cell, zero sample, and zero
weighted semantic allowance. -/
def stationary
    (rootBits coefficientBits allowanceBits : Nat)
    (coordinate : Gaussian) (sheet : Fin 2) :
    SummarizedLiteralPathPackage rootBits coefficientBits allowanceBits sheet
      { coordinate := coordinate, sheet := sheet }
      { coordinate := coordinate,
        sheet := CCL.Riemann.BranchCutLifts.otherSheet sheet } :=
  { package := LiteralPathPackage.stationary coordinate sheet
    totals :=
      { count := 1
        sampleRe := 0
        sampleIm := 0
        weightedAllowance := 0
        movementSq := 0
        transportWeightedError := 0 }
    count_eq := rfl
    integralSample_eq := by
      dsimp only [LiteralPathPackage.stationary]
      rw [CCL.ProgressiveGaussianIntegration.PathModel.singleton_integralSample,
        LiteralPathPackage.stationaryModel_integralSample]
      apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
        simp only [CompactTotals.literalSample, DyadicGaussian.toGaussian,
          Dyadic.toCoordinate_zero_numerator,
          RFAP.ConstructiveGaussian.Gaussian.zero_re,
          RFAP.ConstructiveGaussian.Gaussian.zero_im]
    totalWeightedAllowance_eq := by
      dsimp only [LiteralPathPackage.stationary]
      unfold CCL.ProgressiveGaussianIntegration.PathModel.totalWeightedAllowance
      simp only [List.foldr_cons, List.foldr_nil,
        LiteralPathPackage.stationaryModel_weightedAllowance,
        RFAP.ConstructiveFraction.zero_add,
        CompactTotals.weightedAllowanceValue,
        Dyadic.toCoordinate_zero_numerator] }

end SummarizedLiteralPathPackage

def CompactCheckedShard.literalSummary
    {rootBits coefficientBits allowanceBits offset : Nat}
    (shard : CompactCheckedShard rootBits coefficientBits allowanceBits
      offset) (sheet : Fin 2) :
    SummarizedLiteralPathPackage rootBits coefficientBits allowanceBits sheet
      (liftedStart shard.first sheet) (liftedFinish shard.last sheet) := by
  let path := shard.literalPath sheet
  let package := path.toPackage
  exact
    { package := package
      totals := shard.totals
      count_eq := by
        change path.models.length = shard.totals.count
        rw [path.models_eq_map, List.length_map, ← shard.totalsChecked,
          compactTotals_count]
        rw [List.length_map]
      integralSample_eq := by
        change (CCL.ProgressiveGaussianIntegration.PathModel.mk
            path.models).integralSample =
          shard.totals.literalSample coefficientBits
        rw [path.models_eq_map,
          ← compactTotals_literalModels_integralSample,
          shard.totalsChecked]
      totalWeightedAllowance_eq := by
        change (CCL.ProgressiveGaussianIntegration.PathModel.mk
            path.models).totalWeightedAllowance =
          shard.totals.weightedAllowanceValue allowanceBits
        rw [path.models_eq_map,
          ← compactTotals_literalModels_totalWeightedAllowance,
          shard.totalsChecked] }

structure ClosedLiteralPathPackage
    (sheet : Fin 2)
    (basepoint : CCL.Riemann.LiftedPaths.LiftedPoint 2) where
  models : List CCL.ProgressiveGaussianIntegration.CellModel
  closedPath : CCL.Riemann.LiftedPaths.ClosedLiftedPath 2
  basepoint_eq : closedPath.basepoint = basepoint
  certificates :
    CCL.Riemann.AlgebraicDifferentials.UniformPathCertificates
      CCL.Riemann.ExplicitLegendreLoopBaseBranches.baseCurve
      CompactCellData.legendreDifferential models closedPath.path

def LiteralPathPackage.close
    {sheet : Fin 2}
    {start finish : CCL.Riemann.LiftedPaths.LiftedPoint 2}
    (package : LiteralPathPackage sheet start finish)
    (endpoint : finish = start) :
    ClosedLiteralPathPackage sheet start := by
  let closedPath : CCL.Riemann.LiftedPaths.ClosedLiftedPath 2 :=
    { basepoint := start
      path := package.path.castFinish endpoint }
  exact
    { models := package.models
      closedPath := closedPath
      basepoint_eq := rfl
      certificates := package.certificates.castFinish endpoint }

theorem shardLink_endpoint
    {rootBits coefficientBits allowanceBits leftOffset rightOffset : Nat}
    {left : CompactCheckedShard rootBits coefficientBits allowanceBits
      leftOffset}
    {right : CompactCheckedShard rootBits coefficientBits allowanceBits
      rightOffset}
    (bounds : ({ left := left.last, right := right.first } :
      CompactShardLink).Bounds rootBits) (sheet : Fin 2) :
    liftedFinish left.last sheet = liftedStart right.first sheet := by
  exact congrArg
    (fun coordinate : Gaussian =>
      ({ coordinate := coordinate, sheet := sheet } :
        CCL.Riemann.LiftedPaths.LiftedPoint 2))
    bounds.bridge.endpoint

namespace CompactCellData

/-- The compact coordinatewise link check has its expected geometric
meaning: consecutive generated root squares have a displayed intersection.
This is intentionally weaker than identifying their root names; the latter
requires a winding-one bridge, not just overlapping rectangles. -/
theorem rootBoxes_not_separated (rootBits : Nat)
    {left right : CompactCellData}
    (overlap : Overlap rootBits left right) :
    ¬(left.rootBox rootBits).Separated (right.rootBox rootBits) := by
  intro separated
  unfold RFAP.Boxes.Box.Separated at separated
  unfold rootBox RFAP.AffineWinding.centeredSquare at separated
  have realUpper := overlap.realUpper
  have realLower := overlap.realLower
  have imaginaryUpper := overlap.imaginaryUpper
  have imaginaryLower := overlap.imaginaryLower
  rw [Dyadic.toCoordinate_sub, Dyadic.toCoordinate_add] at realUpper
  rw [Dyadic.toCoordinate_neg, Dyadic.toCoordinate_sub,
    Dyadic.toCoordinate_add] at realLower
  rw [Dyadic.toCoordinate_sub, Dyadic.toCoordinate_add] at imaginaryUpper
  rw [Dyadic.toCoordinate_neg, Dyadic.toCoordinate_sub,
    Dyadic.toCoordinate_add] at imaginaryLower
  rcases separated with leftOf | rightOf | below | above
  · apply (not_lt_of_ge realLower)
    change left.halfWidth + right.halfWidth <
      -((left.rootCenterValue rootBits).re -
        (right.rootCenterValue rootBits).re)
    change (left.rootCenterValue rootBits).re + left.halfWidth <
      (right.rootCenterValue rootBits).re - right.halfWidth at leftOf
    calc
      left.halfWidth + right.halfWidth =
          ((left.rootCenterValue rootBits).re + left.halfWidth -
            (left.rootCenterValue rootBits).re) + right.halfWidth := by ring1
      _ < ((right.rootCenterValue rootBits).re - right.halfWidth -
            (left.rootCenterValue rootBits).re) + right.halfWidth :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          (RFAP.ConstructiveFraction.sub_lt_sub_right_direct leftOf _)
          right.halfWidth
      _ = -((left.rootCenterValue rootBits).re -
          (right.rootCenterValue rootBits).re) := by ring1
  · apply (not_lt_of_ge realUpper)
    change left.halfWidth + right.halfWidth <
      (left.rootCenterValue rootBits).re -
        (right.rootCenterValue rootBits).re
    change (right.rootCenterValue rootBits).re + right.halfWidth <
      (left.rootCenterValue rootBits).re - left.halfWidth at rightOf
    calc
      left.halfWidth + right.halfWidth =
          ((right.rootCenterValue rootBits).re + right.halfWidth -
            (right.rootCenterValue rootBits).re) + left.halfWidth := by ring1
      _ < ((left.rootCenterValue rootBits).re - left.halfWidth -
            (right.rootCenterValue rootBits).re) + left.halfWidth :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          (RFAP.ConstructiveFraction.sub_lt_sub_right_direct rightOf _)
          left.halfWidth
      _ = (left.rootCenterValue rootBits).re -
          (right.rootCenterValue rootBits).re := by ring1
  · apply (not_lt_of_ge imaginaryLower)
    change left.halfWidth + right.halfWidth <
      -((left.rootCenterValue rootBits).im -
        (right.rootCenterValue rootBits).im)
    change (left.rootCenterValue rootBits).im + left.halfWidth <
      (right.rootCenterValue rootBits).im - right.halfWidth at below
    calc
      left.halfWidth + right.halfWidth =
          ((left.rootCenterValue rootBits).im + left.halfWidth -
            (left.rootCenterValue rootBits).im) + right.halfWidth := by ring1
      _ < ((right.rootCenterValue rootBits).im - right.halfWidth -
            (left.rootCenterValue rootBits).im) + right.halfWidth :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          (RFAP.ConstructiveFraction.sub_lt_sub_right_direct below _)
          right.halfWidth
      _ = -((left.rootCenterValue rootBits).im -
          (right.rootCenterValue rootBits).im) := by ring1
  · apply (not_lt_of_ge imaginaryUpper)
    change left.halfWidth + right.halfWidth <
      (left.rootCenterValue rootBits).im -
        (right.rootCenterValue rootBits).im
    change (right.rootCenterValue rootBits).im + right.halfWidth <
      (left.rootCenterValue rootBits).im - left.halfWidth at above
    calc
      left.halfWidth + right.halfWidth =
          ((right.rootCenterValue rootBits).im + right.halfWidth -
            (right.rootCenterValue rootBits).im) + left.halfWidth := by ring1
      _ < ((left.rootCenterValue rootBits).im - left.halfWidth -
            (right.rootCenterValue rootBits).im) + left.halfWidth :=
        RFAP.ConstructiveFraction.add_lt_add_right_direct
          (RFAP.ConstructiveFraction.sub_lt_sub_right_direct above _)
          left.halfWidth
      _ = (left.rootCenterValue rootBits).im -
          (right.rootCenterValue rootBits).im := by ring1

def rootBoxesCommonPoint (rootBits : Nat)
    (left right : CompactCellData) : Gaussian :=
  RFAP.Boxes.Box.overlapPoint (left.rootBox rootBits) (right.rootBox rootBits)

theorem rootBoxesCommonPoint_inside (rootBits : Nat)
    {left right : CompactCellData}
    (overlap : Overlap rootBits left right) :
    (left.rootBox rootBits).Contains
        (rootBoxesCommonPoint rootBits left right) ∧
      (right.rootBox rootBits).Contains
        (rootBoxesCommonPoint rootBits left right) :=
  RFAP.Boxes.Box.contains_overlapPoint_of_not_separated
    (rootBoxes_not_separated rootBits overlap)

def bridgeHalfWidthValue (left right : CompactCellData) : Coordinate :=
  (bridgeHalfWidth left right).toCoordinate

theorem bridgeHalfWidthValue_positive (left right : CompactCellData) :
    0 < bridgeHalfWidthValue left right := by
  unfold bridgeHalfWidthValue bridgeHalfWidth Dyadic.toCoordinate
    Dyadic.toFraction
  rw [RFAP.ConstructiveFraction.ofFraction_eq_div]
  apply RFAP.ConstructiveFraction.div_pos_direct
  · change (0 : Coordinate) < 1
    decide
  · rw [RFAP.CanonicalFraction.intCast_eq_fromInt,
      RFAP.CanonicalFraction.zero_lt_iff_num_pos]
    exact Int.pow_pos (by decide)

def rootBridgeBox (rootBits : Nat) (left right : CompactCellData) :
    RFAP.Boxes.Box :=
  RFAP.AffineWinding.centeredSquare (right.rootCenterValue rootBits)
    (bridgeHalfWidthValue left right)
      (bridgeHalfWidthValue_positive left right).le

theorem rootBridgeBox_proper (rootBits : Nat)
    (left right : CompactCellData) :
    (rootBridgeBox rootBits left right).Proper :=
  RFAP.AffineWinding.centeredSquare_proper _
    (bridgeHalfWidthValue_positive left right)

@[simp] theorem bridgeRoucheLinearSq_toCoordinate (rootBits : Nat)
    (left right : CompactCellData) :
    (bridgeRoucheLinearSq rootBits left right).toCoordinate =
      4 * (normSq (right.rootCenterValue rootBits) *
        bridgeHalfWidthValue left right ^ 2) := by
  unfold bridgeRoucheLinearSq bridgeHalfWidthValue rootCenterValue
    Dyadic.square
  rw [Dyadic.toCoordinate_scale, Dyadic.toCoordinate_mul,
    Dyadic.toCoordinate_mul, DyadicGaussian.normSq_toGaussian, pow_two]
  rfl

@[simp] theorem bridgeRoucheRemainderSq_toCoordinate (rootBits : Nat)
    (left right : CompactCellData) :
    (bridgeRoucheRemainderSq rootBits left right).toCoordinate =
      4 * (normSq (right.rootCenterValue rootBits *
          right.rootCenterValue rootBits - radicand right.startValue) +
        4 * bridgeHalfWidthValue left right ^ 4) := by
  unfold bridgeRoucheRemainderSq bridgeHalfWidthValue Dyadic.square
  rw [Dyadic.toCoordinate_scale, Dyadic.toCoordinate_add,
    Dyadic.toCoordinate_scale, Dyadic.toCoordinate_mul,
    Dyadic.toCoordinate_mul, rootResidualSq_toCoordinate]
  ring1

theorem rootBridgeBox_strict_left (rootBits : Nat)
    {left right : CompactCellData}
    (bounds : BridgeBounds rootBits left right) :
    (rootBridgeBox rootBits left right).StrictInterior
      (left.rootBox rootBits) := by
  rcases bounds.strictLeft with ⟨leftSide, rightSide, bottomSide, topSide⟩
  simp only [Dyadic.toCoordinate_sub] at leftSide bottomSide
  simp only [Dyadic.toCoordinate_add] at rightSide topSide
  unfold rootBridgeBox rootBox RFAP.AffineWinding.centeredSquare
  exact ⟨by simpa only [rootCenterValue, halfWidth, bridgeHalfWidthValue,
      DyadicGaussian.toGaussian] using leftSide,
    by simpa only [rootCenterValue, halfWidth, bridgeHalfWidthValue,
      DyadicGaussian.toGaussian] using rightSide,
    by simpa only [rootCenterValue, halfWidth, bridgeHalfWidthValue,
      DyadicGaussian.toGaussian] using bottomSide,
    by simpa only [rootCenterValue, halfWidth, bridgeHalfWidthValue,
      DyadicGaussian.toGaussian] using topSide⟩

theorem rootBridgeBox_strict_right (rootBits : Nat)
    {left right : CompactCellData}
    (bounds : BridgeBounds rootBits left right) :
    (rootBridgeBox rootBits left right).StrictInterior
      (right.rootBox rootBits) := by
  rcases bounds.strictRight with ⟨leftSide, rightSide, bottomSide, topSide⟩
  simp only [Dyadic.toCoordinate_sub] at leftSide bottomSide
  simp only [Dyadic.toCoordinate_add] at rightSide topSide
  unfold rootBridgeBox rootBox RFAP.AffineWinding.centeredSquare
  exact ⟨by simpa only [rootCenterValue, halfWidth, bridgeHalfWidthValue,
      DyadicGaussian.toGaussian] using leftSide,
    by simpa only [rootCenterValue, halfWidth, bridgeHalfWidthValue,
      DyadicGaussian.toGaussian] using rightSide,
    by simpa only [rootCenterValue, halfWidth, bridgeHalfWidthValue,
      DyadicGaussian.toGaussian] using bottomSide,
    by simpa only [rootCenterValue, halfWidth, bridgeHalfWidthValue,
      DyadicGaussian.toGaussian] using topSide⟩

theorem rootBridgeLinearBoundaryLower (rootBits : Nat)
    (left right : CompactCellData) (value : Gaussian)
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (rootBridgeBox rootBits left right) value) :
    (bridgeRoucheLinearSq rootBits left right).toCoordinate <=
      normSq ((right.rootLinearPolynomial rootBits).eval value) := by
  let center := right.rootCenterValue rootBits
  let radius := bridgeHalfWidthValue left right
  have radial :=
    (RFAP.AffineWinding.translatedCoordinate_boundaryClearance center
      (bridgeHalfWidthValue_positive left right)).lower value boundary
  dsimp only [RFAP.AffineWinding.translatedCoordinate_boundaryClearance]
    at radial
  rw [RFAP.AffineWinding.translatedCoordinate_eval] at radial
  rw [rootLinearPolynomial, RFAP.AffineWinding.affineCoordinate_eval,
    normSq_mul, bridgeRoucheLinearSq_toCoordinate, rootSlope,
    CCL.FiniteExp.normSq_scale]
  have scaled := RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
    radial
    (RFAP.ConstructiveFraction.mul_nonneg_direct
      (RFAP.ConstructiveFraction.sq_nonneg_direct (2 : Coordinate))
      (normSq_nonneg center))
  dsimp only [center, radius] at scaled ⊢
  convert scaled using 1
  all_goals ring1

theorem rootBridgePerturbationBoundaryUpper (rootBits : Nat)
    (left right : CompactCellData) (value : Gaussian)
    (boundary : RFAP.BoxClearance.OnBoxBoundary
      (rootBridgeBox rootBits left right) value) :
    normSq ((right.rootPerturbation rootBits 0).eval value) <=
      (bridgeRoucheRemainderSq rootBits left right).toCoordinate := by
  let center := right.rootCenterValue rootBits
  let radius := bridgeHalfWidthValue left right
  let offset := value - center
  let residual := center * center - radicand right.startValue
  have perturbationIdentity :
      (right.rootPerturbation rootBits 0).eval value =
        offset * offset + residual := by
    rw [rootPerturbation_eval, parameterValue_zero,
      RFAP.ConstructiveGaussian.Gaussian.sub_self]
    dsimp only [offset, residual, center]
    apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
      simp only [sub_re, sub_im, add_re, add_im, zero_re, zero_im] <;> ring1
  have offsetNorm : normSq offset <= 2 * radius ^ 2 := by
    exact RFAP.AffineWinding.centeredSquare_normSq_sub_center_le center
      (bridgeHalfWidthValue_positive left right).le boundary.1
  have offsetSquare : normSq (offset * offset) <= 4 * radius ^ 4 :=
    normSq_mul_self_le_four offsetNorm
  have sumBound : normSq (offset * offset + residual) <=
      2 * (4 * radius ^ 4 + normSq residual) :=
    (normSq_add_le_two (offset * offset) residual).trans
      (RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        (add_le_add offsetSquare le_rfl) (by decide))
  have termsNonnegative :
      0 <= normSq residual + 4 * radius ^ 4 :=
    add_nonneg (normSq_nonneg residual)
      (RFAP.ConstructiveFraction.mul_nonneg_direct (by decide)
        (RFAP.ConstructiveFraction.pow_nonneg_direct
          (bridgeHalfWidthValue_positive left right).le 4))
  rw [perturbationIdentity, bridgeRoucheRemainderSq_toCoordinate]
  calc
    normSq (offset * offset + residual) <=
        2 * (4 * radius ^ 4 + normSq residual) := sumBound
    _ = 2 * (normSq residual + 4 * radius ^ 4) := by ring1
    _ <= 4 * (normSq residual + 4 * radius ^ 4) :=
      RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
        (by decide) termsNonnegative

def rootBridgeLinearClearance
    {rootBits coefficientBits allowanceBits : Nat}
    {left right : CompactCellData}
    (rightBounds : right.Bounds rootBits coefficientBits allowanceBits) :
    RFAP.BoxClearance.BoundaryClearance
      (right.rootLinearPolynomial rootBits)
      (rootBridgeBox rootBits left right) where
  bound := (bridgeRoucheLinearSq rootBits left right).toCoordinate
  positive := by
    rw [bridgeRoucheLinearSq_toCoordinate]
    exact RFAP.ConstructiveFraction.mul_pos_direct (by decide)
      (RFAP.ConstructiveFraction.mul_pos_direct
        (normSq_pos (right.rootCenter_nonzero rightBounds))
        (RFAP.ConstructiveFraction.pow_pos_direct
          (bridgeHalfWidthValue_positive left right) 2))
  lower := rootBridgeLinearBoundaryLower rootBits left right

def rootBridgeDominance
    {rootBits : Nat}
    {left right : CompactCellData}
    (bridgeBounds : BridgeBounds rootBits left right) :
    RFAP.WindingHomotopy.BoundaryNormDominance
      (right.rootLinearPolynomial rootBits)
      (right.rootPerturbation rootBits 0)
      (rootBridgeBox rootBits left right) where
  margin := (bridgeRoucheLinearSq rootBits left right).toCoordinate -
    (bridgeRoucheRemainderSq rootBits left right).toCoordinate
  positive := RFAP.ConstructiveFraction.sub_pos_direct bridgeBounds.rouche
  lower := by
    intro value boundary
    exact RFAP.ConstructiveFraction.sub_le_sub_direct
      (rootBridgeLinearBoundaryLower rootBits left right value boundary)
      (rootBridgePerturbationBoundaryUpper rootBits left right value boundary)

def rootBridgeClearance
    {rootBits : Nat}
    {left right : CompactCellData}
    (bridgeBounds : BridgeBounds rootBits left right) :
    RFAP.BoxClearance.BoundaryClearance
      (right.rootTargetPolynomial 0) (rootBridgeBox rootBits left right) := by
  rw [right.rootTarget_eq_linear_add_perturbation rootBits 0]
  exact RFAP.WindingHomotopy.boundaryClearance_add_of_boundaryNormDominance
    (right.rootLinearPolynomial rootBits)
    (right.rootPerturbation rootBits 0) (rootBridgeBox rootBits left right)
    (rootBridgeBox_proper rootBits left right)
    (rootBridgeDominance bridgeBounds)

theorem rootBridgeWindingFour
    {rootBits coefficientBits allowanceBits : Nat}
    {left right : CompactCellData}
    (rightBounds : right.Bounds rootBits coefficientBits allowanceBits)
    (bridgeBounds : BridgeBounds rootBits left right) :
    RFAP.Winding.quadrupledBoxWinding
      (right.rootTargetPolynomial 0) (rootBridgeBox rootBits left right) = 4 := by
  rw [right.rootTarget_eq_linear_add_perturbation rootBits 0]
  exact (RFAP.WindingHomotopy.quadrupledBoxWinding_add_of_boundaryNormDominance
    (right.rootLinearPolynomial rootBits)
    (right.rootPerturbation rootBits 0) (rootBridgeBox rootBits left right)
    (rootBridgeBox_proper rootBits left right)
    (rootBridgeLinearClearance (left := left) rightBounds)
    (rootBridgeDominance bridgeBounds)).trans
      (RFAP.AffineWinding.quadrupledBoxWinding_affineCoordinate_centeredSquare
        (right.rootSlope_nonzero rightBounds)
        (right.rootCenterValue rootBits)
        (bridgeHalfWidthValue_positive left right))

def rootBridgeState
    {rootBits coefficientBits allowanceBits : Nat}
    {left right : CompactCellData}
    (rightBounds : right.Bounds rootBits coefficientBits allowanceBits)
    (bridgeBounds : BridgeBounds rootBits left right) :
    RFAP.ShrinkingTrack.WindingOneState
      (right.rootTargetPolynomial 0) (rootBridgeBox rootBits left right) :=
  let clearance := rootBridgeClearance bridgeBounds
  { box := rootBridgeBox rootBits left right
    refinesAmbient := RFAP.Boxes.Box.refines_refl _
    proper := rootBridgeBox_proper rootBits left right
    clearance := clearance
    rawWindingFour := rootBridgeWindingFour rightBounds bridgeBounds
    ambientLeftClearance := RFAP.BoxClearance.leftOfBoundary clearance
    ambientRightClearance := RFAP.BoxClearance.rightOfBoundary clearance
    ambientBottomClearance := RFAP.BoxClearance.bottomOfBoundary clearance
    ambientTopClearance := RFAP.BoxClearance.topOfBoundary clearance }

def rootBridgeOwner
    {rootBits coefficientBits allowanceBits : Nat}
    {left right : CompactCellData}
    (rightBounds : right.Bounds rootBits coefficientBits allowanceBits)
    (bridgeBounds : BridgeBounds rootBits left right) :
    CCL.Riemann.SquareRootContinuationChain.Owner
      (radicand (right.parameterValue 0)) :=
  CCL.Riemann.SquareRootContinuationChain.Owner.ofState
    (right.radicand_parameter_nonzero rightBounds 0 (by decide) (by decide))
    (rootBridgeState rightBounds bridgeBounds)

@[simp] theorem rootBridgeOwner_initial_box
    {rootBits coefficientBits allowanceBits : Nat}
    {left right : CompactCellData}
    (rightBounds : right.Bounds rootBits coefficientBits allowanceBits)
    (bridgeBounds : BridgeBounds rootBits left right) :
    (rootBridgeOwner rightBounds bridgeBounds).track.initial.box =
      rootBridgeBox rootBits left right := by
  rfl

/-- A winding-one owner strictly containing one common winding-one bridge
names the same productive square root as that bridge.  Applying this on both
sides of a generated link turns the two strict-containment checks into an
operational equality of the neighboring root names. -/
def ownerRootEquivalent_of_commonStrictBridge
    {parameter : Gaussian} (parameterNonzero : parameter ≠ 0)
    (left right bridge :
      CCL.Riemann.SquareRootContinuationChain.Owner parameter)
    (bridgeStrictLeft :
      bridge.track.initial.box.StrictInterior left.track.initial.box)
    (bridgeStrictRight :
      bridge.track.initial.box.StrictInterior right.track.initial.box) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        parameterNonzero left)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName
        parameterNonzero right) :=
  CCL.OperationalEquivalence.NamedEquivalent.trans
    (CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      parameterNonzero left.track bridge.track bridgeStrictLeft)
    (CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
      parameterNonzero right.track bridge.track bridgeStrictRight).symm

/-- The same common-bridge comparison when the two owners' parameters are
propositionally, rather than definitionally, equal. -/
def ownerRootEquivalent_of_commonStrictBridge_eq
    {leftParameter rightParameter : Gaussian}
    (parameterEq : leftParameter = rightParameter)
    (leftNonzero : leftParameter ≠ 0) (rightNonzero : rightParameter ≠ 0)
    (left : CCL.Riemann.SquareRootContinuationChain.Owner leftParameter)
    (right bridge :
      CCL.Riemann.SquareRootContinuationChain.Owner rightParameter)
    (bridgeStrictLeft :
      bridge.track.initial.box.StrictInterior left.track.initial.box)
    (bridgeStrictRight :
      bridge.track.initial.box.StrictInterior right.track.initial.box) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName leftNonzero left)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName rightNonzero right) := by
  subst rightParameter
  exact ownerRootEquivalent_of_commonStrictBridge leftNonzero left right bridge
    bridgeStrictLeft bridgeStrictRight

/-- Strict containment also compares owners whose displayed parameters are
equal only after an exact rational endpoint calculation. -/
def ownerRootEquivalent_of_initial_strict_eq
    {outerParameter innerParameter : Gaussian}
    (parameterEq : outerParameter = innerParameter)
    (outerNonzero : outerParameter ≠ 0) (innerNonzero : innerParameter ≠ 0)
    (outer : CCL.Riemann.SquareRootContinuationChain.Owner outerParameter)
    (inner : CCL.Riemann.SquareRootContinuationChain.Owner innerParameter)
    (innerStrict :
      inner.track.initial.box.StrictInterior outer.track.initial.box) :
    CCL.OperationalEquivalence.NamedEquivalent
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName outerNonzero outer)
      (CCL.Riemann.SquareRootTrackEquivalence.ownerRootName innerNonzero inner) := by
  subst innerParameter
  exact CCL.Riemann.SquareRootTrackEquivalence.rootEquivalent_of_initial_strict
    outerNonzero outer.track inner.track innerStrict

/-- Consecutive generated rows carry the same operational square-root name at
their common path endpoint.  The proof uses the independently checked bridge
square, rather than treating geometric overlap as evidence of root identity. -/
def adjacentRootEquivalent
    {rootBits coefficientBits allowanceBits : Nat}
    {left right : CompactCellData}
    (leftBounds : left.Bounds rootBits coefficientBits allowanceBits)
    (rightBounds : right.Bounds rootBits coefficientBits allowanceBits)
    (bridgeBounds : BridgeBounds rootBits left right) :
    CCL.OperationalEquivalence.NamedEquivalent
      (left.finishRootName leftBounds)
      (right.startRootName rightBounds) := by
  let leftOwner := left.rootOwner leftBounds 1 (by decide) (by decide)
  let rightOwner := right.rootOwner rightBounds 0 (by decide) (by decide)
  let bridge := rootBridgeOwner rightBounds bridgeBounds
  have leftStrict : bridge.track.initial.box.StrictInterior
      leftOwner.track.initial.box :=
    by
      simpa only [bridge, leftOwner, rootBridgeOwner_initial_box,
        rootOwner_initial_box] using
        (rootBridgeBox_strict_left rootBits bridgeBounds)
  have rightStrict : bridge.track.initial.box.StrictInterior
      rightOwner.track.initial.box :=
    by
      simpa only [bridge, rightOwner, rootBridgeOwner_initial_box,
        rootOwner_initial_box] using
        (rootBridgeBox_strict_right rootBits bridgeBounds)
  have endpoint : left.parameterValue 1 = right.parameterValue 0 :=
    left.parameterValue_one.trans
      (bridgeBounds.endpoint.trans right.parameterValue_zero.symm)
  exact ownerRootEquivalent_of_commonStrictBridge_eq
    (congrArg radicand endpoint)
    leftOwner.parameterNonzero rightOwner.parameterNonzero
    leftOwner rightOwner bridge leftStrict rightStrict

end CompactCellData

namespace CompactShardLink

/-- A checked inter-shard link, together with local bounds for its two cells,
has the same semantic root-continuity conclusion as an in-shard link. -/
def rootEquivalent {rootBits coefficientBits allowanceBits : Nat}
    {link : CompactShardLink}
    (leftBounds : link.left.Bounds rootBits coefficientBits allowanceBits)
    (rightBounds : link.right.Bounds rootBits coefficientBits allowanceBits)
    (bounds : link.Bounds rootBits) :
    CCL.OperationalEquivalence.NamedEquivalent
      (link.left.finishRootName leftBounds)
      (link.right.startRootName rightBounds) :=
  CompactCellData.adjacentRootEquivalent leftBounds rightBounds bounds.bridge

end CompactShardLink

end CCL.Riemann.GeneratedLegendreCertificateData
