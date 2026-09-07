import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.Curve.Rational

/-!
# Canonical rational line and circle parameterizations

The CCL branch boundaries originate as coordinate lines or centered norm
circles before finite homographic pullback.  These explicit parameterizations
retain that provenance, including a proof that their parameter denominator
never vanishes.  Homographic transformation can subsequently move them into
the original polynomial coordinate.
-/

namespace CCL.CanonicalCurves

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial := RFAP.ConstructivePolynomial.GaussianPolynomial
abbrev RationalCurve := CCL.RationalCurve.RationalCurve

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ComputablePolynomial.DensePolynomial

def ofCoordinate (value : Coordinate) : Gaussian := ⟨value, 0⟩
def imaginaryUnit : Gaussian := ⟨0, 1⟩
def imaginaryCoordinate (value : Coordinate) : Gaussian := ⟨0, value⟩

/-- Vertical line `re z = threshold`, parameterized by its imaginary
coordinate. -/
def realLine (threshold : Coordinate) : RationalCurve where
  numerator := ⟨[imaginaryUnit, ofCoordinate threshold]⟩
  denominator := constant 1

/-- Horizontal line `im z = threshold`, parameterized by its real
coordinate. -/
def imaginaryLine (threshold : Coordinate) : RationalCurve where
  numerator := ⟨[1, imaginaryCoordinate threshold]⟩
  denominator := constant 1

@[simp] theorem realLine_denominatorAt
    (threshold parameter : Coordinate) :
    (realLine threshold).denominatorAt parameter = 1 := by
  simp [realLine, CCL.RationalCurve.RationalCurve.denominatorAt]

@[simp] theorem imaginaryLine_denominatorAt
    (threshold parameter : Coordinate) :
    (imaginaryLine threshold).denominatorAt parameter = 1 := by
  simp [imaginaryLine,
    CCL.RationalCurve.RationalCurve.denominatorAt]

theorem one_ne_zero : (1 : Gaussian) ≠ 0 := by
  intro oneZero
  have realOneZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re oneZero
  exact RFAP.ConstructiveFraction.zero_ne_one realOneZero.symm

theorem realLine_denominator_ne
    (threshold parameter : Coordinate) :
    (realLine threshold).denominatorAt parameter ≠ 0 := by
  rw [realLine_denominatorAt]
  exact one_ne_zero

theorem imaginaryLine_denominator_ne
    (threshold parameter : Coordinate) :
    (imaginaryLine threshold).denominatorAt parameter ≠ 0 := by
  rw [imaginaryLine_denominatorAt]
  exact one_ne_zero

@[simp] theorem realLine_numeratorAt
    (threshold parameter : Coordinate) :
    (realLine threshold).numeratorAt parameter = ⟨threshold, parameter⟩ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp [CCL.RationalCurve.RationalCurve.numeratorAt,
      realLine, imaginaryUnit, ofCoordinate,
      RFAP.PathPolynomial.ofCoordinate,
      RFAP.ComputablePolynomial.DensePolynomial.eval,
      RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs]

@[simp] theorem imaginaryLine_numeratorAt
    (threshold parameter : Coordinate) :
    (imaginaryLine threshold).numeratorAt parameter = ⟨parameter, threshold⟩ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp [CCL.RationalCurve.RationalCurve.numeratorAt,
      imaginaryLine, imaginaryCoordinate,
      RFAP.PathPolynomial.ofCoordinate,
      RFAP.ComputablePolynomial.DensePolynomial.eval,
      RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs]

@[simp] theorem realLine_point
    (threshold parameter : Coordinate) :
    (realLine threshold).point parameter = ⟨threshold, parameter⟩ := by
  rw [CCL.RationalCurve.RationalCurve.point,
    realLine_numeratorAt, realLine_denominatorAt]
  have inverseOne : (1 : Gaussian)⁻¹ = 1 :=
    RFAP.ConstructiveGaussian.Gaussian.inv_one_direct
  rw [inverseOne,
    RFAP.ConstructiveGaussian.Gaussian.mul_one]

@[simp] theorem imaginaryLine_point
    (threshold parameter : Coordinate) :
    (imaginaryLine threshold).point parameter = ⟨parameter, threshold⟩ := by
  rw [CCL.RationalCurve.RationalCurve.point,
    imaginaryLine_numeratorAt, imaginaryLine_denominatorAt]
  have inverseOne : (1 : Gaussian)⁻¹ = 1 :=
    RFAP.ConstructiveGaussian.Gaussian.inv_one_direct
  rw [inverseOne,
    RFAP.ConstructiveGaussian.Gaussian.mul_one]

/-- Stereographic parameterization of the centered circle through `base`.
It misses only `-base`, which remains an explicit rational exceptional point. -/
def circle (base : Gaussian) : RationalCurve where
  numerator :=
    ⟨[-base, (ofCoordinate 2 * imaginaryUnit) * base, base]⟩
  denominator := ⟨[1, 0, 1]⟩

@[simp] theorem circle_numeratorAt (base : Gaussian) (parameter : Coordinate) :
    (circle base).numeratorAt parameter =
      base * ⟨1 - parameter ^ 2, 2 * parameter⟩ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp [circle, CCL.RationalCurve.RationalCurve.numeratorAt,
      RFAP.PathPolynomial.ofCoordinate,
      RFAP.ComputablePolynomial.DensePolynomial.eval,
      RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs,
      imaginaryUnit, ofCoordinate] <;>
    ring1

theorem circle_denominatorAt_re
    (base : Gaussian) (parameter : Coordinate) :
    ((circle base).denominatorAt parameter).re = parameter ^ 2 + 1 := by
  change
    (((((0 : Gaussian) * ⟨parameter, 0⟩ + 1) *
        ⟨parameter, 0⟩ + 0) * ⟨parameter, 0⟩ + 1).re) =
      parameter ^ 2 + 1
  simp only [RFAP.ConstructiveGaussian.Gaussian.zero_mul,
    RFAP.ConstructiveGaussian.Gaussian.zero_add,
    RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.add_zero,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.one_re]
  ring1

theorem circle_denominatorAt_im
    (base : Gaussian) (parameter : Coordinate) :
    ((circle base).denominatorAt parameter).im = 0 := by
  change
    (((((0 : Gaussian) * ⟨parameter, 0⟩ + 1) *
        ⟨parameter, 0⟩ + 0) * ⟨parameter, 0⟩ + 1).im) = 0
  simp only [RFAP.ConstructiveGaussian.Gaussian.zero_mul,
    RFAP.ConstructiveGaussian.Gaussian.zero_add,
    RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.add_zero,
    RFAP.ConstructiveGaussian.Gaussian.add_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.one_im]
  ring1

@[simp] theorem circle_denominatorAt
    (base : Gaussian) (parameter : Coordinate) :
    (circle base).denominatorAt parameter =
      ⟨parameter ^ 2 + 1, 0⟩ :=
  RFAP.ConstructiveGaussian.Gaussian.ext
    (circle_denominatorAt_re base parameter)
    (circle_denominatorAt_im base parameter)

theorem circle_denominator_ne (base : Gaussian) (parameter : Coordinate) :
    (circle base).denominatorAt parameter ≠ 0 := by
  rw [circle_denominatorAt]
  intro denominatorZero
  have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re denominatorZero
  have positive : 0 < parameter ^ 2 + 1 :=
    lt_of_le_of_lt
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter)
      (by
        have := RFAP.ConstructiveFraction.add_lt_add_left_direct
          (show (0 : Coordinate) < 1 by decide) (parameter ^ 2)
        calc
          parameter ^ 2 = parameter ^ 2 + 0 := by ring1
          _ < parameter ^ 2 + 1 := this)
  change parameter ^ 2 + 1 = 0 at realZero
  rw [realZero] at positive
  exact (lt_irrefl 0 positive).elim

private theorem sub_square_add_four_product
    (left right : Coordinate) :
    (left - right) ^ 2 + 4 * left * right = (left + right) ^ 2 := by
  have fourAsTwoPlusTwo : (4 : Coordinate) = 2 + 2 := by decide
  have fourProduct : 4 * left * right =
      2 * left * right + 2 * left * right := by
    rw [fourAsTwoPlusTwo, _root_.add_mul, _root_.add_mul]
  rw [sub_sq, add_sq, fourProduct,
    RFAP.ConstructiveFraction.sub_eq_add_neg_direct]
  simp only [RFAP.ConstructiveFraction.add_comm, _root_.add_left_comm,
    add_neg_cancel, _root_.add_zero]

/-- Every finite stereographic parameter lies on the centered circle through
the displayed rational base point. -/
theorem normSq_circle_point (base : Gaussian) (parameter : Coordinate) :
    normSq ((circle base).point parameter) = normSq base := by
  let direction : Gaussian := ⟨1 - parameter ^ 2, 2 * parameter⟩
  let denominatorValue : Gaussian := ⟨parameter ^ 2 + 1, 0⟩
  have directionNorm : normSq direction = (parameter ^ 2 + 1) ^ 2 := by
    dsimp only [direction, normSq]
    rw [mul_pow]
    have twoSquared : (2 : Coordinate) ^ 2 = 4 := by decide
    rw [twoSquared]
    calc
      (1 - parameter ^ 2) ^ 2 + 4 * parameter ^ 2 =
          (1 - parameter ^ 2) ^ 2 + 4 * 1 * parameter ^ 2 := by
        rw [RFAP.ConstructiveFraction.mul_one_direct]
      _ = (1 + parameter ^ 2) ^ 2 :=
        sub_square_add_four_product 1 (parameter ^ 2)
      _ = (parameter ^ 2 + 1) ^ 2 := by
        rw [RFAP.ConstructiveFraction.add_comm]
  have denominatorNorm :
      normSq denominatorValue = (parameter ^ 2 + 1) ^ 2 := by
    dsimp only [denominatorValue, normSq]
    change (parameter ^ 2 + 1) ^ 2 + (0 : Coordinate) ^ 2 =
      (parameter ^ 2 + 1) ^ 2
    simp only [pow_two, RFAP.ConstructiveFraction.zero_mul_direct,
      _root_.add_zero]
  have denominatorNonzero : denominatorValue ≠ 0 := by
    simpa only [circle_denominatorAt] using
      circle_denominator_ne base parameter
  have denominatorNormNonzero : normSq denominatorValue ≠ 0 :=
    fun zero => denominatorNonzero (normSq_eq_zero.mp zero)
  have displayedNormNonzero : (parameter ^ 2 + 1) ^ 2 ≠ 0 := by
    rw [← denominatorNorm]
    exact denominatorNormNonzero
  rw [CCL.RationalCurve.RationalCurve.point,
    circle_numeratorAt, circle_denominatorAt]
  change normSq ((base * direction) * denominatorValue⁻¹) = normSq base
  rw [normSq_mul, normSq_mul]
  rw [inv_eq, normSq_inv denominatorValue denominatorNonzero,
    directionNorm, denominatorNorm,
    RFAP.ConstructiveFraction.mul_assoc,
    RFAP.ConstructiveFraction.mul_inv_cancel _ displayedNormNonzero,
    RFAP.ConstructiveFraction.mul_one_direct]

/-! ## Reciprocal circle chart -/

/-- The reciprocal stereographic chart of the same centered circle.  Its
zero parameter is the primary chart's missing point `-base`; together the two
finite charts cover the projective parameter line. -/
def reciprocalCircle (base : Gaussian) : RationalCurve where
  numerator :=
    ⟨[base, (ofCoordinate 2 * imaginaryUnit) * base, -base]⟩
  denominator := ⟨[1, 0, 1]⟩

@[simp] theorem reciprocalCircle_numeratorAt
    (base : Gaussian) (parameter : Coordinate) :
    (reciprocalCircle base).numeratorAt parameter =
      base * ⟨parameter ^ 2 - 1, 2 * parameter⟩ := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp [reciprocalCircle,
      CCL.RationalCurve.RationalCurve.numeratorAt,
      RFAP.PathPolynomial.ofCoordinate,
      RFAP.ComputablePolynomial.DensePolynomial.eval,
      RFAP.ComputablePolynomial.DensePolynomial.evalCoeffs,
      imaginaryUnit, ofCoordinate] <;>
    ring1

theorem reciprocalCircle_denominatorAt_re
    (base : Gaussian) (parameter : Coordinate) :
    ((reciprocalCircle base).denominatorAt parameter).re =
      parameter ^ 2 + 1 := by
  change
    (((((0 : Gaussian) * ⟨parameter, 0⟩ + 1) *
        ⟨parameter, 0⟩ + 0) * ⟨parameter, 0⟩ + 1).re) =
      parameter ^ 2 + 1
  simp only [RFAP.ConstructiveGaussian.Gaussian.zero_mul,
    RFAP.ConstructiveGaussian.Gaussian.zero_add,
    RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.add_zero,
    RFAP.ConstructiveGaussian.Gaussian.add_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.one_re]
  ring1

theorem reciprocalCircle_denominatorAt_im
    (base : Gaussian) (parameter : Coordinate) :
    ((reciprocalCircle base).denominatorAt parameter).im = 0 := by
  change
    (((((0 : Gaussian) * ⟨parameter, 0⟩ + 1) *
        ⟨parameter, 0⟩ + 0) * ⟨parameter, 0⟩ + 1).im) = 0
  simp only [RFAP.ConstructiveGaussian.Gaussian.zero_mul,
    RFAP.ConstructiveGaussian.Gaussian.zero_add,
    RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.add_zero,
    RFAP.ConstructiveGaussian.Gaussian.add_im,
    RFAP.ConstructiveGaussian.Gaussian.mul_im,
    RFAP.ConstructiveGaussian.Gaussian.one_im]
  ring1

@[simp] theorem reciprocalCircle_denominatorAt
    (base : Gaussian) (parameter : Coordinate) :
    (reciprocalCircle base).denominatorAt parameter =
      ⟨parameter ^ 2 + 1, 0⟩ :=
  RFAP.ConstructiveGaussian.Gaussian.ext
    (reciprocalCircle_denominatorAt_re base parameter)
    (reciprocalCircle_denominatorAt_im base parameter)

theorem reciprocalCircle_denominator_ne
    (base : Gaussian) (parameter : Coordinate) :
    (reciprocalCircle base).denominatorAt parameter ≠ 0 := by
  rw [reciprocalCircle_denominatorAt]
  intro denominatorZero
  have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re
    denominatorZero
  have positive : 0 < parameter ^ 2 + 1 :=
    lt_of_le_of_lt
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter)
      (by
        have := RFAP.ConstructiveFraction.add_lt_add_left_direct
          (show (0 : Coordinate) < 1 by decide) (parameter ^ 2)
        calc
          parameter ^ 2 = parameter ^ 2 + 0 := by ring1
          _ < parameter ^ 2 + 1 := this)
  change parameter ^ 2 + 1 = 0 at realZero
  rw [realZero] at positive
  exact (lt_irrefl 0 positive).elim

@[simp] theorem reciprocalCircle_point_zero (base : Gaussian) :
    (reciprocalCircle base).point 0 = -base := by
  rw [CCL.RationalCurve.RationalCurve.point,
    reciprocalCircle_numeratorAt, reciprocalCircle_denominatorAt]
  change (base * ⟨-1, 0⟩) * (1 : Gaussian)⁻¹ = -base
  have inverseOne : (1 : Gaussian)⁻¹ = 1 :=
    RFAP.ConstructiveGaussian.Gaussian.inv_one_direct
  rw [inverseOne, RFAP.ConstructiveGaussian.Gaussian.mul_one]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im,
      RFAP.ConstructiveGaussian.Gaussian.neg_re,
      RFAP.ConstructiveGaussian.Gaussian.neg_im] <;>
    ring1

/-- Every finite reciprocal parameter lies on the same centered circle. -/
theorem normSq_reciprocalCircle_point
    (base : Gaussian) (parameter : Coordinate) :
    normSq ((reciprocalCircle base).point parameter) = normSq base := by
  let direction : Gaussian := ⟨parameter ^ 2 - 1, 2 * parameter⟩
  let denominatorValue : Gaussian := ⟨parameter ^ 2 + 1, 0⟩
  have directionNorm : normSq direction = (parameter ^ 2 + 1) ^ 2 := by
    dsimp only [direction, normSq]
    rw [mul_pow]
    have twoSquared : (2 : Coordinate) ^ 2 = 4 := by decide
    rw [twoSquared]
    calc
      (parameter ^ 2 - 1) ^ 2 + 4 * parameter ^ 2 =
          (parameter ^ 2 - 1) ^ 2 + 4 * parameter ^ 2 * 1 := by
        rw [RFAP.ConstructiveFraction.mul_one_direct]
      _ = (parameter ^ 2 + 1) ^ 2 :=
        sub_square_add_four_product (parameter ^ 2) 1
  have denominatorNorm :
      normSq denominatorValue = (parameter ^ 2 + 1) ^ 2 := by
    dsimp only [denominatorValue, normSq]
    change (parameter ^ 2 + 1) ^ 2 + (0 : Coordinate) ^ 2 =
      (parameter ^ 2 + 1) ^ 2
    simp only [pow_two, RFAP.ConstructiveFraction.zero_mul_direct,
      _root_.add_zero]
  have denominatorNonzero : denominatorValue ≠ 0 := by
    simpa only [reciprocalCircle_denominatorAt] using
      reciprocalCircle_denominator_ne base parameter
  have denominatorNormNonzero : normSq denominatorValue ≠ 0 :=
    fun zero => denominatorNonzero (normSq_eq_zero.mp zero)
  have displayedNormNonzero : (parameter ^ 2 + 1) ^ 2 ≠ 0 := by
    rw [← denominatorNorm]
    exact denominatorNormNonzero
  rw [CCL.RationalCurve.RationalCurve.point,
    reciprocalCircle_numeratorAt, reciprocalCircle_denominatorAt]
  change normSq ((base * direction) * denominatorValue⁻¹) = normSq base
  rw [normSq_mul, normSq_mul]
  rw [inv_eq, normSq_inv denominatorValue denominatorNonzero,
    directionNorm, denominatorNorm,
    RFAP.ConstructiveFraction.mul_assoc,
    RFAP.ConstructiveFraction.mul_inv_cancel _ displayedNormNonzero,
    RFAP.ConstructiveFraction.mul_one_direct]

/-- Changing the displayed circle base multiplies every primary-chart point
by that base. -/
theorem circle_point_scale
    (base : Gaussian) (parameter : Coordinate) :
    (circle base).point parameter =
      base * (circle 1).point parameter := by
  rw [CCL.RationalCurve.RationalCurve.point,
    CCL.RationalCurve.RationalCurve.point,
    circle_numeratorAt, circle_numeratorAt,
    circle_denominatorAt, circle_denominatorAt]
  change (base * ⟨1 - parameter ^ 2, 2 * parameter⟩) *
      (⟨parameter ^ 2 + 1, 0⟩ : Gaussian)⁻¹ =
    base * ((1 * ⟨1 - parameter ^ 2, 2 * parameter⟩) *
      (⟨parameter ^ 2 + 1, 0⟩ : Gaussian)⁻¹)
  rw [RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.mul_assoc]

/-- Changing the displayed circle base multiplies every reciprocal-chart
point by that base. -/
theorem reciprocalCircle_point_scale
    (base : Gaussian) (parameter : Coordinate) :
    (reciprocalCircle base).point parameter =
      base * (reciprocalCircle 1).point parameter := by
  rw [CCL.RationalCurve.RationalCurve.point,
    CCL.RationalCurve.RationalCurve.point,
    reciprocalCircle_numeratorAt, reciprocalCircle_numeratorAt,
    reciprocalCircle_denominatorAt, reciprocalCircle_denominatorAt]
  change (base * ⟨parameter ^ 2 - 1, 2 * parameter⟩) *
      (⟨parameter ^ 2 + 1, 0⟩ : Gaussian)⁻¹ =
    base * ((1 * ⟨parameter ^ 2 - 1, 2 * parameter⟩) *
      (⟨parameter ^ 2 + 1, 0⟩ : Gaussian)⁻¹)
  rw [RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.mul_assoc]

theorem realLine_point_injective (threshold : Coordinate) :
    Function.Injective (realLine threshold).point := by
  intro left right equal
  have imaginary := congrArg RFAP.ConstructiveGaussian.Gaussian.im equal
  simpa only [realLine_point] using imaginary

theorem imaginaryLine_point_injective (threshold : Coordinate) :
    Function.Injective (imaginaryLine threshold).point := by
  intro left right equal
  have real := congrArg RFAP.ConstructiveGaussian.Gaussian.re equal
  simpa only [imaginaryLine_point] using real

private theorem circle_one_coordinate_products (parameter : Coordinate) :
    let point := (circle 1).point parameter
    point.re * (parameter ^ 2 + 1) = 1 - parameter ^ 2 ∧
      point.im * (parameter ^ 2 + 1) = 2 * parameter := by
  let point := (circle 1).point parameter
  have denominatorNonzero := circle_denominator_ne 1 parameter
  have numeratorIdentity :=
    CCL.RationalCurve.RationalCurve.numeratorAt_eq_point_mul_denominatorAt
      (circle 1) parameter denominatorNonzero
  have realIdentity :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.re numeratorIdentity
  have imaginaryIdentity :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.im numeratorIdentity
  rw [circle_numeratorAt, circle_denominatorAt] at realIdentity imaginaryIdentity
  simp only [RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im] at realIdentity imaginaryIdentity
  constructor
  · change point.re * (parameter ^ 2 + 1) = 1 - parameter ^ 2
    change 1 - parameter ^ 2 =
      point.re * (parameter ^ 2 + 1) - point.im * 0 at realIdentity
    calc
      point.re * (parameter ^ 2 + 1) =
          point.re * (parameter ^ 2 + 1) - point.im * 0 := by ring1
      _ = 1 - parameter ^ 2 := realIdentity.symm
  · change point.im * (parameter ^ 2 + 1) = 2 * parameter
    change 2 * parameter =
      point.re * 0 + point.im * (parameter ^ 2 + 1) at imaginaryIdentity
    simpa only [RFAP.ConstructiveFraction.mul_zero_direct,
      RFAP.ConstructiveFraction.zero_add] using imaginaryIdentity.symm

private theorem reciprocalCircle_one_coordinate_products
    (parameter : Coordinate) :
    let point := (reciprocalCircle 1).point parameter
    point.re * (parameter ^ 2 + 1) = parameter ^ 2 - 1 ∧
      point.im * (parameter ^ 2 + 1) = 2 * parameter := by
  let point := (reciprocalCircle 1).point parameter
  have denominatorNonzero := reciprocalCircle_denominator_ne 1 parameter
  have numeratorIdentity :=
    CCL.RationalCurve.RationalCurve.numeratorAt_eq_point_mul_denominatorAt
      (reciprocalCircle 1) parameter denominatorNonzero
  have realIdentity :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.re numeratorIdentity
  have imaginaryIdentity :=
    congrArg RFAP.ConstructiveGaussian.Gaussian.im numeratorIdentity
  rw [reciprocalCircle_numeratorAt,
    reciprocalCircle_denominatorAt] at realIdentity imaginaryIdentity
  simp only [RFAP.ConstructiveGaussian.Gaussian.one_mul,
    RFAP.ConstructiveGaussian.Gaussian.mul_re,
    RFAP.ConstructiveGaussian.Gaussian.mul_im] at realIdentity imaginaryIdentity
  constructor
  · change point.re * (parameter ^ 2 + 1) = parameter ^ 2 - 1
    change parameter ^ 2 - 1 =
      point.re * (parameter ^ 2 + 1) - point.im * 0 at realIdentity
    calc
      point.re * (parameter ^ 2 + 1) =
          point.re * (parameter ^ 2 + 1) - point.im * 0 := by ring1
      _ = parameter ^ 2 - 1 := realIdentity.symm
  · change point.im * (parameter ^ 2 + 1) = 2 * parameter
    change 2 * parameter =
      point.re * 0 + point.im * (parameter ^ 2 + 1) at imaginaryIdentity
    simpa only [RFAP.ConstructiveFraction.mul_zero_direct,
      RFAP.ConstructiveFraction.zero_add] using imaginaryIdentity.symm

/-- Recover the primary stereographic parameter from its displayed rational
point.  This is a finite algebraic inverse, not a choice of angle. -/
theorem circle_one_parameter_of_point (parameter : Coordinate) :
    let point := (circle 1).point parameter
    point.im / (1 + point.re) = parameter := by
  let point := (circle 1).point parameter
  let denominator := parameter ^ 2 + 1
  have denominatorPositive : 0 < denominator := by
    dsimp only [denominator]
    exact lt_of_le_of_lt
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter)
      (by
        have added := RFAP.ConstructiveFraction.add_lt_add_left_direct
          (show (0 : Coordinate) < 1 by decide) (parameter ^ 2)
        calc
          parameter ^ 2 = parameter ^ 2 + 0 := by ring1
          _ < parameter ^ 2 + 1 := added)
  have products := circle_one_coordinate_products parameter
  have sumProduct : (1 + point.re) * denominator = 2 := by
    calc
      (1 + point.re) * denominator =
          denominator + point.re * denominator := by ring1
      _ = denominator + (1 - parameter ^ 2) := by rw [products.1]
      _ = 2 := by dsimp only [denominator]; ring1
  have sumNonzero : 1 + point.re ≠ 0 := by
    intro zero
    rw [zero, RFAP.ConstructiveFraction.zero_mul_direct] at sumProduct
    exact (show (0 : Coordinate) ≠ 2 by decide) sumProduct
  have factorization : point.im = parameter * (1 + point.re) := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      denominatorPositive.ne'
    calc
      point.im * denominator = 2 * parameter := products.2
      _ = parameter * 2 := RFAP.ConstructiveFraction.mul_comm _ _
      _ = parameter * ((1 + point.re) * denominator) := by rw [sumProduct]
      _ = (parameter * (1 + point.re)) * denominator :=
        (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
  change point.im / (1 + point.re) = parameter
  rw [factorization, RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveFraction.mul_assoc,
    RFAP.ConstructiveFraction.mul_inv_cancel _ sumNonzero,
    RFAP.ConstructiveFraction.mul_one_direct]

/-- Recover the reciprocal stereographic parameter from its displayed
rational point. -/
theorem reciprocalCircle_one_parameter_of_point (parameter : Coordinate) :
    let point := (reciprocalCircle 1).point parameter
    point.im / (1 - point.re) = parameter := by
  let point := (reciprocalCircle 1).point parameter
  let denominator := parameter ^ 2 + 1
  have denominatorPositive : 0 < denominator := by
    dsimp only [denominator]
    exact lt_of_le_of_lt
      (RFAP.ConstructiveFraction.sq_nonneg_direct parameter)
      (by
        have added := RFAP.ConstructiveFraction.add_lt_add_left_direct
          (show (0 : Coordinate) < 1 by decide) (parameter ^ 2)
        calc
          parameter ^ 2 = parameter ^ 2 + 0 := by ring1
          _ < parameter ^ 2 + 1 := added)
  have products := reciprocalCircle_one_coordinate_products parameter
  have differenceProduct : (1 - point.re) * denominator = 2 := by
    calc
      (1 - point.re) * denominator =
          denominator - point.re * denominator := by ring1
      _ = denominator - (parameter ^ 2 - 1) := by rw [products.1]
      _ = 2 := by dsimp only [denominator]; ring1
  have differenceNonzero : 1 - point.re ≠ 0 := by
    intro zero
    rw [zero, RFAP.ConstructiveFraction.zero_mul_direct] at differenceProduct
    exact (show (0 : Coordinate) ≠ 2 by decide) differenceProduct
  have factorization : point.im = parameter * (1 - point.re) := by
    apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
      denominatorPositive.ne'
    calc
      point.im * denominator = 2 * parameter := products.2
      _ = parameter * 2 := RFAP.ConstructiveFraction.mul_comm _ _
      _ = parameter * ((1 - point.re) * denominator) := by
        rw [differenceProduct]
      _ = (parameter * (1 - point.re)) * denominator :=
        (RFAP.ConstructiveFraction.mul_assoc _ _ _).symm
  change point.im / (1 - point.re) = parameter
  rw [factorization, RFAP.ExplicitField.div_eq_mul_inv,
    RFAP.ConstructiveFraction.mul_assoc,
    RFAP.ConstructiveFraction.mul_inv_cancel _ differenceNonzero,
    RFAP.ConstructiveFraction.mul_one_direct]

theorem circle_one_point_injective : Function.Injective (circle 1).point := by
  intro left right equal
  have recovered := congrArg
    (fun point : Gaussian => point.im / (1 + point.re)) equal
  simpa only [circle_one_parameter_of_point] using recovered

theorem reciprocalCircle_one_point_injective :
    Function.Injective (reciprocalCircle 1).point := by
  intro left right equal
  have recovered := congrArg
    (fun point : Gaussian => point.im / (1 - point.re)) equal
  simpa only [reciprocalCircle_one_parameter_of_point] using recovered

theorem circle_point_injective (base : Gaussian) (baseNonzero : base ≠ 0) :
    Function.Injective (circle base).point := by
  intro left right equal
  have equal' : base * (circle 1).point left =
      base * (circle 1).point right := by
    calc
      base * (circle 1).point left = (circle base).point left :=
        (circle_point_scale base left).symm
      _ = (circle base).point right := equal
      _ = base * (circle 1).point right := circle_point_scale base right
  apply circle_one_point_injective
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne baseNonzero
  calc
    (circle 1).point left * base = base * (circle 1).point left :=
      RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
    _ = base * (circle 1).point right := equal'
    _ = (circle 1).point right * base :=
      RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _

theorem reciprocalCircle_point_injective
    (base : Gaussian) (baseNonzero : base ≠ 0) :
    Function.Injective (reciprocalCircle base).point := by
  intro left right equal
  have equal' : base * (reciprocalCircle 1).point left =
      base * (reciprocalCircle 1).point right := by
    calc
      base * (reciprocalCircle 1).point left =
          (reciprocalCircle base).point left :=
        (reciprocalCircle_point_scale base left).symm
      _ = (reciprocalCircle base).point right := equal
      _ = base * (reciprocalCircle 1).point right :=
        reciprocalCircle_point_scale base right
  apply reciprocalCircle_one_point_injective
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne baseNonzero
  calc
    (reciprocalCircle 1).point left * base =
        base * (reciprocalCircle 1).point left :=
      RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
    _ = base * (reciprocalCircle 1).point right := equal'
    _ = (reciprocalCircle 1).point right * base :=
      RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _

/-- Centered circle of squared radius `2^exponent`, with the displayed base
point `(1+i)^exponent`. -/
def dyadicCircle (exponent : Nat) : RationalCurve :=
  circle (natPow gamma exponent)

theorem normSq_dyadicCircle_point (exponent : Nat) (parameter : Coordinate) :
    normSq ((dyadicCircle exponent).point parameter) =
      (2 : Coordinate) ^ exponent := by
  rw [dyadicCircle, normSq_circle_point, normSq_natPow, normSq_gamma]

/-- Centered circle of squared radius `1 / 2^exponent`. -/
def inverseDyadicCircle (exponent : Nat) : RationalCurve :=
  circle ((natPow gamma exponent)⁻¹)

theorem normSq_inverseDyadicCircle_point
    (exponent : Nat) (parameter : Coordinate) :
    normSq ((inverseDyadicCircle exponent).point parameter) =
      ((2 : Coordinate) ^ exponent)⁻¹ := by
  have powerNonzero : natPow gamma exponent ≠ 0 :=
    natPow_ne_zero_direct gamma (by
      intro gammaZero
      have realZero := congrArg RFAP.ConstructiveGaussian.Gaussian.re gammaZero
      exact RFAP.ConstructiveFraction.zero_ne_one realZero.symm) exponent
  rw [inverseDyadicCircle, normSq_circle_point]
  rw [inv_eq, normSq_inv _ powerNonzero, normSq_natPow, normSq_gamma]

/-- Circle for the upper inequality in the initial-low radial bracket:
`2^exponent * normSq z = 2`. -/
def lowUpperCircle : Nat → RationalCurve
  | 0 => dyadicCircle 1
  | exponent + 1 => inverseDyadicCircle exponent

theorem scaled_normSq_lowUpperCircle_point
    (exponent : Nat) (parameter : Coordinate) :
    (2 : Coordinate) ^ exponent *
        normSq ((lowUpperCircle exponent).point parameter) = 2 := by
  cases exponent with
  | zero =>
      simp only [lowUpperCircle, pow_zero,
        normSq_dyadicCircle_point, pow_one]
      exact one_mul 2
  | succ exponent =>
      rw [lowUpperCircle, normSq_inverseDyadicCircle_point, pow_succ]
      have powerNonzero : (2 : Coordinate) ^ exponent ≠ 0 := by
        intro powerZero
        have powerPositive :=
          RFAP.ConstructiveFraction.pow_pos_direct
            (show (0 : Coordinate) < 2 by decide) exponent
        rw [powerZero] at powerPositive
        exact (lt_irrefl 0 powerPositive).elim
      calc
        ((2 : Coordinate) ^ exponent * 2) *
            ((2 : Coordinate) ^ exponent)⁻¹ =
          2 * ((2 : Coordinate) ^ exponent *
            ((2 : Coordinate) ^ exponent)⁻¹) := by
              calc
                ((2 : Coordinate) ^ exponent * 2) *
                    ((2 : Coordinate) ^ exponent)⁻¹ =
                  (2 * (2 : Coordinate) ^ exponent) *
                    ((2 : Coordinate) ^ exponent)⁻¹ := by
                      rw [RFAP.ConstructiveFraction.mul_comm
                        ((2 : Coordinate) ^ exponent) 2]
                _ = 2 * ((2 : Coordinate) ^ exponent *
                    ((2 : Coordinate) ^ exponent)⁻¹) :=
                  RFAP.ConstructiveFraction.mul_assoc _ _ _
        _ = 2 * 1 := by
          rw [RFAP.ConstructiveFraction.mul_inv_cancel _ powerNonzero]
        _ = 2 := RFAP.ConstructiveFraction.mul_one_direct _

end CCL.CanonicalCurves
