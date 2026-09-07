import RationalRotations.HalfSpreads

/-!
# Rational rotations, section 9: the anchor product

The partial product is stored by its displayed finite vector formula.  Its
composition law is proved directly in coordinates, rather than transferred
from an ordered or infinite field.  This keeps the construction executable
over every explicit field in its stated domain.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- The scalar whose nonvanishing defines the affine anchor product. -/
def anchorProductDenominator (left right : Vector K) : K :=
  1 - Vector.dot left right

/-- The numerator that remains meaningful when the affine product is
undefined and its composed rotation is a half turn. -/
def anchorProductNumerator (left right : Vector K) : Vector K :=
  Vector.sub (Vector.add left right) (Vector.cross left right)

/-- Definition 45: the partial product of two anchor vectors. -/
def anchorProduct (left right : Vector K)
    (_defined : anchorProductDenominator left right ≠ 0) : Vector K :=
  Vector.scale (1 / anchorProductDenominator left right)
    (anchorProductNumerator left right)

/-- The matrix-side denominator from Definition 45. -/
def anchorMatrixProductDenominator (left right : Matrix3 K) : K :=
  1 - anchorForm left right

/-- Definition 45 on displayed anchor matrices. -/
def anchorMatrixProduct (left right : Matrix3 K)
    (_defined : anchorMatrixProductDenominator left right ≠ 0) : Matrix3 K :=
  Matrix3.scale (1 / anchorMatrixProductDenominator left right)
    (Matrix3.add (Matrix3.add left right)
      (Matrix3.sub (Matrix3.mul left right) (Matrix3.mul right left)))

theorem anchorProductDenominator_anchor (left right : Vector K)
    (twoNonzero : (2 : K) ≠ 0) :
    anchorMatrixProductDenominator (anchor left) (anchor right) =
      anchorProductDenominator left right := by
  unfold anchorMatrixProductDenominator anchorProductDenominator
  rw [anchorForm_anchor left right twoNonzero]

/-- The vector and matrix formulas in Definition 45 agree under the anchor
bijection. -/
theorem anchor_anchorProduct (left right : Vector K)
    (defined : anchorProductDenominator left right ≠ 0) :
    anchor (anchorProduct left right defined) =
      Matrix3.scale (1 / anchorProductDenominator left right)
        (Matrix3.add (Matrix3.add (anchor left) (anchor right))
          (Matrix3.sub (Matrix3.mul (anchor left) (anchor right))
            (Matrix3.mul (anchor right) (anchor left)))) := by
  ext <;> unfold anchorProduct anchorProductNumerator
    anchorProductDenominator Vector.sub Vector.add Vector.scale Vector.cross
    anchor Matrix3.scale Matrix3.add Matrix3.sub Matrix3.mul <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1

theorem anchorMatrixProduct_anchor (left right : Vector K)
    (twoNonzero : (2 : K) ≠ 0)
    (defined : anchorProductDenominator left right ≠ 0) :
    anchorMatrixProduct (anchor left) (anchor right)
        (by rwa [anchorProductDenominator_anchor left right twoNonzero]) =
      anchor (anchorProduct left right defined) := by
  rw [anchor_anchorProduct]
  unfold anchorMatrixProduct
  rw [anchorProductDenominator_anchor left right twoNonzero]

private theorem cap_congr_vector {first second : Vector K}
    (equal : first = second)
    (firstDefined : capDenominator first ≠ 0)
    (secondDefined : capDenominator second ≠ 0) :
    cap first firstDefined = cap second secondDefined := by
  subst second
  rfl

/-- The homogeneous quadratic denominator used internally to clear the
affine chart without introducing a limit or an infinite object. -/
private def homogeneousNorm (scalar : K) (vector : Vector K) : K :=
  scalar ^ 2 + vector.quadrance

/-- The numerator of the homogeneous rotation formula, displayed in the
paper's row-vector convention. -/
private def homogeneousRotationNumerator (scalar : K)
    (vector : Vector K) : Matrix3 K :=
  ⟨scalar ^ 2 + vector.t ^ 2 - vector.r ^ 2 - vector.s ^ 2,
    2 * (scalar * vector.s + vector.r * vector.t),
    2 * (-scalar * vector.r + vector.s * vector.t),
    2 * (-scalar * vector.s + vector.r * vector.t),
    scalar ^ 2 - vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2,
    2 * (scalar * vector.t + vector.r * vector.s),
    2 * (scalar * vector.r + vector.s * vector.t),
    2 * (-scalar * vector.t + vector.r * vector.s),
    scalar ^ 2 - vector.t ^ 2 - vector.r ^ 2 + vector.s ^ 2⟩

private theorem cap_eq_scaled_homogeneousNumerator (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    cap vector defined =
      Matrix3.scale (capDenominator vector)⁻¹
        (homogeneousRotationNumerator 1 vector) := by
  rw [cap_coordinate_formula]
  ext <;> unfold homogeneousRotationNumerator Matrix3.scale <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1

/-- Euler's four-square identity in the specialization needed by the affine
anchor product. -/
private theorem homogeneousNorm_anchorProductNumerator
    (left right : Vector K) :
    homogeneousNorm (anchorProductDenominator left right)
        (anchorProductNumerator left right) =
      capDenominator left * capDenominator right := by
  unfold homogeneousNorm anchorProductDenominator anchorProductNumerator
    capDenominator Vector.quadrance Vector.dot Vector.sub Vector.add
    Vector.cross
  ring1

/-- The denominator-cleared coordinate composition identity. -/
private theorem homogeneousRotationNumerator_product
    (left right : Vector K) :
    Matrix3.mul (homogeneousRotationNumerator 1 left)
        (homogeneousRotationNumerator 1 right) =
      homogeneousRotationNumerator (anchorProductDenominator left right)
        (anchorProductNumerator left right) := by
  ext <;> unfold homogeneousRotationNumerator anchorProductDenominator
    anchorProductNumerator Matrix3.mul Vector.sub Vector.add Vector.cross
    Vector.dot <;> ring1

private theorem homogeneousRotationNumerator_scale (factor scalar : K)
    (vector : Vector K) :
    homogeneousRotationNumerator (factor * scalar)
        (Vector.scale factor vector) =
      Matrix3.scale (factor ^ 2)
        (homogeneousRotationNumerator scalar vector) := by
  ext <;> unfold homogeneousRotationNumerator Matrix3.scale Vector.scale <;>
    ring1

private theorem anchorProduct_eq_inverse_scale (left right : Vector K)
    (defined : anchorProductDenominator left right ≠ 0) :
    anchorProduct left right defined =
      Vector.scale (anchorProductDenominator left right)⁻¹
        (anchorProductNumerator left right) := by
  unfold anchorProduct
  congr 1
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

private theorem homogeneousRotationNumerator_anchorProduct
    (left right : Vector K)
    (defined : anchorProductDenominator left right ≠ 0) :
    homogeneousRotationNumerator 1 (anchorProduct left right defined) =
      Matrix3.scale ((anchorProductDenominator left right)⁻¹ ^ 2)
        (homogeneousRotationNumerator
          (anchorProductDenominator left right)
          (anchorProductNumerator left right)) := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (anchorProductDenominator left right) defined
  have reverseCancel :
      (anchorProductDenominator left right)⁻¹ *
          anchorProductDenominator left right = 1 := by
    calc
      (anchorProductDenominator left right)⁻¹ *
          anchorProductDenominator left right =
        anchorProductDenominator left right *
          (anchorProductDenominator left right)⁻¹ := by ring1
      _ = 1 := cancel
  rw [anchorProduct_eq_inverse_scale]
  conv_lhs =>
    lhs
    rw [← reverseCancel]
  exact homogeneousRotationNumerator_scale
    (anchorProductDenominator left right)⁻¹
    (anchorProductDenominator left right)
    (anchorProductNumerator left right)

private theorem homogeneousNorm_scale (factor scalar : K)
    (vector : Vector K) :
    homogeneousNorm (factor * scalar) (Vector.scale factor vector) =
      factor ^ 2 * homogeneousNorm scalar vector := by
  unfold homogeneousNorm Vector.quadrance Vector.dot Vector.scale
  ring1

/-- The result denominator is cached algebraically from the two input
denominators and the affine-chart denominator. -/
theorem capDenominator_anchorProduct (left right : Vector K)
    (defined : anchorProductDenominator left right ≠ 0) :
    capDenominator (anchorProduct left right defined) =
      (anchorProductDenominator left right)⁻¹ ^ 2 *
        (capDenominator left * capDenominator right) := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (anchorProductDenominator left right) defined
  have reverseCancel :
      (anchorProductDenominator left right)⁻¹ *
          anchorProductDenominator left right = 1 := by
    calc
      (anchorProductDenominator left right)⁻¹ *
          anchorProductDenominator left right =
        anchorProductDenominator left right *
          (anchorProductDenominator left right)⁻¹ := by ring1
      _ = 1 := cancel
  calc
    capDenominator (anchorProduct left right defined) =
        homogeneousNorm 1 (anchorProduct left right defined) := by
      unfold capDenominator homogeneousNorm
      ring1
    _ = homogeneousNorm
        ((anchorProductDenominator left right)⁻¹ *
          anchorProductDenominator left right)
        (Vector.scale (anchorProductDenominator left right)⁻¹
          (anchorProductNumerator left right)) := by
      rw [reverseCancel, anchorProduct_eq_inverse_scale]
    _ = (anchorProductDenominator left right)⁻¹ ^ 2 *
        homogeneousNorm (anchorProductDenominator left right)
          (anchorProductNumerator left right) :=
      homogeneousNorm_scale _ _ _
    _ = (anchorProductDenominator left right)⁻¹ ^ 2 *
        (capDenominator left * capDenominator right) := by
      rw [homogeneousNorm_anchorProductNumerator]

theorem capDenominator_anchorProduct_ne_zero (left right : Vector K)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0)
    (productDefined : anchorProductDenominator left right ≠ 0) :
    capDenominator (anchorProduct left right productDefined) ≠ 0 := by
  rw [capDenominator_anchorProduct left right productDefined]
  exact RFAP.ExplicitField.mul_ne_zero
    (by
      simpa only [pow_two] using RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.inv_ne_zero productDefined)
        (RFAP.ExplicitField.inv_ne_zero productDefined))
    (RFAP.ExplicitField.mul_ne_zero leftDefined rightDefined)

private theorem inverse_eq_of_mul_eq_one {value candidate : K}
    (valueNonzero : value ≠ 0) (certificate : value * candidate = 1) :
    value⁻¹ = candidate := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel value valueNonzero
  calc
    value⁻¹ = value⁻¹ * 1 := by rw [mul_one]
    _ = value⁻¹ * (value * candidate) := by rw [certificate]
    _ = (value * value⁻¹) * candidate := by ring1
    _ = candidate := by rw [cancel, one_mul]

private theorem inverse_product {left right : K}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    (left * right)⁻¹ = left⁻¹ * right⁻¹ := by
  apply inverse_eq_of_mul_eq_one
    (RFAP.ExplicitField.mul_ne_zero leftNonzero rightNonzero)
  have leftCancel := RFAP.ExplicitField.mul_inv_cancel left leftNonzero
  have rightCancel := RFAP.ExplicitField.mul_inv_cancel right rightNonzero
  calc
    left * right * (left⁻¹ * right⁻¹) =
        (left * left⁻¹) * (right * right⁻¹) := by ring1
    _ = 1 := by rw [leftCancel, rightCancel, one_mul]

private theorem cap_anchorProduct_eq_scaled_homogeneousNumerator
    (left right : Vector K)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0)
    (productDefined : anchorProductDenominator left right ≠ 0) :
    cap (anchorProduct left right productDefined)
        (capDenominator_anchorProduct_ne_zero left right leftDefined
          rightDefined productDefined) =
      Matrix3.scale
        (homogeneousNorm (anchorProductDenominator left right)
          (anchorProductNumerator left right))⁻¹
        (homogeneousRotationNumerator
          (anchorProductDenominator left right)
          (anchorProductNumerator left right)) := by
  let result := anchorProduct left right productDefined
  let resultDefined := capDenominator_anchorProduct_ne_zero left right
    leftDefined rightDefined productDefined
  have resultCancel := RFAP.ExplicitField.mul_inv_cancel
    (capDenominator result) resultDefined
  have normNonzero :
      homogeneousNorm (anchorProductDenominator left right)
          (anchorProductNumerator left right) ≠ 0 := by
    rw [homogeneousNorm_anchorProductNumerator]
    exact RFAP.ExplicitField.mul_ne_zero leftDefined rightDefined
  have normCancel := RFAP.ExplicitField.mul_inv_cancel
    (homogeneousNorm (anchorProductDenominator left right)
      (anchorProductNumerator left right)) normNonzero
  have coefficient :
      (capDenominator result)⁻¹ *
          (anchorProductDenominator left right)⁻¹ ^ 2 =
        (homogeneousNorm (anchorProductDenominator left right)
          (anchorProductNumerator left right))⁻¹ := by
    calc
      (capDenominator result)⁻¹ *
          (anchorProductDenominator left right)⁻¹ ^ 2 =
        (capDenominator result)⁻¹ *
          (anchorProductDenominator left right)⁻¹ ^ 2 *
          (homogeneousNorm (anchorProductDenominator left right)
            (anchorProductNumerator left right) *
            (homogeneousNorm (anchorProductDenominator left right)
              (anchorProductNumerator left right))⁻¹) := by
          rw [normCancel, mul_one]
      _ = ((capDenominator result)⁻¹ * capDenominator result) *
          (homogeneousNorm (anchorProductDenominator left right)
            (anchorProductNumerator left right))⁻¹ := by
        rw [capDenominator_anchorProduct left right productDefined,
          homogeneousNorm_anchorProductNumerator]
        ring1
      _ = (homogeneousNorm (anchorProductDenominator left right)
          (anchorProductNumerator left right))⁻¹ := by
        rw [show (capDenominator result)⁻¹ * capDenominator result = 1 by
          calc
            (capDenominator result)⁻¹ * capDenominator result =
                capDenominator result * (capDenominator result)⁻¹ := by ring1
            _ = 1 := resultCancel,
          one_mul]
  rw [cap_eq_scaled_homogeneousNumerator,
    homogeneousRotationNumerator_anchorProduct, Matrix3.scale_scale,
    coefficient]

private theorem cap_mul_cap_eq_scaled_homogeneousNumerator
    (left right : Vector K)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0) :
    Matrix3.mul (cap left leftDefined) (cap right rightDefined) =
      Matrix3.scale
        ((capDenominator left)⁻¹ * (capDenominator right)⁻¹)
        (homogeneousRotationNumerator
          (anchorProductDenominator left right)
          (anchorProductNumerator left right)) := by
  rw [cap_eq_scaled_homogeneousNumerator left leftDefined,
    cap_eq_scaled_homogeneousNumerator right rightDefined,
    Matrix3.mul_scale_left, Matrix3.mul_scale_right,
    Matrix3.scale_scale, homogeneousRotationNumerator_product]

/-- Theorem 46, proved by denominator-cleared finite coordinate algebra. -/
theorem cap_mul_cap (left right : Vector K)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0)
    (productDefined : anchorProductDenominator left right ≠ 0) :
    Matrix3.mul (cap left leftDefined) (cap right rightDefined) =
      cap (anchorProduct left right productDefined)
        (capDenominator_anchorProduct_ne_zero left right leftDefined
          rightDefined productDefined) := by
  rw [cap_eq_scaled_homogeneousNumerator left leftDefined,
    cap_eq_scaled_homogeneousNumerator right rightDefined,
    Matrix3.mul_scale_left, Matrix3.mul_scale_right,
    Matrix3.scale_scale, homogeneousRotationNumerator_product,
    cap_anchorProduct_eq_scaled_homogeneousNumerator left right leftDefined
      rightDefined productDefined,
    homogeneousNorm_anchorProductNumerator,
    inverse_product leftDefined rightDefined]

/-- Executable multiplication in the stored rotation structure. -/
def rotationProduct (left right : Rotation K) : Rotation K where
  matrix := Matrix3.mul left.matrix right.matrix
  orthogonal := Matrix3.isOrthogonal_mul left.orthogonal right.orthogonal
  determinantOne := by
    rw [Matrix3.determinant_mul, left.determinantOne,
      right.determinantOne, one_mul]

/-- The trace formula valid even on the forbidden affine locus. -/
theorem trace_cap_mul_cap (left right : Vector K)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0) :
    Matrix3.trace (Matrix3.mul (cap left leftDefined)
        (cap right rightDefined)) =
      (3 * anchorProductDenominator left right ^ 2 -
          (anchorProductNumerator left right).quadrance) /
        (capDenominator left * capDenominator right) := by
  rw [cap_mul_cap_eq_scaled_homogeneousNumerator left right leftDefined
    rightDefined]
  unfold Matrix3.trace Matrix3.scale homogeneousRotationNumerator
    Vector.quadrance Vector.dot
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [← inverse_product leftDefined rightDefined]
  ring1

/-- The complementary half spread of a product of two caps is the square of
the affine denominator divided by the two cap denominators. -/
theorem one_sub_halfSpread_capProduct (left right : Vector K)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    1 - halfSpread
        (rotationProduct (capRotation left leftDefined)
          (capRotation right rightDefined)) =
      anchorProductDenominator left right ^ 2 /
        (capDenominator left * capDenominator right) := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have fourCancel := RFAP.ExplicitField.mul_inv_cancel (4 : K) fourNonzero
  have denominatorNonzero :=
    RFAP.ExplicitField.mul_ne_zero leftDefined rightDefined
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (capDenominator left * capDenominator right) denominatorNonzero
  have normEquation :
      capDenominator left * capDenominator right =
        anchorProductDenominator left right ^ 2 +
          (anchorProductNumerator left right).quadrance := by
    symm
    exact homogeneousNorm_anchorProductNumerator left right
  unfold halfSpread rotationProduct capRotation
  rw [trace_cap_mul_cap left right leftDefined rightDefined]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 -
        (3 -
          (3 * anchorProductDenominator left right ^ 2 -
              (anchorProductNumerator left right).quadrance) *
            (capDenominator left * capDenominator right)⁻¹) *
          (4 : K)⁻¹ =
      (4 -
        (3 -
          (3 * anchorProductDenominator left right ^ 2 -
              (anchorProductNumerator left right).quadrance) *
            (capDenominator left * capDenominator right)⁻¹)) *
        (4 : K)⁻¹ := by rw [← fourCancel]; ring1
    _ = ((capDenominator left * capDenominator right) *
          (capDenominator left * capDenominator right)⁻¹ +
        (3 * anchorProductDenominator left right ^ 2 -
            (anchorProductNumerator left right).quadrance) *
          (capDenominator left * capDenominator right)⁻¹) *
        (4 : K)⁻¹ := by rw [denominatorCancel]; ring1
    _ = 4 * anchorProductDenominator left right ^ 2 *
        (capDenominator left * capDenominator right)⁻¹ *
          (4 : K)⁻¹ := by rw [normEquation]; ring1
    _ = anchorProductDenominator left right ^ 2 *
        (capDenominator left * capDenominator right)⁻¹ := by
      calc
        4 * anchorProductDenominator left right ^ 2 *
            (capDenominator left * capDenominator right)⁻¹ * (4 : K)⁻¹ =
          (4 * (4 : K)⁻¹) *
            (anchorProductDenominator left right ^ 2 *
              (capDenominator left * capDenominator right)⁻¹) := by ring1
        _ = anchorProductDenominator left right ^ 2 *
            (capDenominator left * capDenominator right)⁻¹ := by
          rw [fourCancel, one_mul]

/-- Corollary 48: the composed cap rotation is a half turn exactly on the
forbidden affine locus. -/
theorem capProduct_halfSpread_eq_one [DecidableEq K]
    (left right : Vector K)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread
        (rotationProduct (capRotation left leftDefined)
          (capRotation right rightDefined)) = 1 ↔
      Vector.dot left right = 1 := by
  have denominatorNonzero :=
    RFAP.ExplicitField.mul_ne_zero leftDefined rightDefined
  constructor
  · intro halfTurn
    have complementZero :
        1 - halfSpread
          (rotationProduct (capRotation left leftDefined)
            (capRotation right rightDefined)) = 0 := by
      rw [halfTurn]
      ring1
    rw [one_sub_halfSpread_capProduct left right leftDefined rightDefined
      twoNonzero] at complementZero
    have squareZero : anchorProductDenominator left right ^ 2 = 0 := by
      calc
        anchorProductDenominator left right ^ 2 =
            (anchorProductDenominator left right ^ 2 /
              (capDenominator left * capDenominator right)) *
                (capDenominator left * capDenominator right) := by
          symm
          exact RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero
        _ = 0 := by rw [complementZero, zero_mul]
    by_cases denominatorZero : anchorProductDenominator left right = 0
    · have displayedZero : 1 - Vector.dot left right = 0 := by
        simpa only [anchorProductDenominator] using denominatorZero
      calc
        Vector.dot left right =
            1 - (1 - Vector.dot left right) := by ring1
        _ = 1 := by rw [displayedZero]; ring1
    · have squareNonzero : anchorProductDenominator left right ^ 2 ≠ 0 := by
        simpa only [pow_two] using RFAP.ExplicitField.mul_ne_zero
          denominatorZero denominatorZero
      exact (squareNonzero squareZero).elim
  · intro dotOne
    have denominatorZero : anchorProductDenominator left right = 0 := by
      unfold anchorProductDenominator
      rw [dotOne]
      ring1
    have complementZero :
        1 - halfSpread
          (rotationProduct (capRotation left leftDefined)
            (capRotation right rightDefined)) = 0 := by
      rw [one_sub_halfSpread_capProduct left right leftDefined rightDefined
        twoNonzero, denominatorZero]
      rw [show (0 : K) ^ 2 = 0 by ring1,
        RFAP.ExplicitField.zero_div]
    calc
      halfSpread
          (rotationProduct (capRotation left leftDefined)
            (capRotation right rightDefined)) =
        1 - (1 - halfSpread
          (rotationProduct (capRotation left leftDefined)
            (capRotation right rightDefined))) := by ring1
      _ = 1 := by rw [complementZero]; ring1

/-- On the forbidden affine locus, the surviving numerator has exactly the
product of the two cap denominators as its quadrance. -/
theorem anchorProductNumerator_quadrance_of_dot_eq_one
    (left right : Vector K) (dotOne : Vector.dot left right = 1) :
    (anchorProductNumerator left right).quadrance =
      capDenominator left * capDenominator right := by
  have identity := homogeneousNorm_anchorProductNumerator left right
  unfold homogeneousNorm at identity
  have denominatorZero : anchorProductDenominator left right = 0 := by
    unfold anchorProductDenominator
    rw [dotOne]
    ring1
  rw [denominatorZero] at identity
  rw [show (0 : K) ^ 2 = 0 by ring1, zero_add] at identity
  exact identity

theorem anchorProductNumerator_nonNull_of_dot_eq_one
    (left right : Vector K)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0)
    (dotOne : Vector.dot left right = 1) :
    (anchorProductNumerator left right).quadrance ≠ 0 := by
  rw [anchorProductNumerator_quadrance_of_dot_eq_one left right dotOne]
  exact RFAP.ExplicitField.mul_ne_zero leftDefined rightDefined

/-- The exact axis refinement of Corollary 48 used in Example 53. -/
theorem cap_mul_cap_eq_halfTurn_of_dot_eq_one
    (left right : Vector K)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0)
    (dotOne : Vector.dot left right = 1) :
    Matrix3.mul (cap left leftDefined) (cap right rightDefined) =
      halfTurn (anchorProductNumerator left right)
        (anchorProductNumerator_nonNull_of_dot_eq_one left right leftDefined
          rightDefined dotOne) := by
  let axis := anchorProductNumerator left right
  have axisQuadrance : axis.quadrance =
      capDenominator left * capDenominator right :=
    anchorProductNumerator_quadrance_of_dot_eq_one left right dotOne
  have axisNonNull : axis.quadrance ≠ 0 := by
    rw [axisQuadrance]
    exact RFAP.ExplicitField.mul_ne_zero leftDefined rightDefined
  have denominatorZero : anchorProductDenominator left right = 0 := by
    unfold anchorProductDenominator
    rw [dotOne]
    ring1
  calc
    Matrix3.mul (cap left leftDefined) (cap right rightDefined) =
      Matrix3.scale
        ((capDenominator left)⁻¹ * (capDenominator right)⁻¹)
        (homogeneousRotationNumerator 0 axis) := by
      rw [cap_mul_cap_eq_scaled_homogeneousNumerator left right leftDefined
        rightDefined, denominatorZero]
    _ = Matrix3.scale axis.quadrance⁻¹
        (homogeneousRotationNumerator 0 axis) := by
      rw [axisQuadrance, inverse_product leftDefined rightDefined]
    _ = halfTurn axis axisNonNull := by
      have axisCancel := RFAP.ExplicitField.mul_inv_cancel
        axis.quadrance axisNonNull
      have axisCancelExpanded :
          (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s) *
            axis.quadrance⁻¹ = 1 := by
        simpa only [Vector.quadrance, Vector.dot] using axisCancel
      have inverseExpanded : axis.quadrance⁻¹ =
          (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s)⁻¹ := by
        rfl
      have expandedCancel :
          (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s) *
            (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s)⁻¹ = 1 := by
        rw [← inverseExpanded]
        exact axisCancelExpanded
      ext <;> unfold homogeneousRotationNumerator <;>
        unfold halfTurn reflection <;>
        unfold Matrix3.neg Matrix3.sub Matrix3.scale Matrix3.identity
          Matrix3.outer Vector.quadrance Vector.dot <;>
        simp only [RFAP.ExplicitField.div_eq_mul_inv] <;>
        (try rw [← expandedCancel]) <;> ring1

namespace ExampleFortySeven

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def left : Vector Scalar := ⟨4, 1, 5⟩

def right : Vector Scalar := ⟨-3, 4, 2⟩

def result : Vector Scalar := ⟨-19, -28, 12⟩

theorem dot_value : Vector.dot left right = 2 := by
  unfold left right Vector.dot
  ring1

theorem cross_value : Vector.cross left right = ⟨-18, -23, 19⟩ := by
  apply Vector.ext <;> decide

theorem numerator_value : anchorProductNumerator left right =
    ⟨19, 28, -12⟩ := by
  apply Vector.ext <;> decide

theorem productDefined : anchorProductDenominator left right ≠ 0 := by
  unfold anchorProductDenominator
  rw [dot_value]
  decide

theorem product_value : anchorProduct left right productDefined = result := by
  rw [anchorProduct_eq_inverse_scale, numerator_value]
  have denominatorValue : anchorProductDenominator left right = -1 := by
    unfold anchorProductDenominator
    rw [dot_value]
    ring1
  rw [denominatorValue]
  apply Vector.ext <;> decide

theorem left_quadrance : left.quadrance = 42 := by
  unfold left Vector.quadrance Vector.dot
  ring1

theorem right_quadrance : right.quadrance = 29 := by
  unfold right Vector.quadrance Vector.dot
  ring1

theorem result_quadrance : result.quadrance = 1289 := by
  unfold result Vector.quadrance Vector.dot
  ring1

private theorem natCast_ne_zero {value : Nat} (nonzero : value ≠ 0) :
    (value : Scalar) ≠ 0 := by
  intro castZero
  exact nonzero (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

theorem leftDefined : capDenominator left ≠ 0 := by
  rw [show capDenominator left = (43 : Scalar) by
    unfold capDenominator
    rw [left_quadrance]
    ring1]
  exact natCast_ne_zero (by decide)

theorem rightDefined : capDenominator right ≠ 0 := by
  rw [show capDenominator right = (30 : Scalar) by
    unfold capDenominator
    rw [right_quadrance]
    ring1]
  exact natCast_ne_zero (by decide)

theorem resultDefined : capDenominator result ≠ 0 := by
  rw [show capDenominator result = (1290 : Scalar) by
    unfold capDenominator
    rw [result_quadrance]
    ring1]
  exact natCast_ne_zero (by decide)

theorem twoNonzero : (2 : Scalar) ≠ 0 := by decide

theorem left_halfSpread : halfSpread (capRotation left leftDefined) =
    (42 : Scalar) / 43 := by
  rw [halfSpread_cap left leftDefined twoNonzero, left_quadrance]
  unfold capDenominator
  rw [left_quadrance]
  rw [show (1 + 42 : Scalar) = 43 by ring1]

theorem right_halfSpread : halfSpread (capRotation right rightDefined) =
    (29 : Scalar) / 30 := by
  rw [halfSpread_cap right rightDefined twoNonzero, right_quadrance]
  unfold capDenominator
  rw [right_quadrance]
  rw [show (1 + 29 : Scalar) = 30 by ring1]

theorem result_halfSpread : halfSpread (capRotation result resultDefined) =
    (1289 : Scalar) / 1290 := by
  rw [halfSpread_cap result resultDefined twoNonzero, result_quadrance]
  unfold capDenominator
  rw [result_quadrance]
  rw [show (1 + 1289 : Scalar) = 1290 by ring1]

/-- Example 47's composition, without multiplying the two displayed
three-by-three matrices by hand. -/
theorem composition :
    Matrix3.mul (cap left leftDefined) (cap right rightDefined) =
      cap result resultDefined := by
  calc
    Matrix3.mul (cap left leftDefined) (cap right rightDefined) =
        cap (anchorProduct left right productDefined)
          (capDenominator_anchorProduct_ne_zero left right leftDefined
            rightDefined productDefined) :=
      cap_mul_cap left right leftDefined rightDefined productDefined
    _ = cap result resultDefined :=
      cap_congr_vector product_value _ _

end ExampleFortySeven

/-- The scalar denominator in Corollary 49. -/
def tangentDenominator (axis : Vector K) (left right : K) : K :=
  1 - axis.quadrance * left * right

theorem anchorProductDenominator_scale_same (axis : Vector K)
    (left right : K) :
    anchorProductDenominator (Vector.scale left axis)
        (Vector.scale right axis) =
      tangentDenominator axis left right := by
  unfold anchorProductDenominator tangentDenominator Vector.quadrance
  rw [Vector.dot_scale_left, Vector.dot_scale_right]
  ring1

/-- The vector calculation underlying tangent addition. -/
theorem anchorProduct_scale_same (axis : Vector K) (left right : K)
    (defined : tangentDenominator axis left right ≠ 0) :
    anchorProduct (Vector.scale left axis) (Vector.scale right axis)
        (by rwa [anchorProductDenominator_scale_same]) =
      Vector.scale ((left + right) / tangentDenominator axis left right)
        axis := by
  have numerator :
      anchorProductNumerator (Vector.scale left axis)
          (Vector.scale right axis) =
        Vector.scale (left + right) axis := by
    apply Vector.ext <;> unfold anchorProductNumerator Vector.scale Vector.sub
      Vector.add Vector.cross <;> ring1
  rw [anchorProduct_eq_inverse_scale,
    anchorProductDenominator_scale_same, numerator, Vector.scale_scale]
  congr 1
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

theorem tangentResultDefined (axis : Vector K) (left right : K)
    (leftDefined : capDenominator (Vector.scale left axis) ≠ 0)
    (rightDefined : capDenominator (Vector.scale right axis) ≠ 0)
    (productDefined : tangentDenominator axis left right ≠ 0) :
    capDenominator
        (Vector.scale ((left + right) /
          tangentDenominator axis left right) axis) ≠ 0 := by
  rw [← anchorProduct_scale_same axis left right productDefined]
  exact capDenominator_anchorProduct_ne_zero _ _ leftDefined rightDefined
    (by rwa [anchorProductDenominator_scale_same])

/-- Corollary 49: tangent addition on a fixed anchor line. -/
theorem tangentAddition (axis : Vector K) (left right : K)
    (leftDefined : capDenominator (Vector.scale left axis) ≠ 0)
    (rightDefined : capDenominator (Vector.scale right axis) ≠ 0)
    (productDefined : tangentDenominator axis left right ≠ 0) :
    Matrix3.mul
        (cap (Vector.scale left axis) leftDefined)
        (cap (Vector.scale right axis) rightDefined) =
      cap
        (Vector.scale ((left + right) /
          tangentDenominator axis left right) axis)
        (tangentResultDefined axis left right leftDefined rightDefined
          productDefined) := by
  let affineDefined : anchorProductDenominator
      (Vector.scale left axis) (Vector.scale right axis) ≠ 0 := by
    rwa [anchorProductDenominator_scale_same]
  calc
    Matrix3.mul
        (cap (Vector.scale left axis) leftDefined)
        (cap (Vector.scale right axis) rightDefined) =
      cap
        (anchorProduct (Vector.scale left axis) (Vector.scale right axis)
          affineDefined)
        (capDenominator_anchorProduct_ne_zero _ _ leftDefined rightDefined
          affineDefined) :=
      cap_mul_cap _ _ leftDefined rightDefined affineDefined
    _ = cap
        (Vector.scale ((left + right) /
          tangentDenominator axis left right) axis)
        (tangentResultDefined axis left right leftDefined rightDefined
          productDefined) := by
      exact cap_congr_vector
        (anchorProduct_scale_same axis left right productDefined) _ _

/-- Scalar coordinate of the denominator-cleared pair product used to prove
associativity without assuming that any cap exists. -/
def homogeneousAnchorProductScalar (leftScalar : K) (left : Vector K)
    (rightScalar : K) (right : Vector K) : K :=
  leftScalar * rightScalar - Vector.dot left right

/-- Vector coordinate of the denominator-cleared pair product. -/
def homogeneousAnchorProductVector (leftScalar : K) (left : Vector K)
    (rightScalar : K) (right : Vector K) : Vector K :=
  Vector.sub
    (Vector.add (Vector.scale leftScalar right)
      (Vector.scale rightScalar left))
    (Vector.cross left right)

private theorem homogeneousAnchorProduct_scalar_associative
    (firstScalar : K) (first : Vector K)
    (secondScalar : K) (second : Vector K)
    (thirdScalar : K) (third : Vector K) :
    homogeneousAnchorProductScalar
        (homogeneousAnchorProductScalar firstScalar first secondScalar second)
        (homogeneousAnchorProductVector firstScalar first secondScalar second)
        thirdScalar third =
      homogeneousAnchorProductScalar firstScalar first
        (homogeneousAnchorProductScalar secondScalar second thirdScalar third)
        (homogeneousAnchorProductVector secondScalar second thirdScalar third) := by
  unfold homogeneousAnchorProductScalar homogeneousAnchorProductVector
    Vector.dot Vector.sub Vector.add Vector.scale Vector.cross
  ring1

private theorem homogeneousAnchorProduct_vector_associative
    (firstScalar : K) (first : Vector K)
    (secondScalar : K) (second : Vector K)
    (thirdScalar : K) (third : Vector K) :
    homogeneousAnchorProductVector
        (homogeneousAnchorProductScalar firstScalar first secondScalar second)
        (homogeneousAnchorProductVector firstScalar first secondScalar second)
        thirdScalar third =
      homogeneousAnchorProductVector firstScalar first
        (homogeneousAnchorProductScalar secondScalar second thirdScalar third)
        (homogeneousAnchorProductVector secondScalar second thirdScalar third) := by
  apply Vector.ext <;> unfold homogeneousAnchorProductScalar
    homogeneousAnchorProductVector Vector.dot Vector.sub Vector.add
    Vector.scale Vector.cross <;> ring1

private theorem anchorProduct_congr_left {first second right : Vector K}
    (equal : first = second)
    (firstDefined : anchorProductDenominator first right ≠ 0)
    (secondDefined : anchorProductDenominator second right ≠ 0) :
    anchorProduct first right firstDefined =
      anchorProduct second right secondDefined := by
  subst second
  rfl

private theorem anchorProduct_congr_right {left first second : Vector K}
    (equal : first = second)
    (firstDefined : anchorProductDenominator left first ≠ 0)
    (secondDefined : anchorProductDenominator left second ≠ 0) :
    anchorProduct left first firstDefined =
      anchorProduct left second secondDefined := by
  subst second
  rfl

private theorem anchorProduct_normalized_left (scalar : K)
    (vector right : Vector K) (scalarNonzero : scalar ≠ 0)
    (defined : anchorProductDenominator
      (Vector.scale scalar⁻¹ vector) right ≠ 0) :
    anchorProduct (Vector.scale scalar⁻¹ vector) right defined =
      Vector.scale
        (homogeneousAnchorProductScalar scalar vector 1 right)⁻¹
        (homogeneousAnchorProductVector scalar vector 1 right) := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel scalar scalarNonzero
  have reverseCancel : scalar⁻¹ * scalar = 1 := by
    calc
      scalar⁻¹ * scalar = scalar * scalar⁻¹ := by ring1
      _ = 1 := cancel
  have denominatorRelation :
      anchorProductDenominator (Vector.scale scalar⁻¹ vector) right =
        scalar⁻¹ *
          homogeneousAnchorProductScalar scalar vector 1 right := by
    unfold anchorProductDenominator homogeneousAnchorProductScalar
    rw [Vector.dot_scale_left]
    calc
      1 - scalar⁻¹ * Vector.dot vector right =
          scalar⁻¹ * scalar - scalar⁻¹ * Vector.dot vector right := by
        rw [reverseCancel]
      _ = scalar⁻¹ *
          (scalar * 1 - Vector.dot vector right) := by ring1
  have numeratorRelation :
      anchorProductNumerator (Vector.scale scalar⁻¹ vector) right =
        Vector.scale scalar⁻¹
          (homogeneousAnchorProductVector scalar vector 1 right) := by
    have rightRescaled : right =
        Vector.scale scalar⁻¹ (Vector.scale scalar right) := by
      symm
      rw [Vector.scale_scale, reverseCancel, Vector.one_scale]
    unfold anchorProductNumerator
    rw [Vector.cross_scale_left]
    calc
      Vector.sub (Vector.add (Vector.scale scalar⁻¹ vector) right)
          (Vector.scale scalar⁻¹ (Vector.cross vector right)) =
        Vector.sub
          (Vector.add (Vector.scale scalar⁻¹ vector)
            (Vector.scale scalar⁻¹ (Vector.scale scalar right)))
          (Vector.scale scalar⁻¹ (Vector.cross vector right)) :=
        congrArg
          (fun replacement => Vector.sub
            (Vector.add (Vector.scale scalar⁻¹ vector) replacement)
            (Vector.scale scalar⁻¹ (Vector.cross vector right)))
          rightRescaled
      _ = Vector.sub
          (Vector.scale scalar⁻¹
            (Vector.add vector (Vector.scale scalar right)))
          (Vector.scale scalar⁻¹ (Vector.cross vector right)) := by
        rw [Vector.scale_add]
      _ = Vector.scale scalar⁻¹
          (Vector.sub (Vector.add vector (Vector.scale scalar right))
            (Vector.cross vector right)) := by
        rw [Vector.scale_sub]
      _ = Vector.scale scalar⁻¹
          (homogeneousAnchorProductVector scalar vector 1 right) := by
        congr 1
        apply Vector.ext <;> unfold homogeneousAnchorProductVector
          Vector.sub Vector.add Vector.scale <;> ring1
  have resultScalarNonzero :
      homogeneousAnchorProductScalar scalar vector 1 right ≠ 0 := by
    intro resultZero
    apply defined
    rw [denominatorRelation, resultZero, mul_zero]
  have resultCancel := RFAP.ExplicitField.mul_inv_cancel
    (homogeneousAnchorProductScalar scalar vector 1 right)
    resultScalarNonzero
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (anchorProductDenominator (Vector.scale scalar⁻¹ vector) right) defined
  have coefficient :
      (anchorProductDenominator (Vector.scale scalar⁻¹ vector) right)⁻¹ *
          scalar⁻¹ =
        (homogeneousAnchorProductScalar scalar vector 1 right)⁻¹ := by
    calc
      (anchorProductDenominator (Vector.scale scalar⁻¹ vector) right)⁻¹ *
          scalar⁻¹ =
        (anchorProductDenominator (Vector.scale scalar⁻¹ vector) right)⁻¹ *
          scalar⁻¹ *
          (homogeneousAnchorProductScalar scalar vector 1 right *
            (homogeneousAnchorProductScalar scalar vector 1 right)⁻¹) := by
              rw [resultCancel, mul_one]
      _ = ((anchorProductDenominator
          (Vector.scale scalar⁻¹ vector) right)⁻¹ *
            anchorProductDenominator (Vector.scale scalar⁻¹ vector) right) *
          (homogeneousAnchorProductScalar scalar vector 1 right)⁻¹ := by
        rw [denominatorRelation]
        ring1
      _ = (homogeneousAnchorProductScalar scalar vector 1 right)⁻¹ := by
        rw [show
          (anchorProductDenominator
            (Vector.scale scalar⁻¹ vector) right)⁻¹ *
              anchorProductDenominator (Vector.scale scalar⁻¹ vector) right = 1 by
            calc
              _ = anchorProductDenominator
                  (Vector.scale scalar⁻¹ vector) right *
                    (anchorProductDenominator
                      (Vector.scale scalar⁻¹ vector) right)⁻¹ := by ring1
              _ = 1 := denominatorCancel,
          one_mul]
  rw [anchorProduct_eq_inverse_scale, numeratorRelation,
    Vector.scale_scale, coefficient]

private theorem anchorProduct_normalized_right (left : Vector K)
    (scalar : K) (vector : Vector K) (scalarNonzero : scalar ≠ 0)
    (defined : anchorProductDenominator left
      (Vector.scale scalar⁻¹ vector) ≠ 0) :
    anchorProduct left (Vector.scale scalar⁻¹ vector) defined =
      Vector.scale
        (homogeneousAnchorProductScalar 1 left scalar vector)⁻¹
        (homogeneousAnchorProductVector 1 left scalar vector) := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel scalar scalarNonzero
  have reverseCancel : scalar⁻¹ * scalar = 1 := by
    calc
      scalar⁻¹ * scalar = scalar * scalar⁻¹ := by ring1
      _ = 1 := cancel
  have denominatorRelation :
      anchorProductDenominator left (Vector.scale scalar⁻¹ vector) =
        scalar⁻¹ *
          homogeneousAnchorProductScalar 1 left scalar vector := by
    unfold anchorProductDenominator homogeneousAnchorProductScalar
    rw [Vector.dot_scale_right]
    calc
      1 - scalar⁻¹ * Vector.dot left vector =
          scalar⁻¹ * scalar - scalar⁻¹ * Vector.dot left vector := by
        rw [reverseCancel]
      _ = scalar⁻¹ *
          (1 * scalar - Vector.dot left vector) := by ring1
  have numeratorRelation :
      anchorProductNumerator left (Vector.scale scalar⁻¹ vector) =
        Vector.scale scalar⁻¹
          (homogeneousAnchorProductVector 1 left scalar vector) := by
    have leftRescaled : left =
        Vector.scale scalar⁻¹ (Vector.scale scalar left) := by
      symm
      rw [Vector.scale_scale, reverseCancel, Vector.one_scale]
    unfold anchorProductNumerator
    rw [Vector.cross_scale_right]
    calc
      Vector.sub (Vector.add left (Vector.scale scalar⁻¹ vector))
          (Vector.scale scalar⁻¹ (Vector.cross left vector)) =
        Vector.sub
          (Vector.add (Vector.scale scalar⁻¹ (Vector.scale scalar left))
            (Vector.scale scalar⁻¹ vector))
          (Vector.scale scalar⁻¹ (Vector.cross left vector)) :=
        congrArg
          (fun replacement => Vector.sub
            (Vector.add replacement (Vector.scale scalar⁻¹ vector))
            (Vector.scale scalar⁻¹ (Vector.cross left vector)))
          leftRescaled
      _ = Vector.sub
          (Vector.scale scalar⁻¹
            (Vector.add (Vector.scale scalar left) vector))
          (Vector.scale scalar⁻¹ (Vector.cross left vector)) := by
        rw [Vector.scale_add]
      _ = Vector.scale scalar⁻¹
          (Vector.sub (Vector.add (Vector.scale scalar left) vector)
            (Vector.cross left vector)) := by
        rw [Vector.scale_sub]
      _ = Vector.scale scalar⁻¹
          (homogeneousAnchorProductVector 1 left scalar vector) := by
        congr 1
        apply Vector.ext <;> unfold homogeneousAnchorProductVector
          Vector.sub Vector.add Vector.scale <;> ring1
  have resultScalarNonzero :
      homogeneousAnchorProductScalar 1 left scalar vector ≠ 0 := by
    intro resultZero
    apply defined
    rw [denominatorRelation, resultZero, mul_zero]
  have resultCancel := RFAP.ExplicitField.mul_inv_cancel
    (homogeneousAnchorProductScalar 1 left scalar vector)
    resultScalarNonzero
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (anchorProductDenominator left (Vector.scale scalar⁻¹ vector)) defined
  have coefficient :
      (anchorProductDenominator left (Vector.scale scalar⁻¹ vector))⁻¹ *
          scalar⁻¹ =
        (homogeneousAnchorProductScalar 1 left scalar vector)⁻¹ := by
    calc
      (anchorProductDenominator left (Vector.scale scalar⁻¹ vector))⁻¹ *
          scalar⁻¹ =
        (anchorProductDenominator left (Vector.scale scalar⁻¹ vector))⁻¹ *
          scalar⁻¹ *
          (homogeneousAnchorProductScalar 1 left scalar vector *
            (homogeneousAnchorProductScalar 1 left scalar vector)⁻¹) := by
              rw [resultCancel, mul_one]
      _ = ((anchorProductDenominator left
          (Vector.scale scalar⁻¹ vector))⁻¹ *
            anchorProductDenominator left (Vector.scale scalar⁻¹ vector)) *
          (homogeneousAnchorProductScalar 1 left scalar vector)⁻¹ := by
        rw [denominatorRelation]
        ring1
      _ = (homogeneousAnchorProductScalar 1 left scalar vector)⁻¹ := by
        rw [show
          (anchorProductDenominator left
            (Vector.scale scalar⁻¹ vector))⁻¹ *
              anchorProductDenominator left (Vector.scale scalar⁻¹ vector) = 1 by
            calc
              _ = anchorProductDenominator left
                  (Vector.scale scalar⁻¹ vector) *
                    (anchorProductDenominator left
                      (Vector.scale scalar⁻¹ vector))⁻¹ := by ring1
              _ = 1 := denominatorCancel,
          one_mul]
  rw [anchorProduct_eq_inverse_scale, numeratorRelation,
    Vector.scale_scale, coefficient]

private theorem nestedAnchorProduct_left_normalized
    (first second third : Vector K)
    (firstDefined : anchorProductDenominator first second ≠ 0)
    (secondDefined : anchorProductDenominator
      (anchorProduct first second firstDefined) third ≠ 0) :
    anchorProduct (anchorProduct first second firstDefined) third
        secondDefined =
      Vector.scale
        (homogeneousAnchorProductScalar
          (anchorProductDenominator first second)
          (anchorProductNumerator first second) 1 third)⁻¹
        (homogeneousAnchorProductVector
          (anchorProductDenominator first second)
          (anchorProductNumerator first second) 1 third) := by
  have innerEqual := anchorProduct_eq_inverse_scale first second firstDefined
  let normalizedDefined : anchorProductDenominator
      (Vector.scale (anchorProductDenominator first second)⁻¹
        (anchorProductNumerator first second)) third ≠ 0 := by
    rw [← innerEqual]
    exact secondDefined
  calc
    anchorProduct (anchorProduct first second firstDefined) third
        secondDefined =
      anchorProduct
        (Vector.scale (anchorProductDenominator first second)⁻¹
          (anchorProductNumerator first second)) third normalizedDefined :=
      anchorProduct_congr_left innerEqual _ _
    _ = _ := anchorProduct_normalized_left _ _ _ firstDefined
      normalizedDefined

private theorem nestedAnchorProduct_right_normalized
    (first second third : Vector K)
    (firstDefined : anchorProductDenominator second third ≠ 0)
    (secondDefined : anchorProductDenominator first
      (anchorProduct second third firstDefined) ≠ 0) :
    anchorProduct first (anchorProduct second third firstDefined)
        secondDefined =
      Vector.scale
        (homogeneousAnchorProductScalar 1 first
          (anchorProductDenominator second third)
          (anchorProductNumerator second third))⁻¹
        (homogeneousAnchorProductVector 1 first
          (anchorProductDenominator second third)
          (anchorProductNumerator second third)) := by
  have innerEqual := anchorProduct_eq_inverse_scale second third firstDefined
  let normalizedDefined : anchorProductDenominator first
      (Vector.scale (anchorProductDenominator second third)⁻¹
        (anchorProductNumerator second third)) ≠ 0 := by
    rw [← innerEqual]
    exact secondDefined
  calc
    anchorProduct first (anchorProduct second third firstDefined)
        secondDefined =
      anchorProduct first
        (Vector.scale (anchorProductDenominator second third)⁻¹
          (anchorProductNumerator second third)) normalizedDefined :=
      anchorProduct_congr_right innerEqual _ _
    _ = _ := anchorProduct_normalized_right _ _ _ firstDefined
      normalizedDefined

/-- Theorem 50, proved directly for every explicit field without requiring
the three input anchors to lie in the cap chart. -/
theorem anchorProduct_associative (first second third : Vector K)
    (firstSecondDefined : anchorProductDenominator first second ≠ 0)
    (leftDefined : anchorProductDenominator
      (anchorProduct first second firstSecondDefined) third ≠ 0)
    (secondThirdDefined : anchorProductDenominator second third ≠ 0)
    (rightDefined : anchorProductDenominator first
      (anchorProduct second third secondThirdDefined) ≠ 0) :
    anchorProduct (anchorProduct first second firstSecondDefined) third
        leftDefined =
      anchorProduct first (anchorProduct second third secondThirdDefined)
        rightDefined := by
  rw [nestedAnchorProduct_left_normalized first second third
      firstSecondDefined leftDefined,
    nestedAnchorProduct_right_normalized first second third
      secondThirdDefined rightDefined]
  have scalarAssociative :
      homogeneousAnchorProductScalar
          (anchorProductDenominator first second)
          (anchorProductNumerator first second) 1 third =
        homogeneousAnchorProductScalar 1 first
          (anchorProductDenominator second third)
          (anchorProductNumerator second third) := by
    unfold homogeneousAnchorProductScalar anchorProductDenominator
      anchorProductNumerator Vector.dot Vector.sub Vector.add Vector.cross
    ring1
  have vectorAssociative :
      homogeneousAnchorProductVector
          (anchorProductDenominator first second)
          (anchorProductNumerator first second) 1 third =
        homogeneousAnchorProductVector 1 first
          (anchorProductDenominator second third)
          (anchorProductNumerator second third) := by
    apply Vector.ext <;> unfold homogeneousAnchorProductVector
      anchorProductDenominator
      anchorProductNumerator Vector.dot Vector.sub Vector.add Vector.scale
      Vector.cross <;> ring1
  exact congrArg₂ Vector.scale (congrArg Inv.inv scalarAssociative)
    vectorAssociative

theorem anchorProductDenominator_neg_right (vector : Vector K) :
    anchorProductDenominator vector (Vector.neg vector) =
      capDenominator vector := by
  unfold anchorProductDenominator capDenominator Vector.quadrance
  rw [Vector.dot_neg_right]
  ring1

theorem anchorProduct_neg_right_eq_zero (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    anchorProduct vector (Vector.neg vector)
        (by rwa [anchorProductDenominator_neg_right]) = Vector.zero := by
  rw [anchorProduct_eq_inverse_scale]
  apply Vector.ext <;> unfold anchorProductNumerator Vector.neg Vector.sub
    Vector.add Vector.cross Vector.scale Vector.zero <;> ring1

theorem anchorProductDenominator_zero_right (vector : Vector K) :
    anchorProductDenominator vector Vector.zero = 1 := by
  unfold anchorProductDenominator
  rw [Vector.dot_zero_right]
  ring1

private theorem one_ne_zero_of_two_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply twoNonzero
  calc
    (2 : K) = 2 * 1 := by ring1
    _ = 2 * 0 := by rw [oneZero]
    _ = 0 := by ring1

theorem anchorProduct_zero_right (vector : Vector K)
    (oneNonzero : (1 : K) ≠ 0) :
    anchorProduct vector Vector.zero
        (by rwa [anchorProductDenominator_zero_right]) = vector := by
  have oneCancel := RFAP.ExplicitField.mul_inv_cancel (1 : K) oneNonzero
  rw [anchorProduct_eq_inverse_scale]
  have denominator : anchorProductDenominator vector Vector.zero = 1 :=
    anchorProductDenominator_zero_right vector
  rw [denominator]
  have inverseOne : (1 : K)⁻¹ = 1 := by
    calc
      (1 : K)⁻¹ = 1 * (1 : K)⁻¹ := by rw [one_mul]
      _ = 1 := oneCancel
  rw [inverseOne, Vector.one_scale]
  apply Vector.ext <;> unfold anchorProductNumerator Vector.zero Vector.sub
    Vector.add Vector.cross <;> ring1

namespace ExampleFifty

def axis : Vector K := ⟨1, 0, 0⟩

theorem dot_self : Vector.dot (axis : Vector K) axis = 1 := by
  unfold axis Vector.dot
  ring1

theorem first_product_undefined :
    anchorProductDenominator (axis : Vector K) axis = 0 := by
  unfold anchorProductDenominator
  rw [dot_self]
  ring1

theorem axis_capDenominator : capDenominator (axis : Vector K) = 2 := by
  unfold capDenominator axis Vector.quadrance Vector.dot
  ring1

theorem innerDefined (twoNonzero : (2 : K) ≠ 0) :
    anchorProductDenominator (axis : Vector K) (Vector.neg axis) ≠ 0 := by
  rw [anchorProductDenominator_neg_right, axis_capDenominator]
  exact twoNonzero

theorem inner_value (twoNonzero : (2 : K) ≠ 0) :
    anchorProduct (axis : Vector K) (Vector.neg axis)
        (innerDefined twoNonzero) = Vector.zero := by
  exact anchorProduct_neg_right_eq_zero axis
    (by rw [axis_capDenominator]; exact twoNonzero)

theorem outerDefined (twoNonzero : (2 : K) ≠ 0) :
    anchorProductDenominator (axis : Vector K)
        (anchorProduct axis (Vector.neg axis) (innerDefined twoNonzero)) ≠ 0 := by
  rw [inner_value twoNonzero, anchorProductDenominator_zero_right]
  exact one_ne_zero_of_two_ne_zero twoNonzero

/-- The explicit partiality witness following Theorem 50: the right
bracketing exists and returns the first anchor, while the left inner product
is undefined. -/
theorem right_bracketing_value (twoNonzero : (2 : K) ≠ 0) :
    anchorProduct (axis : Vector K)
        (anchorProduct axis (Vector.neg axis) (innerDefined twoNonzero))
        (outerDefined twoNonzero) = axis := by
  let zeroDefined : anchorProductDenominator (axis : Vector K)
      Vector.zero ≠ 0 := by
    rw [anchorProductDenominator_zero_right]
    exact one_ne_zero_of_two_ne_zero twoNonzero
  calc
    anchorProduct (axis : Vector K)
        (anchorProduct axis (Vector.neg axis) (innerDefined twoNonzero))
        (outerDefined twoNonzero) =
      anchorProduct axis Vector.zero zeroDefined :=
        anchorProduct_congr_right (inner_value twoNonzero) _ _
    _ = axis := anchorProduct_zero_right axis
      (one_ne_zero_of_two_ne_zero twoNonzero)

end ExampleFifty

/-- The companion numerator of Theorem 51. -/
def oppositeAnchorProductNumerator (left right : Vector K) : Vector K :=
  Vector.add (Vector.add left right) (Vector.cross left right)

/-- Theorem 51's companion partial operation. -/
def oppositeAnchorProduct (left right : Vector K)
    (_defined : anchorProductDenominator left right ≠ 0) : Vector K :=
  Vector.scale (1 / anchorProductDenominator left right)
    (oppositeAnchorProductNumerator left right)

theorem anchorProductDenominator_comm (left right : Vector K) :
    anchorProductDenominator left right =
      anchorProductDenominator right left := by
  unfold anchorProductDenominator
  rw [Vector.dot_comm]

/-- Theorem 51: the companion operation is the ordinary product in reverse
order. -/
theorem oppositeAnchorProduct_eq_reverse (left right : Vector K)
    (defined : anchorProductDenominator left right ≠ 0) :
    oppositeAnchorProduct left right defined =
      anchorProduct right left
        (by rwa [← anchorProductDenominator_comm left right]) := by
  have numerator : oppositeAnchorProductNumerator left right =
      anchorProductNumerator right left := by
    apply Vector.ext <;> unfold oppositeAnchorProductNumerator
      anchorProductNumerator Vector.add Vector.sub Vector.cross <;> ring1
  unfold oppositeAnchorProduct
  rw [anchorProduct_eq_inverse_scale,
    ← anchorProductDenominator_comm left right, numerator]
  congr 1
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- The opposite anchor product inherits conditional associativity from the
ordinary anchor product, with the three inputs and the two bracketings
reversed. -/
theorem oppositeAnchorProduct_associative (first second third : Vector K)
    (firstSecondDefined : anchorProductDenominator first second ≠ 0)
    (secondThirdDefined : anchorProductDenominator second third ≠ 0)
    (leftDefined : anchorProductDenominator
      (oppositeAnchorProduct first second firstSecondDefined) third ≠ 0)
    (rightDefined : anchorProductDenominator first
      (oppositeAnchorProduct second third secondThirdDefined) ≠ 0) :
    oppositeAnchorProduct
        (oppositeAnchorProduct first second firstSecondDefined) third
          leftDefined =
      oppositeAnchorProduct first
        (oppositeAnchorProduct second third secondThirdDefined) rightDefined := by
  let thirdSecondDefined : anchorProductDenominator third second ≠ 0 := by
    rwa [anchorProductDenominator_comm third second]
  let secondFirstDefined : anchorProductDenominator second first ≠ 0 := by
    rwa [anchorProductDenominator_comm second first]
  have firstSecondReverse := oppositeAnchorProduct_eq_reverse first second
    firstSecondDefined
  have secondThirdReverse := oppositeAnchorProduct_eq_reverse second third
    secondThirdDefined
  let reversedLeftDefined : anchorProductDenominator third
      (anchorProduct second first secondFirstDefined) ≠ 0 := by
    rw [← firstSecondReverse, anchorProductDenominator_comm]
    exact leftDefined
  let reversedRightDefined : anchorProductDenominator
      (anchorProduct third second thirdSecondDefined) first ≠ 0 := by
    rw [← secondThirdReverse, anchorProductDenominator_comm]
    exact rightDefined
  calc
    oppositeAnchorProduct
        (oppositeAnchorProduct first second firstSecondDefined) third
          leftDefined =
      anchorProduct third
        (oppositeAnchorProduct first second firstSecondDefined)
          (by rwa [anchorProductDenominator_comm third]) :=
            oppositeAnchorProduct_eq_reverse _ _ _
    _ = anchorProduct third (anchorProduct second first secondFirstDefined)
        reversedLeftDefined :=
      anchorProduct_congr_right firstSecondReverse _ _
    _ = anchorProduct (anchorProduct third second thirdSecondDefined) first
        reversedRightDefined :=
      (anchorProduct_associative third second first thirdSecondDefined
        reversedRightDefined secondFirstDefined reversedLeftDefined).symm
    _ = anchorProduct
        (oppositeAnchorProduct second third secondThirdDefined) first
          (by rwa [secondThirdReverse]) :=
      anchorProduct_congr_left secondThirdReverse.symm _ _
    _ = oppositeAnchorProduct first
        (oppositeAnchorProduct second third secondThirdDefined) rightDefined :=
      (oppositeAnchorProduct_eq_reverse _ _ _).symm

/-- The rotation interpretation of Theorem 51. -/
theorem cap_mul_cap_opposite (left right : Vector K)
    (leftDefined : capDenominator left ≠ 0)
    (rightDefined : capDenominator right ≠ 0)
    (productDefined : anchorProductDenominator left right ≠ 0) :
    Matrix3.mul (cap right rightDefined) (cap left leftDefined) =
      cap (oppositeAnchorProduct left right productDefined)
        (by
          rw [show oppositeAnchorProduct left right productDefined =
              anchorProduct right left
                (by rwa [← anchorProductDenominator_comm left right]) from
            oppositeAnchorProduct_eq_reverse left right productDefined]
          exact capDenominator_anchorProduct_ne_zero right left rightDefined
            leftDefined
            (by rwa [← anchorProductDenominator_comm left right])) := by
  let reverseDefined : anchorProductDenominator right left ≠ 0 := by
    rwa [← anchorProductDenominator_comm left right]
  calc
    Matrix3.mul (cap right rightDefined) (cap left leftDefined) =
        cap (anchorProduct right left reverseDefined)
          (capDenominator_anchorProduct_ne_zero right left rightDefined
            leftDefined reverseDefined) :=
      cap_mul_cap right left rightDefined leftDefined reverseDefined
    _ = cap (oppositeAnchorProduct left right productDefined) _ :=
      cap_congr_vector
        (oppositeAnchorProduct_eq_reverse left right productDefined).symm _ _

end RationalRotations
