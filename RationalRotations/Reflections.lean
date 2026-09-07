import RationalRotations.Anchors
import mathlib.RFAP.ConstructiveFraction

/-!
# Rational rotations, section 4: reflections and half turns

The reflection and half-turn matrices are stored as explicit nine-entry
matrices.  Orthogonality, determinant, fixed-vector, and composition claims
are proved by finite field arithmetic.  No basis extension or dimension
argument is used for the determinant calculation.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- A rotation is an executable matrix together with the two finite
certificates defining membership in `SO(3)`. -/
structure Rotation (K : Type*) [RFAP.ExplicitField K] where
  matrix : Matrix3 K
  orthogonal : matrix.IsOrthogonal
  determinantOne : matrix.determinant = 1

/-- Definition 14: reflection in the plane perpendicular to a non-null
vector. -/
def reflection (vector : Vector K) (_nonNull : vector.quadrance ≠ 0) :
    Matrix3 K :=
  Matrix3.sub Matrix3.identity
    (Matrix3.scale (2 / vector.quadrance) (Matrix3.outer vector vector))

/-- The row-vector action of a reflection, in the formula used throughout
the paper. -/
theorem rowMul_reflection (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) (other : Vector K) :
    Matrix3.rowMul other (reflection vector nonNull) =
      Vector.sub other
        (Vector.scale (2 * Vector.dot other vector / vector.quadrance) vector) := by
  ext <;> unfold Matrix3.rowMul reflection Matrix3.sub Matrix3.identity
    Matrix3.scale Matrix3.outer Vector.sub Vector.scale Vector.dot
    Vector.quadrance <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1

/-- The reflection is symmetric. -/
theorem reflection_transpose (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.transpose (reflection vector nonNull) = reflection vector nonNull := by
  unfold reflection
  rw [Matrix3.transpose_sub, Matrix3.transpose_identity,
    Matrix3.transpose_scale, Matrix3.outer_transpose]

private theorem reflection_coefficient (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    (2 / vector.quadrance) ^ 2 * vector.quadrance =
      2 * (2 / vector.quadrance) := by
  have cancel : vector.quadrance * vector.quadrance⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel vector.quadrance nonNull
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (2 * vector.quadrance⁻¹) ^ 2 * vector.quadrance =
        4 * (vector.quadrance * vector.quadrance⁻¹) *
          vector.quadrance⁻¹ := by ring1
    _ = 2 * (2 * vector.quadrance⁻¹) := by rw [cancel]; ring1

/-- Theorem 15.1: reflection is an involution. -/
theorem reflection_square (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.mul (reflection vector nonNull) (reflection vector nonNull) =
      Matrix3.identity := by
  have coefficientZero :
      (2 / vector.quadrance) ^ 2 * vector.quadrance -
        2 * (2 / vector.quadrance) = 0 := by
    rw [reflection_coefficient vector nonNull]
    ring1
  calc
    Matrix3.mul (reflection vector nonNull) (reflection vector nonNull) =
        Matrix3.add Matrix3.identity
          (Matrix3.scale
            ((2 / vector.quadrance) ^ 2 * vector.quadrance -
              2 * (2 / vector.quadrance))
            (Matrix3.outer vector vector)) := by
      ext <;> unfold reflection Matrix3.mul Matrix3.sub Matrix3.add
        Matrix3.identity Matrix3.scale Matrix3.outer Vector.quadrance
        Vector.dot <;> ring1
    _ = Matrix3.identity := by
      rw [coefficientZero]
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.outer
        Matrix3.identity <;> ring1

/-- Theorem 15.2: the normal vector is negated by its reflection. -/
theorem rowMul_self_reflection (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.rowMul vector (reflection vector nonNull) = Vector.neg vector := by
  have cancel : vector.quadrance * vector.quadrance⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel vector.quadrance nonNull
  have factor :
      2 * Vector.dot vector vector / vector.quadrance = (2 : K) := by
    change 2 * vector.quadrance / vector.quadrance = (2 : K)
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * vector.quadrance * vector.quadrance⁻¹ =
          2 * (vector.quadrance * vector.quadrance⁻¹) := by ring1
      _ = 2 := by rw [cancel, mul_one]
  rw [rowMul_reflection, factor]
  ext <;> unfold Vector.sub Vector.scale Vector.neg <;> ring1

private theorem eq_zero_of_two_mul_eq_zero (twoNonzero : (2 : K) ≠ 0)
    (value : K) (twiceZero : 2 * value = 0) : value = 0 := by
  have cancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  calc
    value = 1 * value := by rw [one_mul]
    _ = (2 * (2 : K)⁻¹) * value := by rw [cancel]
    _ = (2 * value) * (2 : K)⁻¹ := by ring1
    _ = 0 := by rw [twiceZero, zero_mul]

/-- Theorem 15.3: a vector is fixed by the reflection precisely when it is
perpendicular to the normal. -/
theorem rowMul_reflection_eq_iff_perpendicular (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (other : Vector K) :
    Matrix3.rowMul other (reflection vector nonNull) = other ↔
      Vector.Perpendicular other vector := by
  have cancel : vector.quadrance * vector.quadrance⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel vector.quadrance nonNull
  have reflectedDot :
      Vector.dot (Matrix3.rowMul other (reflection vector nonNull)) vector =
        -Vector.dot other vector := by
    rw [rowMul_reflection]
    calc
      Vector.dot
          (Vector.sub other
            (Vector.scale
              (2 * Vector.dot other vector / vector.quadrance) vector))
          vector =
        Vector.dot other vector -
          (2 * Vector.dot other vector / vector.quadrance) *
            vector.quadrance := by
              unfold Vector.quadrance Vector.dot Vector.sub Vector.scale
              ring1
      _ = Vector.dot other vector -
          2 * Vector.dot other vector *
            (vector.quadrance * vector.quadrance⁻¹) := by
            simp only [RFAP.ExplicitField.div_eq_mul_inv]
            ring1
      _ = -Vector.dot other vector := by rw [cancel]; ring1
  constructor
  · intro fixed
    have equalDots := congrArg (fun value => Vector.dot value vector) fixed
    rw [reflectedDot] at equalDots
    apply eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * Vector.dot other vector =
          Vector.dot other vector - (-Vector.dot other vector) := by ring1
      _ = 0 := by rw [equalDots]; ring1
  · intro perpendicular
    unfold Vector.Perpendicular at perpendicular
    rw [rowMul_reflection, perpendicular, mul_zero,
      RFAP.ExplicitField.zero_div]
    unfold Vector.sub Vector.scale
    ext <;> ring1

/-- Theorem 15.4: reflection is orthogonal. -/
theorem reflection_isOrthogonal (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.IsOrthogonal (reflection vector nonNull) := by
  unfold Matrix3.IsOrthogonal
  rw [reflection_transpose, reflection_square]

/-- The dot-product part of Theorem 15.4. -/
theorem dot_rowMul_reflection (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) (first second : Vector K) :
    Vector.dot (Matrix3.rowMul first (reflection vector nonNull))
        (Matrix3.rowMul second (reflection vector nonNull)) =
      Vector.dot first second := by
  have coefficient := reflection_coefficient vector nonNull
  rw [rowMul_reflection, rowMul_reflection]
  calc
    Vector.dot
        (Vector.sub first
          (Vector.scale
            (2 * Vector.dot first vector / vector.quadrance) vector))
        (Vector.sub second
          (Vector.scale
            (2 * Vector.dot second vector / vector.quadrance) vector)) =
      Vector.dot first second +
        ((2 / vector.quadrance) ^ 2 * vector.quadrance -
          2 * (2 / vector.quadrance)) *
          Vector.dot first vector * Vector.dot second vector := by
            unfold Vector.quadrance Vector.dot Vector.sub Vector.scale
            simp only [RFAP.ExplicitField.div_eq_mul_inv]
            ring1
    _ = Vector.dot first second := by rw [coefficient]; ring1

/-- Theorem 15.5: a reflection has determinant minus one, proved by direct
coordinate expansion rather than a basis extension. -/
theorem determinant_reflection (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.determinant (reflection vector nonNull) = -1 := by
  have cancel : vector.quadrance * vector.quadrance⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel vector.quadrance nonNull
  unfold Matrix3.determinant reflection Matrix3.sub Matrix3.identity
    Matrix3.scale Matrix3.outer Vector.quadrance Vector.dot
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    _ = 1 - 2 * (vector.quadrance * vector.quadrance⁻¹) := by
      unfold Vector.quadrance Vector.dot
      ring1
    _ = -1 := by rw [cancel]; ring1

private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel rightDenominator rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

/-- The reflection depends only on the nonzero scalar class of its normal. -/
theorem reflection_scale (scalar : K) (vector : Vector K)
    (scalarNonzero : scalar ≠ 0) (nonNull : vector.quadrance ≠ 0) :
    reflection (Vector.scale scalar vector)
        (Vector.quadrance_scale_ne_zero scalar vector scalarNonzero nonNull) =
      reflection vector nonNull := by
  have scalarSquareNonzero : scalar ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero scalarNonzero scalarNonzero
  have scaledDenominatorNonzero :
      scalar ^ 2 * vector.quadrance ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero scalarSquareNonzero nonNull
  have ratio :
      (2 * scalar ^ 2) / (scalar ^ 2 * vector.quadrance) =
        2 / vector.quadrance := by
    apply div_eq_div_of_cross_mul scaledDenominatorNonzero nonNull
    ring1
  have coefficient :
      2 / (scalar ^ 2 * vector.quadrance) * scalar ^ 2 =
        2 / vector.quadrance := by
    calc
      2 / (scalar ^ 2 * vector.quadrance) * scalar ^ 2 =
          (2 * scalar ^ 2) / (scalar ^ 2 * vector.quadrance) := by
            simp only [RFAP.ExplicitField.div_eq_mul_inv]
            ring1
      _ = 2 / vector.quadrance := ratio
  unfold reflection
  rw [Vector.quadrance_scale, Matrix3.outer_scale_both,
    Matrix3.scale_scale, coefficient]

/-- Definition 16: the half turn about a non-null line. -/
def halfTurn (vector : Vector K) (nonNull : vector.quadrance ≠ 0) :
    Matrix3 K := Matrix3.neg (reflection vector nonNull)

/-- A half turn depends only on the nonzero scalar class of its axis. -/
theorem halfTurn_scale (scalar : K) (vector : Vector K)
    (scalarNonzero : scalar ≠ 0) (nonNull : vector.quadrance ≠ 0) :
    halfTurn (Vector.scale scalar vector)
        (Vector.quadrance_scale_ne_zero scalar vector scalarNonzero nonNull) =
      halfTurn vector nonNull := by
  unfold halfTurn
  rw [reflection_scale scalar vector scalarNonzero nonNull]

/-- Theorem 17: a half turn fixes its axis vector. -/
theorem rowMul_self_halfTurn (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.rowMul vector (halfTurn vector nonNull) = vector := by
  unfold halfTurn
  rw [Matrix3.rowMul_neg, rowMul_self_reflection]
  ext <;> unfold Vector.neg <;> ring1

/-- Theorem 17: a half turn negates each perpendicular vector. -/
theorem rowMul_halfTurn_of_perpendicular (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (other : Vector K) (perpendicular : other.Perpendicular vector) :
    Matrix3.rowMul other (halfTurn vector nonNull) = Vector.neg other := by
  unfold halfTurn
  rw [Matrix3.rowMul_neg,
    (rowMul_reflection_eq_iff_perpendicular vector nonNull twoNonzero other).2
      perpendicular]

/-- Theorem 17: a half turn is an involution. -/
theorem halfTurn_square (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.mul (halfTurn vector nonNull) (halfTurn vector nonNull) =
      Matrix3.identity := by
  unfold halfTurn
  rw [Matrix3.mul_neg_neg, reflection_square]

/-- Theorem 17: a half turn lies in `SO(3)`. -/
theorem halfTurn_isSpecialOrthogonal (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.IsSpecialOrthogonal (halfTurn vector nonNull) := by
  constructor
  · unfold Matrix3.IsOrthogonal halfTurn
    rw [Matrix3.transpose_neg, reflection_transpose,
      Matrix3.mul_neg_neg, reflection_square]
  · unfold halfTurn
    rw [Matrix3.determinant_neg, determinant_reflection]
    ring1

/-- The half turn bundled with its executable `SO(3)` certificates. -/
def halfTurnRotation (vector : Vector K) (nonNull : vector.quadrance ≠ 0) :
    Rotation K where
  matrix := halfTurn vector nonNull
  orthogonal := (halfTurn_isSpecialOrthogonal vector nonNull).1
  determinantOne := (halfTurn_isSpecialOrthogonal vector nonNull).2

/-- The converse half of Theorem 18: a product of two reflections is a
rotation.  The direct factorization is proved later in the paper from the
anchor of an arbitrary rotation. -/
theorem reflection_product_isSpecialOrthogonal
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0) :
    Matrix3.IsSpecialOrthogonal
      (Matrix3.mul (reflection first firstNonNull)
        (reflection second secondNonNull)) := by
  constructor
  · exact Matrix3.isOrthogonal_mul
      (reflection_isOrthogonal first firstNonNull)
      (reflection_isOrthogonal second secondNonNull)
  · rw [Matrix3.determinant_mul, determinant_reflection,
      determinant_reflection]
    ring1

/-- The product of two reflections bundled as a rotation. -/
def reflectionProductRotation
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0) : Rotation K where
  matrix := Matrix3.mul (reflection first firstNonNull)
    (reflection second secondNonNull)
  orthogonal := (reflection_product_isSpecialOrthogonal first second
    firstNonNull secondNonNull).1
  determinantOne := (reflection_product_isSpecialOrthogonal first second
    firstNonNull secondNonNull).2

/-- Displayed independence of two three-dimensional vectors. -/
def Vector.Independent (first second : Vector K) : Prop :=
  Vector.cross first second ≠ Vector.zero

/-- Theorem 19: the cross-product axis is fixed by the composition of its
two reflections. -/
theorem rowMul_cross_reflection_product
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul (Vector.cross first second)
        (Matrix3.mul (reflection first firstNonNull)
          (reflection second secondNonNull)) =
      Vector.cross first second := by
  rw [← Matrix3.rowMul_mul]
  have firstPerpendicular :
      (Vector.cross first second).Perpendicular first :=
    Vector.cross_dot_left first second
  have secondPerpendicular :
      (Vector.cross first second).Perpendicular second :=
    Vector.cross_dot_right first second
  rw [(rowMul_reflection_eq_iff_perpendicular first firstNonNull twoNonzero
      (Vector.cross first second)).2 firstPerpendicular,
    (rowMul_reflection_eq_iff_perpendicular second secondNonNull twoNonzero
      (Vector.cross first second)).2 secondPerpendicular]

namespace ExampleTwenty

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def first : Vector Scalar := ⟨1, 2, 3⟩

def second : Vector Scalar := ⟨2, 1, -1⟩

theorem first_quadrance : first.quadrance = 14 := by decide

theorem second_quadrance : second.quadrance = 6 := by decide

theorem first_nonNull : first.quadrance ≠ 0 := by decide

theorem second_nonNull : second.quadrance ≠ 0 := by decide

def firstDisplayed : Matrix3 Scalar :=
  Matrix3.scale (1 / 7) ⟨6, -2, -3, -2, 3, -6, -3, -6, -2⟩

def secondDisplayed : Matrix3 Scalar :=
  Matrix3.scale (1 / 3) ⟨-1, -2, 2, -2, 2, 1, 2, 1, 2⟩

def productDisplayed : Matrix3 Scalar :=
  Matrix3.scale (1 / 21) ⟨-8, -19, 4, -16, 4, -13, 11, -8, -16⟩

def axis : Vector Scalar := ⟨-5, 7, -3⟩

theorem first_reflection_displayed :
    reflection first first_nonNull = firstDisplayed := by decide

theorem second_reflection_displayed :
    reflection second second_nonNull = secondDisplayed := by decide

theorem product_displayed :
    Matrix3.mul (reflection first first_nonNull)
        (reflection second second_nonNull) = productDisplayed := by decide

theorem cross_displayed : Vector.cross first second = axis := by decide

theorem axis_fixed : Matrix3.rowMul axis productDisplayed = axis := by decide

end ExampleTwenty

end RationalRotations
