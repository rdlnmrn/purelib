import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.ExplicitField

/-!
# Rational rotations, section 2: finite vector algebra

This module formalizes the coordinate algebra in Section 2 of
*Rational rotations of three dimensional Euclidean space*.  Vectors are
explicit triples and every operation is a finite coordinate calculation.
No basis, dimension, cardinality, norm, square root, or completed scalar
object is used.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- A displayed row vector `(t,r,s)` in three-dimensional space. -/
@[ext]
structure Vector (K : Type*) where
  t : K
  r : K
  s : K
deriving DecidableEq

namespace Vector

/-- The zero vector. -/
def zero : Vector K := ⟨0, 0, 0⟩

/-- Coordinatewise vector addition. -/
def add (left right : Vector K) : Vector K :=
  ⟨left.t + right.t, left.r + right.r, left.s + right.s⟩

/-- Coordinatewise vector negation. -/
def neg (vector : Vector K) : Vector K :=
  ⟨-vector.t, -vector.r, -vector.s⟩

/-- Coordinatewise vector subtraction. -/
def sub (left right : Vector K) : Vector K :=
  ⟨left.t - right.t, left.r - right.r, left.s - right.s⟩

/-- Left scalar multiplication of a displayed vector. -/
def scale (scalar : K) (vector : Vector K) : Vector K :=
  ⟨scalar * vector.t, scalar * vector.r, scalar * vector.s⟩

/-- The finite Cartesian dot product. -/
def dot (left right : Vector K) : K :=
  left.t * right.t + left.r * right.r + left.s * right.s

/-- The finite Cartesian cross product. -/
def cross (left right : Vector K) : Vector K :=
  ⟨left.r * right.s - right.r * left.s,
    left.s * right.t - right.s * left.t,
    left.t * right.r - right.t * left.r⟩

/-- Definition 1: the quadrance `Q(v)=v·v`. -/
def quadrance (vector : Vector K) : K := dot vector vector

/-- A vector is null precisely when its quadrance vanishes. -/
def IsNull (vector : Vector K) : Prop := quadrance vector = 0

/-- Two vectors are perpendicular precisely when their dot product vanishes. -/
def Perpendicular (left right : Vector K) : Prop := dot left right = 0

/-- The displayed determinant with the three vectors as rows. -/
def determinant (first second third : Vector K) : K :=
  first.t * (second.r * third.s - second.s * third.r) -
    first.r * (second.t * third.s - second.s * third.t) +
      first.s * (second.t * third.r - second.r * third.t)

/-- The displayed determinant is additive in its third row. -/
theorem determinant_add_third (first second third fourth : Vector K) :
    determinant first second (add third fourth) =
      determinant first second third + determinant first second fourth := by
  unfold determinant add
  ring1

/-- The displayed determinant is homogeneous in its third row. -/
theorem determinant_scale_third (scalar : K)
    (first second third : Vector K) :
    determinant first second (scale scalar third) =
      scalar * determinant first second third := by
  unfold determinant scale
  ring1

/-- Repeating the second row makes the displayed determinant vanish. -/
@[simp] theorem determinant_repeat_second (first second : Vector K) :
    determinant first second second = 0 := by
  unfold determinant
  ring1

/-- Negating the first row negates the displayed determinant. -/
theorem determinant_neg_first (first second third : Vector K) :
    determinant (neg first) second third =
      -determinant first second third := by
  unfold determinant neg
  ring1

/-- Definition 4: spread of two non-null displayed directions.  The
non-nullness certificates are retained in the data interface so callers
cannot form the paper's geometric quantity at a forbidden denominator. -/
def spread (left right : Vector K)
    (_leftNonNull : quadrance left ≠ 0)
    (_rightNonNull : quadrance right ≠ 0) : K :=
  1 - dot left right ^ 2 / (quadrance left * quadrance right)

@[simp] theorem zero_t : (zero : Vector K).t = 0 := rfl

@[simp] theorem zero_r : (zero : Vector K).r = 0 := rfl

@[simp] theorem zero_s : (zero : Vector K).s = 0 := rfl

@[simp] theorem add_t (left right : Vector K) :
    (add left right).t = left.t + right.t := rfl

@[simp] theorem add_r (left right : Vector K) :
    (add left right).r = left.r + right.r := rfl

@[simp] theorem add_s (left right : Vector K) :
    (add left right).s = left.s + right.s := rfl

@[simp] theorem neg_t (vector : Vector K) :
    (neg vector).t = -vector.t := rfl

@[simp] theorem neg_r (vector : Vector K) :
    (neg vector).r = -vector.r := rfl

@[simp] theorem neg_s (vector : Vector K) :
    (neg vector).s = -vector.s := rfl

@[simp] theorem sub_t (left right : Vector K) :
    (sub left right).t = left.t - right.t := rfl

@[simp] theorem sub_r (left right : Vector K) :
    (sub left right).r = left.r - right.r := rfl

@[simp] theorem sub_s (left right : Vector K) :
    (sub left right).s = left.s - right.s := rfl

@[simp] theorem scale_t (scalar : K) (vector : Vector K) :
    (scale scalar vector).t = scalar * vector.t := rfl

@[simp] theorem scale_r (scalar : K) (vector : Vector K) :
    (scale scalar vector).r = scalar * vector.r := rfl

@[simp] theorem scale_s (scalar : K) (vector : Vector K) :
    (scale scalar vector).s = scalar * vector.s := rfl

@[simp] theorem add_zero (vector : Vector K) : add vector zero = vector := by
  apply Vector.ext <;> exact _root_.add_zero _

@[simp] theorem zero_add (vector : Vector K) : add zero vector = vector := by
  apply Vector.ext <;> exact _root_.zero_add _

@[simp] theorem neg_zero : neg (zero : Vector K) = zero := by
  apply Vector.ext <;> exact _root_.neg_zero

@[simp] theorem scale_zero (scalar : K) : scale scalar zero = zero := by
  ext <;> simp only [scale_t, scale_r, scale_s, zero_t, zero_r, zero_s, mul_zero]

@[simp] theorem zero_scale (vector : Vector K) : scale 0 vector = zero := by
  ext <;> simp only [scale_t, scale_r, scale_s, zero_t, zero_r, zero_s, zero_mul]

@[simp] theorem one_scale (vector : Vector K) : scale 1 vector = vector := by
  ext <;> simp only [scale_t, scale_r, scale_s, one_mul]

theorem scale_scale (first second : K) (vector : Vector K) :
    scale first (scale second vector) = scale (first * second) vector := by
  ext <;> unfold scale <;> ring1

theorem scale_add (scalar : K) (left right : Vector K) :
    scale scalar (add left right) =
      add (scale scalar left) (scale scalar right) := by
  ext <;> unfold scale add <;> ring1

theorem scale_sub (scalar : K) (left right : Vector K) :
    scale scalar (sub left right) =
      sub (scale scalar left) (scale scalar right) := by
  ext <;> unfold scale sub <;> ring1

theorem dot_comm (left right : Vector K) : dot left right = dot right left := by
  unfold dot
  ring1

@[simp] theorem dot_zero_left (vector : Vector K) : dot zero vector = 0 := by
  unfold dot zero
  ring1

@[simp] theorem dot_zero_right (vector : Vector K) : dot vector zero = 0 := by
  rw [dot_comm, dot_zero_left]

@[simp] theorem dot_add_left (first second third : Vector K) :
    dot (add first second) third = dot first third + dot second third := by
  unfold dot add
  ring1

@[simp] theorem dot_add_right (first second third : Vector K) :
    dot first (add second third) = dot first second + dot first third := by
  unfold dot add
  ring1

/-- Quadrance of a displayed vector sum. -/
theorem quadrance_add (left right : Vector K) :
    quadrance (add left right) =
      quadrance left + 2 * dot left right + quadrance right := by
  unfold quadrance dot add
  ring1

@[simp] theorem dot_neg_left (left right : Vector K) :
    dot (neg left) right = -dot left right := by
  unfold dot neg
  ring1

@[simp] theorem dot_neg_right (left right : Vector K) :
    dot left (neg right) = -dot left right := by
  unfold dot neg
  ring1

@[simp] theorem dot_scale_left (scalar : K) (left right : Vector K) :
    dot (scale scalar left) right = scalar * dot left right := by
  unfold dot scale
  ring1

@[simp] theorem dot_scale_right (scalar : K) (left right : Vector K) :
    dot left (scale scalar right) = scalar * dot left right := by
  unfold dot scale
  ring1

@[simp] theorem cross_zero_left (vector : Vector K) : cross zero vector = zero := by
  ext <;> unfold cross zero <;> ring1

@[simp] theorem cross_zero_right (vector : Vector K) : cross vector zero = zero := by
  ext <;> unfold cross zero <;> ring1

theorem cross_anticomm (left right : Vector K) :
    cross left right = neg (cross right left) := by
  ext <;> unfold cross neg <;> ring1

@[simp] theorem cross_add_left (first second third : Vector K) :
    cross (add first second) third =
      add (cross first third) (cross second third) := by
  ext <;> unfold cross add <;> ring1

@[simp] theorem cross_add_right (first second third : Vector K) :
    cross first (add second third) =
      add (cross first second) (cross first third) := by
  ext <;> unfold cross add <;> ring1

@[simp] theorem cross_scale_left (scalar : K) (left right : Vector K) :
    cross (scale scalar left) right = scale scalar (cross left right) := by
  ext <;> unfold cross scale <;> ring1

@[simp] theorem cross_scale_right (scalar : K) (left right : Vector K) :
    cross left (scale scalar right) = scale scalar (cross left right) := by
  ext <;> unfold cross scale <;> ring1

/-- Theorem 5.1: the scalar triple product is the displayed determinant. -/
theorem scalar_triple_product (first second third : Vector K) :
    dot (cross first second) third = determinant first second third := by
  unfold dot cross determinant
  ring1

/-- The scalar triple product vanishes when its third argument repeats the
first cross-product argument. -/
@[simp] theorem cross_dot_left (left right : Vector K) :
    dot (cross left right) left = 0 := by
  unfold dot cross
  ring1

/-- The scalar triple product vanishes when its third argument repeats the
second cross-product argument. -/
@[simp] theorem cross_dot_right (left right : Vector K) :
    dot (cross left right) right = 0 := by
  unfold dot cross
  ring1

/-- Theorem 5.2: the vector triple-product identity. -/
theorem vector_triple_product (first second third : Vector K) :
    cross first (cross second third) =
      sub (scale (dot first third) second)
        (scale (dot first second) third) := by
  ext <;> unfold cross sub scale dot <;> ring1

/-- Theorem 5.3: the Binet--Cauchy identity in displayed coordinates. -/
theorem binet_cauchy (first second third fourth : Vector K) :
    dot (cross first second) (cross third fourth) =
      dot first third * dot second fourth -
        dot first fourth * dot second third := by
  unfold dot cross
  ring1

/-- Theorem 6: Lagrange's identity. -/
theorem lagrange (left right : Vector K) :
    dot left right ^ 2 + quadrance (cross left right) =
      quadrance left * quadrance right := by
  unfold quadrance dot cross
  ring1

@[simp] theorem quadrance_zero : quadrance (zero : Vector K) = 0 := by
  unfold quadrance
  rw [dot_zero_left]

@[simp] theorem quadrance_neg (vector : Vector K) :
    quadrance (neg vector) = quadrance vector := by
  unfold quadrance dot neg
  ring1

theorem quadrance_scale (scalar : K) (vector : Vector K) :
    quadrance (scale scalar vector) = scalar ^ 2 * quadrance vector := by
  unfold quadrance dot scale
  ring1

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

private theorem one_sub_div (numerator denominator : K)
    (denominatorNonzero : denominator ≠ 0) :
    1 - numerator / denominator =
      (denominator - numerator) / denominator := by
  have cancel : denominator * denominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 - numerator * denominator⁻¹ =
        denominator * denominator⁻¹ -
          numerator * denominator⁻¹ := by rw [cancel]
    _ = (denominator - numerator) * denominator⁻¹ := by ring1

/-- The consequence of Theorem 6 printed after Lagrange's identity: spread
is the quadrance of the cross product divided by the two quadrances. -/
theorem spread_eq_cross_quadrance (left right : Vector K)
    (leftNonNull : quadrance left ≠ 0)
    (rightNonNull : quadrance right ≠ 0) :
    spread left right leftNonNull rightNonNull =
      quadrance (cross left right) /
        (quadrance left * quadrance right) := by
  have denominatorNonzero : quadrance left * quadrance right ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero leftNonNull rightNonNull
  unfold spread
  rw [one_sub_div _ _ denominatorNonzero]
  congr 1
  have identity := lagrange left right
  calc
    quadrance left * quadrance right - dot left right ^ 2 =
        dot left right ^ 2 + quadrance (cross left right) -
          dot left right ^ 2 := by rw [identity]
    _ = quadrance (cross left right) := by ring1

/-- Scaling a non-null vector by a nonzero scalar preserves non-nullness. -/
theorem quadrance_scale_ne_zero (scalar : K) (vector : Vector K)
    (scalarNonzero : scalar ≠ 0) (vectorNonNull : quadrance vector ≠ 0) :
    quadrance (scale scalar vector) ≠ 0 := by
  rw [quadrance_scale]
  exact RFAP.ExplicitField.mul_ne_zero
    (by
      simpa only [pow_two] using
        RFAP.ExplicitField.mul_ne_zero scalarNonzero scalarNonzero)
    vectorNonNull

/-- Spread is unchanged by a nonzero rescaling of its first direction. -/
theorem spread_scale_left (scalar : K) (left right : Vector K)
    (scalarNonzero : scalar ≠ 0)
    (leftNonNull : quadrance left ≠ 0)
    (rightNonNull : quadrance right ≠ 0) :
    spread (scale scalar left) right
        (quadrance_scale_ne_zero scalar left scalarNonzero leftNonNull)
        rightNonNull =
      spread left right leftNonNull rightNonNull := by
  unfold spread
  congr 1
  rw [dot_scale_left, quadrance_scale]
  apply div_eq_div_of_cross_mul
  · exact RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero
        (by
          simpa only [pow_two] using
            RFAP.ExplicitField.mul_ne_zero scalarNonzero scalarNonzero)
        leftNonNull)
      rightNonNull
  · exact RFAP.ExplicitField.mul_ne_zero leftNonNull rightNonNull
  · ring1

/-- Spread is unchanged by a nonzero rescaling of its second direction. -/
theorem spread_scale_right (scalar : K) (left right : Vector K)
    (scalarNonzero : scalar ≠ 0)
    (leftNonNull : quadrance left ≠ 0)
    (rightNonNull : quadrance right ≠ 0) :
    spread left (scale scalar right) leftNonNull
        (quadrance_scale_ne_zero scalar right scalarNonzero rightNonNull) =
      spread left right leftNonNull rightNonNull := by
  unfold spread
  congr 1
  rw [dot_scale_right, quadrance_scale]
  apply div_eq_div_of_cross_mul
  · exact RFAP.ExplicitField.mul_ne_zero leftNonNull
      (RFAP.ExplicitField.mul_ne_zero
        (by
          simpa only [pow_two] using
            RFAP.ExplicitField.mul_ne_zero scalarNonzero scalarNonzero)
        rightNonNull)
  · exact RFAP.ExplicitField.mul_ne_zero leftNonNull rightNonNull
  · ring1

private theorem square_eq_zero [DecidableEq K] (value : K)
    (squareZero : value ^ 2 = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        RFAP.ExplicitField.mul_ne_zero valueZero valueZero
    exact (squareNonzero squareZero).elim

private theorem div_eq_zero [DecidableEq K]
    (numerator denominator : K) (denominatorNonzero : denominator ≠ 0)
    (quotientZero : numerator / denominator = 0) : numerator = 0 := by
  by_cases numeratorZero : numerator = 0
  · exact numeratorZero
  · exact (RFAP.ExplicitField.div_ne_zero numeratorZero denominatorNonzero
      quotientZero).elim

/-- For non-null vectors over a computational field, spread one is exactly
perpendicularity. -/
theorem spread_eq_one_iff_perpendicular [DecidableEq K]
    (left right : Vector K)
    (leftNonNull : quadrance left ≠ 0)
    (rightNonNull : quadrance right ≠ 0) :
    spread left right leftNonNull rightNonNull = 1 ↔
      Perpendicular left right := by
  have denominatorNonzero : quadrance left * quadrance right ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero leftNonNull rightNonNull
  constructor
  · intro spreadOne
    have quotientZero :
        dot left right ^ 2 /
          (quadrance left * quadrance right) = 0 := by
      unfold spread at spreadOne
      calc
        dot left right ^ 2 / (quadrance left * quadrance right) =
            1 - (1 - dot left right ^ 2 /
              (quadrance left * quadrance right)) := by ring1
        _ = 0 := by rw [spreadOne]; ring1
    exact square_eq_zero _
      (div_eq_zero _ _ denominatorNonzero quotientZero)
  · intro perpendicular
    unfold Perpendicular at perpendicular
    unfold spread
    rw [perpendicular]
    simp only [zero_pow (by decide : 2 ≠ 0), RFAP.ExplicitField.zero_div]
    ring1

end Vector

end RationalRotations
