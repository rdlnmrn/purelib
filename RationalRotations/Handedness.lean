import RationalRotations.RotationAnchors

/-!
# Rational rotations, section 8: handedness

Handedness is stored as the determinant of the displayed frame formed by an
anchor axis, a perpendicular vector, and its rotated image.  The determinant
formula is valid over every explicit field.  Positivity is separated into a
small coherent ordered-field interface so the algebraic theorem remains
available over finite fields.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- The inverse rotation, represented by the certified transpose matrix. -/
def inverseRotation (rotation : Rotation K) : Rotation K where
  matrix := Matrix3.transpose rotation.matrix
  orthogonal := by
    unfold Matrix3.IsOrthogonal
    rw [Matrix3.transpose_transpose]
    exact transpose_mul_rotation rotation
  determinantOne := by
    rw [Matrix3.determinant_transpose, rotation.determinantOne]

theorem halfSpread_inverseRotation (rotation : Rotation K) :
    halfSpread (inverseRotation rotation) = halfSpread rotation := by
  unfold halfSpread inverseRotation
  rw [Matrix3.trace_transpose]

theorem inverseRotation_notHalfTurn (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1) :
    halfSpread (inverseRotation rotation) ≠ 1 := by
  rw [halfSpread_inverseRotation]
  exact notHalfTurn

/-- The introductory identity of Section 8: inversion negates the recovered
anchor matrix. -/
theorem rotationAnchor_inverseRotation (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1) :
    rotationAnchor (inverseRotation rotation)
        (inverseRotation_notHalfTurn rotation notHalfTurn) =
      Matrix3.neg (rotationAnchor rotation notHalfTurn) := by
  unfold rotationAnchor inverseRotation
  rw [Matrix3.trace_transpose, Matrix3.transpose_transpose]
  ext <;> unfold Matrix3.scale Matrix3.sub Matrix3.neg <;> ring1

/-- In vector coordinates, inversion reverses the anchor direction. -/
theorem rotationAnchorVector_inverseRotation (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationAnchorVector (inverseRotation rotation)
        (inverseRotation_notHalfTurn rotation notHalfTurn) =
      Vector.neg (rotationAnchorVector rotation notHalfTurn) := by
  apply anchor_injective
  rw [anchor_rotationAnchorVector _ _ twoNonzero, anchor_neg,
    anchor_rotationAnchorVector rotation notHalfTurn twoNonzero,
    rotationAnchor_inverseRotation]

/-- The determinant of the axis/transversal/rotated-transversal frame. -/
def handednessDet (axis transversal : Vector K) (matrix : Matrix3 K) : K :=
  Vector.determinant axis transversal (Matrix3.rowMul transversal matrix)

/-- Theorem 41 in its direct quadrance form. -/
theorem handednessDet_cap (axis : Vector K)
    (defined : capDenominator axis ≠ 0) (transversal : Vector K)
    (perpendicular : transversal.Perpendicular axis) :
    handednessDet axis transversal (cap axis defined) =
      (2 * axis.quadrance / capDenominator axis) *
        transversal.quadrance := by
  have reversePerpendicular : Vector.dot axis transversal = 0 := by
    rw [Vector.dot_comm]
    exact perpendicular
  have lagrange := Vector.lagrange axis transversal
  rw [reversePerpendicular] at lagrange
  have crossQuadrance :
      (Vector.cross axis transversal).quadrance =
        axis.quadrance * transversal.quadrance := by
    calc
      (Vector.cross axis transversal).quadrance =
          0 ^ 2 + (Vector.cross axis transversal).quadrance := by ring1
      _ = axis.quadrance * transversal.quadrance := lagrange
  unfold handednessDet
  rw [rowMul_cap_of_perpendicular axis defined transversal perpendicular,
    Vector.determinant_add_third, Vector.determinant_scale_third,
    Vector.determinant_repeat_second, mul_zero, zero_add,
    Vector.determinant_scale_third,
    ← Vector.scalar_triple_product]
  change (2 / capDenominator axis) *
      (Vector.cross axis transversal).quadrance =
    (2 * axis.quadrance / capDenominator axis) *
      transversal.quadrance
  rw [crossQuadrance]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- Theorem 41 in the paper's half-spread form. -/
theorem handednessDet_cap_halfSpread (axis : Vector K)
    (defined : capDenominator axis ≠ 0) (transversal : Vector K)
    (perpendicular : transversal.Perpendicular axis)
    (twoNonzero : (2 : K) ≠ 0) :
    handednessDet axis transversal (cap axis defined) =
      2 * halfSpread (capRotation axis defined) *
        (1 - halfSpread (capRotation axis defined)) *
        capDenominator axis * transversal.quadrance := by
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (capDenominator axis) defined
  rw [handednessDet_cap axis defined transversal perpendicular,
    one_sub_halfSpread_cap axis defined twoNonzero,
    halfSpread_cap axis defined twoNonzero]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    2 * axis.quadrance * (capDenominator axis)⁻¹ *
        transversal.quadrance =
      2 * axis.quadrance * (capDenominator axis)⁻¹ *
        (capDenominator axis * (capDenominator axis)⁻¹) *
        transversal.quadrance := by rw [denominatorCancel]; ring1
    _ = 2 * (axis.quadrance * (capDenominator axis)⁻¹) *
        (1 * (capDenominator axis)⁻¹) *
        capDenominator axis * transversal.quadrance := by ring1

/-- The metric handedness determinant vanishes identically on a null anchor
axis. -/
theorem handednessDet_cap_of_null (axis : Vector K)
    (defined : capDenominator axis ≠ 0) (transversal : Vector K)
    (perpendicular : transversal.Perpendicular axis)
    (null : axis.quadrance = 0) :
    handednessDet axis transversal (cap axis defined) = 0 := by
  rw [handednessDet_cap axis defined transversal perpendicular, null]
  simp only [mul_zero, RFAP.ExplicitField.zero_div, zero_mul]

/-- Reversing the anchor while retaining the same displayed first frame row
reverses the handedness determinant. -/
theorem handednessDet_cap_neg_sameAxis (axis : Vector K)
    (defined : capDenominator axis ≠ 0) (transversal : Vector K)
    (perpendicular : transversal.Perpendicular axis) :
    handednessDet axis transversal
        (cap (Vector.neg axis) (cap_neg_defined axis defined)) =
      -((2 * axis.quadrance / capDenominator axis) *
        transversal.quadrance) := by
  have negPerpendicular : transversal.Perpendicular (Vector.neg axis) := by
    unfold Vector.Perpendicular at *
    rw [Vector.dot_neg_right, perpendicular]
    ring1
  have formula := handednessDet_cap (Vector.neg axis)
    (cap_neg_defined axis defined) transversal negPerpendicular
  unfold handednessDet at formula ⊢
  rw [Vector.determinant_neg_first, Vector.quadrance_neg,
    capDenominator_neg] at formula
  calc
    Vector.determinant axis transversal
        (Matrix3.rowMul transversal
          (cap (Vector.neg axis) (cap_neg_defined axis defined))) =
      -(-Vector.determinant axis transversal
        (Matrix3.rowMul transversal
          (cap (Vector.neg axis) (cap_neg_defined axis defined)))) := by ring1
    _ = -((2 * axis.quadrance / capDenominator axis) *
        transversal.quadrance) := by rw [formula]

/-- The constructive positive-cone fragment needed by the right-hand rule.
It deliberately records the finite order laws directly, rather than deriving
them through Mathlib's broader ordered-ring hierarchy. -/
class OrderedExplicitField (K : Type*) extends RFAP.ExplicitField K, LT K where
  eq_decidable : DecidableEq K
  zero_lt_one_direct : 0 < (1 : K)
  add_pos_direct : ∀ {left right : K},
    0 < left → 0 < right → 0 < left + right
  mul_pos_direct : ∀ {left right : K},
    0 < left → 0 < right → 0 < left * right
  mul_self_pos_direct : ∀ {value : K}, value ≠ 0 → 0 < value * value
  inv_pos_direct : ∀ {value : K}, 0 < value → 0 < value⁻¹

section Ordered

variable {F : Type*} [OrderedExplicitField F]

local instance : DecidableEq F := OrderedExplicitField.eq_decidable

private theorem add_square_pos {base : F} (value : F)
    (basePositive : 0 < base) : 0 < base + value * value := by
  by_cases valueZero : value = 0
  · rw [valueZero, zero_mul, add_zero]
    exact basePositive
  · exact OrderedExplicitField.add_pos_direct basePositive
      (OrderedExplicitField.mul_self_pos_direct valueZero)

private theorem vector_quadrance_positive (vector : Vector F)
    (nonzero : vector ≠ Vector.zero) : 0 < vector.quadrance := by
  by_cases tZero : vector.t = 0
  · by_cases rZero : vector.r = 0
    · by_cases sZero : vector.s = 0
      · apply False.elim
        apply nonzero
        apply Vector.ext
        · exact tZero
        · exact rZero
        · exact sZero
      · have sPositive : 0 < vector.s * vector.s :=
          OrderedExplicitField.mul_self_pos_direct sZero
        unfold Vector.quadrance Vector.dot
        rw [tZero, rZero]
        simpa only [zero_mul, zero_add] using sPositive
    · have rPositive : 0 < vector.r * vector.r :=
        OrderedExplicitField.mul_self_pos_direct rZero
      unfold Vector.quadrance Vector.dot
      rw [tZero]
      simpa only [zero_mul, zero_add] using
        add_square_pos vector.s rPositive
  · have tPositive : 0 < vector.t * vector.t :=
      OrderedExplicitField.mul_self_pos_direct tZero
    unfold Vector.quadrance Vector.dot
    exact add_square_pos vector.s (add_square_pos vector.r tPositive)

/-- Corollary 42: the anchor/transversal/rotated-transversal frame is
strictly positively oriented over an ordered field. -/
theorem rightHandRule (axis transversal : Vector F)
    (defined : capDenominator axis ≠ 0)
    (axisNonzero : axis ≠ Vector.zero)
    (transversalNonzero : transversal ≠ Vector.zero)
    (perpendicular : transversal.Perpendicular axis) :
    0 < handednessDet axis transversal (cap axis defined) := by
  rw [handednessDet_cap axis defined transversal perpendicular]
  have axisPositive := vector_quadrance_positive axis axisNonzero
  have transversalPositive :=
    vector_quadrance_positive transversal transversalNonzero
  have denominatorPositive : 0 < capDenominator axis := by
    unfold capDenominator
    exact OrderedExplicitField.add_pos_direct
      OrderedExplicitField.zero_lt_one_direct axisPositive
  have twoPositive : 0 < (2 : F) := by
    rw [show (2 : F) = 1 + 1 by ring1]
    exact OrderedExplicitField.add_pos_direct
      OrderedExplicitField.zero_lt_one_direct
      OrderedExplicitField.zero_lt_one_direct
  have coefficientPositive :
      0 < 2 * axis.quadrance / capDenominator axis := by
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    exact OrderedExplicitField.mul_pos_direct
      (OrderedExplicitField.mul_pos_direct twoPositive axisPositive)
      (OrderedExplicitField.inv_pos_direct denominatorPositive)
  exact OrderedExplicitField.mul_pos_direct coefficientPositive
    transversalPositive

end Ordered

/-- Negating an anchor preserves the half spread of its cap. -/
theorem halfSpread_cap_neg (axis : Vector K)
    (defined : capDenominator axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    halfSpread
        (capRotation (Vector.neg axis) (cap_neg_defined axis defined)) =
      halfSpread (capRotation axis defined) := by
  rw [halfSpread_cap (Vector.neg axis) (cap_neg_defined axis defined)
      twoNonzero,
    halfSpread_cap axis defined twoNonzero,
    Vector.quadrance_neg, capDenominator_neg]

private theorem scalar_eq_zero_of_two_mul_eq_zero
    (twoNonzero : (2 : K) ≠ 0) {value : K}
    (twiceZero : 2 * value = 0) : value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  calc
    value = (2 * (2 : K)⁻¹) * value := by rw [cancel, one_mul]
    _ = (2 * value) * (2 : K)⁻¹ := by ring1
    _ = 0 := by rw [twiceZero, zero_mul]

private theorem vector_eq_zero_of_eq_neg (vector : Vector K)
    (twoNonzero : (2 : K) ≠ 0)
    (selfNegative : vector = Vector.neg vector) :
    vector = Vector.zero := by
  have tRelation : vector.t = -vector.t := by
    simpa only [Vector.neg_t] using congrArg Vector.t selfNegative
  have rRelation : vector.r = -vector.r := by
    simpa only [Vector.neg_r] using congrArg Vector.r selfNegative
  have sRelation : vector.s = -vector.s := by
    simpa only [Vector.neg_s] using congrArg Vector.s selfNegative
  apply Vector.ext
  · apply scalar_eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * vector.t = vector.t + vector.t := by ring1
      _ = -vector.t + vector.t :=
        congrArg (fun value => value + vector.t) tRelation
      _ = 0 := neg_add_cancel vector.t
  · apply scalar_eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * vector.r = vector.r + vector.r := by ring1
      _ = -vector.r + vector.r :=
        congrArg (fun value => value + vector.r) rRelation
      _ = 0 := neg_add_cancel vector.r
  · apply scalar_eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * vector.s = vector.s + vector.s := by ring1
      _ = -vector.s + vector.s :=
        congrArg (fun value => value + vector.s) sRelation
      _ = 0 := neg_add_cancel vector.s

/-- Corollary 42's algebraic distinction: opposite nonzero anchors give
different inverse rotations, even when no order is available. -/
theorem cap_ne_cap_neg_of_ne_zero (axis : Vector K)
    (defined : capDenominator axis ≠ 0) (axisNonzero : axis ≠ Vector.zero)
    (twoNonzero : (2 : K) ≠ 0) :
    cap axis defined ≠
      cap (Vector.neg axis) (cap_neg_defined axis defined) := by
  intro equalCaps
  have selfNegative := cap_injective twoNonzero axis (Vector.neg axis)
    defined (cap_neg_defined axis defined) equalCaps
  exact axisNonzero
    (vector_eq_zero_of_eq_neg axis twoNonzero selfNegative)

namespace ExampleFortyThree

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def transversal : Vector Scalar := ⟨1, 3, -1⟩

theorem perpendicular :
    transversal.Perpendicular ExampleTwentyFive.vector := by
  unfold transversal ExampleTwentyFive.vector Vector.Perpendicular Vector.dot
  ring1

theorem quadrance : transversal.quadrance = (11 : Scalar) := by
  unfold transversal Vector.quadrance Vector.dot
  ring1

theorem handedness_value :
    handednessDet ExampleTwentyFive.vector transversal
        (cap ExampleTwentyFive.vector ExampleTwentyFive.defined) =
      (1452 : Scalar) / 67 := by
  rw [handednessDet_cap ExampleTwentyFive.vector ExampleTwentyFive.defined
      transversal perpendicular]
  unfold capDenominator
  rw [ExampleTwentyFive.quadrance, quadrance]
  rw [show (1 + 66 : Scalar) = 67 by ring1]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

theorem handedness_positive :
    0 < handednessDet ExampleTwentyFive.vector transversal
      (cap ExampleTwentyFive.vector ExampleTwentyFive.defined) := by
  rw [handedness_value]
  exact RFAP.ConstructiveFraction.div_pos_direct
    (RFAP.ConstructiveFraction.natCast_pos_direct (by decide))
    (RFAP.ConstructiveFraction.natCast_pos_direct (by decide))

theorem inverse_handedness_value :
    handednessDet ExampleTwentyFive.vector transversal
        (cap (Vector.neg ExampleTwentyFive.vector)
          (cap_neg_defined ExampleTwentyFive.vector
            ExampleTwentyFive.defined)) =
      (-1452 : Scalar) / 67 := by
  rw [handednessDet_cap_neg_sameAxis ExampleTwentyFive.vector
      ExampleTwentyFive.defined transversal perpendicular]
  unfold capDenominator
  rw [ExampleTwentyFive.quadrance, quadrance]
  rw [show (1 + 66 : Scalar) = 67 by ring1]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

theorem inverse_handedness_negative :
    handednessDet ExampleTwentyFive.vector transversal
        (cap (Vector.neg ExampleTwentyFive.vector)
          (cap_neg_defined ExampleTwentyFive.vector
            ExampleTwentyFive.defined)) < 0 := by
  rw [inverse_handedness_value]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  change -((1452 : Scalar)) * (67 : Scalar)⁻¹ < 0
  rw [neg_mul]
  exact neg_lt_zero.mpr
    (RFAP.ConstructiveFraction.mul_pos_direct
      (RFAP.ConstructiveFraction.natCast_pos_direct (by decide))
      (RFAP.ConstructiveFraction.inv_pos_direct
        (RFAP.ConstructiveFraction.natCast_pos_direct (by decide))))

end ExampleFortyThree

namespace ExampleFortyFour

abbrev Scalar := DivineProportions.FieldFive.Element

theorem handedness_invisible (transversal : Vector Scalar)
    (perpendicular :
      transversal.Perpendicular ExampleTwentySeven.vector) :
    handednessDet ExampleTwentySeven.vector transversal
        (cap ExampleTwentySeven.vector ExampleTwentySeven.defined) = 0 := by
  exact handednessDet_cap_of_null ExampleTwentySeven.vector
    ExampleTwentySeven.defined transversal perpendicular
    ExampleTwentySeven.null

theorem inverse_product :
    Matrix3.mul
        (cap ExampleTwentySeven.vector ExampleTwentySeven.defined)
        (cap (Vector.neg ExampleTwentySeven.vector)
          (cap_neg_defined ExampleTwentySeven.vector
            ExampleTwentySeven.defined)) = Matrix3.identity :=
  cap_mul_cap_neg ExampleTwentySeven.vector ExampleTwentySeven.defined

theorem reverse_inverse_product :
    Matrix3.mul
        (cap (Vector.neg ExampleTwentySeven.vector)
          (cap_neg_defined ExampleTwentySeven.vector
            ExampleTwentySeven.defined))
        (cap ExampleTwentySeven.vector ExampleTwentySeven.defined) =
      Matrix3.identity :=
  cap_neg_mul_cap ExampleTwentySeven.vector ExampleTwentySeven.defined

theorem inverse_distinct :
    cap ExampleTwentySeven.vector ExampleTwentySeven.defined ≠
      cap (Vector.neg ExampleTwentySeven.vector)
        (cap_neg_defined ExampleTwentySeven.vector
          ExampleTwentySeven.defined) := by
  decide

theorem not_involution :
    Matrix3.mul
        (cap ExampleTwentySeven.vector ExampleTwentySeven.defined)
        (cap ExampleTwentySeven.vector ExampleTwentySeven.defined) ≠
      Matrix3.identity := by
  decide

theorem inverse_not_involution :
    Matrix3.mul
        (cap (Vector.neg ExampleTwentySeven.vector)
          (cap_neg_defined ExampleTwentySeven.vector
            ExampleTwentySeven.defined))
        (cap (Vector.neg ExampleTwentySeven.vector)
          (cap_neg_defined ExampleTwentySeven.vector
            ExampleTwentySeven.defined)) ≠ Matrix3.identity := by
  decide

end ExampleFortyFour

end RationalRotations
