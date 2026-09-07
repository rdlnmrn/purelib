import RationalRotations.HalfSpreads

/-!
# Rational rotations, section 7: recovering the anchor

The paper's boxed antisymmetric formula is the executable definition of a
rotation's anchor.  An explicit adjugate inverse for `I + ρ` ties that cached
value to the big Cayley transform; downstream proofs use the cached formula
rather than recomputing the inverse.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- Definition 34: the big Cayley transform, with its inverse supplied by the
displayed adjugate certificate. -/
def bigCayley (matrix : Matrix3 K)
    (defined : Matrix3.determinant
      (Matrix3.add Matrix3.identity matrix) ≠ 0) : Matrix3 K :=
  Matrix3.mul (Matrix3.sub Matrix3.identity matrix)
    (Matrix3.inverse (Matrix3.add Matrix3.identity matrix) defined)

/-- The antisymmetric part `1/2 (M-Mᵀ)` used in Theorem 35. -/
def antisymmetricPart (matrix : Matrix3 K) : Matrix3 K :=
  Matrix3.scale (1 / 2) (Matrix3.sub matrix (Matrix3.transpose matrix))

/-- Definition 34, cached in the boxed formula of Theorem 35.5. -/
def rotationAnchor (rotation : Rotation K)
    (_notHalfTurn : halfSpread rotation ≠ 1) : Matrix3 K :=
  Matrix3.scale (1 / (1 + Matrix3.trace rotation.matrix))
    (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix))

/-- The unique displayed vector encoded by a rotation's cached anchor. -/
def rotationAnchorVector (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1) : Vector K :=
  anchorVector (rotationAnchor rotation notHalfTurn)

private theorem one_ne_zero_of_two_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply twoNonzero
  calc
    (2 : K) = 2 * 1 := by ring1
    _ = 2 * 0 := by rw [oneZero]
    _ = 0 := by ring1

private theorem four_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (4 : K) ≠ 0 := by
  have productNonzero :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero

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

private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel := RFAP.ExplicitField.mul_inv_cancel
    leftDenominator leftNonzero
  have rightCancel := RFAP.ExplicitField.mul_inv_cancel
    rightDenominator rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

/-- The trace denominator is four times the complementary half spread. -/
theorem one_add_trace_eq_four_mul_one_sub_halfSpread
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    1 + Matrix3.trace rotation.matrix =
      4 * (1 - halfSpread rotation) := by
  have fourNonzero := four_ne_zero twoNonzero
  have fourHalfSpread :
      4 * halfSpread rotation = 3 - Matrix3.trace rotation.matrix := by
    unfold halfSpread
    calc
      4 * ((3 - Matrix3.trace rotation.matrix) / 4) =
          ((3 - Matrix3.trace rotation.matrix) / 4) * 4 := by ring1
      _ = 3 - Matrix3.trace rotation.matrix :=
        RFAP.ExplicitField.div_mul_cancel _ fourNonzero
  calc
    1 + Matrix3.trace rotation.matrix =
        4 * (1 - halfSpread rotation) +
          (4 * halfSpread rotation -
            (3 - Matrix3.trace rotation.matrix)) := by ring1
    _ = 4 * (1 - halfSpread rotation) := by
      rw [fourHalfSpread]
      ring1

theorem rotationAnchorDenominator_ne_zero (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    1 + Matrix3.trace rotation.matrix ≠ 0 := by
  have complementNonzero : 1 - halfSpread rotation ≠ 0 := by
    intro complementZero
    apply notHalfTurn
    calc
      halfSpread rotation = 1 - (1 - halfSpread rotation) := by ring1
      _ = 1 := by rw [complementZero]; ring1
  rw [one_add_trace_eq_four_mul_one_sub_halfSpread rotation twoNonzero]
  exact RFAP.ExplicitField.mul_ne_zero
    (four_ne_zero twoNonzero) complementNonzero

/-- For a rotation, `det(I+ρ)=2(1+tr ρ)`. -/
theorem determinant_identity_add_rotation (rotation : Rotation K) :
    Matrix3.determinant
        (Matrix3.add Matrix3.identity rotation.matrix) =
      2 * (1 + Matrix3.trace rotation.matrix) := by
  have negatedSum :
      Matrix3.sub (Matrix3.scale (-1 : K) Matrix3.identity)
          rotation.matrix =
        Matrix3.neg (Matrix3.add Matrix3.identity rotation.matrix) := by
    ext <;> unfold Matrix3.sub Matrix3.scale Matrix3.identity Matrix3.neg
      Matrix3.add <;> ring1
  calc
    Matrix3.determinant
        (Matrix3.add Matrix3.identity rotation.matrix) =
      -Matrix3.determinant
        (Matrix3.neg
          (Matrix3.add Matrix3.identity rotation.matrix)) := by
            rw [Matrix3.determinant_neg]
            ring1
    _ = -Matrix3.characteristicValue rotation.matrix (-1) := by
      unfold Matrix3.characteristicValue
      rw [negatedSum]
    _ = 2 * (1 + Matrix3.trace rotation.matrix) := by
      rw [Matrix3.characteristicValue_expansion,
        principalTrace_rotation, rotation.determinantOne]
      ring1

theorem determinant_identity_add_rotation_ne_zero (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.determinant
        (Matrix3.add Matrix3.identity rotation.matrix) ≠ 0 := by
  rw [determinant_identity_add_rotation]
  exact RFAP.ExplicitField.mul_ne_zero twoNonzero
    (rotationAnchorDenominator_ne_zero rotation notHalfTurn twoNonzero)

/-- Definition 34's exact domain equivalence: the big Cayley denominator is
invertible precisely away from half turns. -/
theorem determinant_identity_add_rotation_ne_zero_iff
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.determinant
        (Matrix3.add Matrix3.identity rotation.matrix) ≠ 0 ↔
      halfSpread rotation ≠ 1 := by
  constructor
  · intro determinantNonzero halfTurnSpread
    apply determinantNonzero
    rw [determinant_identity_add_rotation,
      one_add_trace_eq_four_mul_one_sub_halfSpread rotation twoNonzero,
      halfTurnSpread]
    ring1
  · intro notHalfTurn
    exact determinant_identity_add_rotation_ne_zero rotation notHalfTurn
      twoNonzero

/-- The left inverse relation missing from the stored row-orthogonality
certificate. -/
theorem transpose_mul_rotation (rotation : Rotation K) :
    Matrix3.mul (Matrix3.transpose rotation.matrix) rotation.matrix =
      Matrix3.identity := by
  calc
    Matrix3.mul (Matrix3.transpose rotation.matrix) rotation.matrix =
        Matrix3.mul (Matrix3.adjugate rotation.matrix) rotation.matrix := by
          rw [adjugate_rotation]
    _ = Matrix3.scale (Matrix3.determinant rotation.matrix)
        Matrix3.identity := Matrix3.adjugate_mul _
    _ = Matrix3.identity := by
      rw [rotation.determinantOne]
      ext <;> unfold Matrix3.scale Matrix3.identity <;> ring1

/-- Cayley--Hamilton reduction specialized to a rotation. -/
theorem rotation_square_sub_transpose (rotation : Rotation K) :
    Matrix3.sub (Matrix3.mul rotation.matrix rotation.matrix)
        (Matrix3.transpose rotation.matrix) =
      Matrix3.scale (Matrix3.trace rotation.matrix)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
  rw [← adjugate_rotation rotation, Matrix3.adjugate_expansion,
    principalTrace_rotation]
  ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale Matrix3.identity <;>
    ring1

private theorem anchorNumerator_mul_rotationSum (rotation : Rotation K) :
    Matrix3.mul
        (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix))
        (Matrix3.add rotation.matrix Matrix3.identity) =
      Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
  calc
    Matrix3.mul
        (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix))
        (Matrix3.add rotation.matrix Matrix3.identity) =
      Matrix3.sub
        (Matrix3.add (Matrix3.mul rotation.matrix rotation.matrix)
          rotation.matrix)
        (Matrix3.add Matrix3.identity
          (Matrix3.transpose rotation.matrix)) := by
            rw [Matrix3.mul_sub_left, Matrix3.mul_add_right,
              Matrix3.mul_add_right, Matrix3.mul_identity,
              Matrix3.mul_identity, transpose_mul_rotation]
    _ = Matrix3.add
        (Matrix3.sub (Matrix3.mul rotation.matrix rotation.matrix)
          (Matrix3.transpose rotation.matrix))
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          ext <;> unfold Matrix3.add Matrix3.sub <;> ring1
    _ = Matrix3.add
        (Matrix3.scale (Matrix3.trace rotation.matrix)
          (Matrix3.sub rotation.matrix Matrix3.identity))
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          rw [rotation_square_sub_transpose]
    _ = Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale <;> ring1

private theorem rotationSum_mul_anchorNumerator (rotation : Rotation K) :
    Matrix3.mul
        (Matrix3.add rotation.matrix Matrix3.identity)
        (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix)) =
      Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
  calc
    Matrix3.mul
        (Matrix3.add rotation.matrix Matrix3.identity)
        (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix)) =
      Matrix3.sub
        (Matrix3.add (Matrix3.mul rotation.matrix rotation.matrix)
          rotation.matrix)
        (Matrix3.add Matrix3.identity
          (Matrix3.transpose rotation.matrix)) := by
            rw [Matrix3.mul_sub_right, Matrix3.mul_add_left,
              Matrix3.mul_add_left, Matrix3.identity_mul,
              Matrix3.identity_mul, rotation.orthogonal]
    _ = Matrix3.add
        (Matrix3.sub (Matrix3.mul rotation.matrix rotation.matrix)
          (Matrix3.transpose rotation.matrix))
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          ext <;> unfold Matrix3.add Matrix3.sub <;> ring1
    _ = Matrix3.add
        (Matrix3.scale (Matrix3.trace rotation.matrix)
          (Matrix3.sub rotation.matrix Matrix3.identity))
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          rw [rotation_square_sub_transpose]
    _ = Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale <;> ring1

theorem rotationAnchor_mul_rotationSum (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul (rotationAnchor rotation notHalfTurn)
        (Matrix3.add rotation.matrix Matrix3.identity) =
      Matrix3.sub rotation.matrix Matrix3.identity := by
  have denominatorNonzero := rotationAnchorDenominator_ne_zero rotation
    notHalfTurn twoNonzero
  have coefficient :
      (1 / (1 + Matrix3.trace rotation.matrix)) *
        (1 + Matrix3.trace rotation.matrix) = (1 : K) := by
    exact RFAP.ExplicitField.div_mul_cancel 1 denominatorNonzero
  unfold rotationAnchor
  rw [Matrix3.mul_scale_left, anchorNumerator_mul_rotationSum,
    Matrix3.scale_scale, coefficient]
  ext <;> unfold Matrix3.scale <;> ring1

theorem rotationSum_mul_rotationAnchor (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul (Matrix3.add rotation.matrix Matrix3.identity)
        (rotationAnchor rotation notHalfTurn) =
      Matrix3.sub rotation.matrix Matrix3.identity := by
  have denominatorNonzero := rotationAnchorDenominator_ne_zero rotation
    notHalfTurn twoNonzero
  have coefficient :
      (1 / (1 + Matrix3.trace rotation.matrix)) *
        (1 + Matrix3.trace rotation.matrix) = (1 : K) :=
    RFAP.ExplicitField.div_mul_cancel 1 denominatorNonzero
  unfold rotationAnchor
  rw [Matrix3.mul_scale_right, rotationSum_mul_anchorNumerator,
    Matrix3.scale_scale, coefficient]
  ext <;> unfold Matrix3.scale <;> ring1

/-- Definition 34 agrees with the cached boxed formula. -/
theorem rotationAnchor_eq_bigCayleyFormula (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationAnchor rotation notHalfTurn =
      Matrix3.mul (Matrix3.sub rotation.matrix Matrix3.identity)
        (Matrix3.inverse
          (Matrix3.add Matrix3.identity rotation.matrix)
          (determinant_identity_add_rotation_ne_zero rotation notHalfTurn
            twoNonzero)) := by
  let sum := Matrix3.add Matrix3.identity rotation.matrix
  let sumInverse := Matrix3.inverse sum
    (determinant_identity_add_rotation_ne_zero rotation notHalfTurn
      twoNonzero)
  have rightInverse : Matrix3.mul sum sumInverse = Matrix3.identity :=
    Matrix3.mul_inverse sum _
  calc
    rotationAnchor rotation notHalfTurn =
        Matrix3.mul (rotationAnchor rotation notHalfTurn) Matrix3.identity := by
          rw [Matrix3.mul_identity]
    _ = Matrix3.mul (rotationAnchor rotation notHalfTurn)
        (Matrix3.mul sum sumInverse) := by rw [rightInverse]
    _ = Matrix3.mul
        (Matrix3.mul (rotationAnchor rotation notHalfTurn) sum) sumInverse := by
          rw [Matrix3.mul_assoc]
    _ = Matrix3.mul (Matrix3.sub rotation.matrix Matrix3.identity)
        sumInverse := by
          unfold sum
          rw [show Matrix3.add Matrix3.identity rotation.matrix =
              Matrix3.add rotation.matrix Matrix3.identity by
                ext <;> unfold Matrix3.add <;> ring1,
            rotationAnchor_mul_rotationSum rotation notHalfTurn twoNonzero]
    _ = Matrix3.mul (Matrix3.sub rotation.matrix Matrix3.identity)
        (Matrix3.inverse
          (Matrix3.add Matrix3.identity rotation.matrix)
          (determinant_identity_add_rotation_ne_zero rotation notHalfTurn
            twoNonzero)) := by
          rfl

/-- The anchor is the negative big Cayley transform. -/
theorem rotationAnchor_eq_neg_bigCayley (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationAnchor rotation notHalfTurn =
      Matrix3.neg
        (bigCayley rotation.matrix
          (determinant_identity_add_rotation_ne_zero rotation notHalfTurn
            twoNonzero)) := by
  rw [rotationAnchor_eq_bigCayleyFormula rotation notHalfTurn twoNonzero]
  unfold bigCayley
  ext <;> unfold Matrix3.mul Matrix3.sub Matrix3.neg <;> ring1

/-- Theorem 35.1: the recovered anchor is antisymmetric. -/
theorem rotationAnchor_isAntisymmetric (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1) :
    Matrix3.IsAntisymmetric (rotationAnchor rotation notHalfTurn) := by
  unfold Matrix3.IsAntisymmetric rotationAnchor
  rw [Matrix3.transpose_scale, Matrix3.transpose_sub,
    Matrix3.transpose_transpose]
  ext <;> unfold Matrix3.transpose Matrix3.sub Matrix3.neg Matrix3.scale <;>
    ring1

/-- The recovered vector re-encodes the recovered anchor. -/
theorem anchor_rotationAnchorVector (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    anchor (rotationAnchorVector rotation notHalfTurn) =
      rotationAnchor rotation notHalfTurn := by
  exact anchor_anchorVector_of_isAntisymmetric _ twoNonzero
    (rotationAnchor_isAntisymmetric rotation notHalfTurn)

/-- Theorem 35.1: uniqueness of the recovered anchor vector. -/
theorem rotationAnchorVector_unique (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) (vector : Vector K)
    (encodes : anchor vector = rotationAnchor rotation notHalfTurn) :
    vector = rotationAnchorVector rotation notHalfTurn := by
  apply anchor_injective
  rw [encodes, anchor_rotationAnchorVector rotation notHalfTurn twoNonzero]

/-- Theorem 35.5 in exactly the paper's antisymmetric-part form. -/
theorem rotationAnchor_eq_antisymmetricPart (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationAnchor rotation notHalfTurn =
      Matrix3.scale (2 / (1 + Matrix3.trace rotation.matrix))
        (antisymmetricPart rotation.matrix) := by
  have twoCancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  unfold rotationAnchor antisymmetricPart
  rw [Matrix3.scale_scale]
  have coefficient :
      (2 / (1 + Matrix3.trace rotation.matrix)) * (1 / 2) =
        1 / (1 + Matrix3.trace rotation.matrix) := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 * (1 + Matrix3.trace rotation.matrix)⁻¹ *
          (1 * (2 : K)⁻¹) =
        (1 + Matrix3.trace rotation.matrix)⁻¹ *
          (2 * (2 : K)⁻¹) := by ring1
      _ = 1 * (1 + Matrix3.trace rotation.matrix)⁻¹ := by
        rw [twoCancel]
        ring1
  rw [coefficient]

/-- The cached anchor of a cap is the original anchor. -/
theorem rotationAnchor_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationAnchor (capRotation vector defined)
        (halfSpread_cap_ne_one vector defined twoNonzero) =
      anchor vector := by
  have traceDenominator :
      1 + Matrix3.trace (cap vector defined) =
        4 / capDenominator vector := by
    have cancel := RFAP.ExplicitField.mul_inv_cancel
      (capDenominator vector) defined
    rw [trace_cap]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      1 + (3 - vector.quadrance) * (capDenominator vector)⁻¹ =
          capDenominator vector * (capDenominator vector)⁻¹ +
            (3 - vector.quadrance) *
              (capDenominator vector)⁻¹ := by rw [cancel]
      _ = 4 * (capDenominator vector)⁻¹ := by
        unfold capDenominator
        ring1
  have scalarNonzero : 4 / capDenominator vector ≠ 0 :=
    RFAP.ExplicitField.div_ne_zero (four_ne_zero twoNonzero) defined
  unfold rotationAnchor capRotation
  rw [traceDenominator, cap_antisymmetric_part, Matrix3.scale_scale]
  have coefficient :
      (1 / (4 / capDenominator vector)) *
        (4 / capDenominator vector) = (1 : K) :=
    RFAP.ExplicitField.div_mul_cancel 1 scalarNonzero
  rw [coefficient]
  ext <;> unfold Matrix3.scale <;> ring1

/-- The recovered anchor satisfies the Cayley relation with its rotation. -/
theorem identity_sub_rotationAnchor_mul_rotation (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul
        (Matrix3.sub Matrix3.identity
          (rotationAnchor rotation notHalfTurn))
        rotation.matrix =
      Matrix3.add Matrix3.identity
        (rotationAnchor rotation notHalfTurn) := by
  have expanded := rotationAnchor_mul_rotationSum rotation notHalfTurn
    twoNonzero
  rw [Matrix3.mul_add_right, Matrix3.mul_identity] at expanded
  have anchorTimesRotation :
      Matrix3.mul (rotationAnchor rotation notHalfTurn) rotation.matrix =
        Matrix3.sub (Matrix3.sub rotation.matrix Matrix3.identity)
          (rotationAnchor rotation notHalfTurn) :=
    Matrix3.eq_sub_of_add_eq expanded
  calc
    Matrix3.mul
        (Matrix3.sub Matrix3.identity
          (rotationAnchor rotation notHalfTurn))
        rotation.matrix =
      Matrix3.sub rotation.matrix
        (Matrix3.mul (rotationAnchor rotation notHalfTurn)
          rotation.matrix) := by
            rw [Matrix3.mul_sub_left, Matrix3.identity_mul]
    _ = Matrix3.sub rotation.matrix
        (Matrix3.sub (Matrix3.sub rotation.matrix Matrix3.identity)
          (rotationAnchor rotation notHalfTurn)) := by
            rw [anchorTimesRotation]
    _ = Matrix3.add Matrix3.identity
        (rotationAnchor rotation notHalfTurn) := by
          ext <;> unfold Matrix3.add Matrix3.sub <;> ring1

private theorem identity_sub_rotationAnchor_mul_rotationSum
    (rotation : Rotation K) (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul
        (Matrix3.sub Matrix3.identity
          (rotationAnchor rotation notHalfTurn))
        (Matrix3.add rotation.matrix Matrix3.identity) =
      Matrix3.scale 2 Matrix3.identity := by
  calc
    Matrix3.mul
        (Matrix3.sub Matrix3.identity
          (rotationAnchor rotation notHalfTurn))
        (Matrix3.add rotation.matrix Matrix3.identity) =
      Matrix3.sub (Matrix3.add rotation.matrix Matrix3.identity)
        (Matrix3.mul (rotationAnchor rotation notHalfTurn)
          (Matrix3.add rotation.matrix Matrix3.identity)) := by
            rw [Matrix3.mul_sub_left, Matrix3.identity_mul]
    _ = Matrix3.sub (Matrix3.add rotation.matrix Matrix3.identity)
        (Matrix3.sub rotation.matrix Matrix3.identity) := by
          rw [rotationAnchor_mul_rotationSum rotation notHalfTurn twoNonzero]
    _ = Matrix3.scale 2 Matrix3.identity := by
      ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale Matrix3.identity <;>
        ring1

private theorem identity_sub_rotationAnchor_has_rightInverse
    (rotation : Rotation K) (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul
        (Matrix3.sub Matrix3.identity
          (rotationAnchor rotation notHalfTurn))
        (Matrix3.scale (1 / 2)
          (Matrix3.add rotation.matrix Matrix3.identity)) =
      Matrix3.identity := by
  have coefficient : (1 / 2 : K) * 2 = 1 :=
    RFAP.ExplicitField.div_mul_cancel 1 twoNonzero
  rw [Matrix3.mul_scale_right,
    identity_sub_rotationAnchor_mul_rotationSum rotation notHalfTurn
      twoNonzero,
    Matrix3.scale_scale, coefficient]
  ext <;> unfold Matrix3.scale Matrix3.identity <;> ring1

/-- The anchor vector recovered from a non-half-turn rotation lies in the cap
domain. -/
theorem rotationAnchorVector_capDefined (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    capDenominator (rotationAnchorVector rotation notHalfTurn) ≠ 0 := by
  let anchorMatrix := rotationAnchor rotation notHalfTurn
  let rightInverse := Matrix3.scale (1 / 2)
    (Matrix3.add rotation.matrix Matrix3.identity)
  have inverseCertificate :
      Matrix3.mul (Matrix3.sub Matrix3.identity anchorMatrix) rightInverse =
        Matrix3.identity := by
    unfold anchorMatrix rightInverse
    exact identity_sub_rotationAnchor_has_rightInverse rotation notHalfTurn
      twoNonzero
  have determinantProduct := congrArg Matrix3.determinant inverseCertificate
  rw [Matrix3.determinant_mul, Matrix3.determinant_identity]
    at determinantProduct
  have determinantNonzero :
      Matrix3.determinant
        (Matrix3.sub Matrix3.identity anchorMatrix) ≠ 0 := by
    intro determinantZero
    rw [determinantZero, zero_mul] at determinantProduct
    exact (one_ne_zero_of_two_ne_zero twoNonzero) determinantProduct.symm
  rw [← determinant_identity_sub_anchor]
  have encodes := anchor_rotationAnchorVector rotation notHalfTurn twoNonzero
  rw [encodes]
  exact determinantNonzero

/-- Theorem 35.2: taking the cap of the recovered anchor returns the original
rotation matrix. -/
theorem cap_rotationAnchor (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    cap (rotationAnchorVector rotation notHalfTurn)
        (rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero) =
      rotation.matrix := by
  let vector := rotationAnchorVector rotation notHalfTurn
  let capDefined := rotationAnchorVector_capDefined rotation notHalfTurn
    twoNonzero
  have encodes : anchor vector = rotationAnchor rotation notHalfTurn := by
    unfold vector
    exact anchor_rotationAnchorVector rotation notHalfTurn twoNonzero
  have rotationRelation := identity_sub_rotationAnchor_mul_rotation rotation
    notHalfTurn twoNonzero
  rw [← encodes] at rotationRelation
  have capRelation := identity_sub_anchor_mul_cap vector capDefined
  have inverseLeft := anchorResolventInverse_right vector capDefined
  calc
    cap vector capDefined =
        Matrix3.mul Matrix3.identity (cap vector capDefined) := by
          rw [Matrix3.identity_mul]
    _ = Matrix3.mul
        (Matrix3.mul (anchorResolventInverse vector capDefined)
          (Matrix3.sub Matrix3.identity (anchor vector)))
        (cap vector capDefined) := by rw [inverseLeft]
    _ = Matrix3.mul (anchorResolventInverse vector capDefined)
        (Matrix3.mul (Matrix3.sub Matrix3.identity (anchor vector))
          (cap vector capDefined)) := by rw [Matrix3.mul_assoc]
    _ = Matrix3.mul (anchorResolventInverse vector capDefined)
        (Matrix3.add Matrix3.identity (anchor vector)) := by
          rw [capRelation]
    _ = Matrix3.mul (anchorResolventInverse vector capDefined)
        (Matrix3.mul (Matrix3.sub Matrix3.identity (anchor vector))
          rotation.matrix) := by rw [rotationRelation]
    _ = Matrix3.mul
        (Matrix3.mul (anchorResolventInverse vector capDefined)
          (Matrix3.sub Matrix3.identity (anchor vector)))
        rotation.matrix := by rw [Matrix3.mul_assoc]
    _ = rotation.matrix := by rw [inverseLeft, Matrix3.identity_mul]

/-- Theorem 35.3: a rotation fixes its recovered anchor vector. -/
theorem rowMul_rotationAnchorVector (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul (rotationAnchorVector rotation notHalfTurn)
        rotation.matrix =
      rotationAnchorVector rotation notHalfTurn := by
  rw [← cap_rotationAnchor rotation notHalfTurn twoNonzero]
  exact rowMul_self_cap _ _

/-- The half spread is unchanged when the rotation is replaced by the cap of
its recovered anchor. -/
private theorem halfSpread_recoveredCap (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread
        (capRotation (rotationAnchorVector rotation notHalfTurn)
          (rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero)) =
      halfSpread rotation := by
  have traceEqual := congrArg Matrix3.trace
    (cap_rotationAnchor rotation notHalfTurn twoNonzero)
  unfold halfSpread capRotation
  rw [traceEqual]

/-- Theorem 35.4: quadrance of the recovered anchor vector. -/
theorem quadrance_rotationAnchorVector (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (rotationAnchorVector rotation notHalfTurn).quadrance =
      halfSpread rotation / (1 - halfSpread rotation) := by
  let vector := rotationAnchorVector rotation notHalfTurn
  let defined := rotationAnchorVector_capDefined rotation notHalfTurn
    twoNonzero
  have recovered := quadrance_eq_halfSpread_div_one_sub vector defined
    twoNonzero
  rw [halfSpread_recoveredCap rotation notHalfTurn twoNonzero] at recovered
  exact recovered

namespace ExampleThirtySix

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def rotation : Rotation Scalar :=
  capRotation ExampleTwentyFive.vector ExampleTwentyFive.defined

private theorem twoNonzero : (2 : Scalar) ≠ 0 := by
  intro castZero
  exact (by decide : (2 : Nat) ≠ 0)
    (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

private theorem sixtySevenNonzero : (67 : Scalar) ≠ 0 := by
  intro castZero
  exact (by decide : (67 : Nat) ≠ 0)
    (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

private theorem trace_denominator_identity
    {F : Type*} [RFAP.ExplicitField F] (denominatorNonzero : (67 : F) ≠ 0) :
    1 + (-63 : F) / 67 = 4 / 67 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel (67 : F)
    denominatorNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 + (-63 : F) * (67 : F)⁻¹ =
        67 * (67 : F)⁻¹ + (-63 : F) * (67 : F)⁻¹ := by
          rw [cancel]
    _ = 4 * (67 : F)⁻¹ := by ring1

private theorem antisymmetricPart_numeric
    {F : Type*} [RFAP.ExplicitField F] (twoNonzero : (2 : F) ≠ 0) :
    Matrix3.scale ((1 / 2 : F) * (4 / 67))
        (anchor (⟨4, 1, 7⟩ : Vector F)) =
      Matrix3.scale (1 / 67)
        ⟨0, 14, -2, -14, 0, 8, 2, -8, 0⟩ := by
  have twoCancel := RFAP.ExplicitField.mul_inv_cancel (2 : F) twoNonzero
  have coefficient :
      (1 / 2 : F) * (4 / 67) = 2 / 67 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      1 * (2 : F)⁻¹ * (4 * (67 : F)⁻¹) =
          (2 * (67 : F)⁻¹) * (2 * (2 : F)⁻¹) := by ring1
      _ = 2 * (67 : F)⁻¹ := by rw [twoCancel]; ring1
  rw [coefficient]
  ext <;> unfold Matrix3.scale anchor <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1

theorem trace_value : Matrix3.trace rotation.matrix = (-63 : Scalar) / 67 := by
  unfold rotation
  change Matrix3.trace
      (cap ExampleTwentyFive.vector ExampleTwentyFive.defined) =
    (-63 : Scalar) / 67
  rw [trace_cap]
  unfold capDenominator
  rw [ExampleTwentyFive.quadrance]
  have numerator : (3 - 66 : Scalar) = -63 := by ring1
  have denominator : (1 + 66 : Scalar) = 67 := by ring1
  rw [numerator, denominator]

theorem trace_denominator :
    1 + Matrix3.trace rotation.matrix = (4 : Scalar) / 67 := by
  rw [trace_value]
  exact trace_denominator_identity sixtySevenNonzero

def displayedAntisymmetricPart : Matrix3 Scalar :=
  Matrix3.scale (1 / 67) ⟨0, 14, -2, -14, 0, 8, 2, -8, 0⟩

theorem antisymmetricPart_displayed :
    antisymmetricPart rotation.matrix = displayedAntisymmetricPart := by
  have denominator :
      capDenominator ExampleTwentyFive.vector = (67 : Scalar) := by
    unfold capDenominator
    rw [ExampleTwentyFive.quadrance]
    ring1
  unfold rotation capRotation antisymmetricPart displayedAntisymmetricPart
  rw [cap_antisymmetric_part, denominator, Matrix3.scale_scale]
  exact antisymmetricPart_numeric twoNonzero

theorem recovered_anchor :
    rotationAnchor rotation
        (halfSpread_cap_ne_one ExampleTwentyFive.vector
          ExampleTwentyFive.defined twoNonzero) =
      anchor ExampleTwentyFive.vector := by
  exact rotationAnchor_cap ExampleTwentyFive.vector ExampleTwentyFive.defined
    twoNonzero

theorem recovered_vector :
    rotationAnchorVector rotation
        (halfSpread_cap_ne_one ExampleTwentyFive.vector
          ExampleTwentyFive.defined twoNonzero) =
      ExampleTwentyFive.vector := by
  apply anchor_injective
  rw [anchor_rotationAnchorVector rotation _ twoNonzero, recovered_anchor]

end ExampleThirtySix

/-- The vector in the anchor formula for a product of two reflections. -/
def reflectionProductAnchorVector (first second : Vector K)
    (_dotNonzero : Vector.dot first second ≠ 0) : Vector K :=
  Vector.scale (1 / Vector.dot first second) (Vector.cross first second)

/-- Non-perpendicular mirror normals give a non-half-turn product. -/
theorem reflectionProduct_notHalfTurn (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (dotNonzero : Vector.dot first second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread
        (reflectionProductRotation first second firstNonNull secondNonNull) ≠
      1 := by
  have denominatorNonzero : first.quadrance * second.quadrance ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  have dotSquareNonzero : Vector.dot first second ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero dotNonzero dotNonzero
  have quotientNonzero :
      Vector.dot first second ^ 2 /
        (first.quadrance * second.quadrance) ≠ 0 :=
    RFAP.ExplicitField.div_ne_zero dotSquareNonzero denominatorNonzero
  rw [halfSpread_reflectionProduct first second firstNonNull secondNonNull
    twoNonzero]
  intro spreadOne
  apply quotientNonzero
  unfold Vector.spread at spreadOne
  calc
    Vector.dot first second ^ 2 /
        (first.quadrance * second.quadrance) =
      1 - (1 - Vector.dot first second ^ 2 /
        (first.quadrance * second.quadrance)) := by ring1
    _ = 0 := by rw [spreadOne]; ring1

private theorem reflectionProduct_antisymmetricNumerator
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0) :
    Matrix3.sub
        (Matrix3.mul (reflection first firstNonNull)
          (reflection second secondNonNull))
        (Matrix3.transpose
          (Matrix3.mul (reflection first firstNonNull)
            (reflection second secondNonNull))) =
      Matrix3.scale
        (4 * Vector.dot first second /
          (first.quadrance * second.quadrance))
        (anchor (Vector.cross first second)) := by
  have productInverse := inverse_product firstNonNull secondNonNull
  rw [Matrix3.transpose_mul, reflection_transpose, reflection_transpose]
  ext <;> unfold reflection Matrix3.mul Matrix3.sub Matrix3.identity
    Matrix3.scale Matrix3.outer anchor Vector.cross <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv, productInverse] <;>
    unfold Vector.quadrance Vector.dot <;> ring1

private theorem one_add_trace_reflectionProduct
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0) :
    1 + Matrix3.trace
        (Matrix3.mul (reflection first firstNonNull)
          (reflection second secondNonNull)) =
      4 * Vector.dot first second ^ 2 /
        (first.quadrance * second.quadrance) := by
  rw [trace_reflection_product]
  unfold Vector.spread
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- Theorem 37: anchor of a product of two non-perpendicular reflections. -/
theorem rotationAnchor_reflectionProduct (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (dotNonzero : Vector.dot first second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationAnchor
        (reflectionProductRotation first second firstNonNull secondNonNull)
        (reflectionProduct_notHalfTurn first second firstNonNull secondNonNull
          dotNonzero twoNonzero) =
      anchor (reflectionProductAnchorVector first second dotNonzero) := by
  let quadranceProduct := first.quadrance * second.quadrance
  let traceDenominator :=
    4 * Vector.dot first second ^ 2 / quadranceProduct
  let numeratorScalar :=
    4 * Vector.dot first second / quadranceProduct
  have quadranceProductNonzero : quadranceProduct ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstNonNull secondNonNull
  have fourNonzero := four_ne_zero twoNonzero
  have dotSquareNonzero : Vector.dot first second ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero dotNonzero dotNonzero
  have traceDenominatorNonzero : traceDenominator ≠ 0 := by
    unfold traceDenominator
    exact RFAP.ExplicitField.div_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero dotSquareNonzero)
      quadranceProductNonzero
  have coefficient :
      (1 / traceDenominator) * numeratorScalar =
        1 / Vector.dot first second := by
    calc
      (1 / traceDenominator) * numeratorScalar =
          numeratorScalar / traceDenominator := by
            simp only [RFAP.ExplicitField.div_eq_mul_inv]
            ring1
      _ = 1 / Vector.dot first second := by
        apply div_eq_div_of_cross_mul traceDenominatorNonzero dotNonzero
        unfold numeratorScalar traceDenominator quadranceProduct
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  unfold rotationAnchor reflectionProductRotation
  rw [one_add_trace_reflectionProduct,
    reflectionProduct_antisymmetricNumerator, Matrix3.scale_scale]
  change Matrix3.scale ((1 / traceDenominator) * numeratorScalar)
      (anchor (Vector.cross first second)) =
    anchor (reflectionProductAnchorVector first second dotNonzero)
  rw [coefficient]
  exact (anchor_scale _ _).symm

/-- Theorem 37 in its displayed outer-product numerator form. -/
theorem rotationAnchor_reflectionProduct_outerFormula
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (dotNonzero : Vector.dot first second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationAnchor
        (reflectionProductRotation first second firstNonNull secondNonNull)
        (reflectionProduct_notHalfTurn first second firstNonNull secondNonNull
          dotNonzero twoNonzero) =
      Matrix3.scale (1 / Vector.dot first second)
        (Matrix3.sub (Matrix3.outer first second)
          (Matrix3.outer second first)) := by
  rw [rotationAnchor_reflectionProduct first second firstNonNull secondNonNull
      dotNonzero twoNonzero,
    outer_commutator_eq_anchor_cross]
  exact anchor_scale _ _

/-- The vector recovered by the general anchor construction is the explicit
cross-product formula of Theorem 37. -/
theorem rotationAnchorVector_reflectionProduct (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (dotNonzero : Vector.dot first second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationAnchorVector
        (reflectionProductRotation first second firstNonNull secondNonNull)
        (reflectionProduct_notHalfTurn first second firstNonNull secondNonNull
          dotNonzero twoNonzero) =
      reflectionProductAnchorVector first second dotNonzero := by
  apply anchor_injective
  rw [anchor_rotationAnchorVector _ _ twoNonzero,
    rotationAnchor_reflectionProduct first second firstNonNull secondNonNull
      dotNonzero twoNonzero]

/-- Theorem 38: quadrance of the two-reflection anchor vector. -/
theorem quadrance_reflectionProductAnchorVector (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (dotNonzero : Vector.dot first second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    (reflectionProductAnchorVector first second dotNonzero).quadrance =
      Vector.spread first second firstNonNull secondNonNull /
        (1 - Vector.spread first second firstNonNull secondNonNull) := by
  have recovered := quadrance_rotationAnchorVector
    (reflectionProductRotation first second firstNonNull secondNonNull)
    (reflectionProduct_notHalfTurn first second firstNonNull secondNonNull
      dotNonzero twoNonzero) twoNonzero
  rw [rotationAnchorVector_reflectionProduct first second firstNonNull
      secondNonNull dotNonzero twoNonzero,
    halfSpread_reflectionProduct first second firstNonNull secondNonNull
      twoNonzero] at recovered
  exact recovered

/-- Theorem 38's independent rescaling of the two mirror lines. -/
theorem reflectionProductAnchorVector_scale (first second : Vector K)
    (firstScalar secondScalar : K)
    (firstScalarNonzero : firstScalar ≠ 0)
    (secondScalarNonzero : secondScalar ≠ 0)
    (dotNonzero : Vector.dot first second ≠ 0) :
    reflectionProductAnchorVector
        (Vector.scale firstScalar first)
        (Vector.scale secondScalar second)
        (by
          rw [Vector.dot_scale_left, Vector.dot_scale_right]
          exact RFAP.ExplicitField.mul_ne_zero
            firstScalarNonzero
            (RFAP.ExplicitField.mul_ne_zero secondScalarNonzero
              dotNonzero)) =
      reflectionProductAnchorVector first second dotNonzero := by
  let factor := firstScalar * secondScalar
  have factorNonzero : factor ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero firstScalarNonzero secondScalarNonzero
  have factorCancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  have productInverse := inverse_product factorNonzero dotNonzero
  have coefficient :
      (1 / (factor * Vector.dot first second)) * factor =
        1 / Vector.dot first second := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv, productInverse]
    calc
      1 * (factor⁻¹ * (Vector.dot first second)⁻¹) * factor =
          (Vector.dot first second)⁻¹ * (factor * factor⁻¹) := by
            ring1
      _ = 1 * (Vector.dot first second)⁻¹ := by
        rw [factorCancel, mul_one, one_mul]
  unfold reflectionProductAnchorVector
  rw [Vector.dot_scale_left, Vector.dot_scale_right,
    Vector.cross_scale_left, Vector.cross_scale_right,
    Vector.scale_scale, Vector.scale_scale]
  have denominator :
      firstScalar * (secondScalar * Vector.dot first second) =
        factor * Vector.dot first second := by
    unfold factor
    ring1
  rw [denominator]
  have scaledCoefficient :
      1 / (factor * Vector.dot first second) * firstScalar * secondScalar =
        (1 / (factor * Vector.dot first second)) * factor := by
    unfold factor
    ring1
  rw [scaledCoefficient, coefficient]

namespace ExampleThirtyNine

abbrev Scalar := RFAP.ConstructiveFraction.Rational

private theorem twoNonzero : (2 : Scalar) ≠ 0 := by
  intro castZero
  exact (by decide : (2 : Nat) ≠ 0)
    (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

theorem dot_value :
    Vector.dot ExampleTwenty.first ExampleTwenty.second = (1 : Scalar) :=
  ExampleThirtyThree.dot_value

theorem dot_nonzero :
    Vector.dot ExampleTwenty.first ExampleTwenty.second ≠ (0 : Scalar) := by
  rw [dot_value]
  intro oneZero
  exact (by decide : (1 : Nat) ≠ 0)
    (RFAP.ConstructiveFraction.natCast_injective_direct oneZero)

theorem recovered_vector :
    reflectionProductAnchorVector ExampleTwenty.first ExampleTwenty.second
        dot_nonzero = ExampleTwenty.axis := by
  unfold reflectionProductAnchorVector
  rw [dot_value, ExampleTwenty.cross_displayed]
  have oneNonzero : (1 : Scalar) ≠ 0 := by
    intro oneZero
    exact (by decide : (1 : Nat) ≠ 0)
      (RFAP.ConstructiveFraction.natCast_injective_direct oneZero)
  have oneCancel := RFAP.ExplicitField.mul_inv_cancel (1 : Scalar) oneNonzero
  have oneDivOne : (1 : Scalar) / 1 = 1 := by
    rw [RFAP.ExplicitField.div_eq_mul_inv, oneCancel]
  rw [oneDivOne, Vector.one_scale]

theorem recovered_quadrance :
    (reflectionProductAnchorVector ExampleTwenty.first ExampleTwenty.second
      dot_nonzero).quadrance = (83 : Scalar) := by
  rw [recovered_vector]
  unfold ExampleTwenty.axis Vector.quadrance Vector.dot
  ring1

theorem half_twist :
    Vector.spread ExampleTwenty.first ExampleTwenty.second
        ExampleTwenty.first_nonNull ExampleTwenty.second_nonNull /
      (1 - Vector.spread ExampleTwenty.first ExampleTwenty.second
        ExampleTwenty.first_nonNull ExampleTwenty.second_nonNull) =
      (83 : Scalar) := by
  rw [← quadrance_reflectionProductAnchorVector ExampleTwenty.first
      ExampleTwenty.second ExampleTwenty.first_nonNull
      ExampleTwenty.second_nonNull dot_nonzero twoNonzero,
    recovered_quadrance]

end ExampleThirtyNine

/-! ### The missing half-turn classification used by Theorem 40 -/

private theorem trace_eq_neg_one_of_halfSpread_eq_one
    (rotation : Rotation K) (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.trace rotation.matrix = -1 := by
  have traceRelation :=
    one_add_trace_eq_four_mul_one_sub_halfSpread rotation twoNonzero
  rw [halfTurnSpread] at traceRelation
  calc
    Matrix3.trace rotation.matrix =
        (1 + Matrix3.trace rotation.matrix) - 1 := by ring1
    _ = -1 := by rw [traceRelation]; ring1

private theorem transpose_square_sub_rotation (rotation : Rotation K) :
    Matrix3.sub
        (Matrix3.mul (Matrix3.transpose rotation.matrix)
          (Matrix3.transpose rotation.matrix))
        rotation.matrix =
      Matrix3.scale (Matrix3.trace rotation.matrix)
        (Matrix3.sub (Matrix3.transpose rotation.matrix)
          Matrix3.identity) := by
  have transposed := congrArg Matrix3.transpose
    (rotation_square_sub_transpose rotation)
  simpa only [Matrix3.transpose_sub, Matrix3.transpose_mul,
    Matrix3.transpose_transpose, Matrix3.transpose_scale,
    Matrix3.transpose_identity, Matrix3.trace_transpose] using transposed

private theorem rotationAntisymmetricNumerator_square
    (rotation : Rotation K) :
    Matrix3.mul
        (Matrix3.sub rotation.matrix
          (Matrix3.transpose rotation.matrix))
        (Matrix3.sub rotation.matrix
          (Matrix3.transpose rotation.matrix)) =
      Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub
          (Matrix3.add rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.scale 2 Matrix3.identity)) := by
  calc
    Matrix3.mul
        (Matrix3.sub rotation.matrix
          (Matrix3.transpose rotation.matrix))
        (Matrix3.sub rotation.matrix
          (Matrix3.transpose rotation.matrix)) =
      Matrix3.sub
        (Matrix3.sub
          (Matrix3.mul rotation.matrix rotation.matrix)
          Matrix3.identity)
        (Matrix3.sub Matrix3.identity
          (Matrix3.mul (Matrix3.transpose rotation.matrix)
            (Matrix3.transpose rotation.matrix))) := by
              rw [Matrix3.mul_sub_right, Matrix3.mul_sub_left,
                Matrix3.mul_sub_left, rotation.orthogonal,
                transpose_mul_rotation]
    _ = Matrix3.add
        (Matrix3.add
          (Matrix3.sub
            (Matrix3.mul rotation.matrix rotation.matrix)
            (Matrix3.transpose rotation.matrix))
          (Matrix3.sub
            (Matrix3.mul (Matrix3.transpose rotation.matrix)
              (Matrix3.transpose rotation.matrix))
            rotation.matrix))
        (Matrix3.sub
          (Matrix3.add rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.scale 2 Matrix3.identity)) := by
            ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale
              Matrix3.identity <;> ring1
    _ = Matrix3.add
        (Matrix3.add
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (Matrix3.sub rotation.matrix Matrix3.identity))
          (Matrix3.scale (Matrix3.trace rotation.matrix)
            (Matrix3.sub (Matrix3.transpose rotation.matrix)
              Matrix3.identity)))
        (Matrix3.sub
          (Matrix3.add rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.scale 2 Matrix3.identity)) := by
            rw [rotation_square_sub_transpose,
              transpose_square_sub_rotation]
    _ = Matrix3.scale (1 + Matrix3.trace rotation.matrix)
        (Matrix3.sub
          (Matrix3.add rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.scale 2 Matrix3.identity)) := by
            ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale
              Matrix3.identity <;> ring1

private theorem scalar_eq_zero_of_two_mul_eq_zero
    (twoNonzero : (2 : K) ≠ 0) {value : K}
    (twiceZero : 2 * value = 0) : value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  calc
    value = (2 * (2 : K)⁻¹) * value := by rw [cancel, one_mul]
    _ = (2 * value) * (2 : K)⁻¹ := by ring1
    _ = 0 := by rw [twiceZero, zero_mul]

private theorem scalar_eq_zero_of_square_eq_zero [DecidableEq K]
    {value : K} (squareZero : value * value = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero valueZero valueZero) squareZero)

private theorem antisymmetric_eq_zero_of_square_eq_zero [DecidableEq K]
    (matrix : Matrix3 K) (twoNonzero : (2 : K) ≠ 0)
    (antisymmetric : matrix.IsAntisymmetric)
    (squareZero : Matrix3.mul matrix matrix = Matrix3.zero) :
    matrix = Matrix3.zero := by
  let vector := anchorVector matrix
  have encodes : anchor vector = matrix :=
    anchor_anchorVector_of_isAntisymmetric matrix twoNonzero antisymmetric
  have anchorSquareZero :
      Matrix3.mul (anchor vector) (anchor vector) = Matrix3.zero := by
    rw [encodes]
    exact squareZero
  have traceZero := congrArg Matrix3.trace anchorSquareZero
  rw [trace_anchor_product] at traceZero
  have traceMatrixZero :
      Matrix3.trace (Matrix3.zero : Matrix3 K) = 0 := by
    unfold Matrix3.trace
    unfold Matrix3.zero
    ring1
  rw [traceMatrixZero] at traceZero
  change -2 * vector.quadrance = 0 at traceZero
  have quadranceZero : vector.quadrance = 0 := by
    apply scalar_eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * vector.quadrance = -(-2 * vector.quadrance) := by ring1
      _ = 0 := by rw [traceZero]; ring1
  have outerZero : Matrix3.outer vector vector = Matrix3.zero := by
    calc
      Matrix3.outer vector vector =
          Matrix3.sub (Matrix3.outer vector vector)
            (Matrix3.scale vector.quadrance Matrix3.identity) := by
              rw [quadranceZero]
              ext <;> unfold Matrix3.sub Matrix3.scale Matrix3.identity <;>
                ring1
      _ = Matrix3.mul (anchor vector) (anchor vector) :=
        (anchor_square vector).symm
      _ = Matrix3.zero := anchorSquareZero
  have tSquare := congrArg Matrix3.tt outerZero
  have rSquare := congrArg Matrix3.rr outerZero
  have sSquare := congrArg Matrix3.ss outerZero
  change vector.t * vector.t = 0 at tSquare
  change vector.r * vector.r = 0 at rSquare
  change vector.s * vector.s = 0 at sSquare
  have vectorZero : vector = Vector.zero := by
    apply Vector.ext
    · exact scalar_eq_zero_of_square_eq_zero tSquare
    · exact scalar_eq_zero_of_square_eq_zero rSquare
    · exact scalar_eq_zero_of_square_eq_zero sSquare
  calc
    matrix = anchor vector := encodes.symm
    _ = anchor Vector.zero := by rw [vectorZero]
    _ = Matrix3.zero := by
      ext <;> unfold anchor <;> unfold Vector.zero Matrix3.zero <;> ring1

/-- A rotation of half spread one is symmetric.  This is the finite
classification step invoked, but not supplied, by the paper's proof of
Theorem 40. -/
theorem rotation_isSymmetric_of_halfSpread_eq_one [DecidableEq K]
    (rotation : Rotation K) (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.IsSymmetric rotation.matrix := by
  have traceValue := trace_eq_neg_one_of_halfSpread_eq_one rotation
    halfTurnSpread twoNonzero
  have squareZero := rotationAntisymmetricNumerator_square rotation
  rw [traceValue] at squareZero
  have numeratorSquareZero :
      Matrix3.mul
          (Matrix3.sub rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.sub rotation.matrix
            (Matrix3.transpose rotation.matrix)) =
        Matrix3.zero := by
    calc
      Matrix3.mul
          (Matrix3.sub rotation.matrix
            (Matrix3.transpose rotation.matrix))
          (Matrix3.sub rotation.matrix
            (Matrix3.transpose rotation.matrix)) =
        Matrix3.scale (1 + (-1 : K))
          (Matrix3.sub
            (Matrix3.add rotation.matrix
              (Matrix3.transpose rotation.matrix))
            (Matrix3.scale 2 Matrix3.identity)) := squareZero
      _ = Matrix3.zero := by
        ext <;> unfold Matrix3.scale Matrix3.zero <;> ring1
  have numeratorAntisymmetric :
      Matrix3.IsAntisymmetric
        (Matrix3.sub rotation.matrix
          (Matrix3.transpose rotation.matrix)) := by
    unfold Matrix3.IsAntisymmetric
    rw [Matrix3.transpose_sub, Matrix3.transpose_transpose]
    ext <;> unfold Matrix3.sub Matrix3.neg <;> ring1
  have numeratorZero := antisymmetric_eq_zero_of_square_eq_zero
    (Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix))
    twoNonzero numeratorAntisymmetric numeratorSquareZero
  unfold Matrix3.IsSymmetric
  exact (Matrix3.eq_of_sub_eq_zero numeratorZero).symm

/-- The symmetric idempotent projector onto the axis of a half turn. -/
def halfTurnProjector (rotation : Rotation K) : Matrix3 K :=
  Matrix3.scale (1 / 2)
    (Matrix3.add Matrix3.identity rotation.matrix)

private theorem halfTurnProjector_isSymmetric [DecidableEq K]
    (rotation : Rotation K) (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (halfTurnProjector rotation).IsSymmetric := by
  have rotationSymmetric := rotation_isSymmetric_of_halfSpread_eq_one
    rotation halfTurnSpread twoNonzero
  unfold Matrix3.IsSymmetric halfTurnProjector at *
  rw [Matrix3.transpose_scale, Matrix3.transpose_add,
    Matrix3.transpose_identity, rotationSymmetric]

private theorem halfTurnProjector_idempotent [DecidableEq K]
    (rotation : Rotation K) (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul (halfTurnProjector rotation) (halfTurnProjector rotation) =
      halfTurnProjector rotation := by
  have symmetric := rotation_isSymmetric_of_halfSpread_eq_one rotation
    halfTurnSpread twoNonzero
  have rotationSquare :
      Matrix3.mul rotation.matrix rotation.matrix = Matrix3.identity := by
    unfold Matrix3.IsSymmetric at symmetric
    calc
      Matrix3.mul rotation.matrix rotation.matrix =
          Matrix3.mul rotation.matrix
            (Matrix3.transpose rotation.matrix) := by rw [symmetric]
      _ = Matrix3.identity := rotation.orthogonal
  have twoCancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  have coefficient :
      (1 / 2 : K) * (1 / 2) * 2 = 1 / 2 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      1 * (2 : K)⁻¹ * (1 * (2 : K)⁻¹) * 2 =
          (2 : K)⁻¹ * (2 * (2 : K)⁻¹) := by ring1
      _ = 1 * (2 : K)⁻¹ := by rw [twoCancel, mul_one, one_mul]
  unfold halfTurnProjector
  rw [Matrix3.mul_scale_left, Matrix3.mul_scale_right,
    Matrix3.scale_scale, Matrix3.mul_add_left, Matrix3.mul_add_right,
    Matrix3.mul_add_right, Matrix3.identity_mul, Matrix3.identity_mul,
    Matrix3.mul_identity, rotationSquare]
  rw [show Matrix3.add
      (Matrix3.add Matrix3.identity rotation.matrix)
      (Matrix3.add rotation.matrix Matrix3.identity) =
        Matrix3.scale 2
          (Matrix3.add Matrix3.identity rotation.matrix) by
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.identity <;> ring1,
    Matrix3.scale_scale, coefficient]

private theorem halfTurnProjector_trace [DecidableEq K]
    (rotation : Rotation K) (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.trace (halfTurnProjector rotation) = 1 := by
  have traceValue := trace_eq_neg_one_of_halfSpread_eq_one rotation
    halfTurnSpread twoNonzero
  have twoCancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  unfold halfTurnProjector
  rw [Matrix3.trace_scale, Matrix3.trace_add, traceValue]
  unfold Matrix3.trace Matrix3.identity
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (1 * (2 : K)⁻¹) * (1 + 1 + 1 + -1) =
        2 * (2 : K)⁻¹ := by ring1
    _ = 1 := twoCancel

private theorem halfTurnProjector_adjugate [DecidableEq K]
    (rotation : Rotation K) (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.adjugate (halfTurnProjector rotation) = Matrix3.zero := by
  let projector := halfTurnProjector rotation
  have idempotent : Matrix3.mul projector projector = projector := by
    unfold projector
    exact halfTurnProjector_idempotent rotation halfTurnSpread twoNonzero
  have traceOne : Matrix3.trace projector = 1 := by
    unfold projector
    exact halfTurnProjector_trace rotation halfTurnSpread twoNonzero
  have traceSquare := congrArg Matrix3.trace idempotent
  rw [Matrix3.trace_square, traceOne] at traceSquare
  have principalZero : Matrix3.principalTrace projector = 0 := by
    apply scalar_eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * Matrix3.principalTrace projector =
          1 ^ 2 -
            (1 ^ 2 - 2 * Matrix3.principalTrace projector) := by ring1
      _ = 0 := by rw [traceSquare]; ring1
  rw [Matrix3.adjugate_expansion, idempotent, traceOne, principalZero]
  ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale Matrix3.identity
    Matrix3.zero <;> ring1

omit [RFAP.ExplicitField K] in
private theorem symmetric_rt_eq_tr (matrix : Matrix3 K)
    (symmetric : matrix.IsSymmetric) : matrix.rt = matrix.tr := by
  have coordinate := congrArg Matrix3.tr symmetric
  unfold Matrix3.transpose at coordinate
  exact coordinate

omit [RFAP.ExplicitField K] in
private theorem symmetric_st_eq_ts (matrix : Matrix3 K)
    (symmetric : matrix.IsSymmetric) : matrix.st = matrix.ts := by
  have coordinate := congrArg Matrix3.ts symmetric
  unfold Matrix3.transpose at coordinate
  exact coordinate

omit [RFAP.ExplicitField K] in
private theorem symmetric_sr_eq_rs (matrix : Matrix3 K)
    (symmetric : matrix.IsSymmetric) : matrix.sr = matrix.rs := by
  have coordinate := congrArg Matrix3.rs symmetric
  unfold Matrix3.transpose at coordinate
  exact coordinate

private theorem entry_eq_one_div_mul {pivot target left right : K}
    (pivotNonzero : pivot ≠ 0)
    (minor : pivot * target = left * right) :
    target = (1 / pivot) * (left * right) := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel pivot pivotNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    target = 1 * target := by rw [one_mul]
    _ = (pivot * pivot⁻¹) * target := by rw [cancel]
    _ = pivot⁻¹ * (pivot * target) := by ring1
    _ = pivot⁻¹ * (left * right) := by rw [minor]
    _ = 1 * pivot⁻¹ * (left * right) := by ring1

private theorem rowT_quadrance_of_idempotent
    (matrix : Matrix3 K) (symmetric : matrix.IsSymmetric)
    (idempotent : Matrix3.mul matrix matrix = matrix) :
    (Matrix3.rowT matrix).quadrance = matrix.tt := by
  have coordinate := congrArg Matrix3.tt idempotent
  unfold Matrix3.mul at coordinate
  rw [symmetric_rt_eq_tr matrix symmetric,
    symmetric_st_eq_ts matrix symmetric] at coordinate
  unfold Matrix3.rowT Vector.quadrance Vector.dot
  exact coordinate

private theorem rowR_quadrance_of_idempotent
    (matrix : Matrix3 K) (symmetric : matrix.IsSymmetric)
    (idempotent : Matrix3.mul matrix matrix = matrix) :
    (Matrix3.rowR matrix).quadrance = matrix.rr := by
  have coordinate := congrArg Matrix3.rr idempotent
  unfold Matrix3.mul at coordinate
  rw [← symmetric_rt_eq_tr matrix symmetric,
    symmetric_sr_eq_rs matrix symmetric] at coordinate
  unfold Matrix3.rowR Vector.quadrance Vector.dot
  exact coordinate

private theorem rowS_quadrance_of_idempotent
    (matrix : Matrix3 K) (symmetric : matrix.IsSymmetric)
    (idempotent : Matrix3.mul matrix matrix = matrix) :
    (Matrix3.rowS matrix).quadrance = matrix.ss := by
  have coordinate := congrArg Matrix3.ss idempotent
  unfold Matrix3.mul at coordinate
  rw [← symmetric_st_eq_ts matrix symmetric,
    ← symmetric_sr_eq_rs matrix symmetric] at coordinate
  unfold Matrix3.rowS Vector.quadrance Vector.dot
  exact coordinate

private theorem reconstruct_from_rowT (matrix : Matrix3 K)
    (symmetric : matrix.IsSymmetric)
    (idempotent : Matrix3.mul matrix matrix = matrix)
    (adjugateZero : Matrix3.adjugate matrix = Matrix3.zero)
    (pivotNonzero : matrix.tt ≠ 0) :
    matrix = Matrix3.scale (1 / (Matrix3.rowT matrix).quadrance)
      (Matrix3.outer (Matrix3.rowT matrix) (Matrix3.rowT matrix)) := by
  have rtEq := symmetric_rt_eq_tr matrix symmetric
  have stEq := symmetric_st_eq_ts matrix symmetric
  have srEq := symmetric_sr_eq_rs matrix symmetric
  have rrMinor := congrArg Matrix3.ss adjugateZero
  unfold Matrix3.adjugate at rrMinor
  unfold Matrix3.zero at rrMinor
  rw [rtEq] at rrMinor
  have rrRelation : matrix.tt * matrix.rr = matrix.tr * matrix.tr :=
    sub_eq_zero.mp rrMinor
  have rsMinor := congrArg Matrix3.sr adjugateZero
  unfold Matrix3.adjugate at rsMinor
  unfold Matrix3.zero at rsMinor
  rw [stEq, srEq] at rsMinor
  have rsRelation : matrix.tt * matrix.rs = matrix.tr * matrix.ts :=
    (sub_eq_zero.mp rsMinor).symm
  have ssMinor := congrArg Matrix3.rr adjugateZero
  unfold Matrix3.adjugate at ssMinor
  unfold Matrix3.zero at ssMinor
  rw [stEq] at ssMinor
  have ssRelation : matrix.tt * matrix.ss = matrix.ts * matrix.ts :=
    sub_eq_zero.mp ssMinor
  rw [rowT_quadrance_of_idempotent matrix symmetric idempotent]
  apply Matrix3.ext
  all_goals
    unfold Matrix3.scale
    unfold Matrix3.outer
    unfold Matrix3.rowT
  · apply entry_eq_one_div_mul pivotNonzero
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    rw [rtEq]
    ring1
  · exact entry_eq_one_div_mul pivotNonzero rrRelation
  · exact entry_eq_one_div_mul pivotNonzero rsRelation
  · apply entry_eq_one_div_mul pivotNonzero
    rw [stEq]
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    rw [srEq]
    calc
      matrix.tt * matrix.rs = matrix.tr * matrix.ts := rsRelation
      _ = matrix.ts * matrix.tr := by ring1
  · exact entry_eq_one_div_mul pivotNonzero ssRelation

private theorem reconstruct_from_rowR (matrix : Matrix3 K)
    (symmetric : matrix.IsSymmetric)
    (idempotent : Matrix3.mul matrix matrix = matrix)
    (adjugateZero : Matrix3.adjugate matrix = Matrix3.zero)
    (pivotNonzero : matrix.rr ≠ 0) :
    matrix = Matrix3.scale (1 / (Matrix3.rowR matrix).quadrance)
      (Matrix3.outer (Matrix3.rowR matrix) (Matrix3.rowR matrix)) := by
  have rtEq := symmetric_rt_eq_tr matrix symmetric
  have stEq := symmetric_st_eq_ts matrix symmetric
  have srEq := symmetric_sr_eq_rs matrix symmetric
  have ttMinor := congrArg Matrix3.ss adjugateZero
  unfold Matrix3.adjugate at ttMinor
  unfold Matrix3.zero at ttMinor
  rw [rtEq] at ttMinor
  have ttRelation : matrix.rr * matrix.tt = matrix.rt * matrix.rt := by
    calc
      matrix.rr * matrix.tt = matrix.tt * matrix.rr := by ring1
      _ = matrix.tr * matrix.tr := sub_eq_zero.mp ttMinor
      _ = matrix.rt * matrix.rt := by rw [rtEq]
  have tsMinor := congrArg Matrix3.ts adjugateZero
  unfold Matrix3.adjugate at tsMinor
  unfold Matrix3.zero at tsMinor
  rw [rtEq] at tsMinor
  have tsRelation : matrix.rr * matrix.ts = matrix.rt * matrix.rs := by
    calc
      matrix.rr * matrix.ts = matrix.ts * matrix.rr := by ring1
      _ = matrix.tr * matrix.rs := (sub_eq_zero.mp tsMinor).symm
      _ = matrix.rt * matrix.rs := by rw [rtEq]
  have ssMinor := congrArg Matrix3.tt adjugateZero
  unfold Matrix3.adjugate at ssMinor
  unfold Matrix3.zero at ssMinor
  rw [srEq] at ssMinor
  have ssRelation : matrix.rr * matrix.ss = matrix.rs * matrix.rs :=
    sub_eq_zero.mp ssMinor
  rw [rowR_quadrance_of_idempotent matrix symmetric idempotent]
  apply Matrix3.ext
  all_goals
    unfold Matrix3.scale
    unfold Matrix3.outer
    unfold Matrix3.rowR
  · exact entry_eq_one_div_mul pivotNonzero ttRelation
  · apply entry_eq_one_div_mul pivotNonzero
    rw [rtEq]
    ring1
  · exact entry_eq_one_div_mul pivotNonzero tsRelation
  · apply entry_eq_one_div_mul pivotNonzero
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    rw [stEq]
    calc
      matrix.rr * matrix.ts = matrix.rt * matrix.rs := tsRelation
      _ = matrix.rs * matrix.rt := by ring1
  · apply entry_eq_one_div_mul pivotNonzero
    rw [srEq]
    ring1
  · exact entry_eq_one_div_mul pivotNonzero ssRelation

private theorem reconstruct_from_rowS (matrix : Matrix3 K)
    (symmetric : matrix.IsSymmetric)
    (idempotent : Matrix3.mul matrix matrix = matrix)
    (adjugateZero : Matrix3.adjugate matrix = Matrix3.zero)
    (pivotNonzero : matrix.ss ≠ 0) :
    matrix = Matrix3.scale (1 / (Matrix3.rowS matrix).quadrance)
      (Matrix3.outer (Matrix3.rowS matrix) (Matrix3.rowS matrix)) := by
  have rtEq := symmetric_rt_eq_tr matrix symmetric
  have stEq := symmetric_st_eq_ts matrix symmetric
  have srEq := symmetric_sr_eq_rs matrix symmetric
  have ttMinor := congrArg Matrix3.rr adjugateZero
  unfold Matrix3.adjugate at ttMinor
  unfold Matrix3.zero at ttMinor
  rw [stEq] at ttMinor
  have ttRelation : matrix.ss * matrix.tt = matrix.st * matrix.st := by
    calc
      matrix.ss * matrix.tt = matrix.tt * matrix.ss := by ring1
      _ = matrix.ts * matrix.ts := sub_eq_zero.mp ttMinor
      _ = matrix.st * matrix.st := by rw [stEq]
  have trMinor := congrArg Matrix3.tr adjugateZero
  unfold Matrix3.adjugate at trMinor
  unfold Matrix3.zero at trMinor
  rw [stEq] at trMinor
  have trRelation : matrix.ss * matrix.tr = matrix.st * matrix.sr := by
    calc
      matrix.ss * matrix.tr = matrix.tr * matrix.ss := by ring1
      _ = matrix.ts * matrix.sr := (sub_eq_zero.mp trMinor).symm
      _ = matrix.st * matrix.sr := by rw [stEq]
  have rrMinor := congrArg Matrix3.tt adjugateZero
  unfold Matrix3.adjugate at rrMinor
  unfold Matrix3.zero at rrMinor
  rw [srEq] at rrMinor
  have rrRelation : matrix.ss * matrix.rr = matrix.sr * matrix.sr := by
    calc
      matrix.ss * matrix.rr = matrix.rr * matrix.ss := by ring1
      _ = matrix.rs * matrix.rs := sub_eq_zero.mp rrMinor
      _ = matrix.sr * matrix.sr := by rw [srEq]
  rw [rowS_quadrance_of_idempotent matrix symmetric idempotent]
  apply Matrix3.ext
  all_goals
    unfold Matrix3.scale
    unfold Matrix3.outer
    unfold Matrix3.rowS
  · exact entry_eq_one_div_mul pivotNonzero ttRelation
  · exact entry_eq_one_div_mul pivotNonzero trRelation
  · apply entry_eq_one_div_mul pivotNonzero
    rw [stEq]
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    rw [rtEq]
    calc
      matrix.ss * matrix.tr = matrix.st * matrix.sr := trRelation
      _ = matrix.sr * matrix.st := by ring1
  · exact entry_eq_one_div_mul pivotNonzero rrRelation
  · apply entry_eq_one_div_mul pivotNonzero
    rw [srEq]
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    ring1
  · apply entry_eq_one_div_mul pivotNonzero
    ring1

/-- Cached executable data extracted from a displayed symmetric rank-one
projector. -/
structure RankOneProjectorWitness (matrix : Matrix3 K) where
  vector : Vector K
  nonNull : vector.quadrance ≠ 0
  reconstruction :
    matrix = Matrix3.scale (1 / vector.quadrance)
      (Matrix3.outer vector vector)

/-- Select a non-null row of a symmetric rank-one projector by testing its
three diagonal entries in order. -/
def rankOneProjectorWitness [DecidableEq K] (matrix : Matrix3 K)
    (symmetric : matrix.IsSymmetric)
    (idempotent : Matrix3.mul matrix matrix = matrix)
    (traceOne : Matrix3.trace matrix = 1)
    (adjugateZero : Matrix3.adjugate matrix = Matrix3.zero)
    (twoNonzero : (2 : K) ≠ 0) : RankOneProjectorWitness matrix := by
  by_cases ttZero : matrix.tt = 0
  · by_cases rrZero : matrix.rr = 0
    · have ssNonzero : matrix.ss ≠ 0 := by
        intro ssZero
        have oneZero : (1 : K) = 0 := by
          calc
            (1 : K) = Matrix3.trace matrix := traceOne.symm
            _ = 0 := by
              unfold Matrix3.trace
              rw [ttZero, rrZero, ssZero]
              ring1
        exact (one_ne_zero_of_two_ne_zero twoNonzero) oneZero
      refine
        { vector := Matrix3.rowS matrix
          nonNull := ?_
          reconstruction := reconstruct_from_rowS matrix symmetric idempotent
            adjugateZero ssNonzero }
      rw [rowS_quadrance_of_idempotent matrix symmetric idempotent]
      exact ssNonzero
    · refine
        { vector := Matrix3.rowR matrix
          nonNull := ?_
          reconstruction := reconstruct_from_rowR matrix symmetric idempotent
            adjugateZero rrZero }
      rw [rowR_quadrance_of_idempotent matrix symmetric idempotent]
      exact rrZero
  · refine
      { vector := Matrix3.rowT matrix
        nonNull := ?_
        reconstruction := reconstruct_from_rowT matrix symmetric idempotent
          adjugateZero ttZero }
    rw [rowT_quadrance_of_idempotent matrix symmetric idempotent]
    exact ttZero

/-- The cached non-null axis extracted from a half-spread-one rotation. -/
def halfTurnAxisWitness [DecidableEq K] (rotation : Rotation K)
    (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    RankOneProjectorWitness (halfTurnProjector rotation) :=
  rankOneProjectorWitness (halfTurnProjector rotation)
    (halfTurnProjector_isSymmetric rotation halfTurnSpread twoNonzero)
    (halfTurnProjector_idempotent rotation halfTurnSpread twoNonzero)
    (halfTurnProjector_trace rotation halfTurnSpread twoNonzero)
    (halfTurnProjector_adjugate rotation halfTurnSpread twoNonzero)
    twoNonzero

/-- The executable axis vector selected for a half-spread-one rotation. -/
def halfTurnAxis [DecidableEq K] (rotation : Rotation K)
    (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) : Vector K :=
  (halfTurnAxisWitness rotation halfTurnSpread twoNonzero).vector

theorem halfTurnAxis_nonNull [DecidableEq K] (rotation : Rotation K)
    (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (halfTurnAxis rotation halfTurnSpread twoNonzero).quadrance ≠ 0 :=
  (halfTurnAxisWitness rotation halfTurnSpread twoNonzero).nonNull

theorem halfTurnProjector_eq_axisOuter [DecidableEq K]
    (rotation : Rotation K) (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    halfTurnProjector rotation =
      Matrix3.scale
        (1 / (halfTurnAxis rotation halfTurnSpread twoNonzero).quadrance)
        (Matrix3.outer
          (halfTurnAxis rotation halfTurnSpread twoNonzero)
          (halfTurnAxis rotation halfTurnSpread twoNonzero)) :=
  (halfTurnAxisWitness rotation halfTurnSpread twoNonzero).reconstruction

private theorem halfTurnProjector_doubled (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.scale 2 (halfTurnProjector rotation) =
      Matrix3.add Matrix3.identity rotation.matrix := by
  have twoCancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  unfold halfTurnProjector
  rw [Matrix3.scale_scale]
  have coefficient : (2 : K) * (1 / 2) = 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    rw [one_mul, twoCancel]
  rw [coefficient]
  ext <;> unfold Matrix3.scale <;> ring1

/-- Constructive classification of the missing case in the paper: every
rotation with half spread one is the half turn about its selected non-null
axis. -/
theorem rotation_eq_halfTurn_halfTurnAxis [DecidableEq K]
    (rotation : Rotation K) (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    rotation.matrix =
      halfTurn (halfTurnAxis rotation halfTurnSpread twoNonzero)
        (halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero) := by
  let axis := halfTurnAxis rotation halfTurnSpread twoNonzero
  let axisNonNull := halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero
  have projectorForm :
      halfTurnProjector rotation =
        Matrix3.scale (1 / axis.quadrance) (Matrix3.outer axis axis) := by
    unfold axis
    exact halfTurnProjector_eq_axisOuter rotation halfTurnSpread twoNonzero
  calc
    rotation.matrix =
        Matrix3.sub
          (Matrix3.add Matrix3.identity rotation.matrix)
          Matrix3.identity := by
            ext <;> unfold Matrix3.add Matrix3.sub Matrix3.identity <;> ring1
    _ = Matrix3.sub
        (Matrix3.scale 2 (halfTurnProjector rotation))
        Matrix3.identity := by
          rw [halfTurnProjector_doubled rotation twoNonzero]
    _ = Matrix3.sub
        (Matrix3.scale 2
          (Matrix3.scale (1 / axis.quadrance)
            (Matrix3.outer axis axis)))
        Matrix3.identity := by rw [projectorForm]
    _ = halfTurn axis axisNonNull := by
      unfold halfTurn reflection
      ext <;> unfold Matrix3.sub Matrix3.neg Matrix3.scale Matrix3.identity
        Matrix3.outer <;>
        simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1

/-! ### A uniform constructive axis and spread witness -/

/-- The two finite charts used by the canonical axis construction.  Each
branch stores the denominator or non-nullness certificate needed to evaluate
its displayed matrix, together with the equality identifying that matrix with
the supplied rotation. -/
inductive RotationAxisChart (rotation : Rotation K) (axis : Vector K) where
  | affine
      (notHalfTurn : halfSpread rotation ≠ 1)
      (defined : capDenominator axis ≠ 0)
      (matrix_eq : rotation.matrix = cap axis defined)
  | halfTurn
      (halfTurnSpread : halfSpread rotation = 1)
      (axisNonNull : axis.quadrance ≠ 0)
      (matrix_eq : rotation.matrix = halfTurn axis axisNonNull)

/-- Cached canonical axis, chart, and geometric spread data for an arbitrary
rotation.  Downstream constructions can consume the selected axis and
perpendicular direction without repeating the half-spread test, projector
calculation, or perpendicular search. -/
structure RotationAxisSpreadWitness (rotation : Rotation K) where
  axis : Vector K
  direction : Vector K
  directionNonNull : direction.quadrance ≠ 0
  directionPerpendicular : direction.Perpendicular axis
  chart : RotationAxisChart rotation axis
  spread_eq :
    rotationSpreadAt rotation direction directionNonNull =
      rotationSpread rotation

private theorem rotation_eq_of_matrix_eq (left right : Rotation K)
    (matrix_eq : left.matrix = right.matrix) : left = right := by
  cases left with
  | mk leftMatrix leftOrthogonal leftDeterminant =>
      cases right with
      | mk rightMatrix rightOrthogonal rightDeterminant =>
          cases matrix_eq
          rfl

/-- Construct the canonical axis and spread witness for every rotation by one
decidable chart split. -/
def rotationAxisSpreadWitness [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    RotationAxisSpreadWitness rotation := by
  by_cases halfTurnSpread : halfSpread rotation = 1
  · let axis := halfTurnAxis rotation halfTurnSpread twoNonzero
    let axisNonNull := halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero
    let chosen := perpendicularNonNullWitness axis twoNonzero
    have matrixEq : rotation.matrix = halfTurn axis axisNonNull := by
      unfold axis axisNonNull
      exact rotation_eq_halfTurn_halfTurnAxis rotation halfTurnSpread
        twoNonzero
    have rotationEq :
        rotation = halfTurnRotation axis axisNonNull :=
      rotation_eq_of_matrix_eq rotation (halfTurnRotation axis axisNonNull)
        matrixEq
    refine
      { axis := axis
        direction := chosen.value
        directionNonNull := chosen.nonNull
        directionPerpendicular := chosen.perpendicular
        chart := RotationAxisChart.halfTurn halfTurnSpread axisNonNull matrixEq
        spread_eq := ?_ }
    rw [rotationEq]
    exact rotationSpreadAt_halfTurn axis axisNonNull twoNonzero chosen.value
      chosen.nonNull chosen.perpendicular
  · let axis := rotationAnchorVector rotation halfTurnSpread
    let defined := rotationAnchorVector_capDefined rotation halfTurnSpread
      twoNonzero
    let chosen := perpendicularNonNullWitness axis twoNonzero
    have matrixEq : rotation.matrix = cap axis defined := by
      unfold axis defined
      exact (cap_rotationAnchor rotation halfTurnSpread twoNonzero).symm
    have rotationEq : rotation = capRotation axis defined :=
      rotation_eq_of_matrix_eq rotation (capRotation axis defined) matrixEq
    refine
      { axis := axis
        direction := chosen.value
        directionNonNull := chosen.nonNull
        directionPerpendicular := chosen.perpendicular
        chart := RotationAxisChart.affine halfTurnSpread defined matrixEq
        spread_eq := ?_ }
    rw [rotationEq]
    exact rotationSpreadAt_cap axis defined twoNonzero chosen.value
      chosen.nonNull chosen.perpendicular

/-- The canonical axis selected by `rotationAxisSpreadWitness`. -/
def canonicalRotationAxis [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) : Vector K :=
  (rotationAxisSpreadWitness rotation twoNonzero).axis

/-- The canonical non-null perpendicular direction selected for a rotation. -/
def canonicalRotationSpreadDirection [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) : Vector K :=
  (rotationAxisSpreadWitness rotation twoNonzero).direction

theorem canonicalRotationSpreadDirection_nonNull [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    (canonicalRotationSpreadDirection rotation twoNonzero).quadrance ≠ 0 :=
  (rotationAxisSpreadWitness rotation twoNonzero).directionNonNull

theorem canonicalRotationSpreadDirection_perpendicular [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    (canonicalRotationSpreadDirection rotation twoNonzero).Perpendicular
      (canonicalRotationAxis rotation twoNonzero) :=
  (rotationAxisSpreadWitness rotation twoNonzero).directionPerpendicular

/-- Uniform form of Theorem 31: the geometric spread computed from the
canonical perpendicular direction agrees with the trace expression for every
rotation. -/
theorem rotationSpreadAt_canonical [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) :
    rotationSpreadAt rotation
        (canonicalRotationSpreadDirection rotation twoNonzero)
        (canonicalRotationSpreadDirection_nonNull rotation twoNonzero) =
      rotationSpread rotation :=
  (rotationAxisSpreadWitness rotation twoNonzero).spread_eq

/-- The uniform canonical-direction theorem with the second spread polynomial
exposed directly, rather than through the `rotationSpread` abbreviation. -/
theorem rotationSpreadAt_canonical_eq_halfSpreadPolynomial [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    rotationSpreadAt rotation
        (canonicalRotationSpreadDirection rotation twoNonzero)
        (canonicalRotationSpreadDirection_nonNull rotation twoNonzero) =
      4 * halfSpread rotation * (1 - halfSpread rotation) := by
  rw [rotationSpreadAt_canonical rotation twoNonzero]
  rfl

/-- Affine-chart projection of the uniform witness: after exposing its cached
chart certificate, the spread theorem is exactly the existing cap theorem. -/
theorem RotationAxisSpreadWitness.affine_spread_projection
    {rotation : Rotation K} (witness : RotationAxisSpreadWitness rotation)
    (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (defined : capDenominator witness.axis ≠ 0)
    (matrixEq : rotation.matrix = cap witness.axis defined)
    (_chartEq : witness.chart =
      RotationAxisChart.affine notHalfTurn defined matrixEq) :
    rotationSpreadAt rotation witness.direction witness.directionNonNull =
      rotationSpread (capRotation witness.axis defined) := by
  calc
    rotationSpreadAt rotation witness.direction witness.directionNonNull =
        rotationSpreadAt (capRotation witness.axis defined)
          witness.direction witness.directionNonNull := by
      unfold rotationSpreadAt Vector.spread
      rw [matrixEq]
      rfl
    _ = rotationSpread (capRotation witness.axis defined) :=
      rotationSpreadAt_cap witness.axis defined twoNonzero witness.direction
        witness.directionNonNull witness.directionPerpendicular

/-- Half-turn-chart projection of the uniform witness: after exposing its
cached chart certificate, the spread theorem is exactly the existing
half-turn theorem. -/
theorem RotationAxisSpreadWitness.halfTurn_spread_projection
    {rotation : Rotation K} (witness : RotationAxisSpreadWitness rotation)
    (twoNonzero : (2 : K) ≠ 0)
    (halfTurnSpread : halfSpread rotation = 1)
    (axisNonNull : witness.axis.quadrance ≠ 0)
    (matrixEq : rotation.matrix = halfTurn witness.axis axisNonNull)
    (_chartEq : witness.chart =
      RotationAxisChart.halfTurn halfTurnSpread axisNonNull matrixEq) :
    rotationSpreadAt rotation witness.direction witness.directionNonNull =
      rotationSpread (halfTurnRotation witness.axis axisNonNull) := by
  calc
    rotationSpreadAt rotation witness.direction witness.directionNonNull =
        rotationSpreadAt (halfTurnRotation witness.axis axisNonNull)
          witness.direction witness.directionNonNull := by
      unfold rotationSpreadAt Vector.spread
      rw [matrixEq]
      rfl
    _ = rotationSpread (halfTurnRotation witness.axis axisNonNull) :=
      rotationSpreadAt_halfTurn witness.axis axisNonNull twoNonzero
        witness.direction witness.directionNonNull
        witness.directionPerpendicular

/-- Every admissible perpendicular direction to the canonical axis computes
the same rotation spread. -/
theorem rotationSpreadAt_canonicalAxis [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (direction : Vector K) (directionNonNull : direction.quadrance ≠ 0)
    (perpendicular :
      direction.Perpendicular (canonicalRotationAxis rotation twoNonzero)) :
    rotationSpreadAt rotation direction directionNonNull =
      rotationSpread rotation := by
  let witness := rotationAxisSpreadWitness rotation twoNonzero
  change direction.Perpendicular witness.axis at perpendicular
  change rotationSpreadAt rotation direction directionNonNull =
    rotationSpread rotation
  cases witness.chart with
  | affine notHalfTurn defined matrixEq =>
      have rotationEq : rotation = capRotation witness.axis defined :=
        rotation_eq_of_matrix_eq rotation
          (capRotation witness.axis defined) matrixEq
      rw [rotationEq]
      exact rotationSpreadAt_cap witness.axis defined twoNonzero direction
        directionNonNull perpendicular
  | halfTurn halfTurnSpread axisNonNull matrixEq =>
      have rotationEq : rotation = halfTurnRotation witness.axis axisNonNull :=
        rotation_eq_of_matrix_eq rotation
          (halfTurnRotation witness.axis axisNonNull) matrixEq
      rw [rotationEq]
      exact rotationSpreadAt_halfTurn witness.axis axisNonNull twoNonzero
        direction directionNonNull perpendicular

/-- Choice independence for the uniform form of Definition 30. -/
theorem rotationSpreadAt_canonicalAxis_independent [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0)
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (firstPerpendicular :
      first.Perpendicular (canonicalRotationAxis rotation twoNonzero))
    (secondPerpendicular :
      second.Perpendicular (canonicalRotationAxis rotation twoNonzero)) :
    rotationSpreadAt rotation first firstNonNull =
      rotationSpreadAt rotation second secondNonNull := by
  rw [rotationSpreadAt_canonicalAxis rotation twoNonzero first firstNonNull
      firstPerpendicular,
    rotationSpreadAt_canonicalAxis rotation twoNonzero second secondNonNull
      secondPerpendicular]

namespace CanonicalAxisSpreadExamples

abbrev RationalScalar := RFAP.ConstructiveFraction.Rational
abbrev FieldFiveScalar := DivineProportions.FieldFive.Element

theorem rationalTwoNonzero : (2 : RationalScalar) ≠ 0 := by
  intro castZero
  exact (by decide : (2 : Nat) ≠ 0)
    (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

theorem rationalOneNonzero : (1 : RationalScalar) ≠ 0 :=
  one_ne_zero_of_two_ne_zero rationalTwoNonzero

theorem fieldFiveTwoNonzero : (2 : FieldFiveScalar) ≠ 0 := by decide

theorem identityDefined :
    capDenominator (Vector.zero : Vector RationalScalar) ≠ 0 := by
  unfold capDenominator
  rw [Vector.quadrance_zero, add_zero]
  exact rationalOneNonzero

/-- Rational identity example for the affine zero-axis branch. -/
def identity : Rotation RationalScalar :=
  capRotation Vector.zero identityDefined

/-- The null nonidentity cap over `F₅` exercises the affine null-axis branch. -/
def nullCap : Rotation FieldFiveScalar :=
  capRotation ExampleTwentySeven.vector ExampleTwentySeven.defined

def halfTurnAxisExample : Vector RationalScalar := ⟨1, 0, 0⟩

theorem halfTurnAxisExample_nonNull : halfTurnAxisExample.quadrance ≠ 0 := by
  intro quadranceZero
  apply rationalOneNonzero
  calc
    (1 : RationalScalar) = halfTurnAxisExample.quadrance := by
      unfold halfTurnAxisExample Vector.quadrance Vector.dot
      ring1
    _ = 0 := quadranceZero

/-- Rational half turn example for the projector-at-infinity branch. -/
def halfTurnExample : Rotation RationalScalar :=
  halfTurnRotation halfTurnAxisExample halfTurnAxisExample_nonNull

theorem identity_halfSpread : halfSpread identity = 0 := by
  unfold identity
  rw [halfSpread_cap Vector.zero identityDefined rationalTwoNonzero,
    Vector.quadrance_zero]
  unfold capDenominator
  exact RFAP.ExplicitField.zero_div _

theorem nullCap_halfSpread : halfSpread nullCap = 0 := by
  unfold nullCap
  rw [halfSpread_cap ExampleTwentySeven.vector ExampleTwentySeven.defined
      fieldFiveTwoNonzero,
    ExampleTwentySeven.null]
  unfold capDenominator
  exact RFAP.ExplicitField.zero_div _

theorem halfTurnExample_halfSpread : halfSpread halfTurnExample = 1 := by
  unfold halfTurnExample
  exact halfSpread_halfTurn halfTurnAxisExample halfTurnAxisExample_nonNull
    rationalTwoNonzero

theorem identity_canonical_spread :
    rotationSpreadAt identity
        (canonicalRotationSpreadDirection identity rationalTwoNonzero)
        (canonicalRotationSpreadDirection_nonNull identity
          rationalTwoNonzero) = 0 := by
  rw [rotationSpreadAt_canonical identity rationalTwoNonzero]
  unfold rotationSpread
  rw [identity_halfSpread, mul_zero, zero_mul]

theorem nullCap_canonical_spread :
    rotationSpreadAt nullCap
        (canonicalRotationSpreadDirection nullCap fieldFiveTwoNonzero)
        (canonicalRotationSpreadDirection_nonNull nullCap
          fieldFiveTwoNonzero) = 0 := by
  rw [rotationSpreadAt_canonical nullCap fieldFiveTwoNonzero]
  unfold rotationSpread
  rw [nullCap_halfSpread]
  decide

theorem halfTurnExample_canonical_spread :
    rotationSpreadAt halfTurnExample
        (canonicalRotationSpreadDirection halfTurnExample rationalTwoNonzero)
        (canonicalRotationSpreadDirection_nonNull halfTurnExample
          rationalTwoNonzero) = 0 := by
  rw [rotationSpreadAt_canonical halfTurnExample rationalTwoNonzero]
  unfold rotationSpread
  rw [halfTurnExample_halfSpread, sub_self, mul_zero]

end CanonicalAxisSpreadExamples

/-! ### The two constructive factorization branches -/

/-- The second mirror normal for a half turn, determined by the axis and the
freely chosen first mirror normal. -/
def halfTurnSecondMirror (axis first : Vector K) : Vector K :=
  Vector.cross axis first

private theorem quadrance_halfTurnSecondMirror (axis first : Vector K)
    (perpendicular : first.Perpendicular axis) :
    (halfTurnSecondMirror axis first).quadrance =
      axis.quadrance * first.quadrance := by
  have dotZero : Vector.dot axis first = 0 := by
    rw [Vector.dot_comm]
    exact perpendicular
  have lagrange := Vector.lagrange axis first
  rw [dotZero] at lagrange
  unfold halfTurnSecondMirror
  calc
    (Vector.cross axis first).quadrance =
        0 ^ 2 + (Vector.cross axis first).quadrance := by ring1
    _ = axis.quadrance * first.quadrance := lagrange

theorem halfTurnSecondMirror_nonNull (axis first : Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular axis) :
    (halfTurnSecondMirror axis first).quadrance ≠ 0 := by
  rw [quadrance_halfTurnSecondMirror axis first perpendicular]
  exact RFAP.ExplicitField.mul_ne_zero axisNonNull firstNonNull

private theorem orthogonal_outer_decomposition (axis first : Vector K)
    (perpendicular : first.Perpendicular axis) :
    Matrix3.add
        (Matrix3.add
          (Matrix3.scale first.quadrance (Matrix3.outer axis axis))
          (Matrix3.scale axis.quadrance (Matrix3.outer first first)))
        (Matrix3.outer (halfTurnSecondMirror axis first)
          (halfTurnSecondMirror axis first)) =
      Matrix3.scale (axis.quadrance * first.quadrance)
        Matrix3.identity := by
  have dotZero : Vector.dot axis first = 0 := by
    rw [Vector.dot_comm]
    exact perpendicular
  unfold halfTurnSecondMirror
  rw [Matrix3.outer_cross_self, dotZero]
  ext <;> unfold Matrix3.add Matrix3.sub Matrix3.scale Matrix3.identity <;>
    ring1

private theorem normalized_orthogonal_outer_decomposition
    (axis first : Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular axis) :
    Matrix3.add
        (Matrix3.add
          (Matrix3.scale (1 / axis.quadrance) (Matrix3.outer axis axis))
          (Matrix3.scale (1 / first.quadrance)
            (Matrix3.outer first first)))
        (Matrix3.scale
          (1 / (halfTurnSecondMirror axis first).quadrance)
          (Matrix3.outer (halfTurnSecondMirror axis first)
            (halfTurnSecondMirror axis first))) =
      Matrix3.identity := by
  let product := axis.quadrance * first.quadrance
  have productNonzero : product ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero axisNonNull firstNonNull
  have productCancel := RFAP.ExplicitField.mul_inv_cancel product productNonzero
  have productInverseCancel : product⁻¹ * product = 1 := by
    calc
      product⁻¹ * product = product * product⁻¹ := by ring1
      _ = 1 := productCancel
  have axisCancel := RFAP.ExplicitField.mul_inv_cancel
    axis.quadrance axisNonNull
  have firstCancel := RFAP.ExplicitField.mul_inv_cancel
    first.quadrance firstNonNull
  have productInverse := inverse_product axisNonNull firstNonNull
  have secondQuadrance := quadrance_halfTurnSecondMirror axis first perpendicular
  have axisCoefficient : product⁻¹ * first.quadrance = axis.quadrance⁻¹ := by
    unfold product
    rw [productInverse]
    calc
      axis.quadrance⁻¹ * first.quadrance⁻¹ * first.quadrance =
          axis.quadrance⁻¹ *
            (first.quadrance * first.quadrance⁻¹) := by ring1
      _ = axis.quadrance⁻¹ := by rw [firstCancel, mul_one]
  have firstCoefficient : product⁻¹ * axis.quadrance = first.quadrance⁻¹ := by
    unfold product
    rw [productInverse]
    calc
      axis.quadrance⁻¹ * first.quadrance⁻¹ * axis.quadrance =
          first.quadrance⁻¹ *
            (axis.quadrance * axis.quadrance⁻¹) := by ring1
      _ = first.quadrance⁻¹ := by rw [axisCancel, mul_one]
  have secondCoefficient :
      product⁻¹ = (halfTurnSecondMirror axis first).quadrance⁻¹ := by
    rw [secondQuadrance]
  have base := orthogonal_outer_decomposition axis first perpendicular
  have scaled := congrArg (Matrix3.scale product⁻¹) base
  rw [Matrix3.scale_add, Matrix3.scale_add,
    Matrix3.scale_scale, Matrix3.scale_scale, Matrix3.scale_scale,
    axisCoefficient, firstCoefficient, productInverseCancel,
    secondCoefficient, Matrix3.one_scale] at scaled
  simpa only [RFAP.ExplicitField.div_eq_mul_inv, one_mul] using scaled

/-- Perpendicular non-null mirrors compose to the half turn about their
cross-product axis, with the second mirror determined by the selected axis
and first mirror. -/
theorem reflection_mul_halfTurnSecondMirror (axis first : Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular axis) :
    Matrix3.mul (reflection first firstNonNull)
        (reflection (halfTurnSecondMirror axis first)
          (halfTurnSecondMirror_nonNull axis first axisNonNull firstNonNull
            perpendicular)) =
      halfTurn axis axisNonNull := by
  let second := halfTurnSecondMirror axis first
  let secondNonNull := halfTurnSecondMirror_nonNull axis first axisNonNull
    firstNonNull perpendicular
  have firstSecondDot : Vector.dot first second = 0 := by
    unfold second halfTurnSecondMirror
    rw [Vector.dot_comm]
    exact Vector.cross_dot_right axis first
  have outerProductZero :
      Matrix3.mul (Matrix3.outer first first)
          (Matrix3.outer second second) = Matrix3.zero := by
    rw [Matrix3.mul_outer, firstSecondDot]
    ext <;> unfold Matrix3.scale Matrix3.zero <;> ring1
  have expanded :
      Matrix3.mul (reflection first firstNonNull)
          (reflection second secondNonNull) =
        Matrix3.sub
          (Matrix3.sub Matrix3.identity
            (Matrix3.scale (2 / first.quadrance)
              (Matrix3.outer first first)))
          (Matrix3.scale (2 / second.quadrance)
            (Matrix3.outer second second)) := by
    unfold reflection
    rw [Matrix3.mul_sub_right, Matrix3.mul_identity,
      Matrix3.mul_scale_right, Matrix3.mul_sub_left,
      Matrix3.identity_mul, Matrix3.mul_scale_left, outerProductZero]
    ext <;> unfold Matrix3.sub Matrix3.scale Matrix3.zero <;> ring1
  rw [expanded]
  have decomposition := normalized_orthogonal_outer_decomposition axis first
    axisNonNull firstNonNull perpendicular
  unfold second at *
  unfold halfTurn reflection
  rw [← decomposition]
  ext <;> unfold Matrix3.add Matrix3.sub Matrix3.neg Matrix3.scale <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1

/-- Theorem 40's determined second mirror in the affine anchor chart. -/
def capSecondMirror (anchorVector first : Vector K) : Vector K :=
  Vector.add first (Vector.cross anchorVector first)

theorem dot_capSecondMirror (anchorVector first : Vector K) :
    Vector.dot first (capSecondMirror anchorVector first) =
      first.quadrance := by
  unfold capSecondMirror
  rw [Vector.dot_add_right]
  have crossDot : Vector.dot first (Vector.cross anchorVector first) = 0 := by
    rw [Vector.dot_comm]
    exact Vector.cross_dot_right anchorVector first
  rw [crossDot]
  unfold Vector.quadrance
  ring1

theorem cross_capSecondMirror (anchorVector first : Vector K)
    (perpendicular : first.Perpendicular anchorVector) :
    Vector.cross first (capSecondMirror anchorVector first) =
      Vector.scale first.quadrance anchorVector := by
  have selfCross : Vector.cross first first = Vector.zero := by
    ext <;> unfold Vector.cross Vector.zero <;> ring1
  unfold capSecondMirror
  rw [Vector.cross_add_right, selfCross, Vector.zero_add,
    Vector.vector_triple_product]
  unfold Vector.Perpendicular at perpendicular
  rw [perpendicular]
  ext <;> unfold Vector.sub Vector.scale Vector.quadrance <;>
    ring1

theorem quadrance_capSecondMirror (anchorVector first : Vector K)
    (perpendicular : first.Perpendicular anchorVector) :
    (capSecondMirror anchorVector first).quadrance =
      first.quadrance * (1 + anchorVector.quadrance) := by
  have firstCrossDot :
      Vector.dot first (Vector.cross anchorVector first) = 0 := by
    rw [Vector.dot_comm]
    exact Vector.cross_dot_right anchorVector first
  have anchorFirstDot : Vector.dot anchorVector first = 0 := by
    rw [Vector.dot_comm]
    exact perpendicular
  have lagrange := Vector.lagrange anchorVector first
  rw [anchorFirstDot] at lagrange
  have crossQuadrance :
      (Vector.cross anchorVector first).quadrance =
        anchorVector.quadrance * first.quadrance := by
    calc
      (Vector.cross anchorVector first).quadrance =
          0 ^ 2 + (Vector.cross anchorVector first).quadrance := by ring1
      _ = anchorVector.quadrance * first.quadrance := lagrange
  unfold capSecondMirror
  rw [Vector.quadrance_add, firstCrossDot, crossQuadrance]
  ring1

theorem capSecondMirror_nonNull (anchorVector first : Vector K)
    (anchorDefined : capDenominator anchorVector ≠ 0)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular anchorVector) :
    (capSecondMirror anchorVector first).quadrance ≠ 0 := by
  rw [quadrance_capSecondMirror anchorVector first perpendicular]
  apply RFAP.ExplicitField.mul_ne_zero firstNonNull
  unfold capDenominator at anchorDefined
  exact anchorDefined

private theorem reflectionProductAnchorVector_capSecondMirror
    (anchorVector first : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular anchorVector) :
    reflectionProductAnchorVector first (capSecondMirror anchorVector first)
        (by rw [dot_capSecondMirror]; exact firstNonNull) =
      anchorVector := by
  have cancel : (1 / first.quadrance) * first.quadrance = (1 : K) :=
    RFAP.ExplicitField.div_mul_cancel 1 firstNonNull
  unfold reflectionProductAnchorVector
  rw [dot_capSecondMirror,
    cross_capSecondMirror anchorVector first perpendicular,
    Vector.scale_scale, cancel, Vector.one_scale]

/-- The non-half-turn branch of Theorem 40, with an arbitrary certified first
mirror normal perpendicular to the anchor vector. -/
theorem reflection_mul_capSecondMirror (anchorVector first : Vector K)
    (anchorDefined : capDenominator anchorVector ≠ 0)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular : first.Perpendicular anchorVector)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.mul (reflection first firstNonNull)
        (reflection (capSecondMirror anchorVector first)
          (capSecondMirror_nonNull anchorVector first anchorDefined
            firstNonNull perpendicular)) =
      cap anchorVector anchorDefined := by
  let second := capSecondMirror anchorVector first
  let secondNonNull := capSecondMirror_nonNull anchorVector first
    anchorDefined firstNonNull perpendicular
  let dotNonzero : Vector.dot first second ≠ 0 := by
    unfold second
    rw [dot_capSecondMirror]
    exact firstNonNull
  let product := reflectionProductRotation first second firstNonNull
    secondNonNull
  let productNotHalfTurn := reflectionProduct_notHalfTurn first second
    firstNonNull secondNonNull dotNonzero twoNonzero
  let productAnchorDefined := rotationAnchorVector_capDefined product
    productNotHalfTurn twoNonzero
  have recoveredVector :
      rotationAnchorVector product productNotHalfTurn = anchorVector := by
    calc
      rotationAnchorVector product productNotHalfTurn =
          reflectionProductAnchorVector first second dotNonzero := by
            unfold product productNotHalfTurn
            exact rotationAnchorVector_reflectionProduct first second
              firstNonNull secondNonNull dotNonzero twoNonzero
      _ = anchorVector := by
        unfold second dotNonzero
        exact reflectionProductAnchorVector_capSecondMirror anchorVector first
          firstNonNull perpendicular
  change product.matrix = cap anchorVector anchorDefined
  calc
    product.matrix =
        cap (rotationAnchorVector product productNotHalfTurn)
          productAnchorDefined :=
      (cap_rotationAnchor product productNotHalfTurn twoNonzero).symm
    _ = cap anchorVector anchorDefined := by
      unfold cap
      rw [recoveredVector]

/-- The free-first-mirror form of Theorem 40 for a rotation in the affine
anchor chart. -/
theorem reflectionProduct_eq_rotation_of_notHalfTurn
    (rotation : Rotation K) (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) (first : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular :
      first.Perpendicular (rotationAnchorVector rotation notHalfTurn)) :
    Matrix3.mul (reflection first firstNonNull)
        (reflection
          (capSecondMirror (rotationAnchorVector rotation notHalfTurn) first)
          (capSecondMirror_nonNull
            (rotationAnchorVector rotation notHalfTurn) first
            (rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero)
            firstNonNull perpendicular)) =
      rotation.matrix := by
  calc
    Matrix3.mul (reflection first firstNonNull)
        (reflection
          (capSecondMirror (rotationAnchorVector rotation notHalfTurn) first)
          (capSecondMirror_nonNull
            (rotationAnchorVector rotation notHalfTurn) first
            (rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero)
            firstNonNull perpendicular)) =
      cap (rotationAnchorVector rotation notHalfTurn)
        (rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero) :=
          reflection_mul_capSecondMirror
            (rotationAnchorVector rotation notHalfTurn) first
            (rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero)
            firstNonNull perpendicular twoNonzero
    _ = rotation.matrix :=
      cap_rotationAnchor rotation notHalfTurn twoNonzero

/-- The free-first-mirror form of Theorem 40 for the half-turn chart. -/
theorem reflectionProduct_eq_rotation_of_halfSpread_eq_one [DecidableEq K]
    (rotation : Rotation K) (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) (first : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (perpendicular :
      first.Perpendicular
        (halfTurnAxis rotation halfTurnSpread twoNonzero)) :
    Matrix3.mul (reflection first firstNonNull)
        (reflection
          (halfTurnSecondMirror
            (halfTurnAxis rotation halfTurnSpread twoNonzero) first)
          (halfTurnSecondMirror_nonNull
            (halfTurnAxis rotation halfTurnSpread twoNonzero) first
            (halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero)
            firstNonNull perpendicular)) =
      rotation.matrix := by
  calc
    Matrix3.mul (reflection first firstNonNull)
        (reflection
          (halfTurnSecondMirror
            (halfTurnAxis rotation halfTurnSpread twoNonzero) first)
          (halfTurnSecondMirror_nonNull
            (halfTurnAxis rotation halfTurnSpread twoNonzero) first
            (halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero)
            firstNonNull perpendicular)) =
      halfTurn (halfTurnAxis rotation halfTurnSpread twoNonzero)
        (halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero) :=
          reflection_mul_halfTurnSecondMirror
            (halfTurnAxis rotation halfTurnSpread twoNonzero) first
            (halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero)
            firstNonNull perpendicular
    _ = rotation.matrix :=
      (rotation_eq_halfTurn_halfTurnAxis rotation halfTurnSpread
        twoNonzero).symm

/-- Cached executable witnesses and certificates for a two-reflection
factorization of a rotation. -/
structure ReflectionFactorization (rotation : Rotation K) where
  first : Vector K
  second : Vector K
  firstNonNull : first.quadrance ≠ 0
  secondNonNull : second.quadrance ≠ 0
  product_eq :
    Matrix3.mul (reflection first firstNonNull)
      (reflection second secondNonNull) = rotation.matrix

/-- Theorem 40: every rotation is constructively factored into two
reflections.  The canonical axis/spread witness performs the sole chart test
and perpendicular search; this construction consumes that cached data and
stores both mirror normals and their non-nullness certificates. -/
def twoReflectionsTheorem [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) : ReflectionFactorization rotation := by
  let witness := rotationAxisSpreadWitness rotation twoNonzero
  cases witness.chart with
  | halfTurn halfTurnSpread axisNonNull matrixEq =>
    let second := halfTurnSecondMirror witness.axis witness.direction
    let secondNonNull := halfTurnSecondMirror_nonNull witness.axis
      witness.direction axisNonNull witness.directionNonNull
      witness.directionPerpendicular
    refine
      { first := witness.direction
        second := second
        firstNonNull := witness.directionNonNull
        secondNonNull := secondNonNull
        product_eq := ?_ }
    calc
      Matrix3.mul
          (reflection witness.direction witness.directionNonNull)
          (reflection second secondNonNull) =
        halfTurn witness.axis axisNonNull := by
          unfold secondNonNull second
          exact reflection_mul_halfTurnSecondMirror witness.axis
            witness.direction axisNonNull witness.directionNonNull
            witness.directionPerpendicular
      _ = rotation.matrix := matrixEq.symm
  | affine notHalfTurn defined matrixEq =>
    let second := capSecondMirror witness.axis witness.direction
    let secondNonNull := capSecondMirror_nonNull witness.axis witness.direction
      defined witness.directionNonNull witness.directionPerpendicular
    refine
      { first := witness.direction
        second := second
        firstNonNull := witness.directionNonNull
        secondNonNull := secondNonNull
        product_eq := ?_ }
    calc
      Matrix3.mul
          (reflection witness.direction witness.directionNonNull)
          (reflection second secondNonNull) =
        cap witness.axis defined := by
          unfold secondNonNull second
          exact reflection_mul_capSecondMirror witness.axis witness.direction
            defined witness.directionNonNull witness.directionPerpendicular
            twoNonzero
      _ = rotation.matrix := matrixEq.symm

end RationalRotations
