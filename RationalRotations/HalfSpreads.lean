import RationalRotations.Caps

/-!
# Rational rotations, section 6: half spreads

Half spread and spread are stored as executable field expressions.  For the
paper's auxiliary perpendicular direction, this module computes one of three
fixed coordinate candidates and caches both its perpendicularity and
non-nullness certificates.  No basis choice or representation theorem is
used.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- Definition 28: the half spread of a rotation. -/
def halfSpread (rotation : Rotation K) : K :=
  (3 - Matrix3.trace rotation.matrix) / 4

/-- The canonical executable spread of a rotation, as identified by
Theorem 31. -/
def rotationSpread (rotation : Rotation K) : K :=
  4 * halfSpread rotation * (1 - halfSpread rotation)

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

private theorem inverse_square {value : K} (valueNonzero : value ≠ 0) :
    (value ^ 2)⁻¹ = value⁻¹ ^ 2 := by
  simpa only [pow_two] using inverse_product valueNonzero valueNonzero

private theorem eq_zero_of_nonzero_mul_eq_zero {factor value : K}
    (factorNonzero : factor ≠ 0) (productZero : factor * value = 0) :
    value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

private theorem eq_zero_of_square_eq_zero [DecidableEq K] (value : K)
    (squareZero : value ^ 2 = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        RFAP.ExplicitField.mul_ne_zero valueZero valueZero
    exact (squareNonzero squareZero).elim

/-- Theorem 29: the half spread of a cap is `Q/(1+Q)`. -/
theorem halfSpread_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (capRotation vector defined) =
      vector.quadrance / capDenominator vector := by
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (capDenominator vector) defined
  have fourCancel := RFAP.ExplicitField.mul_inv_cancel 4
    (four_ne_zero twoNonzero)
  unfold halfSpread capRotation
  rw [trace_cap]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (3 - (3 - vector.quadrance) * (capDenominator vector)⁻¹) *
        (4 : K)⁻¹ =
      (4 * vector.quadrance * (capDenominator vector)⁻¹) *
        (4 : K)⁻¹ := by
          calc
            (3 - (3 - vector.quadrance) *
                (capDenominator vector)⁻¹) * (4 : K)⁻¹ =
              (3 * (capDenominator vector *
                    (capDenominator vector)⁻¹) -
                (3 - vector.quadrance) *
                  (capDenominator vector)⁻¹) * (4 : K)⁻¹ := by
                    rw [denominatorCancel]
                    ring1
            _ = (4 * vector.quadrance *
                (capDenominator vector)⁻¹) * (4 : K)⁻¹ := by
                  unfold capDenominator
                  ring1
    _ = vector.quadrance * (capDenominator vector)⁻¹ *
        (4 * (4 : K)⁻¹) := by ring1
    _ = vector.quadrance * (capDenominator vector)⁻¹ := by
      rw [fourCancel, mul_one]

/-- Theorem 29: complementary half spread of a cap. -/
theorem one_sub_halfSpread_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    1 - halfSpread (capRotation vector defined) =
      1 / capDenominator vector := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (capDenominator vector) defined
  rw [halfSpread_cap vector defined twoNonzero]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 - vector.quadrance * (capDenominator vector)⁻¹ =
        capDenominator vector * (capDenominator vector)⁻¹ -
          vector.quadrance * (capDenominator vector)⁻¹ := by rw [cancel]
    _ = 1 * (capDenominator vector)⁻¹ := by
      unfold capDenominator
      ring1

/-- Theorem 29: the doubled complementary half-spread identity. -/
theorem one_sub_two_mul_halfSpread_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    1 - 2 * halfSpread (capRotation vector defined) =
      (1 - vector.quadrance) / capDenominator vector := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (capDenominator vector) defined
  rw [halfSpread_cap vector defined twoNonzero]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 - 2 * (vector.quadrance * (capDenominator vector)⁻¹) =
        capDenominator vector * (capDenominator vector)⁻¹ -
          2 * vector.quadrance * (capDenominator vector)⁻¹ := by
            rw [cancel]
            ring1
    _ = (1 - vector.quadrance) *
        (capDenominator vector)⁻¹ := by
      unfold capDenominator
      ring1

/-- Theorem 29: product of the two complementary half-spread factors. -/
theorem halfSpread_mul_one_sub_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (capRotation vector defined) *
        (1 - halfSpread (capRotation vector defined)) =
      vector.quadrance / capDenominator vector ^ 2 := by
  rw [one_sub_halfSpread_cap vector defined twoNonzero,
    halfSpread_cap vector defined twoNonzero]
  simp only [RFAP.ExplicitField.div_eq_mul_inv,
    inverse_square defined]
  ring1

/-- Theorem 29: a cap never has half spread one. -/
theorem halfSpread_cap_ne_one (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (capRotation vector defined) ≠ 1 := by
  intro spreadOne
  have complementZero :
      1 - halfSpread (capRotation vector defined) = 0 := by
    rw [spreadOne]
    ring1
  rw [one_sub_halfSpread_cap vector defined twoNonzero] at complementZero
  exact (RFAP.ExplicitField.div_ne_zero
    (one_ne_zero_of_two_ne_zero twoNonzero) defined) complementZero

/-- Theorem 29: recover the anchor quadrance from the half spread. -/
theorem quadrance_eq_halfSpread_div_one_sub (vector : Vector K)
    (defined : capDenominator vector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    vector.quadrance =
      halfSpread (capRotation vector defined) /
        (1 - halfSpread (capRotation vector defined)) := by
  rw [one_sub_halfSpread_cap vector defined twoNonzero,
    halfSpread_cap vector defined twoNonzero]
  have denominatorInverseNonzero :=
    RFAP.ExplicitField.inv_ne_zero defined
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (capDenominator vector)⁻¹ denominatorInverseNonzero
  have oneDiv :
      (1 : K) / capDenominator vector =
        (capDenominator vector)⁻¹ := by
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  rw [oneDiv]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    vector.quadrance = vector.quadrance * 1 := by rw [mul_one]
    _ = vector.quadrance *
        ((capDenominator vector)⁻¹ *
          ((capDenominator vector)⁻¹)⁻¹) := by rw [cancel]
    _ = vector.quadrance * (capDenominator vector)⁻¹ *
        ((capDenominator vector)⁻¹)⁻¹ := by ring1

/-- The adjugate of a rotation is its transpose, proved from explicit
two-sided finite inverse certificates. -/
theorem adjugate_rotation (rotation : Rotation K) :
    Matrix3.adjugate rotation.matrix =
      Matrix3.transpose rotation.matrix := by
  have adjugateProduct :
      Matrix3.mul (Matrix3.adjugate rotation.matrix) rotation.matrix =
        Matrix3.identity := by
    calc
      Matrix3.mul (Matrix3.adjugate rotation.matrix) rotation.matrix =
          Matrix3.scale (Matrix3.determinant rotation.matrix)
            Matrix3.identity := Matrix3.adjugate_mul _
      _ = Matrix3.identity := by
        rw [rotation.determinantOne]
        ext <;> unfold Matrix3.scale Matrix3.identity <;> ring1
  calc
    Matrix3.adjugate rotation.matrix =
        Matrix3.mul (Matrix3.adjugate rotation.matrix) Matrix3.identity := by
          rw [Matrix3.mul_identity]
    _ = Matrix3.mul (Matrix3.adjugate rotation.matrix)
        (Matrix3.mul rotation.matrix
          (Matrix3.transpose rotation.matrix)) := by
            rw [rotation.orthogonal]
    _ = Matrix3.mul
        (Matrix3.mul (Matrix3.adjugate rotation.matrix) rotation.matrix)
        (Matrix3.transpose rotation.matrix) := by
          rw [Matrix3.mul_assoc]
    _ = Matrix3.transpose rotation.matrix := by
      rw [adjugateProduct, Matrix3.identity_mul]

theorem principalTrace_rotation (rotation : Rotation K) :
    Matrix3.principalTrace rotation.matrix =
      Matrix3.trace rotation.matrix := by
  unfold Matrix3.principalTrace
  rw [adjugate_rotation, Matrix3.trace_transpose]

private theorem trace_sub_one_eq_halfSpread_coefficient
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.trace rotation.matrix - 1 =
      2 * (1 - 2 * halfSpread rotation) := by
  have fourNonzero := four_ne_zero twoNonzero
  have fourCancellation :
      4 * halfSpread rotation = 3 - Matrix3.trace rotation.matrix := by
    unfold halfSpread
    calc
      4 * ((3 - Matrix3.trace rotation.matrix) / 4) =
          ((3 - Matrix3.trace rotation.matrix) / 4) * 4 := by ring1
      _ = 3 - Matrix3.trace rotation.matrix :=
        RFAP.ExplicitField.div_mul_cancel _ fourNonzero
  calc
    Matrix3.trace rotation.matrix - 1 =
        2 * (1 - 2 * halfSpread rotation) +
          (4 * halfSpread rotation -
            (3 - Matrix3.trace rotation.matrix)) := by ring1
    _ = 2 * (1 - 2 * halfSpread rotation) := by
      rw [fourCancellation]
      ring1

/-- Theorem 29: characteristic polynomial of an arbitrary rotation in terms
of its half spread. -/
theorem characteristicValue_rotation (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) (X : K) :
    Matrix3.characteristicValue rotation.matrix X =
      (X - 1) *
        (X ^ 2 - 2 * (1 - 2 * halfSpread rotation) * X + 1) := by
  calc
    Matrix3.characteristicValue rotation.matrix X =
        X ^ 3 - Matrix3.trace rotation.matrix * X ^ 2 +
          Matrix3.principalTrace rotation.matrix * X -
            Matrix3.determinant rotation.matrix :=
      Matrix3.characteristicValue_expansion _ _
    _ = X ^ 3 - Matrix3.trace rotation.matrix * X ^ 2 +
          Matrix3.trace rotation.matrix * X - 1 := by
      rw [principalTrace_rotation, rotation.determinantOne]
    _ = (X - 1) *
        (X ^ 2 - (Matrix3.trace rotation.matrix - 1) * X + 1) := by
      ring1
    _ = (X - 1) *
        (X ^ 2 - 2 * (1 - 2 * halfSpread rotation) * X + 1) := by
      rw [trace_sub_one_eq_halfSpread_coefficient rotation twoNonzero]

/-- A rotation has the unipotent characteristic polynomial `(X - 1)^3`
exactly when its half spread is zero.  The converse uses only the two
displayed evaluations at `1` and `-1`, so it neither compares polynomial
coefficients nor appeals to an infinite-root argument. -/
theorem characteristicUnipotent_iff_halfSpread_eq_zero
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    (∀ X : K,
      Matrix3.characteristicValue rotation.matrix X = (X - 1) ^ 3) ↔
      halfSpread rotation = 0 := by
  constructor
  · intro characteristic
    have atOne := characteristic 1
    rw [Matrix3.characteristicValue_expansion,
      rotation.determinantOne] at atOne
    have principalEqTrace :
        Matrix3.principalTrace rotation.matrix =
          Matrix3.trace rotation.matrix := by
      calc
        Matrix3.principalTrace rotation.matrix =
            (1 ^ 3 - Matrix3.trace rotation.matrix * 1 ^ 2 +
                Matrix3.principalTrace rotation.matrix * 1 - 1) +
              Matrix3.trace rotation.matrix := by ring1
        _ = (1 - 1) ^ 3 + Matrix3.trace rotation.matrix := by
          rw [atOne]
        _ = Matrix3.trace rotation.matrix := by ring1
    have atNegativeOne := characteristic (-1)
    rw [Matrix3.characteristicValue_expansion,
      rotation.determinantOne] at atNegativeOne
    have tracePlusPrincipal :
        Matrix3.trace rotation.matrix +
            Matrix3.principalTrace rotation.matrix = 6 := by
      calc
        Matrix3.trace rotation.matrix +
            Matrix3.principalTrace rotation.matrix =
          -((-1) ^ 3 - Matrix3.trace rotation.matrix * (-1) ^ 2 +
              Matrix3.principalTrace rotation.matrix * (-1) - 1) - 2 := by
            ring1
        _ = -((-1 - 1) ^ 3) - 2 := by rw [atNegativeOne]
        _ = 6 := by ring1
    have twiceTrace : 2 * Matrix3.trace rotation.matrix = 6 := by
      calc
        2 * Matrix3.trace rotation.matrix =
            Matrix3.trace rotation.matrix +
              Matrix3.principalTrace rotation.matrix := by
          rw [principalEqTrace]
          ring1
        _ = 6 := tracePlusPrincipal
    have traceDifferenceZero :
        Matrix3.trace rotation.matrix - 3 = 0 := by
      apply eq_zero_of_nonzero_mul_eq_zero twoNonzero
      calc
        2 * (Matrix3.trace rotation.matrix - 3) =
            2 * Matrix3.trace rotation.matrix - 6 := by ring1
        _ = 0 := by rw [twiceTrace]; ring1
    have traceEqThree : Matrix3.trace rotation.matrix = 3 := by
      calc
        Matrix3.trace rotation.matrix =
            (Matrix3.trace rotation.matrix - 3) + 3 := by ring1
        _ = 0 + 3 := by rw [traceDifferenceZero]
        _ = 3 := by ring1
    unfold halfSpread
    rw [traceEqThree]
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    ring1
  · intro spreadZero X
    rw [characteristicValue_rotation rotation twoNonzero X, spreadZero]
    ring1

/-- A reflection has trace one. -/
theorem trace_reflection (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.trace (reflection vector nonNull) = 1 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    vector.quadrance nonNull
  unfold Matrix3.trace reflection Matrix3.sub Matrix3.identity Matrix3.scale
    Matrix3.outer Vector.quadrance Vector.dot
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    _ = 3 - 2 * (vector.quadrance * vector.quadrance⁻¹) := by
      unfold Vector.quadrance Vector.dot
      ring1
    _ = 1 := by rw [cancel]; ring1

/-- A half turn has trace minus one. -/
theorem trace_halfTurn (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) :
    Matrix3.trace (halfTurn vector nonNull) = -1 := by
  unfold halfTurn
  rw [show Matrix3.trace (Matrix3.neg (reflection vector nonNull)) =
      -Matrix3.trace (reflection vector nonNull) by
        unfold Matrix3.trace Matrix3.neg
        ring1,
    trace_reflection]

/-- Theorem 29: every half turn has half spread one. -/
theorem halfSpread_halfTurn (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread (halfTurnRotation vector nonNull) = 1 := by
  have fourNonzero := four_ne_zero twoNonzero
  have fourCancel := RFAP.ExplicitField.mul_inv_cancel (4 : K) fourNonzero
  have numerator : (3 - (-1 : K)) = 4 := by ring1
  unfold halfSpread halfTurnRotation
  rw [trace_halfTurn]
  rw [numerator, RFAP.ExplicitField.div_eq_mul_inv]
  exact fourCancel

/-- Orthogonal action by a bundled rotation preserves quadrance. -/
theorem quadrance_rowMul_rotation (rotation : Rotation K)
    (vector : Vector K) :
    Vector.quadrance (Matrix3.rowMul vector rotation.matrix) =
      Vector.quadrance vector :=
  Matrix3.quadrance_rowMul_of_isOrthogonal rotation.orthogonal vector

/-- A non-null vector remains non-null after rotation. -/
theorem rowMul_rotation_nonNull (rotation : Rotation K)
    (vector : Vector K) (nonNull : vector.quadrance ≠ 0) :
    (Matrix3.rowMul vector rotation.matrix).quadrance ≠ 0 := by
  rw [quadrance_rowMul_rotation]
  exact nonNull

/-- Definition 30 evaluated at one supplied non-null direction. -/
def rotationSpreadAt (rotation : Rotation K) (vector : Vector K)
    (nonNull : vector.quadrance ≠ 0) : K :=
  Vector.spread vector (Matrix3.rowMul vector rotation.matrix)
    nonNull (rowMul_rotation_nonNull rotation vector nonNull)

/-- First coordinate candidate perpendicular to an axis. -/
def perpendicularCandidateTR (axis : Vector K) : Vector K :=
  ⟨-axis.r, axis.t, 0⟩

/-- Second coordinate candidate perpendicular to an axis. -/
def perpendicularCandidateTS (axis : Vector K) : Vector K :=
  ⟨-axis.s, 0, axis.t⟩

/-- Third coordinate candidate perpendicular to an axis. -/
def perpendicularCandidateRS (axis : Vector K) : Vector K :=
  ⟨0, -axis.s, axis.r⟩

@[simp] theorem perpendicularCandidateTR_perpendicular (axis : Vector K) :
    (perpendicularCandidateTR axis).Perpendicular axis := by
  unfold Vector.Perpendicular perpendicularCandidateTR Vector.dot
  ring1

@[simp] theorem perpendicularCandidateTS_perpendicular (axis : Vector K) :
    (perpendicularCandidateTS axis).Perpendicular axis := by
  unfold Vector.Perpendicular perpendicularCandidateTS Vector.dot
  ring1

@[simp] theorem perpendicularCandidateRS_perpendicular (axis : Vector K) :
    (perpendicularCandidateRS axis).Perpendicular axis := by
  unfold Vector.Perpendicular perpendicularCandidateRS Vector.dot
  ring1

/-- The three fixed candidate quadrances add to twice the axis quadrance. -/
theorem perpendicularCandidates_quadrance_sum (axis : Vector K) :
    (perpendicularCandidateTR axis).quadrance +
        (perpendicularCandidateTS axis).quadrance +
        (perpendicularCandidateRS axis).quadrance =
      2 * axis.quadrance := by
  unfold perpendicularCandidateTR perpendicularCandidateTS
    perpendicularCandidateRS Vector.quadrance Vector.dot
  ring1

/-- Cached executable data for the non-null perpendicular direction used in
Definition 30. -/
structure PerpendicularNonNullWitness (axis : Vector K) where
  value : Vector K
  nonNull : value.quadrance ≠ 0
  perpendicular : value.Perpendicular axis

/-- Constructively choose a non-null perpendicular direction for every axis.
The three cross-coordinate candidates suffice unless all are null; in that
case characteristic different from two forces the first axis coordinate to
vanish, so the first coordinate vector is a certified fallback. -/
def perpendicularNonNullWitness [DecidableEq K]
    (axis : Vector K) (twoNonzero : (2 : K) ≠ 0) :
    PerpendicularNonNullWitness axis :=
  if firstNull : (perpendicularCandidateTR axis).quadrance = 0 then
    if secondNull : (perpendicularCandidateTS axis).quadrance = 0 then
      if thirdNull : (perpendicularCandidateRS axis).quadrance = 0 then
        { value := ⟨1, 0, 0⟩
          nonNull := by
            have oneNonzero := one_ne_zero_of_two_ne_zero twoNonzero
            unfold Vector.quadrance Vector.dot
            intro quadranceZero
            apply oneNonzero
            calc
              (1 : K) = 1 * 1 + 0 * 0 + 0 * 0 := by ring1
              _ = 0 := quadranceZero
          perpendicular := by
            have twiceFirstSquare : 2 * axis.t ^ 2 = 0 := by
              calc
                2 * axis.t ^ 2 =
                    (perpendicularCandidateTR axis).quadrance +
                      (perpendicularCandidateTS axis).quadrance -
                      (perpendicularCandidateRS axis).quadrance := by
                        unfold perpendicularCandidateTR
                          perpendicularCandidateTS perpendicularCandidateRS
                          Vector.quadrance Vector.dot
                        ring1
                _ = 0 := by rw [firstNull, secondNull, thirdNull]; ring1
            have firstSquareZero := eq_zero_of_nonzero_mul_eq_zero
              twoNonzero twiceFirstSquare
            have firstZero := eq_zero_of_square_eq_zero axis.t firstSquareZero
            unfold Vector.Perpendicular Vector.dot
            rw [firstZero]
            ring1 }
      else
        { value := perpendicularCandidateRS axis
          nonNull := thirdNull
          perpendicular := perpendicularCandidateRS_perpendicular axis }
    else
      { value := perpendicularCandidateTS axis
        nonNull := secondNull
        perpendicular := perpendicularCandidateTS_perpendicular axis }
  else
    { value := perpendicularCandidateTR axis
      nonNull := firstNull
      perpendicular := perpendicularCandidateTR_perpendicular axis }

/-- Quadratic reduction of a cap on a direction perpendicular to its anchor
axis. -/
theorem rowMul_cap_of_perpendicular (axis : Vector K)
    (defined : capDenominator axis ≠ 0) (vector : Vector K)
    (perpendicular : vector.Perpendicular axis) :
    Matrix3.rowMul vector (cap axis defined) =
      Vector.add
        (Vector.scale
          ((1 - axis.quadrance) / capDenominator axis) vector)
        (Vector.scale (2 / capDenominator axis)
          (Vector.cross axis vector)) := by
  have reversePerpendicular : Vector.dot axis vector = 0 := by
    unfold Vector.Perpendicular at perpendicular
    rw [Vector.dot_comm]
    exact perpendicular
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (capDenominator axis) defined
  have coefficient :
      1 - (2 / capDenominator axis) * axis.quadrance =
        (1 - axis.quadrance) / capDenominator axis := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      1 - 2 * (capDenominator axis)⁻¹ * axis.quadrance =
          capDenominator axis * (capDenominator axis)⁻¹ -
            2 * axis.quadrance * (capDenominator axis)⁻¹ := by
              rw [denominatorCancel]
              ring1
      _ = (1 - axis.quadrance) * (capDenominator axis)⁻¹ := by
        unfold capDenominator
        ring1
  calc
    Matrix3.rowMul vector (cap axis defined) =
        Vector.add vector
          (Vector.scale (2 / capDenominator axis)
            (Vector.add (Vector.cross axis vector)
              (Vector.sub
                (Vector.scale (Vector.dot axis vector) axis)
                (Vector.scale axis.quadrance vector)))) := by
      unfold cap
      rw [Matrix3.rowMul_add, Matrix3.rowMul_identity,
        Matrix3.rowMul_scale, Matrix3.rowMul_add, rowMul_anchor,
        ← Matrix3.rowMul_mul, rowMul_anchor, rowMul_anchor,
        Vector.vector_triple_product]
      rfl
    _ = Vector.add
        (Vector.scale
          (1 - (2 / capDenominator axis) * axis.quadrance) vector)
        (Vector.scale (2 / capDenominator axis)
          (Vector.cross axis vector)) := by
      rw [reversePerpendicular]
      ext <;> unfold Vector.add Vector.sub Vector.scale <;> ring1
    _ = Vector.add
        (Vector.scale
          ((1 - axis.quadrance) / capDenominator axis) vector)
        (Vector.scale (2 / capDenominator axis)
          (Vector.cross axis vector)) := by rw [coefficient]

/-- Dot-product component of the perpendicular cap action. -/
theorem dot_self_rowMul_cap_of_perpendicular (axis : Vector K)
    (defined : capDenominator axis ≠ 0) (vector : Vector K)
    (perpendicular : vector.Perpendicular axis) :
    Vector.dot vector (Matrix3.rowMul vector (cap axis defined)) =
      ((1 - axis.quadrance) / capDenominator axis) *
        vector.quadrance := by
  have crossPerpendicular :
      Vector.dot vector (Vector.cross axis vector) = 0 := by
    rw [Vector.dot_comm]
    exact Vector.cross_dot_right axis vector
  rw [rowMul_cap_of_perpendicular axis defined vector perpendicular,
    Vector.dot_add_right, Vector.dot_scale_right,
    Vector.dot_scale_right, crossPerpendicular]
  unfold Vector.quadrance
  ring1

/-- Theorem 31 for a cap: every admissible perpendicular direction computes
the same canonical rotation spread. -/
theorem rotationSpreadAt_cap (axis : Vector K)
    (defined : capDenominator axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (vector : Vector K) (nonNull : vector.quadrance ≠ 0)
    (perpendicular : vector.Perpendicular axis) :
    rotationSpreadAt (capRotation axis defined) vector nonNull =
      rotationSpread (capRotation axis defined) := by
  have vectorSquareNonzero : vector.quadrance * vector.quadrance ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero nonNull nonNull
  have vectorSquareCancel := RFAP.ExplicitField.mul_inv_cancel
    (vector.quadrance * vector.quadrance) vectorSquareNonzero
  have denominatorCancel := RFAP.ExplicitField.mul_inv_cancel
    (capDenominator axis) defined
  have capQuadrance :
      (Matrix3.rowMul vector (cap axis defined)).quadrance =
        vector.quadrance :=
    Matrix3.quadrance_rowMul_of_isOrthogonal
      (cap_isOrthogonal axis defined) vector
  unfold rotationSpreadAt Vector.spread rotationSpread
  change
    1 - Vector.dot vector (Matrix3.rowMul vector (cap axis defined)) ^ 2 /
        (vector.quadrance *
          (Matrix3.rowMul vector (cap axis defined)).quadrance) =
      4 * halfSpread (capRotation axis defined) *
        (1 - halfSpread (capRotation axis defined))
  rw [dot_self_rowMul_cap_of_perpendicular axis defined vector perpendicular,
    capQuadrance,
    one_sub_halfSpread_cap axis defined twoNonzero,
    halfSpread_cap axis defined twoNonzero]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 -
        (((1 - axis.quadrance) * (capDenominator axis)⁻¹) *
          vector.quadrance) ^ 2 *
          (vector.quadrance * vector.quadrance)⁻¹ =
      1 - ((1 - axis.quadrance) *
        (capDenominator axis)⁻¹) ^ 2 := by
          calc
            1 -
                (((1 - axis.quadrance) *
                    (capDenominator axis)⁻¹) *
                  vector.quadrance) ^ 2 *
                  (vector.quadrance * vector.quadrance)⁻¹ =
              1 - ((1 - axis.quadrance) *
                  (capDenominator axis)⁻¹) ^ 2 *
                ((vector.quadrance * vector.quadrance) *
                  (vector.quadrance * vector.quadrance)⁻¹) := by ring1
            _ = 1 - ((1 - axis.quadrance) *
                (capDenominator axis)⁻¹) ^ 2 := by
              rw [vectorSquareCancel]
              ring1
    _ = 4 * (axis.quadrance * (capDenominator axis)⁻¹) *
        (1 * (capDenominator axis)⁻¹) := by
      calc
        1 - ((1 - axis.quadrance) *
            (capDenominator axis)⁻¹) ^ 2 =
          (capDenominator axis * (capDenominator axis)⁻¹) ^ 2 -
            ((1 - axis.quadrance) *
              (capDenominator axis)⁻¹) ^ 2 := by
                rw [denominatorCancel]
                ring1
        _ = 4 * (axis.quadrance * (capDenominator axis)⁻¹) *
            (1 * (capDenominator axis)⁻¹) := by
          unfold capDenominator
          ring1

/-- Theorem 31 for a half turn. -/
theorem rotationSpreadAt_halfTurn (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (vector : Vector K) (nonNull : vector.quadrance ≠ 0)
    (perpendicular : vector.Perpendicular axis) :
    rotationSpreadAt (halfTurnRotation axis axisNonNull) vector nonNull =
      rotationSpread (halfTurnRotation axis axisNonNull) := by
  have squareNonzero : vector.quadrance * vector.quadrance ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero nonNull nonNull
  have squareCancel := RFAP.ExplicitField.mul_inv_cancel
    (vector.quadrance * vector.quadrance) squareNonzero
  unfold rotationSpreadAt Vector.spread rotationSpread
  rw [show Matrix3.rowMul vector
      (halfTurnRotation axis axisNonNull).matrix = Vector.neg vector by
        exact rowMul_halfTurn_of_perpendicular axis axisNonNull twoNonzero
          vector perpendicular,
    Vector.dot_neg_right, Vector.quadrance_neg,
    halfSpread_halfTurn axis axisNonNull twoNonzero]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 - (-Vector.dot vector vector) ^ 2 *
        (vector.quadrance * vector.quadrance)⁻¹ =
      1 - (vector.quadrance * vector.quadrance) *
        (vector.quadrance * vector.quadrance)⁻¹ := by
          unfold Vector.quadrance
          ring1
    _ = 0 := by rw [squareCancel]; ring1
    _ = 4 * 1 * (1 - 1) := by ring1

/-- Independence of the perpendicular direction in Definition 30 for caps. -/
theorem rotationSpreadAt_cap_independent (axis : Vector K)
    (defined : capDenominator axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (firstPerpendicular : first.Perpendicular axis)
    (secondPerpendicular : second.Perpendicular axis) :
    rotationSpreadAt (capRotation axis defined) first firstNonNull =
      rotationSpreadAt (capRotation axis defined) second secondNonNull := by
  rw [rotationSpreadAt_cap axis defined twoNonzero first firstNonNull
      firstPerpendicular,
    rotationSpreadAt_cap axis defined twoNonzero second secondNonNull
      secondPerpendicular]

/-- Independence of the perpendicular direction in Definition 30 for half
turns. -/
theorem rotationSpreadAt_halfTurn_independent (axis : Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (firstPerpendicular : first.Perpendicular axis)
    (secondPerpendicular : second.Perpendicular axis) :
    rotationSpreadAt (halfTurnRotation axis axisNonNull) first firstNonNull =
    rotationSpreadAt (halfTurnRotation axis axisNonNull) second secondNonNull := by
  rw [rotationSpreadAt_halfTurn axis axisNonNull twoNonzero first firstNonNull
      firstPerpendicular,
    rotationSpreadAt_halfTurn axis axisNonNull twoNonzero second secondNonNull
      secondPerpendicular]

/-- Trace calculation underlying Theorem 32. -/
theorem trace_reflection_product (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0) :
    Matrix3.trace
        (Matrix3.mul (reflection first firstNonNull)
          (reflection second secondNonNull)) =
      3 - 4 * Vector.spread first second firstNonNull secondNonNull := by
  have firstCancel := RFAP.ExplicitField.mul_inv_cancel
    first.quadrance firstNonNull
  have secondCancel := RFAP.ExplicitField.mul_inv_cancel
    second.quadrance secondNonNull
  have productInverse :
      (first.quadrance * second.quadrance)⁻¹ =
        first.quadrance⁻¹ * second.quadrance⁻¹ :=
    inverse_product firstNonNull secondNonNull
  calc
    Matrix3.trace
        (Matrix3.mul (reflection first firstNonNull)
          (reflection second secondNonNull)) =
      -1 + 4 * Vector.dot first second ^ 2 *
        first.quadrance⁻¹ * second.quadrance⁻¹ := by
          unfold Matrix3.trace Matrix3.mul reflection Matrix3.sub
            Matrix3.identity Matrix3.scale Matrix3.outer
          simp only [RFAP.ExplicitField.div_eq_mul_inv]
          calc
            _ = 3 - 2 * (first.quadrance * first.quadrance⁻¹) -
                2 * (second.quadrance * second.quadrance⁻¹) +
                4 * Vector.dot first second ^ 2 *
                  first.quadrance⁻¹ * second.quadrance⁻¹ := by
                    unfold Vector.quadrance Vector.dot
                    ring1
            _ = -1 + 4 * Vector.dot first second ^ 2 *
                first.quadrance⁻¹ * second.quadrance⁻¹ := by
              rw [firstCancel, secondCancel]
              ring1
    _ = 3 - 4 * Vector.spread first second firstNonNull secondNonNull := by
      unfold Vector.spread
      simp only [RFAP.ExplicitField.div_eq_mul_inv, productInverse]
      ring1

/-- Theorem 32: the half spread of a product of two reflections is the spread
between their non-null normals. -/
theorem halfSpread_reflectionProduct (first second : Vector K)
    (firstNonNull : first.quadrance ≠ 0)
    (secondNonNull : second.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread
        (reflectionProductRotation first second firstNonNull secondNonNull) =
      Vector.spread first second firstNonNull secondNonNull := by
  have fourCancel := RFAP.ExplicitField.mul_inv_cancel (4 : K)
    (four_ne_zero twoNonzero)
  unfold halfSpread reflectionProductRotation
  rw [trace_reflection_product]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (3 - (3 - 4 * Vector.spread first second firstNonNull secondNonNull)) *
        (4 : K)⁻¹ =
      Vector.spread first second firstNonNull secondNonNull *
        (4 * (4 : K)⁻¹) := by ring1
    _ = Vector.spread first second firstNonNull secondNonNull := by
      rw [fourCancel, mul_one]

namespace ExampleThirtyThree

abbrev Scalar := RFAP.ConstructiveFraction.Rational

private theorem rational_natCast_ne_zero {value : Nat}
    (valueNonzero : value ≠ 0) : (value : Scalar) ≠ 0 := by
  intro castZero
  exact valueNonzero
    (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

private theorem eightyFourNonzero : (84 : Scalar) ≠ 0 :=
  rational_natCast_ne_zero (by decide)

private theorem twoNonzero : (2 : Scalar) ≠ 0 :=
  rational_natCast_ne_zero (by decide)

private theorem numerical_spread_identity
    {F : Type*} [RFAP.ExplicitField F] (eightyFourNonzero : (84 : F) ≠ 0) :
    1 - (1 : F) ^ 2 / (14 * 6) = 83 / 84 := by
  have denominator : (14 : F) * 6 = 84 := by ring1
  have cancel := RFAP.ExplicitField.mul_inv_cancel (84 : F)
    eightyFourNonzero
  rw [denominator]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 - 1 ^ 2 * (84 : F)⁻¹ =
        84 * (84 : F)⁻¹ - 1 ^ 2 * (84 : F)⁻¹ := by
          rw [cancel]
    _ = 83 * (84 : F)⁻¹ := by ring1

theorem dot_value :
    Vector.dot ExampleTwenty.first ExampleTwenty.second = (1 : Scalar) := by
  unfold ExampleTwenty.first ExampleTwenty.second Vector.dot
  ring1

theorem spread_value :
    Vector.spread ExampleTwenty.first ExampleTwenty.second
        ExampleTwenty.first_nonNull ExampleTwenty.second_nonNull =
      (83 : Scalar) / 84 := by
  unfold Vector.spread
  rw [dot_value, ExampleTwenty.first_quadrance,
    ExampleTwenty.second_quadrance]
  exact numerical_spread_identity eightyFourNonzero

theorem product_halfSpread :
    halfSpread
        (reflectionProductRotation ExampleTwenty.first ExampleTwenty.second
          ExampleTwenty.first_nonNull ExampleTwenty.second_nonNull) =
      (83 : Scalar) / 84 := by
  rw [halfSpread_reflectionProduct _ _ _ _ twoNonzero]
  exact spread_value

theorem product_trace :
    Matrix3.trace
        (Matrix3.mul
          (reflection ExampleTwenty.first ExampleTwenty.first_nonNull)
          (reflection ExampleTwenty.second ExampleTwenty.second_nonNull)) =
      (-20 : Scalar) / 21 := by
  rw [ExampleTwenty.product_displayed]
  decide

end ExampleThirtyThree

end RationalRotations
