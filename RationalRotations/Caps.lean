import RationalRotations.Reflections
import DivineProportions.Algebra.FieldFive

/-!
# Rational rotations, section 5: the cap of an anchor

The cap is stored by the executable quadratic formula from Theorem 23.  The
canonical Cayley specification from Definition 21 is tied to it by an
explicit two-sided inverse for `I-A`; no generic matrix inversion or choice is
used.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- The scalar denominator controlling whether an anchor has a cap. -/
def capDenominator (vector : Vector K) : K := 1 + vector.quadrance

/-- Lemma 22's executable inverse candidate for `I-A`. -/
def anchorResolventInverse (vector : Vector K)
    (_defined : capDenominator vector ≠ 0) : Matrix3 K :=
  Matrix3.add Matrix3.identity
    (Matrix3.scale (1 / capDenominator vector)
      (Matrix3.add (anchor vector)
        (Matrix3.mul (anchor vector) (anchor vector))))

/-- Definition 21, cached in the quadratic form of Theorem 23. -/
def cap (vector : Vector K) (_defined : capDenominator vector ≠ 0) :
    Matrix3 K :=
  Matrix3.add Matrix3.identity
    (Matrix3.scale (2 / capDenominator vector)
      (Matrix3.add (anchor vector)
        (Matrix3.mul (anchor vector) (anchor vector))))

private theorem denominator_mul_inverse (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    capDenominator vector * (capDenominator vector)⁻¹ = (1 : K) :=
  RFAP.ExplicitField.mul_inv_cancel (capDenominator vector) defined

private theorem zero_scale_add_identity (matrix : Matrix3 K) :
    Matrix3.add Matrix3.identity (Matrix3.scale 0 matrix) =
      Matrix3.identity := by
  ext <;> unfold Matrix3.add Matrix3.scale Matrix3.identity <;> ring1

/-- Lemma 22, left-inverse certificate. -/
theorem anchorResolventInverse_left (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul
        (Matrix3.sub Matrix3.identity (anchor vector))
        (anchorResolventInverse vector defined) =
      Matrix3.identity := by
  have cancel := denominator_mul_inverse vector defined
  have coefficientZero :
      capDenominator vector * (capDenominator vector)⁻¹ - 1 = 0 := by
    rw [cancel]
    ring1
  calc
    Matrix3.mul
        (Matrix3.sub Matrix3.identity (anchor vector))
        (anchorResolventInverse vector defined) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          (capDenominator vector * (capDenominator vector)⁻¹ - 1)
          (anchor vector)) := by
            ext <;> unfold anchorResolventInverse capDenominator Matrix3.mul
              Matrix3.sub Matrix3.add Matrix3.scale Matrix3.identity anchor
              Vector.quadrance Vector.dot <;>
              simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1
    _ = Matrix3.identity := by
      rw [coefficientZero]
      exact zero_scale_add_identity (anchor vector)

/-- Lemma 22, right-inverse certificate. -/
theorem anchorResolventInverse_right (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul
        (anchorResolventInverse vector defined)
        (Matrix3.sub Matrix3.identity (anchor vector)) =
      Matrix3.identity := by
  have cancel := denominator_mul_inverse vector defined
  have coefficientZero :
      capDenominator vector * (capDenominator vector)⁻¹ - 1 = 0 := by
    rw [cancel]
    ring1
  calc
    Matrix3.mul
        (anchorResolventInverse vector defined)
        (Matrix3.sub Matrix3.identity (anchor vector)) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          (capDenominator vector * (capDenominator vector)⁻¹ - 1)
          (anchor vector)) := by
            ext <;> unfold anchorResolventInverse capDenominator Matrix3.mul
              Matrix3.sub Matrix3.add Matrix3.scale Matrix3.identity anchor
              Vector.quadrance Vector.dot <;>
              simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1
    _ = Matrix3.identity := by
      rw [coefficientZero]
      exact zero_scale_add_identity (anchor vector)

/-- Definition 21 agrees with the cached quadratic value: the cap is the
displayed Cayley product `(I+A)(I-A)⁻¹`. -/
theorem cap_eq_cayley (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    cap vector defined =
      Matrix3.mul (Matrix3.add Matrix3.identity (anchor vector))
        (anchorResolventInverse vector defined) := by
  have cancel := denominator_mul_inverse vector defined
  have coefficientZero :
      1 - capDenominator vector * (capDenominator vector)⁻¹ = 0 := by
    rw [cancel]
    ring1
  symm
  calc
    Matrix3.mul (Matrix3.add Matrix3.identity (anchor vector))
        (anchorResolventInverse vector defined) =
      Matrix3.add (cap vector defined)
        (Matrix3.scale
          (1 - capDenominator vector * (capDenominator vector)⁻¹)
          (anchor vector)) := by
            ext <;> unfold anchorResolventInverse cap capDenominator
              Matrix3.mul Matrix3.add Matrix3.scale
              Matrix3.identity anchor Vector.quadrance Vector.dot <;>
              simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1
    _ = cap vector defined := by
      rw [coefficientZero]
      ext <;> unfold Matrix3.add Matrix3.scale <;> ring1

/-- Theorem 23: the quadratic reduction is the executable definition of the
cap. -/
theorem cap_quadratic (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    cap vector defined =
      Matrix3.add Matrix3.identity
        (Matrix3.scale (2 / capDenominator vector)
          (Matrix3.add (anchor vector)
            (Matrix3.mul (anchor vector) (anchor vector)))) := rfl

/-- The coordinate matrix printed after Theorem 23. -/
theorem cap_coordinate_formula (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    cap vector defined =
      Matrix3.scale (1 / capDenominator vector)
        ⟨vector.t ^ 2 - vector.r ^ 2 - vector.s ^ 2 + 1,
          2 * (vector.s + vector.r * vector.t),
          2 * (-vector.r + vector.s * vector.t),
          2 * (-vector.s + vector.r * vector.t),
          -vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2 + 1,
          2 * (vector.t + vector.r * vector.s),
          2 * (vector.r + vector.s * vector.t),
          2 * (-vector.t + vector.r * vector.s),
          -vector.t ^ 2 - vector.r ^ 2 + vector.s ^ 2 + 1⟩ := by
  have cancel := denominator_mul_inverse vector defined
  have inverseCancel :
      capDenominator vector * (1 / capDenominator vector) = 1 := by
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      capDenominator vector * (1 * (capDenominator vector)⁻¹) =
          capDenominator vector * (capDenominator vector)⁻¹ := by ring1
      _ = 1 := cancel
  have doubleCancel :
      capDenominator vector * (2 / capDenominator vector) = 2 := by
    rw [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      capDenominator vector * (2 * (capDenominator vector)⁻¹) =
          2 * (capDenominator vector * (capDenominator vector)⁻¹) := by
            ring1
      _ = 2 := by rw [cancel]; ring1
  apply Matrix3.eq_of_scale_eq_scale defined
  unfold cap
  rw [Matrix3.scale_add, Matrix3.scale_scale, doubleCancel,
    Matrix3.scale_scale, inverseCancel]
  ext <;> unfold capDenominator Matrix3.add Matrix3.scale Matrix3.identity
    Matrix3.mul anchor Vector.quadrance Vector.dot <;> ring1

/-- The determinant calculation preceding Lemma 22. -/
theorem determinant_identity_sub_anchor (vector : Vector K) :
    Matrix3.determinant (Matrix3.sub Matrix3.identity (anchor vector)) =
      capDenominator vector := by
  unfold Matrix3.determinant Matrix3.sub Matrix3.identity anchor
    capDenominator Vector.quadrance Vector.dot
  ring1

/-- The matching determinant for `I+A`. -/
theorem determinant_identity_add_anchor (vector : Vector K) :
    Matrix3.determinant (Matrix3.add Matrix3.identity (anchor vector)) =
      capDenominator vector := by
  unfold Matrix3.determinant Matrix3.add Matrix3.identity anchor
    capDenominator Vector.quadrance Vector.dot
  ring1

/-- Multiplying the quadratic cap by `I-A` recovers `I+A`. -/
theorem cap_mul_identity_sub_anchor (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul (cap vector defined)
        (Matrix3.sub Matrix3.identity (anchor vector)) =
      Matrix3.add Matrix3.identity (anchor vector) := by
  have cancel := denominator_mul_inverse vector defined
  have coefficientZero :
      2 * (capDenominator vector * (capDenominator vector)⁻¹ - 1) =
        0 := by
    rw [cancel]
    ring1
  calc
    Matrix3.mul (cap vector defined)
        (Matrix3.sub Matrix3.identity (anchor vector)) =
      Matrix3.add (Matrix3.add Matrix3.identity (anchor vector))
        (Matrix3.scale
          (2 * (capDenominator vector *
            (capDenominator vector)⁻¹ - 1)) (anchor vector)) := by
              ext <;> unfold cap capDenominator Matrix3.mul Matrix3.sub
                Matrix3.add Matrix3.scale Matrix3.identity anchor
                Vector.quadrance Vector.dot <;>
                simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1
    _ = Matrix3.add Matrix3.identity (anchor vector) := by
      rw [coefficientZero]
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.identity anchor <;>
        ring1

/-- The same Cayley relation with `I-A` on the left. -/
theorem identity_sub_anchor_mul_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul (Matrix3.sub Matrix3.identity (anchor vector))
        (cap vector defined) =
      Matrix3.add Matrix3.identity (anchor vector) := by
  have cancel := denominator_mul_inverse vector defined
  have coefficientZero :
      2 * (capDenominator vector * (capDenominator vector)⁻¹ - 1) =
        0 := by
    rw [cancel]
    ring1
  calc
    Matrix3.mul (Matrix3.sub Matrix3.identity (anchor vector))
        (cap vector defined) =
      Matrix3.add (Matrix3.add Matrix3.identity (anchor vector))
        (Matrix3.scale
          (2 * (capDenominator vector *
            (capDenominator vector)⁻¹ - 1)) (anchor vector)) := by
              ext <;> unfold cap capDenominator Matrix3.mul Matrix3.sub
                Matrix3.add Matrix3.scale Matrix3.identity anchor
                Vector.quadrance Vector.dot <;>
                simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1
    _ = Matrix3.add Matrix3.identity (anchor vector) := by
      rw [coefficientZero]
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.identity anchor <;>
        ring1

theorem capDenominator_neg (vector : Vector K) :
    capDenominator (Vector.neg vector) = capDenominator vector := by
  unfold capDenominator
  rw [Vector.quadrance_neg]

theorem cap_neg_defined (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    capDenominator (Vector.neg vector) ≠ 0 := by
  rw [capDenominator_neg]
  exact defined

/-- Transposition negates the anchor vector of a cap. -/
theorem transpose_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.transpose (cap vector defined) =
      cap (Vector.neg vector) (cap_neg_defined vector defined) := by
  unfold cap
  rw [capDenominator_neg, anchor_neg]
  ext <;> unfold Matrix3.transpose Matrix3.add Matrix3.scale
    Matrix3.identity Matrix3.mul Matrix3.neg anchor <;> ring1

private theorem cap_inverse_coefficient (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    2 * (2 / capDenominator vector) -
      (2 / capDenominator vector) ^ 2 * capDenominator vector = 0 := by
  have cancel := denominator_mul_inverse vector defined
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    2 * (2 * (capDenominator vector)⁻¹) -
        (2 * (capDenominator vector)⁻¹) ^ 2 *
          capDenominator vector =
      4 * (capDenominator vector)⁻¹ *
        (1 - capDenominator vector * (capDenominator vector)⁻¹) := by
          ring1
    _ = 0 := by rw [cancel]; ring1

/-- A cap multiplied by the cap at the negated anchor is the identity. -/
theorem cap_mul_cap_neg (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul (cap vector defined)
        (cap (Vector.neg vector) (cap_neg_defined vector defined)) =
      Matrix3.identity := by
  have coefficientZero := cap_inverse_coefficient vector defined
  calc
    Matrix3.mul (cap vector defined)
        (cap (Vector.neg vector) (cap_neg_defined vector defined)) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          (2 * (2 / capDenominator vector) -
            (2 / capDenominator vector) ^ 2 * capDenominator vector)
          (Matrix3.mul (anchor vector) (anchor vector))) := by
            unfold cap
            rw [capDenominator_neg, anchor_neg]
            ext <;> unfold Matrix3.mul Matrix3.add Matrix3.scale
              Matrix3.identity Matrix3.neg anchor capDenominator
              Vector.quadrance Vector.dot <;> ring1
    _ = Matrix3.identity := by
      rw [coefficientZero]
      exact zero_scale_add_identity _

/-- The inverse multiplication in the opposite order. -/
theorem cap_neg_mul_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.mul
        (cap (Vector.neg vector) (cap_neg_defined vector defined))
        (cap vector defined) = Matrix3.identity := by
  have coefficientZero := cap_inverse_coefficient vector defined
  calc
    Matrix3.mul
        (cap (Vector.neg vector) (cap_neg_defined vector defined))
        (cap vector defined) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale
          (2 * (2 / capDenominator vector) -
            (2 / capDenominator vector) ^ 2 * capDenominator vector)
          (Matrix3.mul (anchor vector) (anchor vector))) := by
            unfold cap
            rw [capDenominator_neg, anchor_neg]
            ext <;> unfold Matrix3.mul Matrix3.add Matrix3.scale
              Matrix3.identity Matrix3.neg anchor capDenominator
              Vector.quadrance Vector.dot <;> ring1
    _ = Matrix3.identity := by
      rw [coefficientZero]
      exact zero_scale_add_identity _

/-- Theorem 24.1, orthogonality of a cap. -/
theorem cap_isOrthogonal (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.IsOrthogonal (cap vector defined) := by
  unfold Matrix3.IsOrthogonal
  rw [transpose_cap, cap_mul_cap_neg]

/-- Theorem 24.1, determinant one. -/
theorem determinant_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.determinant (cap vector defined) = 1 := by
  have determinantEquation := congrArg Matrix3.determinant
    (cap_mul_identity_sub_anchor vector defined)
  rw [Matrix3.determinant_mul, determinant_identity_sub_anchor,
    determinant_identity_add_anchor] at determinantEquation
  have cancel := denominator_mul_inverse vector defined
  calc
    Matrix3.determinant (cap vector defined) =
        Matrix3.determinant (cap vector defined) *
          (capDenominator vector * (capDenominator vector)⁻¹) := by
            rw [cancel, mul_one]
    _ = (Matrix3.determinant (cap vector defined) *
          capDenominator vector) * (capDenominator vector)⁻¹ := by ring1
    _ = capDenominator vector * (capDenominator vector)⁻¹ := by
      rw [determinantEquation]
    _ = 1 := cancel

/-- The cap bundled with its executable `SO(3)` certificates. -/
def capRotation (vector : Vector K) (defined : capDenominator vector ≠ 0) :
    Rotation K where
  matrix := cap vector defined
  orthogonal := cap_isOrthogonal vector defined
  determinantOne := determinant_cap vector defined

/-- Theorem 24.2: the anchor vector is fixed by its cap. -/
theorem rowMul_self_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.rowMul vector (cap vector defined) = vector := by
  ext <;> unfold Matrix3.rowMul cap capDenominator Matrix3.add
    Matrix3.scale Matrix3.identity Matrix3.mul anchor Vector.quadrance
    Vector.dot <;> ring1

/-- Trace calculation used in Theorem 24.3. -/
theorem trace_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.trace (cap vector defined) =
      (3 - vector.quadrance) / capDenominator vector := by
  have cancel := denominator_mul_inverse vector defined
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    Matrix3.trace (cap vector defined) =
        3 - 4 * vector.quadrance * (capDenominator vector)⁻¹ := by
          unfold Matrix3.trace cap capDenominator Matrix3.add Matrix3.scale
            Matrix3.identity Matrix3.mul anchor Vector.quadrance Vector.dot
          simp only [RFAP.ExplicitField.div_eq_mul_inv]
          ring1
    _ = 3 * (capDenominator vector * (capDenominator vector)⁻¹) -
        4 * vector.quadrance * (capDenominator vector)⁻¹ := by
          rw [cancel]
          ring1
    _ = (3 - vector.quadrance) * (capDenominator vector)⁻¹ := by
      unfold capDenominator
      ring1

/-- The adjugate of a cap is its transpose, obtained from the explicit left
inverse rather than a generic inverse theorem. -/
theorem adjugate_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.adjugate (cap vector defined) =
      Matrix3.transpose (cap vector defined) := by
  have adjugateProduct :
      Matrix3.mul (cap vector defined) (Matrix3.adjugate (cap vector defined)) =
        Matrix3.identity := by
    calc
      Matrix3.mul (cap vector defined) (Matrix3.adjugate (cap vector defined)) =
          Matrix3.scale (Matrix3.determinant (cap vector defined))
            Matrix3.identity := Matrix3.mul_adjugate _
      _ = Matrix3.identity := by
        rw [determinant_cap]
        ext <;> unfold Matrix3.scale Matrix3.identity <;> ring1
  calc
    Matrix3.adjugate (cap vector defined) =
        Matrix3.mul Matrix3.identity (Matrix3.adjugate (cap vector defined)) := by
          rw [Matrix3.identity_mul]
    _ = Matrix3.mul
        (Matrix3.mul
          (cap (Vector.neg vector) (cap_neg_defined vector defined))
          (cap vector defined))
        (Matrix3.adjugate (cap vector defined)) := by
          rw [cap_neg_mul_cap]
    _ = Matrix3.mul
        (cap (Vector.neg vector) (cap_neg_defined vector defined))
        (Matrix3.mul (cap vector defined)
          (Matrix3.adjugate (cap vector defined))) := by
            rw [Matrix3.mul_assoc]
    _ = cap (Vector.neg vector) (cap_neg_defined vector defined) := by
      rw [adjugateProduct, Matrix3.mul_identity]
    _ = Matrix3.transpose (cap vector defined) :=
      (transpose_cap vector defined).symm

/-- For a cap, the two non-leading characteristic coefficients agree. -/
theorem principalTrace_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.principalTrace (cap vector defined) =
      Matrix3.trace (cap vector defined) := by
  unfold Matrix3.principalTrace
  rw [adjugate_cap, Matrix3.trace_transpose]

private theorem trace_cap_sub_one (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.trace (cap vector defined) - 1 =
      2 * (1 - vector.quadrance) / capDenominator vector := by
  have cancel := denominator_mul_inverse vector defined
  rw [trace_cap]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (3 - vector.quadrance) * (capDenominator vector)⁻¹ - 1 =
        (3 - vector.quadrance) * (capDenominator vector)⁻¹ -
          capDenominator vector * (capDenominator vector)⁻¹ := by
            rw [cancel]
    _ = 2 * (1 - vector.quadrance) *
        (capDenominator vector)⁻¹ := by
      unfold capDenominator
      ring1

/-- Theorem 24.3: characteristic polynomial of a cap. -/
theorem characteristicValue_cap (vector : Vector K)
    (defined : capDenominator vector ≠ 0) (X : K) :
    Matrix3.characteristicValue (cap vector defined) X =
      (X - 1) *
        (X ^ 2 -
          (2 * (1 - vector.quadrance) / capDenominator vector) * X + 1) := by
  calc
    Matrix3.characteristicValue (cap vector defined) X =
        X ^ 3 - Matrix3.trace (cap vector defined) * X ^ 2 +
          Matrix3.principalTrace (cap vector defined) * X -
            Matrix3.determinant (cap vector defined) :=
      Matrix3.characteristicValue_expansion _ _
    _ = X ^ 3 - Matrix3.trace (cap vector defined) * X ^ 2 +
          Matrix3.trace (cap vector defined) * X - 1 := by
      rw [principalTrace_cap, determinant_cap]
    _ = (X - 1) *
        (X ^ 2 - (Matrix3.trace (cap vector defined) - 1) * X + 1) := by
      ring1
    _ = (X - 1) *
        (X ^ 2 -
          (2 * (1 - vector.quadrance) / capDenominator vector) * X + 1) := by
      rw [trace_cap_sub_one]

private theorem eq_zero_of_two_mul_eq_zero (twoNonzero : (2 : K) ≠ 0)
    (value : K) (twiceZero : 2 * value = 0) : value = 0 := by
  have cancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  calc
    value = 1 * value := by rw [one_mul]
    _ = (2 * (2 : K)⁻¹) * value := by rw [cancel]
    _ = (2 * value) * (2 : K)⁻¹ := by ring1
    _ = 0 := by rw [twiceZero, zero_mul]

/-- Theorem 24.4: minus one is not an eigenvalue of a cap. -/
theorem rowMul_cap_eq_neg_implies_zero (vector : Vector K)
    (defined : capDenominator vector ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (other : Vector K)
    (negativeEigen : Matrix3.rowMul other (cap vector defined) =
      Vector.neg other) : other = Vector.zero := by
  have transported := congrArg
    (fun value => Matrix3.rowMul value
      (Matrix3.sub Matrix3.identity (anchor vector))) negativeEigen
  rw [Matrix3.rowMul_mul, cap_mul_identity_sub_anchor] at transported
  have tEquation := congrArg Vector.t transported
  have rEquation := congrArg Vector.r transported
  have sEquation := congrArg Vector.s transported
  apply Vector.ext
  · apply eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * other.t =
          (Matrix3.rowMul other
            (Matrix3.add Matrix3.identity (anchor vector))).t -
          (Matrix3.rowMul (Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).t := by
              unfold Matrix3.rowMul Matrix3.add Matrix3.sub Matrix3.identity
                anchor Vector.neg
              ring1
      _ = (Matrix3.rowMul (Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).t -
          (Matrix3.rowMul (Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).t := by
              rw [tEquation]
      _ = 0 := by ring1
  · apply eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * other.r =
          (Matrix3.rowMul other
            (Matrix3.add Matrix3.identity (anchor vector))).r -
          (Matrix3.rowMul (Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).r := by
              unfold Matrix3.rowMul Matrix3.add Matrix3.sub Matrix3.identity
                anchor Vector.neg
              ring1
      _ = (Matrix3.rowMul (Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).r -
          (Matrix3.rowMul (Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).r := by
              rw [rEquation]
      _ = 0 := by ring1
  · apply eq_zero_of_two_mul_eq_zero twoNonzero
    calc
      2 * other.s =
          (Matrix3.rowMul other
            (Matrix3.add Matrix3.identity (anchor vector))).s -
          (Matrix3.rowMul (Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).s := by
              unfold Matrix3.rowMul Matrix3.add Matrix3.sub Matrix3.identity
                anchor Vector.neg
              ring1
      _ = (Matrix3.rowMul (Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).s -
          (Matrix3.rowMul (Vector.neg other)
            (Matrix3.sub Matrix3.identity (anchor vector))).s := by
              rw [sEquation]
      _ = 0 := by ring1

/-- The antisymmetric part of a cap exposes its anchor up to the displayed
nonzero scalar. -/
theorem cap_antisymmetric_part (vector : Vector K)
    (defined : capDenominator vector ≠ 0) :
    Matrix3.sub (cap vector defined) (Matrix3.transpose (cap vector defined)) =
      Matrix3.scale (4 / capDenominator vector) (anchor vector) := by
  ext <;> unfold cap capDenominator Matrix3.sub Matrix3.transpose
    Matrix3.add Matrix3.scale Matrix3.identity Matrix3.mul anchor
    Vector.quadrance Vector.dot <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1

private theorem cross_mul_of_div_eq_div
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (equal : leftNumerator / leftDenominator =
      rightNumerator / rightDenominator) :
    leftNumerator * rightDenominator =
      rightNumerator * leftDenominator := by
  have leftCancel := RFAP.ExplicitField.mul_inv_cancel
    leftDenominator leftNonzero
  have rightCancel := RFAP.ExplicitField.mul_inv_cancel
    rightDenominator rightNonzero
  calc
    leftNumerator * rightDenominator =
        leftNumerator *
          (leftDenominator * leftDenominator⁻¹) * rightDenominator := by
            rw [leftCancel]
            ring1
    _ =
        (leftNumerator / leftDenominator) *
          (leftDenominator * rightDenominator) := by
            simp only [RFAP.ExplicitField.div_eq_mul_inv]
            ring1
    _ = (rightNumerator / rightDenominator) *
          (leftDenominator * rightDenominator) := by rw [equal]
    _ = rightNumerator * leftDenominator := by
      simp only [RFAP.ExplicitField.div_eq_mul_inv]
      calc
        rightNumerator * rightDenominator⁻¹ *
            (leftDenominator * rightDenominator) =
          rightNumerator *
            (rightDenominator * rightDenominator⁻¹) * leftDenominator := by
              ring1
        _ = rightNumerator * leftDenominator := by
          rw [rightCancel]
          ring1

private theorem eq_zero_of_nonzero_mul_eq_zero {factor value : K}
    (factorNonzero : factor ≠ 0) (productZero : factor * value = 0) :
    value = 0 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = (factor * factor⁻¹) * value := by rw [cancel, one_mul]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero, mul_zero]

/-- Theorem 24.5: the cap is injective on its domain. -/
theorem cap_injective (twoNonzero : (2 : K) ≠ 0)
    (first second : Vector K)
    (firstDefined : capDenominator first ≠ 0)
    (secondDefined : capDenominator second ≠ 0)
    (equalCaps : cap first firstDefined = cap second secondDefined) :
    first = second := by
  have traceEqual := congrArg Matrix3.trace equalCaps
  rw [trace_cap first firstDefined, trace_cap second secondDefined] at traceEqual
  have crossed := cross_mul_of_div_eq_div firstDefined secondDefined traceEqual
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have quadranceDifference :
      4 * (second.quadrance - first.quadrance) = 0 := by
    calc
      4 * (second.quadrance - first.quadrance) =
          (3 - first.quadrance) * capDenominator second -
            (3 - second.quadrance) * capDenominator first := by
              unfold capDenominator
              ring1
      _ = 0 := by rw [crossed]; ring1
  have differenceZero := eq_zero_of_nonzero_mul_eq_zero
    fourNonzero quadranceDifference
  have quadrancesEqual : first.quadrance = second.quadrance := by
    calc
      first.quadrance = second.quadrance -
          (second.quadrance - first.quadrance) := by ring1
      _ = second.quadrance := by rw [differenceZero]; ring1
  have partsEqual := congrArg
    (fun matrix => Matrix3.sub matrix (Matrix3.transpose matrix)) equalCaps
  rw [cap_antisymmetric_part first firstDefined,
    cap_antisymmetric_part second secondDefined] at partsEqual
  have denominatorsEqual : capDenominator first = capDenominator second := by
    unfold capDenominator
    rw [quadrancesEqual]
  rw [denominatorsEqual] at partsEqual
  have scalarNonzero : 4 / capDenominator second ≠ 0 :=
    RFAP.ExplicitField.div_ne_zero fourNonzero secondDefined
  exact anchor_injective
    (Matrix3.eq_of_scale_eq_scale scalarNonzero partsEqual)

namespace ExampleTwentyFive

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def vector : Vector Scalar := ⟨4, 1, 7⟩

theorem quadrance : vector.quadrance = 66 := by
  unfold vector Vector.quadrance Vector.dot
  ring1

theorem defined : capDenominator vector ≠ 0 := by decide

def displayed : Matrix3 Scalar :=
  Matrix3.scale (1 / 67) ⟨-33, 22, 54, -6, -63, 22, 58, 6, 33⟩

private theorem numerator_displayed {F : Type*} [RFAP.ExplicitField F] :
    (⟨(4 : F) ^ 2 - 1 ^ 2 - 7 ^ 2 + 1,
        2 * (7 + 1 * 4),
        2 * (-1 + 7 * 4),
        2 * (-7 + 1 * 4),
        -(4 : F) ^ 2 + 1 ^ 2 - 7 ^ 2 + 1,
        2 * (4 + 1 * 7),
        2 * (1 + 7 * 4),
        2 * (-4 + 1 * 7),
        -(4 : F) ^ 2 - 1 ^ 2 + 7 ^ 2 + 1⟩ : Matrix3 F) =
      ⟨-33, 22, 54, -6, -63, 22, 58, 6, 33⟩ := by
  ext <;> ring1

theorem cap_displayed : cap vector defined = displayed := by
  rw [cap_coordinate_formula]
  have denominator : capDenominator vector = 67 := by
    unfold capDenominator
    rw [quadrance]
    ring1
  rw [denominator]
  simpa only [vector, displayed] using
    congrArg (Matrix3.scale (1 / 67 : Scalar))
      (numerator_displayed (F := Scalar))

theorem vector_fixed : Matrix3.rowMul vector displayed = vector := by
  rw [← cap_displayed]
  exact rowMul_self_cap vector defined

end ExampleTwentyFive

namespace ExampleTwentySix

abbrev Scalar := DivineProportions.FieldFive.Element

def vector : Vector Scalar := ⟨2, 0, 0⟩

theorem quadrance : vector.quadrance = -1 := by decide

theorem denominator_zero : capDenominator vector = 0 := by decide

theorem identity_sub_anchor_singular :
    Matrix3.determinant (Matrix3.sub Matrix3.identity (anchor vector)) = 0 := by
  rw [determinant_identity_sub_anchor, denominator_zero]

end ExampleTwentySix

namespace ExampleTwentySeven

abbrev Scalar := DivineProportions.FieldFive.Element

def vector : Vector Scalar := ⟨1, 2, 0⟩

theorem null : vector.quadrance = 0 := by decide

theorem defined : capDenominator vector ≠ 0 := by decide

def displayed : Matrix3 Scalar := ⟨3, 4, 1, 4, 4, 2, 4, 3, 1⟩

theorem cap_displayed : cap vector defined = displayed := by decide

theorem vector_fixed : Matrix3.rowMul vector displayed = vector := by decide

theorem not_identity : displayed ≠ Matrix3.identity := by decide

theorem characteristic_unipotent (X : Scalar) :
    Matrix3.characteristicValue displayed X = (X - 1) ^ 3 := by
  decide +revert

end ExampleTwentySeven

end RationalRotations
