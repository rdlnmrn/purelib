import RationalRotations.ProjectiveRotations
import RationalRotations.RotationAnchors

/-!
# Rational rotations, Theorem 58 and Corollary 60

The projective bijection is expressed without a quotient: every rotation gets
an executable non-null representative, and two representatives give the same
matrix exactly when an explicit nonzero scale relates them.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

private theorem one_ne_zero_of_two_ne_zero (twoNonzero : (2 : K) ≠ 0) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply twoNonzero
  calc
    (2 : K) = 1 + 1 := by ring1
    _ = 0 := by rw [oneZero, zero_add]

private theorem inverse_one (oneNonzero : (1 : K) ≠ 0) :
    (1 : K)⁻¹ = 1 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel (1 : K) oneNonzero
  simpa only [one_mul] using cancel

namespace RotationProportion

/-- The affine inverse branch of Theorem 58. -/
def affine (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) : NonNullProportion K where
  scalar := 1
  vector := rotationAnchorVector rotation notHalfTurn
  normNonzero := by
    simpa only [Proportion.norm, capDenominator, one_pow] using
      rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero

theorem affine_rotationMatrix (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (affine rotation notHalfTurn twoNonzero).rotationMatrix =
      rotation.matrix := by
  let proportion := affine rotation notHalfTurn twoNonzero
  have scalarValue : proportion.scalar = 1 := rfl
  have vectorValue :
      proportion.vector = rotationAnchorVector rotation notHalfTurn := rfl
  have scalarNonzero : proportion.scalar ≠ 0 := by
    rw [scalarValue]
    exact one_ne_zero_of_two_ne_zero twoNonzero
  calc
    proportion.rotationMatrix =
        cap (Vector.scale proportion.scalar⁻¹ proportion.vector)
          (reciprocalAnchorCapDefined proportion.scalar proportion.vector
            scalarNonzero proportion.normNonzero) :=
      NonNullProportion.rotationMatrix_eq_cap proportion scalarNonzero
    _ = cap (rotationAnchorVector rotation notHalfTurn)
        (rotationAnchorVector_capDefined rotation notHalfTurn twoNonzero) := by
      congr 1
      rw [scalarValue, vectorValue,
        inverse_one (one_ne_zero_of_two_ne_zero twoNonzero), Vector.one_scale]
    _ = rotation.matrix := cap_rotationAnchor rotation notHalfTurn twoNonzero

/-- The vector `w` in the paper's unnormalized inverse
`(1 + tr(ρ) : w)`. -/
def affineHomogeneousVector (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1) : Vector K :=
  Vector.scale (1 + Matrix3.trace rotation.matrix)
    (rotationAnchorVector rotation notHalfTurn)

/-- The affine inverse in exactly the homogeneous scale printed in Theorem
58. -/
def affineHomogeneous (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) : NonNullProportion K :=
  NonNullProportion.scale (1 + Matrix3.trace rotation.matrix)
    (rotationAnchorDenominator_ne_zero rotation notHalfTurn twoNonzero)
    (affine rotation notHalfTurn twoNonzero)

theorem affineHomogeneous_scalar (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (affineHomogeneous rotation notHalfTurn twoNonzero).scalar =
      1 + Matrix3.trace rotation.matrix := by
  unfold affineHomogeneous NonNullProportion.scale affine Proportion.scale
  ring1

theorem affineHomogeneous_vector (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (affineHomogeneous rotation notHalfTurn twoNonzero).vector =
      affineHomogeneousVector rotation notHalfTurn := rfl

/-- The displayed inverse vector satisfies `A_w=ρ-ρᵀ=2ρ_as`. -/
theorem anchor_affineHomogeneousVector (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    anchor (affineHomogeneousVector rotation notHalfTurn) =
      Matrix3.sub rotation.matrix (Matrix3.transpose rotation.matrix) := by
  have denominatorNonzero := rotationAnchorDenominator_ne_zero rotation
    notHalfTurn twoNonzero
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    (1 + Matrix3.trace rotation.matrix) denominatorNonzero
  unfold affineHomogeneousVector
  rw [anchor_scale,
    anchor_rotationAnchorVector rotation notHalfTurn twoNonzero]
  unfold rotationAnchor
  rw [Matrix3.scale_scale]
  have coefficient :
      (1 + Matrix3.trace rotation.matrix) *
          (1 / (1 + Matrix3.trace rotation.matrix)) = 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv, one_mul]
    exact cancel
  rw [coefficient, Matrix3.one_scale]

theorem two_mul_antisymmetricPart (matrix : Matrix3 K)
    (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.scale 2 (antisymmetricPart matrix) =
      Matrix3.sub matrix (Matrix3.transpose matrix) := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  unfold antisymmetricPart
  rw [Matrix3.scale_scale]
  have coefficient : (2 : K) * (1 / 2) = 1 := by
    simp only [RFAP.ExplicitField.div_eq_mul_inv, one_mul]
    exact cancel
  rw [coefficient, Matrix3.one_scale]

theorem anchor_affineHomogeneousVector_eq_two_antisymmetricPart
    (rotation : Rotation K) (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    anchor (affineHomogeneousVector rotation notHalfTurn) =
      Matrix3.scale 2 (antisymmetricPart rotation.matrix) := by
  rw [anchor_affineHomogeneousVector rotation notHalfTurn twoNonzero,
    two_mul_antisymmetricPart rotation.matrix twoNonzero]

theorem affineHomogeneous_rotationMatrix (rotation : Rotation K)
    (notHalfTurn : halfSpread rotation ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (affineHomogeneous rotation notHalfTurn twoNonzero).rotationMatrix =
      rotation.matrix := by
  unfold affineHomogeneous
  rw [NonNullProportion.rotationMatrix_scale,
    affine_rotationMatrix rotation notHalfTurn twoNonzero]

/-- The infinity inverse branch of Theorem 58, using the executable row-pivot
axis selected in the constructive half-turn classification. -/
def atInfinity [DecidableEq K] (rotation : Rotation K)
    (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) : NonNullProportion K where
  scalar := 0
  vector := halfTurnAxis rotation halfTurnSpread twoNonzero
  normNonzero := by
    unfold Proportion.norm
    rw [show (0 : K) ^ 2 = 0 by ring1, zero_add]
    exact halfTurnAxis_nonNull rotation halfTurnSpread twoNonzero

theorem atInfinity_rotationMatrix [DecidableEq K]
    (rotation : Rotation K) (halfTurnSpread : halfSpread rotation = 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (atInfinity rotation halfTurnSpread twoNonzero).rotationMatrix =
      rotation.matrix := by
  rw [NonNullProportion.rotationMatrix_eq_halfTurn
    (atInfinity rotation halfTurnSpread twoNonzero) (by rfl)]
  exact (rotation_eq_halfTurn_halfTurnAxis rotation halfTurnSpread
    twoNonzero).symm

private def ofAxisChart (rotation : Rotation K) (axis : Vector K)
    (chart : RotationAxisChart rotation axis) : NonNullProportion K :=
  match chart with
  | .affine _ defined _ =>
      { scalar := 1
        vector := axis
        normNonzero := by
          simpa only [Proportion.norm, capDenominator, one_pow] using defined }
  | .halfTurn _ axisNonNull _ =>
      { scalar := 0
        vector := axis
        normNonzero := by
          unfold Proportion.norm
          rw [show (0 : K) ^ 2 = 0 by ring1, zero_add]
          exact axisNonNull }

private theorem ofAxisChart_rotationMatrix (rotation : Rotation K)
    (axis : Vector K) (chart : RotationAxisChart rotation axis)
    (twoNonzero : (2 : K) ≠ 0) :
    (ofAxisChart rotation axis chart).rotationMatrix = rotation.matrix := by
  cases chart with
  | affine notHalfTurn defined matrixEq =>
      let proportion := ofAxisChart rotation axis
        (RotationAxisChart.affine notHalfTurn defined matrixEq)
      have scalarNonzero : proportion.scalar ≠ 0 := by
        change (1 : K) ≠ 0
        exact one_ne_zero_of_two_ne_zero twoNonzero
      calc
        proportion.rotationMatrix =
            cap (Vector.scale proportion.scalar⁻¹ proportion.vector)
              (reciprocalAnchorCapDefined proportion.scalar
                proportion.vector scalarNonzero proportion.normNonzero) :=
          NonNullProportion.rotationMatrix_eq_cap proportion scalarNonzero
        _ = cap axis defined := by
          congr 1
          change Vector.scale (1 : K)⁻¹ axis = axis
          rw [inverse_one (one_ne_zero_of_two_ne_zero twoNonzero),
            Vector.one_scale]
        _ = rotation.matrix := matrixEq.symm
  | halfTurn halfTurnSpread axisNonNull matrixEq =>
      let proportion := ofAxisChart rotation axis
        (RotationAxisChart.halfTurn halfTurnSpread axisNonNull matrixEq)
      calc
        proportion.rotationMatrix = halfTurn axis axisNonNull := by
          exact NonNullProportion.rotationMatrix_eq_halfTurn proportion rfl
        _ = rotation.matrix := matrixEq.symm

/-- The executable inverse representative from Theorem 58.  It consumes the
canonical axis wrapper, so the affine/infinity chart decision and axis
extraction are shared with the spread and reflection-factorization APIs. -/
def ofRotation [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) : NonNullProportion K :=
  let witness := rotationAxisSpreadWitness rotation twoNonzero
  ofAxisChart rotation witness.axis witness.chart

theorem ofRotation_rotationMatrix [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    (ofRotation rotation twoNonzero).rotationMatrix = rotation.matrix :=
  ofAxisChart_rotationMatrix rotation
    (rotationAxisSpreadWitness rotation twoNonzero).axis
    (rotationAxisSpreadWitness rotation twoNonzero).chart twoNonzero

end RotationProportion

namespace NonNullProportion

private theorem eq_of_two_mul_eq_two_mul (twoNonzero : (2 : K) ≠ 0)
    {left right : K} (equal : 2 * left = 2 * right) : left = right := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel (2 : K) twoNonzero
  calc
    left = (2 * (2 : K)⁻¹) * left := by rw [cancel, one_mul]
    _ = (2 * left) * (2 : K)⁻¹ := by ring1
    _ = (2 * right) * (2 : K)⁻¹ := by rw [equal]
    _ = (2 * (2 : K)⁻¹) * right := by ring1
    _ = right := by rw [cancel, one_mul]

/-- The fixed line of a half turn consists exactly of scalar multiples of its
axis; the scalar witness is displayed explicitly. -/
theorem vector_eq_scale_of_halfTurn_fixed (axis other : Vector K)
    (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (fixed : Matrix3.rowMul other (halfTurn axis axisNonNull) = other) :
    other = Vector.scale (Vector.dot other axis / axis.quadrance) axis := by
  have negReflected :
      Vector.neg (Matrix3.rowMul other (reflection axis axisNonNull)) =
        other := by
    simpa only [halfTurn, Matrix3.rowMul_neg] using fixed
  have reflectedNeg :
      Matrix3.rowMul other (reflection axis axisNonNull) =
        Vector.neg other := by
    calc
      Matrix3.rowMul other (reflection axis axisNonNull) =
          Vector.neg
            (Vector.neg
              (Matrix3.rowMul other (reflection axis axisNonNull))) := by
        apply Vector.ext <;> unfold Vector.neg <;> ring1
      _ = Vector.neg other := by rw [negReflected]
  rw [rowMul_reflection] at reflectedNeg
  apply Vector.ext
  · apply eq_of_two_mul_eq_two_mul twoNonzero
    have coordinate := congrArg Vector.t reflectedNeg
    calc
      2 * other.t =
          (other.t -
              (2 * Vector.dot other axis / axis.quadrance) * axis.t) +
            other.t +
            (2 * Vector.dot other axis / axis.quadrance) * axis.t := by ring1
      _ = -other.t + other.t +
          (2 * Vector.dot other axis / axis.quadrance) * axis.t := by
        simpa only [Vector.sub_t, Vector.scale_t, Vector.neg_t] using
          congrArg
            (fun value => value + other.t +
              (2 * Vector.dot other axis / axis.quadrance) * axis.t)
            coordinate
      _ = 2 *
          (Vector.dot other axis / axis.quadrance * axis.t) := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  · apply eq_of_two_mul_eq_two_mul twoNonzero
    have coordinate := congrArg Vector.r reflectedNeg
    calc
      2 * other.r =
          (other.r -
              (2 * Vector.dot other axis / axis.quadrance) * axis.r) +
            other.r +
            (2 * Vector.dot other axis / axis.quadrance) * axis.r := by ring1
      _ = -other.r + other.r +
          (2 * Vector.dot other axis / axis.quadrance) * axis.r := by
        simpa only [Vector.sub_r, Vector.scale_r, Vector.neg_r] using
          congrArg
            (fun value => value + other.r +
              (2 * Vector.dot other axis / axis.quadrance) * axis.r)
            coordinate
      _ = 2 *
          (Vector.dot other axis / axis.quadrance * axis.r) := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1
  · apply eq_of_two_mul_eq_two_mul twoNonzero
    have coordinate := congrArg Vector.s reflectedNeg
    calc
      2 * other.s =
          (other.s -
              (2 * Vector.dot other axis / axis.quadrance) * axis.s) +
            other.s +
            (2 * Vector.dot other axis / axis.quadrance) * axis.s := by ring1
      _ = -other.s + other.s +
          (2 * Vector.dot other axis / axis.quadrance) * axis.s := by
        simpa only [Vector.sub_s, Vector.scale_s, Vector.neg_s] using
          congrArg
            (fun value => value + other.s +
              (2 * Vector.dot other axis / axis.quadrance) * axis.s)
            coordinate
      _ = 2 *
          (Vector.dot other axis / axis.quadrance * axis.s) := by
        simp only [RFAP.ExplicitField.div_eq_mul_inv]
        ring1

/-- Equality of two half turns forces equality of their represented
projective axis lines. -/
theorem vector_scale_of_halfTurn_eq (left right : Vector K)
    (leftNonNull : left.quadrance ≠ 0)
    (rightNonNull : right.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (equal : halfTurn left leftNonNull = halfTurn right rightNonNull) :
    ∃ factor : K, factor ≠ 0 ∧ right = Vector.scale factor left := by
  let factor := Vector.dot right left / left.quadrance
  have rightFixed : Matrix3.rowMul right (halfTurn left leftNonNull) = right := by
    rw [equal, rowMul_self_halfTurn]
  have rightValue : right = Vector.scale factor left :=
    vector_eq_scale_of_halfTurn_fixed left right leftNonNull twoNonzero
      rightFixed
  have factorNonzero : factor ≠ 0 := by
    intro factorZero
    apply rightNonNull
    rw [rightValue, Vector.quadrance_scale, factorZero]
    ring1
  exact ⟨factor, factorNonzero, rightValue⟩

private theorem halfSpread_eq_of_rotationMatrix_eq
    {left right : NonNullProportion K}
    (equal : left.rotationMatrix = right.rotationMatrix) :
    halfSpread left.rotation = halfSpread right.rotation := by
  unfold halfSpread rotation
  exact congrArg (fun matrix => (3 - Matrix3.trace matrix) / 4) equal

private theorem affineEquivalent_of_rotationMatrix_eq
    (left right : NonNullProportion K)
    (leftScalarNonzero : left.scalar ≠ 0)
    (rightScalarNonzero : right.scalar ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (equal : left.rotationMatrix = right.rotationMatrix) :
    left.Equivalent right := by
  have capEqual := equal
  rw [rotationMatrix_eq_cap left leftScalarNonzero,
    rotationMatrix_eq_cap right rightScalarNonzero] at capEqual
  have normalizedEqual :
      Vector.scale left.scalar⁻¹ left.vector =
        Vector.scale right.scalar⁻¹ right.vector :=
    cap_injective twoNonzero _ _ _ _ capEqual
  let factor := right.scalar * left.scalar⁻¹
  have factorNonzero : factor ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero rightScalarNonzero
      (RFAP.ExplicitField.inv_ne_zero leftScalarNonzero)
  have leftCancel := RFAP.ExplicitField.mul_inv_cancel
    left.scalar leftScalarNonzero
  have rightCancel := RFAP.ExplicitField.mul_inv_cancel
    right.scalar rightScalarNonzero
  have reverseLeftCancel : left.scalar⁻¹ * left.scalar = 1 := by
    calc
      left.scalar⁻¹ * left.scalar =
          left.scalar * left.scalar⁻¹ := by ring1
      _ = 1 := leftCancel
  have reverseRightCancel : right.scalar⁻¹ * right.scalar = 1 := by
    calc
      right.scalar⁻¹ * right.scalar =
          right.scalar * right.scalar⁻¹ := by ring1
      _ = 1 := rightCancel
  refine ⟨factor, factorNonzero, ?_⟩
  apply Proportion.ext
  · unfold factor Proportion.scale
    calc
      right.scalar = right.scalar * 1 := by ring1
      _ = right.scalar * (left.scalar⁻¹ * left.scalar) := by
        rw [reverseLeftCancel]
      _ = (right.scalar * left.scalar⁻¹) * left.scalar := by ring1
  · apply Vector.ext
    · have coordinate := congrArg Vector.t normalizedEqual
      simp only [Vector.scale_t] at coordinate
      unfold factor Proportion.scale Vector.scale
      calc
        right.vector.t =
            (right.scalar * right.scalar⁻¹) * right.vector.t := by
          rw [rightCancel, one_mul]
        _ = right.scalar *
            (right.scalar⁻¹ * right.vector.t) := by ring1
        _ = right.scalar *
            (left.scalar⁻¹ * left.vector.t) := by
          rw [← coordinate]
        _ = (right.scalar * left.scalar⁻¹) * left.vector.t := by ring1
    · have coordinate := congrArg Vector.r normalizedEqual
      simp only [Vector.scale_r] at coordinate
      unfold factor Proportion.scale Vector.scale
      calc
        right.vector.r =
            (right.scalar * right.scalar⁻¹) * right.vector.r := by
          rw [rightCancel, one_mul]
        _ = right.scalar *
            (right.scalar⁻¹ * right.vector.r) := by ring1
        _ = right.scalar *
            (left.scalar⁻¹ * left.vector.r) := by
          rw [← coordinate]
        _ = (right.scalar * left.scalar⁻¹) * left.vector.r := by ring1
    · have coordinate := congrArg Vector.s normalizedEqual
      simp only [Vector.scale_s] at coordinate
      unfold factor Proportion.scale Vector.scale
      calc
        right.vector.s =
            (right.scalar * right.scalar⁻¹) * right.vector.s := by
          rw [rightCancel, one_mul]
        _ = right.scalar *
            (right.scalar⁻¹ * right.vector.s) := by ring1
        _ = right.scalar *
            (left.scalar⁻¹ * left.vector.s) := by
          rw [← coordinate]
        _ = (right.scalar * left.scalar⁻¹) * left.vector.s := by ring1

private theorem infinityEquivalent_of_rotationMatrix_eq
    (left right : NonNullProportion K)
    (leftScalarZero : left.scalar = 0)
    (rightScalarZero : right.scalar = 0)
    (twoNonzero : (2 : K) ≠ 0)
    (equal : left.rotationMatrix = right.rotationMatrix) :
    left.Equivalent right := by
  have halfTurnsEqual := equal
  rw [rotationMatrix_eq_halfTurn left leftScalarZero,
    rotationMatrix_eq_halfTurn right rightScalarZero] at halfTurnsEqual
  rcases vector_scale_of_halfTurn_eq left.vector right.vector
      (vector_nonNull_of_scalar_eq_zero left leftScalarZero)
      (vector_nonNull_of_scalar_eq_zero right rightScalarZero)
      twoNonzero halfTurnsEqual with ⟨factor, factorNonzero, vectorValue⟩
  refine ⟨factor, factorNonzero, ?_⟩
  apply Proportion.ext
  · unfold Proportion.scale
    rw [leftScalarZero, rightScalarZero]
    ring1
  · exact vectorValue

/-- Injectivity in Theorem 58, stated exactly at representative level: equal
rotation matrices are equivalent by a displayed nonzero scale. -/
theorem equivalent_of_rotationMatrix_eq [DecidableEq K]
    (left right : NonNullProportion K) (twoNonzero : (2 : K) ≠ 0)
    (equal : left.rotationMatrix = right.rotationMatrix) :
    left.Equivalent right := by
  have spreadEqual := halfSpread_eq_of_rotationMatrix_eq equal
  by_cases leftScalarZero : left.scalar = 0
  · have leftSpreadOne : halfSpread left.rotation = 1 :=
      (halfSpread_rotation_eq_one_iff left twoNonzero).2 leftScalarZero
    have rightSpreadOne : halfSpread right.rotation = 1 := by
      rw [← spreadEqual]
      exact leftSpreadOne
    have rightScalarZero :=
      (halfSpread_rotation_eq_one_iff right twoNonzero).1 rightSpreadOne
    exact infinityEquivalent_of_rotationMatrix_eq left right leftScalarZero
      rightScalarZero twoNonzero equal
  · have rightScalarNonzero : right.scalar ≠ 0 := by
      intro rightScalarZero
      have rightSpreadOne : halfSpread right.rotation = 1 :=
        (halfSpread_rotation_eq_one_iff right twoNonzero).2 rightScalarZero
      have leftSpreadOne : halfSpread left.rotation = 1 := by
        rw [spreadEqual]
        exact rightSpreadOne
      exact leftScalarZero
        ((halfSpread_rotation_eq_one_iff left twoNonzero).1 leftSpreadOne)
    exact affineEquivalent_of_rotationMatrix_eq left right leftScalarZero
      rightScalarNonzero twoNonzero equal

/-- The injective half of Theorem 58 as an iff, paired with scale
invariance. -/
theorem rotationMatrix_eq_iff_equivalent [DecidableEq K]
    (left right : NonNullProportion K) (twoNonzero : (2 : K) ≠ 0) :
    left.rotationMatrix = right.rotationMatrix ↔ left.Equivalent right := by
  constructor
  · exact equivalent_of_rotationMatrix_eq left right twoNonzero
  · intro equivalent
    exact rotationMatrix_respects_equivalent equivalent

end NonNullProportion

/-- The quotient-free group laws asserted by Corollary 60.  Equality of
projective points is `NonNullProportion.Equivalent`; representative
associativity and identity happen to hold as literal equalities. -/
structure ProjectiveProportionGroupLaws (K : Type*) [RFAP.ExplicitField K]
    where
  identity : NonNullProportion K
  inverse : NonNullProportion K → NonNullProportion K
  associative : ∀ (first second third : NonNullProportion K),
    NonNullProportion.mul (NonNullProportion.mul first second) third =
      NonNullProportion.mul first (NonNullProportion.mul second third)
  leftIdentity : ∀ (proportion : NonNullProportion K),
    NonNullProportion.mul identity proportion = proportion
  rightIdentity : ∀ (proportion : NonNullProportion K),
    NonNullProportion.mul proportion identity = proportion
  leftInverse : ∀ (proportion : NonNullProportion K),
    (NonNullProportion.mul (inverse proportion) proportion).Equivalent
      identity
  rightInverse : ∀ (proportion : NonNullProportion K),
    (NonNullProportion.mul proportion (inverse proportion)).Equivalent
      identity
  respectsEquivalent : ∀ {left left' right right' : NonNullProportion K},
    left.Equivalent left' → right.Equivalent right' →
      (NonNullProportion.mul left right).Equivalent
        (NonNullProportion.mul left' right')

/-- Corollary 60's projective group, with inverse given by quaternion
conjugation. -/
def projectiveProportionGroupLaws (twoNonzero : (2 : K) ≠ 0) :
    ProjectiveProportionGroupLaws K := by
  let identity : NonNullProportion K :=
    { scalar := 1
      vector := Vector.zero
      normNonzero := by
        unfold Proportion.norm
        rw [Vector.quadrance_zero]
        simpa only [one_pow, add_zero] using
          one_ne_zero_of_two_ne_zero twoNonzero }
  refine
    { identity := identity
      inverse := NonNullProportion.conjugate
      associative := NonNullProportion.mul_assoc
      leftIdentity := ?_
      rightIdentity := ?_
      leftInverse := ?_
      rightInverse := ?_
      respectsEquivalent := ?_ }
  · intro proportion
    apply NonNullProportion.ext (K := K)
    · exact congrArg Proportion.scalar
        (Proportion.identity_mul proportion.toProportion)
    · exact congrArg Proportion.vector
        (Proportion.identity_mul proportion.toProportion)
  · intro proportion
    apply NonNullProportion.ext (K := K)
    · exact congrArg Proportion.scalar
        (Proportion.mul_identity proportion.toProportion)
    · exact congrArg Proportion.vector
        (Proportion.mul_identity proportion.toProportion)
  · intro proportion
    apply NonNullProportion.equivalent_symm
    refine ⟨proportion.toProportion.norm, proportion.normNonzero, ?_⟩
    change Proportion.mul
        (Proportion.conjugate proportion.toProportion)
        proportion.toProportion =
      Proportion.scale proportion.toProportion.norm Proportion.identity
    exact Proportion.conjugate_mul proportion.toProportion
  · intro proportion
    apply NonNullProportion.equivalent_symm
    refine ⟨proportion.toProportion.norm, proportion.normNonzero, ?_⟩
    change Proportion.mul proportion.toProportion
        (Proportion.conjugate proportion.toProportion) =
      Proportion.scale proportion.toProportion.norm Proportion.identity
    exact Proportion.mul_conjugate proportion.toProportion
  · intro left left' right right' leftEquivalent rightEquivalent
    exact NonNullProportion.mul_respects_equivalent leftEquivalent
      rightEquivalent

/-- A quotient-free executable formulation of Theorem 58's bijection and
multiplicativity. -/
structure ProjectiveRotationTheorem (K : Type*) [RFAP.ExplicitField K]
    [DecidableEq K] where
  representative : Rotation K → NonNullProportion K
  represents : ∀ rotation,
    (representative rotation).rotationMatrix = rotation.matrix
  injective : ∀ (left right : NonNullProportion K),
    left.rotationMatrix = right.rotationMatrix → left.Equivalent right
  multiplicative : ∀ (left right : NonNullProportion K),
    (NonNullProportion.mul left right).rotationMatrix =
      Matrix3.mul left.rotationMatrix right.rotationMatrix

/-- Theorem 58 and Corollary 60, with every representative and certificate
computed by finite coordinate operations. -/
def projectiveRotationTheorem [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) : ProjectiveRotationTheorem K where
  representative := fun rotation =>
    RotationProportion.ofRotation rotation twoNonzero
  represents := fun rotation =>
    RotationProportion.ofRotation_rotationMatrix rotation twoNonzero
  injective := fun left right equal =>
    NonNullProportion.equivalent_of_rotationMatrix_eq left right twoNonzero
      equal
  multiplicative := NonNullProportion.rotationMatrix_mul

end RationalRotations
