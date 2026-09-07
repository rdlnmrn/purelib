import RationalRotations.Proportions

/-!
# Rational rotations, section 11: the projective rotation map

The map is proved special orthogonal and multiplicative by explicit
denominator-cleared polynomial identities.  In particular, no density of
rational points, root counting, infinite carrier, or polynomial identity
transfer is used in place of the paper's Lemma 59.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- The homogeneous quadratic numerator of Definition 55. -/
def proportionRotationNumerator (proportion : Proportion K) : Matrix3 K :=
  ⟨proportion.scalar ^ 2 + proportion.vector.t ^ 2 -
      proportion.vector.r ^ 2 - proportion.vector.s ^ 2,
    2 * (proportion.scalar * proportion.vector.s +
      proportion.vector.r * proportion.vector.t),
    2 * (-proportion.scalar * proportion.vector.r +
      proportion.vector.s * proportion.vector.t),
    2 * (-proportion.scalar * proportion.vector.s +
      proportion.vector.r * proportion.vector.t),
    proportion.scalar ^ 2 - proportion.vector.t ^ 2 +
      proportion.vector.r ^ 2 - proportion.vector.s ^ 2,
    2 * (proportion.scalar * proportion.vector.t +
      proportion.vector.r * proportion.vector.s),
    2 * (proportion.scalar * proportion.vector.r +
      proportion.vector.s * proportion.vector.t),
    2 * (-proportion.scalar * proportion.vector.t +
      proportion.vector.r * proportion.vector.s),
    proportion.scalar ^ 2 - proportion.vector.t ^ 2 -
      proportion.vector.r ^ 2 + proportion.vector.s ^ 2⟩

theorem proportionRotationNumerator_scale (factor : K)
    (proportion : Proportion K) :
    proportionRotationNumerator (Proportion.scale factor proportion) =
      Matrix3.scale (factor ^ 2)
        (proportionRotationNumerator proportion) := by
  apply Matrix3.ext <;> unfold proportionRotationNumerator Proportion.scale
    Matrix3.scale Vector.scale <;> ring1

/-- The denominator-cleared multiplicativity identity behind Theorem 58. -/
theorem proportionRotationNumerator_mul (left right : Proportion K) :
    Matrix3.mul (proportionRotationNumerator left)
        (proportionRotationNumerator right) =
      proportionRotationNumerator (Proportion.mul left right) := by
  apply Matrix3.ext <;> unfold proportionRotationNumerator Proportion.mul
    Matrix3.mul Vector.dot Vector.sub Vector.add Vector.scale Vector.cross <;>
    ring1

theorem proportionRotationNumerator_mul_transpose
    (proportion : Proportion K) :
    Matrix3.mul (proportionRotationNumerator proportion)
        (Matrix3.transpose (proportionRotationNumerator proportion)) =
      Matrix3.scale (proportion.norm ^ 2) Matrix3.identity := by
  apply Matrix3.ext <;> unfold proportionRotationNumerator Proportion.norm
    Matrix3.mul Matrix3.transpose Matrix3.scale Matrix3.identity
    Vector.quadrance Vector.dot <;> ring1

theorem determinant_proportionRotationNumerator
    (proportion : Proportion K) :
    Matrix3.determinant (proportionRotationNumerator proportion) =
      proportion.norm ^ 3 := by
  unfold proportionRotationNumerator Proportion.norm Matrix3.determinant
    Vector.quadrance Vector.dot
  ring1

theorem trace_proportionRotationNumerator (proportion : Proportion K) :
    Matrix3.trace (proportionRotationNumerator proportion) =
      3 * proportion.scalar ^ 2 - proportion.vector.quadrance := by
  unfold proportionRotationNumerator Matrix3.trace
    Vector.quadrance Vector.dot
  ring1

namespace NonNullProportion

/-- Definition 55, stored by the same executable quadratic formula as the
reciprocal-anchor path in Section 10. -/
def rotationMatrix (proportion : NonNullProportion K) : Matrix3 K :=
  reciprocalAnchorPath proportion.scalar proportion.vector
    proportion.normNonzero

/-- Definition 55 in homogeneous coordinate form. -/
theorem rotationMatrix_eq_scaled_numerator
    (proportion : NonNullProportion K) :
    proportion.rotationMatrix =
      Matrix3.scale proportion.toProportion.norm⁻¹
        (proportionRotationNumerator proportion.toProportion) := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  have expandedCancel :
      (proportion.scalar ^ 2 +
          (proportion.vector.t * proportion.vector.t +
            proportion.vector.r * proportion.vector.r +
            proportion.vector.s * proportion.vector.s)) *
        (proportion.scalar ^ 2 +
          (proportion.vector.t * proportion.vector.t +
            proportion.vector.r * proportion.vector.r +
            proportion.vector.s * proportion.vector.s))⁻¹ = 1 := by
    simpa only [Proportion.norm, Vector.quadrance, Vector.dot] using cancel
  apply Matrix3.ext <;> unfold rotationMatrix reciprocalAnchorPath
    reciprocalAnchorPathDenominator proportionRotationNumerator
    Proportion.norm Matrix3.add Matrix3.scale Matrix3.identity Matrix3.mul
    anchor Vector.quadrance Vector.dot <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;>
    (try rw [← expandedCancel]) <;> ring1

private theorem inverse_product {left right : K}
    (leftNonzero : left ≠ 0) (rightNonzero : right ≠ 0) :
    (left * right)⁻¹ = left⁻¹ * right⁻¹ := by
  have leftCancel := RFAP.ExplicitField.mul_inv_cancel left leftNonzero
  have rightCancel := RFAP.ExplicitField.mul_inv_cancel right rightNonzero
  have productNonzero :=
    RFAP.ExplicitField.mul_ne_zero leftNonzero rightNonzero
  have productCancel := RFAP.ExplicitField.mul_inv_cancel
    (left * right) productNonzero
  calc
    (left * right)⁻¹ = (left * right)⁻¹ * 1 := by rw [mul_one]
    _ = (left * right)⁻¹ *
        ((left * right) * (left⁻¹ * right⁻¹)) := by
      rw [show (left * right) * (left⁻¹ * right⁻¹) = 1 by
        calc
          (left * right) * (left⁻¹ * right⁻¹) =
              (left * left⁻¹) * (right * right⁻¹) := by ring1
          _ = 1 := by rw [leftCancel, rightCancel, one_mul]]
    _ = ((left * right) * (left * right)⁻¹) *
        (left⁻¹ * right⁻¹) := by ring1
    _ = left⁻¹ * right⁻¹ := by rw [productCancel, one_mul]

theorem rotationMatrix_isOrthogonal (proportion : NonNullProportion K) :
    proportion.rotationMatrix.IsOrthogonal := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  have reverseCancel :
      proportion.toProportion.norm⁻¹ * proportion.toProportion.norm = 1 := by
    calc
      proportion.toProportion.norm⁻¹ * proportion.toProportion.norm =
          proportion.toProportion.norm * proportion.toProportion.norm⁻¹ := by
        ring1
      _ = 1 := cancel
  have squareCancel :
      proportion.toProportion.norm⁻¹ ^ 2 *
          proportion.toProportion.norm ^ 2 = 1 := by
    calc
      proportion.toProportion.norm⁻¹ ^ 2 *
          proportion.toProportion.norm ^ 2 =
        (proportion.toProportion.norm⁻¹ *
          proportion.toProportion.norm) ^ 2 := by ring1
      _ = 1 := by rw [reverseCancel]; ring1
  unfold Matrix3.IsOrthogonal
  rw [rotationMatrix_eq_scaled_numerator, Matrix3.transpose_scale,
    Matrix3.mul_scale_left, Matrix3.mul_scale_right, Matrix3.scale_scale,
    proportionRotationNumerator_mul_transpose, Matrix3.scale_scale,
    show proportion.toProportion.norm⁻¹ *
        proportion.toProportion.norm⁻¹ =
      proportion.toProportion.norm⁻¹ ^ 2 by ring1,
    squareCancel, Matrix3.one_scale]

theorem determinant_rotationMatrix (proportion : NonNullProportion K) :
    Matrix3.determinant proportion.rotationMatrix = 1 := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  have reverseCancel :
      proportion.toProportion.norm⁻¹ * proportion.toProportion.norm = 1 := by
    calc
      proportion.toProportion.norm⁻¹ * proportion.toProportion.norm =
          proportion.toProportion.norm * proportion.toProportion.norm⁻¹ := by
        ring1
      _ = 1 := cancel
  have cubeCancel :
      proportion.toProportion.norm⁻¹ ^ 3 *
          proportion.toProportion.norm ^ 3 = 1 := by
    calc
      proportion.toProportion.norm⁻¹ ^ 3 *
          proportion.toProportion.norm ^ 3 =
        (proportion.toProportion.norm⁻¹ *
          proportion.toProportion.norm) ^ 3 := by ring1
      _ = 1 := by rw [reverseCancel]; ring1
  rw [rotationMatrix_eq_scaled_numerator, Matrix3.determinant_scale,
    determinant_proportionRotationNumerator, cubeCancel]

/-- Definition 55 bundled as an executable member of `SO(3)`. -/
def rotation (proportion : NonNullProportion K) : Rotation K where
  matrix := proportion.rotationMatrix
  orthogonal := proportion.rotationMatrix_isOrthogonal
  determinantOne := proportion.determinant_rotationMatrix

/-- Definition 55 is invariant under nonzero homogeneous rescaling. -/
theorem rotationMatrix_scale (factor : K) (factorNonzero : factor ≠ 0)
    (proportion : NonNullProportion K) :
    (scale factor factorNonzero proportion).rotationMatrix =
      proportion.rotationMatrix := by
  have factorSquareNonzero : factor ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero factorNonzero factorNonzero
  have factorSquareCancel := RFAP.ExplicitField.mul_inv_cancel
    (factor ^ 2) factorSquareNonzero
  have reverseFactorSquareCancel : (factor ^ 2)⁻¹ * factor ^ 2 = 1 := by
    calc
      (factor ^ 2)⁻¹ * factor ^ 2 =
          factor ^ 2 * (factor ^ 2)⁻¹ := by ring1
      _ = 1 := factorSquareCancel
  have coefficient :
      (factor ^ 2 * proportion.toProportion.norm)⁻¹ * factor ^ 2 =
        proportion.toProportion.norm⁻¹ := by
    rw [inverse_product factorSquareNonzero proportion.normNonzero]
    calc
      ((factor ^ 2)⁻¹ * proportion.toProportion.norm⁻¹) *
          factor ^ 2 =
        ((factor ^ 2)⁻¹ * factor ^ 2) *
          proportion.toProportion.norm⁻¹ := by ring1
      _ = proportion.toProportion.norm⁻¹ := by
        rw [reverseFactorSquareCancel, one_mul]
  rw [rotationMatrix_eq_scaled_numerator,
    rotationMatrix_eq_scaled_numerator]
  change Matrix3.scale
      (Proportion.norm (Proportion.scale factor proportion.toProportion))⁻¹
      (proportionRotationNumerator
        (Proportion.scale factor proportion.toProportion)) =
    Matrix3.scale proportion.toProportion.norm⁻¹
      (proportionRotationNumerator proportion.toProportion)
  rw [
    Proportion.norm_scale, proportionRotationNumerator_scale,
    Matrix3.scale_scale, coefficient]

theorem rotationMatrix_respects_equivalent
    {left right : NonNullProportion K} (equivalent : left.Equivalent right) :
    left.rotationMatrix = right.rotationMatrix := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  have rightScaled : right = scale factor factorNonzero left := by
    apply NonNullProportion.ext (K := K)
    · exact congrArg Proportion.scalar rightValue
    · exact congrArg Proportion.vector rightValue
  rw [rightScaled, rotationMatrix_scale]

/-- On the affine chart, Definition 55 is the cap of the normalized anchor. -/
theorem rotationMatrix_eq_cap (proportion : NonNullProportion K)
    (scalarNonzero : proportion.scalar ≠ 0) :
    proportion.rotationMatrix =
      cap (Vector.scale proportion.scalar⁻¹ proportion.vector)
        (reciprocalAnchorCapDefined proportion.scalar proportion.vector
          scalarNonzero proportion.normNonzero) :=
  reciprocalAnchorPath_eq_cap proportion.scalar proportion.vector
    scalarNonzero proportion.normNonzero

theorem vector_nonNull_of_scalar_eq_zero
    (proportion : NonNullProportion K) (scalarZero : proportion.scalar = 0) :
    proportion.vector.quadrance ≠ 0 := by
  intro vectorNull
  apply proportion.normNonzero
  unfold Proportion.norm
  rw [scalarZero, vectorNull]
  ring1

/-- At infinity, Definition 55 is exactly the half turn about the represented
non-null line. -/
theorem rotationMatrix_eq_halfTurn (proportion : NonNullProportion K)
    (scalarZero : proportion.scalar = 0) :
    proportion.rotationMatrix =
      halfTurn proportion.vector
        (vector_nonNull_of_scalar_eq_zero proportion scalarZero) := by
  let vectorNonNull := vector_nonNull_of_scalar_eq_zero proportion scalarZero
  simpa only [rotationMatrix, scalarZero] using
    reciprocalAnchorPath_zero proportion.vector vectorNonNull

theorem trace_rotationMatrix (proportion : NonNullProportion K) :
    Matrix3.trace proportion.rotationMatrix =
      (3 * proportion.scalar ^ 2 - proportion.vector.quadrance) /
        proportion.toProportion.norm := by
  rw [rotationMatrix_eq_scaled_numerator, Matrix3.trace_scale,
    trace_proportionRotationNumerator]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

private theorem four_ne_zero (twoNonzero : (2 : K) ≠ 0) : (4 : K) ≠ 0 := by
  have productNonzero :=
    RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero

/-- The half spread of a projective rotation is `Q(v)/N(x,v)`. -/
theorem halfSpread_rotation (proportion : NonNullProportion K)
    (twoNonzero : (2 : K) ≠ 0) :
    halfSpread proportion.rotation =
      proportion.vector.quadrance / proportion.toProportion.norm := by
  have normCancel := RFAP.ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  have fourCancel := RFAP.ExplicitField.mul_inv_cancel (4 : K)
    (four_ne_zero twoNonzero)
  unfold halfSpread rotation
  rw [trace_rotationMatrix]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    (3 - (3 * proportion.scalar ^ 2 - proportion.vector.quadrance) *
        proportion.toProportion.norm⁻¹) * (4 : K)⁻¹ =
      (3 * (proportion.toProportion.norm *
          proportion.toProportion.norm⁻¹) -
        (3 * proportion.scalar ^ 2 - proportion.vector.quadrance) *
          proportion.toProportion.norm⁻¹) * (4 : K)⁻¹ := by
        rw [normCancel]
        ring1
    _ =
      (4 * proportion.vector.quadrance *
        proportion.toProportion.norm⁻¹) * (4 : K)⁻¹ := by
        unfold Proportion.norm
        ring1
    _ = proportion.vector.quadrance *
        proportion.toProportion.norm⁻¹ * (4 * (4 : K)⁻¹) := by
      ring1
    _ = proportion.vector.quadrance *
        proportion.toProportion.norm⁻¹ := by rw [fourCancel, mul_one]

theorem one_sub_halfSpread_rotation (proportion : NonNullProportion K)
    (twoNonzero : (2 : K) ≠ 0) :
    1 - halfSpread proportion.rotation =
      proportion.scalar ^ 2 / proportion.toProportion.norm := by
  have normCancel := RFAP.ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  rw [halfSpread_rotation proportion twoNonzero]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    1 - proportion.vector.quadrance * proportion.toProportion.norm⁻¹ =
        proportion.toProportion.norm * proportion.toProportion.norm⁻¹ -
          proportion.vector.quadrance * proportion.toProportion.norm⁻¹ := by
      rw [normCancel]
    _ = proportion.scalar ^ 2 * proportion.toProportion.norm⁻¹ := by
      unfold Proportion.norm
      ring1

/-- The projective half-turn locus is exactly the hyperplane `x=0`. -/
theorem halfSpread_rotation_eq_one_iff [DecidableEq K]
    (proportion : NonNullProportion K) (twoNonzero : (2 : K) ≠ 0) :
    halfSpread proportion.rotation = 1 ↔ proportion.scalar = 0 := by
  constructor
  · intro spreadOne
    by_cases scalarZero : proportion.scalar = 0
    · exact scalarZero
    · have scalarSquareNonzero : proportion.scalar ^ 2 ≠ 0 := by
        simpa only [pow_two] using
          RFAP.ExplicitField.mul_ne_zero scalarZero scalarZero
      have quotientNonzero := RFAP.ExplicitField.div_ne_zero
        scalarSquareNonzero proportion.normNonzero
      apply (quotientNonzero ?_).elim
      rw [← one_sub_halfSpread_rotation proportion twoNonzero, spreadOne]
      ring1
  · intro scalarZero
    have complement := one_sub_halfSpread_rotation proportion twoNonzero
    rw [scalarZero, show (0 : K) ^ 2 = 0 by ring1,
      RFAP.ExplicitField.zero_div] at complement
    calc
      halfSpread proportion.rotation =
          1 - (1 - halfSpread proportion.rotation) := by ring1
      _ = 1 := by rw [complement]; ring1

/-- Theorem 58's multiplicativity, established directly over the supplied
field rather than transferred from rational points. -/
theorem rotationMatrix_mul (left right : NonNullProportion K) :
    (mul left right).rotationMatrix =
      Matrix3.mul left.rotationMatrix right.rotationMatrix := by
  rw [rotationMatrix_eq_scaled_numerator,
    rotationMatrix_eq_scaled_numerator,
    rotationMatrix_eq_scaled_numerator,
    mul_norm, inverse_product left.normNonzero right.normNonzero,
    Matrix3.mul_scale_left, Matrix3.mul_scale_right, Matrix3.scale_scale,
    proportionRotationNumerator_mul]
  rfl

end NonNullProportion

end RationalRotations
