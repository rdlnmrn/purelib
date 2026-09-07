import RationalRotations.ProjectiveRotationTheorem

/-!
# Rational rotations, Theorem 61: the quadrance class

Square classes are represented quotient-free.  Equality carries an explicit
nonzero square factor, so invariance and multiplicativity remain executable
finite field calculations.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

/-- A nonzero scalar representing an element of `F×/(F×)²`. -/
@[ext]
structure SquareClassRepresentative (K : Type*) [RFAP.ExplicitField K] where
  value : K
  nonzero : value ≠ 0

namespace SquareClassRepresentative

/-- Equality of square classes by a displayed nonzero square factor. -/
def Equivalent (left right : SquareClassRepresentative K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧ right.value = factor ^ 2 * left.value

theorem one_ne_zero (representative : SquareClassRepresentative K) :
    (1 : K) ≠ 0 := by
  intro oneZero
  apply representative.nonzero
  calc
    representative.value = representative.value * 1 := by rw [mul_one]
    _ = representative.value * 0 := by rw [oneZero]
    _ = 0 := by rw [mul_zero]

theorem equivalent_refl (representative : SquareClassRepresentative K) :
    representative.Equivalent representative := by
  refine ⟨1, representative.one_ne_zero, ?_⟩
  ring1

theorem equivalent_symm {left right : SquareClassRepresentative K}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  have reverseCancel : factor⁻¹ * factor = 1 := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := cancel
  refine ⟨factor⁻¹, RFAP.ExplicitField.inv_ne_zero factorNonzero, ?_⟩
  calc
    left.value = (factor⁻¹ * factor) ^ 2 * left.value := by
      rw [reverseCancel]
      ring1
    _ = factor⁻¹ ^ 2 * (factor ^ 2 * left.value) := by ring1
    _ = factor⁻¹ ^ 2 * right.value := by rw [rightValue]

theorem equivalent_trans {first second third : SquareClassRepresentative K}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases firstSecond with ⟨firstFactor, firstFactorNonzero, secondValue⟩
  rcases secondThird with ⟨secondFactor, secondFactorNonzero, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    RFAP.ExplicitField.mul_ne_zero secondFactorNonzero firstFactorNonzero, ?_⟩
  calc
    third.value = secondFactor ^ 2 * second.value := thirdValue
    _ = secondFactor ^ 2 * (firstFactor ^ 2 * first.value) := by
      rw [secondValue]
    _ = (secondFactor * firstFactor) ^ 2 * first.value := by ring1

/-- Multiplication of displayed square-class representatives. -/
def mul (left right : SquareClassRepresentative K) :
    SquareClassRepresentative K where
  value := left.value * right.value
  nonzero := RFAP.ExplicitField.mul_ne_zero left.nonzero right.nonzero

theorem mul_respects_equivalent
    {left left' right right' : SquareClassRepresentative K}
    (leftEquivalent : left.Equivalent left')
    (rightEquivalent : right.Equivalent right') :
    (mul left right).Equivalent (mul left' right') := by
  rcases leftEquivalent with ⟨leftFactor, leftFactorNonzero, leftValue⟩
  rcases rightEquivalent with ⟨rightFactor, rightFactorNonzero, rightValue⟩
  refine ⟨leftFactor * rightFactor,
    RFAP.ExplicitField.mul_ne_zero leftFactorNonzero rightFactorNonzero, ?_⟩
  change left'.value * right'.value =
    (leftFactor * rightFactor) ^ 2 * (left.value * right.value)
  rw [leftValue, rightValue]
  ring1

end SquareClassRepresentative

namespace NonNullProportion

/-- The square-class representative carried by a non-null proportion. -/
def quadranceClass (proportion : NonNullProportion K) :
    SquareClassRepresentative K where
  value := proportion.toProportion.norm
  nonzero := proportion.normNonzero

/-- The quadrance class is independent of the homogeneous representative. -/
theorem quadranceClass_respects_equivalent
    {left right : NonNullProportion K} (equivalent : left.Equivalent right) :
    left.quadranceClass.Equivalent right.quadranceClass := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change right.toProportion.norm = factor ^ 2 * left.toProportion.norm
  rw [rightValue, Proportion.norm_scale]

/-- Theorem 61's homomorphism law at representative level. -/
theorem quadranceClass_mul (left right : NonNullProportion K) :
    (mul left right).quadranceClass =
      SquareClassRepresentative.mul left.quadranceClass
        right.quadranceClass := by
  apply SquareClassRepresentative.ext
  exact Proportion.norm_mul left.toProportion right.toProportion

private theorem scalarSquareNonzero (proportion : NonNullProportion K)
    (scalarNonzero : proportion.scalar ≠ 0) : proportion.scalar ^ 2 ≠ 0 := by
  simpa only [pow_two] using
    RFAP.ExplicitField.mul_ne_zero scalarNonzero scalarNonzero

/-- The affine closed form in Theorem 61:
`[N(x,v)] = [1-halfSpread]`. -/
theorem quadranceClass_equivalent_one_sub_halfSpread
    (proportion : NonNullProportion K)
    (scalarNonzero : proportion.scalar ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    proportion.quadranceClass.Equivalent
      { value := 1 - halfSpread proportion.rotation
        nonzero := by
          rw [one_sub_halfSpread_rotation proportion twoNonzero]
          exact RFAP.ExplicitField.div_ne_zero
            (scalarSquareNonzero proportion scalarNonzero)
            proportion.normNonzero } := by
  let factor := proportion.scalar / proportion.toProportion.norm
  have factorNonzero : factor ≠ 0 :=
    RFAP.ExplicitField.div_ne_zero scalarNonzero proportion.normNonzero
  have normCancel := RFAP.ExplicitField.mul_inv_cancel
    proportion.toProportion.norm proportion.normNonzero
  refine ⟨factor, factorNonzero, ?_⟩
  change 1 - halfSpread proportion.rotation =
    factor ^ 2 * proportion.toProportion.norm
  rw [one_sub_halfSpread_rotation proportion twoNonzero]
  unfold factor
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    proportion.scalar ^ 2 * proportion.toProportion.norm⁻¹ =
        (proportion.scalar * proportion.toProportion.norm⁻¹) ^ 2 *
          proportion.toProportion.norm := by
      symm
      calc
        (proportion.scalar * proportion.toProportion.norm⁻¹) ^ 2 *
            proportion.toProportion.norm =
          proportion.scalar ^ 2 * proportion.toProportion.norm⁻¹ *
            (proportion.toProportion.norm⁻¹ *
              proportion.toProportion.norm) := by ring1
        _ = proportion.scalar ^ 2 * proportion.toProportion.norm⁻¹ := by
          rw [show proportion.toProportion.norm⁻¹ *
              proportion.toProportion.norm = 1 by
            calc
              proportion.toProportion.norm⁻¹ *
                  proportion.toProportion.norm =
                proportion.toProportion.norm *
                  proportion.toProportion.norm⁻¹ := by ring1
              _ = 1 := normCancel,
            mul_one]

/-- The infinity closed form in Theorem 61: `[N(0,v)]=[Q(v)]`. -/
theorem quadranceClass_at_infinity (proportion : NonNullProportion K)
    (scalarZero : proportion.scalar = 0) :
    proportion.quadranceClass.value = proportion.vector.quadrance := by
  change proportion.toProportion.norm = proportion.vector.quadrance
  unfold Proportion.norm
  rw [scalarZero]
  ring1

end NonNullProportion

namespace RotationQuadranceClass

/-- Theorem 61's invariant on rotations, computed from the executable inverse
representative of Theorem 58. -/
def ofRotation [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) : SquareClassRepresentative K :=
  (RotationProportion.ofRotation rotation twoNonzero).quadranceClass

/-- Theorem 61's homomorphism law on stored rotations. -/
theorem of_rotationProduct [DecidableEq K]
    (left right : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    (ofRotation (rotationProduct left right) twoNonzero).Equivalent
      (SquareClassRepresentative.mul
        (ofRotation left twoNonzero) (ofRotation right twoNonzero)) := by
  let leftProportion := RotationProportion.ofRotation left twoNonzero
  let rightProportion := RotationProportion.ofRotation right twoNonzero
  let productProportion := NonNullProportion.mul leftProportion rightProportion
  let canonicalProduct :=
    RotationProportion.ofRotation (rotationProduct left right) twoNonzero
  have matrixEqual : canonicalProduct.rotationMatrix =
      productProportion.rotationMatrix := by
    calc
      canonicalProduct.rotationMatrix =
          (rotationProduct left right).matrix :=
        RotationProportion.ofRotation_rotationMatrix
          (rotationProduct left right) twoNonzero
      _ = Matrix3.mul left.matrix right.matrix := rfl
      _ = Matrix3.mul leftProportion.rotationMatrix
          rightProportion.rotationMatrix := by
        rw [RotationProportion.ofRotation_rotationMatrix left twoNonzero,
          RotationProportion.ofRotation_rotationMatrix right twoNonzero]
      _ = productProportion.rotationMatrix :=
        (NonNullProportion.rotationMatrix_mul leftProportion
          rightProportion).symm
  have equivalent := NonNullProportion.equivalent_of_rotationMatrix_eq
    canonicalProduct productProportion twoNonzero matrixEqual
  have classEquivalent :=
    NonNullProportion.quadranceClass_respects_equivalent equivalent
  change canonicalProduct.quadranceClass.Equivalent
    (SquareClassRepresentative.mul leftProportion.quadranceClass
      rightProportion.quadranceClass)
  exact SquareClassRepresentative.equivalent_trans classEquivalent
    (by
      rw [NonNullProportion.quadranceClass_mul]
      exact SquareClassRepresentative.equivalent_refl _)

end RotationQuadranceClass

/-- Finite certificate consumed by the constructive core of Theorem 62.  It
retains the four square roots instead of invoking an unbounded existence
theorem inside the paper-facing dependency graph. -/
structure FourSquareRepresentation (value : K) where
  scalar : K
  t : K
  r : K
  s : K
  equation : scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 = value

/-- A supplied four-square certificate realizes its nonzero square class by
an executable projective rotation. -/
def FourSquareRepresentation.proportion
    (target : SquareClassRepresentative K)
    (representation : FourSquareRepresentation target.value) :
    NonNullProportion K where
  scalar := representation.scalar
  vector := ⟨representation.t, representation.r, representation.s⟩
  normNonzero := by
    rw [show Proportion.norm
        ⟨representation.scalar,
          (⟨representation.t, representation.r, representation.s⟩ :
            Vector K)⟩ = target.value by
      unfold Proportion.norm Vector.quadrance Vector.dot
      change representation.scalar ^ 2 +
          (representation.t * representation.t +
            representation.r * representation.r +
            representation.s * representation.s) = target.value
      calc
        representation.scalar ^ 2 +
              (representation.t * representation.t +
                representation.r * representation.r +
                representation.s * representation.s) =
            representation.scalar ^ 2 + representation.t ^ 2 +
              representation.r ^ 2 + representation.s ^ 2 := by ring1
        _ = target.value := representation.equation]
    exact target.nonzero

theorem FourSquareRepresentation.realizes_quadranceClass
    (target : SquareClassRepresentative K)
    (representation : FourSquareRepresentation target.value) :
    (representation.proportion target).quadranceClass.value = target.value := by
  change Proportion.norm
      ⟨representation.scalar,
        (⟨representation.t, representation.r, representation.s⟩ : Vector K)⟩ =
    target.value
  unfold Proportion.norm Vector.quadrance Vector.dot
  change representation.scalar ^ 2 +
      (representation.t * representation.t +
        representation.r * representation.r +
        representation.s * representation.s) = target.value
  calc
    representation.scalar ^ 2 +
          (representation.t * representation.t +
            representation.r * representation.r +
            representation.s * representation.s) =
        representation.scalar ^ 2 + representation.t ^ 2 +
          representation.r ^ 2 + representation.s ^ 2 := by ring1
    _ = target.value := representation.equation

end RationalRotations
