import RationalRotations.QuadranceClasses

/-!
# Rational rotations, Corollary 63 and Example 64

The finite obstruction is the existence of a norm-one representative in a
projective class.  The claims that the rational image or its index is
infinite are not used here; the two displayed nonsquare obstructions are
proved from canonical reduced fractions.
-/

namespace RationalRotations

variable {K : Type*} [RFAP.ExplicitField K]

namespace NonNullProportion

/-- A projective proportion admits a unit-quaternion representative. -/
def HasUnitRepresentative (proportion : NonNullProportion K) : Prop :=
  ∃ factor : K, factor ≠ 0 ∧
    (Proportion.scale factor proportion.toProportion).norm = 1

/-- Executable data witnessing a norm-one representative, separated from
the proposition so finite algorithms can retain the normalizing scalar. -/
structure UnitRepresentativeCertificate
    (proportion : NonNullProportion K) where
  factor : K
  factorNonzero : factor ≠ 0
  normOne : (Proportion.scale factor proportion.toProportion).norm = 1

theorem UnitRepresentativeCertificate.hasUnitRepresentative
    {proportion : NonNullProportion K}
    (certificate : UnitRepresentativeCertificate proportion) :
    proportion.HasUnitRepresentative :=
  ⟨certificate.factor, certificate.factorNonzero, certificate.normOne⟩

/-- The trivial square class. -/
def unitSquareClass (proportion : NonNullProportion K) :
    SquareClassRepresentative K where
  value := 1
  nonzero := proportion.one_ne_zero

/-- Corollary 63's exact finite obstruction criterion. -/
theorem hasUnitRepresentative_iff_quadranceClass_trivial
    (proportion : NonNullProportion K) :
    proportion.HasUnitRepresentative ↔
      proportion.quadranceClass.Equivalent proportion.unitSquareClass := by
  constructor
  · rintro ⟨factor, factorNonzero, unitNorm⟩
    refine ⟨factor, factorNonzero, ?_⟩
    change (1 : K) = factor ^ 2 * proportion.toProportion.norm
    rw [← Proportion.norm_scale, unitNorm]
  · rintro ⟨factor, factorNonzero, unitValue⟩
    refine ⟨factor, factorNonzero, ?_⟩
    rw [Proportion.norm_scale]
    exact unitValue.symm

theorem hasUnitRepresentative_respects_equivalent
    {left right : NonNullProportion K} (equivalent : left.Equivalent right) :
    left.HasUnitRepresentative ↔ right.HasUnitRepresentative := by
  constructor
  · intro leftUnit
    have leftTrivial :=
      (hasUnitRepresentative_iff_quadranceClass_trivial left).1 leftUnit
    have classEquivalent := quadranceClass_respects_equivalent equivalent
    have rightToLeft := SquareClassRepresentative.equivalent_symm classEquivalent
    have rightTrivial := SquareClassRepresentative.equivalent_trans rightToLeft
      leftTrivial
    exact (hasUnitRepresentative_iff_quadranceClass_trivial right).2
      (SquareClassRepresentative.equivalent_trans rightTrivial (by
        refine ⟨1, right.one_ne_zero, ?_⟩
        change (1 : K) = 1 ^ 2 * 1
        ring1))
  · intro rightUnit
    have rightTrivial :=
      (hasUnitRepresentative_iff_quadranceClass_trivial right).1 rightUnit
    have classEquivalent := quadranceClass_respects_equivalent equivalent
    have leftTrivial := SquareClassRepresentative.equivalent_trans
      classEquivalent rightTrivial
    exact (hasUnitRepresentative_iff_quadranceClass_trivial left).2
      (SquareClassRepresentative.equivalent_trans leftTrivial (by
        refine ⟨1, left.one_ne_zero, ?_⟩
        change (1 : K) = 1 ^ 2 * 1
        ring1))

/-- Two displayed projective proportions lie in the same coset of the
unit-quaternion kernel when their relative product is in that kernel. -/
def InSameUnitKernelCoset (left right : NonNullProportion K) : Prop :=
  HasUnitRepresentative (mul (conjugate left) right)

/-- Equality modulo the unit-quaternion kernel is exactly equality of the
two quadrance classes. -/
theorem inSameUnitKernelCoset_iff_quadranceClass_equivalent
    (left right : NonNullProportion K) :
    InSameUnitKernelCoset left right ↔
      left.quadranceClass.Equivalent right.quadranceClass := by
  have conjugateNorm :
      (conjugate left).toProportion.norm = left.toProportion.norm :=
    Proportion.norm_conjugate left.toProportion
  constructor
  · rintro ⟨unitFactor, unitFactorNonzero, unitNorm⟩
    have relativeNorm :
        unitFactor ^ 2 *
            (left.toProportion.norm * right.toProportion.norm) = 1 := by
      change Proportion.norm
          (Proportion.scale unitFactor
            (mul (conjugate left) right).toProportion) = 1 at unitNorm
      rw [Proportion.norm_scale, mul_norm, conjugateNorm] at unitNorm
      exact unitNorm
    refine ⟨unitFactor * right.toProportion.norm,
      RFAP.ExplicitField.mul_ne_zero unitFactorNonzero right.normNonzero, ?_⟩
    change right.toProportion.norm =
      (unitFactor * right.toProportion.norm) ^ 2 *
        left.toProportion.norm
    calc
      right.toProportion.norm =
          1 * right.toProportion.norm := by ring1
      _ = (unitFactor ^ 2 *
            (left.toProportion.norm * right.toProportion.norm)) *
          right.toProportion.norm := by rw [relativeNorm]
      _ = (unitFactor * right.toProportion.norm) ^ 2 *
          left.toProportion.norm := by ring1
  · rintro ⟨classFactor, classFactorNonzero, classEquation⟩
    let normalizer := classFactor * left.toProportion.norm
    have normalizerNonzero : normalizer ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero classFactorNonzero left.normNonzero
    refine ⟨normalizer⁻¹,
      RFAP.ExplicitField.inv_ne_zero normalizerNonzero, ?_⟩
    rw [Proportion.norm_scale, mul_norm, conjugateNorm]
    change right.toProportion.norm =
      classFactor ^ 2 * left.toProportion.norm at classEquation
    have normalizerCancel :=
      RFAP.ExplicitField.mul_inv_cancel normalizer normalizerNonzero
    calc
      normalizer⁻¹ ^ 2 *
          (left.toProportion.norm * right.toProportion.norm) =
        normalizer⁻¹ ^ 2 * normalizer ^ 2 := by
          rw [classEquation]
          unfold normalizer
          ring1
      _ = (normalizer * normalizer⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [normalizerCancel]; ring1

end NonNullProportion

namespace RotationQuadranceClass

/-- A stored rotation arises from a norm-one quaternion when one of its
non-null projective representatives has norm one. -/
def HasUnitQuaternion [DecidableEq K] (rotation : Rotation K)
    (twoNonzero : (2 : K) ≠ 0) : Prop :=
  (RotationProportion.ofRotation rotation twoNonzero).HasUnitRepresentative

theorem hasUnitQuaternion_iff_trivial [DecidableEq K]
    (rotation : Rotation K) (twoNonzero : (2 : K) ≠ 0) :
    HasUnitQuaternion rotation twoNonzero ↔
      (ofRotation rotation twoNonzero).Equivalent
        (RotationProportion.ofRotation rotation twoNonzero).unitSquareClass :=
  NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial _

end RotationQuadranceClass

namespace ExampleSixtyFour

abbrev Scalar := RFAP.ConstructiveFraction.Rational

def axis : Vector Scalar := ⟨1, 0, 0⟩

private theorem natCast_ne_zero {value : Nat} (nonzero : value ≠ 0) :
    (value : Scalar) ≠ 0 := by
  intro castZero
  exact nonzero (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

def quarterTurn : NonNullProportion Scalar where
  scalar := 1
  vector := axis
  normNonzero := by
    change (2 : Scalar) ≠ 0
    exact natCast_ne_zero (by decide)

def quarterTurnDisplayed : Matrix3 Scalar :=
  ⟨1, 0, 0, 0, 0, 1, 0, -1, 0⟩

theorem quarterTurn_norm : quarterTurn.toProportion.norm = 2 := by
  unfold quarterTurn axis Proportion.norm Vector.quadrance Vector.dot
  ring1

theorem quarterTurn_matrix : quarterTurn.rotationMatrix =
    quarterTurnDisplayed := by
  decide

theorem quarterTurn_action (vector : Vector Scalar) :
    Matrix3.rowMul vector quarterTurnDisplayed =
      ⟨vector.t, -vector.s, vector.r⟩ := by
  apply Vector.ext <;> unfold quarterTurnDisplayed Matrix3.rowMul <;> ring1

theorem quarterTurn_halfSpread :
    halfSpread quarterTurn.rotation = (1 : Scalar) / 2 := by
  rw [NonNullProportion.halfSpread_rotation quarterTurn
      (natCast_ne_zero (by decide))]
  change axis.quadrance / quarterTurn.toProportion.norm = (1 : Scalar) / 2
  rw [quarterTurn_norm]
  rw [show axis.quadrance = (1 : Scalar) by
    unfold axis Vector.quadrance Vector.dot
    ring1]

theorem quarterTurn_class : quarterTurn.quadranceClass.value = 2 :=
  quarterTurn_norm

theorem quarterTurn_class_nontrivial :
    ¬ quarterTurn.quadranceClass.Equivalent quarterTurn.unitSquareClass := by
  rintro ⟨factor, _, unitValue⟩
  change (1 : Scalar) = factor ^ 2 * 2 at unitValue
  apply RFAP.ConstructiveFraction.square_ne_two (2 * factor)
  calc
    (2 * factor) ^ 2 = 2 * (factor ^ 2 * 2) := by ring1
    _ = 2 := by rw [← unitValue]; ring1

theorem quarterTurn_no_unit_quaternion :
    ¬ quarterTurn.HasUnitRepresentative := by
  rw [NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial]
  exact quarterTurn_class_nontrivial

/-- The paper's `3-4-5` rotation representative `(2:1:0:0)`. -/
def threeFourFive : NonNullProportion Scalar where
  scalar := 2
  vector := axis
  normNonzero := by
    change (5 : Scalar) ≠ 0
    exact natCast_ne_zero (by decide)

def threeFourFiveDisplayed : Matrix3 Scalar :=
  ⟨1, 0, 0,
    0, (3 : Scalar) / 5, 4 / 5,
    0, -4 / 5, 3 / 5⟩

theorem threeFourFive_norm : threeFourFive.toProportion.norm = 5 := by
  unfold threeFourFive axis Proportion.norm Vector.quadrance Vector.dot
  ring1

theorem threeFourFive_matrix : threeFourFive.rotationMatrix =
    threeFourFiveDisplayed := by
  decide

theorem threeFourFive_halfSpread :
    halfSpread threeFourFive.rotation = (1 : Scalar) / 5 := by
  rw [NonNullProportion.halfSpread_rotation threeFourFive
      (natCast_ne_zero (by decide))]
  change axis.quadrance / threeFourFive.toProportion.norm = (1 : Scalar) / 5
  rw [threeFourFive_norm]
  rw [show axis.quadrance = (1 : Scalar) by
    unfold axis Vector.quadrance Vector.dot
    ring1]

theorem threeFourFive_class : threeFourFive.quadranceClass.value = 5 :=
  threeFourFive_norm

theorem threeFourFive_class_nontrivial :
    ¬ threeFourFive.quadranceClass.Equivalent
      threeFourFive.unitSquareClass := by
  rintro ⟨factor, _, unitValue⟩
  change (1 : Scalar) = factor ^ 2 * 5 at unitValue
  apply RFAP.ConstructiveFraction.square_ne_five (5 * factor)
  calc
    (5 * factor) ^ 2 = 5 * (factor ^ 2 * 5) := by ring1
    _ = 5 := by rw [← unitValue]; ring1

theorem threeFourFive_no_unit_quaternion :
    ¬ threeFourFive.HasUnitRepresentative := by
  rw [NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial]
  exact threeFourFive_class_nontrivial

end ExampleSixtyFour

end RationalRotations
