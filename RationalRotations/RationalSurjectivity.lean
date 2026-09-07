import RationalRotations.QuadranceClasses
import mathlib.RFAP.ConstructiveFraction
import mathlib.RFAP.ConstructiveFourSquares

/-!
# Rational rotations, Theorem 62: constructive surjectivity boundary

The paper invokes Lagrange's four-square theorem to represent every positive
rational square class.  The upstream theorem is not in the paper-facing
dependency graph: its proof uses classical finite-field and cardinality
infrastructure excluded by this repository.

This module supplies that obligation by an explicitly finite prime-residue
search, Lagrange descent, bounded proper-factor recursion, and Euler products.
The algorithm returns four natural numbers together with their checked
equation.  From it the paper's rational construction is performed in finite
coordinates.  Conversely, every non-null rational proportion is proved to
have strictly positive norm.
-/

namespace RationalRotations

namespace TheoremSixtyTwo

abbrev Scalar := RFAP.ConstructiveFraction.Rational

/-- Checked output of a finite four-square calculation. -/
structure NaturalFourSquareRepresentation (value : Nat) where
  scalar : Nat
  t : Nat
  r : Nat
  s : Nat
  equation : scalar ^ 2 + t ^ 2 + r ^ 2 + s ^ 2 = value

/-- The computational content required from Lagrange's theorem.  Keeping the
four roots in the output makes downstream construction executable; no choice
of witnesses is hidden in a proposition. -/
structure NaturalFourSquareAlgorithm where
  represent : (value : Nat) → NaturalFourSquareRepresentation value

/-- The repository's finite, constructive Lagrange algorithm. -/
def lagrangeAlgorithm : NaturalFourSquareAlgorithm where
  represent value := by
    let output := RFAP.ConstructiveFourSquares.naturalRepresentation value
    exact
      { scalar := output.first
        t := output.second
        r := output.third
        s := output.fourth
        equation := output.equation }

/-- A nonzero rational square-class representative together with its strict
positivity certificate. -/
structure PositiveSquareClassRepresentative where
  representative : SquareClassRepresentative Scalar
  positive : 0 < representative.value

namespace PositiveSquareClassRepresentative

/-- The positive natural numerator stored by the canonical rational
representative. -/
def numerator (target : PositiveSquareClassRepresentative) : Nat :=
  target.representative.value.num.toNat

/-- The already-positive natural denominator stored by the canonical rational
representative. -/
def denominator (target : PositiveSquareClassRepresentative) : Nat :=
  target.representative.value.den

theorem numerator_positive (target : PositiveSquareClassRepresentative) :
    0 < target.numerator := by
  apply RFAP.ConstructiveFraction.toNat_pos_direct
  exact
    (RFAP.CanonicalFraction.zero_lt_iff_num_pos
      target.representative.value).mp target.positive

theorem denominator_positive (target : PositiveSquareClassRepresentative) :
    0 < target.denominator :=
  target.representative.value.den_pos

theorem denominator_cast_ne_zero
    (target : PositiveSquareClassRepresentative) :
    (target.denominator : Scalar) ≠ 0 := by
  intro castZero
  have naturalZero : target.denominator = 0 :=
    RFAP.ConstructiveFraction.natCast_injective_direct (by
      simpa only [Nat.cast_zero] using castZero)
  exact (Nat.ne_of_gt target.denominator_positive) naturalZero

theorem numerator_cast (target : PositiveSquareClassRepresentative) :
    (target.numerator : Scalar) =
      (target.representative.value.num : Scalar) := by
  have numeratorNonnegative :
      (0 : Int) ≤ target.representative.value.num :=
    Int.le_of_lt
      ((RFAP.CanonicalFraction.zero_lt_iff_num_pos
        target.representative.value).mp target.positive)
  have integerEquality :
      (target.representative.value.num.toNat : Int) =
        target.representative.value.num :=
    Int.toNat_of_nonneg numeratorNonnegative
  simpa only [numerator, Int.cast_natCast] using
    congrArg (fun value : Int => (value : Scalar)) integerEquality

/-- The canonical stored numerator and denominator display the target value
without selecting a quotient representative. -/
theorem value_eq_div (target : PositiveSquareClassRepresentative) :
    target.representative.value =
      (target.numerator : Scalar) / (target.denominator : Scalar) := by
  apply RFAP.ConstructiveFraction.mul_right_cancel_of_ne
    target.denominator_cast_ne_zero
  calc
    target.representative.value * (target.denominator : Scalar) =
        (target.representative.value.num : Scalar) :=
      RFAP.ConstructiveFraction.representative_mul_den
        target.representative.value
    _ = (target.numerator : Scalar) := target.numerator_cast.symm
    _ = ((target.numerator : Scalar) /
          (target.denominator : Scalar)) *
          (target.denominator : Scalar) :=
      (RFAP.ConstructiveFraction.div_mul_cancel_of_ne _ _
        target.denominator_cast_ne_zero).symm

end PositiveSquareClassRepresentative

/-- The four-square output used for a positive rational `a/b` is the checked
representation of the finite integer `a*b`. -/
def naturalRepresentation (algorithm : NaturalFourSquareAlgorithm)
    (target : PositiveSquareClassRepresentative) :
    NaturalFourSquareRepresentation (target.numerator * target.denominator) :=
  algorithm.represent (target.numerator * target.denominator)

/-- The exact denominator-clearing construction in the proof of Theorem 62:
if `ab=w²+x²+y²+z²`, divide all four roots by `b` to obtain a rational
four-square representation of `a/b`. -/
def rationalRepresentation (algorithm : NaturalFourSquareAlgorithm)
    (target : PositiveSquareClassRepresentative) :
    FourSquareRepresentation target.representative.value := by
  let output := naturalRepresentation algorithm target
  let denominator : Scalar := target.denominator
  refine
    { scalar := (output.scalar : Scalar) / denominator
      t := (output.t : Scalar) / denominator
      r := (output.r : Scalar) / denominator
      s := (output.s : Scalar) / denominator
      equation := ?_ }
  have outputEquation := congrArg (fun value : Nat => (value : Scalar))
    output.equation
  have outputEquationCast :
      (output.scalar : Scalar) ^ 2 + (output.t : Scalar) ^ 2 +
          (output.r : Scalar) ^ 2 + (output.s : Scalar) ^ 2 =
        (target.numerator : Scalar) * (target.denominator : Scalar) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow] using
      outputEquation
  have denominatorNonzero : denominator ≠ 0 :=
    target.denominator_cast_ne_zero
  have denominatorCancel :=
    RFAP.ExplicitField.mul_inv_cancel denominator denominatorNonzero
  change
    ((output.scalar : Scalar) / denominator) ^ 2 +
        ((output.t : Scalar) / denominator) ^ 2 +
        ((output.r : Scalar) / denominator) ^ 2 +
        ((output.s : Scalar) / denominator) ^ 2 =
      target.representative.value
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    ((output.scalar : Scalar) * denominator⁻¹) ^ 2 +
          ((output.t : Scalar) * denominator⁻¹) ^ 2 +
          ((output.r : Scalar) * denominator⁻¹) ^ 2 +
          ((output.s : Scalar) * denominator⁻¹) ^ 2 =
        ((output.scalar : Scalar) ^ 2 + (output.t : Scalar) ^ 2 +
          (output.r : Scalar) ^ 2 + (output.s : Scalar) ^ 2) *
            denominator⁻¹ ^ 2 := by ring1
    _ = ((target.numerator : Scalar) *
          (target.denominator : Scalar)) * denominator⁻¹ ^ 2 := by
      rw [outputEquationCast]
    _ = (target.numerator : Scalar) * denominator⁻¹ := by
      change
        (target.numerator : Scalar) * denominator * denominator⁻¹ ^ 2 =
          (target.numerator : Scalar) * denominator⁻¹
      calc
        (target.numerator : Scalar) * denominator * denominator⁻¹ ^ 2 =
            (target.numerator : Scalar) * denominator⁻¹ *
              (denominator * denominator⁻¹) := by ring1
        _ = (target.numerator : Scalar) * denominator⁻¹ := by
          rw [denominatorCancel, mul_one]
    _ = (target.numerator : Scalar) / (target.denominator : Scalar) := rfl
    _ = target.representative.value := target.value_eq_div.symm

/-- An executable four-square algorithm supplies a preimage for every
positive rational square-class representative. -/
def preimage (algorithm : NaturalFourSquareAlgorithm)
    (target : PositiveSquareClassRepresentative) : NonNullProportion Scalar :=
  (rationalRepresentation algorithm target).proportion target.representative

theorem preimage_quadranceClass (algorithm : NaturalFourSquareAlgorithm)
    (target : PositiveSquareClassRepresentative) :
    (preimage algorithm target).quadranceClass.value =
      target.representative.value :=
  FourSquareRepresentation.realizes_quadranceClass target.representative
    (rationalRepresentation algorithm target)

/-- Every rational proportion norm is nonnegative by its four displayed
squares. -/
theorem proportion_norm_nonnegative (proportion : Proportion Scalar) :
    0 ≤ proportion.norm := by
  have scalarNonnegative : 0 ≤ proportion.scalar ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct proportion.scalar
  have tNonnegative : 0 ≤ proportion.vector.t * proportion.vector.t := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.sq_nonneg_direct proportion.vector.t
  have rNonnegative : 0 ≤ proportion.vector.r * proportion.vector.r := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.sq_nonneg_direct proportion.vector.r
  have sNonnegative : 0 ≤ proportion.vector.s * proportion.vector.s := by
    simpa only [pow_two] using
      RFAP.ConstructiveFraction.sq_nonneg_direct proportion.vector.s
  unfold Proportion.norm Vector.quadrance Vector.dot
  exact add_nonneg scalarNonnegative
    (add_nonneg (add_nonneg tNonnegative rNonnegative) sNonnegative)

/-- The other direction of Theorem 62: every non-null rational proportion
has strictly positive norm, hence the quadrance-class image contains no
negative representative. -/
theorem nonNullProportion_norm_positive
    (proportion : NonNullProportion Scalar) :
    0 < proportion.toProportion.norm :=
  lt_of_le_of_ne (proportion_norm_nonnegative proportion.toProportion)
    proportion.normNonzero.symm

/-- Quotient-free membership in the image of the quadrance-class map. -/
def InQuadranceClassImage (target : SquareClassRepresentative Scalar) : Prop :=
  ∃ proportion : NonNullProportion Scalar,
    proportion.quadranceClass.Equivalent target

/-- Parametric core of Theorem 62: given executable four-square output, the
image of the quadrance-class map is precisely the positive square classes. -/
theorem inQuadranceClassImage_iff_positive
    (algorithm : NaturalFourSquareAlgorithm)
    (target : SquareClassRepresentative Scalar) :
    InQuadranceClassImage target ↔ 0 < target.value := by
  constructor
  · rintro ⟨proportion, factor, factorNonzero, targetValue⟩
    have factorSquareNonzero : factor ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        RFAP.ConstructiveFraction.mul_ne_zero_direct factorNonzero
          factorNonzero
    have factorSquarePositive : 0 < factor ^ 2 :=
      lt_of_le_of_ne
        (RFAP.ConstructiveFraction.sq_nonneg_direct factor)
        factorSquareNonzero.symm
    rw [targetValue]
    exact RFAP.ConstructiveFraction.mul_pos_direct factorSquarePositive
      (nonNullProportion_norm_positive proportion)
  · intro targetPositive
    let positiveTarget : PositiveSquareClassRepresentative :=
      ⟨target, targetPositive⟩
    have preimageValue := preimage_quadranceClass algorithm positiveTarget
    change (preimage algorithm positiveTarget).toProportion.norm =
      target.value at preimageValue
    refine ⟨preimage algorithm positiveTarget, 1, target.one_ne_zero, ?_⟩
    change target.value =
      (1 : Scalar) ^ 2 *
        (preimage algorithm positiveTarget).toProportion.norm
    rw [preimageValue]
    ring1

/-- Theorem 62 with the finite four-square algorithm instantiated: the image
of rational quadrance classes is exactly the positive square classes. -/
theorem quadranceClassImage_iff_positive
    (target : SquareClassRepresentative Scalar) :
    InQuadranceClassImage target ↔ 0 < target.value :=
  inQuadranceClassImage_iff_positive lagrangeAlgorithm target

end TheoremSixtyTwo

end RationalRotations
