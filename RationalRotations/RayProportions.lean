import RationalRotations.PrescribedAxes

/-!
# Rational rotations, section 12.2: ray proportions and spin

Ray equivalence is kept quotient-free: equality carries a displayed positive
scale.  The ordered-field interface includes the finite sign decision and
incompatibility laws actually used to split each projective class into its
two rays.  Products, inverses, the two-to-one rotation map, and the central
ray `(-1:0)` are all represented by executable coordinates.
-/

namespace RationalRotations

/-- The constructive ordered-field fragment needed for ray projectivization.
It extends the positivity fragment used by handedness with a finite sign
split for nonzero values and the two strict-order separation laws consumed
below. -/
class RayOrderedExplicitField (K : Type*) extends OrderedExplicitField K where
  positive_ne_zero_direct : ∀ {value : K}, 0 < value → value ≠ 0
  positive_neg_exclusive_direct : ∀ {value : K}, 0 < value → ¬ 0 < -value
  sign_split_direct : ∀ value : K, value ≠ 0 → (0 < value) ∨ (0 < -value)

namespace RayOrderedExplicitField

variable {F : Type*} [RayOrderedExplicitField F]

theorem one_ne_zero : (1 : F) ≠ 0 :=
  positive_ne_zero_direct OrderedExplicitField.zero_lt_one_direct

theorem neg_one_ne_zero : (-1 : F) ≠ 0 := by
  intro negOneZero
  apply one_ne_zero (F := F)
  calc
    (1 : F) = -(-1) := by ring1
    _ = -0 := by rw [negOneZero]
    _ = 0 := by ring1

theorem two_pos : 0 < (2 : F) := by
  rw [show (2 : F) = 1 + 1 by ring1]
  exact OrderedExplicitField.add_pos_direct
    OrderedExplicitField.zero_lt_one_direct
    OrderedExplicitField.zero_lt_one_direct

theorem two_ne_zero : (2 : F) ≠ 0 :=
  positive_ne_zero_direct two_pos

end RayOrderedExplicitField

variable {F : Type*} [RayOrderedExplicitField F]

local instance : DecidableEq F := OrderedExplicitField.eq_decidable

private theorem eq_of_mul_right_eq {left right factor : F}
    (factorNonzero : factor ≠ 0) (equal : left * factor = right * factor) :
    left = right := by
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * (factor * factor⁻¹) := by rw [cancel, mul_one]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [equal]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [cancel, mul_one]

private theorem add_square_pos {base value : F} (basePositive : 0 < base) :
    0 < base + value ^ 2 := by
  by_cases valueZero : value = 0
  · rw [valueZero]
    simpa only [pow_two, zero_mul, add_zero] using basePositive
  · have squarePositive : 0 < value ^ 2 := by
      simpa only [pow_two] using
        OrderedExplicitField.mul_self_pos_direct valueZero
    exact OrderedExplicitField.add_pos_direct basePositive squarePositive

/-- Every nonzero displayed four-tuple has positive norm in the finite
ordered interface. -/
theorem proportion_norm_pos_of_isNonzero (proportion : Proportion F)
    (nonzero : proportion.IsNonzero) : 0 < proportion.norm := by
  by_cases scalarZero : proportion.scalar = 0
  · by_cases tZero : proportion.vector.t = 0
    · by_cases rZero : proportion.vector.r = 0
      · by_cases sZero : proportion.vector.s = 0
        · apply False.elim
          apply nonzero
          apply Proportion.ext
          · exact scalarZero
          · exact Vector.ext tZero rZero sZero
        · have sPositive : 0 < proportion.vector.s ^ 2 := by
            simpa only [pow_two] using
              OrderedExplicitField.mul_self_pos_direct sZero
          unfold Proportion.norm Vector.quadrance Vector.dot
          rw [scalarZero, tZero, rZero]
          simpa only [pow_two, zero_mul, zero_add]
            using sPositive
      · have rPositive : 0 < proportion.vector.r ^ 2 := by
          simpa only [pow_two] using
            OrderedExplicitField.mul_self_pos_direct rZero
        have withS := add_square_pos (value := proportion.vector.s) rPositive
        unfold Proportion.norm Vector.quadrance Vector.dot
        rw [scalarZero, tZero]
        simpa only [pow_two, zero_mul, zero_add]
          using withS
    · have tPositive : 0 < proportion.vector.t ^ 2 := by
        simpa only [pow_two] using
          OrderedExplicitField.mul_self_pos_direct tZero
      have withR := add_square_pos (value := proportion.vector.r) tPositive
      have withS := add_square_pos (value := proportion.vector.s) withR
      unfold Proportion.norm Vector.quadrance Vector.dot
      rw [scalarZero]
      simpa only [pow_two, zero_mul, zero_add, add_assoc]
        using withS
  · have scalarPositive : 0 < proportion.scalar ^ 2 := by
      simpa only [pow_two] using
        OrderedExplicitField.mul_self_pos_direct scalarZero
    have withT := add_square_pos (value := proportion.vector.t) scalarPositive
    have withR := add_square_pos (value := proportion.vector.r) withT
    have withS := add_square_pos (value := proportion.vector.s) withR
    unfold Proportion.norm Vector.quadrance Vector.dot
    simpa only [pow_two, add_assoc] using withS

/-- Ordered fields have no nonzero null proportions, now as an executable
constructor from any displayed nonzero tuple. -/
def nonNullProportionOfNonzero (proportion : Proportion F)
    (nonzero : proportion.IsNonzero) : NonNullProportion F where
  toProportion := proportion
  normNonzero := RayOrderedExplicitField.positive_ne_zero_direct
    (proportion_norm_pos_of_isNonzero proportion nonzero)

/-- A ray representative is a displayed non-null proportion.  The stronger
ray equivalence below remembers the sign of homogeneous scale. -/
@[ext]
structure RayProportion (F : Type*) [RayOrderedExplicitField F] where
  toNonNullProportion : NonNullProportion F

namespace RayProportion

/-- Construct a ray directly from a nonzero displayed four-tuple. -/
def ofNonzero (proportion : Proportion F) (nonzero : proportion.IsNonzero) :
    RayProportion F :=
  ⟨nonNullProportionOfNonzero proportion nonzero⟩

/-- Positive homogeneous equivalence of ray representatives. -/
def Equivalent (left right : RayProportion F) : Prop :=
  ∃ factor : F, 0 < factor ∧
    right.toNonNullProportion.toProportion =
      Proportion.scale factor left.toNonNullProportion.toProportion

theorem equivalent_refl (proportion : RayProportion F) :
    proportion.Equivalent proportion := by
  refine ⟨1, OrderedExplicitField.zero_lt_one_direct, ?_⟩
  exact (Proportion.one_scale _).symm

theorem equivalent_symm {left right : RayProportion F}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorPositive, rightValue⟩
  have factorNonzero :=
    RayOrderedExplicitField.positive_ne_zero_direct factorPositive
  have cancel := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  have reverseCancel : factor⁻¹ * factor = 1 := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := cancel
  refine ⟨factor⁻¹, OrderedExplicitField.inv_pos_direct factorPositive, ?_⟩
  calc
    left.toNonNullProportion.toProportion =
        Proportion.scale 1 left.toNonNullProportion.toProportion := by
      rw [Proportion.one_scale]
    _ = Proportion.scale (factor⁻¹ * factor)
        left.toNonNullProportion.toProportion := by rw [reverseCancel]
    _ = Proportion.scale factor⁻¹
        (Proportion.scale factor left.toNonNullProportion.toProportion) := by
      rw [Proportion.scale_scale]
    _ = Proportion.scale factor⁻¹
        right.toNonNullProportion.toProportion := by rw [← rightValue]

theorem equivalent_trans {first second third : RayProportion F}
    (firstSecond : first.Equivalent second)
    (secondThird : second.Equivalent third) : first.Equivalent third := by
  rcases firstSecond with ⟨firstFactor, firstPositive, secondValue⟩
  rcases secondThird with ⟨secondFactor, secondPositive, thirdValue⟩
  refine ⟨secondFactor * firstFactor,
    OrderedExplicitField.mul_pos_direct secondPositive firstPositive, ?_⟩
  calc
    third.toNonNullProportion.toProportion =
        Proportion.scale secondFactor
          second.toNonNullProportion.toProportion := thirdValue
    _ = Proportion.scale secondFactor
        (Proportion.scale firstFactor
          first.toNonNullProportion.toProportion) := by rw [secondValue]
    _ = Proportion.scale (secondFactor * firstFactor)
        first.toNonNullProportion.toProportion :=
      Proportion.scale_scale _ _ _

/-- Positive rescaling of a ray representative. -/
def scale (factor : F) (factorPositive : 0 < factor)
    (proportion : RayProportion F) : RayProportion F where
  toNonNullProportion := NonNullProportion.scale factor
    (RayOrderedExplicitField.positive_ne_zero_direct factorPositive)
    proportion.toNonNullProportion

theorem equivalent_scale (factor : F) (factorPositive : 0 < factor)
    (proportion : RayProportion F) :
    proportion.Equivalent (scale factor factorPositive proportion) := by
  exact ⟨factor, factorPositive, rfl⟩

/-- The opposite ray representative. -/
def neg (proportion : RayProportion F) : RayProportion F where
  toNonNullProportion := NonNullProportion.scale (-1)
    RayOrderedExplicitField.neg_one_ne_zero proportion.toNonNullProportion

@[simp] theorem neg_toProportion (proportion : RayProportion F) :
    (neg proportion).toNonNullProportion.toProportion =
      Proportion.scale (-1) proportion.toNonNullProportion.toProportion :=
  rfl

private theorem scale_factor_injective
    (proportion : Proportion F) (nonzero : proportion.IsNonzero)
    {left right : F}
    (equal : Proportion.scale left proportion =
      Proportion.scale right proportion) : left = right := by
  by_cases scalarZero : proportion.scalar = 0
  · by_cases tZero : proportion.vector.t = 0
    · by_cases rZero : proportion.vector.r = 0
      · by_cases sZero : proportion.vector.s = 0
        · apply False.elim
          apply nonzero
          apply Proportion.ext
          · exact scalarZero
          · exact Vector.ext tZero rZero sZero
        · apply eq_of_mul_right_eq sZero
          exact congrArg (fun value => value.vector.s) equal
      · apply eq_of_mul_right_eq rZero
        exact congrArg (fun value => value.vector.r) equal
    · apply eq_of_mul_right_eq tZero
      exact congrArg (fun value => value.vector.t) equal
  · apply eq_of_mul_right_eq scalarZero
    exact congrArg Proportion.scalar equal

/-- The two opposite rays in a projective class are genuinely distinct. -/
theorem not_equivalent_neg (proportion : RayProportion F) :
    ¬ proportion.Equivalent proportion.neg := by
  rintro ⟨factor, factorPositive, negValue⟩
  have factorEqual : factor = -1 := by
    apply scale_factor_injective proportion.toNonNullProportion.toProportion
      proportion.toNonNullProportion.isNonzero
    calc
      Proportion.scale factor proportion.toNonNullProportion.toProportion =
          proportion.neg.toNonNullProportion.toProportion := negValue.symm
      _ = Proportion.scale (-1)
          proportion.toNonNullProportion.toProportion := rfl
  have negOnePositive : 0 < (-1 : F) := by rw [← factorEqual]; exact factorPositive
  exact (RayOrderedExplicitField.positive_neg_exclusive_direct
    OrderedExplicitField.zero_lt_one_direct) negOnePositive

/-- Quaternion product on ray representatives. -/
def mul (left right : RayProportion F) : RayProportion F :=
  ⟨NonNullProportion.mul left.toNonNullProportion
    right.toNonNullProportion⟩

theorem mul_assoc (first second third : RayProportion F) :
    mul (mul first second) third = mul first (mul second third) := by
  apply RayProportion.ext
  exact NonNullProportion.mul_assoc first.toNonNullProportion
    second.toNonNullProportion third.toNonNullProportion

theorem mul_respects_equivalent
    {left left' right right' : RayProportion F}
    (leftEquivalent : left.Equivalent left')
    (rightEquivalent : right.Equivalent right') :
    (mul left right).Equivalent (mul left' right') := by
  rcases leftEquivalent with ⟨leftFactor, leftPositive, leftValue⟩
  rcases rightEquivalent with ⟨rightFactor, rightPositive, rightValue⟩
  refine ⟨leftFactor * rightFactor,
    OrderedExplicitField.mul_pos_direct leftPositive rightPositive, ?_⟩
  change Proportion.mul left'.toNonNullProportion.toProportion
      right'.toNonNullProportion.toProportion =
    Proportion.scale (leftFactor * rightFactor)
      (Proportion.mul left.toNonNullProportion.toProportion
        right.toNonNullProportion.toProportion)
  rw [leftValue, rightValue, Proportion.mul_scale_both]

/-- Canonical identity ray `(1:0)`. -/
def identity : RayProportion F where
  toNonNullProportion :=
    { toProportion := Proportion.identity
      normNonzero := by
        unfold Proportion.norm Proportion.identity
        rw [Vector.quadrance_zero]
        simpa only [one_pow, add_zero] using
          RayOrderedExplicitField.one_ne_zero (F := F) }

@[simp] theorem identity_mul (proportion : RayProportion F) :
    mul identity proportion = proportion := by
  apply RayProportion.ext
  apply NonNullProportion.ext (K := F)
  · exact congrArg Proportion.scalar
      (Proportion.identity_mul proportion.toNonNullProportion.toProportion)
  · exact congrArg Proportion.vector
      (Proportion.identity_mul proportion.toNonNullProportion.toProportion)

@[simp] theorem mul_identity (proportion : RayProportion F) :
    mul proportion identity = proportion := by
  apply RayProportion.ext
  apply NonNullProportion.ext (K := F)
  · exact congrArg Proportion.scalar
      (Proportion.mul_identity proportion.toNonNullProportion.toProportion)
  · exact congrArg Proportion.vector
      (Proportion.mul_identity proportion.toNonNullProportion.toProportion)

/-- Quaternion conjugation is the ray-group inverse. -/
def conjugate (proportion : RayProportion F) : RayProportion F :=
  ⟨NonNullProportion.conjugate proportion.toNonNullProportion⟩

theorem norm_positive (proportion : RayProportion F) :
    0 < proportion.toNonNullProportion.toProportion.norm :=
  proportion_norm_pos_of_isNonzero _ proportion.toNonNullProportion.isNonzero

theorem mul_conjugate_equivalent_identity (proportion : RayProportion F) :
    (mul proportion proportion.conjugate).Equivalent identity := by
  apply equivalent_symm
  refine ⟨proportion.toNonNullProportion.toProportion.norm,
    proportion.norm_positive, ?_⟩
  exact Proportion.mul_conjugate proportion.toNonNullProportion.toProportion

theorem conjugate_mul_equivalent_identity (proportion : RayProportion F) :
    (mul proportion.conjugate proportion).Equivalent identity := by
  apply equivalent_symm
  refine ⟨proportion.toNonNullProportion.toProportion.norm,
    proportion.norm_positive, ?_⟩
  exact Proportion.conjugate_mul proportion.toNonNullProportion.toProportion

end RayProportion

/-- The quotient-free group laws for ray proportions. -/
structure RayProportionGroupLaws (F : Type*) [RayOrderedExplicitField F] where
  identity : RayProportion F
  inverse : RayProportion F → RayProportion F
  associative : ∀ first second third : RayProportion F,
    RayProportion.mul (RayProportion.mul first second) third =
      RayProportion.mul first (RayProportion.mul second third)
  leftIdentity : ∀ proportion : RayProportion F,
    RayProportion.mul identity proportion = proportion
  rightIdentity : ∀ proportion : RayProportion F,
    RayProportion.mul proportion identity = proportion
  leftInverse : ∀ proportion : RayProportion F,
    (RayProportion.mul (inverse proportion) proportion).Equivalent identity
  rightInverse : ∀ proportion : RayProportion F,
    (RayProportion.mul proportion (inverse proportion)).Equivalent identity
  respectsEquivalent :
    ∀ {left left' right right' : RayProportion F},
      left.Equivalent left' → right.Equivalent right' →
        (RayProportion.mul left right).Equivalent
          (RayProportion.mul left' right')

/-- Section 12.2's ray group, with conjugation as inverse. -/
def rayProportionGroupLaws : RayProportionGroupLaws F where
  identity := RayProportion.identity
  inverse := RayProportion.conjugate
  associative := RayProportion.mul_assoc
  leftIdentity := RayProportion.identity_mul
  rightIdentity := RayProportion.mul_identity
  leftInverse := RayProportion.conjugate_mul_equivalent_identity
  rightInverse := RayProportion.mul_conjugate_equivalent_identity
  respectsEquivalent := RayProportion.mul_respects_equivalent

namespace RayProportion

/-- Forgetting ray orientation gives the ordinary projective equivalence. -/
theorem projectivelyEquivalent_of_equivalent {left right : RayProportion F}
    (equivalent : left.Equivalent right) :
    left.toNonNullProportion.Equivalent right.toNonNullProportion := by
  rcases equivalent with ⟨factor, factorPositive, rightValue⟩
  exact ⟨factor,
    RayOrderedExplicitField.positive_ne_zero_direct factorPositive,
    rightValue⟩

/-- A projective equivalence has positive or negative scale, so it belongs
to the original ray or to its opposite. -/
theorem equivalent_or_neg_equivalent_of_projectivelyEquivalent
    (left right : RayProportion F)
    (equivalent : left.toNonNullProportion.Equivalent
      right.toNonNullProportion) :
    left.Equivalent right ∨ left.neg.Equivalent right := by
  rcases equivalent with ⟨factor, factorNonzero, rightValue⟩
  rcases RayOrderedExplicitField.sign_split_direct factor factorNonzero with
    factorPositive | negativePositive
  · exact Or.inl ⟨factor, factorPositive, rightValue⟩
  · apply Or.inr
    refine ⟨-factor, negativePositive, ?_⟩
    calc
      right.toNonNullProportion.toProportion =
          Proportion.scale factor left.toNonNullProportion.toProportion :=
        rightValue
      _ = Proportion.scale ((-factor) * (-1))
          left.toNonNullProportion.toProportion := by
        congr 1
        ring1
      _ = Proportion.scale (-factor)
          (Proportion.scale (-1)
            left.toNonNullProportion.toProportion) :=
        (Proportion.scale_scale _ _ _).symm
      _ = Proportion.scale (-factor)
          left.neg.toNonNullProportion.toProportion := rfl

/-- The rotation represented by a ray. -/
def rotation (proportion : RayProportion F) : Rotation F :=
  proportion.toNonNullProportion.rotation

theorem rotation_respects_equivalent {left right : RayProportion F}
    (equivalent : left.Equivalent right) :
    left.rotation.matrix = right.rotation.matrix :=
  NonNullProportion.rotationMatrix_respects_equivalent
    (projectivelyEquivalent_of_equivalent equivalent)

/-- Opposite rays lie over the same rotation. -/
theorem rotation_neg (proportion : RayProportion F) :
    proportion.neg.rotation.matrix = proportion.rotation.matrix := by
  exact NonNullProportion.rotationMatrix_scale (-1)
    RayOrderedExplicitField.neg_one_ne_zero proportion.toNonNullProportion

/-- The ray map preserves quaternion multiplication. -/
theorem rotation_mul (left right : RayProportion F) :
    (mul left right).rotation.matrix =
      Matrix3.mul left.rotation.matrix right.rotation.matrix :=
  NonNullProportion.rotationMatrix_mul left.toNonNullProportion
    right.toNonNullProportion

/-- Every stored rotation has a computed ray representative. -/
def representativeOfRotation (rotation : Rotation F) : RayProportion F :=
  ⟨RotationProportion.ofRotation rotation
    RayOrderedExplicitField.two_ne_zero⟩

theorem representativeOfRotation_represents (rotation : Rotation F) :
    (representativeOfRotation rotation).rotation.matrix = rotation.matrix :=
  RotationProportion.ofRotation_rotationMatrix rotation
    RayOrderedExplicitField.two_ne_zero

/-- The map from ray proportions to rotations is surjective. -/
theorem rotation_surjective (rotation : Rotation F) :
    ∃ proportion : RayProportion F,
      proportion.rotation.matrix = rotation.matrix :=
  ⟨representativeOfRotation rotation,
    representativeOfRotation_represents rotation⟩

/-- Exact quotient-free two-to-one statement: equal rotations mean the same
ray or the opposite ray, and either alternative gives equal rotations. -/
theorem rotation_eq_iff_equivalent_or_neg_equivalent
    (left right : RayProportion F) :
    left.rotation.matrix = right.rotation.matrix ↔
      left.Equivalent right ∨ left.neg.Equivalent right := by
  constructor
  · intro equalRotation
    have projective := NonNullProportion.equivalent_of_rotationMatrix_eq
      left.toNonNullProportion right.toNonNullProportion
      RayOrderedExplicitField.two_ne_zero equalRotation
    exact equivalent_or_neg_equivalent_of_projectivelyEquivalent left right
      projective
  · rintro (sameRay | oppositeRay)
    · exact rotation_respects_equivalent sameRay
    · calc
        left.rotation.matrix = left.neg.rotation.matrix :=
          (rotation_neg left).symm
        _ = right.rotation.matrix :=
          rotation_respects_equivalent oppositeRay

/-- The two alternatives in a rotation fiber are distinct. -/
theorem rotation_fiber_has_two_distinct_rays (proportion : RayProportion F) :
    proportion.neg.rotation.matrix = proportion.rotation.matrix ∧
      ¬ proportion.Equivalent proportion.neg :=
  ⟨rotation_neg proportion, not_equivalent_neg proportion⟩

/-- The nontrivial central ray over the identity rotation. -/
def negativeIdentity : RayProportion F := identity.neg

theorem identity_rotation_matrix :
    (identity : RayProportion F).rotation.matrix =
      (Matrix3.identity : Matrix3 F) := by
  let defined : reciprocalAnchorPathDenominator (1 : F) Vector.zero ≠ 0 := by
    unfold reciprocalAnchorPathDenominator
    rw [Vector.quadrance_zero, add_zero]
    simpa only [one_pow] using
      RayOrderedExplicitField.one_ne_zero (F := F)
  change reciprocalAnchorPath 1 Vector.zero defined = Matrix3.identity
  ext <;> unfold reciprocalAnchorPath reciprocalAnchorPathDenominator
    Matrix3.add Matrix3.scale Matrix3.identity Matrix3.mul anchor
    Vector.zero Vector.quadrance Vector.dot <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;> ring1

theorem negativeIdentity_rotation_matrix :
    (negativeIdentity : RayProportion F).rotation.matrix =
      (Matrix3.identity : Matrix3 F) := by
  calc
    (negativeIdentity : RayProportion F).rotation.matrix =
        (identity : RayProportion F).rotation.matrix :=
      rotation_neg (identity : RayProportion F)
    _ = Matrix3.identity := identity_rotation_matrix

theorem negativeIdentity_distinct :
    ¬ (identity : RayProportion F).Equivalent negativeIdentity :=
  not_equivalent_neg (identity : RayProportion F)

/-- The ray `(-1:0)` has order two already at representative level. -/
theorem negativeIdentity_square :
    mul (negativeIdentity : RayProportion F) negativeIdentity = identity := by
  have raw : Proportion.mul
      (Proportion.scale (-1) Proportion.identity)
      (Proportion.scale (-1) Proportion.identity) =
      (Proportion.identity : Proportion F) := by
    apply Proportion.ext
    · unfold Proportion.mul Proportion.scale Proportion.identity
        Vector.zero Vector.scale Vector.dot
      ring1
    · apply Vector.ext <;>
        unfold Proportion.mul Proportion.scale Proportion.identity Vector.zero
          Vector.scale Vector.dot Vector.sub Vector.add Vector.cross <;> ring1
  apply RayProportion.ext
  apply NonNullProportion.ext (K := F)
  · exact congrArg Proportion.scalar raw
  · exact congrArg Proportion.vector raw

/-- The ray `(-1:0)` is central and negates every displayed
representative. -/
theorem negativeIdentity_central (proportion : RayProportion F) :
    mul negativeIdentity proportion = proportion.neg ∧
      mul proportion negativeIdentity = proportion.neg := by
  have leftRaw :
      Proportion.mul (Proportion.scale (-1) Proportion.identity)
          proportion.toNonNullProportion.toProportion =
        Proportion.scale (-1)
          proportion.toNonNullProportion.toProportion := by
    apply Proportion.ext
    · unfold Proportion.mul Proportion.scale Proportion.identity Vector.zero
        Vector.scale Vector.dot
      ring1
    · apply Vector.ext <;>
        unfold Proportion.mul Proportion.scale Proportion.identity Vector.zero
          Vector.scale Vector.dot Vector.sub Vector.add Vector.cross <;> ring1
  have rightRaw :
      Proportion.mul proportion.toNonNullProportion.toProportion
          (Proportion.scale (-1) Proportion.identity) =
        Proportion.scale (-1)
          proportion.toNonNullProportion.toProportion := by
    apply Proportion.ext
    · unfold Proportion.mul Proportion.scale Proportion.identity Vector.zero
        Vector.scale Vector.dot
      ring1
    · apply Vector.ext <;>
        unfold Proportion.mul Proportion.scale Proportion.identity Vector.zero
          Vector.scale Vector.dot Vector.sub Vector.add Vector.cross <;> ring1
  constructor
  · apply RayProportion.ext
    apply NonNullProportion.ext (K := F)
    · exact congrArg Proportion.scalar leftRaw
    · exact congrArg Proportion.vector leftRaw
  · apply RayProportion.ext
    apply NonNullProportion.ext (K := F)
    · exact congrArg Proportion.scalar rightRaw
    · exact congrArg Proportion.vector rightRaw

end RayProportion

namespace RationalRayModel

abbrev Scalar := RFAP.ConstructiveFraction.Rational

/-- The repository's executable rational field satisfies the finite ordered
interface used by ray projectivization. -/
instance : RayOrderedExplicitField Scalar where
  toOrderedExplicitField :=
    { toExplicitField := inferInstance
      toLT := inferInstance
      eq_decidable := inferInstance
      zero_lt_one_direct :=
        RFAP.ConstructiveFraction.natCast_pos_direct (n := 1) (by decide)
      add_pos_direct := by
        intro left right leftPositive rightPositive
        exact add_pos leftPositive rightPositive
      mul_pos_direct := RFAP.ConstructiveFraction.mul_pos_direct
      mul_self_pos_direct := by
        intro value valueNonzero
        rcases lt_trichotomy value 0 with negative | zero | positive
        · have negatedPositive : 0 < -value := neg_pos.mpr negative
          have productPositive := RFAP.ConstructiveFraction.mul_pos_direct
            negatedPositive negatedPositive
          simpa only [neg_mul_neg] using productPositive
        · exact (valueNonzero zero).elim
        · exact RFAP.ConstructiveFraction.mul_pos_direct positive positive
      inv_pos_direct := RFAP.ConstructiveFraction.inv_pos_direct }
  positive_ne_zero_direct := by
    intro value positive
    exact ne_of_gt positive
  positive_neg_exclusive_direct := by
    intro value positive negativePositive
    have negative : value < 0 := neg_pos.mp negativePositive
    exact lt_asymm positive negative
  sign_split_direct := by
    intro value valueNonzero
    rcases lt_trichotomy value 0 with negative | zero | positive
    · exact Or.inr (neg_pos.mpr negative)
    · exact (valueNonzero zero).elim
    · exact Or.inl positive

/-- The full ray group is therefore available over the canonical rational
carrier, without normalization to the unit sphere. -/
def groupLaws : RayProportionGroupLaws Scalar := rayProportionGroupLaws

end RationalRayModel

end RationalRotations
