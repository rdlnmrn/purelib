module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Data.Rat.Fraction.ExplicitOrder.Sign
import Purelib.Algebra.Field.ExplicitOrder.Basic
import Purelib.Algebra.Field.ExplicitOrder.Sign
public import Purelib.Algebra.Quaternion.Projective.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

open Purelib.Algebra.Field.ExplicitOrder.Basic

open Purelib.Algebra.Field.ExplicitOrder.Sign

open Purelib.Algebra.Quaternion.Projective.Basic

open Purelib.Data.Rat

section
public section

/-!
# Rational rotations, section 12.2: ray proportions and spin

Ray equivalence is kept quotient-free: equality carries a displayed positive
scale.  The ordered-field interface includes the finite sign decision and
incompatibility laws actually used to split each projective class into its
two rays.  Products, inverses, the two-to-one rotation map, and the central
ray `(-1:0)` are all represented by executable coordinates.
-/

namespace Purelib.Algebra.Quaternion.Ray.Basic

variable {F : Type*} [RayOrderedExplicitField F]

-- Preserve the original local instance owner and keep its full active scope.
with_weak_namespace _root_.Purelib.Rotations
  /-- Use the decidable equality retained by the ray-ordered explicit field. -/
  local instance : DecidableEq F := OrderedExplicitField.eq_decidable

/-- Every nonzero quaternion quadruple has positive norm in the ray-ordered field.

At least one coordinate square is positive, and adding the remaining squares preserves positivity. -/
theorem proportion_norm_pos_of_isNonzero (proportion : Proportion F)
    (nonzero : proportion.IsNonzero) : 0 < proportion.norm := open Purelib.Algebra.Quaternion in open
      Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3 in by
  by_cases scalarZero : proportion.scalar = 0
  · by_cases tZero : proportion.vector.t = 0
    · by_cases rZero : proportion.vector.r = 0
      · by_cases sZero : proportion.vector.s = 0
        · apply False.elim
          apply nonzero
          apply Proportion.ext
          · exact scalarZero
          · exact Vector3.ext tZero rZero sZero
        · have sPositive : 0 < proportion.vector.s ^ 2 := by
            simpa only [pow_two] using
              OrderedExplicitField.mul_self_pos_direct sZero
          unfold Proportion.norm Vector3.quadrance Vector3.dot
          rw [scalarZero, tZero, rZero]
          simpa only [pow_two, zero_mul, zero_add]
            using sPositive
      · have rPositive : 0 < proportion.vector.r ^ 2 := by
          simpa only [pow_two] using
            OrderedExplicitField.mul_self_pos_direct rZero
        have withS := Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField.add_square_pos (value :=
          proportion.vector.s) rPositive
        unfold Proportion.norm Vector3.quadrance Vector3.dot
        rw [scalarZero, tZero]
        simpa only [pow_two, zero_mul, zero_add]
          using withS
    · have tPositive : 0 < proportion.vector.t ^ 2 := by
        simpa only [pow_two] using
          OrderedExplicitField.mul_self_pos_direct tZero
      have withR := Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField.add_square_pos (value :=
        proportion.vector.r) tPositive
      have withS := Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField.add_square_pos (value :=
        proportion.vector.s) withR
      unfold Proportion.norm Vector3.quadrance Vector3.dot
      rw [scalarZero]
      simpa only [pow_two, zero_mul, zero_add, add_assoc]
        using withS
  · have scalarPositive : 0 < proportion.scalar ^ 2 := by
      simpa only [pow_two] using
        OrderedExplicitField.mul_self_pos_direct scalarZero
    have withT := Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField.add_square_pos (value :=
      proportion.vector.t) scalarPositive
    have withR := Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField.add_square_pos (value :=
      proportion.vector.r) withT
    have withS := Purelib.Algebra.Field.ExplicitOrder.Sign.RayOrderedExplicitField.add_square_pos (value :=
      proportion.vector.s) withR
    unfold Proportion.norm Vector3.quadrance Vector3.dot
    simpa only [pow_two, add_assoc] using withS

open Purelib.Algebra.Quaternion in
/-- Certify a displayed nonzero quaternion quadruple as non-null.

The ordered positivity laws show its retained norm is positive and hence nonzero. -/
@[expose] def nonNullProportionOfNonzero (proportion : Proportion F)
    (nonzero : proportion.IsNonzero) : NonNullProportion F where
  toProportion := proportion
  normNonzero := RayOrderedExplicitField.positive_ne_zero_direct
    (Ray.Basic.proportion_norm_pos_of_isNonzero proportion nonzero)

set_option genInjectivity false in
/-- A displayed non-null quaternion representative with oriented ray equivalence.

The underlying projective proportion is retained directly; equivalence is defined separately using positive homogeneous
scales. -/
@[ext]
structure RayProportion (F : Type*) [RayOrderedExplicitField F] where
  /-- The retained non-null projective quaternion representative. -/ toNonNullProportion : NonNullProportion F

constructive_injectivity Purelib.Algebra.Quaternion.Ray.Basic.RayProportion

namespace RayProportion

open Purelib.Algebra.Quaternion.Ray.Basic in
open Purelib.Algebra.Quaternion in
/-- Construct a ray from a displayed nonzero quaternion quadruple.

The ordered positivity certificate makes its original norm nonzero. -/
@[expose] def ofNonzero (proportion : Proportion F) (nonzero :
  proportion.IsNonzero) :
    RayProportion F :=
  ⟨Ray.Basic.nonNullProportionOfNonzero proportion nonzero⟩

section
open Purelib.Algebra.Quaternion.Ray.Basic
/-- Two ray representatives differ by a displayed positive homogeneous scale.

The factor and the exact scaled-coordinate equality are retained without quotienting the representatives. -/
@[expose] def Equivalent (left right : RayProportion F) : Prop
  :=
  ∃ factor : F, 0 < factor ∧
    right.toNonNullProportion.toProportion =
      Proportion.scale factor left.toNonNullProportion.toProportion

/-- Each ray representative is positively equivalent to itself using unit scale. -/
theorem equivalent_refl (proportion : RayProportion F) :
    proportion.Equivalent proportion := by
  refine ⟨1, OrderedExplicitField.zero_lt_one_direct, ?_⟩
  exact (Proportion.one_scale _).symm

/-- Reverse ray equivalence by inverting its retained positive scale. -/
theorem equivalent_symm {left right : RayProportion F}
    (equivalent : left.Equivalent right) : right.Equivalent left := by
  rcases equivalent with ⟨factor, factorPositive, rightValue⟩
  have factorNonzero :=
    RayOrderedExplicitField.positive_ne_zero_direct factorPositive
  have cancel := ExplicitField.mul_inv_cancel factor factorNonzero
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

/-- Compose ray equivalences by multiplying their retained positive scales. -/
theorem equivalent_trans {first second third : RayProportion
  F}
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

/-- Rescale a ray representative by the supplied positive factor.

Positivity provides the nonzero certificate required by the underlying projective scaling. -/
@[expose] def scale (factor : F) (factorPositive : 0 < factor)
    (proportion : RayProportion F) : RayProportion F where
  toNonNullProportion := NonNullProportion.scale factor
    (RayOrderedExplicitField.positive_ne_zero_direct factorPositive)
    proportion.toNonNullProportion

/-- A positive rescaling represents the same ray. -/
theorem equivalent_scale (factor : F) (factorPositive : 0 <
  factor)
    (proportion : RayProportion F) :
    proportion.Equivalent (RayProportion.scale factor factorPositive proportion) := by
  exact ⟨factor, factorPositive, rfl⟩

/-- Construct the opposite ray by multiplying its coordinates by negative one. -/
@[expose] def neg (proportion : RayProportion F) :
  RayProportion F where
  toNonNullProportion := NonNullProportion.scale (-1)
    RayOrderedExplicitField.neg_one_ne_zero proportion.toNonNullProportion

/-- The opposite ray retains the original proportion scaled by negative one. -/
@[simp] theorem neg_toProportion (proportion : RayProportion
  F) :
    (RayProportion.neg proportion).toNonNullProportion.toProportion =
      Proportion.scale (-1) proportion.toNonNullProportion.toProportion :=
  rfl

end

/-- Distinct homogeneous scales give distinct rescalings of a nonzero quadruple.

A displayed nonzero coordinate supports cancellation of the equality of scaled tuples. -/
private theorem scale_factor_injective
    (proportion : Proportion F) (nonzero : proportion.IsNonzero)
    {left right : F}
    (equal : Proportion.scale left proportion =
      Proportion.scale right proportion) : left = right := open Purelib.LinearAlgebra.Coordinates3 renaming Vector ->
        Vector3 in by
  by_cases scalarZero : proportion.scalar = 0
  · by_cases tZero : proportion.vector.t = 0
    · by_cases rZero : proportion.vector.r = 0
      · by_cases sZero : proportion.vector.s = 0
        · apply False.elim
          apply nonzero
          apply Proportion.ext
          · exact scalarZero
          · exact Vector3.ext tZero rZero sZero
        · apply ExplicitOrder.Sign.RayOrderedExplicitField.eq_of_mul_right_eq sZero
          exact congrArg (fun value => value.vector.s) equal
      · apply ExplicitOrder.Sign.RayOrderedExplicitField.eq_of_mul_right_eq rZero
        exact congrArg (fun value => value.vector.r) equal
    · apply ExplicitOrder.Sign.RayOrderedExplicitField.eq_of_mul_right_eq tZero
      exact congrArg (fun value => value.vector.t) equal
  · apply ExplicitOrder.Sign.RayOrderedExplicitField.eq_of_mul_right_eq scalarZero
    exact congrArg Proportion.scalar equal

section
open Purelib.Algebra.Quaternion.Ray.Basic
/-- A ray is not positively equivalent to its opposite.

Injectivity of homogeneous scaling and exclusivity of positive opposite signs rule out the proposed factor. -/
theorem not_equivalent_neg (proportion : RayProportion F) :
    ¬ proportion.Equivalent proportion.neg := open Purelib.Algebra.Quaternion.Ray.Basic in by
  rintro ⟨factor, factorPositive, negValue⟩
  have factorEqual : factor = -1 := by
    apply RayProportion.scale_factor_injective proportion.toNonNullProportion.toProportion
      proportion.toNonNullProportion.isNonzero
    calc
      Proportion.scale factor proportion.toNonNullProportion.toProportion =
          proportion.neg.toNonNullProportion.toProportion := negValue.symm
      _ = Proportion.scale (-1)
          proportion.toNonNullProportion.toProportion := rfl
  have negOnePositive : 0 < (-1 : F) := by rw [← factorEqual]; exact factorPositive
  exact (RayOrderedExplicitField.positive_neg_exclusive_direct
    OrderedExplicitField.zero_lt_one_direct) negOnePositive

/-- Multiply ray representatives using their retained non-null quaternion product. -/
@[expose] def mul (left right : RayProportion F) :
  RayProportion F :=
  ⟨NonNullProportion.mul left.toNonNullProportion
    right.toNonNullProportion⟩

/-- Multiplication of displayed ray representatives is associative. -/
theorem mul_assoc (first second third : RayProportion F) :
    RayProportion.mul (RayProportion.mul first second) third = RayProportion.mul first (RayProportion.mul second third)
      := by
  apply RayProportion.ext
  exact NonNullProportion.mul_assoc first.toNonNullProportion
    second.toNonNullProportion third.toNonNullProportion

/-- Ray multiplication respects positive equivalence in both inputs.

The product of the retained positive factors witnesses the output equivalence. -/
theorem mul_respects_equivalent
    {left left' right right' : RayProportion F}
    (leftEquivalent : left.Equivalent left')
    (rightEquivalent : right.Equivalent right') :
    (RayProportion.mul left right).Equivalent (RayProportion.mul left' right') := by
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

/-- The identity ray has scalar coordinate one and zero vector.

The ordered unit positivity certifies its nonzero norm. -/
@[expose] def identity : RayProportion F where
  toNonNullProportion :=
    { toProportion := Proportion.identity
      normNonzero := by
        unfold Proportion.norm Proportion.identity
        rw [Purelib.LinearAlgebra.Coordinates3.Vector.quadrance_zero]
        simpa only [one_pow, add_zero] using
          RayOrderedExplicitField.one_ne_zero (F := F) }

/-- The identity ray is an exact left identity for multiplication. -/
@[simp] theorem identity_mul (proportion : RayProportion F) :
    RayProportion.mul RayProportion.identity proportion = proportion := by
  apply RayProportion.ext
  apply NonNullProportion.ext (K := F)
  · exact congrArg Proportion.scalar
      (Proportion.identity_mul proportion.toNonNullProportion.toProportion)
  · exact congrArg Proportion.vector
      (Proportion.identity_mul proportion.toNonNullProportion.toProportion)

/-- The identity ray is an exact right identity for multiplication. -/
@[simp] theorem mul_identity (proportion : RayProportion F) :
    RayProportion.mul proportion RayProportion.identity = proportion := by
  apply RayProportion.ext
  apply NonNullProportion.ext (K := F)
  · exact congrArg Proportion.scalar
      (Proportion.mul_identity proportion.toNonNullProportion.toProportion)
  · exact congrArg Proportion.vector
      (Proportion.mul_identity proportion.toNonNullProportion.toProportion)

/-- Conjugate the retained non-null proportion to obtain the ray inverse representative. -/
@[expose] def conjugate (proportion : RayProportion F) :
  RayProportion F :=
  ⟨NonNullProportion.conjugate proportion.toNonNullProportion⟩

end

open Purelib.Algebra.Quaternion.Ray.Basic in
open Purelib.Algebra.Quaternion in
/-- The original proportion retained by every ray has positive norm. -/
theorem norm_positive (proportion : RayProportion F) :
    0 < proportion.toNonNullProportion.toProportion.norm :=
  Ray.Basic.proportion_norm_pos_of_isNonzero _ proportion.toNonNullProportion.isNonzero

open Purelib.Algebra.Quaternion.Ray.Basic
/-- A ray times its conjugate is positively equivalent to the identity.

The original positive norm supplies the homogeneous factor. -/
theorem mul_conjugate_equivalent_identity (proportion :
  RayProportion F) :
    (RayProportion.mul proportion proportion.conjugate).Equivalent RayProportion.identity := by
  apply RayProportion.equivalent_symm
  refine ⟨proportion.toNonNullProportion.toProportion.norm,
    proportion.norm_positive, ?_⟩
  exact Proportion.mul_conjugate proportion.toNonNullProportion.toProportion

/-- A conjugate times its original ray is positively equivalent to the identity.

The original positive norm supplies the homogeneous factor. -/
theorem conjugate_mul_equivalent_identity (proportion :
  RayProportion F) :
    (RayProportion.mul proportion.conjugate proportion).Equivalent RayProportion.identity := by
  apply RayProportion.equivalent_symm
  refine ⟨proportion.toNonNullProportion.toProportion.norm,
    proportion.norm_positive, ?_⟩
  exact Proportion.conjugate_mul proportion.toNonNullProportion.toProportion

end RayProportion

open Purelib.Algebra.Quaternion.Ray.Basic in
set_option genInjectivity false in
/-- Retain quaternion group laws on ray representatives modulo positive scaling.

Associativity and identity hold exactly, while left and right inverse laws retain ray equivalences with the stored
identity. -/
structure RayProportionGroupLaws (F : Type*) [RayOrderedExplicitField F]
  where
  /-- The retained identity ray representative. -/ identity : RayProportion F
  /-- The retained inverse representative operation. -/ inverse : RayProportion F → RayProportion F
  /-- The ray representative product is exactly associative. -/ associative : ∀ first second third : RayProportion F,
    RayProportion.mul (RayProportion.mul first second) third =
      RayProportion.mul first (RayProportion.mul second third)
  /-- The retained identity is an exact left identity. -/ leftIdentity : ∀ proportion : RayProportion F,
    RayProportion.mul identity proportion = proportion
  /-- The retained identity is an exact right identity. -/ rightIdentity : ∀ proportion : RayProportion F,
    RayProportion.mul proportion identity = proportion
  /-- An inverse times its original ray is positively equivalent to the identity. -/ leftInverse : ∀ proportion :
    RayProportion F,
    (RayProportion.mul (inverse proportion) proportion).Equivalent identity
  /-- A ray times its inverse is positively equivalent to the identity. -/ rightInverse : ∀ proportion : RayProportion
    F,
    (RayProportion.mul proportion (inverse proportion)).Equivalent identity
  /-- Multiplication respects positive-scale equivalence in both inputs. -/ respectsEquivalent :
    ∀ {left left' right right' : RayProportion F},
      left.Equivalent left' → right.Equivalent right' →
        (RayProportion.mul left right).Equivalent
          (RayProportion.mul left' right')

constructive_injectivity Purelib.Algebra.Quaternion.Ray.Basic.RayProportionGroupLaws

open Purelib.Algebra.Quaternion.Ray.Basic in
/-- Assemble the ray group laws with unit representative and conjugation inverse.

The construction retains exact coordinate multiplication and the positive-scale equivalence certificates. -/
@[expose] def rayProportionGroupLaws : RayProportionGroupLaws F where
  identity := RayProportion.identity
  inverse := RayProportion.conjugate
  associative := RayProportion.mul_assoc
  leftIdentity := RayProportion.identity_mul
  rightIdentity := RayProportion.mul_identity
  leftInverse := RayProportion.conjugate_mul_equivalent_identity
  rightInverse := RayProportion.mul_conjugate_equivalent_identity
  respectsEquivalent := RayProportion.mul_respects_equivalent

namespace RayProportion

open Purelib.Algebra.Quaternion.Ray.Basic in
/-- Positive ray equivalence implies ordinary nonzero-scale projective equivalence. -/
theorem projectivelyEquivalent_of_equivalent {left right :
  RayProportion F}
    (equivalent : left.Equivalent right) :
    left.toNonNullProportion.Equivalent right.toNonNullProportion := by
  rcases equivalent with ⟨factor, factorPositive, rightValue⟩
  exact ⟨factor,
    RayOrderedExplicitField.positive_ne_zero_direct factorPositive,
    rightValue⟩

open Purelib.Algebra.Quaternion.Ray.Basic
/-- Projectively equivalent representatives lie on the same ray or on opposite rays.

The retained nonzero scale is split into its positive or negative sign by the ray-order decision. -/
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

/-- The opposite of the unit ray, represented by scalar negative one and zero vector. -/
@[expose] def negativeIdentity : RayProportion F :=
  RayProportion.neg RayProportion.identity

/-- The negative identity ray is not positively equivalent to the identity. -/
theorem negativeIdentity_distinct :
    ¬ (RayProportion.identity : RayProportion F).Equivalent RayProportion.negativeIdentity :=
  RayProportion.not_equivalent_neg (RayProportion.identity : RayProportion F)

/-- The negative identity ray squares exactly to the identity representative. -/
theorem negativeIdentity_square :
    RayProportion.mul (RayProportion.negativeIdentity : RayProportion F) RayProportion.negativeIdentity =
      RayProportion.identity := open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3 in by
  have raw : Proportion.mul
      (Proportion.scale (-1) Proportion.identity)
      (Proportion.scale (-1) Proportion.identity) =
      (Proportion.identity : Proportion F) := by
    apply Proportion.ext
    · unfold Proportion.mul Proportion.scale Proportion.identity
        Vector3.zero Vector3.scale Vector3.dot
      ring1
    · apply Vector3.ext <;>
        unfold Proportion.mul Proportion.scale Proportion.identity Vector3.zero
          Vector3.scale Vector3.dot Vector3.sub Vector3.add Vector3.cross <;> ring1
  apply RayProportion.ext
  apply NonNullProportion.ext (K := F)
  · exact congrArg Proportion.scalar raw
  · exact congrArg Proportion.vector raw

/-- Multiplication by the negative identity negates every ray representative on either side. -/
theorem negativeIdentity_central (proportion : RayProportion
  F) :
    RayProportion.mul RayProportion.negativeIdentity proportion = proportion.neg ∧
      RayProportion.mul proportion RayProportion.negativeIdentity = proportion.neg := open
        Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3 in by
  have leftRaw :
      Proportion.mul (Proportion.scale (-1) Proportion.identity)
          proportion.toNonNullProportion.toProportion =
        Proportion.scale (-1)
          proportion.toNonNullProportion.toProportion := by
    apply Proportion.ext
    · unfold Proportion.mul Proportion.scale Proportion.identity Vector3.zero
        Vector3.scale Vector3.dot
      ring1
    · apply Vector3.ext <;>
        unfold Proportion.mul Proportion.scale Proportion.identity Vector3.zero
          Vector3.scale Vector3.dot Vector3.sub Vector3.add Vector3.cross <;> ring1
  have rightRaw :
      Proportion.mul proportion.toNonNullProportion.toProportion
          (Proportion.scale (-1) Proportion.identity) =
        Proportion.scale (-1)
          proportion.toNonNullProportion.toProportion := by
    apply Proportion.ext
    · unfold Proportion.mul Proportion.scale Proportion.identity Vector3.zero
        Vector3.scale Vector3.dot
      ring1
    · apply Vector3.ext <;>
        unfold Proportion.mul Proportion.scale Proportion.identity Vector3.zero
          Vector3.scale Vector3.dot Vector3.sub Vector3.add Vector3.cross <;> ring1
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

open Purelib.Algebra.Quaternion.Ray.Basic in
open Purelib.Algebra.Quaternion in
/-- Instantiate the retained ray group laws over the executable rational field.

The rational ray-order instance supplies the sign and positivity decisions without normalizing coordinates to unit norm.
-/
@[expose] def groupLaws : RayProportionGroupLaws
  Fraction.Rational := Ray.Basic.rayProportionGroupLaws

end RationalRayModel

end Purelib.Algebra.Quaternion.Ray.Basic

end
