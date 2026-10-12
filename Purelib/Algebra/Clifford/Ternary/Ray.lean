module

import Purelib.Algebra.Clifford.Ternary.Basic
public import Purelib.Algebra.Clifford.Ternary.SquareClass
public import Purelib.Algebra.Field.ExplicitOrder.Sign
import Purelib.Algebra.Field.Squares
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Oriented rays of non-null ternary Clifford representatives

The original form-indexed representative remains the owner of every scalar,
vector and norm certificate. Positive homogeneous scales define ray equality.
The original Clifford product and computed two-sided inverse descend through
this relation even when the reduced norm is negative.
-/

public section

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Basic (OrderedExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign (RayOrderedExplicitField)
open Purelib.Algebra.Field.Squares (eq_or_eq_neg_of_square_eq)
open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section Inversion

variable {K : Type*} [ExplicitField K] {form : TernaryForm K}

/-- Compute the original non-null Clifford representative's certified two-sided inverse.

The original conjugate-over-norm procedure computes the retained inverse.
Its exact product with the input is the identity, which also certifies the
inverse's nonzero norm without choosing any coordinates or roots.
-/
@[expose] def inverse (value : form.NonNullEvenClifford) : form.NonNullEvenClifford :=
  let retained := EvenClifford.inverse value.toEvenClifford value.normNonzero
  { toEvenClifford := retained
    normNonzero := by
      intro normZero
      have productNorm := congrArg EvenClifford.norm
        (EvenClifford.mul_inverse value.toEvenClifford value.normNonzero)
      rw [EvenClifford.norm_mul, EvenClifford.norm_identity, normZero, mul_zero] at productNorm
      exact form.one_ne_zero productNorm.symm }

/-- Multiplication by the computed original inverse on the right gives the original identity representative. -/
theorem mul_inverse (value : form.NonNullEvenClifford) : mul value (inverse value) = identity form := by
  have raw := EvenClifford.mul_inverse value.toEvenClifford value.normNonzero
  exact TernaryForm.NonNullEvenClifford.ext
    (congrArg TernaryForm.EvenClifford.scalar raw) (congrArg TernaryForm.EvenClifford.vector raw)

/-- Multiplication by the computed original inverse on the left gives the original identity representative. -/
theorem inverse_mul (value : form.NonNullEvenClifford) : mul (inverse value) value = identity form := by
  have raw := EvenClifford.inverse_mul value.toEvenClifford value.normNonzero
  exact TernaryForm.NonNullEvenClifford.ext
    (congrArg TernaryForm.EvenClifford.scalar raw) (congrArg TernaryForm.EvenClifford.vector raw)

/-- Inverting a nonzero homogeneous rescaling multiplies the original inverse by the reciprocal scale. -/
theorem inverse_scale (factor : K) (factorNonzero : factor ≠ 0) (value : form.NonNullEvenClifford) :
    inverse (scale factor factorNonzero value) =
      scale factor⁻¹ (ExplicitField.inv_ne_zero factorNonzero) (inverse value) := by
  let scaled := scale factor factorNonzero value
  let candidate := scale factor⁻¹ (ExplicitField.inv_ne_zero factorNonzero) (inverse value)
  have product : mul scaled candidate = identity form := by
    have raw : EvenClifford.mul scaled.toEvenClifford candidate.toEvenClifford = EvenClifford.identity form := by
      change EvenClifford.mul (EvenClifford.scale factor value.toEvenClifford)
        (EvenClifford.scale factor⁻¹ (inverse value).toEvenClifford) = _
      rw [EvenClifford.mul_scale_both, ExplicitField.mul_inv_cancel _ factorNonzero,
        EvenClifford.one_scale]
      exact EvenClifford.mul_inverse value.toEvenClifford value.normNonzero
    exact TernaryForm.NonNullEvenClifford.ext
      (congrArg TernaryForm.EvenClifford.scalar raw) (congrArg TernaryForm.EvenClifford.vector raw)
  calc
    inverse scaled = mul (inverse scaled) (identity form) := (mul_identity _).symm
    _ = mul (inverse scaled) (mul scaled candidate) := congrArg (mul (inverse scaled)) product.symm
    _ = mul (mul (inverse scaled) scaled) candidate := (mul_assoc _ _ _).symm
    _ = candidate := by rw [inverse_mul, identity_mul]

end Inversion

section Rays

variable {K : Type*} [RayOrderedExplicitField K] {form : TernaryForm K}

/-- Use the equality decision retained by the original ordered field. -/
local instance : DecidableEq K := OrderedExplicitField.eq_decidable

/-- The two original non-null Clifford representatives differ by a retained positive homogeneous scale. -/
@[expose] def RayEquivalent (left right : form.NonNullEvenClifford) : Prop :=
  ∃ factor : K, 0 < factor ∧ right.toEvenClifford = EvenClifford.scale factor left.toEvenClifford

/-- Positive ray equivalence supplies the same original projective equivalence and scale. -/
theorem equivalent_of_rayEquivalent {left right : form.NonNullEvenClifford}
    (equivalent : RayEquivalent left right) : Equivalent left right := by
  rcases equivalent with ⟨factor, positive, equal⟩
  exact ⟨factor, RayOrderedExplicitField.positive_ne_zero_direct positive, equal⟩

/-- Unit homogeneous scale represents each original ray itself. -/
theorem rayEquivalent_refl (value : form.NonNullEvenClifford) : RayEquivalent value value :=
  ⟨1, OrderedExplicitField.zero_lt_one_direct, (EvenClifford.one_scale _).symm⟩

/-- Reverse a retained positive ray scale by its positive reciprocal. -/
theorem rayEquivalent_symm {left right : form.NonNullEvenClifford}
    (equivalent : RayEquivalent left right) : RayEquivalent right left := by
  rcases equivalent with ⟨factor, positive, equal⟩
  have factorNonzero := RayOrderedExplicitField.positive_ne_zero_direct positive
  have cancel : factor⁻¹ * factor = 1 := by
    rw [mul_comm, ExplicitField.mul_inv_cancel _ factorNonzero]
  refine ⟨factor⁻¹, OrderedExplicitField.inv_pos_direct positive, ?_⟩
  rw [equal, EvenClifford.scale_scale, cancel, EvenClifford.one_scale]

/-- Compose retained ray scales by their positive product. -/
theorem rayEquivalent_trans {first second third : form.NonNullEvenClifford}
    (firstSecond : RayEquivalent first second) (secondThird : RayEquivalent second third) :
    RayEquivalent first third := by
  rcases firstSecond with ⟨firstFactor, firstPositive, firstEq⟩
  rcases secondThird with ⟨secondFactor, secondPositive, secondEq⟩
  refine ⟨secondFactor * firstFactor, OrderedExplicitField.mul_pos_direct secondPositive firstPositive, ?_⟩
  rw [secondEq, firstEq, EvenClifford.scale_scale]

/-- Negate the original non-null Clifford coordinates to represent the opposite oriented ray. -/
@[expose] def neg (value : form.NonNullEvenClifford) : form.NonNullEvenClifford :=
  scale (-1) RayOrderedExplicitField.neg_one_ne_zero value

/-- Negating the original coordinates twice returns the same original representative. -/
theorem neg_neg (value : form.NonNullEvenClifford) : neg (neg value) = value := by
  have raw : (neg (neg value)).toEvenClifford = value.toEvenClifford := by
    change EvenClifford.scale (-1) (EvenClifford.scale (-1) value.toEvenClifford) = _
    have factorOne : (-1 : K) * (-1) = 1 := by ring1
    rw [EvenClifford.scale_scale, factorOne]
    exact EvenClifford.one_scale _
  exact TernaryForm.NonNullEvenClifford.ext
    (congrArg TernaryForm.EvenClifford.scalar raw) (congrArg TernaryForm.EvenClifford.vector raw)

/-- Equal rescalings of a non-null Clifford representative have equal scalar factors.

Finite coordinate equality decisions identify an original nonzero coordinate.
If all coordinates vanished, its original nonzero reduced norm would vanish.
-/
theorem scale_factor_injective (value : form.NonNullEvenClifford) {left right : K}
    (equal : EvenClifford.scale left value.toEvenClifford =
      EvenClifford.scale right value.toEvenClifford) : left = right := by
  by_cases scalarZero : value.scalar = 0
  · by_cases timeZero : value.vector.t = 0
    · by_cases firstZero : value.vector.r = 0
      · by_cases secondZero : value.vector.s = 0
        · have vectorZero : value.vector = Vector3.zero := Vector3.ext timeZero firstZero secondZero
          apply False.elim
          apply value.normNonzero
          change value.scalar ^ 2 + form.determinant * form.quadrance value.vector = 0
          rw [scalarZero, vectorZero, TernaryForm.quadrance_zero, mul_zero, add_zero, zero_pow (by decide)]
        · exact RayOrderedExplicitField.eq_of_mul_right_eq secondZero
            (congrArg (fun entry => entry.vector.s) equal)
      · exact RayOrderedExplicitField.eq_of_mul_right_eq firstZero
          (congrArg (fun entry => entry.vector.r) equal)
    · exact RayOrderedExplicitField.eq_of_mul_right_eq timeZero
        (congrArg (fun entry => entry.vector.t) equal)
  · exact RayOrderedExplicitField.eq_of_mul_right_eq scalarZero
      (congrArg TernaryForm.EvenClifford.scalar equal)

/-- An original non-null ray is distinct from its opposite ray under positive homogeneous equivalence. -/
theorem not_rayEquivalent_neg (value : form.NonNullEvenClifford) : ¬ RayEquivalent value (neg value) := by
  rintro ⟨factor, positive, equal⟩
  have factorEq : factor = -1 := scale_factor_injective value equal.symm
  have negOnePositive : 0 < (-1 : K) := by rw [← factorEq]; exact positive
  exact RayOrderedExplicitField.positive_neg_exclusive_direct OrderedExplicitField.zero_lt_one_direct negOnePositive

/-- Every original projective class has exactly the same-ray or opposite-ray alternatives. -/
theorem equivalent_iff_rayEquivalent_or_neg (left right : form.NonNullEvenClifford) :
    Equivalent left right ↔ RayEquivalent left right ∨ RayEquivalent (neg left) right := by
  constructor
  · rintro ⟨factor, factorNonzero, equal⟩
    rcases RayOrderedExplicitField.sign_split_direct factor factorNonzero with positive | negative
    · exact Or.inl ⟨factor, positive, equal⟩
    · right
      refine ⟨-factor, negative, ?_⟩
      change right.toEvenClifford = EvenClifford.scale (-factor) (EvenClifford.scale (-1) left.toEvenClifford)
      have factorEq : (-factor) * (-1) = factor := by ring1
      rw [EvenClifford.scale_scale, factorEq]
      exact equal
  · rintro (same | opposite)
    · exact equivalent_of_rayEquivalent same
    · exact equivalent_trans (equivalent_scale (-1) RayOrderedExplicitField.neg_one_ne_zero left)
        (equivalent_of_rayEquivalent opposite)

/-- The original Clifford product respects both retained positive ray scales. -/
theorem mul_respects_rayEquivalent {left left' right right' : form.NonNullEvenClifford}
    (leftEq : RayEquivalent left left') (rightEq : RayEquivalent right right') :
    RayEquivalent (mul left right) (mul left' right') := by
  rcases leftEq with ⟨leftFactor, leftPositive, leftValue⟩
  rcases rightEq with ⟨rightFactor, rightPositive, rightValue⟩
  refine ⟨leftFactor * rightFactor, OrderedExplicitField.mul_pos_direct leftPositive rightPositive, ?_⟩
  change EvenClifford.mul left'.toEvenClifford right'.toEvenClifford = _
  rw [leftValue, rightValue, EvenClifford.mul_scale_both]
  rfl

/-- The computed original two-sided inverse respects positive ray equivalence by the reciprocal positive scale. -/
theorem inverse_respects_rayEquivalent {left right : form.NonNullEvenClifford}
    (equivalent : RayEquivalent left right) : RayEquivalent (inverse left) (inverse right) := by
  rcases equivalent with ⟨factor, positive, equal⟩
  have factorNonzero := RayOrderedExplicitField.positive_ne_zero_direct positive
  have rightEq : right = scale factor factorNonzero left :=
    TernaryForm.NonNullEvenClifford.ext
      (congrArg TernaryForm.EvenClifford.scalar equal) (congrArg TernaryForm.EvenClifford.vector equal)
  refine ⟨factor⁻¹, OrderedExplicitField.inv_pos_direct positive, ?_⟩
  rw [rightEq, inverse_scale]
  rfl

/-- An original ray has a unit-norm representative exactly when its retained norm class is trivial.

The original projective normalizing factor is positive or has positive
negative. Negating it preserves its squared factor and therefore its unit
norm, while selecting the positive alternative keeps the same oriented ray.
-/
theorem ray_unitNormScale_iff (value : form.NonNullEvenClifford) :
    (∃ factor : K, 0 < factor ∧ EvenClifford.norm (EvenClifford.scale factor value.toEvenClifford) = 1) ↔
      (normClass value).Equivalent ⟨1, form.one_ne_zero⟩ := by
  constructor
  · rintro ⟨factor, positive, normOne⟩
    exact (unitNormScale_iff value).mp
      ⟨factor, RayOrderedExplicitField.positive_ne_zero_direct positive, normOne⟩
  · intro trivial
    rcases (unitNormScale_iff value).mpr trivial with ⟨factor, factorNonzero, normOne⟩
    rcases RayOrderedExplicitField.sign_split_direct factor factorNonzero with positive | negative
    · exact ⟨factor, positive, normOne⟩
    · refine ⟨-factor, negative, ?_⟩
      rw [EvenClifford.norm_scale] at normOne ⊢
      have factorSquare : (-factor) ^ 2 = factor ^ 2 := by ring1
      rw [factorSquare]
      exact normOne

/-- Two unit-norm original representatives on the same positive ray are equal.

Their retained norms force the positive homogeneous factor to square to one.
The opposite-root alternative contradicts positivity, so the factor is one
and the original scalar and vector coordinates agree.
-/
theorem eq_of_rayEquivalent_norm_one {left right : form.NonNullEvenClifford}
    (leftNorm : EvenClifford.norm left.toEvenClifford = 1)
    (rightNorm : EvenClifford.norm right.toEvenClifford = 1)
    (equivalent : RayEquivalent left right) : left = right := by
  rcases equivalent with ⟨factor, positive, equal⟩
  have factorSquare : factor ^ 2 = (1 : K) ^ 2 := by
    have normEq := congrArg EvenClifford.norm equal
    rw [EvenClifford.norm_scale, leftNorm, rightNorm, mul_one] at normEq
    exact normEq.symm.trans (one_pow _).symm
  have factorOne : factor = 1 := by
    rcases eq_or_eq_neg_of_square_eq factorSquare with same | opposite
    · exact same
    · have negOnePositive : 0 < (-1 : K) := by rw [← opposite]; exact positive
      exact False.elim
        (RayOrderedExplicitField.positive_neg_exclusive_direct OrderedExplicitField.zero_lt_one_direct negOnePositive)
  rw [factorOne, EvenClifford.one_scale] at equal
  exact TernaryForm.NonNullEvenClifford.ext
    (congrArg TernaryForm.EvenClifford.scalar equal.symm) (congrArg TernaryForm.EvenClifford.vector equal.symm)

end Rays

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford
