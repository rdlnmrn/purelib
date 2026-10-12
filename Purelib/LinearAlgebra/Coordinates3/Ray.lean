module

public import Purelib.LinearAlgebra.Coordinates3.Vector
public import Purelib.Algebra.Field.ExplicitOrder.Sign
import Purelib.Tactic.Ring

/-!
# Positive rays of displayed three-dimensional vectors

The original vector coordinates retain the positive scale witnessing ray
equivalence. Every nonzero scalar line has its same-ray and opposite-ray
alternatives, and a nonzero vector's opposite ray is distinct.
-/

public section

namespace Purelib.LinearAlgebra.Coordinates3.Vector

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Basic (OrderedExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign (RayOrderedExplicitField)

variable {K : Type*} [RayOrderedExplicitField K]

/-- Use the equality decision retained by the original ordered field. -/
local instance : DecidableEq K := OrderedExplicitField.eq_decidable

/-- Two original displayed vectors differ by a retained positive scalar. -/
@[expose] def RayEquivalent (left right : Vector K) : Prop :=
  ∃ factor : K, 0 < factor ∧ right = scale factor left

/-- The unit scale represents each original vector's own ray. -/
theorem rayEquivalent_refl (value : Vector K) : RayEquivalent value value := by
  refine ⟨1, OrderedExplicitField.zero_lt_one_direct, ?_⟩
  exact (Vector.ext (one_mul _) (one_mul _) (one_mul _)).symm

/-- Reverse the original positive ray scale by its positive reciprocal. -/
theorem rayEquivalent_symm {left right : Vector K} (equivalent : RayEquivalent left right) :
    RayEquivalent right left := by
  rcases equivalent with ⟨factor, positive, equal⟩
  have cancel : factor⁻¹ * factor = 1 := by
    rw [mul_comm, ExplicitField.mul_inv_cancel _
      (RayOrderedExplicitField.positive_ne_zero_direct positive)]
  refine ⟨factor⁻¹, OrderedExplicitField.inv_pos_direct positive, ?_⟩
  rw [equal, scale_scale, cancel]
  exact (Vector.ext (one_mul _) (one_mul _) (one_mul _)).symm

/-- Compose the original positive ray scales by their positive product. -/
theorem rayEquivalent_trans {first second third : Vector K}
    (firstSecond : RayEquivalent first second) (secondThird : RayEquivalent second third) :
    RayEquivalent first third := by
  rcases firstSecond with ⟨firstFactor, firstPositive, firstEq⟩
  rcases secondThird with ⟨secondFactor, secondPositive, secondEq⟩
  refine ⟨secondFactor * firstFactor, OrderedExplicitField.mul_pos_direct secondPositive firstPositive, ?_⟩
  rw [secondEq, firstEq, scale_scale]

/-- Equal homogeneous scalings of an original nonzero vector have equal scalar factors. -/
theorem scale_factor_injective (value : Vector K) (nonzero : value ≠ zero) {left right : K}
    (equal : scale left value = scale right value) : left = right := by
  by_cases timeZero : value.t = 0
  · by_cases firstZero : value.r = 0
    · by_cases secondZero : value.s = 0
      · exact (nonzero (Vector.ext timeZero firstZero secondZero)).elim
      · exact RayOrderedExplicitField.eq_of_mul_right_eq secondZero (congrArg Vector.s equal)
    · exact RayOrderedExplicitField.eq_of_mul_right_eq firstZero (congrArg Vector.r equal)
  · exact RayOrderedExplicitField.eq_of_mul_right_eq timeZero (congrArg Vector.t equal)

/-- A nonzero scalar preserves nonzeroness of the original vector. -/
theorem scale_nonzero {factor : K} (factorNonzero : factor ≠ 0) {value : Vector K}
    (valueNonzero : value ≠ zero) : scale factor value ≠ zero := by
  intro scaledZero
  have scaled : scale factor value = scale factor zero := by
    calc
      _ = zero := scaledZero
      _ = scale factor zero := (Vector.ext (mul_zero _) (mul_zero _) (mul_zero _)).symm
  exact valueNonzero (eq_of_scale_eq_scale factorNonzero scaled)

/-- A nonzero original vector belongs to a scaled vector's ray precisely when the scale is positive. -/
theorem rayEquivalent_scale_iff (value : Vector K) (nonzero : value ≠ zero) (factor : K) :
    RayEquivalent value (scale factor value) ↔ 0 < factor := by
  constructor
  · rintro ⟨retained, positive, equal⟩
    have factors := scale_factor_injective value nonzero equal
    rw [factors]
    exact positive
  · intro positive
    exact ⟨factor, positive, rfl⟩

/-- An original nonzero vector's positive ray is distinct from the ray of its negative. -/
theorem not_rayEquivalent_neg (value : Vector K) (nonzero : value ≠ zero) :
    ¬ RayEquivalent value (neg value) := by
  have negative : neg value = scale (-1) value := by
    apply Vector.ext <;> change -_ = (-1 : K) * _ <;> ring1
  intro equivalent
  rw [negative] at equivalent
  exact RayOrderedExplicitField.positive_neg_exclusive_direct OrderedExplicitField.zero_lt_one_direct
    ((rayEquivalent_scale_iff value nonzero (-1)).mp equivalent)

/-- A retained nonzero line scale gives precisely the same-ray or opposite-ray alternatives. -/
theorem lineScale_iff_rayEquivalent_or_neg (left right : Vector K) :
    (∃ factor : K, factor ≠ 0 ∧ right = scale factor left) ↔
      RayEquivalent left right ∨ RayEquivalent (neg left) right := by
  constructor
  · rintro ⟨factor, factorNonzero, equal⟩
    rcases RayOrderedExplicitField.sign_split_direct factor factorNonzero with positive | negative
    · exact Or.inl ⟨factor, positive, equal⟩
    · right
      refine ⟨-factor, negative, ?_⟩
      calc
        right = scale factor left := equal
        _ = scale (-factor) (neg left) := by
          apply Vector.ext <;> change factor * _ = -factor * (-_) <;> ring1
  · rintro (same | opposite)
    · rcases same with ⟨factor, positive, equal⟩
      exact ⟨factor, RayOrderedExplicitField.positive_ne_zero_direct positive, equal⟩
    · rcases opposite with ⟨factor, positive, equal⟩
      refine ⟨-factor, ?_, ?_⟩
      · intro zero
        have original := congrArg (fun value : K => -value) zero
        rw [_root_.neg_neg, _root_.neg_zero] at original
        exact RayOrderedExplicitField.positive_ne_zero_direct positive original
      · calc
          right = scale factor (neg left) := equal
          _ = scale (-factor) left := by
            apply Vector.ext <;> change factor * (-_) = -factor * _ <;> ring1

end Purelib.LinearAlgebra.Coordinates3.Vector
