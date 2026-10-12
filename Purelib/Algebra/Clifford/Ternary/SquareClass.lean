module

public import Purelib.Algebra.Clifford.Ternary.Basic
public import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

/-!
# Reduced-norm square classes of ternary Clifford representatives

The invariant retains the original non-null Clifford parent and its
exact norm certificate. Projective invariance uses the supplied nonzero
scale, and multiplication uses the original reduced-norm product law.
-/

public section

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.SquareClass.Basic (SquareClassRepresentative)
open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)

variable {K : Type*} [ExplicitField K] {form : TernaryForm K}

/-- Retain the reduced norm of an original non-null Clifford value as a square-class representative. -/
@[expose] def normClass (value : form.NonNullEvenClifford) : SquareClassRepresentative K :=
  ⟨EvenClifford.norm value.toEvenClifford, value.normNonzero⟩

/-- Explicit projective equivalence preserves the reduced-norm square class.

The original homogeneous factor also witnesses square-class equivalence:
its square multiplies the retained left norm to the retained right norm.
-/
theorem normClass_respects_equivalent {left right : form.NonNullEvenClifford}
    (equivalent : Equivalent left right) : (normClass left).Equivalent (normClass right) := by
  rcases equivalent with ⟨factor, factorNonzero, equal⟩
  refine ⟨factor, factorNonzero, ?_⟩
  change EvenClifford.norm right.toEvenClifford = factor ^ 2 * EvenClifford.norm left.toEvenClifford
  rw [equal, EvenClifford.norm_scale]

/-- Multiplication of original non-null Clifford representatives multiplies their exact norm classes. -/
theorem normClass_mul (left right : form.NonNullEvenClifford) :
    normClass (mul left right) = SquareClassRepresentative.mul (normClass left) (normClass right) := by
  apply SquareClassRepresentative.ext
  exact EvenClifford.norm_mul left.toEvenClifford right.toEvenClifford

/-- Conjugation preserves the exact retained reduced-norm square-class representative. -/
theorem normClass_conjugate (value : form.NonNullEvenClifford) :
    normClass (conjugate value) = normClass value := by
  apply SquareClassRepresentative.ext
  exact EvenClifford.norm_conjugate value.toEvenClifford

/-- A projective Clifford representative admits unit-norm scaling exactly when its norm class is trivial.

Both directions retain the same nonzero factor. The target unit class
uses the original form's unit nonzero certificate, and the scaled norm
is computed by the original Clifford scaling law.
-/
theorem unitNormScale_iff (value : form.NonNullEvenClifford) :
    (∃ factor : K, factor ≠ 0 ∧ EvenClifford.norm (EvenClifford.scale factor value.toEvenClifford) = 1) ↔
      (normClass value).Equivalent ⟨1, form.one_ne_zero⟩ := by
  constructor
  · rintro ⟨factor, factorNonzero, normOne⟩
    refine ⟨factor, factorNonzero, ?_⟩
    change 1 = factor ^ 2 * EvenClifford.norm value.toEvenClifford
    rw [EvenClifford.norm_scale] at normOne
    exact normOne.symm
  · rintro ⟨factor, factorNonzero, normOne⟩
    refine ⟨factor, factorNonzero, ?_⟩
    rw [EvenClifford.norm_scale]
    exact normOne.symm

/-- Unit normalization of a relative Clifford representative is equivalent to equality of its two norm classes.

The relative value is the original conjugate-left product. Each direction
retains a nonzero scalar built from the same input norms and the supplied
normalizing or square-class factor.
-/
theorem unitNormRelativeScale_iff (left right : form.NonNullEvenClifford) :
    (∃ factor : K, factor ≠ 0 ∧
      EvenClifford.norm (EvenClifford.scale factor
        (mul (conjugate left) right).toEvenClifford) = 1) ↔
      (normClass left).Equivalent (normClass right) := by
  constructor
  · rintro ⟨factor, factorNonzero, normOne⟩
    change EvenClifford.norm (EvenClifford.scale factor
      (EvenClifford.mul (EvenClifford.conjugate left.toEvenClifford) right.toEvenClifford)) = 1 at normOne
    rw [EvenClifford.norm_scale, EvenClifford.norm_mul,
      EvenClifford.norm_conjugate] at normOne
    refine ⟨factor * EvenClifford.norm right.toEvenClifford,
      ExplicitField.mul_ne_zero factorNonzero right.normNonzero, ?_⟩
    change EvenClifford.norm right.toEvenClifford =
      (factor * EvenClifford.norm right.toEvenClifford) ^ 2 *
        EvenClifford.norm left.toEvenClifford
    calc
      _ = 1 * EvenClifford.norm right.toEvenClifford := by ring1
      _ = (factor ^ 2 * (EvenClifford.norm left.toEvenClifford *
          EvenClifford.norm right.toEvenClifford)) *
          EvenClifford.norm right.toEvenClifford := by rw [normOne]
      _ = _ := by ring1
  · rintro ⟨factor, factorNonzero, sameClass⟩
    let normalizer := factor * EvenClifford.norm left.toEvenClifford
    have normalizerNonzero : normalizer ≠ 0 :=
      ExplicitField.mul_ne_zero factorNonzero left.normNonzero
    refine ⟨normalizer⁻¹, ExplicitField.inv_ne_zero normalizerNonzero, ?_⟩
    change EvenClifford.norm (EvenClifford.scale normalizer⁻¹
      (EvenClifford.mul (EvenClifford.conjugate left.toEvenClifford) right.toEvenClifford)) = 1
    rw [EvenClifford.norm_scale, EvenClifford.norm_mul, EvenClifford.norm_conjugate]
    change EvenClifford.norm right.toEvenClifford =
      factor ^ 2 * EvenClifford.norm left.toEvenClifford at sameClass
    calc
      _ = normalizer⁻¹ ^ 2 * normalizer ^ 2 := by
        rw [sameClass]
        unfold normalizer
        ring1
      _ = (normalizer * normalizer⁻¹) ^ 2 := by ring1
      _ = 1 := by rw [ExplicitField.mul_inv_cancel _ normalizerNonzero, one_pow]

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford
