module

public import Purelib.Algebra.Clifford.Ternary.Ray
public import Purelib.Geometry.Rotations.Ternary.Clifford
import Purelib.Geometry.Rotations.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField

/-!
# Oriented Clifford rays over the original rotation group

The original Clifford action maps positive rays onto every original
special-orthogonal rotation of the retained ternary form. Each fiber is
exactly one ray and its distinct opposite, including the two scalar rays
over the identity. All preimages use the original constructive correspondence.
-/

public section

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Basic (OrderedExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign (RayOrderedExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)
open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm

variable {K : Type*} [RayOrderedExplicitField K] {form : TernaryForm K}

/-- Use the equality decision retained by the supplied ordered field. -/
local instance : DecidableEq K := OrderedExplicitField.eq_decidable

/-- The original rotation action is unchanged by positive ray rescaling. -/
theorem actionRotation_respects_rayEquivalent {left right : form.NonNullEvenClifford}
    (equivalent : RayEquivalent left right) : actionRotation left = actionRotation right :=
  actionRotation_respects_equivalent (equivalent_of_rayEquivalent equivalent)

/-- Opposite original Clifford rays act as the same original rotation. -/
theorem actionRotation_neg (value : form.NonNullEvenClifford) : actionRotation (neg value) = actionRotation value :=
  (actionRotation_respects_equivalent (equivalent_scale (-1) RayOrderedExplicitField.neg_one_ne_zero value)).symm

/-- Equal original rotations have exactly the same-ray or opposite-ray alternatives. -/
theorem actionRotation_eq_iff_rayEquivalent_or_neg (left right : form.NonNullEvenClifford) :
    actionRotation left = actionRotation right ↔ RayEquivalent left right ∨ RayEquivalent (neg left) right :=
  (actionRotation_eq_iff_equivalent left right RayOrderedExplicitField.two_ne_zero).trans
    (equivalent_iff_rayEquivalent_or_neg left right)

/-- The two rays in each original rotation fiber have equal action and distinct positive ray classes. -/
theorem actionRotation_fiber_two_distinct_rays (value : form.NonNullEvenClifford) :
    actionRotation (neg value) = actionRotation value ∧ ¬ RayEquivalent value (neg value) :=
  ⟨actionRotation_neg value, not_rayEquivalent_neg value⟩

/-- Every original special-orthogonal rotation has an original non-null Clifford ray preimage.

The preimage is the one computed by the original finite two-reflection
correspondence, and its action agrees with the supplied rotation itself.
-/
theorem actionRotation_ray_surjective (rotation : form.SpecialOrthogonal) :
    ∃ value : form.NonNullEvenClifford, actionRotation value = rotation :=
  ⟨(form.projectiveCliffordCorrespondence RayOrderedExplicitField.two_ne_zero).preimage rotation,
    (form.projectiveCliffordCorrespondence RayOrderedExplicitField.two_ne_zero).action_preimage rotation⟩

/-- The original ray-action kernel consists exactly of the positive and negative scalar identity rays. -/
theorem actionRotation_eq_identity_iff_scalar_rays (value : form.NonNullEvenClifford) :
    actionRotation value = SpecialOrthogonal.identity form ↔
      RayEquivalent (identity form) value ∨ RayEquivalent (neg (identity form)) value := by
  constructor
  · intro acts
    exact (actionRotation_eq_iff_rayEquivalent_or_neg (identity form) value).mp
      ((actionRotation_identity form).trans acts.symm)
  · intro rays
    exact ((actionRotation_eq_iff_rayEquivalent_or_neg (identity form) value).mpr rays).symm.trans
      (actionRotation_identity form)

/-- The computed two-sided Clifford inverse acts as the original rotation's retained inverse. -/
theorem actionRotation_inverse (value : form.NonNullEvenClifford) :
    actionRotation (inverse value) = SpecialOrthogonal.inverse (actionRotation value) := by
  have equivalent : Equivalent (conjugate value) (inverse value) :=
    ⟨(EvenClifford.norm value.toEvenClifford)⁻¹, ExplicitField.inv_ne_zero value.normNonzero, rfl⟩
  exact (actionRotation_respects_equivalent equivalent).symm.trans (actionRotation_conjugate value)

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford
