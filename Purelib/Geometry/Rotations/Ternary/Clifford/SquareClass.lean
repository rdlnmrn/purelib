module

public import Purelib.Algebra.Clifford.Ternary.SquareClass
public import Purelib.Geometry.Rotations.Ternary.Clifford
import Purelib.Geometry.Rotations.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Square classes of displayed ternary rotations

The executable projective correspondence retains one original non-null
Clifford preimage. Its reduced norm represents the rotation's invariant;
every other preimage agrees through an explicit square factor.
-/

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.SpecialOrthogonal

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.SquareClass.Basic (SquareClassRepresentative)
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)
open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] [DecidableEq K] {form : TernaryForm K}

/-- Retain a rotation's reduced-norm square class through its original executable Clifford preimage.

The representative and nonzero certificate belong to the same cached
preimage supplied by the projective correspondence. No canonical square
class or quotient representative is selected.
-/
@[expose] def quadranceClass (rotation : form.SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0) :
    SquareClassRepresentative K :=
  NonNullEvenClifford.normClass ((form.projectiveCliffordCorrespondence twoNonzero).preimage rotation)

/-- Every original Clifford representative of a rotation has the same reduced-norm square class.

Projective faithfulness supplies the actual nonzero factor relating the
cached preimage to the given original representative. Its square is the
retained witness of this invariant's independence.
-/
theorem quadranceClass_action (value : form.NonNullEvenClifford) (twoNonzero : (2 : K) ≠ 0) :
    (quadranceClass (NonNullEvenClifford.actionRotation value) twoNonzero).Equivalent
      (NonNullEvenClifford.normClass value) := by
  apply NonNullEvenClifford.normClass_respects_equivalent
  apply (form.projectiveCliffordCorrespondence twoNonzero).action_eq_iff_equivalent _ _ |>.mp
  exact (form.projectiveCliffordCorrespondence twoNonzero).action_preimage
    (NonNullEvenClifford.actionRotation value)

/-- The quadrance class of a product is the product of the two original rotation classes.

The two retained preimages are multiplied in the original Clifford owner.
Its exact action and norm multiplication laws identify the product class
with an explicit square-factor equivalence.
-/
theorem quadranceClass_mul (left right : form.SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0) :
    (quadranceClass (SpecialOrthogonal.mul left right) twoNonzero).Equivalent
      (SquareClassRepresentative.mul (quadranceClass left twoNonzero) (quadranceClass right twoNonzero)) := by
  let correspondence := form.projectiveCliffordCorrespondence twoNonzero
  let leftValue := correspondence.preimage left
  let rightValue := correspondence.preimage right
  have actionProduct : NonNullEvenClifford.actionRotation (NonNullEvenClifford.mul leftValue rightValue) =
      SpecialOrthogonal.mul left right := by
    rw [NonNullEvenClifford.actionRotation_mul, correspondence.action_preimage, correspondence.action_preimage]
  have classes := quadranceClass_action (NonNullEvenClifford.mul leftValue rightValue) twoNonzero
  rw [actionProduct, NonNullEvenClifford.normClass_mul] at classes
  exact classes

/-- A displayed rotation has a unit-norm Clifford preimage exactly when its quadrance class is trivial.

The reverse construction rescales the same retained executable preimage
by the supplied nonzero square-class factor. Projective invariance proves
that this original Clifford owner still acts as the requested rotation.
-/
theorem unitNormPreimage_iff (rotation : form.SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0) :
    (∃ value : form.NonNullEvenClifford,
      NonNullEvenClifford.actionRotation value = rotation ∧ EvenClifford.norm value.toEvenClifford = 1) ↔
      (quadranceClass rotation twoNonzero).Equivalent ⟨1, form.one_ne_zero⟩ := by
  constructor
  · rintro ⟨value, represents, normOne⟩
    have classes := quadranceClass_action value twoNonzero
    rw [represents] at classes
    apply SquareClassRepresentative.equivalent_trans classes
    refine ⟨1, form.one_ne_zero, ?_⟩
    change 1 = 1 ^ 2 * EvenClifford.norm value.toEvenClifford
    rw [normOne, one_pow, one_mul]
  · intro trivial
    let value := (form.projectiveCliffordCorrespondence twoNonzero).preimage rotation
    rcases (NonNullEvenClifford.unitNormScale_iff value).mpr trivial with ⟨factor, factorNonzero, normOne⟩
    refine ⟨NonNullEvenClifford.scale factor factorNonzero value, ?_, normOne⟩
    exact (NonNullEvenClifford.actionRotation_respects_equivalent
      (NonNullEvenClifford.equivalent_scale factor factorNonzero value)).symm.trans
      ((form.projectiveCliffordCorrespondence twoNonzero).action_preimage rotation)

/-- The quadrance class of two reflections is the square class of the product of their normal quadrances.

The original two pure-vector Clifford representatives give the same
certified reflection product. Their norm product has an extra square
of the form determinant, removed by its retained nonzero inverse factor.
-/
theorem quadranceClass_reflectionProduct (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    ((form.reflectionProductRotation first second firstNonNull secondNonNull).quadranceClass twoNonzero).Equivalent
      ⟨form.quadrance first * form.quadrance second, ExplicitField.mul_ne_zero firstNonNull secondNonNull⟩ := by
  let left := NonNullEvenClifford.halfTurnValue form first firstNonNull
  let right := NonNullEvenClifford.halfTurnValue form second secondNonNull
  have represents : NonNullEvenClifford.actionRotation (NonNullEvenClifford.mul left right) =
      form.reflectionProductRotation first second firstNonNull secondNonNull :=
    (NonNullEvenClifford.halfTurnRotation_mul form first second firstNonNull secondNonNull).symm.trans
      (form.halfTurnRotation_mul first second firstNonNull secondNonNull)
  have classes := quadranceClass_action (NonNullEvenClifford.mul left right) twoNonzero
  rw [represents] at classes
  apply SquareClassRepresentative.equivalent_trans classes
  refine ⟨form.determinant⁻¹, ExplicitField.inv_ne_zero form.determinantNonzero, ?_⟩
  change form.quadrance first * form.quadrance second =
    form.determinant⁻¹ ^ 2 * EvenClifford.norm (EvenClifford.mul left.toEvenClifford right.toEvenClifford)
  rw [EvenClifford.norm_mul, NonNullEvenClifford.halfTurnValue_norm,
    NonNullEvenClifford.halfTurnValue_norm]
  calc
    _ = (form.determinant * form.determinant⁻¹) ^ 2 *
        (form.quadrance first * form.quadrance second) := by
      rw [ExplicitField.mul_inv_cancel _ form.determinantNonzero, one_pow, one_mul]
    _ = _ := by ring1

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm.SpecialOrthogonal

namespace Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)
open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm

variable {K : Type*} [ExplicitField K] [DecidableEq K] {form : TernaryForm K}

/-- A relative rotation has a unit-norm preimage exactly when its retained input norm classes agree.

The transformation is the inverse of the original left action followed
by the original right action. Projective faithfulness transports any
unit preimage to the same conjugate-left Clifford product.
-/
theorem unitNormRelativePreimage_iff (left right : form.NonNullEvenClifford)
    (twoNonzero : (2 : K) ≠ 0) :
    (∃ value : form.NonNullEvenClifford,
      actionRotation value = SpecialOrthogonal.mul
        (SpecialOrthogonal.inverse (actionRotation left)) (actionRotation right) ∧
      EvenClifford.norm value.toEvenClifford = 1) ↔
      (normClass left).Equivalent (normClass right) := by
  let relative := mul (conjugate left) right
  have relativeActs : actionRotation relative = SpecialOrthogonal.mul
      (SpecialOrthogonal.inverse (actionRotation left)) (actionRotation right) := by
    rw [actionRotation_mul, actionRotation_conjugate]
  constructor
  · rintro ⟨value, represents, normOne⟩
    have equivalent : Equivalent relative value :=
      ((form.projectiveCliffordCorrespondence twoNonzero).action_eq_iff_equivalent relative value).mp
        (relativeActs.trans represents.symm)
    rcases normClass_respects_equivalent equivalent with ⟨factor, factorNonzero, equal⟩
    have relativeUnit : EvenClifford.norm (EvenClifford.scale factor relative.toEvenClifford) = 1 := by
      rw [EvenClifford.norm_scale]
      change EvenClifford.norm value.toEvenClifford =
        factor ^ 2 * EvenClifford.norm relative.toEvenClifford at equal
      exact equal.symm.trans normOne
    exact (unitNormRelativeScale_iff left right).mp ⟨factor, factorNonzero, relativeUnit⟩
  · intro sameClass
    rcases (unitNormRelativeScale_iff left right).mpr sameClass with ⟨factor, factorNonzero, normOne⟩
    refine ⟨scale factor factorNonzero relative, ?_, normOne⟩
    exact (actionRotation_respects_equivalent (equivalent_scale factor factorNonzero relative)).symm.trans
      relativeActs

end Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm.NonNullEvenClifford
