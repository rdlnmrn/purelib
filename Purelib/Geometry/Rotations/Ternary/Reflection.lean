module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Geometry.Rotations.Ternary.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quadratic.Ternary.Basic
public import Purelib.Algebra.Quadratic.Ternary.Minkowski
import Purelib.Geometry.Quadratic.Ternary.Isometry
public import Purelib.Geometry.Quadratic.Ternary.Reflection
import Purelib.LinearAlgebra.Coordinates3.Vector
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Constructive displayed ternary forms

This module begins the finite coordinate-algebra part of Problem 71.  A form
stores its displayed symmetric matrix together with cached determinant,
adjugate, and inverse data.  The certificates connect every cached value to
the canonical fixed-size matrix calculation, so downstream executable code
does not repeat those calculations or recover an inverse by choice.
-/

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section

set_option genInjectivity false in
/-- Cached first Cartan--Dieudonne reduction for a displayed rotation. A supplied non-null seed with non-null
displacement determines a reflection which sends its image back to the seed; composing on the right therefore produces
an orientation-reversing isometry fixing that seed. -/
structure DisplacementReflectionReduction (form :
  Ternary.Basic.TernaryForm K)
    (rotation : form.SpecialOrthogonal) where
  /-- The retained vector used for the first reflection reduction. -/ seed : Coordinates3.Vector K
  /-- The retained seed has nonzero form quadrance. -/ seedNonNull : form.quadrance seed ≠ 0
  /-- The retained reflection normal. -/ mirror : Coordinates3.Vector K
  /-- The normal is exactly the displacement of the seed under the input rotation. -/ mirror_eq : mirror =
    Coordinates3.Vector.sub ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act rotation.toIsometry) seed) seed
  /-- The displacement normal has nonzero form quadrance. -/ mirrorNonNull : form.quadrance mirror ≠ 0
  /-- The cached isometry after composing the input rotation with the displacement reflection. -/ reduced :
    form.Isometry
  /-- The cached result is the stated row-order product with the retained reflection. -/ reduced_eq : reduced =
    Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.mul rotation.toIsometry
    (form.reflectionIsometry mirror mirrorNonNull)
  /-- The reduced isometry fixes the original seed. -/
  seedFixed : Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act reduced seed = seed
  /-- The reduced isometry has determinant minus one. -/ determinantMinusOne : Matrix3.determinant reduced.matrix = -1

constructive_injectivity DisplacementReflectionReduction

/-- Execute the first reflection reduction from the supplied finite denominator certificates. -/
def displacementReflectionReduction (form :
  Ternary.Basic.TernaryForm K)
    (rotation : form.SpecialOrthogonal) (seed : Coordinates3.Vector K)
    (seedNonNull : form.quadrance seed ≠ 0)
    (displacementNonNull :
      form.quadrance (Coordinates3.Vector.sub ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
          rotation.toIsometry) seed) seed) ≠ 0) :
    DisplacementReflectionReduction form rotation where
  seed := seed
  seedNonNull := seedNonNull
  mirror := Coordinates3.Vector.sub ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act rotation.toIsometry)
      seed) seed
  mirror_eq := rfl
  mirrorNonNull := displacementNonNull
  reduced := Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.mul rotation.toIsometry
    (form.reflectionIsometry (Coordinates3.Vector.sub ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
        rotation.toIsometry) seed) seed)
      displacementNonNull)
  reduced_eq := rfl
  seedFixed := by
    rw [Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act_mul]
    change Matrix3.rowMul ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act rotation.toIsometry) seed)
      (form.reflection (Coordinates3.Vector.sub ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
          rotation.toIsometry) seed) seed)
        displacementNonNull) = seed
    apply form.rowMul_reflection_difference
    exact (SpecialOrthogonal.quadrance_act rotation) seed
  determinantMinusOne := by
    change Matrix3.determinant
      (Matrix3.mul rotation.matrix
        (form.reflection (Coordinates3.Vector.sub ((Algebra.Quadratic.Ternary.Basic.TernaryForm.Isometry.act
            rotation.toIsometry) seed) seed)
          displacementNonNull)) = -1
    rw [Matrix3.determinant_mul, rotation.determinantOne,
      form.determinant_reflection, one_mul]

/-- Form-relative half turn about a non-null axis. -/
def halfTurn (form : Ternary.Basic.TernaryForm K) (vector :
  Coordinates3.Vector K)
    (nonNull : form.quadrance vector ≠ 0) : Coordinates3.Matrix3 K :=
  Matrix3.neg (form.reflection vector nonNull)

/-- The form-relative half turn squares to the identity matrix. -/
theorem halfTurn_square (form : Ternary.Basic.TernaryForm K)
  (vector : Coordinates3.Vector K)
    (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.mul (form.halfTurn vector nonNull)
      (form.halfTurn vector nonNull) = Matrix3.identity := by
  unfold TernaryForm.halfTurn
  rw [Matrix3.mul_neg_neg, form.reflection_square]

/-- The form-relative half turn preserves the displayed ternary form. -/
theorem halfTurn_preservesMatrix (form :
  Ternary.Basic.TernaryForm K)
    (vector : Coordinates3.Vector K) (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.mul (Matrix3.mul (form.halfTurn vector nonNull) form.matrix)
        (Matrix3.transpose (form.halfTurn vector nonNull)) =
      form.matrix := by
  unfold TernaryForm.halfTurn
  rw [Matrix3.transpose_neg]
  calc
    Matrix3.mul
        (Matrix3.mul (Matrix3.neg (form.reflection vector nonNull)) form.matrix)
        (Matrix3.neg
          (Matrix3.transpose (form.reflection vector nonNull))) =
      Matrix3.mul
        (Matrix3.mul (form.reflection vector nonNull) form.matrix)
        (Matrix3.transpose (form.reflection vector nonNull)) := by
      ext <;> unfold Matrix3.mul Matrix3.neg <;> ring1
    _ = form.matrix := form.reflection_preservesMatrix vector nonNull

/-- The form-relative half turn has determinant one. -/
theorem determinant_halfTurn (form :
  Ternary.Basic.TernaryForm K) (vector : Coordinates3.Vector K)
    (nonNull : form.quadrance vector ≠ 0) :
    Matrix3.determinant (form.halfTurn vector nonNull) = 1 := by
  unfold TernaryForm.halfTurn
  rw [Matrix3.determinant_neg, form.determinant_reflection]
  ring1

/-- The form-relative half turn packaged as a determinant-one isometry. -/
def halfTurnRotation (form : Ternary.Basic.TernaryForm K)
  (vector : Coordinates3.Vector K)
    (nonNull : form.quadrance vector ≠ 0) : form.SpecialOrthogonal where
  matrix := form.halfTurn vector nonNull
  inverseMatrix := form.halfTurn vector nonNull
  matrix_mul_inverse := form.halfTurn_square vector nonNull
  inverse_mul_matrix := form.halfTurn_square vector nonNull
  preservesMatrix := form.halfTurn_preservesMatrix vector nonNull
  determinantOne := form.determinant_halfTurn vector nonNull

/-- Exact coordinate evaluation of a Minkowski half turn. -/
theorem minkowski_coordinate_halfTurn (oneNonzero : (1 : K) ≠
  0) :
    (TernaryForm.minkowski oneNonzero).halfTurn (⟨1, 0, 0⟩ : Coordinates3.Vector K) (by
      intro quadranceZero
      apply oneNonzero
      calc
        (1 : K) =
            (TernaryForm.minkowski oneNonzero).quadrance (⟨1, 0, 0⟩ : Coordinates3.Vector K) := by
          rw [TernaryForm.quadrance_minkowski]
          ring1
        _ = 0 := quadranceZero) =
      (⟨1, 0, 0, 0, -1, 0, 0, 0, -1⟩ : Coordinates3.Matrix3 K) := by
  let axis : Coordinates3.Vector K := ⟨1, 0, 0⟩
  have axisQuadrance :
      (TernaryForm.minkowski oneNonzero).quadrance axis = (1 : K) := by
    rw [TernaryForm.quadrance_minkowski]
    unfold axis
    ring1
  have oneInverse : ((1 : K)⁻¹) = 1 := by
    calc
      (1 : K)⁻¹ = 1 * (1 : K)⁻¹ := by rw [one_mul]
      _ = 1 := Algebra.Field.ExplicitField.mul_inv_cancel 1 oneNonzero
  change (TernaryForm.minkowski oneNonzero).halfTurn axis _ = _
  unfold TernaryForm.halfTurn TernaryForm.reflection
  rw [axisQuadrance]
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  rw [oneInverse]
  ext <;> unfold TernaryForm.dual TernaryForm.minkowski TernaryForm.ofMatrix Matrix3.neg Matrix3.sub
    Matrix3.identity Matrix3.scale Matrix3.outer Matrix3.rowMul axis <;> ring1

end

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

end

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Field
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- A half turn doubles the normal projection and subtracts the input vector. -/
theorem rowMul_halfTurn (form : TernaryForm K) (axis : Vector3 K)
    (nonNull : form.quadrance axis ≠ 0) (vector : Vector3 K) :
    Matrix3.rowMul vector (form.halfTurn axis nonNull) =
      Vector3.sub (Vector3.scale (2 * form.bilinear vector axis / form.quadrance axis) axis) vector := by
  unfold halfTurn
  rw [Matrix3.rowMul_neg, form.rowMul_reflection]
  ext <;> unfold Vector3.neg Vector3.sub Vector3.scale <;> ring1

/-- A half turn fixes its non-null axis vector. -/
theorem rowMul_self_halfTurn (form : TernaryForm K) (axis : Vector3 K)
    (nonNull : form.quadrance axis ≠ 0) :
    Matrix3.rowMul axis (form.halfTurn axis nonNull) = axis := by
  unfold halfTurn
  rw [Matrix3.rowMul_neg, form.rowMul_self_reflection, Vector3.neg_neg]

/-- A half turn negates every vector perpendicular to its axis. -/
theorem rowMul_halfTurn_of_perpendicular (form : TernaryForm K) (axis : Vector3 K)
    (nonNull : form.quadrance axis ≠ 0) (vector : Vector3 K) (perpendicular : form.Perpendicular vector axis) :
    Matrix3.rowMul vector (form.halfTurn axis nonNull) = Vector3.neg vector := by
  unfold halfTurn
  rw [Matrix3.rowMul_neg, form.rowMul_reflection_of_perpendicular axis nonNull vector perpendicular]

/-- The fixed vectors of a half turn are exactly their explicit projections onto its axis.

Nonzero two cancels the doubled-vector equation. The resulting projection
coefficient is the original pairing divided by the retained non-null quadrance.
-/
theorem rowMul_halfTurn_eq_self_iff_projection (form : TernaryForm K) (axis : Vector3 K)
    (nonNull : form.quadrance axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) (vector : Vector3 K) :
    Matrix3.rowMul vector (form.halfTurn axis nonNull) = vector ↔
      vector = Vector3.scale (form.bilinear vector axis / form.quadrance axis) axis := by
  constructor
  · intro fixed
    rw [form.rowMul_halfTurn] at fixed
    have doubled :
        Vector3.scale 2 (Vector3.scale (form.bilinear vector axis / form.quadrance axis) axis) =
          Vector3.scale 2 vector := by
      calc
        _ = Vector3.add
            (Vector3.sub (Vector3.scale (2 * form.bilinear vector axis / form.quadrance axis) axis) vector)
            vector := by
          ext <;> unfold Vector3.scale Vector3.add Vector3.sub <;>
            simp only [ExplicitField.div_eq_mul_inv] <;> ring1
        _ = Vector3.add vector vector := congrArg (fun value => Vector3.add value vector) fixed
        _ = _ := by ext <;> unfold Vector3.add Vector3.scale <;> ring1
    exact (Vector3.eq_of_scale_eq_scale twoNonzero doubled).symm
  · intro projected
    have fixedScaled (scalar : K) :
        Matrix3.rowMul (Vector3.scale scalar axis) (form.halfTurn axis nonNull) =
          Vector3.scale scalar axis := by
      rw [Matrix3.rowMul_vector_scale, form.rowMul_self_halfTurn]
    rw [projected]
    exact fixedScaled _

/-- A half turn is uniquely determined by fixing its axis and negating the perpendicular plane.

The denominator-free perpendicular projection reconstructs every vector after
scaling by the axis quadrance. Cancelling that nonzero scalar determines all rows.
-/
theorem halfTurn_unique (form : TernaryForm K) (axis : Vector3 K)
    (nonNull : form.quadrance axis ≠ 0) (matrix : Matrix3 K)
    (fixesAxis : Matrix3.rowMul axis matrix = axis)
    (negatesPerpendicular : ∀ vector : Vector3 K, form.Perpendicular vector axis →
      Matrix3.rowMul vector matrix = Vector3.neg vector) :
    matrix = form.halfTurn axis nonNull := by
  apply Matrix3.eq_of_rowMul_eq
  intro vector
  apply Vector3.eq_of_scale_eq_scale nonNull
  calc
    _ = Matrix3.rowMul (Vector3.scale (form.quadrance axis) vector) matrix :=
      (Matrix3.rowMul_vector_scale _ _ _).symm
    _ = Matrix3.rowMul
        (Vector3.add (form.perpendicularProjection axis vector)
          (Vector3.scale (form.bilinear vector axis) axis)) matrix := by
      rw [form.perpendicularProjection_reconstruct]
    _ = Vector3.add (Vector3.neg (form.perpendicularProjection axis vector))
        (Vector3.scale (form.bilinear vector axis) axis) := by
      rw [Matrix3.rowMul_vector_add, Matrix3.rowMul_vector_scale, fixesAxis,
        negatesPerpendicular _ (form.perpendicularProjection_perpendicular axis vector)]
    _ = Matrix3.rowMul
        (Vector3.add (form.perpendicularProjection axis vector)
          (Vector3.scale (form.bilinear vector axis) axis)) (form.halfTurn axis nonNull) := by
      rw [Matrix3.rowMul_vector_add, Matrix3.rowMul_vector_scale, form.rowMul_self_halfTurn,
        form.rowMul_halfTurn_of_perpendicular axis nonNull _
          (form.perpendicularProjection_perpendicular axis vector)]
    _ = Matrix3.rowMul (Vector3.scale (form.quadrance axis) vector) (form.halfTurn axis nonNull) := by
      rw [form.perpendicularProjection_reconstruct]
    _ = _ := Matrix3.rowMul_vector_scale _ _ _

/-- Nonzero rescaling of an axis preserves its half turn. -/
theorem halfTurn_scale (form : TernaryForm K) (scalar : K) (axis : Vector3 K)
    (scalarNonzero : scalar ≠ 0) (nonNull : form.quadrance axis ≠ 0) :
    form.halfTurn (Vector3.scale scalar axis)
        (form.quadrance_scale_ne_zero scalar axis scalarNonzero nonNull) =
      form.halfTurn axis nonNull := by
  unfold halfTurn
  rw [form.reflection_scale scalar axis scalarNonzero nonNull]

/-- Equal half turns have the same non-null axis line, and conversely.

The forward implication retains the scalar obtained by projecting the second
axis onto the first. Its nonzero certificate follows from the second quadrance.
-/
theorem halfTurn_eq_iff_same_line (form : TernaryForm K) (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    form.halfTurn first firstNonNull = form.halfTurn second secondNonNull ↔
      ∃ scalar : K, scalar ≠ 0 ∧ second = Vector3.scale scalar first := by
  constructor
  · intro equal
    have fixed : Matrix3.rowMul second (form.halfTurn first firstNonNull) = second := by
      rw [equal, form.rowMul_self_halfTurn]
    have projected := (form.rowMul_halfTurn_eq_self_iff_projection first firstNonNull twoNonzero second).mp fixed
    refine ⟨form.bilinear second first / form.quadrance first, ?_, projected⟩
    intro zeroCoefficient
    apply secondNonNull
    rw [projected, zeroCoefficient]
    have zeroScale : Vector3.scale (0 : K) first = Vector3.zero := by
      ext <;> unfold Vector3.scale Vector3.zero <;> ring1
    rw [zeroScale, form.quadrance_zero]
  · rintro ⟨scalar, scalarNonzero, scaled⟩
    subst second
    exact (form.halfTurn_scale scalar first scalarNonzero firstNonNull).symm

/-- Compose two reflections as a certified rotation of the original displayed form.

The isometry product retains the two original reflection matrices and
their reversed product as its inverse. Their determinant-minus-one
certificates give determinant one for the result.
-/
@[expose] def reflectionProductRotation (form : TernaryForm K) (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0) :
    form.SpecialOrthogonal where
  toIsometry := Isometry.mul (form.reflectionIsometry first firstNonNull)
    (form.reflectionIsometry second secondNonNull)
  determinantOne := by
    change Matrix3.determinant (Matrix3.mul (form.reflection first firstNonNull)
      (form.reflection second secondNonNull)) = 1
    rw [Matrix3.determinant_mul, form.determinant_reflection, form.determinant_reflection]
    ring1

/-- A product of two half turns equals the rotation constructed from their two reflections. -/
theorem halfTurnRotation_mul (form : TernaryForm K) (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0) :
    SpecialOrthogonal.mul (form.halfTurnRotation first firstNonNull)
        (form.halfTurnRotation second secondNonNull) =
      form.reflectionProductRotation first second firstNonNull secondNonNull := by
  apply SpecialOrthogonal.eq_of_matrix_eq
  change Matrix3.mul (form.halfTurn first firstNonNull) (form.halfTurn second secondNonNull) = _
  unfold halfTurn
  exact Matrix3.mul_neg_neg _ _

/-- Independently rescaling two non-null normals preserves their original reflection-product rotation.

The two supplied nonzero scale certificates preserve the original normal
quadrances. Each reflection is unchanged, so their ordered product has
the same forward matrix and hence the same certified rotation owner.
-/
theorem reflectionProductRotation_scale (form : TernaryForm K) (leftScale rightScale : K)
    (first second : Vector3 K) (leftNonzero : leftScale ≠ 0) (rightNonzero : rightScale ≠ 0)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0) :
    form.reflectionProductRotation (Vector3.scale leftScale first) (Vector3.scale rightScale second)
        (form.quadrance_scale_ne_zero leftScale first leftNonzero firstNonNull)
        (form.quadrance_scale_ne_zero rightScale second rightNonzero secondNonNull) =
      form.reflectionProductRotation first second firstNonNull secondNonNull := by
  apply SpecialOrthogonal.eq_of_matrix_eq
  change Matrix3.mul
    (form.reflection (Vector3.scale leftScale first)
      (form.quadrance_scale_ne_zero leftScale first leftNonzero firstNonNull))
    (form.reflection (Vector3.scale rightScale second)
      (form.quadrance_scale_ne_zero rightScale second rightNonzero secondNonNull)) =
    Matrix3.mul (form.reflection first firstNonNull) (form.reflection second secondNonNull)
  rw [form.reflection_scale leftScale first leftNonzero firstNonNull,
    form.reflection_scale rightScale second rightNonzero secondNonNull]

/-- Equal non-null reflections have exactly the same normal line, and conversely.

Negating the two reflection matrices gives their half turns. Their exact
fixed-line characterization retains a nonzero scale between the normals.
-/
theorem reflection_eq_iff_same_line (form : TernaryForm K) (first second : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (secondNonNull : form.quadrance second ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    form.reflection first firstNonNull = form.reflection second secondNonNull ↔
      ∃ scalar : K, scalar ≠ 0 ∧ second = Vector3.scale scalar first := by
  constructor
  · intro equal
    apply (form.halfTurn_eq_iff_same_line first second firstNonNull secondNonNull twoNonzero).mp
    exact congrArg Matrix3.neg equal
  · intro sameLine
    have equal := (form.halfTurn_eq_iff_same_line first second firstNonNull secondNonNull twoNonzero).mpr sameLine
    have negEqual := congrArg Matrix3.neg equal
    change Matrix3.neg (Matrix3.neg (form.reflection first firstNonNull)) =
      Matrix3.neg (Matrix3.neg (form.reflection second secondNonNull)) at negEqual
    have doubleNeg (matrix : Matrix3 K) : Matrix3.neg (Matrix3.neg matrix) = matrix := by
      ext <;> unfold Matrix3.neg <;> ring1
    rw [doubleNeg, doubleNeg] at negEqual
    exact negEqual

/-- A fixed first reflection determines the second normal line of its product uniquely.

Left multiplication by the first reflection cancels it using its involution
law. The retained second reflection then determines its non-null normal line.
-/
theorem reflectionProduct_secondLine_unique (form : TernaryForm K) (first left right : Vector3 K)
    (firstNonNull : form.quadrance first ≠ 0) (leftNonNull : form.quadrance left ≠ 0)
    (rightNonNull : form.quadrance right ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (sameProduct : form.reflectionProductRotation first left firstNonNull leftNonNull =
      form.reflectionProductRotation first right firstNonNull rightNonNull) :
    ∃ scalar : K, scalar ≠ 0 ∧ right = Vector3.scale scalar left := by
  have matrixEqual := congrArg (fun rotation : form.SpecialOrthogonal => rotation.matrix) sameProduct
  change Matrix3.mul (form.reflection first firstNonNull) (form.reflection left leftNonNull) =
    Matrix3.mul (form.reflection first firstNonNull) (form.reflection right rightNonNull) at matrixEqual
  have cancelled := congrArg (Matrix3.mul (form.reflection first firstNonNull)) matrixEqual
  rw [← Matrix3.mul_assoc, form.reflection_square, Matrix3.identity_mul,
    ← Matrix3.mul_assoc, form.reflection_square, Matrix3.identity_mul] at cancelled
  exact (form.reflection_eq_iff_same_line left right leftNonNull rightNonNull twoNonzero).mp cancelled

/-- Equal non-null axes give equal original half-turn rotations with their respective certificates. -/
theorem halfTurnRotation_eq_of_axis_eq (form : TernaryForm K) (left right : Vector3 K)
    (leftNonNull : form.quadrance left ≠ 0) (rightNonNull : form.quadrance right ≠ 0)
    (equal : left = right) : form.halfTurnRotation left leftNonNull = form.halfTurnRotation right rightNonNull := by
  cases equal
  rfl

/-- Reversing a non-null axis preserves its original certified half turn. -/
theorem halfTurnRotation_neg (form : TernaryForm K) (axis : Vector3 K)
    (nonNull : form.quadrance axis ≠ 0) :
    form.halfTurnRotation (Vector3.neg axis) (by rw [form.quadrance_neg]; exact nonNull) =
      form.halfTurnRotation axis nonNull := by
  apply Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
  change form.halfTurn (Vector3.neg axis) _ = form.halfTurn axis nonNull
  unfold TernaryForm.halfTurn
  rw [form.reflection_neg]

/-- The row space of identity plus a half turn consists of explicit scalar multiples of its original axis. -/
theorem rowMul_identity_add_halfTurn (form : TernaryForm K) (axis input : Vector3 K)
    (nonNull : form.quadrance axis ≠ 0) :
    Matrix3.rowMul input (Matrix3.add Matrix3.identity (form.halfTurn axis nonNull)) =
      Vector3.scale (2 * form.bilinear input axis / form.quadrance axis) axis := by
  rw [Matrix3.rowMul_add, Matrix3.rowMul_identity, form.rowMul_halfTurn]
  ext <;> unfold Vector3.add Vector3.sub Vector3.scale <;> ring1

/-- Every nonzero vector in the row space of identity plus a half turn is non-null.

The exact projection coefficient is nonzero because the output is nonzero.
Its square multiplies the original non-null axis quadrance, supplying the
retained output certificate without a new choice of axis.
-/
theorem quadrance_rowMul_identity_add_halfTurn_ne_zero (form : TernaryForm K) (axis input : Vector3 K)
    (nonNull : form.quadrance axis ≠ 0)
    (nonzero : Matrix3.rowMul input (Matrix3.add Matrix3.identity (form.halfTurn axis nonNull)) ≠ Vector3.zero) :
    form.quadrance (Matrix3.rowMul input (Matrix3.add Matrix3.identity (form.halfTurn axis nonNull))) ≠ 0 := by
  have coefficientNonzero : 2 * form.bilinear input axis / form.quadrance axis ≠ 0 := by
    intro coefficientZero
    apply nonzero
    rw [form.rowMul_identity_add_halfTurn, coefficientZero, Vector3.zero_scale]
  rw [form.rowMul_identity_add_halfTurn]
  exact form.quadrance_scale_ne_zero _ axis coefficientNonzero nonNull

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm
