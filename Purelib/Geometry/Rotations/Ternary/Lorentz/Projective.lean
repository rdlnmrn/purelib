module

public import Purelib.Algebra.Clifford.Lorentz.Matrix
public import Purelib.Geometry.Rotations.Ternary.Lorentz.Anchor
public import Purelib.Geometry.Rotations.Ternary.Cayley.HalfTurn
import Purelib.Algebra.Clifford.Ternary.Action
import Purelib.Algebra.Clifford.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Rotations.Ternary.Basic
import Purelib.Geometry.Rotations.Ternary.Clifford
import Purelib.Geometry.Quadratic.Ternary.Lorentz
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.LinearAlgebra.Coordinates2.Invertible
import Purelib.Tactic.Ring

/-!
# Projective Lorentz rotations in source coordinates

The source proportion `(x:v)` is the original non-null Clifford value
with coordinates `(x,-v)`. Its rotation retains the original form owner,
cached inverse and action certificates, including both affine charts.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Clifford.Lorentz
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry
open Purelib.Geometry.Rotations.Ternary
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)

/-- Rotate by a non-null source proportion in the original Lorentz Clifford owner.

The supplied certificate retains the scalar square plus the original
source vector quadrance as nonzero. Both the rotation matrix and its
cached inverse are those of the original Clifford action.
-/
@[expose] def proportionRotation (scalar : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0) :
    (Form.lorentz oneNonzero).SpecialOrthogonal :=
  NonNullEvenClifford.actionRotation (Matrix.nonNullCoordinates oneNonzero scalar vector defined)

/-- The source proportion matrix has the original quadratic anchor formula.

Its denominator is the exact source norm. The scalar part multiplies
the original signed anchor, and the anchor square supplies the remaining
quadratic term; no affine scalar normalization is required.
-/
theorem proportionRotation_matrix (scalar : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0) :
    (proportionRotation oneNonzero scalar vector defined).matrix =
      Matrix3.add Matrix3.identity
        (Matrix3.scale (2 / (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector))
          (Matrix3.add (Matrix3.scale scalar (Quadratic.Ternary.Lorentz.anchor oneNonzero vector))
            (Matrix3.mul (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)
              (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)))) := by
  let value := Matrix.nonNullCoordinates oneNonzero scalar vector defined
  change NonNullEvenClifford.actionMatrix value = _
  unfold NonNullEvenClifford.actionMatrix
  rw [EvenClifford.actionNumeratorMatrix_eq_quadratic]
  dsimp only [value, Matrix.nonNullCoordinates]
  rw [Matrix.norm_coordinates_quadrance]
  change Matrix3.scale (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹
    (Matrix3.add (Matrix3.add
      (Matrix3.scale (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector) Matrix3.identity)
      (Matrix3.scale (2 * scalar) (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)))
      (Matrix3.scale 2 (Matrix3.mul (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)
        (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)))) = _
  have cancellation : (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹ *
      (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector) = 1 :=
    (mul_comm _ _).trans (ExplicitField.mul_inv_cancel _ defined)
  rw [Matrix3.scale_add, Matrix3.scale_add, Matrix3.scale_scale, cancellation, Matrix3.one_scale]
  ext <;> unfold Matrix3.add Matrix3.scale Matrix3.identity <;>
    simp only [ExplicitField.div_eq_mul_inv] <;> ring1

/-- The scalar-one source chart is the original Lorentz cap rotation. -/
theorem proportionRotation_one (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) :
    proportionRotation oneNonzero 1 vector (by
      intro normZero
      apply defined
      calc
        capDenominator oneNonzero vector = 1 ^ 2 + (Form.lorentz oneNonzero).quadrance vector := by
          unfold capDenominator
          ring1
        _ = 0 := normZero) = capRotation oneNonzero vector defined := rfl

/-- The scalar-zero source chart is the original half turn about its non-null vector line. -/
theorem proportionRotation_zero (vector : Vector3 K)
    (nonNull : (Form.lorentz oneNonzero).quadrance vector ≠ 0) :
    proportionRotation oneNonzero 0 vector (by
      intro normZero
      apply nonNull
      calc
        (Form.lorentz oneNonzero).quadrance vector = 0 ^ 2 +
            (Form.lorentz oneNonzero).quadrance vector := by ring1
        _ = 0 := normZero) = (Form.lorentz oneNonzero).halfTurnRotation vector nonNull := by
  let value := Matrix.nonNullCoordinates oneNonzero 0 vector (by
    intro normZero
    apply nonNull
    calc
      (Form.lorentz oneNonzero).quadrance vector = 0 ^ 2 +
          (Form.lorentz oneNonzero).quadrance vector := by ring1
      _ = 0 := normZero)
  have halfTurn := Cayley.TernaryForm.NonNullEvenClifford.actionRotation_eq_halfTurn_of_scalar_eq_zero
    value (by rfl)
  exact halfTurn.trans ((Form.lorentz oneNonzero).halfTurnRotation_neg vector nonNull)

/-- The original source proportion half spread is its vector quadrance divided by its exact norm. -/
theorem halfSpread_proportionRotation (scalar : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
        (proportionRotation oneNonzero scalar vector defined) =
      (Form.lorentz oneNonzero).quadrance vector /
        (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector) := by
  unfold proportionRotation
  rw [Cayley.TernaryForm.NonNullEvenClifford.rotationHalfSpread_actionRotation _ twoNonzero]
  change (Form.lorentz oneNonzero).determinant * (Form.lorentz oneNonzero).quadrance (Vector3.neg vector) /
    EvenClifford.norm (Matrix.coordinates oneNonzero scalar vector) = _
  rw [Form.lorentz_determinant, Form.quadrance_neg, one_mul, Matrix.norm_coordinates_quadrance]

/-- One minus the source proportion half spread is its scalar square divided by its exact norm. -/
theorem one_sub_halfSpread_proportionRotation (scalar : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    1 - Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
        (proportionRotation oneNonzero scalar vector defined) =
      scalar ^ 2 / (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector) := by
  rw [halfSpread_proportionRotation oneNonzero scalar vector defined twoNonzero]
  simp only [ExplicitField.div_eq_mul_inv]
  have cancellation := ExplicitField.mul_inv_cancel _ defined
  calc
    _ = (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector) *
        (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹ -
        (Form.lorentz oneNonzero).quadrance vector *
          (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹ := by rw [cancellation]
    _ = _ := by ring1

/-- Negating the source vector gives the retained inverse of its original proportion rotation. -/
theorem proportionRotation_conjugate (scalar : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0) :
    proportionRotation oneNonzero scalar (Vector3.neg vector) (by rw [Form.quadrance_neg]; exact defined) =
      Basic.TernaryForm.SpecialOrthogonal.inverse (proportionRotation oneNonzero scalar vector defined) :=
  NonNullEvenClifford.actionRotation_conjugate (Matrix.nonNullCoordinates oneNonzero scalar vector defined)

/-- The source projective product preserves the exact multiplicative norm.

The scalar pairing and signed cross product use the paper's row-action
order. This identity applies before any non-nullness certificates are
supplied, including scalar-zero and null-vector representatives.
-/
theorem proportionProduct_norm (leftScalar rightScalar : K) (leftVector rightVector : Vector3 K) :
    (leftScalar * rightScalar - (Form.lorentz oneNonzero).bilinear leftVector rightVector) ^ 2 +
      (Form.lorentz oneNonzero).quadrance
        (Vector3.sub (Vector3.add (Vector3.scale leftScalar rightVector) (Vector3.scale rightScalar leftVector))
          (Quadratic.Ternary.Lorentz.cross oneNonzero leftVector rightVector)) =
      (leftScalar ^ 2 + (Form.lorentz oneNonzero).quadrance leftVector) *
        (rightScalar ^ 2 + (Form.lorentz oneNonzero).quadrance rightVector) := by
  have productNorm := EvenClifford.norm_mul
    (Matrix.coordinates oneNonzero leftScalar leftVector)
    (Matrix.coordinates oneNonzero rightScalar rightVector)
  rw [Matrix.coordinates_mul, Matrix.norm_coordinates_quadrance,
    Matrix.norm_coordinates_quadrance, Matrix.norm_coordinates_quadrance] at productNorm
  exact productNorm

/-- Every product of non-null source proportions retains a non-null output norm. -/
theorem proportionProduct_nonzero (leftScalar rightScalar : K) (leftVector rightVector : Vector3 K)
    (leftDefined : leftScalar ^ 2 + (Form.lorentz oneNonzero).quadrance leftVector ≠ 0)
    (rightDefined : rightScalar ^ 2 + (Form.lorentz oneNonzero).quadrance rightVector ≠ 0) :
    (leftScalar * rightScalar - (Form.lorentz oneNonzero).bilinear leftVector rightVector) ^ 2 +
      (Form.lorentz oneNonzero).quadrance
        (Vector3.sub (Vector3.add (Vector3.scale leftScalar rightVector) (Vector3.scale rightScalar leftVector))
          (Quadratic.Ternary.Lorentz.cross oneNonzero leftVector rightVector)) ≠ 0 := by
  rw [proportionProduct_norm]
  exact ExplicitField.mul_ne_zero leftDefined rightDefined

/-- The source proportion product maps to the product of the original certified Lorentz rotations.

Its output certificate is obtained from the same retained input norms.
There is no exceptional pairing condition and no scalar normalization;
the scalar-zero product remains in the original projective action.
-/
theorem proportionRotation_mul (leftScalar rightScalar : K) (leftVector rightVector : Vector3 K)
    (leftDefined : leftScalar ^ 2 + (Form.lorentz oneNonzero).quadrance leftVector ≠ 0)
    (rightDefined : rightScalar ^ 2 + (Form.lorentz oneNonzero).quadrance rightVector ≠ 0) :
    proportionRotation oneNonzero
        (leftScalar * rightScalar - (Form.lorentz oneNonzero).bilinear leftVector rightVector)
        (Vector3.sub (Vector3.add (Vector3.scale leftScalar rightVector) (Vector3.scale rightScalar leftVector))
          (Quadratic.Ternary.Lorentz.cross oneNonzero leftVector rightVector))
        (proportionProduct_nonzero oneNonzero leftScalar rightScalar leftVector rightVector leftDefined rightDefined) =
      Basic.TernaryForm.SpecialOrthogonal.mul
        (proportionRotation oneNonzero leftScalar leftVector leftDefined)
        (proportionRotation oneNonzero rightScalar rightVector rightDefined) := by
  let left := Matrix.nonNullCoordinates oneNonzero leftScalar leftVector leftDefined
  let right := Matrix.nonNullCoordinates oneNonzero rightScalar rightVector rightDefined
  have productValue : (NonNullEvenClifford.mul left right).toEvenClifford =
      (Matrix.nonNullCoordinates oneNonzero
        (leftScalar * rightScalar - (Form.lorentz oneNonzero).bilinear leftVector rightVector)
        (Vector3.sub (Vector3.add (Vector3.scale leftScalar rightVector) (Vector3.scale rightScalar leftVector))
          (Quadratic.Ternary.Lorentz.cross oneNonzero leftVector rightVector))
        (proportionProduct_nonzero oneNonzero leftScalar rightScalar leftVector rightVector
          leftDefined rightDefined)).toEvenClifford :=
    Matrix.coordinates_mul oneNonzero leftScalar rightScalar leftVector rightVector
  have equivalent : NonNullEvenClifford.Equivalent (NonNullEvenClifford.mul left right)
      (Matrix.nonNullCoordinates oneNonzero
        (leftScalar * rightScalar - (Form.lorentz oneNonzero).bilinear leftVector rightVector)
        (Vector3.sub (Vector3.add (Vector3.scale leftScalar rightVector) (Vector3.scale rightScalar leftVector))
          (Quadratic.Ternary.Lorentz.cross oneNonzero leftVector rightVector))
        (proportionProduct_nonzero oneNonzero leftScalar rightScalar leftVector rightVector
          leftDefined rightDefined)) :=
    ⟨1, oneNonzero, by rw [EvenClifford.one_scale]; exact productValue.symm⟩
  exact (NonNullEvenClifford.actionRotation_respects_equivalent equivalent).symm.trans
    (NonNullEvenClifford.actionRotation_mul left right)

/-- Nonzero homogeneous rescaling preserves the non-null source norm certificate. -/
theorem proportionScale_nonzero (scalar factor : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0)
    (factorNonzero : factor ≠ 0) :
    (factor * scalar) ^ 2 + (Form.lorentz oneNonzero).quadrance (Vector3.scale factor vector) ≠ 0 := by
  rw [Form.quadrance_scale]
  have normScale : (factor * scalar) ^ 2 + factor ^ 2 * (Form.lorentz oneNonzero).quadrance vector =
      factor ^ 2 * (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector) := by ring1
  rw [normScale]
  exact ExplicitField.mul_ne_zero (ExplicitField.square_nonzero_of_nonzero factorNonzero) defined

/-- Homogeneous rescaling preserves the original source proportion rotation.

The equality is induced by the explicit nonzero scale on the original
Clifford parent, so its projective witness retains the same source vector
and non-nullness certificates.
-/
theorem proportionRotation_scale (scalar factor : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0)
    (factorNonzero : factor ≠ 0) :
    proportionRotation oneNonzero (factor * scalar) (Vector3.scale factor vector)
        (proportionScale_nonzero oneNonzero scalar factor vector defined factorNonzero) =
      proportionRotation oneNonzero scalar vector defined := by
  apply Eq.symm
  apply NonNullEvenClifford.actionRotation_respects_equivalent
  refine ⟨factor, factorNonzero, ?_⟩
  apply Form.EvenClifford.ext
  · rfl
  · ext <;> unfold Matrix.nonNullCoordinates Matrix.coordinates EvenClifford.scale Vector3.neg Vector3.scale <;> ring1

/-- Equality of source proportion rotations is exactly explicit nonzero homogeneous scaling.

Both the scalar and source vector use the same retained factor. The
criterion applies to every non-null representative, including the
scalar-zero half-turn chart, in characteristic different from two.
-/
theorem proportionRotation_eq_iff (leftScalar rightScalar : K) (leftVector rightVector : Vector3 K)
    (leftDefined : leftScalar ^ 2 + (Form.lorentz oneNonzero).quadrance leftVector ≠ 0)
    (rightDefined : rightScalar ^ 2 + (Form.lorentz oneNonzero).quadrance rightVector ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    proportionRotation oneNonzero leftScalar leftVector leftDefined =
        proportionRotation oneNonzero rightScalar rightVector rightDefined ↔
      ∃ factor : K, factor ≠ 0 ∧ rightScalar = factor * leftScalar ∧
        rightVector = Vector3.scale factor leftVector := by
  constructor
  · intro equal
    rcases (NonNullEvenClifford.actionRotation_eq_iff_equivalent
      (Matrix.nonNullCoordinates oneNonzero leftScalar leftVector leftDefined)
      (Matrix.nonNullCoordinates oneNonzero rightScalar rightVector rightDefined) twoNonzero).mp equal with
      ⟨factor, factorNonzero, scaled⟩
    refine ⟨factor, factorNonzero, congrArg Form.EvenClifford.scalar scaled, ?_⟩
    have vectors := congrArg Form.EvenClifford.vector scaled
    change Vector3.neg rightVector = Vector3.scale factor (Vector3.neg leftVector) at vectors
    have negated := congrArg Vector3.neg vectors
    rw [Vector3.neg_neg] at negated
    exact negated.trans (by ext <;> unfold Vector3.neg Vector3.scale <;> ring1)
  · rintro ⟨factor, factorNonzero, scalars, vectors⟩
    apply NonNullEvenClifford.actionRotation_respects_equivalent
    refine ⟨factor, factorNonzero, ?_⟩
    apply Form.EvenClifford.ext
    · exact scalars
    · change Vector3.neg rightVector = Vector3.scale factor (Vector3.neg leftVector)
      rw [vectors]
      ext <;> unfold Vector3.neg Vector3.scale <;> ring1

/-- Retain the original executable Clifford preimage of a source Lorentz rotation.

The finite two-half-turn construction supplies this original form-indexed
owner. Its scalar and negated vector are source proportion coordinates;
the cached norm and action equation remain on that same owner.
-/
@[expose] def rotationProportion [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) :
    (Form.lorentz oneNonzero).NonNullEvenClifford :=
  ((Form.lorentz oneNonzero).projectiveCliffordCorrespondence twoNonzero).preimage rotation

/-- The retained rotation preimage has a nonzero norm in its exact source coordinates. -/
theorem rotationProportion_nonzero [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) :
    (rotationProportion oneNonzero twoNonzero rotation).scalar ^ 2 +
      (Form.lorentz oneNonzero).quadrance
        (Vector3.neg (rotationProportion oneNonzero twoNonzero rotation).vector) ≠ 0 := by
  rw [Form.quadrance_neg]
  have normNonzero := (rotationProportion oneNonzero twoNonzero rotation).normNonzero
  unfold EvenClifford.norm at normNonzero
  rw [Form.lorentz_determinant, one_mul] at normNonzero
  exact normNonzero

/-- Reading the retained preimage as a source proportion reconstructs its original rotation.

The source readback negates the original Clifford vector without changing
its scalar, norm certificate or nominal form owner. This gives an
executable preimage for every displayed source Lorentz rotation.
-/
theorem proportionRotation_rotationProportion [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) :
    proportionRotation oneNonzero (rotationProportion oneNonzero twoNonzero rotation).scalar
        (Vector3.neg (rotationProportion oneNonzero twoNonzero rotation).vector)
        (rotationProportion_nonzero oneNonzero twoNonzero rotation) = rotation := by
  let value := rotationProportion oneNonzero twoNonzero rotation
  have equivalent : NonNullEvenClifford.Equivalent value
      (Matrix.nonNullCoordinates oneNonzero value.scalar (Vector3.neg value.vector)
        (rotationProportion_nonzero oneNonzero twoNonzero rotation)) := by
    refine ⟨1, oneNonzero, ?_⟩
    rw [EvenClifford.one_scale]
    apply Form.EvenClifford.ext
    · rfl
    · exact Vector3.neg_neg value.vector
  exact (NonNullEvenClifford.actionRotation_respects_equivalent equivalent).symm.trans
    (((Form.lorentz oneNonzero).projectiveCliffordCorrespondence twoNonzero).action_preimage rotation)

/-- The source sandwich computes row multiplication by the original proportion rotation.

Pure source dihedrons are embedded through the same signed coordinate
map as the acting representative. Scaling the retained conjugate sandwich
by its exact inverse norm yields another pure dihedron with the displayed
row-action vector.
-/
theorem proportionRotation_sandwich (scalar : K) (vector input : Vector3 K)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0) :
    Matrix.coordinates oneNonzero 0
        (Matrix3.rowMul input (proportionRotation oneNonzero scalar vector defined).matrix) =
      EvenClifford.scale (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹
        (EvenClifford.mul
          (EvenClifford.mul (EvenClifford.conjugate (Matrix.coordinates oneNonzero scalar vector))
            (Matrix.coordinates oneNonzero 0 input)) (Matrix.coordinates oneNonzero scalar vector)) := by
  let value := Matrix.nonNullCoordinates oneNonzero scalar vector defined
  change Matrix.coordinates oneNonzero 0 (Matrix3.rowMul input (NonNullEvenClifford.actionMatrix value)) = _
  rw [NonNullEvenClifford.rowMul_actionMatrix]
  change Matrix.coordinates oneNonzero 0 (NonNullEvenClifford.action value input) =
    EvenClifford.scale (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹
      (EvenClifford.mul
        (EvenClifford.mul (EvenClifford.conjugate value.toEvenClifford)
          (EvenClifford.ofVector (Form.lorentz oneNonzero) (Vector3.neg input))) value.toEvenClifford)
  rw [EvenClifford.conjugate_mul_ofVector_mul]
  apply Form.EvenClifford.ext
  · change 0 = (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹ * 0
    ring1
  · change Vector3.neg
        (Vector3.scale (EvenClifford.norm (Matrix.coordinates oneNonzero scalar vector))⁻¹
          (EvenClifford.actionNumerator value.toEvenClifford input)) =
      Vector3.scale (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹
        (EvenClifford.actionNumerator value.toEvenClifford (Vector3.neg input))
    rw [Matrix.norm_coordinates_quadrance]
    have negative : Vector3.neg input = Vector3.scale (-1) input := by
      ext <;> unfold Vector3.neg Vector3.scale <;> ring1
    rw [negative, EvenClifford.actionNumerator_scale_vector]
    ext <;> unfold Vector3.neg Vector3.scale <;> ring1

/-- The time entry of a proportion rotation is the sum of four squares divided by its exact norm.

The source time coordinate occupies the first row and column. Its anchor
entry vanishes, while the anchor-square entry is the sum of the two
spatial squares, giving the displayed numerator without normalization.
-/
theorem proportionRotation_timeEntry (scalar : K) (vector : Vector3 K)
    (defined : scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0) :
    (proportionRotation oneNonzero scalar vector defined).matrix.tt =
      (scalar ^ 2 + vector.t ^ 2 + vector.r ^ 2 + vector.s ^ 2) /
        (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector) := by
  rw [proportionRotation_matrix, Quadratic.Ternary.Lorentz.anchor_coordinates]
  dsimp only [Matrix3.add, Matrix3.scale, Matrix3.identity, Matrix3.mul]
  simp only [ExplicitField.div_eq_mul_inv]
  have cancellation := ExplicitField.mul_inv_cancel _ defined
  calc
    _ = (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector) *
        (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹ +
        (2 * (scalar ^ 2 + (Form.lorentz oneNonzero).quadrance vector)⁻¹) *
          ((scalar * 0) + (0 * 0 + vector.s * vector.s + -vector.r * -vector.r)) := by
      rw [cancellation]
    _ = _ := by rw [Form.quadrance_lorentz]; ring1

/-- Read the homogeneous inverse vector from twice a rotation's original antisymmetric part.

This source vector is defined without an affine denominator. In the cap
chart its anchor is twice the antisymmetric part, and its scalar partner
is one plus the trace of the original rotation matrix.
-/
@[expose] def projectiveInverseVector (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (twoNonzero : (2 : K) ≠ 0) : Vector3 K :=
  Quadratic.Ternary.Lorentz.anchorVector (Matrix3.scale 2 (rotation.antisymmetricPart twoNonzero))

/-- The homogeneous inverse vector is the computed affine anchor multiplied by one plus trace. -/
theorem projectiveInverseVector_eq_scale_anchor (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    projectiveInverseVector oneNonzero rotation twoNonzero =
      Vector3.scale rotation.anchorDenominator (rotationAnchorVector oneNonzero rotation defined) := by
  unfold projectiveInverseVector rotationAnchorVector
  rw [rotation.anchor_eq_antisymmetricPart defined twoNonzero,
    Quadratic.Ternary.Lorentz.anchorVector_scale, Quadratic.Ternary.Lorentz.anchorVector_scale,
    Vector3.scale_scale]
  have coefficient : rotation.anchorDenominator * (2 / rotation.anchorDenominator) = 2 := by
    rw [ExplicitField.div_eq_mul_inv]
    calc
      _ = 2 * (rotation.anchorDenominator * rotation.anchorDenominator⁻¹) := by ring1
      _ = 2 := by rw [ExplicitField.mul_inv_cancel _ defined, mul_one]
  rw [coefficient]

/-- The homogeneous inverse vector's source anchor is twice the original antisymmetric part.

The cap-chart trace denominator cancels its affine anchor normalization.
Both matrix operations retain the original rotation and its cached inverse.
-/
theorem anchor_projectiveInverseVector (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal)
    (defined : rotation.anchorDenominator ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Quadratic.Ternary.Lorentz.anchor oneNonzero (projectiveInverseVector oneNonzero rotation twoNonzero) =
      Matrix3.scale 2 (rotation.antisymmetricPart twoNonzero) := by
  rw [projectiveInverseVector_eq_scale_anchor oneNonzero rotation defined twoNonzero,
    Quadratic.Ternary.Lorentz.anchor_scale, anchor_rotationAnchorVector oneNonzero rotation defined twoNonzero,
    rotation.anchor_eq_antisymmetricPart defined twoNonzero, Matrix3.scale_scale]
  have coefficient : rotation.anchorDenominator * (2 / rotation.anchorDenominator) = 2 := by
    rw [ExplicitField.div_eq_mul_inv]
    calc
      _ = 2 * (rotation.anchorDenominator * rotation.anchorDenominator⁻¹) := by ring1
      _ = 2 := by rw [ExplicitField.mul_inv_cancel _ defined, mul_one]
  rw [coefficient]

/-- The trace and homogeneous inverse vector give a non-null source proportion for every cap-chart rotation.

The original computed anchor lies in the cap domain. Rescaling its
scalar-one representative by the retained nonzero trace denominator
supplies this exact homogeneous norm certificate.
-/
theorem projectiveInverse_nonzero [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1) :
    rotation.anchorDenominator ^ 2 + (Form.lorentz oneNonzero).quadrance
      (projectiveInverseVector oneNonzero rotation twoNonzero) ≠ 0 := by
  let defined := (rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn
  let vector := rotationAnchorVector oneNonzero rotation defined
  have recovery := rotationAnchorVector_cap_recovery oneNonzero rotation twoNonzero notHalfTurn
  have normDefined : 1 ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0 := by
    simpa only [one_pow, capDenominator] using recovery.1
  have scaled := proportionScale_nonzero oneNonzero 1 rotation.anchorDenominator vector normDefined defined
  rw [mul_one] at scaled
  rw [projectiveInverseVector_eq_scale_anchor oneNonzero rotation defined twoNonzero]
  exact scaled

/-- A cap-chart rotation is reconstructed from one plus trace and its literal homogeneous inverse vector.

The same computed affine anchor supplies the source coordinate identity,
the non-nullness certificate and the original rotation readback. Explicit
projective scaling transports the trace/antisymmetric recipe to that
cached cap without rebuilding its Clifford owner.
-/
theorem proportionRotation_projectiveInverse [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1) :
    proportionRotation oneNonzero rotation.anchorDenominator
        (projectiveInverseVector oneNonzero rotation twoNonzero)
        (projectiveInverse_nonzero oneNonzero rotation twoNonzero notHalfTurn) = rotation := by
  let defined := (rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn
  let vector := rotationAnchorVector oneNonzero rotation defined
  have recovery := rotationAnchorVector_cap_recovery oneNonzero rotation twoNonzero notHalfTurn
  let capDefined : capDenominator oneNonzero vector ≠ 0 := recovery.1
  have normDefined : 1 ^ 2 + (Form.lorentz oneNonzero).quadrance vector ≠ 0 := by
    simpa only [one_pow, capDenominator] using capDefined
  have scaled := proportionRotation_scale oneNonzero 1 rotation.anchorDenominator vector normDefined defined
  have sameCoordinates := (proportionRotation_eq_iff oneNonzero rotation.anchorDenominator
    (rotation.anchorDenominator * 1) (projectiveInverseVector oneNonzero rotation twoNonzero)
    (Vector3.scale rotation.anchorDenominator vector)
    (projectiveInverse_nonzero oneNonzero rotation twoNonzero notHalfTurn)
    (proportionScale_nonzero oneNonzero 1 rotation.anchorDenominator vector normDefined defined) twoNonzero).mpr
      ⟨1, oneNonzero, by ring1, by
        rw [Vector3.one_scale]
        exact (projectiveInverseVector_eq_scale_anchor oneNonzero rotation defined twoNonzero).symm⟩
  exact sameCoordinates.trans (scaled.trans
    ((proportionRotation_one oneNonzero vector capDefined).trans (recovery.2 capDefined)))

/-- Construct the original half turn from any supplied nonzero vector in the row space of identity plus its matrix.

Every displayed row is obtained by supplying its corresponding coordinate
unit vector. The original half-turn row witness supplies the exact vector
quadrance certificate; the scalar-zero source chart reads back the same
certified rotation.
-/
@[expose] def halfTurnRowProportion [DecidableEq K]
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (halfSpreadOne : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation = 1)
    (input : Vector3 K)
    (nonzero : Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix) ≠ Vector3.zero) :
    Σ' defined : 0 ^ 2 + (Form.lorentz oneNonzero).quadrance
      (Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix)) ≠ 0,
      proportionRotation oneNonzero 0 (Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix))
        defined = rotation := by
  let witness := Cayley.TernaryForm.halfTurnRowWitness (Form.lorentz oneNonzero) rotation
    twoNonzero halfSpreadOne input nonzero
  have defined : 0 ^ 2 + (Form.lorentz oneNonzero).quadrance
      (Matrix3.rowMul input (Matrix3.add Matrix3.identity rotation.matrix)) ≠ 0 := by
    simpa only [zero_pow (by decide : 2 ≠ 0), zero_add] using witness.1
  exact ⟨defined, (proportionRotation_zero oneNonzero _ witness.1).trans witness.2⟩

/-- Decode an invertible two-by-two matrix into its original Lorentz Clifford rotation.

The matrix entries determine the retained non-null dihedron, without a
projective normalization. Its action uses the original time-first Lorentz
form and the original Clifford action certificates.
-/
@[expose] def matrixRotation (twoNonzero : (2 : K) ≠ 0) (value : Matrix2.Invertible K) :
    (Form.lorentz oneNonzero).SpecialOrthogonal :=
  NonNullEvenClifford.actionRotation (Matrix.fromInvertible oneNonzero twoNonzero value)

/-- Compute an invertible matrix representative of a displayed Lorentz rotation.

The executable Clifford preimage is retained before its matrix is read
back. Its determinant certificate is the same original non-null norm.
-/
@[expose] def rotationMatrixRepresentative [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) : Matrix2.Invertible K :=
  Matrix.toInvertible oneNonzero (rotationProportion oneNonzero twoNonzero rotation)

/-- The computed invertible matrix representative reconstructs the original Lorentz rotation. -/
theorem matrixRotation_rotationMatrixRepresentative [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) :
    matrixRotation oneNonzero twoNonzero (rotationMatrixRepresentative oneNonzero twoNonzero rotation) = rotation := by
  unfold matrixRotation rotationMatrixRepresentative
  rw [Matrix.fromInvertible_toInvertible]
  exact (Form.lorentz oneNonzero).cliffordAction_surjective twoNonzero rotation

/-- Matrix multiplication gives the ordered product of the original certified Lorentz rotations. -/
theorem matrixRotation_mul (twoNonzero : (2 : K) ≠ 0) (left right : Matrix2.Invertible K) :
    matrixRotation oneNonzero twoNonzero (Matrix2.Invertible.mul left right) =
      Basic.TernaryForm.SpecialOrthogonal.mul (matrixRotation oneNonzero twoNonzero left)
        (matrixRotation oneNonzero twoNonzero right) := by
  unfold matrixRotation
  rw [Matrix.fromInvertible_mul]
  exact NonNullEvenClifford.actionRotation_mul _ _

/-- Two invertible matrices give the same Lorentz rotation exactly when they differ by a nonzero scalar.

This describes every fiber of the executable matrix correspondence. The
dihedron conversion preserves and reflects the same supplied scale on
the original matrices, including scalar-zero dihedron representatives.
-/
theorem matrixRotation_eq_iff_equivalent (twoNonzero : (2 : K) ≠ 0)
    (left right : Matrix2.Invertible K) :
    matrixRotation oneNonzero twoNonzero left = matrixRotation oneNonzero twoNonzero right ↔
      left.Equivalent right := by
  unfold matrixRotation
  exact (NonNullEvenClifford.actionRotation_eq_iff_equivalent _ _ twoNonzero).trans
    (Matrix.fromInvertible_equivalent_iff oneNonzero twoNonzero left right)

/-- Reconstructing a represented Lorentz rotation returns a matrix in the original projective class. -/
theorem rotationMatrixRepresentative_matrixRotation [DecidableEq K] (twoNonzero : (2 : K) ≠ 0)
    (value : Matrix2.Invertible K) :
    (rotationMatrixRepresentative oneNonzero twoNonzero (matrixRotation oneNonzero twoNonzero value)).Equivalent
      value :=
  (matrixRotation_eq_iff_equivalent oneNonzero twoNonzero _ _).mp
    (matrixRotation_rotationMatrixRepresentative oneNonzero twoNonzero _)

end Purelib.Geometry.Rotations.Ternary.Lorentz
