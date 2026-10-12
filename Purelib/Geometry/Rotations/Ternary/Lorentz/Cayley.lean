module

public import Purelib.Geometry.Quadratic.Ternary.Lorentz
public import Purelib.Geometry.Rotations.Ternary.Cayley.Matrix
public import Purelib.Geometry.Rotations.Ternary.Cayley.Spread
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Inverse
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Cayley caps in time-first Lorentz coordinates

The paper anchor is the skew matrix of the negated vector in the generic
Clifford convention. The cap retains that original form-indexed rotation;
its literal matrix and inverse formulas follow from the shared construction.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry
open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)

/-- The Lorentz cap denominator is one plus the original vector quadrance. -/
@[expose] def capDenominator (vector : Vector3 K) : K :=
  1 + (Form.lorentz oneNonzero).quadrance vector

/-- Negating the Lorentz vector converts the generic cap denominator to the paper denominator. -/
theorem cayleyDenominator_neg (vector : Vector3 K) :
    Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator
        (Form.lorentz oneNonzero) (Vector3.neg vector) = capDenominator oneNonzero vector := by
  unfold Rotations.Ternary.Cayley.TernaryForm.cayleyDenominator capDenominator
  rw [Form.lorentz_determinant, Form.quadrance_neg, one_mul]

/-- The original Lorentz cap domain excludes precisely quadrance minus one. -/
theorem capDenominator_ne_zero_iff (vector : Vector3 K) :
    capDenominator oneNonzero vector ≠ 0 ↔ (Form.lorentz oneNonzero).quadrance vector ≠ -1 := by
  constructor
  · intro defined excluded
    apply defined
    unfold capDenominator
    rw [excluded]
    ring1
  · intro admissible denominatorZero
    apply admissible
    calc
      _ = capDenominator oneNonzero vector - 1 := by unfold capDenominator; ring1
      _ = -1 := by rw [denominatorZero]; ring1

/-- The Lorentz cap retains the generic rotation at the negated anchor vector.

The supplied denominator certificate is transported to the same Lorentz form.
The resulting matrix, inverse and preservation certificates are those of the
original Clifford cap, with no new rotation owner.
-/
@[expose] def capRotation (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) :
    (Form.lorentz oneNonzero).SpecialOrthogonal :=
  Rotations.Ternary.Cayley.TernaryForm.capRotation (Form.lorentz oneNonzero) (Vector3.neg vector)
    (by rw [cayleyDenominator_neg]; exact defined)

/-- The Lorentz cap matrix is the retained matrix of its certified rotation. -/
@[expose] def cap (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) : Matrix3 K :=
  (capRotation oneNonzero vector defined).matrix

/-- Equal original Lorentz anchor vectors give the same retained cap rotation. -/
theorem capRotation_congr_vector {left right : Vector3 K} (equal : left = right)
    (leftDefined : capDenominator oneNonzero left ≠ 0)
    (rightDefined : capDenominator oneNonzero right ≠ 0) :
    capRotation oneNonzero left leftDefined = capRotation oneNonzero right rightDefined := by
  cases equal
  rfl

/-- Identity minus a Lorentz anchor has determinant one plus its quadrance. -/
theorem determinant_identity_sub_anchor (vector : Vector3 K) :
    Matrix3.determinant (Matrix3.sub Matrix3.identity (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)) =
      capDenominator oneNonzero vector := by
  change Matrix3.determinant
    (Matrix3.sub Matrix3.identity ((Form.lorentz oneNonzero).actionSkew (Vector3.neg vector))) = _
  rw [(Form.lorentz oneNonzero).determinant_identity_sub_actionSkew, cayleyDenominator_neg]

/-- Identity plus a Lorentz anchor has the same resolvent determinant. -/
theorem determinant_identity_add_anchor (vector : Vector3 K) :
    Matrix3.determinant (Matrix3.add Matrix3.identity (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)) =
      capDenominator oneNonzero vector := by
  change Matrix3.determinant
    (Matrix3.add Matrix3.identity ((Form.lorentz oneNonzero).actionSkew (Vector3.neg vector))) = _
  rw [(Form.lorentz oneNonzero).determinant_identity_add_actionSkew, cayleyDenominator_neg]

/-- The Lorentz anchor resolvent uses the original generic finite matrix inverse. -/
@[expose] def anchorResolventInverse (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0) : Matrix3 K :=
  (Form.lorentz oneNonzero).actionSkewResolventInverse (Vector3.neg vector)
    (by rw [cayleyDenominator_neg]; exact defined)

/-- The Lorentz resolvent inverse is identity plus the divided anchor and anchor square. -/
theorem anchorResolventInverse_eq (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0) :
    anchorResolventInverse oneNonzero vector defined =
      Matrix3.add Matrix3.identity (Matrix3.scale (1 / capDenominator oneNonzero vector)
        (Matrix3.add (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)
          (Matrix3.mul (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)
            (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)))) := by
  unfold anchorResolventInverse
  rw [(Form.lorentz oneNonzero).actionSkewResolventInverse_eq, cayleyDenominator_neg]
  rfl

/-- The retained Lorentz cap satisfies the literal quadratic reduction. -/
theorem cap_quadratic (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) :
    cap oneNonzero vector defined =
      Matrix3.add Matrix3.identity (Matrix3.scale (2 / capDenominator oneNonzero vector)
        (Matrix3.add (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)
          (Matrix3.mul (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)
            (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)))) := by
  unfold cap capRotation
  rw [(Form.lorentz oneNonzero).capRotation_matrix_quadratic, cayleyDenominator_neg]
  rfl

/-- The retained Lorentz cap is identity plus the anchor times the resolvent inverse. -/
theorem cap_eq_cayley (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) :
    cap oneNonzero vector defined =
      Matrix3.mul (Matrix3.add Matrix3.identity (Quadratic.Ternary.Lorentz.anchor oneNonzero vector))
        (anchorResolventInverse oneNonzero vector defined) :=
  (Form.lorentz oneNonzero).capRotation_matrix_eq_cayley (Vector3.neg vector) _

/-- The literal time-first Lorentz cap matrix has denominator one plus the vector quadrance. -/
theorem cap_coordinates (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) :
    cap oneNonzero vector defined =
      Matrix3.scale (1 / capDenominator oneNonzero vector)
        ⟨vector.t ^ 2 + vector.r ^ 2 + vector.s ^ 2 + 1,
          2 * (vector.s + vector.t * vector.r), 2 * (vector.t * vector.s - vector.r),
          2 * (vector.s - vector.t * vector.r), 1 - vector.t ^ 2 - vector.r ^ 2 + vector.s ^ 2,
          2 * (vector.t - vector.r * vector.s), -2 * (vector.r + vector.s * vector.t),
          -2 * (vector.t + vector.r * vector.s), 1 - vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2⟩ := by
  rw [cap_quadratic]
  have cancel := ExplicitField.mul_inv_cancel (capDenominator oneNonzero vector) defined
  calc
    _ = Matrix3.add
        (Matrix3.scale (capDenominator oneNonzero vector * (capDenominator oneNonzero vector)⁻¹)
          Matrix3.identity)
        (Matrix3.scale (2 / capDenominator oneNonzero vector)
          (Matrix3.add (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)
            (Matrix3.mul (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)
              (Quadratic.Ternary.Lorentz.anchor oneNonzero vector)))) := by
      rw [cancel, Matrix3.one_scale]
    _ = _ := by
      simp only [Quadratic.Ternary.Lorentz.anchor_coordinates,
        capDenominator, Form.quadrance_lorentz, ExplicitField.div_eq_mul_inv]
      ext <;> unfold Matrix3.add Matrix3.scale Matrix3.mul Matrix3.identity <;> ring1

/-- The original Lorentz cap matrix preserves the original time-first Gram matrix. -/
theorem cap_preservesMatrix (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) :
    Matrix3.mul (Matrix3.mul (cap oneNonzero vector defined) (Form.lorentz oneNonzero).matrix)
      (Matrix3.transpose (cap oneNonzero vector defined)) = (Form.lorentz oneNonzero).matrix :=
  (capRotation oneNonzero vector defined).preservesMatrix

/-- The original Lorentz cap matrix has determinant one. -/
theorem determinant_cap (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) :
    Matrix3.determinant (cap oneNonzero vector defined) = 1 :=
  (capRotation oneNonzero vector defined).determinantOne

/-- A Lorentz cap fixes its original anchor vector, including null anchors. -/
theorem rowMul_self_cap (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) :
    Matrix3.rowMul vector (cap oneNonzero vector defined) = vector := by
  rw [cap_quadratic, Matrix3.rowMul_add, Matrix3.rowMul_identity,
    Matrix3.rowMul_scale, Matrix3.rowMul_add, ← Matrix3.rowMul_mul,
    Quadratic.Ternary.Lorentz.rowMul_self_anchor]
  ext <;> unfold Matrix3.rowMul Vector3.add Vector3.scale Vector3.zero <;> ring1

/-- A Lorentz cap fixes exactly the kernel of its original paper anchor. -/
theorem rowMul_cap_eq_self_iff_anchor_kernel (axis vector : Vector3 K)
    (defined : capDenominator oneNonzero axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul vector (cap oneNonzero axis defined) = vector ↔
      Matrix3.rowMul vector (Quadratic.Ternary.Lorentz.anchor oneNonzero axis) = Vector3.zero :=
  (Form.lorentz oneNonzero).rowMul_capRotation_eq_self_iff_skew_kernel (Vector3.neg axis) vector _ twoNonzero

/-- The complete fixed space of a cap with non-null Lorentz anchor is its original axis line.

The coefficient is the original Lorentz pairing divided by the original anchor quadrance. -/
theorem rowMul_cap_eq_self_iff_projection (axis vector : Vector3 K)
    (defined : capDenominator oneNonzero axis ≠ 0)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Matrix3.rowMul vector (cap oneNonzero axis defined) = vector ↔
      vector = Vector3.scale ((Form.lorentz oneNonzero).bilinear vector axis /
        (Form.lorentz oneNonzero).quadrance axis) axis := by
  let form := Form.lorentz oneNonzero
  constructor
  · intro fixed
    have kernel := (rowMul_cap_eq_self_iff_anchor_kernel oneNonzero axis vector defined twoNonzero).mp fixed
    have squared := congrArg (fun value => Matrix3.rowMul value (Quadratic.Ternary.Lorentz.anchor oneNonzero axis))
      kernel
    rw [Matrix3.rowMul_mul, Quadratic.Ternary.Lorentz.anchor_square, Matrix3.rowMul_sub,
      Matrix3.rowMul_outer, Matrix3.rowMul_scale, Matrix3.rowMul_identity] at squared
    have zeroAction : Matrix3.rowMul Vector3.zero (Quadratic.Ternary.Lorentz.anchor oneNonzero axis) =
        Vector3.zero := by
      ext <;> unfold Matrix3.rowMul Vector3.zero <;> ring1
    rw [zeroAction, ← form.bilinear_eq_dot_dual] at squared
    have scaled : Vector3.scale (form.quadrance axis) vector = Vector3.scale (form.bilinear vector axis) axis := by
      have shifted := congrArg (fun value => Vector3.add value (Vector3.scale (form.quadrance axis) vector)) squared
      calc
        _ = Vector3.add Vector3.zero (Vector3.scale (form.quadrance axis) vector) := (Vector3.zero_add _).symm
        _ = Vector3.add (Vector3.sub (Vector3.scale (form.bilinear vector axis) axis)
            (Vector3.scale (form.quadrance axis) vector)) (Vector3.scale (form.quadrance axis) vector) := shifted.symm
        _ = Vector3.scale (form.bilinear vector axis) axis := by
          ext <;> unfold Vector3.add Vector3.sub <;> ring1
    have cancel : (form.quadrance axis)⁻¹ * form.quadrance axis = 1 := by
      rw [mul_comm]
      exact ExplicitField.mul_inv_cancel (form.quadrance axis) axisNonNull
    calc
      vector = Vector3.scale (form.quadrance axis)⁻¹ (Vector3.scale (form.quadrance axis) vector) := by
        rw [Vector3.scale_scale, cancel, Vector3.one_scale]
      _ = Vector3.scale (form.quadrance axis)⁻¹ (Vector3.scale (form.bilinear vector axis) axis) :=
        congrArg (Vector3.scale (form.quadrance axis)⁻¹) scaled
      _ = Vector3.scale (form.bilinear vector axis / form.quadrance axis) axis := by
        rw [Vector3.scale_scale, ExplicitField.div_eq_mul_inv, mul_comm]
  · intro projected
    calc
      Matrix3.rowMul vector (cap oneNonzero axis defined) =
          Matrix3.rowMul (Vector3.scale (form.bilinear vector axis / form.quadrance axis) axis)
            (cap oneNonzero axis defined) := congrArg (fun value => Matrix3.rowMul value
              (cap oneNonzero axis defined)) projected
      _ = Vector3.scale (form.bilinear vector axis / form.quadrance axis) axis := by
        rw [Matrix3.rowMul_vector_scale, rowMul_self_cap]
      _ = vector := projected.symm

/-- Equal Lorentz caps have equal anchor vectors when two is nonzero. -/
theorem cap_injective [DecidableEq K] (left right : Vector3 K)
    (leftDefined : capDenominator oneNonzero left ≠ 0)
    (rightDefined : capDenominator oneNonzero right ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (equal : cap oneNonzero left leftDefined = cap oneNonzero right rightDefined) : left = right := by
  have rotationsEqual := Rotations.Ternary.Basic.TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
    (capRotation oneNonzero left leftDefined) (capRotation oneNonzero right rightDefined) equal
  have negativesEqual := Rotations.Ternary.Cayley.TernaryForm.capRotation_injective
    (Form.lorentz oneNonzero) (Vector3.neg left) (Vector3.neg right) _ _ twoNonzero rotationsEqual
  have vectorsEqual := congrArg Vector3.neg negativesEqual
  rw [Vector3.neg_neg, Vector3.neg_neg] at vectorsEqual
  exact vectorsEqual

/-- The Lorentz cap trace is three minus the quadrance divided by its original denominator. -/
theorem trace_cap (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) :
    Matrix3.trace (cap oneNonzero vector defined) =
      (3 - (Form.lorentz oneNonzero).quadrance vector) / capDenominator oneNonzero vector := by
  rw [cap_coordinates, Matrix3.trace_scale, Form.quadrance_lorentz]
  simp only [ExplicitField.div_eq_mul_inv]
  unfold Matrix3.trace
  ring1

/-- The Lorentz cap trace minus one is its reciprocal quadratic coefficient. -/
theorem trace_cap_sub_one (vector : Vector3 K) (defined : capDenominator oneNonzero vector ≠ 0) :
    Matrix3.trace (cap oneNonzero vector defined) - 1 =
      2 * (1 - (Form.lorentz oneNonzero).quadrance vector) / capDenominator oneNonzero vector := by
  rw [trace_cap]
  have cancel := ExplicitField.mul_inv_cancel (capDenominator oneNonzero vector) defined
  calc
    _ = (3 - (Form.lorentz oneNonzero).quadrance vector) / capDenominator oneNonzero vector -
        capDenominator oneNonzero vector * (capDenominator oneNonzero vector)⁻¹ := by rw [cancel]
    _ = _ := by
      simp only [ExplicitField.div_eq_mul_inv]
      unfold capDenominator
      ring1

/-- The Lorentz cap characteristic polynomial has the paper's quadrance coefficient. -/
theorem characteristicValue_cap (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0) (X : K) :
    Matrix3.characteristicValue (cap oneNonzero vector defined) X =
      (X - 1) * (X ^ 2 -
        (2 * (1 - (Form.lorentz oneNonzero).quadrance vector) / capDenominator oneNonzero vector) * X + 1) := by
  have characteristic := (capRotation oneNonzero vector defined).characteristicValue_matrix X
  change Matrix3.characteristicValue (cap oneNonzero vector defined) X =
    (X - 1) * (X ^ 2 - (Matrix3.trace (cap oneNonzero vector defined) - 1) * X + 1) at characteristic
  rw [trace_cap_sub_one] at characteristic
  exact characteristic

/-- A Lorentz cap has no nonzero vector with eigenvalue minus one. -/
theorem rowMul_cap_eq_neg_implies_zero (axis : Vector3 K)
    (defined : capDenominator oneNonzero axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) (vector : Vector3 K)
    (negativeEigen : Matrix3.rowMul vector (cap oneNonzero axis defined) = Vector3.neg vector) :
    vector = Vector3.zero :=
  (Form.lorentz oneNonzero).rowMul_capRotation_eq_neg_implies_zero
    (Vector3.neg axis) _ twoNonzero vector negativeEigen

/-- The half spread of a Lorentz cap is quadrance divided by one plus quadrance. -/
theorem halfSpread_cap (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
        (capRotation oneNonzero vector defined) =
      (Form.lorentz oneNonzero).quadrance vector / capDenominator oneNonzero vector := by
  unfold capRotation
  rw [Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread_cap,
    Form.lorentz_determinant, Form.quadrance_neg, cayleyDenominator_neg, one_mul]
  exact twoNonzero

/-- The half spread of a defined Lorentz cap cannot be one. -/
theorem halfSpread_cap_ne_one (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
      (capRotation oneNonzero vector defined) ≠ 1 :=
  Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread_cap_ne_one
    (Form.lorentz oneNonzero) (Vector3.neg vector) _ twoNonzero

/-- No defined Lorentz cap is a half turn about a non-null line. -/
theorem capRotation_ne_halfTurn (vector axis : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0)
    (nonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    capRotation oneNonzero vector defined ≠ (Form.lorentz oneNonzero).halfTurnRotation axis nonNull := by
  intro equal
  apply halfSpread_cap_ne_one oneNonzero vector defined twoNonzero
  calc
    _ = Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
        ((Form.lorentz oneNonzero).halfTurnRotation axis nonNull) :=
      congrArg (Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)) equal
    _ = 1 := Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread_halfTurn
      (Form.lorentz oneNonzero) axis nonNull twoNonzero

/-- One minus the Lorentz cap half spread is the inverse original denominator. -/
theorem one_sub_halfSpread_cap (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    1 - Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
        (capRotation oneNonzero vector defined) = 1 / capDenominator oneNonzero vector := by
  rw [halfSpread_cap]
  have cancel := ExplicitField.mul_inv_cancel (capDenominator oneNonzero vector) defined
  calc
    _ = capDenominator oneNonzero vector * (capDenominator oneNonzero vector)⁻¹ -
        (Form.lorentz oneNonzero).quadrance vector / capDenominator oneNonzero vector := by rw [cancel]
    _ = _ := by
      simp only [ExplicitField.div_eq_mul_inv]
      unfold capDenominator
      ring1
  exact twoNonzero

/-- One minus twice the Lorentz cap half spread has numerator one minus quadrance. -/
theorem one_sub_two_halfSpread_cap (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    1 - 2 * Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
        (capRotation oneNonzero vector defined) =
      (1 - (Form.lorentz oneNonzero).quadrance vector) / capDenominator oneNonzero vector := by
  rw [halfSpread_cap]
  have cancel := ExplicitField.mul_inv_cancel (capDenominator oneNonzero vector) defined
  calc
    _ = capDenominator oneNonzero vector * (capDenominator oneNonzero vector)⁻¹ -
        2 * ((Form.lorentz oneNonzero).quadrance vector / capDenominator oneNonzero vector) := by rw [cancel]
    _ = _ := by
      simp only [ExplicitField.div_eq_mul_inv]
      unfold capDenominator
      ring1
  exact twoNonzero

/-- The Lorentz cap half spread times its complement has the squared original denominator. -/
theorem halfSpread_mul_one_sub_cap (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
        (capRotation oneNonzero vector defined) *
      (1 - Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
        (capRotation oneNonzero vector defined)) =
      (Form.lorentz oneNonzero).quadrance vector / capDenominator oneNonzero vector ^ 2 := by
  rw [one_sub_halfSpread_cap _ _ _ twoNonzero, halfSpread_cap _ _ _ twoNonzero]
  simp only [ExplicitField.div_eq_mul_inv]
  rw [Inverse.inverse_square defined]
  ring1

/-- The original Lorentz cap quadrance is recovered from half spread and its complement. -/
theorem quadrance_eq_halfSpread_div_one_sub (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    (Form.lorentz oneNonzero).quadrance vector =
      Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
          (capRotation oneNonzero vector defined) /
        (1 - Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
          (capRotation oneNonzero vector defined)) := by
  rw [one_sub_halfSpread_cap _ _ _ twoNonzero, halfSpread_cap _ _ _ twoNonzero]
  have denominatorNonzero : 1 / capDenominator oneNonzero vector ≠ 0 := by
    rw [ExplicitField.div_eq_mul_inv, one_mul]
    exact ExplicitField.inv_ne_zero defined
  apply Inverse.eq_div_of_mul_eq denominatorNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- Every null Lorentz anchor has the cubic unipotent cap characteristic polynomial. -/
theorem characteristicValue_cap_of_null (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0)
    (null : (Form.lorentz oneNonzero).quadrance vector = 0) (X : K) :
    Matrix3.characteristicValue (cap oneNonzero vector defined) X = (X - 1) ^ 3 := by
  have denominatorOne : capDenominator oneNonzero vector = 1 := by
    unfold capDenominator
    rw [null]
    ring1
  have inverseOne := Inverse.inverse_one oneNonzero
  rw [characteristicValue_cap, null, denominatorOne]
  simp only [ExplicitField.div_eq_mul_inv, inverseOne]
  ring1

/-- Every characteristic root of a null Lorentz cap is one. -/
theorem characteristicRoot_cap_of_null [DecidableEq K] (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0)
    (null : (Form.lorentz oneNonzero).quadrance vector = 0) (X : K)
    (root : Matrix3.characteristicValue (cap oneNonzero vector defined) X = 0) : X = 1 := by
  rw [characteristicValue_cap_of_null _ _ _ null] at root
  by_cases differenceZero : X - 1 = 0
  · calc
      X = (X - 1) + 1 := by ring1
      _ = 1 := by rw [differenceZero]; ring1
  · have squareNonzero := ExplicitField.square_nonzero_of_nonzero differenceZero
    have cubeNonzero := ExplicitField.mul_ne_zero squareNonzero differenceZero
    have cubeIdentity : (X - 1) ^ 2 * (X - 1) = (X - 1) ^ 3 := by ring1
    rw [cubeIdentity] at cubeNonzero
    exact False.elim (cubeNonzero root)

/-- Every null Lorentz cap minus identity has cube zero.

Its trace and principal trace are three, and its determinant is one. The
finite cubic characteristic relation proves nilpotence of the original
matrix minus identity without a Jordan decomposition.
-/
theorem cap_sub_identity_cube_of_null (vector : Vector3 K)
    (defined : capDenominator oneNonzero vector ≠ 0)
    (null : (Form.lorentz oneNonzero).quadrance vector = 0) :
    let difference := Matrix3.sub (cap oneNonzero vector defined) Matrix3.identity
    Matrix3.mul (Matrix3.mul difference difference) difference = Matrix3.zero := by
  have denominatorOne : capDenominator oneNonzero vector = 1 := by
    unfold capDenominator
    rw [null]
    ring1
  have inverseOne := Inverse.inverse_one oneNonzero
  have traceThree : Matrix3.trace (cap oneNonzero vector defined) = 3 := by
    rw [trace_cap, null, denominatorOne, ExplicitField.div_eq_mul_inv, inverseOne]
    ring1
  have principal : Matrix3.principalTrace (cap oneNonzero vector defined) =
      Matrix3.trace (cap oneNonzero vector defined) :=
    (capRotation oneNonzero vector defined).principalTrace_matrix
  dsimp only
  rw [Matrix3.cube_sub_identity, Matrix3.cubic_characteristic, principal, traceThree, determinant_cap]
  ext <;> unfold Matrix3.sub Matrix3.add Matrix3.scale Matrix3.zero <;> ring1

/-- Every non-null direction perpendicular to a Lorentz cap axis measures its canonical rotation spread. -/
theorem spread_cap (axis vector : Vector3 K) (defined : capDenominator oneNonzero axis ≠ 0)
    (nonNull : (Form.lorentz oneNonzero).quadrance vector ≠ 0)
    (perpendicular : (Form.lorentz oneNonzero).Perpendicular vector axis) (twoNonzero : (2 : K) ≠ 0) :
    (Form.lorentz oneNonzero).spread vector
        (Form.Isometry.act (capRotation oneNonzero axis defined).toIsometry vector) nonNull
        ((capRotation oneNonzero axis defined).toIsometry.quadrance_act_ne_zero vector nonNull) =
      Rotations.Ternary.Cayley.TernaryForm.rotationSpread (Form.lorentz oneNonzero)
        (capRotation oneNonzero axis defined) := by
  have perpendicularNeg : (Form.lorentz oneNonzero).Perpendicular vector (Vector3.neg axis) := by
    unfold Form.Perpendicular at perpendicular ⊢
    rw [Form.bilinear_neg_right, perpendicular, neg_zero]
  exact Rotations.Ternary.Cayley.TernaryForm.spread_cap (Form.lorentz oneNonzero) (Vector3.neg axis) vector
    (by rw [cayleyDenominator_neg]; exact defined) nonNull perpendicularNeg twoNonzero

/-- The canonical Lorentz cap spread is four times quadrance divided by the squared cap denominator. -/
theorem rotationSpread_cap (axis : Vector3 K) (defined : capDenominator oneNonzero axis ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Rotations.Ternary.Cayley.TernaryForm.rotationSpread (Form.lorentz oneNonzero)
        (capRotation oneNonzero axis defined) =
      4 * (Form.lorentz oneNonzero).quadrance axis / capDenominator oneNonzero axis ^ 2 := by
  unfold Rotations.Ternary.Cayley.TernaryForm.rotationSpread
  rw [mul_assoc, halfSpread_mul_one_sub_cap oneNonzero axis defined twoNonzero]
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

/-- Construct a retained non-null perpendicular vector measuring a Lorentz cap's geometric spread. -/
@[expose] def capSpreadWitness [DecidableEq K] (axis : Vector3 K)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0)
    (defined : capDenominator oneNonzero axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Σ' witness : (Form.lorentz oneNonzero).PerpendicularNonNullVectorWitness axis,
      (Form.lorentz oneNonzero).spread witness.value
        (Form.Isometry.act (capRotation oneNonzero axis defined).toIsometry witness.value) witness.nonNull
        ((capRotation oneNonzero axis defined).toIsometry.quadrance_act_ne_zero witness.value witness.nonNull) =
          Rotations.Ternary.Cayley.TernaryForm.rotationSpread (Form.lorentz oneNonzero)
            (capRotation oneNonzero axis defined) := by
  let witness := (Form.lorentz oneNonzero).perpendicularNonNullVectorWitness axis axisNonNull twoNonzero
  exact ⟨witness, spread_cap oneNonzero axis witness.value defined witness.nonNull witness.perpendicular twoNonzero⟩

/-- Construct a Lorentz cap with any prescribed half spread other than one.

The original Lorentz quadrance witness realizes `value/(1-value)`. Its
retained quadrance equation gives the nonzero cap denominator and the exact
half-spread value, without choosing roots or a new rotation owner.
-/
@[expose] def capHalfSpreadWitness (twoNonzero : (2 : K) ≠ 0) (value : K) (notOne : value ≠ 1) :
    Σ' vector : Vector3 K, Σ' defined : capDenominator oneNonzero vector ≠ 0,
      Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
        (capRotation oneNonzero vector defined) = value := by
  let witness := Quadratic.Ternary.Lorentz.quadranceWitness oneNonzero twoNonzero (value / (1 - value))
  have complementNonzero : 1 - value ≠ 0 := by
    intro complementZero
    apply notOne
    calc
      value = 1 - (1 - value) := by ring1
      _ = 1 := by rw [complementZero]; ring1
  have denominator : capDenominator oneNonzero witness.1 = 1 / (1 - value) := by
    unfold capDenominator
    rw [witness.2]
    apply ExplicitField.eq_of_mul_eq_mul_right complementNonzero
    calc
      _ = 1 - value + value := by
        rw [add_mul, one_mul, ExplicitField.div_mul_cancel value complementNonzero]
      _ = 1 := by ring1
      _ = _ := (ExplicitField.div_mul_cancel 1 complementNonzero).symm
  have defined : capDenominator oneNonzero witness.1 ≠ 0 := by
    rw [denominator]
    exact ExplicitField.div_ne_zero oneNonzero complementNonzero
  refine ⟨witness.1, defined, ?_⟩
  rw [halfSpread_cap _ _ _ twoNonzero, witness.2]
  apply ExplicitField.eq_of_mul_eq_mul_right defined
  calc
    _ = value / (1 - value) := ExplicitField.div_mul_cancel _ defined
    _ = value * capDenominator oneNonzero witness.1 := by
      rw [denominator]
      simp only [ExplicitField.div_eq_mul_inv]
      ring1

/-- Construct a Lorentz rotation with any prescribed half spread.

Half spread one uses a half turn about the witness with quadrance one. Every
other value uses the retained cap witness, including null-axis caps at zero.
-/
@[expose] def halfSpreadWitness [DecidableEq K] (twoNonzero : (2 : K) ≠ 0) (value : K) :
    Σ' rotation : (Form.lorentz oneNonzero).SpecialOrthogonal,
      Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation = value := by
  by_cases isOne : value = 1
  · let axis := Quadratic.Ternary.Lorentz.quadranceWitness oneNonzero twoNonzero 1
    have axisNonNull : (Form.lorentz oneNonzero).quadrance axis.1 ≠ 0 :=
      fun zero => oneNonzero (axis.2.symm.trans zero)
    refine ⟨(Form.lorentz oneNonzero).halfTurnRotation axis.1 axisNonNull, ?_⟩
    exact (Rotations.Ternary.Cayley.TernaryForm.rotationHalfSpread_halfTurn
      (Form.lorentz oneNonzero) axis.1 axisNonNull twoNonzero).trans isOne.symm
  · let witness := capHalfSpreadWitness oneNonzero twoNonzero value isOne
    exact ⟨capRotation oneNonzero witness.1 witness.2.1, witness.2.2⟩

/-- The time-fixed matrix of a spatial plane rotation with retained scalar coefficients. -/
@[expose] def spatialRotationMatrix (cosine sine : K) : Matrix3 K :=
  ⟨1, 0, 0, 0, cosine, sine, 0, -sine, cosine⟩

/-- Embed a certified spatial plane rotation in the original Lorentz rotation owner.

The supplied squared-sum equation certifies both cached inverse products,
Lorentz form preservation and determinant one. The inverse retains the
same first coefficient and the negated second coefficient.
-/
@[expose] def spatialRotation (cosine sine : K) (unit : cosine ^ 2 + sine ^ 2 = 1) :
    (Form.lorentz oneNonzero).SpecialOrthogonal where
  matrix := spatialRotationMatrix cosine sine
  inverseMatrix := spatialRotationMatrix cosine (-sine)
  matrix_mul_inverse := by
    ext <;> unfold Matrix3.mul spatialRotationMatrix Matrix3.identity
    all_goals first | ring1 | exact (by
      calc
        _ = cosine ^ 2 + sine ^ 2 := by ring1
        _ = 1 := unit)
  inverse_mul_matrix := by
    ext <;> unfold Matrix3.mul spatialRotationMatrix Matrix3.identity
    all_goals first | ring1 | exact (by
      calc
        _ = cosine ^ 2 + sine ^ 2 := by ring1
        _ = 1 := unit)
  preservesMatrix := by
    change Matrix3.mul (Matrix3.mul (spatialRotationMatrix cosine sine)
        ⟨1, 0, 0, 0, -1, 0, 0, 0, -1⟩)
      (Matrix3.transpose (spatialRotationMatrix cosine sine)) = ⟨1, 0, 0, 0, -1, 0, 0, 0, -1⟩
    ext <;> unfold Matrix3.mul Matrix3.transpose spatialRotationMatrix
    all_goals first | ring1 | exact (by
      calc
        _ = -(cosine ^ 2 + sine ^ 2) := by ring1
        _ = -1 := congrArg (fun value : K => -value) unit)
  determinantOne := by
    calc
      _ = cosine ^ 2 + sine ^ 2 := by unfold Matrix3.determinant spatialRotationMatrix; ring1
      _ = 1 := unit

/-- The embedded spatial rotation has exactly its retained time-fixed matrix. -/
theorem spatialRotation_matrix (cosine sine : K) (unit : cosine ^ 2 + sine ^ 2 = 1) :
    (spatialRotation oneNonzero cosine sine unit).matrix = spatialRotationMatrix cosine sine := rfl

/-- The original cached inverse of a spatial rotation negates its second scalar coefficient. -/
theorem spatialRotation_inverse_matrix (cosine sine : K) (unit : cosine ^ 2 + sine ^ 2 = 1) :
    (SpecialOrthogonal.inverse
      (spatialRotation oneNonzero cosine sine unit)).matrix = spatialRotationMatrix cosine (-sine) := rfl

/-- A spatial rotation fixes time and acts by the original two-dimensional Euclidean arithmetic on space. -/
theorem spatialRotation_apply (cosine sine : K) (unit : cosine ^ 2 + sine ^ 2 = 1) (vector : Vector3 K) :
    Matrix3.rowMul vector (spatialRotation oneNonzero cosine sine unit).matrix =
      ⟨vector.t, cosine * vector.r - sine * vector.s, sine * vector.r + cosine * vector.s⟩ := by
  change Matrix3.rowMul vector (spatialRotationMatrix cosine sine) = _
  ext <;> unfold Matrix3.rowMul spatialRotationMatrix <;> ring1

/-- Multiplication of original embedded rotations retains the Euclidean plane coefficient product.

Both input certificates belong to their original Lorentz rotations. The
actual matrix of their original group product has the same time-fixed
block and the usual finite scalar product coefficients.
-/
theorem spatialRotation_mul_matrix (leftCosine leftSine rightCosine rightSine : K)
    (leftUnit : leftCosine ^ 2 + leftSine ^ 2 = 1) (rightUnit : rightCosine ^ 2 + rightSine ^ 2 = 1) :
    (SpecialOrthogonal.mul
      (spatialRotation oneNonzero leftCosine leftSine leftUnit)
      (spatialRotation oneNonzero rightCosine rightSine rightUnit)).matrix =
      spatialRotationMatrix (leftCosine * rightCosine - leftSine * rightSine)
        (leftCosine * rightSine + leftSine * rightCosine) := by
  change Matrix3.mul (spatialRotationMatrix leftCosine leftSine)
    (spatialRotationMatrix rightCosine rightSine) = _
  ext <;> unfold Matrix3.mul spatialRotationMatrix <;> ring1

end Purelib.Geometry.Rotations.Ternary.Lorentz
