module

import Purelib.Geometry.Quadratic.Ternary.Lorentz
public import Purelib.Geometry.Quadratic.Ternary.Lorentz.Reflection
import Purelib.Geometry.Rotations.Ternary.Lorentz.Cayley
import Purelib.Geometry.Rotations.Ternary.Lorentz.Anchor
public import Purelib.Geometry.Rotations.Ternary.Lorentz.Splitting
public import Purelib.Geometry.Rotations.Ternary.Lorentz.Composition
import Purelib.Algebra.Clifford.Lorentz.Matrix
import Purelib.Algebra.Clifford.Ternary.SquareClass
public import Purelib.Geometry.Rotations.Ternary.Lorentz.SquareClass
import Purelib.NumberTheory.SquareClass.Rational.Nonsquare
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.ExplicitOrder.Sign
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.ExplicitOrder.Basic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Rational Lorentz vectors and anchors

The exact computations include a spacelike–timelike pair with spread
greater than one and distinct non-null directions with zero spread.
The same retained pair supplies the anchor product and characteristic
polynomial calculations.
-/

public section

namespace Purelib.Examples.Geometry.Quadratic.Ternary.Lorentz

open Purelib.Geometry.Rotations.Ternary

open Purelib.Algebra.Quadratic.Ternary.Basic (TernaryForm)
open Purelib.Algebra.Clifford.Ternary.Basic.TernaryForm
open Purelib.Algebra.Clifford.Lorentz
open Purelib.NumberTheory.SquareClass.Rational
open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Basic (OrderedExplicitField)
open Purelib.Algebra.Field.Squares
open Purelib.Algebra.Field.SquareClass.Basic (SquareClassRepresentative)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Cast (natCast_eq_fromInt fromInt)
open Purelib.Data.Rat.Fraction.Cast.Order (natCast_pos_direct)
open Purelib.Geometry
open Purelib.Geometry.Quadratic.Ternary
open Purelib.Polynomial.Quadratic
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

/-- The rational unit is nonzero. -/
theorem oneNonzero : (1 : Rational) ≠ 0 := by decide

/-- Two is nonzero in the rational field. -/
theorem twoNonzero : (2 : Rational) ≠ 0 := by decide

/-- The retained rational form has time-first signature `(1,-1,-1)`. -/
@[expose] def form : TernaryForm Rational := TernaryForm.lorentz oneNonzero

/-- The introductory source dihedron retains scalar three and spatial vector `(0,0,1)`. -/
@[expose] def introductoryValue : form.NonNullEvenClifford where
  toEvenClifford := Matrix.coordinates oneNonzero 3 ⟨0, 0, 1⟩
  normNonzero := by decide

/-- The original introductory dihedron has reduced norm eight. -/
theorem introductory_norm : EvenClifford.norm introductoryValue.toEvenClifford = 8 := by decide

/-- The introductory norm represents the rational square class of two through its explicit half scale. -/
theorem introductory_normClass_two :
    (NonNullEvenClifford.normClass introductoryValue).Equivalent ⟨2, by decide⟩ := by
  refine ⟨1 / 2, by decide, ?_⟩
  change 2 = (1 / 2 : Rational) ^ 2 * EvenClifford.norm introductoryValue.toEvenClifford
  rw [introductory_norm]
  decide

/-- The original introductory boost has quadrance class represented by two. -/
theorem introductory_quadranceClass_two :
    ((NonNullEvenClifford.actionRotation introductoryValue).quadranceClass twoNonzero).Equivalent
      ⟨2, by decide⟩ :=
  SquareClassRepresentative.equivalent_trans
    (TernaryForm.SpecialOrthogonal.quadranceClass_action introductoryValue twoNonzero)
    introductory_normClass_two

/-- The introductory rational dihedron has no nonzero rational scaling of unit norm.

A proposed normalizing factor would make its fourfold multiple a rational
square root of two. The original reduced-fraction nonsquare certificate
rules out that exact scalar equation.
-/
theorem introductory_no_unit_scale :
    ¬ ∃ factor : Rational, factor ≠ 0 ∧
      EvenClifford.norm (EvenClifford.scale factor introductoryValue.toEvenClifford) = 1 := by
  rintro ⟨factor, _factorNonzero, normOne⟩
  rw [EvenClifford.norm_scale, introductory_norm] at normOne
  apply Nonsquare.square_ne_two (4 * factor)
  calc
    _ = 2 * (factor ^ 2 * 8) := by ring1
    _ = 2 := by rw [normOne, mul_one]

/-- The introductory rational boost has no original unit-norm Clifford preimage.

Projective faithfulness supplies the exact scale from its retained source
dihedron to any proposed preimage. The preceding scalar obstruction
therefore applies to the original rotation, not merely one matrix encoding.
-/
theorem introductory_no_unit_preimage :
    ¬ ∃ value : form.NonNullEvenClifford,
      NonNullEvenClifford.actionRotation value = NonNullEvenClifford.actionRotation introductoryValue ∧
      EvenClifford.norm value.toEvenClifford = 1 := by
  rintro ⟨value, represents, normOne⟩
  have equivalent := ((form.projectiveCliffordCorrespondence twoNonzero).action_eq_iff_equivalent
    introductoryValue value).mp represents.symm
  rcases equivalent with ⟨factor, factorNonzero, equal⟩
  apply introductory_no_unit_scale
  refine ⟨factor, factorNonzero, ?_⟩
  exact (congrArg EvenClifford.norm equal).symm.trans normOne

/-- The spacelike vector in the retained rational pair. -/
@[expose] def first : Vector3 Rational := ⟨1, 2, 3⟩

/-- The timelike vector in the retained rational pair. -/
@[expose] def second : Vector3 Rational := ⟨2, -1, 1⟩

/-- The time basis vector used for the scalar and vector triple products. -/
@[expose] def time : Vector3 Rational := ⟨1, 0, 0⟩

/-- The first vector has quadrance negative twelve. -/
theorem quadrance_first : form.quadrance first = -12 := by decide

/-- The second vector has quadrance two. -/
theorem quadrance_second : form.quadrance second = 2 := by decide

/-- The retained pair has Lorentz pairing one. -/
theorem bilinear_first_second : form.bilinear first second = 1 := by decide

/-- The first vector pairs with the time basis vector to one. -/
theorem bilinear_first_time : form.bilinear first time = 1 := by decide

/-- The retained pair has signed cross product `(-5,5,-5)`. -/
theorem cross_first_second : Lorentz.cross oneNonzero first second = ⟨-5, 5, -5⟩ := by decide

/-- The retained scalar triple product is negative five. -/
theorem scalar_triple : form.bilinear (Lorentz.cross oneNonzero first second) time = -5 := by decide

/-- The three displayed vectors have determinant five. -/
theorem determinant_first_second_time : Vector3.determinant first second time = 5 := by decide

/-- The retained cross product is perpendicular to the first vector. -/
theorem cross_perpendicular_first : form.bilinear (Lorentz.cross oneNonzero first second) first = 0 := by decide

/-- The retained cross product is perpendicular to the second vector. -/
theorem cross_perpendicular_second : form.bilinear (Lorentz.cross oneNonzero first second) second = 0 := by decide

/-- Crossing the second vector with the time basis vector gives `(0,1,1)`. -/
theorem cross_second_time : Lorentz.cross oneNonzero second time = ⟨0, 1, 1⟩ := by decide

/-- The retained vector triple product gives `(1,-1,1)`. -/
theorem vector_triple :
    Lorentz.cross oneNonzero first (Lorentz.cross oneNonzero second time) = ⟨1, -1, 1⟩ := by decide

/-- The retained vector triple product agrees with its two scalar transports. -/
theorem vector_triple_transport :
    Vector3.sub (Vector3.scale (form.bilinear first time) second)
      (Vector3.scale (form.bilinear first second) time) = ⟨1, -1, 1⟩ := by decide

/-- The retained cross product has quadrance negative twenty-five. -/
theorem quadrance_cross : form.quadrance (Lorentz.cross oneNonzero first second) = -25 := by decide

/-- The first vector is non-null. -/
theorem firstNonNull : form.quadrance first ≠ 0 := by decide

/-- The original negative-time proportion has scalar two and the retained spacelike vector `(1,2,3)`. -/
@[expose] def negativeTimeRotation : form.SpecialOrthogonal :=
  Lorentz.proportionRotation oneNonzero 2 first (by decide)

/-- The negative-time rotation has half spread three halves and time entry negative nine quarters. -/
theorem negativeTimeRotation_values :
    Cayley.TernaryForm.rotationHalfSpread form negativeTimeRotation = 3 / 2 ∧
      negativeTimeRotation.matrix.tt = -9 / 4 := by
  constructor
  · unfold negativeTimeRotation form
    rw [Lorentz.halfSpread_proportionRotation oneNonzero 2 first (by decide) twoNonzero]
    decide
  · decide

/-- The original negative-time rotation fixes the retained spacelike vector exactly. -/
theorem negativeTimeRotation_fixed_first : Matrix3.rowMul first negativeTimeRotation.matrix = first := by
  decide

/-- The negative-time rotation's actual characteristic polynomial has reciprocal center negative two. -/
theorem negativeTimeRotation_characteristic (point : Rational) :
    Matrix3.characteristicValue negativeTimeRotation.matrix point = (point - 1) * Reciprocal.eval (-2) point := by
  rw [TernaryForm.characteristicValue_rotation_halfSpread form negativeTimeRotation twoNonzero point,
    negativeTimeRotation_values.1]
  have center : (1 - 2 * (3 / 2) : Rational) = -2 := by decide
  rw [center]
  rfl

/-- The nontrivial characteristic factor of the negative-time rotation is centered at the square-root equation three. -/
theorem negativeTimeRotation_characteristic_centered (point : Rational) :
    Matrix3.characteristicValue negativeTimeRotation.matrix point = (point - 1) * ((point + 2) ^ 2 - 3) := by
  rw [negativeTimeRotation_characteristic, Reciprocal.eval_centered]
  have constant : ((-2 : Rational) ^ 2 - 1) = 3 := by decide
  rw [constant]
  have centered : point - (-2) = point + 2 := by ring1
  rw [centered]

/-- The original negative-time rotation has no nontrivial rational eigenvalue.

Its reciprocal factor would give a rational square root of three. The
retained rational nonsquare certificate rules this out for every actual
nonzero row eigenvector of the original matrix.
-/
theorem negativeTimeRotation_no_nontrivial_eigenvalue (point : Rational) (notOne : point ≠ 1) :
    ¬ Nonempty (Matrix3.RowEigenvector negativeTimeRotation.matrix point) := by
  rintro ⟨witness⟩
  have zero := witness.characteristicValue_eq_zero
  rw [negativeTimeRotation_characteristic] at zero
  have linearNonzero : point - 1 ≠ 0 := by
    intro zero
    apply notOne
    calc
      point = (point - 1) + 1 := by ring1
      _ = 1 := by rw [zero, zero_add]
  have root := ExplicitField.eq_zero_of_mul_eq_zero_left linearNonzero zero
  have centered := Reciprocal.centered_square_of_root (-2) point root
  have constant : ((-2 : Rational) ^ 2 - 1) = 3 := by decide
  rw [constant] at centered
  exact Nonsquare.square_ne_three (point - (-2)) centered

/-- The negative quadrance of the original spacelike vector has no rational square root. -/
theorem neg_quadrance_first_not_square (root : Rational) : root ^ 2 ≠ -form.quadrance first := by
  rw [quadrance_first, neg_neg]
  exact Nonsquare.square_ne_twelve root

/-- The original spacelike axis and half spread minus three satisfy the axis square condition with root minus twelve. -/
@[expose] def firstAxisSquareCertificate :
    Witness.NonzeroSquare (Lorentz.prescribedAxisSquareValue oneNonzero first (-3)) where
  root := -12
  rootNonzero := by decide
  square := by decide

/-- The original spacelike axis constructs a rational time-preserving rotation with half spread minus three. -/
@[expose] def firstAxisRotation : Lorentz.PrescribedAxisRotation oneNonzero first (-3) :=
  Lorentz.prescribedAxisRotationOfSquare oneNonzero first (-3)
    firstAxisSquareCertificate firstNonNull (by decide) twoNonzero

/-- The retained root computes axis scale one quarter, half spread minus three and time entry fifteen halves. -/
theorem firstAxisRotation_coordinates :
    firstAxisRotation.anchorScale = (1 : Rational) / 4 ∧
      Cayley.TernaryForm.rotationHalfSpread form firstAxisRotation.rotation = -3 ∧
      firstAxisRotation.rotation.matrix.tt = 15 / 2 := by
  constructor
  · decide
  · constructor
    · exact firstAxisRotation.halfSpread_eq
    · decide

/-- The original rational rotation about the spacelike axis preserves time orientation. -/
theorem firstAxisRotation_timePositive : 0 < firstAxisRotation.rotation.matrix.tt := by
  rw [firstAxisRotation_coordinates.2.2, ExplicitField.div_eq_mul_inv]
  exact OrderedExplicitField.mul_pos_direct
    (natCast_pos_direct (n := 15) (by decide))
    (OrderedExplicitField.inv_pos_direct
      (natCast_pos_direct (n := 2) (by decide)))

/-- No rotation with this original rational axis and nonzero half spread different from one has a nontrivial rational
eigenvalue.

The negative original axis quadrance is twelve. Its rational nonsquare certificate applies to actual nonzero
eigenvectors of the original rotation matrix. -/
theorem first_axis_no_nontrivial_eigenvalue {amount : Rational}
    (candidate : Lorentz.PrescribedAxisRotation oneNonzero first amount)
    (amountNonzero : amount ≠ 0) (amountNotOne : amount ≠ 1) :
    ¬ ∃ point : Rational, point ≠ 1 ∧ Nonempty (Matrix3.RowEigenvector candidate.rotation.matrix point) := by
  intro eigenvalue
  obtain ⟨root, square⟩ :=
    (candidate.nontrivial_eigenvalue_iff oneNonzero firstNonNull amountNonzero amountNotOne twoNonzero).mp eigenvalue
  exact neg_quadrance_first_not_square root square

/-- The original time-preserving rational rotation about `(1,2,3)` has no nontrivial rational eigenvalue. -/
theorem firstAxisRotation_no_nontrivial_eigenvalue :
    ¬ ∃ point : Rational, point ≠ 1 ∧ Nonempty (Matrix3.RowEigenvector firstAxisRotation.rotation.matrix point) :=
  first_axis_no_nontrivial_eigenvalue firstAxisRotation (by decide) (by decide)

/-- The second vector is non-null. -/
theorem secondNonNull : form.quadrance second ≠ 0 := by decide

/-- The retained pair has spread twenty-five over twenty-four. -/
theorem spread_first_second : form.spread first second firstNonNull secondNonNull = 25 / 24 := by decide

/-- The retained pair has spread strictly greater than one. -/
theorem spread_first_second_gt_one : 1 < form.spread first second firstNonNull secondNonNull := by decide

/-- The first zero-spread direction is the first spatial basis vector. -/
@[expose] def zeroSpreadFirst : Vector3 Rational := ⟨0, 1, 0⟩

/-- The second zero-spread direction has all three coordinates one. -/
@[expose] def zeroSpreadSecond : Vector3 Rational := ⟨1, 1, 1⟩

/-- Both zero-spread directions have quadrance negative one and pairing negative one. -/
theorem zero_spread_pairings :
    form.quadrance zeroSpreadFirst = -1 ∧ form.quadrance zeroSpreadSecond = -1 ∧
      form.bilinear zeroSpreadFirst zeroSpreadSecond = -1 := by decide

/-- The first zero-spread direction is non-null. -/
theorem zeroSpreadFirstNonNull : form.quadrance zeroSpreadFirst ≠ 0 := by decide

/-- The second zero-spread direction is non-null. -/
theorem zeroSpreadSecondNonNull : form.quadrance zeroSpreadSecond ≠ 0 := by decide

/-- The two retained non-null directions have zero spread. -/
theorem spread_zero_pair :
    form.spread zeroSpreadFirst zeroSpreadSecond zeroSpreadFirstNonNull zeroSpreadSecondNonNull = 0 := by decide

/-- The zero-spread pair has cross product `(-1,0,-1)`. -/
theorem cross_zero_pair : Lorentz.cross oneNonzero zeroSpreadFirst zeroSpreadSecond = ⟨-1, 0, -1⟩ := by decide

/-- The zero-spread cross product is null and nonzero. -/
theorem cross_zero_pair_null_nonzero :
    form.IsNull (Lorentz.cross oneNonzero zeroSpreadFirst zeroSpreadSecond) ∧
      Lorentz.cross oneNonzero zeroSpreadFirst zeroSpreadSecond ≠ Vector3.zero := by
  constructor
  · change form.quadrance (Lorentz.cross oneNonzero zeroSpreadFirst zeroSpreadSecond) = 0
    decide
  · decide

/-- No scalar multiple of the first zero-spread direction is the second direction. -/
theorem zero_spread_directions_distinct (scalar : Rational) :
    Vector3.scale scalar zeroSpreadFirst ≠ zeroSpreadSecond := by
  intro equal
  have timeEqual := congrArg Vector3.t equal
  change scalar * 0 = 1 at timeEqual
  rw [mul_zero] at timeEqual
  exact (by decide : (0 : Rational) ≠ 1) timeEqual

/-- The first vector has the literal Lorentz anchor matrix. -/
theorem anchor_first : Lorentz.anchor oneNonzero first = ⟨0, 3, -2, 3, 0, 1, -2, -1, 0⟩ := by decide

/-- The second vector multiplied by the first anchor gives the displayed cross. -/
theorem rowMul_second_anchor_first :
    Matrix3.rowMul second (Lorentz.anchor oneNonzero first) = ⟨-5, 5, -5⟩ := by decide

/-- The first vector multiplied by its own anchor is zero. -/
theorem rowMul_first_anchor_first :
    Matrix3.rowMul first (Lorentz.anchor oneNonzero first) = Vector3.zero := by decide

/-- The Lorentz dual of the second vector is `(2,1,-1)`. -/
theorem dual_second : form.dual second = ⟨2, 1, -1⟩ := by decide

/-- The retained pair has the displayed product of its two anchors. -/
theorem anchor_product :
    Matrix3.mul (Lorentz.anchor oneNonzero first) (Lorentz.anchor oneNonzero second) =
      ⟨1, 4, 6, 1, 1, 3, -1, -2, -4⟩ := by decide

/-- The reversed cross of the retained pair is `(5,-5,5)`. -/
theorem cross_second_first : Lorentz.cross oneNonzero second first = ⟨5, -5, 5⟩ := by decide

/-- The commutator of the retained anchors is the reversed cross anchor. -/
theorem anchor_commutator :
    Matrix3.sub
        (Matrix3.mul (Lorentz.anchor oneNonzero first) (Lorentz.anchor oneNonzero second))
        (Matrix3.mul (Lorentz.anchor oneNonzero second) (Lorentz.anchor oneNonzero first)) =
      Lorentz.anchor oneNonzero ⟨5, -5, 5⟩ := by decide

/-- The trace of the retained anchor product is negative two. -/
theorem trace_anchor_product :
    Matrix3.trace (Matrix3.mul (Lorentz.anchor oneNonzero first) (Lorentz.anchor oneNonzero second)) = -2 := by decide

/-- The retained anchors have trace pairing one. -/
theorem anchor_pairing :
    Coordinates3.Antisymmetric.anchorForm (Lorentz.anchor oneNonzero first)
      (Lorentz.anchor oneNonzero second) = 1 := by decide

/-- The square of the first anchor has trace twenty-four. -/
theorem trace_anchor_square :
    Matrix3.trace (Matrix3.mul (Lorentz.anchor oneNonzero first) (Lorentz.anchor oneNonzero first)) = 24 := by decide

/-- The first anchor has trace quadrance negative twelve. -/
theorem anchor_quadrance :
    Coordinates3.Antisymmetric.anchorQuadrance (Lorentz.anchor oneNonzero first) = -12 := by decide

/-- The first anchor has trace zero, principal-minor sum negative twelve and determinant zero. -/
theorem anchor_characteristic_coefficients :
    Matrix3.trace (Lorentz.anchor oneNonzero first) = 0 ∧
      Matrix3.principalTrace (Lorentz.anchor oneNonzero first) = -12 ∧
      Matrix3.determinant (Lorentz.anchor oneNonzero first) = 0 := by decide

/-- The first anchor has characteristic polynomial `X³-12X`. -/
theorem anchor_characteristic (X : Rational) :
    Matrix3.characteristicValue (Lorentz.anchor oneNonzero first) X = X ^ 3 - 12 * X := by
  rw [Lorentz.characteristicValue_anchor]
  change X ^ 3 + form.quadrance first * X = X ^ 3 - 12 * X
  rw [quadrance_first]
  ring1

/-- The non-null normal `(2,1,1)` for the retained reflection and half turn. -/
@[expose] def reflectionNormal : Vector3 Rational := ⟨2, 1, 1⟩

/-- The vector `(1,1,1)` lies in the retained reflection's perpendicular plane. -/
@[expose] def reflectionPerpendicular : Vector3 Rational := ⟨1, 1, 1⟩

/-- The retained reflection normal has quadrance two. -/
theorem quadrance_reflectionNormal : form.quadrance reflectionNormal = 2 := by decide

/-- The retained reflection normal has positive quadrance. -/
theorem quadrance_reflectionNormal_pos : 0 < form.quadrance reflectionNormal := by decide

/-- The retained reflection normal is non-null. -/
theorem reflectionNormalNonNull : form.quadrance reflectionNormal ≠ 0 := by decide

/-- The retained test vector is perpendicular to the reflection normal. -/
theorem reflection_perpendicular_pairing : form.bilinear reflectionPerpendicular reflectionNormal = 0 := by decide

/-- Twice the inverse quadrance of the retained reflection normal is one. -/
theorem reflection_coefficient : 2 / form.quadrance reflectionNormal = 1 := by decide

/-- The retained normal has the displayed reflection matrix. -/
theorem reflection_matrix :
    form.reflection reflectionNormal reflectionNormalNonNull = ⟨-3, -2, -2, 2, 2, 1, 2, 1, 2⟩ := by decide

/-- The retained reflection reverses its normal to `(-2,-1,-1)`. -/
theorem reflection_reverses_normal :
    Matrix3.rowMul reflectionNormal (form.reflection reflectionNormal reflectionNormalNonNull) =
      ⟨-2, -1, -1⟩ := by decide

/-- The retained reflection fixes its perpendicular test vector. -/
theorem reflection_fixes_perpendicular :
    Matrix3.rowMul reflectionPerpendicular (form.reflection reflectionNormal reflectionNormalNonNull) =
      reflectionPerpendicular := by decide

/-- The retained reflection has determinant negative one. -/
theorem reflection_determinant :
    Matrix3.determinant (form.reflection reflectionNormal reflectionNormalNonNull) = -1 := by decide

/-- The retained normal has the displayed half-turn matrix. -/
theorem halfTurn_matrix :
    form.halfTurn reflectionNormal reflectionNormalNonNull = ⟨3, 2, 2, -2, -2, -1, -2, -1, -2⟩ := by decide

/-- The retained half turn fixes its normal vector. -/
theorem halfTurn_fixes_normal :
    Matrix3.rowMul reflectionNormal (form.halfTurn reflectionNormal reflectionNormalNonNull) =
      reflectionNormal := by decide

/-- The retained half turn reverses its perpendicular test vector. -/
theorem halfTurn_reverses_perpendicular :
    Matrix3.rowMul reflectionPerpendicular (form.halfTurn reflectionNormal reflectionNormalNonNull) =
      ⟨-1, -1, -1⟩ := by decide

/-- The retained half-turn rows have Lorentz quadrances one, negative one and negative one. -/
theorem halfTurn_row_quadrances :
    form.quadrance (Matrix3.rowT (form.halfTurn reflectionNormal reflectionNormalNonNull)) = 1 ∧
      form.quadrance (Matrix3.rowR (form.halfTurn reflectionNormal reflectionNormalNonNull)) = -1 ∧
      form.quadrance (Matrix3.rowS (form.halfTurn reflectionNormal reflectionNormalNonNull)) = -1 := by decide

/-- The retained half turn preserves the Lorentz metric and has determinant one. -/
theorem halfTurn_rotation :
    Matrix3.mul
        (Matrix3.mul (form.halfTurn reflectionNormal reflectionNormalNonNull) form.matrix)
        (Matrix3.transpose (form.halfTurn reflectionNormal reflectionNormalNonNull)) = form.matrix ∧
      Matrix3.determinant (form.halfTurn reflectionNormal reflectionNormalNonNull) = 1 := by decide

/-- The retained half turn has trace negative one. -/
theorem halfTurn_trace : Matrix3.trace (form.halfTurn reflectionNormal reflectionNormalNonNull) = -1 := by decide

/-- The retained half turn has half spread one in the original rotation owner. -/
theorem halfTurn_halfSpread :
    Cayley.TernaryForm.rotationHalfSpread form
      (form.halfTurnRotation reflectionNormal reflectionNormalNonNull) = 1 :=
  Cayley.TernaryForm.rotationHalfSpread_halfTurn
    form reflectionNormal reflectionNormalNonNull twoNonzero

/-- The first vector has the displayed rational reflection matrix. -/
theorem first_reflection : form.reflection first firstNonNull =
    Matrix3.scale (1 / 6) ⟨7, 2, 3, -2, 2, -6, -3, -6, -3⟩ := by decide

/-- The second vector has the displayed integral reflection matrix. -/
theorem second_reflection : form.reflection second secondNonNull = ⟨-3, 2, -2, -2, 2, -1, 2, -1, 2⟩ := by decide

/-- The original retained pair has the displayed product of two reflection matrices. -/
theorem reflection_product_matrix :
    Matrix3.mul (form.reflection first firstNonNull) (form.reflection second secondNonNull) =
      Matrix3.scale (1 / 6) ⟨-19, 15, -10, -10, 6, -10, 15, -15, 6⟩ := by decide

/-- The retained reflection product preserves the Lorentz metric and has determinant one. -/
theorem reflection_product_rotation :
    Matrix3.mul
        (Matrix3.mul
          (Matrix3.mul (form.reflection first firstNonNull) (form.reflection second secondNonNull)) form.matrix)
        (Matrix3.transpose
          (Matrix3.mul (form.reflection first firstNonNull) (form.reflection second secondNonNull))) =
        form.matrix ∧
      Matrix3.determinant
        (Matrix3.mul (form.reflection first firstNonNull) (form.reflection second secondNonNull)) = 1 := by decide

/-- The retained reflection-product matrix has trace negative seven sixths. -/
theorem reflection_product_trace :
    Matrix3.trace (Matrix3.mul (form.reflection first firstNonNull)
      (form.reflection second secondNonNull)) = -7 / 6 := by decide

/-- The retained reflection-product rotation has half spread twenty-five twenty-fourths. -/
theorem reflection_product_halfSpread :
    Cayley.TernaryForm.rotationHalfSpread form
        (form.reflectionProductRotation first second firstNonNull secondNonNull) = 25 / 24 :=
  (Cayley.TernaryForm.rotationHalfSpread_reflectionProduct
    form first second firstNonNull secondNonNull twoNonzero).trans spread_first_second

/-- The retained reflection product fixes the cross-product axis `(-5,5,-5)`. -/
theorem reflection_product_fixes_cross :
    Matrix3.rowMul (Lorentz.cross oneNonzero first second)
        (Matrix3.mul (form.reflection first firstNonNull) (form.reflection second secondNonNull)) =
      ⟨-5, 5, -5⟩ := by decide

/-- The retained reflection product fixes the normalized direction `(1,-1,1)`. -/
theorem reflection_product_fixes_normalized_axis :
    Matrix3.rowMul (⟨1, -1, 1⟩ : Vector3 Rational)
        (Matrix3.mul (form.reflection first firstNonNull) (form.reflection second secondNonNull)) =
      ⟨1, -1, 1⟩ := by decide

/-- The retained cross is negative five times its normalized axis direction. -/
theorem cross_normalized_axis_scale :
    Lorentz.cross oneNonzero first second = Vector3.scale (-5) ⟨1, -1, 1⟩ := by decide

/-- The retained cross-to-axis scale is nonzero. -/
theorem normalized_axis_scale_nonzero : (-5 : Rational) ≠ 0 := by decide

/-- The retained rational pair has independent coordinate directions. -/
theorem pair_independent : Vector3.Independent first second := by
  change Vector3.cross first second ≠ Vector3.zero
  decide

/-- A balanced scalar relation between the retained pair has zero coefficients. -/
theorem pair_balanced_scalar_coefficients (left right : Rational)
    (relation : Vector3.sub (Vector3.scale left first) (Vector3.scale right second) = Vector3.zero) :
    left = 0 ∧ right = 0 := by
  have tRelation := congrArg Vector3.t relation
  have rRelation := congrArg Vector3.r relation
  change left * 1 - right * 2 = 0 at tRelation
  change left * 2 - right * -1 = 0 at rRelation
  have fiveRightZero : 5 * right = 0 := by
    calc
      5 * right = (left * 2 - right * -1) - 2 * (left * 1 - right * 2) := by ring1
      _ = 0 := by rw [tRelation, rRelation]; ring1
  have rightZero := ExplicitField.eq_zero_of_mul_eq_zero_left
    (by decide : (5 : Rational) ≠ 0) fiveRightZero
  have leftZero : left = 0 := by
    calc
      left = (left * 1 - right * 2) + right * 2 := by ring1
      _ = 0 := by rw [tRelation, rightZero]; ring1
  exact ⟨leftZero, rightZero⟩

/-- The retained spacelike cap axis has two equal spatial coordinates. -/
@[expose] def capAxis : Vector3 Rational := ⟨0, 1, 1⟩

/-- The retained spacelike cap axis has quadrance minus two and denominator minus one. -/
theorem cap_axis_values : form.quadrance capAxis = -2 ∧
    Lorentz.capDenominator oneNonzero capAxis = -1 := by decide

/-- The original cap denominator of the spacelike example is nonzero. -/
theorem capAxisDefined : Lorentz.capDenominator oneNonzero capAxis ≠ 0 := by decide

/-- The spacelike cap anchor and its square have the paper's displayed entries. -/
theorem cap_axis_anchor :
    Lorentz.anchor oneNonzero capAxis = (⟨0, 1, -1, 1, 0, 0, -1, 0, 0⟩ : Matrix3 Rational) ∧
    Matrix3.mul (Lorentz.anchor oneNonzero capAxis) (Lorentz.anchor oneNonzero capAxis) =
      (⟨2, 0, 0, 0, 1, -1, 0, -1, 1⟩ : Matrix3 Rational) := by decide

/-- The spacelike cap has the displayed rational matrix. -/
theorem cap_matrix : Lorentz.cap oneNonzero capAxis capAxisDefined =
    (⟨-3, -2, 2, -2, -1, 2, 2, 2, -1⟩ : Matrix3 Rational) := by decide

/-- The spacelike cap rows retain the three signed unit quadrances. -/
theorem cap_row_quadrances :
    form.quadrance (Matrix3.rowT (Lorentz.cap oneNonzero capAxis capAxisDefined)) = 1 ∧
    form.quadrance (Matrix3.rowR (Lorentz.cap oneNonzero capAxis capAxisDefined)) = -1 ∧
    form.quadrance (Matrix3.rowS (Lorentz.cap oneNonzero capAxis capAxisDefined)) = -1 := by decide

/-- The original spacelike cap fixes its retained axis. -/
theorem cap_fixes_axis :
    Matrix3.rowMul capAxis (Lorentz.cap oneNonzero capAxis capAxisDefined) = capAxis :=
  Lorentz.rowMul_self_cap oneNonzero capAxis capAxisDefined

/-- The spacelike cap trace and half spread are minus five and two. -/
theorem cap_trace_halfSpread :
    Matrix3.trace (Lorentz.cap oneNonzero capAxis capAxisDefined) = -5 ∧
    Cayley.TernaryForm.rotationHalfSpread form
      (Lorentz.capRotation oneNonzero capAxis capAxisDefined) = 2 := by decide

/-- The spacelike cap retains all displayed half-spread complement and recovery values. -/
theorem cap_halfSpread_identities :
    let halfSpread := Cayley.TernaryForm.rotationHalfSpread form
      (Lorentz.capRotation oneNonzero capAxis capAxisDefined)
    1 - halfSpread = -1 ∧ halfSpread * (1 - halfSpread) = -2 ∧
      halfSpread / (1 - halfSpread) = -2 ∧ 1 - 2 * halfSpread = -3 := by decide

/-- The spacelike cap characteristic polynomial has reciprocal quadratic coefficient minus six. -/
theorem cap_characteristic (X : Rational) :
    Matrix3.characteristicValue (Lorentz.cap oneNonzero capAxis capAxisDefined) X =
      (X - 1) * (X ^ 2 + 6 * X + 1) := by
  have quadrance : (TernaryForm.lorentz oneNonzero).quadrance capAxis = -2 := cap_axis_values.1
  rw [Lorentz.characteristicValue_cap, quadrance, cap_axis_values.2]
  have coefficient : 2 * (1 - -2) / (-1 : Rational) = -6 := by decide
  rw [coefficient]
  ring1

/-- The spacelike cap has rotation-anchor denominator negative four and scaling factor negative one half. -/
theorem cap_rotation_anchor_denominator :
    let rotation := Lorentz.capRotation oneNonzero capAxis capAxisDefined
    rotation.anchorDenominator = -4 ∧ 2 / rotation.anchorDenominator = -1 / 2 := by decide

/-- The spacelike cap has nonzero rotation-anchor denominator. -/
theorem capRotationAnchorDefined :
    (Lorentz.capRotation oneNonzero capAxis capAxisDefined).anchorDenominator ≠ 0 := by decide

/-- The spacelike cap has the paper's displayed adjoint-antisymmetric part. -/
theorem cap_adjoint_antisymmetric :
    (Lorentz.capRotation oneNonzero capAxis capAxisDefined).antisymmetricPart twoNonzero =
      ⟨0, -2, 2, -2, 0, 0, 2, 0, 0⟩ := by decide

/-- The computed spacelike rotation anchor recovers the original vector anchor and its displayed matrix. -/
theorem cap_rotation_anchor_matrix :
    (Lorentz.capRotation oneNonzero capAxis capAxisDefined).anchor capRotationAnchorDefined =
        Lorentz.anchor oneNonzero capAxis ∧
      (Lorentz.capRotation oneNonzero capAxis capAxisDefined).anchor capRotationAnchorDefined =
        ⟨0, 1, -1, 1, 0, 0, -1, 0, 0⟩ := by decide

/-- The computed spacelike rotation anchor reads back the original vector `(0,1,1)`. -/
theorem cap_rotation_anchor_vector :
    Lorentz.rotationAnchorVector oneNonzero
      (Lorentz.capRotation oneNonzero capAxis capAxisDefined) capRotationAnchorDefined = capAxis := by
  decide

/-- The spacelike rotation anchor has quadrance and half twist negative two. -/
theorem cap_rotation_anchor_values :
    let rotation := Lorentz.capRotation oneNonzero capAxis capAxisDefined
    let vector := Lorentz.rotationAnchorVector oneNonzero rotation capRotationAnchorDefined
    form.quadrance vector = -2 ∧
      form.quadrance vector = Cayley.TernaryForm.rotationHalfSpread form rotation /
        (1 - Cayley.TernaryForm.rotationHalfSpread form rotation) := by decide

/-- The retained non-null measurement direction perpendicular to the spacelike cap axis. -/
@[expose] def capPerpendicular : Vector3 Rational := ⟨1, 1, -1⟩

/-- The retained measurement direction is perpendicular to the cap axis and has quadrance minus one. -/
theorem cap_perpendicular_values : form.Perpendicular capPerpendicular capAxis ∧
    form.quadrance capPerpendicular = -1 := by
  change form.bilinear capPerpendicular capAxis = 0 ∧ form.quadrance capPerpendicular = -1
  decide

/-- The cap measurement direction has nonzero original quadrance. -/
theorem capPerpendicularNonNull : form.quadrance capPerpendicular ≠ 0 := by decide

/-- The spacelike cap sends its measurement direction to the paper's displayed vector. -/
theorem cap_perpendicular_image :
    Matrix3.rowMul capPerpendicular (Lorentz.cap oneNonzero capAxis capAxisDefined) =
      ⟨-7, -5, 5⟩ := by decide

/-- The rotated measurement retains quadrance minus one and pairs with the input to give three. -/
theorem cap_perpendicular_image_values :
    form.quadrance
        (Matrix3.rowMul capPerpendicular (Lorentz.cap oneNonzero capAxis capAxisDefined)) = -1 ∧
      form.bilinear capPerpendicular
        (Matrix3.rowMul capPerpendicular (Lorentz.cap oneNonzero capAxis capAxisDefined)) = 3 := by
  decide

/-- The geometric and canonical spreads of the spacelike cap both equal minus eight. -/
theorem cap_geometric_spread :
    form.spread capPerpendicular
        (TernaryForm.Isometry.act (Lorentz.capRotation oneNonzero capAxis capAxisDefined).toIsometry
          capPerpendicular) capPerpendicularNonNull
        ((Lorentz.capRotation oneNonzero capAxis capAxisDefined).toIsometry.quadrance_act_ne_zero
          capPerpendicular capPerpendicularNonNull) = -8 ∧
      Cayley.TernaryForm.rotationSpread form
        (Lorentz.capRotation oneNonzero capAxis capAxisDefined) = -8 := by
  decide

/-- The time axis has nonzero cap denominator two. -/
theorem timeCapDefined : Lorentz.capDenominator oneNonzero time ≠ 0 := by decide

/-- The time-axis cap is the spatial quarter turn fixing that original time axis. -/
theorem spatial_cap :
    Lorentz.cap oneNonzero time timeCapDefined =
      (⟨1, 0, 0, 0, 0, 1, 0, -1, 0⟩ : Matrix3 Rational) ∧
    Matrix3.rowMul time (Lorentz.cap oneNonzero time timeCapDefined) = time := by decide

/-- The boost cap retains a third spatial coordinate of one third. -/
@[expose] def boostAxis : Vector3 Rational := ⟨0, 0, 1 / 3⟩

/-- The boost axis has quadrance minus one ninth and denominator eight ninths. -/
theorem boost_axis_values : form.quadrance boostAxis = -1 / 9 ∧
    Lorentz.capDenominator oneNonzero boostAxis = 8 / 9 := by decide

/-- The boost axis has a nonzero original cap denominator. -/
theorem boostAxisDefined : Lorentz.capDenominator oneNonzero boostAxis ≠ 0 := by decide

/-- The unit spacelike vector on the boost line is excluded from the affine cap domain. -/
theorem boost_unit_excluded :
    form.quadrance (⟨0, 0, 1⟩ : Vector3 Rational) = -1 ∧
    Lorentz.capDenominator oneNonzero (⟨0, 0, 1⟩ : Vector3 Rational) = 0 := by decide

/-- The retained boost cap has the displayed scaled matrix. -/
theorem boost_cap_matrix : Lorentz.cap oneNonzero boostAxis boostAxisDefined =
    Matrix3.scale (1 / 4) (⟨5, 3, 0, 3, 5, 0, 0, 0, 4⟩ : Matrix3 Rational) := by decide

/-- The boost frame with the time basis vector has determinant one quarter. -/
theorem boost_time_frame_determinant :
    Vector3.determinant boostAxis time
      (Matrix3.rowMul time (Lorentz.cap oneNonzero boostAxis boostAxisDefined)) = 1 / 4 := by
  decide

/-- The same boost frame with the first space basis vector has determinant minus one quarter. -/
theorem boost_space_frame_determinant :
    Vector3.determinant boostAxis (⟨0, 1, 0⟩ : Vector3 Rational)
      (Matrix3.rowMul ⟨0, 1, 0⟩ (Lorentz.cap oneNonzero boostAxis boostAxisDefined)) = -1 / 4 := by
  decide

/-- The retained boost cap rows have quadrances one, minus one and minus one. -/
theorem boost_cap_row_quadrances :
    form.quadrance (Matrix3.rowT (Lorentz.cap oneNonzero boostAxis boostAxisDefined)) = 1 ∧
    form.quadrance (Matrix3.rowR (Lorentz.cap oneNonzero boostAxis boostAxisDefined)) = -1 ∧
    form.quadrance (Matrix3.rowS
      (Lorentz.cap oneNonzero boostAxis boostAxisDefined)) = -1 := by decide

/-- The boost half spread is minus one eighth and its time-axis velocity ratio is three fifths. -/
theorem boost_halfSpread_velocity :
    Cayley.TernaryForm.rotationHalfSpread form
      (Lorentz.capRotation oneNonzero boostAxis boostAxisDefined) = -1 / 8 ∧
    (Lorentz.cap oneNonzero boostAxis boostAxisDefined).tr /
      (Lorentz.cap oneNonzero boostAxis boostAxisDefined).tt = 3 / 5 := by decide

/-- The retained parabolic anchor is the original nonzero null direction. -/
@[expose] def parabolicAxis : Vector3 Rational := ⟨1, 1, 0⟩

/-- The parabolic axis is null and its original cap denominator is one. -/
theorem parabolic_axis_values : form.quadrance parabolicAxis = 0 ∧
    Lorentz.capDenominator oneNonzero parabolicAxis = 1 := by decide

/-- The original parabolic cap denominator is nonzero. -/
theorem parabolicAxisDefined : Lorentz.capDenominator oneNonzero parabolicAxis ≠ 0 := by decide

/-- The parabolic cap has the displayed matrix and fixes its original null axis. -/
theorem parabolic_cap_matrix :
    Lorentz.cap oneNonzero parabolicAxis parabolicAxisDefined =
      (⟨3, 2, -2, -2, -1, 2, -2, -2, 1⟩ : Matrix3 Rational) ∧
    Matrix3.rowMul parabolicAxis (Lorentz.cap oneNonzero parabolicAxis parabolicAxisDefined) =
      parabolicAxis := by decide

/-- The original parabolic cap is distinct from the identity matrix. -/
theorem parabolic_cap_nonidentity :
    Lorentz.cap oneNonzero parabolicAxis parabolicAxisDefined ≠ Matrix3.identity := by decide

/-- The original parabolic cap minus identity has cube zero. -/
theorem parabolic_cap_nilpotent :
    let difference := Matrix3.sub
      (Lorentz.cap oneNonzero parabolicAxis parabolicAxisDefined) Matrix3.identity
    Matrix3.mul (Matrix3.mul difference difference) difference = Matrix3.zero := by decide

/-- Every scalar input gives the cubic unipotent characteristic polynomial of the parabolic cap. -/
theorem parabolic_cap_characteristic (X : Rational) :
    Matrix3.characteristicValue (Lorentz.cap oneNonzero parabolicAxis parabolicAxisDefined) X =
      (X - 1) ^ 3 :=
  Lorentz.characteristicValue_cap_of_null
    oneNonzero parabolicAxis parabolicAxisDefined parabolic_axis_values.1 X

/-- The retained normals have nonzero Lorentz pairing one. -/
theorem reflectionProductPairingNonzero : form.bilinear first second ≠ 0 := by decide

/-- The retained reflection product has a nonzero computed anchor denominator. -/
theorem reflectionProductAnchorDefined :
    (form.reflectionProductRotation first second firstNonNull secondNonNull).anchorDenominator ≠ 0 :=
  form.reflectionProduct_anchorDefined first second firstNonNull secondNonNull
    reflectionProductPairingNonzero twoNonzero

/-- The computed anchor of the retained normals is the anchor of their signed cross. -/
theorem reflection_product_anchor_matrix :
    (form.reflectionProductRotation first second firstNonNull secondNonNull).anchor reflectionProductAnchorDefined =
      Lorentz.anchor oneNonzero (⟨-5, 5, -5⟩ : Vector3 Rational) := by decide

/-- The original vector readback of the retained reflection product is `(-5,5,-5)`. -/
theorem reflection_product_anchor_vector :
    Lorentz.rotationAnchorVector oneNonzero
      (form.reflectionProductRotation first second firstNonNull secondNonNull) reflectionProductAnchorDefined =
        (⟨-5, 5, -5⟩ : Vector3 Rational) := by decide

/-- The reflection-product anchor has quadrance and half twist negative twenty-five. -/
theorem reflection_product_anchor_values :
    let vector := Lorentz.rotationAnchorVector oneNonzero
      (form.reflectionProductRotation first second firstNonNull secondNonNull) reflectionProductAnchorDefined
    form.quadrance vector = -25 ∧
      form.quadrance vector = form.spread first second firstNonNull secondNonNull /
        (1 - form.spread first second firstNonNull secondNonNull) := by decide

/-- The second normal obtained from the spacelike cap and its retained perpendicular first normal. -/
@[expose] def capSecondNormal : Vector3 Rational :=
  Vector3.add capPerpendicular (Lorentz.cross oneNonzero capAxis capPerpendicular)

/-- The cap construction retains its exact cross, second normal, quadrances, pairing and cross of normals. -/
theorem cap_second_normal_values :
    Lorentz.cross oneNonzero capAxis capPerpendicular = ⟨2, 1, -1⟩ ∧
      capSecondNormal = ⟨3, 2, -2⟩ ∧ form.quadrance capPerpendicular = -1 ∧
      form.quadrance capSecondNormal = 1 ∧
      form.quadrance capSecondNormal = form.quadrance capPerpendicular * (1 + form.quadrance capAxis) ∧
      form.bilinear capPerpendicular capSecondNormal = -1 ∧
      Lorentz.cross oneNonzero capPerpendicular capSecondNormal = ⟨0, -1, -1⟩ := by decide

/-- The constructed second normal has nonzero original Lorentz quadrance. -/
theorem capSecondNormalNonNull : form.quadrance capSecondNormal ≠ 0 := by decide

/-- The retained perpendicular first normal and constructed second normal have nonzero pairing. -/
theorem capNormalsPairingNonzero : form.bilinear capPerpendicular capSecondNormal ≠ 0 := by decide

/-- The constructed normals have a defined reflection-product anchor. -/
theorem capNormalsAnchorDefined :
    (form.reflectionProductRotation capPerpendicular capSecondNormal
      capPerpendicularNonNull capSecondNormalNonNull).anchorDenominator ≠ 0 :=
  form.reflectionProduct_anchorDefined capPerpendicular capSecondNormal
    capPerpendicularNonNull capSecondNormalNonNull capNormalsPairingNonzero twoNonzero

/-- The spacelike cap factorization reads back its original vector `(0,1,1)`. -/
theorem cap_reflection_product_anchor :
    Lorentz.rotationAnchorVector oneNonzero
        (form.reflectionProductRotation capPerpendicular capSecondNormal
          capPerpendicularNonNull capSecondNormalNonNull) capNormalsAnchorDefined = capAxis := by decide

/-- The constructed reflections multiply to the original spacelike cap rotation. -/
theorem cap_reflection_product :
    form.reflectionProductRotation capPerpendicular capSecondNormal capPerpendicularNonNull capSecondNormalNonNull =
      Lorentz.capRotation oneNonzero capAxis capAxisDefined := by
  apply Basic.TernaryForm.SpecialOrthogonal.eq_of_matrix_eq
  decide

/-- The first anchor in the non-collinear composition example. -/
@[expose] def compositionLeft : Vector3 Rational := ⟨2, 1, 0⟩

/-- The second anchor in the non-collinear composition example. -/
@[expose] def compositionRight : Vector3 Rational := ⟨1, 0, 2⟩

/-- Both example anchors have admissible caps and a nonzero affine product denominator. -/
theorem composition_domains :
    Lorentz.capDenominator oneNonzero compositionLeft ≠ 0 ∧
    Lorentz.capDenominator oneNonzero compositionRight ≠ 0 ∧
    Lorentz.anchorProductDenominator oneNonzero compositionLeft compositionRight ≠ 0 := by
  decide

/-- The composition pair has quadrances three and minus three, pairing two and signed cross `(-2,-4,-1)`. -/
theorem composition_input_values : form.quadrance compositionLeft = 3 ∧ form.quadrance compositionRight = -3 ∧
    form.bilinear compositionLeft compositionRight = 2 ∧
    Lorentz.cross oneNonzero compositionLeft compositionRight = ⟨-2, -4, -1⟩ := by decide

/-- The computed composition anchor is `(-5,-5,-3)`, with quadrance minus nine and cap denominator minus eight. -/
theorem composition_anchor_values :
    Lorentz.anchorProduct oneNonzero compositionLeft compositionRight composition_domains.2.2 =
      ⟨-5, -5, -3⟩ ∧
    form.quadrance (⟨-5, -5, -3⟩ : Vector3 Rational) = -9 ∧
    Lorentz.capDenominator oneNonzero (⟨-5, -5, -3⟩ : Vector3 Rational) = -8 := by decide

/-- The three caps in the composition example have half spreads three quarters, three halves and nine eighths. -/
theorem composition_halfSpreads :
    Cayley.TernaryForm.rotationHalfSpread form
      (Lorentz.capRotation oneNonzero compositionLeft composition_domains.1) = 3 / 4 ∧
    Cayley.TernaryForm.rotationHalfSpread form
      (Lorentz.capRotation oneNonzero compositionRight composition_domains.2.1) = 3 / 2 ∧
    Cayley.TernaryForm.rotationHalfSpread form
      (Basic.TernaryForm.SpecialOrthogonal.mul
        (Lorentz.capRotation oneNonzero compositionLeft composition_domains.1)
        (Lorentz.capRotation oneNonzero compositionRight composition_domains.2.1)) = 9 / 8 := by
  decide

/-- Squaring the spatial quarter turn gives the displayed half turn about the time axis. -/
theorem spatial_quarter_turn_square :
    Matrix3.mul (Lorentz.cap oneNonzero time timeCapDefined)
        (Lorentz.cap oneNonzero time timeCapDefined) =
      (⟨1, 0, 0, 0, -1, 0, 0, 0, -1⟩ : Matrix3 Rational) ∧
    form.halfTurn (⟨2, 0, 0⟩ : Vector3 Rational) (by decide) =
      (⟨1, 0, 0, 0, -1, 0, 0, 0, -1⟩ : Matrix3 Rational) := by decide

/-- The one-third circular anchor gives the exact three-four-five spatial rotation. -/
theorem circular_third_cap :
    Lorentz.cap oneNonzero (⟨1 / 3, 0, 0⟩ : Vector3 Rational) (by decide) =
      Matrix3.scale (1 / 5) (⟨5, 0, 0, 0, 4, 3, 0, -3, 4⟩ : Matrix3 Rational) := by decide

/-- Doubling the one-third circular anchor gives parameter three quarters and the displayed spatial rotation. -/
theorem circular_third_double :
    Lorentz.anchorProduct oneNonzero
        (⟨1 / 3, 0, 0⟩ : Vector3 Rational) ⟨1 / 3, 0, 0⟩ (by decide) = ⟨3 / 4, 0, 0⟩ ∧
    Matrix3.mul (Lorentz.cap oneNonzero (⟨1 / 3, 0, 0⟩ : Vector3 Rational) (by decide))
        (Lorentz.cap oneNonzero (⟨1 / 3, 0, 0⟩ : Vector3 Rational) (by decide)) =
      Matrix3.scale (1 / 25) (⟨25, 0, 0, 0, 7, 24, 0, -24, 7⟩ : Matrix3 Rational) ∧
    Lorentz.cap oneNonzero (⟨3 / 4, 0, 0⟩ : Vector3 Rational) (by decide) =
      Matrix3.scale (1 / 25) (⟨25, 0, 0, 0, 7, 24, 0, -24, 7⟩ : Matrix3 Rational) := by decide

/-- The doubled boost has anchor parameter three fifths and physical velocity fifteen seventeenths. -/
theorem boost_double_values :
    Lorentz.anchorProduct oneNonzero boostAxis boostAxis (by decide) = ⟨0, 0, 3 / 5⟩ ∧
    (2 * (1 / 3 : Rational)) / (1 + (1 / 3) ^ 2) = 3 / 5 ∧
    (2 * (3 / 5 : Rational)) / (1 + (3 / 5) ^ 2) = 15 / 17 ∧
    ((3 / 5 : Rational) + 3 / 5) / (1 + (3 / 5) ^ 2) = 15 / 17 := by decide

/-- The named boost-velocity operation gives three fifths, then fifteen seventeenths under doubling. -/
theorem boost_velocity_values :
    Lorentz.boostVelocity (1 / 3 : Rational) = 3 / 5 ∧
    Lorentz.boostVelocity (3 / 5 : Rational) = 15 / 17 ∧
    Lorentz.boostVelocity ((1 / 3 + 1 / 3) / (1 + (1 / 3) ^ 2) : Rational) = 15 / 17 := by
  decide

/-- Two perpendicular boost anchors acquire opposite time components when their order is reversed. -/
theorem perpendicular_boost_products :
    form.bilinear boostAxis (⟨0, 1 / 3, 0⟩ : Vector3 Rational) = 0 ∧
    Lorentz.cross oneNonzero boostAxis (⟨0, 1 / 3, 0⟩ : Vector3 Rational) = ⟨1 / 9, 0, 0⟩ ∧
    Lorentz.anchorProduct oneNonzero boostAxis (⟨0, 1 / 3, 0⟩ : Vector3 Rational)
      (by decide) = ⟨-1 / 9, 1 / 3, 1 / 3⟩ ∧
    Lorentz.anchorProduct oneNonzero (⟨0, 1 / 3, 0⟩ : Vector3 Rational) boostAxis
      (by decide) = ⟨1 / 9, 1 / 3, 1 / 3⟩ := by decide

/-- The partial-associativity example permits the left grouping and forbids the right inner product. -/
theorem partial_association_values :
    form.bilinear first second = 1 ∧
    form.bilinear (⟨2, 0, 0⟩ : Vector3 Rational) first = 2 ∧
    Lorentz.anchorProduct oneNonzero (⟨2, 0, 0⟩ : Vector3 Rational) first (by decide) =
      ⟨-3, -8, 1⟩ ∧
    form.bilinear (⟨-3, -8, 1⟩ : Vector3 Rational) second = -15 ∧
    Lorentz.anchorProductDenominator oneNonzero first second = 0 ∧
    Lorentz.anchorProductDenominator oneNonzero (⟨-3, -8, 1⟩ : Vector3 Rational) second ≠ 0 := by
  decide

/-- Both retained reflection normals also give admissible cap anchors. -/
theorem firstSecondCapsDefined :
    Lorentz.capDenominator oneNonzero first ≠ 0 ∧
    Lorentz.capDenominator oneNonzero second ≠ 0 := by decide

/-- The forbidden affine product retains numerator `(8,-4,9)` with quadrance minus thirty-three. -/
theorem forbidden_product_values :
    Lorentz.anchorProductNumerator oneNonzero first second = ⟨8, -4, 9⟩ ∧
    form.quadrance (⟨8, -4, 9⟩ : Vector3 Rational) = -33 ∧
    Cayley.TernaryForm.rotationHalfSpread form
      (Lorentz.capRotation oneNonzero first firstSecondCapsDefined.1) = 12 / 11 ∧
    Cayley.TernaryForm.rotationHalfSpread form
      (Lorentz.capRotation oneNonzero second firstSecondCapsDefined.2) = 2 / 3 := by decide

/-- The surviving forbidden-product numerator has nonzero Lorentz quadrance. -/
theorem forbiddenNumeratorNonNull : form.quadrance (⟨8, -4, 9⟩ : Vector3 Rational) ≠ 0 := by decide

/-- The forbidden affine product's original cap composition is the displayed half-turn matrix. -/
theorem forbidden_product_matrix :
    Matrix3.mul (Lorentz.cap oneNonzero first firstSecondCapsDefined.1)
        (Lorentz.cap oneNonzero second firstSecondCapsDefined.2) =
      Matrix3.scale (1 / 33) (⟨-161, 64, -144, -64, -1, -72, 144, -72, 129⟩ : Matrix3 Rational) ∧
    form.halfTurn (⟨8, -4, 9⟩ : Vector3 Rational) forbiddenNumeratorNonNull =
      Matrix3.scale (1 / 33) (⟨-161, 64, -144, -64, -1, -72, 144, -72, 129⟩ : Matrix3 Rational) := by
  have cast161 : (161 : Rational) = fromInt 161 := by
    simpa only [Nat.cast_ofNat] using natCast_eq_fromInt 161
  have cast144 : (144 : Rational) = fromInt 144 := by
    simpa only [Nat.cast_ofNat] using natCast_eq_fromInt 144
  have cast129 : (129 : Rational) = fromInt 129 := by
    simpa only [Nat.cast_ofNat] using natCast_eq_fromInt 129
  have cast72 : (72 : Rational) = fromInt 72 := by
    simpa only [Nat.cast_ofNat] using natCast_eq_fromInt 72
  have cast64 : (64 : Rational) = fromInt 64 := by
    simpa only [Nat.cast_ofNat] using natCast_eq_fromInt 64
  have halfTurnDisplayed : form.halfTurn (⟨8, -4, 9⟩ : Vector3 Rational) forbiddenNumeratorNonNull =
      Matrix3.scale (1 / 33) (⟨-161, 64, -144, -64, -1, -72, 144, -72, 129⟩ : Matrix3 Rational) := by
    change (TernaryForm.lorentz oneNonzero).halfTurn ⟨8, -4, 9⟩ forbiddenNumeratorNonNull = _
    rw [Lorentz.halfTurn_coordinates oneNonzero ⟨8, -4, 9⟩ forbiddenNumeratorNonNull]
    rw [cast161, cast144, cast129, cast72, cast64]
    ext <;> decide
  have productRotation := Lorentz.capRotation_mul_of_pairing_one
    oneNonzero first second firstSecondCapsDefined.1 firstSecondCapsDefined.2 bilinear_first_second
  have axisTransport := form.halfTurnRotation_eq_of_axis_eq
    (Lorentz.anchorProductNumerator oneNonzero first second) ⟨8, -4, 9⟩
    (Lorentz.anchorProductNumerator_nonNull_of_pairing_one
      oneNonzero first second firstSecondCapsDefined.1 firstSecondCapsDefined.2 bilinear_first_second)
    forbiddenNumeratorNonNull forbidden_product_values.1
  have productMatrix := congrArg (fun rotation : form.SpecialOrthogonal => rotation.matrix)
    (productRotation.trans axisTransport)
  exact ⟨productMatrix.trans halfTurnDisplayed, halfTurnDisplayed⟩

end Purelib.Examples.Geometry.Quadratic.Ternary.Lorentz
