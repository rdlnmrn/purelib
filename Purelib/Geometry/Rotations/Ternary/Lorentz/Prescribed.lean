module

public import Purelib.Geometry.Rotations.Axis.Parameters
public import Purelib.Geometry.Rotations.Ternary.Lorentz.Anchor
import Purelib.Geometry.Rotations.Ternary.Lorentz.Orientation
import Purelib.Geometry.Rotations.Ternary.Cayley.HalfTurn
import Purelib.Geometry.Quadratic.Ternary.Spread
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Lorentz rotations with prescribed axis and half spread

A retained root of the axis square condition computes two opposite anchor
vectors in the original time-first Lorentz form. Their original caps have
the requested half spread and complete fixed line. Every other solution
has one of these two matrices.
-/

public section

namespace Purelib.Geometry.Rotations.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field
open Purelib.Algebra.Field.Squares
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.Geometry.Rotations.Axis
open Purelib.Geometry.Rotations.Ternary
open Purelib.Geometry.Rotations.Ternary.Basic.TernaryForm
open Purelib.LinearAlgebra.Coordinates3 (Matrix3)
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K] (oneNonzero : (1 : K) ≠ 0)

/-- The square condition retains the original Lorentz axis quadrance and requested half spread. -/
@[expose] def prescribedAxisSquareValue (axis : Vector3 K) (amount : K) : K :=
  Parameters.squareValue ((Form.lorentz oneNonzero).quadrance axis) amount

/-- Compute the Lorentz anchor scale from the original square-condition root. -/
@[expose] def prescribedAnchorScale (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount)) : K :=
  Parameters.anchorScale ((Form.lorentz oneNonzero).quadrance axis) amount certificate

set_option genInjectivity false in
/-- A Lorentz rotation with a retained nonzero scale identifying its computed anchor with the prescribed axis.

The original form-indexed rotation, anchor-domain certificate and requested half spread are retained together. -/
structure PrescribedAxisRotation (axis : Vector3 K) (amount : K) where
  /-- The original Lorentz rotation. -/ rotation : (Form.lorentz oneNonzero).SpecialOrthogonal
  /-- The retained rotation is not a half turn. -/
  notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1
  /-- The retained rotation has the requested half spread. -/
  halfSpread_eq : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation = amount
  /-- The original computed anchor denominator is nonzero. -/ anchorDefined : rotation.anchorDenominator ≠ 0
  /-- The retained scale from the prescribed axis to the computed anchor. -/ anchorScale : K
  /-- The retained axis scale is nonzero. -/ anchorScaleNonzero : anchorScale ≠ 0
  /-- The original computed Lorentz anchor is the prescribed axis multiplied by the retained scale. -/
  anchor_eq : rotationAnchorVector oneNonzero rotation anchorDefined = Vector3.scale anchorScale axis

/-- The root-derived Lorentz anchor has nonzero original cap denominator. -/
theorem prescribedAnchor_capDefined (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount))
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1) :
    capDenominator oneNonzero (Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate) axis) ≠ 0 := by
  unfold capDenominator
  rw [Form.quadrance_scale]
  exact Parameters.denominator_nonzero _ amount certificate axisNonNull amountNotOne

/-- The cap of the retained root-derived anchor has exactly the requested half spread. -/
theorem halfSpread_prescribedAnchor (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount))
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
      (capRotation oneNonzero (Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate) axis)
        (prescribedAnchor_capDefined oneNonzero axis amount certificate axisNonNull amountNotOne)) = amount := by
  rw [halfSpread_cap oneNonzero _ _ twoNonzero, Form.quadrance_scale]
  unfold capDenominator
  rw [Form.quadrance_scale]
  exact Parameters.halfSpread _ amount certificate axisNonNull amountNotOne

/-- Construct the original Lorentz rotation from the supplied axis square certificate.

The same retained root computes the nonzero axis scale, cap denominator and original computed anchor. -/
@[expose] def prescribedAxisRotationOfSquare (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount))
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) : PrescribedAxisRotation oneNonzero axis amount where
  rotation := capRotation oneNonzero
    (Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate) axis)
    (prescribedAnchor_capDefined oneNonzero axis amount certificate axisNonNull amountNotOne)
  notHalfTurn := halfSpread_cap_ne_one oneNonzero _ _ twoNonzero
  halfSpread_eq := halfSpread_prescribedAnchor oneNonzero axis amount certificate axisNonNull amountNotOne twoNonzero
  anchorDefined := (Form.SpecialOrthogonal.anchorDenominator_ne_zero_iff _ twoNonzero).mpr
    (halfSpread_cap_ne_one oneNonzero _ _ twoNonzero)
  anchorScale := prescribedAnchorScale oneNonzero axis amount certificate
  anchorScaleNonzero := Parameters.anchorScale_nonzero _ amount certificate axisNonNull amountNotOne
  anchor_eq := rotationAnchorVector_cap oneNonzero _ _ twoNonzero

/-- A retained prescribed-axis Lorentz rotation supplies the nonzero root of its axis square condition.

Its original recovered anchor quadrance gives the half-twist equation for the same retained axis scale. -/
@[expose] def PrescribedAxisRotation.squareCertificate [DecidableEq K] {axis : Vector3 K} {amount : K}
    (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) : Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount) := by
  have halfTwist := quadrance_rotationAnchorVector oneNonzero candidate.rotation twoNonzero candidate.notHalfTurn
  change (Form.lorentz oneNonzero).quadrance
      (rotationAnchorVector oneNonzero candidate.rotation candidate.anchorDefined) = _ at halfTwist
  rw [candidate.anchor_eq, Form.quadrance_scale, candidate.halfSpread_eq] at halfTwist
  exact Parameters.squareCertificate _ amount candidate.anchorScale candidate.anchorScaleNonzero
    axisNonNull amountNotOne halfTwist

/-- A prescribed non-half-turn Lorentz rotation exists exactly when its retained axis square condition has a root. -/
theorem prescribedAxisRotation_exists_iff [DecidableEq K] (axis : Vector3 K) (amount : K)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (_amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (PrescribedAxisRotation oneNonzero axis amount) ↔
      Nonempty (Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount)) := by
  constructor
  · rintro ⟨candidate⟩
    exact ⟨candidate.squareCertificate oneNonzero axisNonNull amountNotOne twoNonzero⟩
  · rintro ⟨certificate⟩
    exact ⟨prescribedAxisRotationOfSquare oneNonzero axis amount certificate axisNonNull amountNotOne twoNonzero⟩

/-- The same Lorentz axis condition is equivalent to the condition using full spread. -/
theorem prescribedAxis_square_iff_spreadSquare (axis : Vector3 K) (amount : K) (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount)) ↔
      Nonempty (Witness.NonzeroSquare ((Form.lorentz oneNonzero).quadrance axis * (4 * amount * (1 - amount)))) :=
  Parameters.square_iff_spread _ amount twoNonzero

/-- Negating the retained square root negates the computed Lorentz anchor vector. -/
theorem prescribedAnchorVector_neg (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount)) :
    Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate.neg) axis =
      Vector3.neg (Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate) axis) := by
  have scaleNeg : prescribedAnchorScale oneNonzero axis amount certificate.neg =
      -prescribedAnchorScale oneNonzero axis amount certificate := Parameters.anchorScale_neg _ amount certificate
  rw [scaleNeg]
  ext <;> unfold Vector3.scale Vector3.neg <;> ring1

/-- A retained prescribed-axis rotation fixes exactly the scalar multiples of its original Lorentz axis.

The original computed anchor and its nonzero scale transport the cap's complete fixed line to the supplied axis. -/
theorem PrescribedAxisRotation.fixed_iff_scale [DecidableEq K] {axis : Vector3 K} {amount : K}
    (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (vector : Vector3 K) :
    Matrix3.rowMul vector candidate.rotation.matrix = vector ↔
      ∃ factor : K, vector = Vector3.scale factor axis := by
  let recovered := rotationAnchorVector oneNonzero candidate.rotation candidate.anchorDefined
  let defined := rotationAnchorVector_defined oneNonzero candidate.rotation twoNonzero candidate.notHalfTurn
  have recoveredEqual : recovered = Vector3.scale candidate.anchorScale axis := candidate.anchor_eq
  have recoveredNonNull : (Form.lorentz oneNonzero).quadrance recovered ≠ 0 := by
    rw [recoveredEqual]
    exact (Form.lorentz oneNonzero).quadrance_scale_ne_zero candidate.anchorScale axis
      candidate.anchorScaleNonzero axisNonNull
  have capEqual : (capRotation oneNonzero recovered defined).matrix = candidate.rotation.matrix :=
    congrArg (fun value : (Form.lorentz oneNonzero).SpecialOrthogonal => value.matrix)
      (cap_rotationAnchorVector oneNonzero candidate.rotation twoNonzero candidate.notHalfTurn)
  constructor
  · intro fixed
    have projected := (rowMul_cap_eq_self_iff_projection oneNonzero recovered vector defined
      recoveredNonNull twoNonzero).mp ((congrArg (Matrix3.rowMul vector) capEqual).trans fixed)
    refine ⟨((Form.lorentz oneNonzero).bilinear vector recovered /
      (Form.lorentz oneNonzero).quadrance recovered) * candidate.anchorScale, ?_⟩
    calc
      vector = Vector3.scale ((Form.lorentz oneNonzero).bilinear vector recovered /
          (Form.lorentz oneNonzero).quadrance recovered) recovered := projected
      _ = Vector3.scale (((Form.lorentz oneNonzero).bilinear vector recovered /
          (Form.lorentz oneNonzero).quadrance recovered) * candidate.anchorScale) axis := by
        rw [recoveredEqual, Vector3.scale_scale]
  · rintro ⟨factor, equal⟩
    have anchorFixed := rowMul_rotationAnchorVector oneNonzero candidate.rotation twoNonzero candidate.notHalfTurn
    change Matrix3.rowMul recovered candidate.rotation.matrix = recovered at anchorFixed
    rw [recoveredEqual] at anchorFixed
    have cancel : candidate.anchorScale⁻¹ * candidate.anchorScale = 1 := by
      rw [mul_comm]
      exact ExplicitField.mul_inv_cancel candidate.anchorScale candidate.anchorScaleNonzero
    have axisFixed : Matrix3.rowMul axis candidate.rotation.matrix = axis := by
      calc
        _ = Vector3.scale candidate.anchorScale⁻¹
            (Matrix3.rowMul (Vector3.scale candidate.anchorScale axis) candidate.rotation.matrix) := by
          rw [← Matrix3.rowMul_vector_scale, Vector3.scale_scale, cancel, Vector3.one_scale]
        _ = Vector3.scale candidate.anchorScale⁻¹ (Vector3.scale candidate.anchorScale axis) :=
          congrArg (Vector3.scale candidate.anchorScale⁻¹) anchorFixed
        _ = axis := by rw [Vector3.scale_scale, cancel, Vector3.one_scale]
    calc
      Matrix3.rowMul vector candidate.rotation.matrix =
          Matrix3.rowMul (Vector3.scale factor axis) candidate.rotation.matrix :=
        congrArg (fun value => Matrix3.rowMul value candidate.rotation.matrix) equal
      _ = Vector3.scale factor axis := by rw [Matrix3.rowMul_vector_scale, axisFixed]
      _ = vector := equal.symm

/-- Prescribing the complete Lorentz fixed line and a non-endpoint half spread is equivalent to the square condition.

The geometric condition uses the original matrix; its same computed anchor supplies the retained nonzero axis scale. -/
theorem prescribedAxis_fixedLine_exists_iff [DecidableEq K] (axis : Vector3 K) (amount : K)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNonzero : amount ≠ 0)
    (amountNotOne : amount ≠ 1) (twoNonzero : (2 : K) ≠ 0) :
    (∃ rotation : (Form.lorentz oneNonzero).SpecialOrthogonal,
      Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation = amount ∧
      ∀ vector : Vector3 K, Matrix3.rowMul vector rotation.matrix = vector ↔
        ∃ factor : K, vector = Vector3.scale factor axis) ↔
      Nonempty (Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount)) := by
  constructor
  · rintro ⟨rotation, halfSpread, fixedLine⟩
    have notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation ≠ 1 := by
      intro equal
      exact amountNotOne (halfSpread.symm.trans equal)
    let anchorDefined := (rotation.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn
    let recovered := rotationAnchorVector oneNonzero rotation anchorDefined
    have recoveredFixed : Matrix3.rowMul recovered rotation.matrix = recovered :=
      rowMul_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn
    obtain ⟨factor, recoveredEqual⟩ := (fixedLine recovered).mp recoveredFixed
    have recoveredNonNull : (Form.lorentz oneNonzero).quadrance recovered ≠ 0 := by
      rw [quadrance_rotationAnchorVector oneNonzero rotation twoNonzero notHalfTurn, halfSpread]
      exact ExplicitField.div_ne_zero amountNonzero (ExplicitField.one_sub_ne_zero_of_ne_one amountNotOne)
    have factorNonzero : factor ≠ 0 := by
      intro zero
      rw [recoveredEqual, zero, Vector3.zero_scale, Form.quadrance_zero] at recoveredNonNull
      exact recoveredNonNull rfl
    let candidate : PrescribedAxisRotation oneNonzero axis amount :=
      ⟨rotation, notHalfTurn, halfSpread, anchorDefined, factor, factorNonzero, recoveredEqual⟩
    exact ⟨candidate.squareCertificate oneNonzero axisNonNull amountNotOne twoNonzero⟩
  · rintro ⟨certificate⟩
    let candidate := prescribedAxisRotationOfSquare oneNonzero axis amount certificate
      axisNonNull amountNotOne twoNonzero
    exact ⟨candidate.rotation, candidate.halfSpread_eq, candidate.fixed_iff_scale oneNonzero axisNonNull twoNonzero⟩

/-- Every retained prescribed-axis Lorentz solution has one of the two matrices computed from the original root. -/
theorem PrescribedAxisRotation.matrix_eq_pair [DecidableEq K] {axis : Vector3 K} {amount : K}
    (candidate : PrescribedAxisRotation oneNonzero axis amount)
    (certificate : Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount))
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    candidate.rotation.matrix = (prescribedAxisRotationOfSquare oneNonzero axis amount certificate
      axisNonNull amountNotOne twoNonzero).rotation.matrix ∨
      candidate.rotation.matrix = (prescribedAxisRotationOfSquare oneNonzero axis amount certificate.neg
        axisNonNull amountNotOne twoNonzero).rotation.matrix := by
  have halfTwist := quadrance_rotationAnchorVector oneNonzero candidate.rotation twoNonzero candidate.notHalfTurn
  change (Form.lorentz oneNonzero).quadrance
      (rotationAnchorVector oneNonzero candidate.rotation candidate.anchorDefined) = _ at halfTwist
  rw [candidate.anchor_eq, Form.quadrance_scale, candidate.halfSpread_eq] at halfTwist
  have scales := Parameters.scale_eq_or_eq_neg _ amount candidate.anchorScale certificate
    axisNonNull amountNotOne halfTwist
  let recovered := rotationAnchorVector oneNonzero candidate.rotation candidate.anchorDefined
  let defined := rotationAnchorVector_defined oneNonzero candidate.rotation twoNonzero candidate.notHalfTurn
  have recoveredCap : candidate.rotation.matrix = (capRotation oneNonzero recovered defined).matrix :=
    congrArg (fun value : (Form.lorentz oneNonzero).SpecialOrthogonal => value.matrix)
      (cap_rotationAnchorVector oneNonzero candidate.rotation twoNonzero candidate.notHalfTurn).symm
  rcases scales with positive | negative
  · left
    have vectorEqual : recovered = Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate) axis :=
      candidate.anchor_eq.trans (congrArg (fun scale => Vector3.scale scale axis) positive)
    exact recoveredCap.trans (congrArg (fun value : (Form.lorentz oneNonzero).SpecialOrthogonal => value.matrix)
      (capRotation_congr_vector oneNonzero vectorEqual defined
        (prescribedAnchor_capDefined oneNonzero axis amount certificate axisNonNull amountNotOne)))
  · right
    have vectorEqual : recovered = Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate.neg) axis :=
      candidate.anchor_eq.trans (congrArg (fun scale => Vector3.scale scale axis) negative)
    exact recoveredCap.trans (congrArg (fun value : (Form.lorentz oneNonzero).SpecialOrthogonal => value.matrix)
      (capRotation_congr_vector oneNonzero vectorEqual defined
        (prescribedAnchor_capDefined oneNonzero axis amount certificate.neg axisNonNull amountNotOne)))

/-- The two root-derived Lorentz rotations have distinct original matrices. -/
theorem prescribedAxisRotation_pair_distinct [DecidableEq K] (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount))
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    (prescribedAxisRotationOfSquare oneNonzero axis amount certificate
      axisNonNull amountNotOne twoNonzero).rotation.matrix ≠
      (prescribedAxisRotationOfSquare oneNonzero axis amount certificate.neg
        axisNonNull amountNotOne twoNonzero).rotation.matrix := by
  intro equal
  let positive := Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate) axis
  let negative := Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate.neg) axis
  have vectorsEqual : positive = negative := cap_injective oneNonzero positive negative
    (prescribedAnchor_capDefined oneNonzero axis amount certificate axisNonNull amountNotOne)
    (prescribedAnchor_capDefined oneNonzero axis amount certificate.neg axisNonNull amountNotOne) twoNonzero equal
  have positiveZero := Vector3.eq_zero_of_eq_neg positive twoNonzero
    (vectorsEqual.trans (prescribedAnchorVector_neg oneNonzero axis amount certificate))
  have nonNull := (Form.lorentz oneNonzero).quadrance_scale_ne_zero
    (prescribedAnchorScale oneNonzero axis amount certificate) axis
    (Parameters.anchorScale_nonzero _ amount certificate axisNonNull amountNotOne) axisNonNull
  apply nonNull
  change (Form.lorentz oneNonzero).quadrance positive = 0
  rw [positiveZero, Form.quadrance_zero]

/-- The original inverse of the positive-root Lorentz rotation is the negative-root rotation.

Inversion negates the same computed anchor, whose cap recovery reconstructs the inverse in the original form. -/
theorem prescribedAxisRotation_pair_inverse [DecidableEq K] (axis : Vector3 K) (amount : K)
    (certificate : Witness.NonzeroSquare (prescribedAxisSquareValue oneNonzero axis amount))
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (amountNotOne : amount ≠ 1)
    (twoNonzero : (2 : K) ≠ 0) :
    SpecialOrthogonal.inverse
        ((prescribedAxisRotationOfSquare oneNonzero axis amount certificate
          axisNonNull amountNotOne twoNonzero).rotation) =
      (prescribedAxisRotationOfSquare oneNonzero axis amount certificate.neg
        axisNonNull amountNotOne twoNonzero).rotation := by
  let positive := prescribedAxisRotationOfSquare oneNonzero axis amount certificate axisNonNull amountNotOne twoNonzero
  let negative := prescribedAxisRotationOfSquare oneNonzero axis amount certificate.neg
    axisNonNull amountNotOne twoNonzero
  let inverted := SpecialOrthogonal.inverse positive.rotation
  have notHalfTurn : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) inverted ≠ 1 := by
    rw [Cayley.TernaryForm.rotationHalfSpread_inverse]
    exact positive.notHalfTurn
  let inverseDefined := (inverted.anchorDenominator_ne_zero_iff twoNonzero).mpr notHalfTurn
  have vectorEqual : rotationAnchorVector oneNonzero inverted inverseDefined =
      Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate.neg) axis := by
    calc
      _ = Vector3.neg (rotationAnchorVector oneNonzero positive.rotation positive.anchorDefined) :=
        rotationAnchorVector_inverse oneNonzero positive.rotation positive.anchorDefined
      _ = Vector3.neg (Vector3.scale (prescribedAnchorScale oneNonzero axis amount certificate) axis) :=
        congrArg Vector3.neg positive.anchor_eq
      _ = _ := (prescribedAnchorVector_neg oneNonzero axis amount certificate).symm
  calc
    inverted = capRotation oneNonzero (rotationAnchorVector oneNonzero inverted inverseDefined)
        (rotationAnchorVector_defined oneNonzero inverted twoNonzero notHalfTurn) :=
      (cap_rotationAnchorVector oneNonzero inverted twoNonzero notHalfTurn).symm
    _ = negative.rotation := capRotation_congr_vector oneNonzero vectorEqual
      (rotationAnchorVector_defined oneNonzero inverted twoNonzero notHalfTurn)
      (prescribedAnchor_capDefined oneNonzero axis amount certificate.neg axisNonNull amountNotOne)

/-- The half turn about the supplied original Lorentz axis has half spread one. -/
theorem prescribedAxis_halfTurn_halfSpread (axis : Vector3 K)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0) (twoNonzero : (2 : K) ≠ 0) :
    Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero)
      ((Form.lorentz oneNonzero).halfTurnRotation axis axisNonNull) = 1 :=
  Cayley.TernaryForm.rotationHalfSpread_halfTurn _ axis axisNonNull twoNonzero

/-- A half-spread-one Lorentz rotation fixing the supplied non-null axis is its unique original half turn.

The retained half-turn preimage projects the supplied fixed axis onto its own non-null axis. The resulting original
nonzero scale identifies their half-turn matrices. -/
theorem prescribedAxis_halfTurn_unique [DecidableEq K] (axis : Vector3 K)
    (axisNonNull : (Form.lorentz oneNonzero).quadrance axis ≠ 0)
    (rotation : (Form.lorentz oneNonzero).SpecialOrthogonal) (twoNonzero : (2 : K) ≠ 0)
    (halfSpreadOne : Cayley.TernaryForm.rotationHalfSpread (Form.lorentz oneNonzero) rotation = 1)
    (axisFixed : Matrix3.rowMul axis rotation.matrix = axis) :
    rotation = (Form.lorentz oneNonzero).halfTurnRotation axis axisNonNull := by
  let form := Form.lorentz oneNonzero
  let witness := Cayley.TernaryForm.halfTurnWitness form rotation twoNonzero halfSpreadOne
  have matricesEqual : form.halfTurn witness.1 witness.2.1 = rotation.matrix :=
    congrArg (fun value : form.SpecialOrthogonal => value.matrix) witness.2.2
  have fixed : Matrix3.rowMul axis (form.halfTurn witness.1 witness.2.1) = axis :=
    (congrArg (Matrix3.rowMul axis) matricesEqual).trans axisFixed
  have projected := (form.rowMul_halfTurn_eq_self_iff_projection witness.1 witness.2.1 twoNonzero axis).mp fixed
  let factor := form.bilinear axis witness.1 / form.quadrance witness.1
  have factorNonzero : factor ≠ 0 := by
    intro zero
    apply axisNonNull
    have axisEqual : axis = Vector3.scale factor witness.1 := projected
    rw [axisEqual, zero, Vector3.zero_scale, Form.quadrance_zero]
  have sameMatrix := (form.halfTurn_eq_iff_same_line witness.1 axis witness.2.1 axisNonNull twoNonzero).mpr
    ⟨factor, factorNonzero, projected⟩
  apply SpecialOrthogonal.eq_of_matrix_eq
  exact matricesEqual.symm.trans sameMatrix

end Purelib.Geometry.Rotations.Ternary.Lorentz
