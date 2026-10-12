module

import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Algebra.Field.Inverse

import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Geometry.Rotations.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Squares.Witness
public import Purelib.Geometry.Rotations.Axis.Prescribed
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.NumberTheory.SquareClass.Rational.Nonsquare
import Purelib.Geometry.Rotations.Cayley.Cap
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
@[expose] public section

/-!
# Rational rotations, Theorem 65 and Examples 66--67

The square condition for a prescribed axis and half spread is carried by an
explicit nonzero root.  From that root we compute the two opposite anchor
vectors and hence the two inverse rotations.  No square-root operation or
choice principle enters the construction.
-/

namespace Purelib.Examples.Geometry.Rotations.PrescribedAxes

open Purelib.Examples

open Purelib.Geometry.Rotations.Axis
open Purelib.Algebra.Field.Squares.Witness (NonzeroSquare)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rotations.Cayley

open Purelib.Rotations

variable {K : Type*} [ExplicitField K]
namespace ExampleSixtySix

/-- The rational coordinate axis (1,0,0). -/
def coordinateAxis : Vector3 Fraction.Rational
  := ⟨1, 0, 0⟩

/-- The coordinate axis has quadrance one. -/
theorem coordinateAxis_quadrance :
  coordinateAxis.quadrance = 1 := by
  unfold coordinateAxis Vector3.quadrance Vector3.dot
  ring1

/-- The rational parameter in Example 66. -/
def parameterHalfSpread (parameter :
  Fraction.Rational) : Fraction.Rational :=
  parameter ^ 2 / (1 + parameter ^ 2)

/-- The square root of `p(1-p)` supplied by the same parameter. -/
def parameterConditionRoot (parameter :
  Fraction.Rational) : Fraction.Rational :=
  parameter / (1 + parameter ^ 2)

section
/-- The parameter t/(1+t²) witnesses the prescribed-axis square condition for half-spread t²/(1+t²). -/
theorem parameter_condition (parameter :
  Fraction.Rational)
    (denominatorNonzero : 1 + parameter ^ 2 ≠ 0) :
    Prescribed.prescribedAxisSquareValue coordinateAxis
        (parameterHalfSpread parameter) =
      parameterConditionRoot parameter ^ 2 := by
  have cancel := ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2) denominatorNonzero
  unfold Prescribed.prescribedAxisSquareValue
    parameterHalfSpread
    parameterConditionRoot
  rw [coordinateAxis_quadrance]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 * (parameter ^ 2 * (1 + parameter ^ 2)⁻¹) *
          (1 - parameter ^ 2 * (1 + parameter ^ 2)⁻¹) =
        parameter ^ 2 * (1 + parameter ^ 2)⁻¹ *
          ((1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹ -
            parameter ^ 2 * (1 + parameter ^ 2)⁻¹) := by
      rw [cancel]
      ring1
    _ = (parameter * (1 + parameter ^ 2)⁻¹) ^ 2 := by ring1

/-- One minus twice the parametrized half-spread equals (1-t²)/(1+t²). -/
theorem parameter_one_sub_two_halfSpread
  (parameter : Fraction.Rational)
    (denominatorNonzero : 1 + parameter ^ 2 ≠ 0) :
    1 - 2 * parameterHalfSpread parameter =
      (1 - parameter ^ 2) / (1 + parameter ^ 2) := by
  have cancel := ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2) denominatorNonzero
  unfold parameterHalfSpread
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 - 2 * (parameter ^ 2 * (1 + parameter ^ 2)⁻¹) =
        (1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹ -
          2 * parameter ^ 2 * (1 + parameter ^ 2)⁻¹ := by
      rw [cancel]
      ring1
    _ = (1 - parameter ^ 2) * (1 + parameter ^ 2)⁻¹ := by ring1

end

/-- The displayed rational parameter gives a normalized Pythagorean triple. -/
theorem parameter_pythagorean (parameter :
  Fraction.Rational)
    (denominatorNonzero : 1 + parameter ^ 2 ≠ 0) :
    ((1 - parameter ^ 2) / (1 + parameter ^ 2)) ^ 2 +
        ((2 * parameter) / (1 + parameter ^ 2)) ^ 2 = 1 := by
  have cancel := ExplicitField.mul_inv_cancel
    (1 + parameter ^ 2) denominatorNonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    ((1 - parameter ^ 2) * (1 + parameter ^ 2)⁻¹) ^ 2 +
          ((2 * parameter) * (1 + parameter ^ 2)⁻¹) ^ 2 =
        ((1 + parameter ^ 2) * (1 + parameter ^ 2)⁻¹) ^ 2 := by
      ring1
    _ = 1 := by rw [cancel]; ring1

section
/-- The parameter recovered from a supplied nonzero square root. -/
def parameterOfCondition (spread :
  Fraction.Rational)
    (certificate :
      NonzeroSquare (Prescribed.prescribedAxisSquareValue
        coordinateAxis spread)) :
    Fraction.Rational := spread / certificate.root

/-- The retained coordinate-axis condition root squares to p(1-p). -/
private theorem
  condition_root_square
  (spread : Fraction.Rational)
    (certificate :
      NonzeroSquare (Prescribed.prescribedAxisSquareValue
        coordinateAxis spread)) :
    certificate.root ^ 2 = spread * (1 - spread) := by
  simpa only [Prescribed.prescribedAxisSquareValue,
    coordinateAxis_quadrance, one_mul]
    using certificate.square

/-- The recovered parameter squares to p/(1-p) when the half-spread differs from one. -/
private theorem
  parameterOfCondition_square
  (spread : Fraction.Rational)
    (certificate :
      NonzeroSquare (Prescribed.prescribedAxisSquareValue
        coordinateAxis spread))
    (spreadNotOne : spread ≠ 1) :
    parameterOfCondition spread certificate ^ 2 =
      spread / (1 - spread) := by
  have complementNonzero := Purelib.Algebra.Field.ExplicitField.one_sub_ne_zero_of_ne_one spreadNotOne
  have rootCancel := ExplicitField.mul_inv_cancel certificate.root
    certificate.rootNonzero
  apply Purelib.Algebra.Field.Inverse.eq_div_of_mul_eq complementNonzero
  unfold parameterOfCondition
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    (spread * certificate.root⁻¹) ^ 2 * (1 - spread) =
        spread * (spread * (1 - spread)) * certificate.root⁻¹ ^ 2 := by
      ring1
    _ = spread * certificate.root ^ 2 * certificate.root⁻¹ ^ 2 := by
      rw [condition_root_square spread certificate]
    _ = spread * (certificate.root * certificate.root⁻¹) ^ 2 := by
      ring1
    _ = spread := by rw [rootCancel]; ring1

/-- The recovered parameter has nonzero denominator 1+t² when the half-spread differs from one. -/
private theorem
  parameterOfCondition_denominator_nonzero
  (spread : Fraction.Rational)
    (certificate :
      NonzeroSquare (Prescribed.prescribedAxisSquareValue
        coordinateAxis spread))
    (spreadNotOne : spread ≠ 1) :
    1 + parameterOfCondition spread certificate ^ 2 ≠ 0 := by
  have complementNonzero := Purelib.Algebra.Field.ExplicitField.one_sub_ne_zero_of_ne_one spreadNotOne
  have complementCancel := ExplicitField.mul_inv_cancel
    (1 - spread) complementNonzero
  intro denominatorZero
  have product :
      (1 + parameterOfCondition spread certificate ^ 2) *
          (1 - spread) = 1 := by
    rw [parameterOfCondition_square spread
      certificate
      spreadNotOne]
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (1 + spread * (1 - spread)⁻¹) * (1 - spread) =
          (1 - spread) + spread *
            ((1 - spread)⁻¹ * (1 - spread)) := by ring1
      _ = 1 := by
        rw [show (1 - spread)⁻¹ * (1 - spread) = 1 by
          calc
            (1 - spread)⁻¹ * (1 - spread) =
                (1 - spread) * (1 - spread)⁻¹ := by ring1
            _ = 1 := complementCancel]
        ring1
  rw [denominatorZero, zero_mul] at product
  exact (Purelib.Algebra.Field.Characteristic.Nonzero.one_ne_zero_of_nonzero certificate.rootNonzero) product.symm

/-- A nonzero half-spread gives a nonzero recovered parameter from the retained nonzero square root. -/
theorem parameterOfCondition_nonzero (spread :
  Fraction.Rational)
    (certificate :
      NonzeroSquare (Prescribed.prescribedAxisSquareValue
        coordinateAxis spread))
    (spreadNonzero : spread ≠ 0) :
    parameterOfCondition spread certificate ≠ 0 :=
  ExplicitField.div_ne_zero spreadNonzero certificate.rootNonzero

/-- The parameter recovered from the retained square-condition witness reproduces the original half-spread when it
differs from one. -/
theorem parameterOfCondition_recovers (spread
  : Fraction.Rational)
    (certificate :
      NonzeroSquare (Prescribed.prescribedAxisSquareValue
        coordinateAxis spread))
    (spreadNotOne : spread ≠ 1) :
    parameterHalfSpread
      (parameterOfCondition spread certificate) = spread := by
  let parameter := parameterOfCondition spread certificate
  have parameterSquare := parameterOfCondition_square
    spread certificate
    spreadNotOne
  have denominatorNonzero :=
    parameterOfCondition_denominator_nonzero spread
    certificate spreadNotOne
  have complementNonzero := Purelib.Algebra.Field.ExplicitField.one_sub_ne_zero_of_ne_one spreadNotOne
  have complementCancel := ExplicitField.mul_inv_cancel
    (1 - spread) complementNonzero
  have denominatorProduct :
      (1 + parameter ^ 2) * (1 - spread) = 1 := by
    rw [parameterSquare]
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (1 + spread * (1 - spread)⁻¹) * (1 - spread) =
          (1 - spread) + spread *
            ((1 - spread)⁻¹ * (1 - spread)) := by ring1
      _ = 1 := by
        rw [show (1 - spread)⁻¹ * (1 - spread) = 1 by
          calc
            (1 - spread)⁻¹ * (1 - spread) =
                (1 - spread) * (1 - spread)⁻¹ := by ring1
            _ = 1 := complementCancel]
        ring1
  have denominatorInverse := Purelib.Algebra.Field.Inverse.inverse_eq_of_mul_eq_one
    denominatorNonzero
    denominatorProduct
  unfold parameterHalfSpread
  simp only [ExplicitField.div_eq_mul_inv]
  rw [denominatorInverse, parameterSquare]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    spread * (1 - spread)⁻¹ * (1 - spread) =
        spread * ((1 - spread) * (1 - spread)⁻¹) := by ring1
    _ = spread := by rw [complementCancel, mul_one]

/-- Example 66's exact parametrization of all non-endpoint coordinate-axis
half spreads satisfying the square condition. -/
theorem coordinateAxis_condition_iff_parameter
  (spread : Fraction.Rational)
    (spreadNonzero : spread ≠ 0) (spreadNotOne : spread ≠ 1) :
    Nonempty
        (NonzeroSquare (Prescribed.prescribedAxisSquareValue
          coordinateAxis spread)) ↔
      ∃ parameter : Fraction.Rational, parameter ≠ 0 ∧
        1 + parameter ^ 2 ≠ 0 ∧
        spread = parameterHalfSpread parameter := by
  constructor
  · rintro ⟨certificate⟩
    refine ⟨parameterOfCondition spread certificate,
      parameterOfCondition_nonzero spread certificate spreadNonzero,
      parameterOfCondition_denominator_nonzero spread
        certificate spreadNotOne,
      ?_⟩
    exact (parameterOfCondition_recovers spread certificate
      spreadNotOne).symm
  · rintro ⟨parameter, parameterNonzero, denominatorNonzero, spreadFormula⟩
    refine ⟨{
      root := parameterConditionRoot parameter
      rootNonzero := ExplicitField.div_ne_zero parameterNonzero
        denominatorNonzero
      square := ?_ }⟩
    rw [spreadFormula, parameter_condition parameter
      denominatorNonzero]

/-- Parameter one gives half-spread one half. -/
theorem quarterTurn_parameter :
  parameterHalfSpread 1 = (1 : Fraction.Rational) / 2 := by
  decide

/-- Parameter one half gives half-spread one fifth. -/
theorem threeFourFive_parameter :
    parameterHalfSpread ((1 : Fraction.Rational) / 2) = (1 :
      Fraction.Rational) / 5 := by
  decide

end

end ExampleSixtySix

namespace ExampleSixtySeven

/-- The rational diagonal axis (1,1,1). -/
def diagonalAxis : Vector3 Fraction.Rational
  := ⟨1, 1, 1⟩

section
/-- The diagonal axis has quadrance three. -/
theorem diagonalAxis_quadrance :
  diagonalAxis.quadrance = 3 := by
  unfold diagonalAxis Vector3.quadrance Vector3.dot
  ring1

/-- The rational diagonal axis has nonzero quadrance. -/
theorem diagonalAxis_nonNull :
  diagonalAxis.quadrance ≠ 0 := by
  rw [diagonalAxis_quadrance]
  decide

end

section
/-- The diagonal square condition at half-spread one half equals three quarters. -/
theorem quarter_condition_value :
    Prescribed.prescribedAxisSquareValue diagonalAxis
      ((1 : Fraction.Rational) / 2) = 3 / 4 := by
  unfold Prescribed.prescribedAxisSquareValue
  rw [diagonalAxis_quadrance]
  decide

/-- The square condition for a diagonal quarter turn would make three a
rational square. -/
theorem quarter_condition_not_square :
    ¬ Nonempty
      (NonzeroSquare
        (Prescribed.prescribedAxisSquareValue
          diagonalAxis ((1 : Fraction.Rational) / 2))) := open
          Purelib.NumberTheory in by
  rintro ⟨certificate⟩
  have rootSquare : certificate.root ^ 2 = (3 : Fraction.Rational) / 4 := by
    rw [← quarter_condition_value]
    exact certificate.square
  apply SquareClass.Rational.Nonsquare.square_ne_three (2 * certificate.root)
  calc
    (2 * certificate.root) ^ 2 = 4 * certificate.root ^ 2 := by ring1
    _ = 4 * ((3 : Fraction.Rational) / 4) := by rw [rootSquare]
    _ = 3 := by decide

/-- Example 67: no rational rotation has the diagonal axis and half spread
one half. -/
theorem no_rational_quarter_turn :
    ¬ Nonempty
      (Prescribed.PrescribedAxisRotation diagonalAxis
        ((1 : Fraction.Rational) / 2)) := by
  intro candidate
  have condition :=
    (Prescribed.prescribedAxisRotation_exists_iff
      diagonalAxis ((1 : Fraction.Rational) / 2)
      diagonalAxis_nonNull (by decide) (by decide)
        (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (value := 2) (by decide) : (2 :
          Rational) ≠ 0)).1 candidate
  exact quarter_condition_not_square condition

/-- The diagonal square condition at half-spread three quarters equals nine sixteenths. -/
theorem threeQuarter_condition_value :
    Prescribed.prescribedAxisSquareValue diagonalAxis
      ((3 : Fraction.Rational) / 4) = 9 / 16 := by
  unfold Prescribed.prescribedAxisSquareValue
  rw [diagonalAxis_quadrance]
  decide

/-- The displayed root `3/4` certifies the attainable diagonal rotation of
half spread `3/4`. -/
def threeQuarterCertificate :
    NonzeroSquare
      (Prescribed.prescribedAxisSquareValue
        diagonalAxis ((3 : Fraction.Rational) / 4)) where
  root := 3 / 4
  rootNonzero := by decide
  square := by
    rw [threeQuarter_condition_value]
    decide

/-- The retained square root three quarters produces anchor scale one. -/
theorem threeQuarter_anchorScale :
    Prescribed.prescribedAnchorScale diagonalAxis ((3
      : Fraction.Rational) / 4)
      threeQuarterCertificate = 1 := by
  change ((3 : Fraction.Rational) / 4) /
      (diagonalAxis.quadrance * (1 - (3 : Fraction.Rational) / 4)) =
        1
  rw [diagonalAxis_quadrance]
  decide

/-- The diagonal Cayley cap has nonzero denominator four. -/
theorem diagonalCapDefined :
  Cap.capDenominator diagonalAxis ≠ 0 := by
  unfold Cap.capDenominator
  rw [diagonalAxis_quadrance]
  decide

/-- The attainable example is the cap of `A_(1,1,1)` itself. -/
def diagonalRotation :
  Rotations.Basic.Rotation Fraction.Rational :=
  Cap.capRotation diagonalAxis
    diagonalCapDefined

/-- The diagonal Cayley rotation has half-spread three quarters. -/
theorem diagonalRotation_halfSpread :
    Rotations.Spread.halfSpread diagonalRotation = (3 :
      Fraction.Rational) / 4 := by
  unfold diagonalRotation
  rw [Rotations.Spread.halfSpread_cap diagonalAxis
    diagonalCapDefined
    (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (value := 2) (by decide) : (2 :
      Rational) ≠ 0)]
  unfold Cap.capDenominator
  rw [diagonalAxis_quadrance]
  decide

/-- The prescribed-axis constructor with the retained three-quarter root has the same matrix as the diagonal Cayley
rotation. -/
theorem
  constructed_threeQuarter_eq_diagonalRotation
  :
  (Prescribed.prescribedAxisRotationOfSquare
    diagonalAxis ((3 : Fraction.Rational) / 4)
      threeQuarterCertificate
        diagonalAxis_nonNull (by decide)
      (by decide)).rotation.matrix = diagonalRotation.matrix := by
  let constructedVector := Vector3.scale
    (Prescribed.prescribedAnchorScale diagonalAxis
      ((3 : Fraction.Rational) / 4)
      threeQuarterCertificate)
        diagonalAxis
  let constructedDefined := Prescribed.prescribedAnchor_capDefined
    diagonalAxis
    ((3 : Fraction.Rational) / 4) threeQuarterCertificate
      diagonalAxis_nonNull
    (by decide)
  have vectorEqual : constructedVector = diagonalAxis := by
    unfold constructedVector
    rw [threeQuarter_anchorScale, Vector3.one_scale]
  change Cap.cap constructedVector constructedDefined =
    Cap.cap diagonalAxis
      diagonalCapDefined
  exact Cap.cap_congr_vector vectorEqual constructedDefined
    diagonalCapDefined

/-- The half twist of the displayed anchor is three. -/
theorem diagonalRotation_halfTwist :
  diagonalAxis.quadrance = 3 :=
  diagonalAxis_quadrance

end

end ExampleSixtySeven

end Purelib.Examples.Geometry.Rotations.PrescribedAxes

end
