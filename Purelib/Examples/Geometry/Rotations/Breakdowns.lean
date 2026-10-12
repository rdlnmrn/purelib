module

import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Geometry.Rotations.Reflection
public import Purelib.Examples.Geometry.Rotations.Caps
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Geometry.Rotations.Cayley.Charts
public import Purelib.Geometry.Rotations.Cayley.Product
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
@[expose] public section

/-!
# Rational rotations, section 10: three affine-chart breakdowns

This file makes the missing half-turn locus explicit without taking a limit.
The reciprocal-anchor path is stored by the denominator-cleared quadratic
formula, so its value at zero is an ordinary finite field calculation.
-/

namespace Purelib.Examples.Geometry.Rotations.Breakdowns

open Purelib.Examples

open Purelib.Data.Rat.Fraction.Order.Cast (rational_natCast_nonzero)

open Purelib.Geometry.Rotations.Cayley
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Examples.Geometry.Rotations

variable {K : Type*} [ExplicitField K]
namespace ExampleFiftyThree

/-- The rational anchor vector `(-2, 2, 1)`. -/
def fourth : Vector3 Fraction.Rational := ⟨-2,
  2, 1⟩

/-- The half-turn axis vector `(15, 21, -2)`. -/
def axis : Vector3 Fraction.Rational := ⟨15, 21,
  -2⟩

/-- The displayed rational three-by-three matrix of the half-turn product. -/
def displayed : Coordinates3.Matrix3
  Fraction.Rational :=
  ⟨(-22 : Fraction.Rational) / 67, 63 / 67, -6 / 67,
    63 / 67, 106 / 335, -42 / 335,
    -6 / 67, -42 / 335, -331 / 335⟩

/-- The fourth anchor has quadrance nine. -/
theorem fourth_quadrance :
  fourth.quadrance = 9 := by
  unfold fourth Vector3.quadrance Vector3.dot
  ring1

/-- The fourth anchor has nonzero Cayley denominator ten. -/
theorem fourthDefined :
  Cap.capDenominator fourth ≠ 0 := by
  rw [show Cap.capDenominator fourth = (10 :
    Fraction.Rational) by
    unfold Cap.capDenominator
    rw [fourth_quadrance]
    ring1]
  exact (fun {value : Nat} (nonzero : value ≠ 0) => (rational_natCast_nonzero
    (value := value) nonzero : (value : Rational) ≠ 0)) (by decide)

/-- The matrix product of the original first and fourth Cayley caps. -/
def product : Coordinates3.Matrix3
  Fraction.Rational :=
  Coordinates3.Matrix3.mul
    (Cap.cap Caps.ExampleTwentyFive.vector
      Caps.ExampleTwentyFive.defined)
    (Cap.cap fourth
      fourthDefined)

/-- The two cap anchors have dot product one. -/
theorem dot_one : Vector3.dot
  Caps.ExampleTwentyFive.vector fourth = 1 := by
  unfold Caps.ExampleTwentyFive.vector fourth
    Vector3.dot
  ring1

/-- The cap anchors have cross product `(-13, -18, 10)`. -/
theorem cross_value :
    Vector3.cross Caps.ExampleTwentyFive.vector
      fourth = ⟨-13, -18, 10⟩ := by
  apply Vector3.ext <;> decide

/-- The anchor-product numerator is the retained half-turn axis. -/
theorem numerator_value :
    Product.anchorProductNumerator Caps.ExampleTwentyFive.vector
      fourth = axis :=
      by
  apply Vector3.ext <;> decide

/-- The affine anchor-product denominator vanishes. -/
theorem product_denominator_zero :
    Product.anchorProductDenominator Caps.ExampleTwentyFive.vector
      fourth = 0 := by
  unfold Product.anchorProductDenominator
  rw [dot_one]
  ring1

/-- The retained half-turn axis has quadrance 670. -/
theorem axis_quadrance :
  axis.quadrance = 670 := by
  unfold axis Vector3.quadrance Vector3.dot
  ring1

/-- The retained half-turn axis is non-null. -/
theorem axisNonNull :
  axis.quadrance ≠ 0 := by
  rw [axis_quadrance]
  exact (fun {value : Nat} (nonzero : value ≠ 0) => (rational_natCast_nonzero
    (value := value) nonzero : (value : Rational) ≠ 0)) (by decide)

/-- The displayed rational two is nonzero. -/
theorem twoNonzero : (2 : Fraction.Rational) ≠ 0
  := (fun {value : Nat} (nonzero : value ≠ 0) => (rational_natCast_nonzero (value
    := value) nonzero : (value : Rational) ≠ 0)) (by decide)

/-- The first cap rotation has half spread `66/67`. -/
theorem first_halfSpread :
    Rotations.Spread.halfSpread
        (Cap.capRotation Caps.ExampleTwentyFive.vector
          Caps.ExampleTwentyFive.defined) =
      (66 : Fraction.Rational) / 67 := by
  rw [Rotations.Spread.halfSpread_cap Caps.ExampleTwentyFive.vector
    Caps.ExampleTwentyFive.defined
      twoNonzero, Caps.ExampleTwentyFive.quadrance]
  unfold Cap.capDenominator
  rw [Caps.ExampleTwentyFive.quadrance]
  rw [show (1 + 66 : Fraction.Rational) = 67 by ring1]

/-- The fourth cap rotation has half spread `9/10`. -/
theorem fourth_halfSpread :
    Rotations.Spread.halfSpread (Cap.capRotation fourth
      fourthDefined) = (9 : Fraction.Rational) / 10 := by
  rw [Rotations.Spread.halfSpread_cap fourth
    fourthDefined
    twoNonzero,
    fourth_quadrance]
  unfold Cap.capDenominator
  rw [fourth_quadrance]
  rw [show (1 + 9 : Fraction.Rational) = 10 by ring1]

/-- The cap product equals the half turn about the retained non-null axis. -/
theorem product_halfTurn :
  product = Rotations.Reflection.halfTurn
  axis axisNonNull := by
  unfold product
  simpa only [numerator_value] using
    Product.cap_mul_cap_eq_halfTurn_of_dot_eq_one
      Caps.ExampleTwentyFive.vector fourth
        Caps.ExampleTwentyFive.defined fourthDefined
      dot_one

/-- The retained axis half turn equals the displayed rational matrix.

Explicit nonzero denominators and field cancellations identify every matrix entry. -/
theorem halfTurn_displayed :
  Rotations.Reflection.halfTurn axis
  axisNonNull =
  displayed := by
  have sixtySevenNonzero : (67 : Fraction.Rational) ≠ 0 :=
    (fun {value : Nat} (nonzero : value ≠ 0) => (rational_natCast_nonzero (value :=
      value) nonzero : (value : Rational) ≠ 0)) (by decide)
  have threeThirtyFiveNonzero : (335 : Fraction.Rational) ≠ 0 :=
    (fun {value : Nat} (nonzero : value ≠ 0) => (rational_natCast_nonzero (value :=
      value) nonzero : (value : Rational) ≠ 0)) (by decide)
  have sixSeventyNonzero : (670 : Fraction.Rational) ≠ 0 :=
    (fun {value : Nat} (nonzero : value ≠ 0) => (rational_natCast_nonzero (value :=
      value) nonzero : (value : Rational) ≠ 0)) (by decide)
  have cancel67 := ExplicitField.mul_inv_cancel
    (67 : Fraction.Rational) sixtySevenNonzero
  have cancel335 := ExplicitField.mul_inv_cancel
    (335 : Fraction.Rational) threeThirtyFiveNonzero
  have cancel670 := ExplicitField.mul_inv_cancel
    (670 : Fraction.Rational) sixSeventyNonzero
  have inverse67Candidate :
      (67 : Fraction.Rational) * (5 * (335 : Fraction.Rational)⁻¹) = 1 := by
    calc
      (67 : Fraction.Rational) * (5 * 335⁻¹) = (67 * 5) * 335⁻¹ := by ring1
      _ = 335 * 335⁻¹ := by
        rw [show (67 : Fraction.Rational) * 5 = 335 by ring1]
      _ = 1 := cancel335
  have inverse67 : (67 : Fraction.Rational)⁻¹ = 5 * (335 : Fraction.Rational)⁻¹ := by
    calc
      (67 : Fraction.Rational)⁻¹ = 67⁻¹ * 1 := by rw [mul_one]
      _ = 67⁻¹ * (67 * (5 * 335⁻¹)) := by
        rw [inverse67Candidate]
      _ = (67 * 67⁻¹) * (5 * 335⁻¹) := by ring1
      _ = 5 * 335⁻¹ := by rw [cancel67, one_mul]
  have coefficient : (2 : Fraction.Rational) / 670 = 1 / 335 := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      (2 : Fraction.Rational) * 670⁻¹ =
          2 * 670⁻¹ * (335 * 335⁻¹) := by
        rw [cancel335, mul_one]
      _ = (2 * 335) * (670⁻¹ * 335⁻¹) := by ring1
      _ = 670 * (670⁻¹ * 335⁻¹) := by
        rw [show (2 : Fraction.Rational) * 335 = 670 by ring1]
      _ = (670 * 670⁻¹) * 335⁻¹ := by ring1
      _ = 1 * 335⁻¹ := by rw [cancel670]
  have reverse335 : (335 : Fraction.Rational)⁻¹ * 335 = 1 := by
    calc
      (335 : Fraction.Rational)⁻¹ * 335 = 335 * 335⁻¹ := by ring1
      _ = 1 := cancel335
  calc
    Rotations.Reflection.halfTurn axis
      axisNonNull =
        Coordinates3.Matrix3.add (Coordinates3.Matrix3.neg Coordinates3.Matrix3.identity)
          (Coordinates3.Matrix3.scale (2 / axis.quadrance)
            (Coordinates3.Matrix3.outer axis
              axis)) := by
      apply Coordinates3.Matrix3.ext <;> unfold Rotations.Reflection.halfTurn Rotations.Reflection.reflection
        Coordinates3.Matrix3.neg Coordinates3.Matrix3.sub
        Coordinates3.Matrix3.add Coordinates3.Matrix3.identity Coordinates3.Matrix3.scale <;> ring1
    _ = Coordinates3.Matrix3.add (Coordinates3.Matrix3.neg Coordinates3.Matrix3.identity)
          (Coordinates3.Matrix3.scale (1 / 335) (Coordinates3.Matrix3.outer
            axis axis))
            := by
      rw [axis_quadrance, coefficient]
    _ = Coordinates3.Matrix3.scale (1 / 335)
          (Coordinates3.Matrix3.sub (Coordinates3.Matrix3.outer axis
            axis)
            (Coordinates3.Matrix3.scale 335 Coordinates3.Matrix3.identity)) := by
      symm
      calc
        Coordinates3.Matrix3.scale (1 / 335)
            (Coordinates3.Matrix3.sub (Coordinates3.Matrix3.outer axis
              axis)
              (Coordinates3.Matrix3.scale 335 Coordinates3.Matrix3.identity)) =
          Coordinates3.Matrix3.sub
            (Coordinates3.Matrix3.scale (1 / 335) (Coordinates3.Matrix3.outer
              axis
              axis))
            (Coordinates3.Matrix3.scale ((1 / 335) * 335) Coordinates3.Matrix3.identity) := by
          apply Coordinates3.Matrix3.ext <;> unfold Coordinates3.Matrix3.scale Coordinates3.Matrix3.sub <;> ring1
        _ = Coordinates3.Matrix3.sub
            (Coordinates3.Matrix3.scale (1 / 335) (Coordinates3.Matrix3.outer
              axis
              axis))
            (Coordinates3.Matrix3.scale 1 Coordinates3.Matrix3.identity) := by
          simp only [ExplicitField.div_eq_mul_inv, one_mul, reverse335, -eq_self, -iff_self]
          rfl
        _ = Coordinates3.Matrix3.add (Coordinates3.Matrix3.neg Coordinates3.Matrix3.identity)
            (Coordinates3.Matrix3.scale (1 / 335) (Coordinates3.Matrix3.outer
              axis
              axis)) := by
          rw [Coordinates3.Matrix3.one_scale]
          apply Coordinates3.Matrix3.ext <;> unfold Coordinates3.Matrix3.sub Coordinates3.Matrix3.add
            Coordinates3.Matrix3.neg <;>
            ring1
    _ = Geometry.Rotations.Breakdowns.ExampleFiftyThree.displayed := by
      apply Coordinates3.Matrix3.ext <;> unfold displayed
        axis Coordinates3.Matrix3.sub Coordinates3.Matrix3.identity
        Coordinates3.Matrix3.scale Coordinates3.Matrix3.outer <;>
        simp only [ExplicitField.div_eq_mul_inv, inverse67] <;> ring1

/-- The original cap product equals the displayed rational matrix. -/
theorem product_displayed :
  product = displayed :=
  by
  rw [product_halfTurn,
    halfTurn_displayed]

/-- The product's characteristic value is `(X - 1) * (X + 1)^2`. -/
theorem characteristic_polynomial (X :
  Fraction.Rational) :
    Coordinates3.Matrix3.characteristicValue product X = (X - 1) * (X +
      1) ^ 2 := by
  rw [product_halfTurn]
  calc
    Coordinates3.Matrix3.characteristicValue (Rotations.Reflection.halfTurn
      axis axisNonNull)
      X =
        (X - 1) *
          (X ^ 2 -
            2 * (1 - 2 * Rotations.Spread.halfSpread (Rotations.Reflection.halfTurnRotation
              axis
              axisNonNull)) * X +
              1) :=
      Rotations.Spread.characteristicValue_rotation (Rotations.Reflection.halfTurnRotation
        axis
        axisNonNull)
        twoNonzero X
    _ = (X - 1) * (X + 1) ^ 2 := by
      rw [Rotations.Spread.halfSpread_halfTurn axis
        axisNonNull
        twoNonzero]
      ring1

/-- The reciprocal-anchor path has denominator `x^2 + 670`. -/
theorem path_denominator (x : Fraction.Rational)
  :
    Charts.reciprocalAnchorPathDenominator x axis = x ^
      2 + 670 := by
  unfold Charts.reciprocalAnchorPathDenominator
  rw [axis_quadrance]

/-- At a nonzero defined parameter, the reciprocal-anchor path equals the Cayley cap of the inverse-scaled axis. -/
theorem path_at_nonzero (x : Fraction.Rational)
  (xNonzero : x ≠ 0)
    (pathDefined : Charts.reciprocalAnchorPathDenominator x
      axis ≠ 0) :
    Charts.reciprocalAnchorPath x axis pathDefined =
      Cap.cap (Vector3.scale x⁻¹ axis)
        (Charts.reciprocalAnchorCapDefined x axis
          xNonzero pathDefined) :=
  Charts.reciprocalAnchorPath_eq_cap x axis xNonzero
    pathDefined

/-- At parameter zero, the reciprocal-anchor path equals the original half-turn cap product. -/
theorem path_at_zero :
    Charts.reciprocalAnchorPath 0 axis
        (Charts.reciprocalAnchorPath_zeroDefined axis
          axisNonNull) =
          product := by
  rw [Charts.reciprocalAnchorPath_zero axis
    axisNonNull,
    product_halfTurn]

end ExampleFiftyThree

end Purelib.Examples.Geometry.Rotations.Breakdowns

end
