module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Rotations.Reflection
public import Purelib.Geometry.Rotations.Cayley.Cap
import Purelib.LinearAlgebra.Coordinates3.Antisymmetric
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry.Rotations

open Purelib.Geometry.Rotations.Cayley

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3

section
@[expose] public section

/-!
# Rational rotations, section 10: three affine-chart breakdowns

This file makes the missing half-turn locus explicit without taking a limit.
The reciprocal-anchor path is stored by the denominator-cleared quadratic
formula, so its value at zero is an ordinary finite field calculation.
-/

namespace Purelib.Geometry.Rotations.Cayley.Charts

variable {K : Type*} [ExplicitField K]

/-- The first breakdown: no defined affine cap can equal a half turn. -/
theorem cap_ne_halfTurn (vector axis : Coordinates3.Vector K)
    (defined : Cap.capDenominator vector ≠ 0)
    (axisNonNull : axis.quadrance ≠ 0)
    (twoNonzero : (2 : K) ≠ 0) :
    Cap.cap vector defined ≠ Reflection.halfTurn axis axisNonNull := by
  intro equalMatrices
  apply Spread.halfSpread_cap_ne_one vector defined twoNonzero
  calc
    Spread.halfSpread (Cap.capRotation vector defined) =
        Spread.halfSpread (Reflection.halfTurnRotation axis axisNonNull) := by
      unfold Spread.halfSpread Cap.capRotation Reflection.halfTurnRotation
      exact congrArg
        (fun matrix => (3 - Matrix3.trace matrix) / 4) equalMatrices
    _ = 1 := Spread.halfSpread_halfTurn axis axisNonNull twoNonzero

/-- The finite denominator of the reciprocal-anchor path in Example 53. -/
def reciprocalAnchorPathDenominator (x : K) (axis : Coordinates3.Vector
  K) : K :=
  x ^ 2 + axis.quadrance

/-- The denominator-cleared path `I + 2 (x A + A²) / (x² + Q(axis))` from Example 53. -/
def reciprocalAnchorPath (x : K) (axis : Coordinates3.Vector K)
    (_defined : reciprocalAnchorPathDenominator x axis ≠ 0) : Coordinates3.Matrix3 K :=
  Matrix3.add Matrix3.identity
    (Matrix3.scale (2 / reciprocalAnchorPathDenominator x axis)
      (Matrix3.add
        (Matrix3.scale x (Antisymmetric.anchor axis))
        (Matrix3.mul (Antisymmetric.anchor axis) (Antisymmetric.anchor axis))))

/-- The reciprocal-anchor path denominator at zero is nonzero for a non-null axis. -/
theorem reciprocalAnchorPath_zeroDefined (axis : Coordinates3.Vector K)
    (axisNonNull : axis.quadrance ≠ 0) :
    reciprocalAnchorPathDenominator 0 axis ≠ 0 := by
  unfold reciprocalAnchorPathDenominator
  rw [show (0 : K) ^ 2 = 0 by ring1, zero_add]
  exact axisNonNull

/-- On the nonzero chart, the cap denominator is the path denominator times the square of the reciprocal chart
coordinate. -/
theorem capDenominator_inverseScale (x : K) (axis : Coordinates3.Vector
  K)
    (xNonzero : x ≠ 0) :
    Cap.capDenominator (Coordinates3.Vector.scale x⁻¹ axis) =
      x⁻¹ ^ 2 * reciprocalAnchorPathDenominator x axis := by
  have cancel := ExplicitField.mul_inv_cancel x xNonzero
  have reverseCancel : x⁻¹ * x = 1 := by
    calc
      x⁻¹ * x = x * x⁻¹ := by ring1
      _ = 1 := cancel
  have squareCancel : x⁻¹ ^ 2 * x ^ 2 = 1 := by
    calc
      x⁻¹ ^ 2 * x ^ 2 = (x⁻¹ * x) ^ 2 := by ring1
      _ = 1 := by rw [reverseCancel]; ring1
  unfold Cap.capDenominator reciprocalAnchorPathDenominator
  rw [Coordinates3.Vector.quadrance_scale]
  calc
    1 + x⁻¹ ^ 2 * axis.quadrance =
        x⁻¹ ^ 2 * x ^ 2 + x⁻¹ ^ 2 * axis.quadrance := by
      rw [squareCancel]
    _ = x⁻¹ ^ 2 * (x ^ 2 + axis.quadrance) := by ring1

/-- The normalized anchor has a defined cap on a nonzero path chart.

Both the chart coordinate and the path denominator must be nonzero. -/
theorem reciprocalAnchorCapDefined (x : K) (axis : Coordinates3.Vector
  K)
    (xNonzero : x ≠ 0)
    (pathDefined : reciprocalAnchorPathDenominator x axis ≠ 0) :
    Cap.capDenominator (Coordinates3.Vector.scale x⁻¹ axis) ≠ 0 := by
  rw [capDenominator_inverseScale x axis xNonzero]
  exact ExplicitField.mul_ne_zero
    (by
      simpa only [pow_two] using ExplicitField.mul_ne_zero
        (ExplicitField.inv_ne_zero xNonzero)
        (ExplicitField.inv_ne_zero xNonzero))
    pathDefined

/-- For `x ≠ 0`, the denominator-cleared path is exactly the cap of the reciprocal anchor `x⁻¹ axis`. -/
theorem reciprocalAnchorPath_eq_cap (x : K) (axis : Coordinates3.Vector
  K)
    (xNonzero : x ≠ 0)
    (pathDefined : reciprocalAnchorPathDenominator x axis ≠ 0) :
    reciprocalAnchorPath x axis pathDefined =
      Cap.cap (Coordinates3.Vector.scale x⁻¹ axis)
        (reciprocalAnchorCapDefined x axis xNonzero pathDefined) := by
  let capD := Cap.capDenominator (Coordinates3.Vector.scale x⁻¹ axis)
  let pathD := reciprocalAnchorPathDenominator x axis
  have capDValue : capD = x⁻¹ ^ 2 * pathD := by
    exact capDenominator_inverseScale x axis xNonzero
  have capDNonzero : capD ≠ 0 :=
    reciprocalAnchorCapDefined x axis xNonzero pathDefined
  have capDCancel := ExplicitField.mul_inv_cancel capD capDNonzero
  have pathDCancel := ExplicitField.mul_inv_cancel pathD pathDefined
  have inverseQuadratic : capD⁻¹ * x⁻¹ ^ 2 = pathD⁻¹ := by
    calc
      capD⁻¹ * x⁻¹ ^ 2 =
          capD⁻¹ * x⁻¹ ^ 2 * (pathD * pathD⁻¹) := by
        rw [pathDCancel, mul_one]
      _ = capD⁻¹ * (x⁻¹ ^ 2 * pathD) * pathD⁻¹ := by ring1
      _ = capD⁻¹ * capD * pathD⁻¹ := by rw [← capDValue]
      _ = pathD⁻¹ := by rw [show capD⁻¹ * capD = capD * capD⁻¹ by ring1,
          capDCancel, one_mul]
  have xCancel := ExplicitField.mul_inv_cancel x xNonzero
  have reverseCancel : x⁻¹ * x = 1 := by
    calc
      x⁻¹ * x = x * x⁻¹ := by ring1
      _ = 1 := xCancel
  have inverseLinear : capD⁻¹ * x⁻¹ = pathD⁻¹ * x := by
    calc
      capD⁻¹ * x⁻¹ = capD⁻¹ * (x⁻¹ ^ 2 * x) := by
        rw [show x⁻¹ ^ 2 * x = x⁻¹ by
          calc
            x⁻¹ ^ 2 * x = x⁻¹ * (x⁻¹ * x) := by ring1
            _ = x⁻¹ := by rw [reverseCancel, mul_one]]
      _ = (capD⁻¹ * x⁻¹ ^ 2) * x := by ring1
      _ = pathD⁻¹ * x := by rw [inverseQuadratic]
  have linearCoefficient : (2 / capD) * x⁻¹ = (2 / pathD) * x := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      2 * capD⁻¹ * x⁻¹ = 2 * (capD⁻¹ * x⁻¹) := by ring1
      _ = 2 * (pathD⁻¹ * x) := by rw [inverseLinear]
      _ = 2 * pathD⁻¹ * x := by ring1
  have quadraticCoefficient :
      (2 / capD) * (x⁻¹ * x⁻¹) = 2 / pathD := by
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      2 * capD⁻¹ * (x⁻¹ * x⁻¹) =
          2 * (capD⁻¹ * x⁻¹ ^ 2) := by ring1
      _ = 2 * pathD⁻¹ := by rw [inverseQuadratic]
  symm
  calc
    Cap.cap (Coordinates3.Vector.scale x⁻¹ axis)
        (reciprocalAnchorCapDefined x axis xNonzero pathDefined) =
      Matrix3.add Matrix3.identity
        (Matrix3.scale (2 / capD)
          (Matrix3.add
            (Matrix3.scale x⁻¹ (Antisymmetric.anchor axis))
            (Matrix3.scale (x⁻¹ * x⁻¹)
              (Matrix3.mul (Antisymmetric.anchor axis) (Antisymmetric.anchor axis))))) := by
      unfold capD Cap.cap
      rw [Antisymmetric.anchor_scale, Matrix3.mul_scale_left,
        Matrix3.mul_scale_right, Matrix3.scale_scale]
    _ = Matrix3.add Matrix3.identity
        (Matrix3.add
          (Matrix3.scale ((2 / capD) * x⁻¹) (Antisymmetric.anchor axis))
          (Matrix3.scale ((2 / capD) * (x⁻¹ * x⁻¹))
            (Matrix3.mul (Antisymmetric.anchor axis) (Antisymmetric.anchor axis)))) := by
      rw [Matrix3.scale_add, Matrix3.scale_scale, Matrix3.scale_scale]
    _ = Matrix3.add Matrix3.identity
        (Matrix3.add
          (Matrix3.scale ((2 / pathD) * x) (Antisymmetric.anchor axis))
          (Matrix3.scale (2 / pathD)
            (Matrix3.mul (Antisymmetric.anchor axis) (Antisymmetric.anchor axis)))) := by
      rw [linearCoefficient, quadraticCoefficient]
    _ = reciprocalAnchorPath x axis pathDefined := by
      unfold reciprocalAnchorPath pathD
      rw [Matrix3.scale_add, Matrix3.scale_scale]

/-- At zero the same finite formula is the half turn about the axis. This is substitution in the field, not a limiting
argument. -/
theorem reciprocalAnchorPath_zero (axis : Coordinates3.Vector K)
    (axisNonNull : axis.quadrance ≠ 0) :
    reciprocalAnchorPath 0 axis
        (reciprocalAnchorPath_zeroDefined axis axisNonNull) =
      Reflection.halfTurn axis axisNonNull := by
  have cancel := ExplicitField.mul_inv_cancel
    axis.quadrance axisNonNull
  have denominatorAtZero :
      reciprocalAnchorPathDenominator 0 axis = axis.quadrance := by
    unfold reciprocalAnchorPathDenominator
    ring1
  have expandedCancel :
      (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s) *
        (axis.t * axis.t + axis.r * axis.r + axis.s * axis.s)⁻¹ = 1 := by
    simpa only [Coordinates3.Vector.quadrance, Coordinates3.Vector.dot] using cancel
  unfold reciprocalAnchorPath
  rw [denominatorAtZero]
  ext <;>
    unfold Reflection.halfTurn Reflection.reflection <;>
    unfold Matrix3.neg Matrix3.sub Matrix3.add Matrix3.scale Matrix3.identity
      Matrix3.outer Matrix3.mul Antisymmetric.anchor Coordinates3.Vector.quadrance Coordinates3.Vector.dot <;>
    simp only [ExplicitField.div_eq_mul_inv] <;>
    (try rw [← expandedCancel]) <;> ring1

end Purelib.Geometry.Rotations.Cayley.Charts

end
