module

public import Purelib.Geometry.Quadratic.Ternary.Lorentz
public import Purelib.Algebra.Field.ExplicitOrder.Sign
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Ordered Lorentz perpendicular geometry

The orthogonal plane of a timelike vector has strictly positive negative
quadrance on every nonzero vector. The proof uses finite coordinate
identities and the original field's explicit positivity laws.
-/

public section

namespace Purelib.Geometry.Quadratic.Ternary.Lorentz

open Purelib.Algebra.Field (ExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Basic (OrderedExplicitField)
open Purelib.Algebra.Field.ExplicitOrder.Sign (RayOrderedExplicitField)
open Purelib.Algebra.Quadratic.Ternary.Basic renaming TernaryForm -> Form
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [RayOrderedExplicitField K] (oneNonzero : (1 : K) ≠ 0)

/-- Use the equality decision retained by the original ordered field. -/
local instance : DecidableEq K := OrderedExplicitField.eq_decidable

/-- A positive Lorentz quadrance forces a nonzero time coordinate. -/
theorem time_ne_zero_of_quadrance_pos (axis : Vector3 K)
    (positive : 0 < (Form.lorentz oneNonzero).quadrance axis) : axis.t ≠ 0 := by
  have squaresPositive := RayOrderedExplicitField.add_square_pos
    (value := axis.s) (RayOrderedExplicitField.add_square_pos (value := axis.r) positive)
  have timeSquare : (Form.lorentz oneNonzero).quadrance axis + axis.r ^ 2 + axis.s ^ 2 = axis.t ^ 2 := by
    rw [Form.quadrance_lorentz]
    ring1
  rw [timeSquare] at squaresPositive
  have squareNonzero := RayOrderedExplicitField.positive_ne_zero_direct squaresPositive
  intro timeZero
  apply squareNonzero
  rw [timeZero]
  ring1

/-- Every nonzero vector perpendicular to a timelike vector has positive negative quadrance.

The time coordinate of the timelike axis is nonzero. Multiplication by
its square identifies the negative test quadrance with a positive
multiple of the spatial square sum plus a square.
-/
theorem neg_quadrance_pos_of_perpendicular_timelike (axis vector : Vector3 K)
    (positive : 0 < (Form.lorentz oneNonzero).quadrance axis)
    (perpendicular : (Form.lorentz oneNonzero).Perpendicular vector axis)
    (nonzero : vector ≠ Vector3.zero) :
    0 < -(Form.lorentz oneNonzero).quadrance vector := by
  have timeNonzero := time_ne_zero_of_quadrance_pos oneNonzero axis positive
  have pairing : axis.t * vector.t = axis.r * vector.r + axis.s * vector.s := by
    have pairZero := perpendicular
    change (Form.lorentz oneNonzero).bilinear vector axis = 0 at pairZero
    rw [Form.bilinear_lorentz] at pairZero
    calc
      _ = (vector.t * axis.t - vector.r * axis.r - vector.s * axis.s) +
          (axis.r * vector.r + axis.s * vector.s) := by ring1
      _ = _ := by rw [pairZero]; ring1
  have spatialNonzero : vector.r ≠ 0 ∨ vector.s ≠ 0 := by
    by_cases firstZero : vector.r = 0
    · right
      intro secondZero
      have timeProduct : axis.t * vector.t = 0 := by rw [pairing, firstZero, secondZero]; ring1
      have vectorTimeZero : vector.t = 0 := by
        calc
          _ = axis.t⁻¹ * (axis.t * vector.t) := by
            rw [← mul_assoc, show axis.t⁻¹ * axis.t = 1 from
              (mul_comm _ _).trans (ExplicitField.mul_inv_cancel axis.t timeNonzero), one_mul]
          _ = 0 := by rw [timeProduct]; ring1
      apply nonzero
      ext <;> assumption
    · exact Or.inl firstZero
  have spatialPositive : 0 < vector.r ^ 2 + vector.s ^ 2 := by
    cases spatialNonzero with
    | inl firstNonzero =>
      exact RayOrderedExplicitField.add_square_pos (value := vector.s)
        (by simpa only [pow_two] using OrderedExplicitField.mul_self_pos_direct firstNonzero)
    | inr secondNonzero =>
      rw [add_comm]
      exact RayOrderedExplicitField.add_square_pos (value := vector.r)
        (by simpa only [pow_two] using OrderedExplicitField.mul_self_pos_direct secondNonzero)
  have multiplied : axis.t ^ 2 * (-(Form.lorentz oneNonzero).quadrance vector) =
      (Form.lorentz oneNonzero).quadrance axis * (vector.r ^ 2 + vector.s ^ 2) +
        (axis.r * vector.s - axis.s * vector.r) ^ 2 := by
    have pairedSquare := congrArg (fun scalar : K => scalar ^ 2) pairing
    rw [Form.quadrance_lorentz, Form.quadrance_lorentz]
    calc
      _ = (axis.t ^ 2 * (vector.r ^ 2 + vector.s ^ 2) - (axis.t * vector.t) ^ 2) := by ring1
      _ = _ := by rw [pairedSquare]; ring1
  have numeratorPositive := RayOrderedExplicitField.add_square_pos
    (value := axis.r * vector.s - axis.s * vector.r)
    (OrderedExplicitField.mul_pos_direct positive spatialPositive)
  rw [← multiplied] at numeratorPositive
  have timeSquarePositive : 0 < axis.t ^ 2 := by
    simpa only [pow_two] using OrderedExplicitField.mul_self_pos_direct timeNonzero
  have timeSquareNonzero := RayOrderedExplicitField.positive_ne_zero_direct timeSquarePositive
  have quotientPositive := OrderedExplicitField.mul_pos_direct
    (OrderedExplicitField.inv_pos_direct timeSquarePositive) numeratorPositive
  rw [← mul_assoc, show (axis.t ^ 2)⁻¹ * axis.t ^ 2 = 1 from
    (mul_comm _ _).trans (ExplicitField.mul_inv_cancel (axis.t ^ 2) timeSquareNonzero), one_mul] at quotientPositive
  exact quotientPositive

end Purelib.Geometry.Quadratic.Ternary.Lorentz
