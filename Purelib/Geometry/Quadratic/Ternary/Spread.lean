module

public import Purelib.Algebra.Quadratic.Ternary.Basic
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Squares
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.Tactic.Ring

/-!
# Spreads for displayed ternary quadratic forms

The spread is a rational expression in two non-null directions. Its
rescaling and perpendicularity laws use the original form's bilinear
pairing and quadrance, without selecting projective representatives.
-/

public section

namespace Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm

open Purelib.Algebra.Field
open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

variable {K : Type*} [ExplicitField K]

/-- The spread between two non-null vectors is one minus their normalized squared pairing.

The two non-nullity certificates retain the geometric domain of the quotient.
Both quadrances and the pairing are evaluated in the supplied original form.
-/
@[expose] def spread (form : TernaryForm K) (left right : Vector3 K)
    (_leftNonNull : form.quadrance left ≠ 0) (_rightNonNull : form.quadrance right ≠ 0) : K :=
  1 - form.bilinear left right ^ 2 / (form.quadrance left * form.quadrance right)

/-- Interchanging two non-null directions preserves their spread. -/
theorem spread_comm (form : TernaryForm K) (left right : Vector3 K)
    (leftNonNull : form.quadrance left ≠ 0) (rightNonNull : form.quadrance right ≠ 0) :
    form.spread left right leftNonNull rightNonNull =
      form.spread right left rightNonNull leftNonNull := by
  unfold spread
  rw [form.bilinear_comm left right, mul_comm (form.quadrance left)]

/-- Nonzero scalar multiplication preserves the non-nullity of a direction. -/
theorem quadrance_scale_ne_zero (form : TernaryForm K) (scalar : K) (vector : Vector3 K)
    (scalarNonzero : scalar ≠ 0) (vectorNonNull : form.quadrance vector ≠ 0) :
    form.quadrance (Vector3.scale scalar vector) ≠ 0 := by
  rw [form.quadrance_scale, pow_two]
  exact ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero scalarNonzero scalarNonzero) vectorNonNull

/-- Rescaling the first direction by a nonzero scalar preserves spread.

The scaled direction retains its derived non-nullity certificate. Cancellation
uses the nonzero scale and both input quadrances.
-/
theorem spread_scale_left (form : TernaryForm K) (scalar : K) (left right : Vector3 K)
    (scalarNonzero : scalar ≠ 0) (leftNonNull : form.quadrance left ≠ 0)
    (rightNonNull : form.quadrance right ≠ 0) :
    form.spread (Vector3.scale scalar left) right
        (form.quadrance_scale_ne_zero scalar left scalarNonzero leftNonNull) rightNonNull =
      form.spread left right leftNonNull rightNonNull := by
  unfold spread
  congr 1
  rw [form.bilinear_scale_left, form.quadrance_scale]
  apply Ratio.ratio_eq_of_cross_product
  · exact ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero
        (by simpa only [pow_two] using ExplicitField.mul_ne_zero scalarNonzero scalarNonzero)
        leftNonNull) rightNonNull
  · exact ExplicitField.mul_ne_zero leftNonNull rightNonNull
  · ring1

/-- Rescaling the second direction by a nonzero scalar preserves spread. -/
theorem spread_scale_right (form : TernaryForm K) (scalar : K) (left right : Vector3 K)
    (scalarNonzero : scalar ≠ 0) (leftNonNull : form.quadrance left ≠ 0)
    (rightNonNull : form.quadrance right ≠ 0) :
    form.spread left (Vector3.scale scalar right) leftNonNull
        (form.quadrance_scale_ne_zero scalar right scalarNonzero rightNonNull) =
      form.spread left right leftNonNull rightNonNull := by
  rw [form.spread_comm,
    form.spread_scale_left scalar right left scalarNonzero rightNonNull leftNonNull,
    form.spread_comm right left]

/-- Spread one is exactly perpendicularity for two non-null directions.

Non-nullity permits clearing the denominator, and executable scalar equality
permits cancelling the remaining square. No sign restriction is needed.
-/
theorem spread_eq_one_iff_perpendicular [DecidableEq K] (form : TernaryForm K)
    (left right : Vector3 K) (leftNonNull : form.quadrance left ≠ 0)
    (rightNonNull : form.quadrance right ≠ 0) :
    form.spread left right leftNonNull rightNonNull = 1 ↔ form.Perpendicular left right := by
  constructor
  · intro spreadOne
    have quotientZero :
        form.bilinear left right ^ 2 / (form.quadrance left * form.quadrance right) = 0 := by
      unfold spread at spreadOne
      calc
        form.bilinear left right ^ 2 / (form.quadrance left * form.quadrance right) =
            1 - (1 - form.bilinear left right ^ 2 / (form.quadrance left * form.quadrance right)) := by ring1
        _ = 0 := by rw [spreadOne]; ring1
    have squareZero : form.bilinear left right ^ 2 = 0 := by
      calc
        form.bilinear left right ^ 2 =
            (form.bilinear left right ^ 2 / (form.quadrance left * form.quadrance right)) *
              (form.quadrance left * form.quadrance right) :=
          (ExplicitField.div_mul_cancel _ (ExplicitField.mul_ne_zero leftNonNull rightNonNull)).symm
        _ = 0 := by rw [quotientZero, zero_mul]
    exact (Squares.square_eq_zero_iff _).mp squareZero
  · intro perpendicular
    change form.bilinear left right = 0 at perpendicular
    unfold spread
    rw [perpendicular, zero_pow (by decide : 2 ≠ 0), ExplicitField.zero_div]
    ring1

end Purelib.Algebra.Quadratic.Ternary.Basic.TernaryForm
