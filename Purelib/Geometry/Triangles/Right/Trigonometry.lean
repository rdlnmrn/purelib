module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Cross
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Null
import Purelib.Geometry.Plane.Line.Quadrance
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Trigonometry.Conversion
public import Purelib.Geometry.Plane.Line.Twist
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Triangles.Right.Quadrance
import Purelib.Geometry.Triangles.Trigonometry.Spread
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Null

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Triangles

open Purelib.Geometry.Trigonometry

section
@[expose] public section

/-!
# Divine Proportions, §§6.4–6.7: triangle ratio theorems

The book's quotient identities are retained exactly.  Every cancellation is
backed by a displayed non-null side or a characteristic hypothesis.
-/

namespace Purelib.Geometry.Triangles.Right.Trigonometry

variable {K : Type*} [ExplicitField K]

/-- Theorem 35 (Spread ratio), at the first vertex of a non-null right triangle whose right vertex is the third point.
-/
theorem spread_ratio [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (firstSecondNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAtThird :
      (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
        (Incidence.lineThrough second third secondThirdDistinct)) :
    Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
        (Incidence.lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      Quadrance.quadrance second third / Quadrance.quadrance first second := by
  have q₂Nonzero := TriangleRatios.quadrance_ne_zero_of_line_nonNull
    first third firstThirdDistinct firstThirdNonNull
  have q₃Nonzero := TriangleRatios.quadrance_ne_zero_of_line_nonNull
    first second firstSecondDistinct firstSecondNonNull
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have factorNonzero : (4 : K) * Quadrance.quadrance first third ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero q₂Nonzero
  have rightQuadrea := Right.Quadrance.right_triangle_quadrea first second third
    firstThirdDistinct secondThirdDistinct twoNonzero rightAtThird
  have firstSecondReversedNonNull := Purelib.Geometry.Plane.Line.Null.reversedLine_nonNull
    first second firstSecondDistinct firstSecondNonNull
  have firstThirdReversedNonNull := Purelib.Geometry.Plane.Line.Null.reversedLine_nonNull
    first third firstThirdDistinct firstThirdNonNull
  have reverseSpread := NonNull.Basic.NonNullTriangle.spread_lineThrough_reverse_both first second third
    firstSecondDistinct firstThirdDistinct
    firstSecondNonNull firstThirdNonNull
  have spreadQuadrea := Trigonometry.Spread.quadrea_spread second third first
    firstSecondDistinct.symm firstThirdDistinct.symm
    firstSecondReversedNonNull firstThirdReversedNonNull
  rw [Quadrea.Basic.quadrea_cyclic first second third] at spreadQuadrea
  rw [Quadrance.quadrance_symm third first, Quadrance.quadrance_symm second first,
    ← reverseSpread] at spreadQuadrea
  have productZero :
      (4 * Quadrance.quadrance first third) *
        (Quadrance.quadrance second third -
          Quadrance.quadrance first second *
            Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
              (Incidence.lineThrough first third firstThirdDistinct)
              firstSecondNonNull firstThirdNonNull) = 0 := by
    calc
      (4 * Quadrance.quadrance first third) *
          (Quadrance.quadrance second third -
            Quadrance.quadrance first second *
              Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
                (Incidence.lineThrough first third firstThirdDistinct)
                firstSecondNonNull firstThirdNonNull) =
        4 * Quadrance.quadrance second third * Quadrance.quadrance first third -
          4 * Quadrance.quadrance first third * Quadrance.quadrance first second *
            Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
              (Incidence.lineThrough first third firstThirdDistinct)
              firstSecondNonNull firstThirdNonNull := by ring1
      _ = 0 := by rw [← rightQuadrea, ← spreadQuadrea]; ring1
  have differenceZero :=
    ExplicitField.eq_zero_of_mul_eq_zero_left factorNonzero productZero
  have productRelation :
      Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
          (Incidence.lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull * Quadrance.quadrance first second =
        Quadrance.quadrance second third := by
    calc
      Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
            (Incidence.lineThrough first third firstThirdDistinct)
            firstSecondNonNull firstThirdNonNull * Quadrance.quadrance first second =
          Quadrance.quadrance first second *
            Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
              (Incidence.lineThrough first third firstThirdDistinct)
              firstSecondNonNull firstThirdNonNull := by ring1
      _ = Quadrance.quadrance second third -
          (Quadrance.quadrance second third - Quadrance.quadrance first second *
            Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
              (Incidence.lineThrough first third firstThirdDistinct)
              firstSecondNonNull firstThirdNonNull) := by ring1
      _ = Quadrance.quadrance second third := by rw [differenceZero]; ring1
  have denominatorCancel : Quadrance.quadrance first second *
      (Quadrance.quadrance first second)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ q₃Nonzero
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
        (Incidence.lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
          (Incidence.lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull *
        (Quadrance.quadrance first second * (Quadrance.quadrance first second)⁻¹) := by
          rw [denominatorCancel, mul_one]
    _ = Quadrance.quadrance second third * (Quadrance.quadrance first second)⁻¹ := by
      rw [← mul_assoc, productRelation]

/-- Theorem 36 (Cross ratio), at the same vertex. -/
theorem cross_ratio [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (firstSecondNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (rightAtThird :
      (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
        (Incidence.lineThrough second third secondThirdDistinct)) :
    Cross.cross (Incidence.lineThrough first second firstSecondDistinct)
        (Incidence.lineThrough first third firstThirdDistinct)
        firstSecondNonNull firstThirdNonNull =
      Quadrance.quadrance first third / Quadrance.quadrance first second := by
  have q₃Nonzero := TriangleRatios.quadrance_ne_zero_of_line_nonNull
    first second firstSecondDistinct firstSecondNonNull
  have q₃Cancel : Quadrance.quadrance first second *
      (Quadrance.quadrance first second)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ q₃Nonzero
  have pythagoras :=
    (Right.Quadrance.pythagoras_iff_perpendicular first second third
      firstThirdDistinct secondThirdDistinct twoNonzero).2 rightAtThird
  have sumOne := Trigonometry.Conversion.spread_add_cross
    (Incidence.lineThrough first second firstSecondDistinct)
    (Incidence.lineThrough first third firstThirdDistinct)
    firstSecondNonNull firstThirdNonNull
  have spreadValue := spread_ratio first second third
    firstSecondDistinct firstThirdDistinct secondThirdDistinct
    firstSecondNonNull firstThirdNonNull twoNonzero rightAtThird
  have crossAsComplement :
      Cross.cross (Incidence.lineThrough first second firstSecondDistinct)
          (Incidence.lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull =
        1 - Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
          (Incidence.lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull := by
    calc
      Cross.cross (Incidence.lineThrough first second firstSecondDistinct)
          (Incidence.lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull =
        (Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
            (Incidence.lineThrough first third firstThirdDistinct)
            firstSecondNonNull firstThirdNonNull +
          Cross.cross (Incidence.lineThrough first second firstSecondDistinct)
            (Incidence.lineThrough first third firstThirdDistinct)
            firstSecondNonNull firstThirdNonNull) -
          Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
            (Incidence.lineThrough first third firstThirdDistinct)
            firstSecondNonNull firstThirdNonNull := by ring1
      _ = 1 - Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
          (Incidence.lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull := by rw [sumOne]
  rw [crossAsComplement, spreadValue]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    1 - Quadrance.quadrance second third * (Quadrance.quadrance first second)⁻¹ =
        Quadrance.quadrance first second * (Quadrance.quadrance first second)⁻¹ -
          Quadrance.quadrance second third * (Quadrance.quadrance first second)⁻¹ := by
            rw [q₃Cancel]
    _ = Quadrance.quadrance first third * (Quadrance.quadrance first second)⁻¹ := by
      rw [← pythagoras]
      ring1

/-- Theorem 37 (Twist ratio). The only needed metric denominator is the nonzero second quadrance; the hypotenuse may be
null. -/
theorem twist_ratio [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (q₂Nonzero : Quadrance.quadrance first third ≠ 0)
    (rightAtThird :
      (Incidence.lineThrough first third firstThirdDistinct).Perpendicular
        (Incidence.lineThrough second third secondThirdDistinct))
    (notPerpendicularAtFirst :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).Perpendicular
        (Incidence.lineThrough first third firstThirdDistinct)) :
    Twist.twist (Incidence.lineThrough first second firstSecondDistinct)
        (Incidence.lineThrough first third firstThirdDistinct)
        notPerpendicularAtFirst =
      Quadrance.quadrance second third / Quadrance.quadrance first third := by
  let determinant := Incidence.pointDeterminant first second third
  let dotAtFirst :=
    (first.y - second.y) * (first.y - third.y) +
      (second.x - first.x) * (third.x - first.x)
  have perpendicularEquation :
      (first.y - third.y) * (second.y - third.y) +
        (third.x - first.x) * (third.x - second.x) = 0 := by
    exact rightAtThird
  have dotValue : dotAtFirst = Quadrance.quadrance first third := by
    unfold dotAtFirst Quadrance.quadrance
    calc
      (first.y - second.y) * (first.y - third.y) +
          (second.x - first.x) * (third.x - first.x) =
        (third.x - first.x) ^ 2 + (third.y - first.y) ^ 2 -
          ((first.y - third.y) * (second.y - third.y) +
            (third.x - first.x) * (third.x - second.x)) := by ring1
      _ = (third.x - first.x) ^ 2 + (third.y - first.y) ^ 2 := by
        rw [perpendicularEquation]
        ring1
  have determinantSquare : determinant ^ 2 =
      Quadrance.quadrance second third * Quadrance.quadrance first third := by
    have fibonacci : determinant ^ 2 +
        ((first.y - third.y) * (second.y - third.y) +
          (third.x - first.x) * (third.x - second.x)) ^ 2 =
        Quadrance.quadrance second third * Quadrance.quadrance first third := by
      unfold determinant Incidence.pointDeterminant Quadrance.quadrance
      ring1
    rw [perpendicularEquation] at fibonacci
    calc
      determinant ^ 2 = determinant ^ 2 + (0 : K) ^ 2 := by ring1
      _ = Quadrance.quadrance second third * Quadrance.quadrance first third := fibonacci
  have q₂SquareNonzero : Quadrance.quadrance first third ^ 2 ≠ 0 := by
    rw [pow_two]
    exact ExplicitField.mul_ne_zero q₂Nonzero q₂Nonzero
  have q₂SquareCancel : Quadrance.quadrance first third ^ 2 *
      (Quadrance.quadrance first third ^ 2)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ q₂SquareNonzero
  unfold Twist.twist
  change
    (((first.y - second.y) * (third.x - first.x) -
      (first.y - third.y) * (second.x - first.x)) ^ 2) /
      dotAtFirst ^ 2 = Quadrance.quadrance second third / Quadrance.quadrance first third
  have determinantCoordinate :
      ((first.y - second.y) * (third.x - first.x) -
        (first.y - third.y) * (second.x - first.x)) ^ 2 =
        determinant ^ 2 := by
    unfold determinant Incidence.pointDeterminant
    ring1
  rw [determinantCoordinate, determinantSquare, dotValue]
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    Quadrance.quadrance second third * Quadrance.quadrance first third *
        (Quadrance.quadrance first third ^ 2)⁻¹ =
      Quadrance.quadrance second third * (Quadrance.quadrance first third)⁻¹ *
        (Quadrance.quadrance first third ^ 2 *
          (Quadrance.quadrance first third ^ 2)⁻¹) := by
            have q₂Cancel : Quadrance.quadrance first third *
                (Quadrance.quadrance first third)⁻¹ = (1 : K) :=
              ExplicitField.mul_inv_cancel _ q₂Nonzero
            calc
              Quadrance.quadrance second third * Quadrance.quadrance first third *
                  (Quadrance.quadrance first third ^ 2)⁻¹ =
                Quadrance.quadrance second third * (Quadrance.quadrance first third)⁻¹ *
                  (Quadrance.quadrance first third ^ 2 *
                    (Quadrance.quadrance first third ^ 2)⁻¹) +
                  Quadrance.quadrance second third * (Quadrance.quadrance first third ^ 2)⁻¹ *
                    (Quadrance.quadrance first third -
                      Quadrance.quadrance first third ^ 2 *
                        (Quadrance.quadrance first third)⁻¹) := by ring1
              _ = Quadrance.quadrance second third * (Quadrance.quadrance first third)⁻¹ *
                  (Quadrance.quadrance first third ^ 2 *
                    (Quadrance.quadrance first third ^ 2)⁻¹) := by
                      rw [show Quadrance.quadrance first third ^ 2 *
                        (Quadrance.quadrance first third)⁻¹ =
                          Quadrance.quadrance first third by
                            calc
                              Quadrance.quadrance first third ^ 2 *
                                  (Quadrance.quadrance first third)⁻¹ =
                                Quadrance.quadrance first third *
                                  (Quadrance.quadrance first third *
                                    (Quadrance.quadrance first third)⁻¹) := by ring1
                              _ = Quadrance.quadrance first third := by
                                rw [q₂Cancel, mul_one]]
                      ring1
    _ = Quadrance.quadrance second third * (Quadrance.quadrance first third)⁻¹ := by
      rw [q₂SquareCancel, mul_one]
end Purelib.Geometry.Triangles.Right.Trigonometry

end
