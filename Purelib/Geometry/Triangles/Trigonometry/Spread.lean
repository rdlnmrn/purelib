module
import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Null
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Tactic.Ring

open Purelib.Geometry.Plane (Line)
open Purelib.Geometry.Triangles.NonNull.Basic

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane.Line

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

namespace Purelib.Geometry.Triangles.Trigonometry.Spread

variable {K : Type*} [ExplicitField K]

/-- Quadrea is four times the product of two side quadrances and their included spread.

The incident side lines are constructed from distinct endpoints and both are non-null. -/
theorem quadrea_spread [DecidableEq K]
    (first second third : Plane.Point K)
    (firstDistinct : first ≠ third) (secondDistinct : second ≠ third)
    (firstNonNull : ¬ (Incidence.lineThrough first third firstDistinct).IsNull)
    (secondNonNull : ¬ (Incidence.lineThrough second third secondDistinct).IsNull) :
    Quadrea.Basic.quadrea first second third =
      4 * Quadrance.quadrance second third * Quadrance.quadrance first third *
        Spread.spread (Incidence.lineThrough first third firstDistinct)
          (Incidence.lineThrough second third secondDistinct)
          firstNonNull secondNonNull := by
  let determinant := Incidence.pointDeterminant first second third
  have sideOneNonzero := TriangleRatios.quadrance_ne_zero_of_line_nonNull
    second third secondDistinct secondNonNull
  have sideTwoNonzero := TriangleRatios.quadrance_ne_zero_of_line_nonNull
    first third firstDistinct firstNonNull
  have denominatorNonzero :
      Quadrance.quadrance first third * Quadrance.quadrance second third ≠ 0 :=
    ExplicitField.mul_ne_zero sideTwoNonzero sideOneNonzero
  have denominatorCancel :
      (Quadrance.quadrance first third * Quadrance.quadrance second third) *
        (Quadrance.quadrance first third * Quadrance.quadrance second third)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ denominatorNonzero
  rw [Quadrea.Basic.quadrea_coordinate_formula]
  rw [Spread.spread_from_points first second third firstDistinct secondDistinct
    firstNonNull secondNonNull]
  simp only [ExplicitField.div_eq_mul_inv]
  have coordinateDeterminant :
      ((first.y - third.y) * (third.x - second.x) -
        (second.y - third.y) * (third.x - first.x)) ^ 2 =
        determinant ^ 2 := by
    unfold determinant Incidence.pointDeterminant
    ring1
  rw [coordinateDeterminant]
  calc
    4 * determinant ^ 2 = 4 * determinant ^ 2 * 1 := by ring1
    _ = 4 * determinant ^ 2 *
        ((Quadrance.quadrance first third * Quadrance.quadrance second third) *
          (Quadrance.quadrance first third * Quadrance.quadrance second third)⁻¹) := by
            rw [denominatorCancel]
    _ = 4 * Quadrance.quadrance second third * Quadrance.quadrance first third *
        (determinant ^ 2 *
          (Quadrance.quadrance first third * Quadrance.quadrance second third)⁻¹) := by ring1

/-- The ratios of each vertex spread to its opposite side quadrance agree.

All three side lines are non-null and have distinct endpoints, and the field has nonzero two. -/
theorem spread_law [DecidableEq K]
    (first second third : Plane.Point K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (firstSecondNonNull :
      ¬ (Incidence.lineThrough first second firstSecondDistinct).IsNull)
    (firstThirdNonNull :
      ¬ (Incidence.lineThrough first third firstThirdDistinct).IsNull)
    (secondThirdNonNull :
      ¬ (Incidence.lineThrough second third secondThirdDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0) :
    Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
          (Incidence.lineThrough first third firstThirdDistinct)
          firstSecondNonNull firstThirdNonNull / Quadrance.quadrance second third =
      Spread.spread (Incidence.lineThrough second first firstSecondDistinct.symm)
          (Incidence.lineThrough second third secondThirdDistinct)
          (by
            exact Line.Null.reversedLine_nonNull
              first second firstSecondDistinct firstSecondNonNull)
          secondThirdNonNull / Quadrance.quadrance first third ∧
    Spread.spread (Incidence.lineThrough second first firstSecondDistinct.symm)
          (Incidence.lineThrough second third secondThirdDistinct)
          (by
            exact Line.Null.reversedLine_nonNull
              first second firstSecondDistinct firstSecondNonNull)
          secondThirdNonNull / Quadrance.quadrance first third =
      Spread.spread (Incidence.lineThrough third first firstThirdDistinct.symm)
          (Incidence.lineThrough third second secondThirdDistinct.symm)
          (by
            exact Line.Null.reversedLine_nonNull
              first third firstThirdDistinct firstThirdNonNull)
          (by
            exact Line.Null.reversedLine_nonNull
              second third secondThirdDistinct secondThirdNonNull) /
        Quadrance.quadrance first second := by
  -- The proof is algebraically cleaner after naming the reversed-side
  -- non-null certificates used at the second and third vertices.
  let firstSecondReversedNonNull :
      ¬ (Incidence.lineThrough second first firstSecondDistinct.symm).IsNull := by
    exact Line.Null.reversedLine_nonNull
      first second firstSecondDistinct firstSecondNonNull
  let firstThirdReversedNonNull :
      ¬ (Incidence.lineThrough third first firstThirdDistinct.symm).IsNull := by
    exact Line.Null.reversedLine_nonNull
      first third firstThirdDistinct firstThirdNonNull
  let secondThirdReversedNonNull :
      ¬ (Incidence.lineThrough third second secondThirdDistinct.symm).IsNull := by
    exact Line.Null.reversedLine_nonNull
      second third secondThirdDistinct secondThirdNonNull
  let s₁ := Spread.spread (Incidence.lineThrough first second firstSecondDistinct)
    (Incidence.lineThrough first third firstThirdDistinct)
    firstSecondNonNull firstThirdNonNull
  let s₂ := Spread.spread (Incidence.lineThrough second first firstSecondDistinct.symm)
    (Incidence.lineThrough second third secondThirdDistinct)
    firstSecondReversedNonNull secondThirdNonNull
  let s₃ := Spread.spread (Incidence.lineThrough third first firstThirdDistinct.symm)
    (Incidence.lineThrough third second secondThirdDistinct.symm)
    firstThirdReversedNonNull secondThirdReversedNonNull
  have q₁Nonzero := TriangleRatios.quadrance_ne_zero_of_line_nonNull
    second third secondThirdDistinct secondThirdNonNull
  have q₂Nonzero := TriangleRatios.quadrance_ne_zero_of_line_nonNull
    first third firstThirdDistinct firstThirdNonNull
  have q₃Nonzero := TriangleRatios.quadrance_ne_zero_of_line_nonNull
    first second firstSecondDistinct firstSecondNonNull
  have fourAsProduct : (4 : K) = 2 * 2 := by ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [fourAsProduct]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have factorFor12 : (4 : K) * Quadrance.quadrance first second ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero q₃Nonzero
  have factorFor23 : (4 : K) * Quadrance.quadrance second third ≠ 0 :=
    ExplicitField.mul_ne_zero fourNonzero q₁Nonzero
  have reverseSpreadAtFirst := NonNullTriangle.spread_lineThrough_reverse_both
    first second third firstSecondDistinct firstThirdDistinct
    firstSecondNonNull firstThirdNonNull
  have reverseSpreadAtSecond := NonNullTriangle.spread_lineThrough_reverse_both
    second first third firstSecondDistinct.symm secondThirdDistinct
    firstSecondReversedNonNull secondThirdNonNull
  have reverseSpreadAtThird := NonNullTriangle.spread_lineThrough_reverse_both
    third first second firstThirdDistinct.symm secondThirdDistinct.symm
    firstThirdReversedNonNull secondThirdReversedNonNull
  have areaAtFirst := quadrea_spread second third first
    firstSecondDistinct.symm firstThirdDistinct.symm
    firstSecondReversedNonNull firstThirdReversedNonNull
  have areaAtSecond := quadrea_spread first third second
    firstSecondDistinct secondThirdDistinct.symm
    firstSecondNonNull secondThirdReversedNonNull
  have areaAtThird := quadrea_spread first second third
    firstThirdDistinct secondThirdDistinct
    firstThirdNonNull secondThirdNonNull
  rw [Quadrea.Basic.quadrea_cyclic first second third] at areaAtFirst
  rw [Quadrea.Basic.quadrea_swap_second_third first second third] at areaAtSecond
  rw [Quadrance.quadrance_symm third first, Quadrance.quadrance_symm second first,
    ← reverseSpreadAtFirst] at areaAtFirst
  rw [Quadrance.quadrance_symm third second, ← reverseSpreadAtSecond] at areaAtSecond
  rw [← reverseSpreadAtThird] at areaAtThird
  change Quadrea.Basic.quadrea first second third =
      4 * Quadrance.quadrance first third * Quadrance.quadrance first second * s₁ at areaAtFirst
  change Quadrea.Basic.quadrea first second third =
      4 * Quadrance.quadrance second third * Quadrance.quadrance first second * s₂ at areaAtSecond
  change Quadrea.Basic.quadrea first second third =
      4 * Quadrance.quadrance second third * Quadrance.quadrance first third * s₃ at areaAtThird
  have firstSecondCross : s₁ * Quadrance.quadrance first third =
      s₂ * Quadrance.quadrance second third := by
    have productZero : (4 * Quadrance.quadrance first second) *
        (s₁ * Quadrance.quadrance first third -
          s₂ * Quadrance.quadrance second third) = 0 := by
      calc
        (4 * Quadrance.quadrance first second) *
            (s₁ * Quadrance.quadrance first third -
              s₂ * Quadrance.quadrance second third) =
          4 * Quadrance.quadrance first third * Quadrance.quadrance first second * s₁ -
            4 * Quadrance.quadrance second third * Quadrance.quadrance first second * s₂ := by
              ring1
        _ = 0 := by rw [← areaAtFirst, ← areaAtSecond]; ring1
    have differenceZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left factorFor12 productZero
    calc
      s₁ * Quadrance.quadrance first third =
          (s₁ * Quadrance.quadrance first third -
            s₂ * Quadrance.quadrance second third) +
            s₂ * Quadrance.quadrance second third := by ring1
      _ = s₂ * Quadrance.quadrance second third := by rw [differenceZero]; ring1
  have secondThirdCross : s₂ * Quadrance.quadrance first second =
      s₃ * Quadrance.quadrance first third := by
    have productZero : (4 * Quadrance.quadrance second third) *
        (s₂ * Quadrance.quadrance first second -
          s₃ * Quadrance.quadrance first third) = 0 := by
      calc
        (4 * Quadrance.quadrance second third) *
            (s₂ * Quadrance.quadrance first second -
              s₃ * Quadrance.quadrance first third) =
          4 * Quadrance.quadrance second third * Quadrance.quadrance first second * s₂ -
            4 * Quadrance.quadrance second third * Quadrance.quadrance first third * s₃ := by
              ring1
        _ = 0 := by rw [← areaAtSecond, ← areaAtThird]; ring1
    have differenceZero :=
      ExplicitField.eq_zero_of_mul_eq_zero_left factorFor23 productZero
    calc
      s₂ * Quadrance.quadrance first second =
          (s₂ * Quadrance.quadrance first second -
            s₃ * Quadrance.quadrance first third) +
            s₃ * Quadrance.quadrance first third := by ring1
      _ = s₃ * Quadrance.quadrance first third := by rw [differenceZero]; ring1
  change s₁ / Quadrance.quadrance second third =
      s₂ / Quadrance.quadrance first third ∧
    s₂ / Quadrance.quadrance first third = s₃ / Quadrance.quadrance first second
  constructor
  · exact Ratio.ratio_eq_of_cross_product q₁Nonzero q₂Nonzero
      firstSecondCross
  · exact Ratio.ratio_eq_of_cross_product q₂Nonzero q₃Nonzero
      secondThirdCross

end Purelib.Geometry.Triangles.Trigonometry.Spread

end
