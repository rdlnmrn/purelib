module
import Purelib.Algebra.Field.Ratio
import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Geometry.Plane.Line.Spread.Triple
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Eleven
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Cross
import Purelib.Geometry.Plane.Line.Cross.Triple
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Triangles.Quadrea.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, §7.7: quadruple spread and cross formulas

The scalar elimination is kept separate from the geometric specialization.
Two displayed spread triples give two explicit quadratic equations with a
common root; the finite quadratic-compatibility calculation then yields the
four-variable polynomial.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterSeven

open Purelib.Geometry

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace ExerciseSevenFourteenCounterexample

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Plane.Line
/-- The displayed line with coefficients (1, 0, 0) modulo eleven. -/
def line₁ :
  Purelib.Geometry.Plane.Line Eleven.Element := ⟨1, 0, 0, Or.inl (by decide)⟩
/-- The displayed line with coefficients (1, 1, 0) modulo eleven. -/
def line₂ :
  Purelib.Geometry.Plane.Line Eleven.Element := ⟨1, 1, 0, Or.inl (by decide)⟩
/-- The displayed line with coefficients (0, 1, 0) modulo eleven. -/
def line₃ :
  Purelib.Geometry.Plane.Line Eleven.Element := ⟨0, 1, 0, Or.inr (by decide)⟩
/-- The displayed line with coefficients (1, 2, 0) modulo eleven. -/
def line₄ :
  Purelib.Geometry.Plane.Line Eleven.Element := ⟨1, 2, 0, Or.inl (by decide)⟩

end

section
open Purelib.Geometry.Plane.Line.Basic
open formalisations.DivineProportions.Chapters.Examples.ChapterSeven
open formalisations.DivineProportions.Chapters.Examples.ChapterSeven.ExerciseSevenFourteenCounterexample
/-- The displayed line ₁ has nonzero direction quadrance modulo eleven. -/
theorem
  line₁_nonNull
  : ¬ line₁.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₁
  decide

/-- The displayed line ₂ has nonzero direction quadrance modulo eleven. -/
theorem
  line₂_nonNull
  : ¬ line₂.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₂
  decide

/-- The displayed line ₃ has nonzero direction quadrance modulo eleven. -/
theorem
  line₃_nonNull
  : ¬ line₃.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₃
  decide

/-- The displayed line ₄ has nonzero direction quadrance modulo eleven. -/
theorem
  line₄_nonNull
  : ¬ line₄.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₄
  decide

end

open Purelib.Geometry.Plane.Line
open formalisations.DivineProportions.Chapters.Examples.ChapterSeven
/-- The adjacent crosses are `6,6,3,9` in `F₁₁`, while the first
diagonal cross is zero. -/
theorem
  cross_values
  :
    Cross.cross line₁ line₂
      line₁_nonNull line₂_nonNull = 6 ∧
      Cross.cross line₂ line₃
        line₂_nonNull line₃_nonNull = 6 ∧
      Cross.cross line₃ line₄
        line₃_nonNull line₄_nonNull = 3 ∧
      Cross.cross line₁ line₄
        line₁_nonNull line₄_nonNull = 9 ∧
      Cross.cross line₁ line₃
        line₁_nonNull line₃_nonNull = 0 := by
  decide

/-- Exercise 7.14's first printed right-hand side is one, not the actual
diagonal cross zero. -/
theorem
  printed_first_formula_fails
  :
    let c₁₂ := Cross.cross line₁ line₂
      line₁_nonNull line₂_nonNull
    let c₂₃ := Cross.cross line₂ line₃
      line₂_nonNull line₃_nonNull
    let c₃₄ := Cross.cross line₃ line₄
      line₃_nonNull line₄_nonNull
    let c₁₄ := Cross.cross line₁ line₄
      line₁_nonNull line₄_nonNull
    let c₁₃ := Cross.cross line₁ line₃
      line₁_nonNull line₃_nonNull
    let denominator :=
      2 * (c₁₂ + c₂₃ - c₃₄ - c₁₄ -
        2 * c₁₂ * c₂₃ + 2 * c₃₄ * c₁₄)
    denominator ≠ 0 ∧
      c₁₃ ≠ ((c₁₂ - c₂₃) ^ 2 - (c₃₄ - c₁₄) ^ 2) /
        denominator := by
  decide

end ExerciseSevenFourteenCounterexample
end formalisations.DivineProportions.Chapters.Examples.ChapterSeven

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 7 worked examples

This module records the exact rational calculation of Example 7.2 and the
fully executable finite-field calculation of Example 7.3.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterSeven

namespace ChapterSevenExamples
namespace ExampleSevenTwo

section
open Purelib.Data.Rat
open Purelib.Geometry.Plane.Point
/-- The displayed vertex ₁ with coordinates (1, 1) over the rationals. -/
def point₁ : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨1, 1⟩
/-- The displayed vertex ₂ with coordinates (5, 2) over the rationals. -/
def point₂ : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨5, 2⟩
/-- The displayed vertex ₃ with coordinates (3, -1) over the rationals. -/
def point₃ : Purelib.Geometry.Plane.Point Fraction.Rational := ⟨3, -1⟩

end

section
open Purelib.Data.Rat
open Purelib.Geometry.Plane.Line
/-- Line `A₂A₃`. -/
def line₁ : Purelib.Geometry.Plane.Line Fraction.Rational where
  a := 3
  b := -2
  c := -11
  direction_nonzero := Or.inl (by decide)

/-- Line `A₁A₃`. -/
def line₂ : Purelib.Geometry.Plane.Line Fraction.Rational where
  a := 2
  b := 2
  c := -4
  direction_nonzero := Or.inl (by decide)

/-- Line `A₁A₂`. -/
def line₃ : Purelib.Geometry.Plane.Line Fraction.Rational where
  a := -1
  b := 4
  c := -3
  direction_nonzero := Or.inl (by decide)

end

open Purelib.Geometry.Plane.Line.Basic in
/-- Each displayed side line contains both of its designated triangle vertices. -/
theorem line_incidence :
    line₁.Contains point₂ ∧ line₁.Contains point₃ ∧
      line₂.Contains point₁ ∧ line₂.Contains point₃ ∧
      line₃.Contains point₁ ∧ line₃.Contains point₂ := by
  unfold Purelib.Geometry.Plane.Line.Contains line₁ line₂ line₃ point₁ point₂ point₃
  exact ⟨by ring1, by ring1, by ring1, by ring1, by ring1, by ring1⟩

open Purelib.Geometry.Plane.Point in
/-- The three opposite-side quadrances are exactly 13, 8 and 17 over the rationals. -/
theorem quadrance_values :
    Quadrance.quadrance point₂ point₃ = 13 ∧
      Quadrance.quadrance point₁ point₃ = 8 ∧
      Quadrance.quadrance point₁ point₂ = 17 := by
  unfold Quadrance.quadrance point₁ point₂ point₃
  exact ⟨by ring1, by ring1, by ring1⟩

open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Triangles.Quadrea in
open Purelib.Geometry.Trigonometry.QuadTriple in
/-- The triangle has quadrea 400 over the rationals. -/
theorem quadrea_value : Basic.quadrea point₁ point₂ point₃ = 400 := by
  unfold Basic.quadrea Basic.archimedesFunction Quadrance.quadrance point₁ point₂ point₃
  ring1

section
open Purelib.Geometry.Plane.Line.Basic
/-- The side line ₁ has nonzero direction quadrance over the rationals. -/
theorem line₁_nonNull : ¬ line₁.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₁
  decide

/-- The side line ₂ has nonzero direction quadrance over the rationals. -/
theorem line₂_nonNull : ¬ line₂.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₂
  decide

/-- The side line ₃ has nonzero direction quadrance over the rationals. -/
theorem line₃_nonNull : ¬ line₃.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₃
  decide

end

section
open Purelib.Algebra.Field
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Plane.Line
/-- The three vertex spreads are exactly 25/34, 100/221 and 25/26 over the rationals. -/
theorem spread_values :
    Spread.spread line₂ line₃ line₂_nonNull line₃_nonNull =
        (25 : Fraction.Rational) / 34 ∧
      Spread.spread line₁ line₃ line₁_nonNull line₃_nonNull =
        (100 : Fraction.Rational) / 221 ∧
      Spread.spread line₁ line₂ line₁_nonNull line₂_nonNull =
        (25 : Fraction.Rational) / 26 := by
  constructor
  · unfold Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero line₂_nonNull line₃_nonNull)
      (Cast.rational_natCast_nonzero (by decide : 34 ≠ 0))
    unfold line₂ line₃
    ring1
  constructor
  · unfold Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero line₁_nonNull line₃_nonNull)
      (Cast.rational_natCast_nonzero (by decide : 221 ≠ 0))
    unfold line₁ line₃
    ring1
  · unfold Spread.spread
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero line₁_nonNull line₂_nonNull)
      (Cast.rational_natCast_nonzero (by decide : 26 ≠ 0))
    unfold line₁ line₂
    ring1

/-- The three rational vertex crosses are exactly 9/34, 121/221 and 1/26. -/
theorem cross_values :
    Cross.cross line₂ line₃ line₂_nonNull line₃_nonNull =
        (9 : Fraction.Rational) / 34 ∧
      Cross.cross line₁ line₃ line₁_nonNull line₃_nonNull =
        (121 : Fraction.Rational) / 221 ∧
      Cross.cross line₁ line₂ line₁_nonNull line₂_nonNull =
        (1 : Fraction.Rational) / 26 := by
  constructor
  · unfold Cross.cross
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero line₂_nonNull line₃_nonNull)
      (Cast.rational_natCast_nonzero (by decide : 34 ≠ 0))
    unfold line₂ line₃
    ring1
  constructor
  · unfold Cross.cross
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero line₁_nonNull line₃_nonNull)
      (Cast.rational_natCast_nonzero (by decide : 221 ≠ 0))
    unfold line₁ line₃
    ring1
  · unfold Cross.cross
    apply Ratio.ratio_eq_of_cross_product
      (ExplicitField.mul_ne_zero line₁_nonNull line₂_nonNull)
      (Cast.rational_natCast_nonzero (by decide : 26 ≠ 0))
    unfold line₁ line₂
    ring1

end

open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Plane.Line.Cross in
open Purelib.Geometry.Plane.Line.Spread in
/-- The two chapter formulas evaluated on the displayed rational triangle. -/
theorem triple_formulas :
    let s₁ := Spread.spread line₂ line₃ line₂_nonNull line₃_nonNull
    let s₂ := Spread.spread line₁ line₃ line₁_nonNull line₃_nonNull
    let s₃ := Spread.spread line₁ line₂ line₁_nonNull line₂_nonNull
    let c₁ := Cross.cross line₂ line₃ line₂_nonNull line₃_nonNull
    let c₂ := Cross.cross line₁ line₃ line₁_nonNull line₃_nonNull
    let c₃ := Cross.cross line₁ line₂ line₁_nonNull line₂_nonNull
    (s₁ + s₂ + s₃) ^ 2 =
        2 * (s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2) + 4 * s₁ * s₂ * s₃ ∧
      (c₁ + c₂ + c₃ - 1) ^ 2 = 4 * c₁ * c₂ * c₃ := by
  dsimp only
  exact ⟨Triple.triple_spread_formula line₁ line₂ line₃ line₁_nonNull
      line₂_nonNull line₃_nonNull,
    Triple.triple_cross_formula line₁ line₂ line₃ line₁_nonNull line₂_nonNull
      line₃_nonNull⟩

end ExampleSevenTwo

namespace ExampleSevenThree

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Plane.Point
/-- The displayed vertex ₁ with coordinates (1, 1) modulo eleven. -/
def point₁ : Purelib.Geometry.Plane.Point Eleven.Element := ⟨1, 1⟩
/-- The displayed vertex ₂ with coordinates (3, 4) modulo eleven. -/
def point₂ : Purelib.Geometry.Plane.Point Eleven.Element := ⟨3, 4⟩
/-- The displayed vertex ₃ with coordinates (9, 5) modulo eleven. -/
def point₃ : Purelib.Geometry.Plane.Point Eleven.Element := ⟨9, 5⟩

end

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Plane.Line
/-- The side opposite vertex ₁, with coefficients (10, 6, 1) modulo eleven. -/
def line₁ : Purelib.Geometry.Plane.Line Eleven.Element where
  a := 10
  b := 6
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The side opposite vertex ₂, with coefficients (1, 9, 1) modulo eleven. -/
def line₂ : Purelib.Geometry.Plane.Line Eleven.Element where
  a := 1
  b := 9
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The side opposite vertex ₃, with coefficients (8, 2, 1) modulo eleven. -/
def line₃ : Purelib.Geometry.Plane.Line Eleven.Element where
  a := 8
  b := 2
  c := 1
  direction_nonzero := Or.inl (by decide)

end

section
open Purelib.Geometry.Plane.Line.Basic
/-- The side line ₁ has nonzero direction quadrance modulo eleven. -/
theorem line₁_nonNull : ¬ line₁.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₁
  decide

/-- The side line ₂ has nonzero direction quadrance modulo eleven. -/
theorem line₂_nonNull : ¬ line₂.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₂
  decide

/-- The side line ₃ has nonzero direction quadrance modulo eleven. -/
theorem line₃_nonNull : ¬ line₃.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₃
  decide

/-- Each displayed side line contains both of its designated triangle vertices. -/
theorem line_incidence :
    line₁.Contains point₂ ∧ line₁.Contains point₃ ∧
      line₂.Contains point₁ ∧ line₂.Contains point₃ ∧
      line₃.Contains point₁ ∧ line₃.Contains point₂ := by
  unfold Purelib.Geometry.Plane.Line.Contains line₁ line₂ line₃ point₁ point₂ point₃
  exact ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

end

open Purelib.Geometry.Plane.Point in
/-- The three opposite-side quadrances are exactly 4, 3 and 2 modulo eleven. -/
theorem quadrance_values :
    Quadrance.quadrance point₂ point₃ = 4 ∧
      Quadrance.quadrance point₁ point₃ = 3 ∧
      Quadrance.quadrance point₁ point₂ = 2 := by
  exact ⟨by decide, by decide, by decide⟩

open Purelib.Geometry.Triangles.Quadrea in
/-- The triangle has quadrea 1 modulo eleven. -/
theorem quadrea_value : Basic.quadrea point₁ point₂ point₃ = 1 := by
  decide

open Purelib.Geometry.Plane.Line in
/-- The three vertex spreads are exactly 6, 10 and 3 modulo eleven. -/
theorem spread_values :
    Spread.spread line₂ line₃ line₂_nonNull line₃_nonNull = 6 ∧
      Spread.spread line₁ line₃ line₁_nonNull line₃_nonNull = 10 ∧
      Spread.spread line₁ line₂ line₁_nonNull line₂_nonNull = 3 := by
  exact ⟨by decide, by decide, by decide⟩

open Purelib.Geometry.Plane.Line in
open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Triangles.Quadrea in
/-- The complete executable calculation in `F₁₁`. -/
theorem example_7_3 :
    line₁.Contains point₂ ∧ line₁.Contains point₃ ∧
      line₂.Contains point₁ ∧ line₂.Contains point₃ ∧
      line₃.Contains point₁ ∧ line₃.Contains point₂ ∧
      Quadrance.quadrance point₂ point₃ = 4 ∧
      Quadrance.quadrance point₁ point₃ = 3 ∧
      Quadrance.quadrance point₁ point₂ = 2 ∧
      Basic.quadrea point₁ point₂ point₃ = 1 ∧
      Spread.spread line₂ line₃ line₂_nonNull line₃_nonNull = 6 ∧
      Spread.spread line₁ line₃ line₁_nonNull line₃_nonNull = 10 ∧
      Spread.spread line₁ line₂ line₁_nonNull line₂_nonNull = 3 := by
  exact ⟨line_incidence.1, line_incidence.2.1, line_incidence.2.2.1,
    line_incidence.2.2.2.1, line_incidence.2.2.2.2.1,
    line_incidence.2.2.2.2.2, quadrance_values.1,
    quadrance_values.2.1, quadrance_values.2.2, quadrea_value,
    spread_values.1, spread_values.2.1, spread_values.2.2⟩

open Purelib.Geometry.Plane.Line in
/-- Both sides of the triple-spread identity evaluate to nine modulo eleven. -/
theorem triple_spread_value :
    let s₁ := Spread.spread line₂ line₃ line₂_nonNull line₃_nonNull
    let s₂ := Spread.spread line₁ line₃ line₁_nonNull line₃_nonNull
    let s₃ := Spread.spread line₁ line₂ line₁_nonNull line₂_nonNull
    (s₁ + s₂ + s₃) ^ 2 = 9 ∧
      2 * (s₁ ^ 2 + s₂ ^ 2 + s₃ ^ 2) + 4 * s₁ * s₂ * s₃ = 9 := by
  decide

end ExampleSevenThree

end ChapterSevenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterSeven

end
