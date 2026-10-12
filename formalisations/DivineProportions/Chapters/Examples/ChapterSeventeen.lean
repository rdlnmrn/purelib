module
import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Eleven
import Purelib.Geometry.Circles.Conic.Basic
public import Purelib.Geometry.Circles.SubtendedSpread
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance
public import Purelib.Geometry.Plane.Point.Quadrance.FourPoint
import Purelib.Geometry.Polygons.SignedArea.Basic
import Purelib.Geometry.Quadrilaterals.Basic
public import Purelib.Geometry.Quadrilaterals.Cyclic.Quadrea
import Purelib.Geometry.Trigonometry.QuadTriple.Basic
import Purelib.Geometry.Trigonometry.QuadTriple.Quadruple
import Purelib.Geometry.Trigonometry.Spread.Quadruple
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Data.Rat.Fraction.Compatibility

import Purelib.Geometry.Quadrilaterals.Cyclic.Circumquadrance.Polynomial
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Quadrilaterals.Cyclic.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Geometry.Plane

open Purelib.Geometry

section
@[expose] public section

/-!
# Divine Proportions, Chapter 17 worked examples

This module records the complete finite-field arithmetic printed in Examples
17.1, 17.2, and 17.4, together with the exact constructive-rational data of
Example 17.3.  All finite-field coordinates are literal elements of the
executable eleven-element field; no enumeration of all field elements or
roots is used.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterSeventeen

namespace ChapterSeventeenExamples

namespace ExampleSeventeenOne

/-- The origin of the coordinate plane over the field with eleven elements. -/
def origin : Purelib.Geometry.Plane.Point Finite.Eleven.Element := ⟨0, 0⟩

/-- The first vertex (2, 3) of the first quadrilateral over the field with eleven elements. -/
def a₁ : Purelib.Geometry.Plane.Point Finite.Eleven.Element := ⟨2, 3⟩
/-- The second vertex (9, 3) of the first quadrilateral over the field with eleven elements. -/
def a₂ : Purelib.Geometry.Plane.Point Finite.Eleven.Element := ⟨9, 3⟩
/-- The third vertex (1, 10) of the first quadrilateral over the field with eleven elements. -/
def a₃ : Purelib.Geometry.Plane.Point Finite.Eleven.Element := ⟨1, 10⟩
/-- The fourth vertex (8, 9) of the first quadrilateral over the field with eleven elements. -/
def a₄ : Purelib.Geometry.Plane.Point Finite.Eleven.Element := ⟨8, 9⟩

/-- The first vertex (4, 2) of the second quadrilateral over the field with eleven elements. -/
def b₁ : Purelib.Geometry.Plane.Point Finite.Eleven.Element := ⟨4, 2⟩
/-- The second vertex (3, 0) of the second quadrilateral over the field with eleven elements. -/
def b₂ : Purelib.Geometry.Plane.Point Finite.Eleven.Element := ⟨3, 0⟩
/-- The third vertex (8, 0) of the second quadrilateral over the field with eleven elements. -/
def b₃ : Purelib.Geometry.Plane.Point Finite.Eleven.Element := ⟨8, 0⟩
/-- The fourth vertex (9, 7) of the second quadrilateral over the field with eleven elements. -/
def b₄ : Purelib.Geometry.Plane.Point Finite.Eleven.Element := ⟨9, 7⟩

/-- A nonzero coordinate determinant excludes collinearity of the three supplied points. -/
private theorem notCollinear_of_determinant_ne_zero
    {first second third : Purelib.Geometry.Plane.Point Finite.Eleven.Element}
    (determinantNonzero : Line.Incidence.pointDeterminant first second third ≠ 0) :
    ¬ Line.Incidence.Collinear first second third := by
  intro collinear
  exact determinantNonzero
    ((Line.Incidence.collinear_iff_pointDeterminant_eq_zero first second third).1 collinear)

/-- The first displayed point list satisfies the book's quadrilateral
distinctness and noncollinearity conditions. -/
def aQuadrilateral : Quadrilaterals.Basic.Quadrilateral Finite.Eleven.Element where
  first := a₁
  second := a₂
  third := a₃
  fourth := a₄
  firstSecondDistinct := by unfold a₁ a₂; decide
  firstThirdDistinct := by unfold a₁ a₃; decide
  firstFourthDistinct := by unfold a₁ a₄; decide
  secondThirdDistinct := by unfold a₂ a₃; decide
  secondFourthDistinct := by unfold a₂ a₄; decide
  thirdFourthDistinct := by unfold a₃ a₄; decide
  firstSecondThirdNoncollinear := by
    intro collinear
    have determinantNonzero : Line.Incidence.pointDeterminant a₁ a₂ a₃ ≠ 0 := by
      unfold Line.Incidence.pointDeterminant a₁ a₂ a₃
      decide
    exact determinantNonzero
      ((Line.Incidence.collinear_iff_pointDeterminant_eq_zero a₁ a₂ a₃).1 collinear)
  firstSecondFourthNoncollinear := by
    intro collinear
    have determinantNonzero : Line.Incidence.pointDeterminant a₁ a₂ a₄ ≠ 0 := by
      unfold Line.Incidence.pointDeterminant a₁ a₂ a₄
      decide
    exact determinantNonzero
      ((Line.Incidence.collinear_iff_pointDeterminant_eq_zero a₁ a₂ a₄).1 collinear)
  firstThirdFourthNoncollinear := by
    intro collinear
    have determinantNonzero : Line.Incidence.pointDeterminant a₁ a₃ a₄ ≠ 0 := by
      unfold Line.Incidence.pointDeterminant a₁ a₃ a₄
      decide
    exact determinantNonzero
      ((Line.Incidence.collinear_iff_pointDeterminant_eq_zero a₁ a₃ a₄).1 collinear)
  secondThirdFourthNoncollinear := by
    intro collinear
    have determinantNonzero : Line.Incidence.pointDeterminant a₂ a₃ a₄ ≠ 0 := by
      unfold Line.Incidence.pointDeterminant a₂ a₃ a₄
      decide
    exact determinantNonzero
      ((Line.Incidence.collinear_iff_pointDeterminant_eq_zero a₂ a₃ a₄).1 collinear)

/-- The second displayed point list is also a genuine quadrilateral. -/
def bQuadrilateral : Quadrilaterals.Basic.Quadrilateral Finite.Eleven.Element where
  first := b₁
  second := b₂
  third := b₃
  fourth := b₄
  firstSecondDistinct := by unfold b₁ b₂; decide
  firstThirdDistinct := by unfold b₁ b₃; decide
  firstFourthDistinct := by unfold b₁ b₄; decide
  secondThirdDistinct := by unfold b₂ b₃; decide
  secondFourthDistinct := by unfold b₂ b₄; decide
  thirdFourthDistinct := by unfold b₃ b₄; decide
  firstSecondThirdNoncollinear := by
    intro collinear
    have determinantNonzero : Line.Incidence.pointDeterminant b₁ b₂ b₃ ≠ 0 := by
      unfold Line.Incidence.pointDeterminant b₁ b₂ b₃
      decide
    exact determinantNonzero
      ((Line.Incidence.collinear_iff_pointDeterminant_eq_zero b₁ b₂ b₃).1 collinear)
  firstSecondFourthNoncollinear := by
    intro collinear
    have determinantNonzero : Line.Incidence.pointDeterminant b₁ b₂ b₄ ≠ 0 := by
      unfold Line.Incidence.pointDeterminant b₁ b₂ b₄
      decide
    exact determinantNonzero
      ((Line.Incidence.collinear_iff_pointDeterminant_eq_zero b₁ b₂ b₄).1 collinear)
  firstThirdFourthNoncollinear := by
    intro collinear
    have determinantNonzero : Line.Incidence.pointDeterminant b₁ b₃ b₄ ≠ 0 := by
      unfold Line.Incidence.pointDeterminant b₁ b₃ b₄
      decide
    exact determinantNonzero
      ((Line.Incidence.collinear_iff_pointDeterminant_eq_zero b₁ b₃ b₄).1 collinear)
  secondThirdFourthNoncollinear := by
    intro collinear
    have determinantNonzero : Line.Incidence.pointDeterminant b₂ b₃ b₄ ≠ 0 := by
      unfold Line.Incidence.pointDeterminant b₂ b₃ b₄
      decide
    exact determinantNonzero
      ((Line.Incidence.collinear_iff_pointDeterminant_eq_zero b₂ b₃ b₄).1 collinear)

/-- The first displayed side line `⟨0:7:1⟩`. -/
def line₁₂ : Purelib.Geometry.Plane.Line Finite.Eleven.Element where
  a := 0
  b := 7
  c := 1
  direction_nonzero := Or.inr (by decide)

/-- The second displayed side line `⟨7:8:1⟩`. -/
def line₂₃ : Purelib.Geometry.Plane.Line Finite.Eleven.Element where
  a := 7
  b := 8
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The third displayed side line `⟨2:3:1⟩`. -/
def line₃₄ : Purelib.Geometry.Plane.Line Finite.Eleven.Element where
  a := 2
  b := 3
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The fourth displayed side line `⟨1:10:1⟩`. -/
def line₁₄ : Purelib.Geometry.Plane.Line Finite.Eleven.Element where
  a := 1
  b := 10
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The displayed diagonal `⟨8:9:1⟩`. -/
def line₁₃ : Purelib.Geometry.Plane.Line Finite.Eleven.Element where
  a := 8
  b := 9
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The displayed diagonal `⟨8:5:1⟩`. -/
def line₂₄ : Purelib.Geometry.Plane.Line Finite.Eleven.Element where
  a := 8
  b := 5
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The line through the first two vertices has nonzero norm. -/
theorem line₁₂_nonNull : ¬ line₁₂.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₁₂
  decide

/-- The line through the second and third vertices has nonzero norm. -/
theorem line₂₃_nonNull : ¬ line₂₃.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₂₃
  decide

/-- The line through the third and fourth vertices has nonzero norm. -/
theorem line₃₄_nonNull : ¬ line₃₄.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₃₄
  decide

/-- The line through the first and fourth vertices has nonzero norm. -/
theorem line₁₄_nonNull : ¬ line₁₄.IsNull := by
  unfold Purelib.Geometry.Plane.Line.IsNull line₁₄
  decide

/-- The four prescribed side quadrances, shared by both displayed
quadrilaterals. -/
theorem side_quadrances :
    Point.Quadrance.quadrance a₁ a₂ = 5 ∧ Point.Quadrance.quadrance a₂ a₃ = 3 ∧
      Point.Quadrance.quadrance a₃ a₄ = 6 ∧ Point.Quadrance.quadrance a₁ a₄ = 6 ∧
      Point.Quadrance.quadrance b₁ b₂ = 5 ∧ Point.Quadrance.quadrance b₂ b₃ = 3 ∧
      Point.Quadrance.quadrance b₃ b₄ = 6 ∧ Point.Quadrance.quadrance b₁ b₄ = 6 := by
  unfold Point.Quadrance.quadrance a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
  decide

/-- The printed coefficient values `p=3`, `q=0`, and `r=10`. -/
theorem coefficient_values :
    Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP
        (5 : Finite.Eleven.Element) 3 6 6 = 3 ∧
      Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientQ
        (5 : Finite.Eleven.Element) 3 6 6 = 0 ∧
      Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientR
        (5 : Finite.Eleven.Element) 3 6 6 = 10 := by
  unfold Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP
    Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientQ
    Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientR
      Trigonometry.QuadTriple.Quadruple.quadrupleQuadFunction
  decide

/-- Both circumquadrances printed by the source satisfy `3*K²+10=0`. -/
theorem circumquadrance_solutions :
    (3 : Finite.Eleven.Element) * 2 ^ 2 + 10 = 0 ∧
      (3 : Finite.Eleven.Element) * 9 ^ 2 + 10 = 0 := by
  decide

/-- The first four points lie on the central circle of quadrance `2`, and the
second four lie on the central circle of quadrance `9`. -/
theorem central_circle_quadrances :
    Point.Quadrance.quadrance a₁ origin = 2 ∧ Point.Quadrance.quadrance a₂ origin = 2 ∧
      Point.Quadrance.quadrance a₃ origin = 2 ∧ Point.Quadrance.quadrance a₄ origin = 2 ∧
      Point.Quadrance.quadrance b₁ origin = 9 ∧ Point.Quadrance.quadrance b₂ origin = 9 ∧
      Point.Quadrance.quadrance b₃ origin = 9 ∧ Point.Quadrance.quadrance b₄ origin = 9 := by
  unfold Point.Quadrance.quadrance origin a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
  decide

/-- Both displayed quadrilaterals carry the central-circle witnesses claimed
by the source. -/
theorem displayed_quadrilaterals_are_cyclic :
    aQuadrilateral.IsCyclic ∧ bQuadrilateral.IsCyclic := open Purelib in by
  have radii := central_circle_quadrances
  constructor
  · let circle := Curves.Plane.Conic.circleConic origin (2 : Finite.Eleven.Element)
    have presentation :=
      Curves.Plane.Conic.circleConic_isCirclePresentation origin (2 : Finite.Eleven.Element)
    refine ⟨circle, origin, 2, presentation, ?_, ?_, ?_, ?_⟩
    · exact (Curves.Plane.Conic.contains_iff_quadrance_eq circle origin a₁ 2
        presentation).2 radii.1
    · exact (Curves.Plane.Conic.contains_iff_quadrance_eq circle origin a₂ 2
        presentation).2 radii.2.1
    · exact (Curves.Plane.Conic.contains_iff_quadrance_eq circle origin a₃ 2
        presentation).2 radii.2.2.1
    · exact (Curves.Plane.Conic.contains_iff_quadrance_eq circle origin a₄ 2
        presentation).2 radii.2.2.2.1
  · let circle := Curves.Plane.Conic.circleConic origin (9 : Finite.Eleven.Element)
    have presentation :=
      Curves.Plane.Conic.circleConic_isCirclePresentation origin (9 : Finite.Eleven.Element)
    refine ⟨circle, origin, 9, presentation, ?_, ?_, ?_, ?_⟩
    · exact (Curves.Plane.Conic.contains_iff_quadrance_eq circle origin b₁ 9
        presentation).2 radii.2.2.2.2.1
    · exact (Curves.Plane.Conic.contains_iff_quadrance_eq circle origin b₂ 9
        presentation).2 radii.2.2.2.2.2.1
    · exact (Curves.Plane.Conic.contains_iff_quadrance_eq circle origin b₃ 9
        presentation).2 radii.2.2.2.2.2.2.1
    · exact (Curves.Plane.Conic.contains_iff_quadrance_eq circle origin b₄ 9
        presentation).2 radii.2.2.2.2.2.2.2

/-- Each of the six displayed coefficient triples contains its two named
vertices. -/
theorem displayed_line_incidences :
    line₁₂.Contains a₁ ∧ line₁₂.Contains a₂ ∧
      line₂₃.Contains a₂ ∧ line₂₃.Contains a₃ ∧
      line₃₄.Contains a₃ ∧ line₃₄.Contains a₄ ∧
      line₁₄.Contains a₁ ∧ line₁₄.Contains a₄ ∧
      line₁₃.Contains a₁ ∧ line₁₃.Contains a₃ ∧
      line₂₄.Contains a₂ ∧ line₂₄.Contains a₄ := by
  unfold Line.Contains line₁₂ line₂₃ line₃₄ line₁₄ line₁₃ line₂₄
    a₁ a₂ a₃ a₄
  decide

/-- The four ordinary vertex spreads are `6,9,6,9`. -/
theorem vertex_spreads :
    Line.Spread.spread line₁₂ line₁₄ line₁₂_nonNull line₁₄_nonNull = 6 ∧
      Line.Spread.spread line₁₂ line₂₃ line₁₂_nonNull line₂₃_nonNull = 9 ∧
      Line.Spread.spread line₂₃ line₃₄ line₂₃_nonNull line₃₄_nonNull = 6 ∧
      Line.Spread.spread line₃₄ line₁₄ line₃₄_nonNull line₁₄_nonNull = 9 := by
  unfold Line.Spread.spread Line.Basic.lineNorm line₁₂ line₂₃ line₃₄ line₁₄
  decide

/-- The six subtended spreads printed for the first quadrilateral. -/
theorem subtended_spreads :
    Quadrilaterals.Basic.Quadrilateral.normalizedSubtendedSpread 2 a₁ a₂ = 2 ∧
      Quadrilaterals.Basic.Quadrilateral.normalizedSubtendedSpread 2 a₂ a₃ = 10 ∧
      Quadrilaterals.Basic.Quadrilateral.normalizedSubtendedSpread 2 a₃ a₄ = 9 ∧
      Quadrilaterals.Basic.Quadrilateral.normalizedSubtendedSpread 2 a₁ a₄ = 9 ∧
      Quadrilaterals.Basic.Quadrilateral.normalizedSubtendedSpread 2 a₁ a₃ = 9 ∧
      Quadrilaterals.Basic.Quadrilateral.normalizedSubtendedSpread 2 a₂ a₄ = 6 := by
  unfold Quadrilaterals.Basic.Quadrilateral.normalizedSubtendedSpread Point.Quadrance.quadrance
    a₁ a₂ a₃ a₄
  decide

/-- The four subtended side spreads satisfy `R=0`, and the two diagonal
values are recovered by Theorem 110's displayed quotients. -/
theorem subtended_spread_formulas :
    Trigonometry.Spread.Quadruple.quadrupleSpreadFunction (2 : Finite.Eleven.Element) 10 9 9 = 0 ∧
      (9 : Finite.Eleven.Element) =
        ((2 - 10) ^ 2 - (9 - 9) ^ 2) /
          (2 * (2 + 10 - 9 - 9 - 2 * 2 * 10 + 2 * 9 * 9)) ∧
      (6 : Finite.Eleven.Element) =
        ((2 - 9) ^ 2 - (10 - 9) ^ 2) /
          (2 * (2 + 9 - 10 - 9 - 2 * 2 * 9 + 2 * 10 * 9)) := by
  unfold Trigonometry.Spread.Quadruple.quadrupleSpreadFunction Trigonometry.Spread.Quadruple.quadrupleSpreadCore
  decide

/-- The two polygon quadreas printed at the end of Example 17.1. -/
theorem polygon_quadreas :
    Polygons.SignedArea.Basic.polygonQuadrea [a₁, a₂, a₃, a₄] = 4 ∧
      Polygons.SignedArea.Basic.polygonQuadrea [b₁, b₂, b₃, b₄] = 9 := by
  unfold Polygons.SignedArea.Basic.polygonQuadrea Polygons.SignedArea.Basic.polygonDoubleSignedArea a₁ a₂ a₃ a₄ b₁ b₂ b₃
    b₄
  decide

/-- Example 17.2: `m=1`, `p=3`, and the two displayed quadreas `4` and `9`
are the roots of `A²-2A+3`. -/
theorem example_17_2 :
    Quadrilaterals.Basic.Quadrilateral.cyclicQuadreaCoefficientM
        (5 : Finite.Eleven.Element) 3 6 6 = 1 ∧
      Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP
        (5 : Finite.Eleven.Element) 3 6 6 = 3 ∧
      (4 : Finite.Eleven.Element) ^ 2 - 2 * 1 * 4 + 3 = 0 ∧
      (9 : Finite.Eleven.Element) ^ 2 - 2 * 1 * 9 + 3 = 0 ∧
      ((4 : Finite.Eleven.Element) + 9) / 2 = 1 ∧
      (4 : Finite.Eleven.Element) * 9 = 3 := by
  unfold Quadrilaterals.Basic.Quadrilateral.cyclicQuadreaCoefficientM
    Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP
      Trigonometry.QuadTriple.Quadruple.quadrupleQuadFunction
  decide

/-- Example 17.4: the three products reduce to `7,2,10` in `F₁₁`; they
form the quad triple asserted by Ptolemy's theorem, and the displayed
centered-square check has both sides equal to one. -/
theorem example_17_4 :
    (2 : Finite.Eleven.Element) * 9 = 7 ∧
      (9 : Finite.Eleven.Element) * 10 = 2 ∧
      (9 : Finite.Eleven.Element) * 6 = 10 ∧
      Trigonometry.QuadTriple ((2 : Finite.Eleven.Element) * 9) ((9 : Finite.Eleven.Element) * 10)
        ((9 : Finite.Eleven.Element) * 6) ∧
      ((7 : Finite.Eleven.Element) + 2 - 10) ^ 2 = 1 ∧
      4 * (7 : Finite.Eleven.Element) * 2 = 1 := by
  unfold Trigonometry.QuadTriple Trigonometry.QuadTriple.Basic.archimedesFunction
  decide

/-- The printed form of Exercise 17.5 is false even though the Four point
relation holds: taking `Q₁=Q₂=Q₃=P₁=P₂=1` and `P₃=0` gives an
executable counterexample in `F₁₁`. -/
theorem exercise_17_5_printed_counterexample :
    Quadrilaterals.Basic.Quadrilateral.eulerFunction
        (1 : Finite.Eleven.Element) 1 1 1 1 0 = 0 ∧
      (0 - 1 - 1 + 1 - 1 - 1 +
          ((1 - 1) * (1 - 1) / 1 : Finite.Eleven.Element)) ^ 2 ≠
        Trigonometry.QuadTriple.Basic.archimedesFunction (1 : Finite.Eleven.Element) 1 1 *
          Trigonometry.QuadTriple.Basic.archimedesFunction (1 : Finite.Eleven.Element) 1 1 / (4 * (1 :
            Finite.Eleven.Element) ^ 2) := by
  unfold Quadrilaterals.Basic.Quadrilateral.eulerFunction Quadrilaterals.Basic.Quadrilateral.determinantThree
    Trigonometry.QuadTriple.Basic.archimedesFunction
  decide

end ExampleSeventeenOne

namespace ExampleSeventeenThree

/-- The exact quadrances associated with side lengths `5,8,2,10`. -/
theorem side_quadrances :
    (5 : Fraction.Rational) ^ 2 = 25 ∧ (8 : Fraction.Rational) ^ 2 = 64 ∧
      (2 : Fraction.Rational) ^ 2 = 4 ∧ (10 : Fraction.Rational) ^ 2 = 100 := by
  exact ⟨by ring1, by ring1, by ring1, by ring1⟩

/-- The four coefficient values printed in Example 17.3. -/
theorem coefficient_values :
    Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP
        (25 : Fraction.Rational) 64 4 100 = 19490625 ∧
      Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientQ
        (25 : Fraction.Rational) 64 4 100 = 582390000 ∧
      Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientR
        (25 : Fraction.Rational) 64 4 100 = 16964640000 ∧
      Quadrilaterals.Basic.Quadrilateral.cyclicQuadreaCoefficientM
        (25 : Fraction.Rational) 64 4 100 = 7775 := by
  unfold Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientP
    Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientQ
    Quadrilaterals.Cyclic.Circumquadrance.Polynomial.Quadrilateral.circumquadranceCoefficientR
    Quadrilaterals.Basic.Quadrilateral.cyclicQuadreaCoefficientM Trigonometry.QuadTriple.Quadruple.quadrupleQuadFunction
  exact ⟨by ring1, by ring1, by ring1, by ring1⟩

/-- The exact factorization of the circumquadrance equation. -/
theorem circumquadrance_factorization (circleQuadrance : Fraction.Rational) :
    19490625 * circleQuadrance ^ 2 -
        1164780000 * circleQuadrance + 16964640000 =
      50625 * (7 * circleQuadrance - 176) *
        (55 * circleQuadrance - 1904) := by
  ring1

/-- The two exact rational circumquadrances printed by the source. -/
theorem circumquadrance_values :
    19490625 * ((176 : Fraction.Rational) / 7) ^ 2 -
          1164780000 * ((176 : Fraction.Rational) / 7) + 16964640000 = 0 ∧
      19490625 * ((1904 : Fraction.Rational) / 55) ^ 2 -
          1164780000 * ((1904 : Fraction.Rational) / 55) + 16964640000 = 0 := by
  constructor
  · rw [circumquadrance_factorization]
    have cancel : ((176 : Fraction.Rational) / 7) * 7 = 176 :=
      ExplicitField.div_mul_cancel _
        (Fraction.Order.Cast.rational_natCast_nonzero (by decide : 7 ≠ 0))
    have factorZero : (7 : Fraction.Rational) * ((176 : Fraction.Rational) / 7) - 176 = 0 := by
      calc
        (7 : Fraction.Rational) * ((176 : Fraction.Rational) / 7) - 176 =
            ((176 : Fraction.Rational) / 7) * 7 - 176 := by ring1
        _ = 0 := by rw [cancel]; ring1
    rw [factorZero]
    ring1
  · rw [circumquadrance_factorization]
    have cancel : ((1904 : Fraction.Rational) / 55) * 55 = 1904 :=
      ExplicitField.div_mul_cancel _
        (Fraction.Order.Cast.rational_natCast_nonzero (by decide : 55 ≠ 0))
    have factorZero :
        (55 : Fraction.Rational) * ((1904 : Fraction.Rational) / 55) - 1904 = 0 := by
      calc
        (55 : Fraction.Rational) * ((1904 : Fraction.Rational) / 55) - 1904 =
            ((1904 : Fraction.Rational) / 55) * 55 - 1904 := by ring1
        _ = 0 := by rw [cancel]; ring1
    rw [factorZero]
    ring1

/-- The exact factorization of the quadrea equation. -/
theorem quadrea_factorization (area : Fraction.Rational) :
    area ^ 2 - 15550 * area + 19490625 =
      (area - 14175) * (area - 1375) := by
  ring1

/-- The two exact quadreas are roots; their displayed approximate square
roots are deliberately not introduced as completed real numbers. -/
theorem quadrea_values :
    (14175 : Fraction.Rational) ^ 2 - 15550 * 14175 + 19490625 = 0 ∧
      (1375 : Fraction.Rational) ^ 2 - 15550 * 1375 + 19490625 = 0 := by
  exact ⟨by ring1, by ring1⟩

end ExampleSeventeenThree

end ChapterSeventeenExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterSeventeen

end
