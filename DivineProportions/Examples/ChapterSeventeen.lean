import DivineProportions.Quadrilaterals.CyclicQuadrea
import DivineProportions.Quadrilaterals.FourPoint
import DivineProportions.Quadrilaterals.Ptolemy
import DivineProportions.Oriented.SignedArea
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 17 worked examples

This module records the complete finite-field arithmetic printed in Examples
17.1, 17.2, and 17.4, together with the exact constructive-rational data of
Example 17.3.  All finite-field coordinates are literal elements of the
executable eleven-element field; no enumeration of all field elements or
roots is used.
-/

namespace DivineProportions

namespace ChapterSeventeenExamples

namespace ExampleSeventeenOne

abbrev F₁₁ := FieldEleven.Element

def origin : Point F₁₁ := ⟨0, 0⟩

def a₁ : Point F₁₁ := ⟨2, 3⟩
def a₂ : Point F₁₁ := ⟨9, 3⟩
def a₃ : Point F₁₁ := ⟨1, 10⟩
def a₄ : Point F₁₁ := ⟨8, 9⟩

def b₁ : Point F₁₁ := ⟨4, 2⟩
def b₂ : Point F₁₁ := ⟨3, 0⟩
def b₃ : Point F₁₁ := ⟨8, 0⟩
def b₄ : Point F₁₁ := ⟨9, 7⟩

private theorem notCollinear_of_determinant_ne_zero
    {first second third : Point F₁₁}
    (determinantNonzero : pointDeterminant first second third ≠ 0) :
    ¬ Collinear first second third := by
  intro collinear
  exact determinantNonzero
    ((collinear_iff_pointDeterminant_eq_zero first second third).1 collinear)

/-- The first displayed point list satisfies the book's quadrilateral
distinctness and noncollinearity conditions. -/
def aQuadrilateral : Quadrilateral F₁₁ where
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
  firstSecondThirdNoncollinear := notCollinear_of_determinant_ne_zero (by
    unfold pointDeterminant a₁ a₂ a₃
    decide)
  firstSecondFourthNoncollinear := notCollinear_of_determinant_ne_zero (by
    unfold pointDeterminant a₁ a₂ a₄
    decide)
  firstThirdFourthNoncollinear := notCollinear_of_determinant_ne_zero (by
    unfold pointDeterminant a₁ a₃ a₄
    decide)
  secondThirdFourthNoncollinear := notCollinear_of_determinant_ne_zero (by
    unfold pointDeterminant a₂ a₃ a₄
    decide)

/-- The second displayed point list is also a genuine quadrilateral. -/
def bQuadrilateral : Quadrilateral F₁₁ where
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
  firstSecondThirdNoncollinear := notCollinear_of_determinant_ne_zero (by
    unfold pointDeterminant b₁ b₂ b₃
    decide)
  firstSecondFourthNoncollinear := notCollinear_of_determinant_ne_zero (by
    unfold pointDeterminant b₁ b₂ b₄
    decide)
  firstThirdFourthNoncollinear := notCollinear_of_determinant_ne_zero (by
    unfold pointDeterminant b₁ b₃ b₄
    decide)
  secondThirdFourthNoncollinear := notCollinear_of_determinant_ne_zero (by
    unfold pointDeterminant b₂ b₃ b₄
    decide)

/-- The first displayed side line `⟨0:7:1⟩`. -/
def line₁₂ : Line F₁₁ where
  a := 0
  b := 7
  c := 1
  direction_nonzero := Or.inr (by decide)

/-- The second displayed side line `⟨7:8:1⟩`. -/
def line₂₃ : Line F₁₁ where
  a := 7
  b := 8
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The third displayed side line `⟨2:3:1⟩`. -/
def line₃₄ : Line F₁₁ where
  a := 2
  b := 3
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The fourth displayed side line `⟨1:10:1⟩`. -/
def line₁₄ : Line F₁₁ where
  a := 1
  b := 10
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The displayed diagonal `⟨8:9:1⟩`. -/
def line₁₃ : Line F₁₁ where
  a := 8
  b := 9
  c := 1
  direction_nonzero := Or.inl (by decide)

/-- The displayed diagonal `⟨8:5:1⟩`. -/
def line₂₄ : Line F₁₁ where
  a := 8
  b := 5
  c := 1
  direction_nonzero := Or.inl (by decide)

theorem line₁₂_nonNull : ¬ line₁₂.IsNull := by
  unfold Line.IsNull line₁₂
  decide

theorem line₂₃_nonNull : ¬ line₂₃.IsNull := by
  unfold Line.IsNull line₂₃
  decide

theorem line₃₄_nonNull : ¬ line₃₄.IsNull := by
  unfold Line.IsNull line₃₄
  decide

theorem line₁₄_nonNull : ¬ line₁₄.IsNull := by
  unfold Line.IsNull line₁₄
  decide

/-- The four prescribed side quadrances, shared by both displayed
quadrilaterals. -/
theorem side_quadrances :
    quadrance a₁ a₂ = 5 ∧ quadrance a₂ a₃ = 3 ∧
      quadrance a₃ a₄ = 6 ∧ quadrance a₁ a₄ = 6 ∧
      quadrance b₁ b₂ = 5 ∧ quadrance b₂ b₃ = 3 ∧
      quadrance b₃ b₄ = 6 ∧ quadrance b₁ b₄ = 6 := by
  unfold quadrance a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
  decide

/-- The printed coefficient values `p=3`, `q=0`, and `r=10`. -/
theorem coefficient_values :
    Quadrilateral.circumquadranceCoefficientP
        (5 : F₁₁) 3 6 6 = 3 ∧
      Quadrilateral.circumquadranceCoefficientQ
        (5 : F₁₁) 3 6 6 = 0 ∧
      Quadrilateral.circumquadranceCoefficientR
        (5 : F₁₁) 3 6 6 = 10 := by
  unfold Quadrilateral.circumquadranceCoefficientP
    Quadrilateral.circumquadranceCoefficientQ
    Quadrilateral.circumquadranceCoefficientR quadrupleQuadFunction
  decide

/-- Both circumquadrances printed by the source satisfy `3*K²+10=0`. -/
theorem circumquadrance_solutions :
    (3 : F₁₁) * 2 ^ 2 + 10 = 0 ∧
      (3 : F₁₁) * 9 ^ 2 + 10 = 0 := by
  decide

/-- The first four points lie on the central circle of quadrance `2`, and the
second four lie on the central circle of quadrance `9`. -/
theorem central_circle_quadrances :
    quadrance a₁ origin = 2 ∧ quadrance a₂ origin = 2 ∧
      quadrance a₃ origin = 2 ∧ quadrance a₄ origin = 2 ∧
      quadrance b₁ origin = 9 ∧ quadrance b₂ origin = 9 ∧
      quadrance b₃ origin = 9 ∧ quadrance b₄ origin = 9 := by
  unfold quadrance origin a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
  decide

/-- Both displayed quadrilaterals carry the central-circle witnesses claimed
by the source. -/
theorem displayed_quadrilaterals_are_cyclic :
    aQuadrilateral.IsCyclic ∧ bQuadrilateral.IsCyclic := by
  have radii := central_circle_quadrances
  constructor
  · let circle := Conic.circleConic origin (2 : F₁₁)
    have presentation :=
      Conic.circleConic_isCirclePresentation origin (2 : F₁₁)
    refine ⟨circle, origin, 2, presentation, ?_, ?_, ?_, ?_⟩
    · exact (Conic.contains_iff_quadrance_eq circle origin a₁ 2
        presentation).2 radii.1
    · exact (Conic.contains_iff_quadrance_eq circle origin a₂ 2
        presentation).2 radii.2.1
    · exact (Conic.contains_iff_quadrance_eq circle origin a₃ 2
        presentation).2 radii.2.2.1
    · exact (Conic.contains_iff_quadrance_eq circle origin a₄ 2
        presentation).2 radii.2.2.2.1
  · let circle := Conic.circleConic origin (9 : F₁₁)
    have presentation :=
      Conic.circleConic_isCirclePresentation origin (9 : F₁₁)
    refine ⟨circle, origin, 9, presentation, ?_, ?_, ?_, ?_⟩
    · exact (Conic.contains_iff_quadrance_eq circle origin b₁ 9
        presentation).2 radii.2.2.2.2.1
    · exact (Conic.contains_iff_quadrance_eq circle origin b₂ 9
        presentation).2 radii.2.2.2.2.2.1
    · exact (Conic.contains_iff_quadrance_eq circle origin b₃ 9
        presentation).2 radii.2.2.2.2.2.2.1
    · exact (Conic.contains_iff_quadrance_eq circle origin b₄ 9
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
    spread line₁₂ line₁₄ line₁₂_nonNull line₁₄_nonNull = 6 ∧
      spread line₁₂ line₂₃ line₁₂_nonNull line₂₃_nonNull = 9 ∧
      spread line₂₃ line₃₄ line₂₃_nonNull line₃₄_nonNull = 6 ∧
      spread line₃₄ line₁₄ line₃₄_nonNull line₁₄_nonNull = 9 := by
  unfold spread lineNorm line₁₂ line₂₃ line₃₄ line₁₄
  decide

/-- The six subtended spreads printed for the first quadrilateral. -/
theorem subtended_spreads :
    Quadrilateral.normalizedSubtendedSpread 2 a₁ a₂ = 2 ∧
      Quadrilateral.normalizedSubtendedSpread 2 a₂ a₃ = 10 ∧
      Quadrilateral.normalizedSubtendedSpread 2 a₃ a₄ = 9 ∧
      Quadrilateral.normalizedSubtendedSpread 2 a₁ a₄ = 9 ∧
      Quadrilateral.normalizedSubtendedSpread 2 a₁ a₃ = 9 ∧
      Quadrilateral.normalizedSubtendedSpread 2 a₂ a₄ = 6 := by
  unfold Quadrilateral.normalizedSubtendedSpread quadrance
    a₁ a₂ a₃ a₄
  decide

/-- The four subtended side spreads satisfy `R=0`, and the two diagonal
values are recovered by Theorem 110's displayed quotients. -/
theorem subtended_spread_formulas :
    quadrupleSpreadFunction (2 : F₁₁) 10 9 9 = 0 ∧
      (9 : F₁₁) =
        ((2 - 10) ^ 2 - (9 - 9) ^ 2) /
          (2 * (2 + 10 - 9 - 9 - 2 * 2 * 10 + 2 * 9 * 9)) ∧
      (6 : F₁₁) =
        ((2 - 9) ^ 2 - (10 - 9) ^ 2) /
          (2 * (2 + 9 - 10 - 9 - 2 * 2 * 9 + 2 * 10 * 9)) := by
  unfold quadrupleSpreadFunction quadrupleSpreadCore
  decide

/-- The two polygon quadreas printed at the end of Example 17.1. -/
theorem polygon_quadreas :
    polygonQuadrea [a₁, a₂, a₃, a₄] = 4 ∧
      polygonQuadrea [b₁, b₂, b₃, b₄] = 9 := by
  unfold polygonQuadrea polygonDoubleSignedArea a₁ a₂ a₃ a₄ b₁ b₂ b₃ b₄
  decide

/-- Example 17.2: `m=1`, `p=3`, and the two displayed quadreas `4` and `9`
are the roots of `A²-2A+3`. -/
theorem example_17_2 :
    Quadrilateral.cyclicQuadreaCoefficientM
        (5 : F₁₁) 3 6 6 = 1 ∧
      Quadrilateral.circumquadranceCoefficientP
        (5 : F₁₁) 3 6 6 = 3 ∧
      (4 : F₁₁) ^ 2 - 2 * 1 * 4 + 3 = 0 ∧
      (9 : F₁₁) ^ 2 - 2 * 1 * 9 + 3 = 0 ∧
      ((4 : F₁₁) + 9) / 2 = 1 ∧
      (4 : F₁₁) * 9 = 3 := by
  unfold Quadrilateral.cyclicQuadreaCoefficientM
    Quadrilateral.circumquadranceCoefficientP quadrupleQuadFunction
  decide

/-- Example 17.4: the three products reduce to `7,2,10` in `F₁₁`; they
form the quad triple asserted by Ptolemy's theorem, and the displayed
centered-square check has both sides equal to one. -/
theorem example_17_4 :
    (2 : F₁₁) * 9 = 7 ∧
      (9 : F₁₁) * 10 = 2 ∧
      (9 : F₁₁) * 6 = 10 ∧
      QuadTriple ((2 : F₁₁) * 9) ((9 : F₁₁) * 10)
        ((9 : F₁₁) * 6) ∧
      ((7 : F₁₁) + 2 - 10) ^ 2 = 1 ∧
      4 * (7 : F₁₁) * 2 = 1 := by
  unfold QuadTriple archimedesFunction
  decide

/-- The printed form of Exercise 17.5 is false even though the Four point
relation holds: taking `Q₁=Q₂=Q₃=P₁=P₂=1` and `P₃=0` gives an
executable counterexample in `F₁₁`. -/
theorem exercise_17_5_printed_counterexample :
    Quadrilateral.eulerFunction
        (1 : F₁₁) 1 1 1 1 0 = 0 ∧
      (0 - 1 - 1 + 1 - 1 - 1 +
          ((1 - 1) * (1 - 1) / 1 : F₁₁)) ^ 2 ≠
        archimedesFunction (1 : F₁₁) 1 1 *
          archimedesFunction (1 : F₁₁) 1 1 / (4 * (1 : F₁₁) ^ 2) := by
  unfold Quadrilateral.eulerFunction Quadrilateral.determinantThree
    archimedesFunction
  decide

end ExampleSeventeenOne

namespace ExampleSeventeenThree

abbrev Rational := RFAP.ConstructiveFraction.Rational

private theorem rational_natCast_nonzero {value : Nat}
    (valueNonzero : value ≠ 0) : (value : Rational) ≠ 0 := by
  intro castZero
  exact valueNonzero
    (RFAP.ConstructiveFraction.natCast_injective_direct castZero)

/-- The exact quadrances associated with side lengths `5,8,2,10`. -/
theorem side_quadrances :
    (5 : Rational) ^ 2 = 25 ∧ (8 : Rational) ^ 2 = 64 ∧
      (2 : Rational) ^ 2 = 4 ∧ (10 : Rational) ^ 2 = 100 := by
  exact ⟨by ring1, by ring1, by ring1, by ring1⟩

/-- The four coefficient values printed in Example 17.3. -/
theorem coefficient_values :
    Quadrilateral.circumquadranceCoefficientP
        (25 : Rational) 64 4 100 = 19490625 ∧
      Quadrilateral.circumquadranceCoefficientQ
        (25 : Rational) 64 4 100 = 582390000 ∧
      Quadrilateral.circumquadranceCoefficientR
        (25 : Rational) 64 4 100 = 16964640000 ∧
      Quadrilateral.cyclicQuadreaCoefficientM
        (25 : Rational) 64 4 100 = 7775 := by
  unfold Quadrilateral.circumquadranceCoefficientP
    Quadrilateral.circumquadranceCoefficientQ
    Quadrilateral.circumquadranceCoefficientR
    Quadrilateral.cyclicQuadreaCoefficientM quadrupleQuadFunction
  exact ⟨by ring1, by ring1, by ring1, by ring1⟩

/-- The exact factorization of the circumquadrance equation. -/
theorem circumquadrance_factorization (circleQuadrance : Rational) :
    19490625 * circleQuadrance ^ 2 -
        1164780000 * circleQuadrance + 16964640000 =
      50625 * (7 * circleQuadrance - 176) *
        (55 * circleQuadrance - 1904) := by
  ring1

/-- The two exact rational circumquadrances printed by the source. -/
theorem circumquadrance_values :
    19490625 * ((176 : Rational) / 7) ^ 2 -
          1164780000 * ((176 : Rational) / 7) + 16964640000 = 0 ∧
      19490625 * ((1904 : Rational) / 55) ^ 2 -
          1164780000 * ((1904 : Rational) / 55) + 16964640000 = 0 := by
  constructor
  · rw [circumquadrance_factorization]
    have cancel : ((176 : Rational) / 7) * 7 = 176 :=
      RFAP.ExplicitField.div_mul_cancel _
        (rational_natCast_nonzero (by decide : 7 ≠ 0))
    have factorZero : (7 : Rational) * ((176 : Rational) / 7) - 176 = 0 := by
      calc
        (7 : Rational) * ((176 : Rational) / 7) - 176 =
            ((176 : Rational) / 7) * 7 - 176 := by ring1
        _ = 0 := by rw [cancel]; ring1
    rw [factorZero]
    ring1
  · rw [circumquadrance_factorization]
    have cancel : ((1904 : Rational) / 55) * 55 = 1904 :=
      RFAP.ExplicitField.div_mul_cancel _
        (rational_natCast_nonzero (by decide : 55 ≠ 0))
    have factorZero :
        (55 : Rational) * ((1904 : Rational) / 55) - 1904 = 0 := by
      calc
        (55 : Rational) * ((1904 : Rational) / 55) - 1904 =
            ((1904 : Rational) / 55) * 55 - 1904 := by ring1
        _ = 0 := by rw [cancel]; ring1
    rw [factorZero]
    ring1

/-- The exact factorization of the quadrea equation. -/
theorem quadrea_factorization (area : Rational) :
    area ^ 2 - 15550 * area + 19490625 =
      (area - 14175) * (area - 1375) := by
  ring1

/-- The two exact quadreas are roots; their displayed approximate square
roots are deliberately not introduced as completed real numbers. -/
theorem quadrea_values :
    (14175 : Rational) ^ 2 - 15550 * 14175 + 19490625 = 0 ∧
      (1375 : Rational) ^ 2 - 15550 * 1375 + 19490625 = 0 := by
  exact ⟨by ring1, by ring1⟩

end ExampleSeventeenThree

end ChapterSeventeenExamples

end DivineProportions
