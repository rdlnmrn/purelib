import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Quadrilaterals.Cyclic
import DivineProportions.Circles.SubtendedSpread
import DivineProportions.Trigonometry.QuadrupleSpread

/-!
# Divine Proportions, Theorem 110: cyclic quadrilateral spreads

The six subtended spreads are finite field scalars.  Their four triangle
views are stored as explicit `SpreadTriple` certificates; Theorem 110 is then
exactly two applications of the Two spread triples theorem.

For an actual displayed cyclic quadrilateral on a non-null circle,
`normalizedCyclicSubtendedSpreads` constructs those six scalars as
`Q(A_i,A_j)/(4*K)` and derives every triple certificate from the finite
Subtended spread theorem.  The nonzero circle quadrance is visible because
over a general finite field a null circle can have null chords, for which the
book's spread quotients are not defined.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Quadrilateral

/-- The scale-free spread attached to a chord of a circle of quadrance `K`. -/
def normalizedSubtendedSpread
    (circleQuadrance : K) (first second : Point K) : K :=
  quadrance first second / (4 * circleQuadrance)

/-- Normalized subtended spread is symmetric in its chord endpoints. -/
theorem normalizedSubtendedSpread_symm
    (circleQuadrance : K) (first second : Point K) :
    normalizedSubtendedSpread circleQuadrance first second =
      normalizedSubtendedSpread circleQuadrance second first := by
  unfold normalizedSubtendedSpread
  rw [quadrance_symm first second]

/-- Six subtended spreads together with the four triangle spread relations
used in the book's proof of Theorem 110. -/
structure CyclicSubtendedSpreads (K : Type*) [RFAP.ExplicitField K] where
  r₁₂ : K
  r₂₃ : K
  r₃₄ : K
  r₁₄ : K
  r₁₃ : K
  r₂₄ : K
  firstDiagonalAtFourth : SpreadTriple r₁₂ r₂₃ r₁₃
  firstDiagonalAtSecond : SpreadTriple r₃₄ r₁₄ r₁₃
  secondDiagonalAtThird : SpreadTriple r₁₂ r₁₄ r₂₄
  secondDiagonalAtFirst : SpreadTriple r₂₃ r₃₄ r₂₄

private theorem spreadTriple_swap_last {a b c : K}
    (triple : SpreadTriple a b c) : SpreadTriple a c b := by
  exact spreadTriple_rotate
    (spreadTriple_rotate (spreadTriple_swap_first_third triple))

/-- A spread subtended by two circle points at a third circle point equals
the normalized chord quadrance. -/
theorem spread_at_circle_point_eq_normalized
    [Nontrivial K] [DecidableEq K]
    (circle : Conic K) (center first second vertex : Point K)
    (circleQuadrance : K)
    (firstSecondDistinct : first ≠ second)
    (firstVertexDistinct : first ≠ vertex)
    (secondVertexDistinct : second ≠ vertex)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (vertexOnCircle : circle.Contains vertex) :
    let vertexFirstNonNull :=
      Conic.lineThrough_circle_points_nonNull circle center circleQuadrance
        twoNonzero quadranceNonzero presentation vertex first
        firstVertexDistinct.symm vertexOnCircle firstOnCircle
    let vertexSecondNonNull :=
      Conic.lineThrough_circle_points_nonNull circle center circleQuadrance
        twoNonzero quadranceNonzero presentation vertex second
        secondVertexDistinct.symm vertexOnCircle secondOnCircle
    spread (lineThrough vertex first firstVertexDistinct.symm)
        (lineThrough vertex second secondVertexDistinct.symm)
        vertexFirstNonNull vertexSecondNonNull =
      normalizedSubtendedSpread circleQuadrance first second := by
  dsimp only
  have result := Conic.subtended_spread circle center first second vertex
    circleQuadrance firstSecondDistinct firstVertexDistinct
    secondVertexDistinct twoNonzero quadranceNonzero presentation
    firstOnCircle secondOnCircle vertexOnCircle
  dsimp only at result
  exact result.1

/-- Three chords viewed from a fourth point on the same non-null circle form
a spread triple in their normalized subtended-spread values. -/
theorem normalized_subtended_spreads_form_triple
    [Nontrivial K] [DecidableEq K]
    (circle : Conic K) (center first second third vertex : Point K)
    (circleQuadrance : K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (firstVertexDistinct : first ≠ vertex)
    (secondVertexDistinct : second ≠ vertex)
    (thirdVertexDistinct : third ≠ vertex)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third)
    (vertexOnCircle : circle.Contains vertex) :
    SpreadTriple
      (normalizedSubtendedSpread circleQuadrance first second)
      (normalizedSubtendedSpread circleQuadrance second third)
      (normalizedSubtendedSpread circleQuadrance first third) := by
  let firstRayNonNull :=
    Conic.lineThrough_circle_points_nonNull circle center circleQuadrance
      twoNonzero quadranceNonzero presentation vertex first
      firstVertexDistinct.symm vertexOnCircle firstOnCircle
  let secondRayNonNull :=
    Conic.lineThrough_circle_points_nonNull circle center circleQuadrance
      twoNonzero quadranceNonzero presentation vertex second
      secondVertexDistinct.symm vertexOnCircle secondOnCircle
  let thirdRayNonNull :=
    Conic.lineThrough_circle_points_nonNull circle center circleQuadrance
      twoNonzero quadranceNonzero presentation vertex third
      thirdVertexDistinct.symm vertexOnCircle thirdOnCircle
  have rawTriple := three_lines_form_spreadTriple
    (lineThrough vertex first firstVertexDistinct.symm)
    (lineThrough vertex second secondVertexDistinct.symm)
    (lineThrough vertex third thirdVertexDistinct.symm)
    firstRayNonNull secondRayNonNull thirdRayNonNull
  have secondThirdSpread := spread_at_circle_point_eq_normalized circle center
    second third vertex circleQuadrance secondThirdDistinct
    secondVertexDistinct thirdVertexDistinct twoNonzero quadranceNonzero
    presentation secondOnCircle thirdOnCircle vertexOnCircle
  have firstThirdSpread := spread_at_circle_point_eq_normalized circle center
    first third vertex circleQuadrance firstThirdDistinct
    firstVertexDistinct thirdVertexDistinct twoNonzero quadranceNonzero
    presentation firstOnCircle thirdOnCircle vertexOnCircle
  have firstSecondSpread := spread_at_circle_point_eq_normalized circle center
    first second vertex circleQuadrance firstSecondDistinct
    firstVertexDistinct secondVertexDistinct twoNonzero quadranceNonzero
    presentation firstOnCircle secondOnCircle vertexOnCircle
  dsimp only at secondThirdSpread firstThirdSpread firstSecondSpread
  rw [secondThirdSpread, firstThirdSpread, firstSecondSpread] at rawTriple
  exact spreadTriple_rotate (spreadTriple_rotate rawTriple)

/-- Construct all six normalized subtended spreads and their four triangle
certificates from a displayed cyclic quadrilateral on a non-null circle. -/
def normalizedCyclicSubtendedSpreads
    [Nontrivial K] [DecidableEq K]
    (quadrilateral : Quadrilateral K)
    (circle : Conic K) (center : Point K) (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation : circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains quadrilateral.first)
    (secondOnCircle : circle.Contains quadrilateral.second)
    (thirdOnCircle : circle.Contains quadrilateral.third)
    (fourthOnCircle : circle.Contains quadrilateral.fourth) :
    CyclicSubtendedSpreads K where
  r₁₂ := normalizedSubtendedSpread circleQuadrance
    quadrilateral.first quadrilateral.second
  r₂₃ := normalizedSubtendedSpread circleQuadrance
    quadrilateral.second quadrilateral.third
  r₃₄ := normalizedSubtendedSpread circleQuadrance
    quadrilateral.third quadrilateral.fourth
  r₁₄ := normalizedSubtendedSpread circleQuadrance
    quadrilateral.first quadrilateral.fourth
  r₁₃ := normalizedSubtendedSpread circleQuadrance
    quadrilateral.first quadrilateral.third
  r₂₄ := normalizedSubtendedSpread circleQuadrance
    quadrilateral.second quadrilateral.fourth
  firstDiagonalAtFourth :=
    normalized_subtended_spreads_form_triple circle center
      quadrilateral.first quadrilateral.second quadrilateral.third
      quadrilateral.fourth circleQuadrance
      quadrilateral.firstSecondDistinct quadrilateral.firstThirdDistinct
      quadrilateral.secondThirdDistinct quadrilateral.firstFourthDistinct
      quadrilateral.secondFourthDistinct quadrilateral.thirdFourthDistinct
      twoNonzero quadranceNonzero presentation firstOnCircle secondOnCircle
      thirdOnCircle fourthOnCircle
  firstDiagonalAtSecond := by
    have raw := normalized_subtended_spreads_form_triple circle center
      quadrilateral.third quadrilateral.fourth quadrilateral.first
      quadrilateral.second circleQuadrance
      quadrilateral.thirdFourthDistinct
      quadrilateral.firstThirdDistinct.symm
      quadrilateral.firstFourthDistinct.symm
      quadrilateral.secondThirdDistinct.symm
      quadrilateral.secondFourthDistinct.symm
      quadrilateral.firstSecondDistinct
      twoNonzero quadranceNonzero presentation thirdOnCircle fourthOnCircle
      firstOnCircle secondOnCircle
    rw [normalizedSubtendedSpread_symm circleQuadrance quadrilateral.fourth
      quadrilateral.first,
      normalizedSubtendedSpread_symm circleQuadrance quadrilateral.third
        quadrilateral.first] at raw
    exact raw
  secondDiagonalAtThird := by
    have raw := normalized_subtended_spreads_form_triple circle center
      quadrilateral.first quadrilateral.second quadrilateral.fourth
      quadrilateral.third circleQuadrance
      quadrilateral.firstSecondDistinct quadrilateral.firstFourthDistinct
      quadrilateral.secondFourthDistinct quadrilateral.firstThirdDistinct
      quadrilateral.secondThirdDistinct quadrilateral.thirdFourthDistinct.symm
      twoNonzero quadranceNonzero presentation firstOnCircle secondOnCircle
      fourthOnCircle thirdOnCircle
    exact spreadTriple_swap_last raw
  secondDiagonalAtFirst :=
    normalized_subtended_spreads_form_triple circle center
      quadrilateral.second quadrilateral.third quadrilateral.fourth
      quadrilateral.first circleQuadrance
      quadrilateral.secondThirdDistinct quadrilateral.secondFourthDistinct
      quadrilateral.thirdFourthDistinct quadrilateral.firstSecondDistinct.symm
      quadrilateral.firstThirdDistinct.symm
      quadrilateral.firstFourthDistinct.symm
      twoNonzero quadranceNonzero presentation secondOnCircle thirdOnCircle
      fourthOnCircle firstOnCircle

/-- Theorem 110 (Cyclic quadrilateral spreads): the four side spreads obey
the Quadruple spread formula, and each diagonal spread has the printed
quotient whenever its displayed denominator is nonzero. -/
theorem cyclic_quadrilateral_spreads
    (spreads : CyclicSubtendedSpreads K) (twoNonzero : (2 : K) ≠ 0) :
    quadrupleSpreadFunction spreads.r₁₂ spreads.r₂₃ spreads.r₃₄
        spreads.r₁₄ = 0 ∧
      (let denominator :=
          2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₁₄ - spreads.r₃₄ -
            2 * spreads.r₁₂ * spreads.r₂₃ +
            2 * spreads.r₁₄ * spreads.r₃₄);
        denominator ≠ 0 →
          spreads.r₁₃ =
            ((spreads.r₁₂ - spreads.r₂₃) ^ 2 -
              (spreads.r₁₄ - spreads.r₃₄) ^ 2) / denominator) ∧
      (let denominator :=
          2 * (spreads.r₁₂ + spreads.r₁₄ - spreads.r₂₃ - spreads.r₃₄ -
            2 * spreads.r₁₂ * spreads.r₁₄ +
            2 * spreads.r₂₃ * spreads.r₃₄);
        denominator ≠ 0 →
          spreads.r₂₄ =
            ((spreads.r₁₂ - spreads.r₁₄) ^ 2 -
              (spreads.r₂₃ - spreads.r₃₄) ^ 2) / denominator) := by
  dsimp only
  have firstResult := two_spread_triples spreads.r₁₂ spreads.r₂₃
    spreads.r₃₄ spreads.r₁₄ spreads.r₁₃ twoNonzero
    spreads.firstDiagonalAtFourth spreads.firstDiagonalAtSecond
  have secondResult := two_spread_triples spreads.r₁₂ spreads.r₁₄
    spreads.r₂₃ spreads.r₃₄ spreads.r₂₄ twoNonzero
    spreads.secondDiagonalAtThird spreads.secondDiagonalAtFirst
  refine ⟨firstResult.1, ?_, ?_⟩
  · intro denominatorNonzero
    have centersDistinct :
        spreads.r₁₂ + spreads.r₂₃ - 2 * spreads.r₁₂ * spreads.r₂₃ ≠
          spreads.r₃₄ + spreads.r₁₄ - 2 * spreads.r₃₄ * spreads.r₁₄ := by
      intro centersEqual
      apply denominatorNonzero
      calc
        2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₁₄ - spreads.r₃₄ -
            2 * spreads.r₁₂ * spreads.r₂₃ +
            2 * spreads.r₁₄ * spreads.r₃₄) =
          2 * ((spreads.r₁₂ + spreads.r₂₃ -
              2 * spreads.r₁₂ * spreads.r₂₃) -
            (spreads.r₃₄ + spreads.r₁₄ -
              2 * spreads.r₃₄ * spreads.r₁₄)) := by ring1
        _ = 0 := by rw [centersEqual]; ring1
    have formula := (firstResult.2 centersDistinct).2
    have numeratorEqual :
        (spreads.r₁₂ - spreads.r₂₃) ^ 2 -
            (spreads.r₃₄ - spreads.r₁₄) ^ 2 =
          (spreads.r₁₂ - spreads.r₂₃) ^ 2 -
            (spreads.r₁₄ - spreads.r₃₄) ^ 2 := by ring1
    have denominatorEqual :
        2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₃₄ - spreads.r₁₄ -
            2 * spreads.r₁₂ * spreads.r₂₃ +
            2 * spreads.r₃₄ * spreads.r₁₄) =
          2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₁₄ - spreads.r₃₄ -
            2 * spreads.r₁₂ * spreads.r₂₃ +
            2 * spreads.r₁₄ * spreads.r₃₄) := by ring1
    calc
      spreads.r₁₃ =
          ((spreads.r₁₂ - spreads.r₂₃) ^ 2 -
            (spreads.r₃₄ - spreads.r₁₄) ^ 2) /
            (2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₃₄ -
              spreads.r₁₄ - 2 * spreads.r₁₂ * spreads.r₂₃ +
              2 * spreads.r₃₄ * spreads.r₁₄)) := formula
      _ = ((spreads.r₁₂ - spreads.r₂₃) ^ 2 -
            (spreads.r₁₄ - spreads.r₃₄) ^ 2) /
          (2 * (spreads.r₁₂ + spreads.r₂₃ - spreads.r₁₄ -
            spreads.r₃₄ - 2 * spreads.r₁₂ * spreads.r₂₃ +
            2 * spreads.r₁₄ * spreads.r₃₄)) := by
        rw [numeratorEqual, denominatorEqual]
  · intro denominatorNonzero
    have centersDistinct :
        spreads.r₁₂ + spreads.r₁₄ - 2 * spreads.r₁₂ * spreads.r₁₄ ≠
          spreads.r₂₃ + spreads.r₃₄ - 2 * spreads.r₂₃ * spreads.r₃₄ := by
      intro centersEqual
      apply denominatorNonzero
      calc
        2 * (spreads.r₁₂ + spreads.r₁₄ - spreads.r₂₃ - spreads.r₃₄ -
            2 * spreads.r₁₂ * spreads.r₁₄ +
            2 * spreads.r₂₃ * spreads.r₃₄) =
          2 * ((spreads.r₁₂ + spreads.r₁₄ -
              2 * spreads.r₁₂ * spreads.r₁₄) -
            (spreads.r₂₃ + spreads.r₃₄ -
              2 * spreads.r₂₃ * spreads.r₃₄)) := by ring1
        _ = 0 := by rw [centersEqual]; ring1
    exact (secondResult.2 centersDistinct).2

end Quadrilateral

end DivineProportions
