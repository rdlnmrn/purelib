import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Circles.Chord
import DivineProportions.Centers.ExtendedSpread

/-!
# Divine Proportions, §16.2: subtended spreads

The Extended spread law supplies the fixed cleared ratio on a circle.  A
second finite determinant identity for the two radius vectors converts that
ratio into the source's `S₂(s) = 4s(1-s)` formula.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by ring1
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel]; ring1

/-- The line through two distinct points of a non-null circle is non-null. -/
theorem lineThrough_circle_points_nonNull [DecidableEq K]
    (circle : Conic K) (center : Point K) (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (first second : Point K) (distinct : first ≠ second)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second) :
    ¬ (lineThrough first second distinct).IsNull := by
  apply circle_chord circle (lineThrough first second distinct) center
    circleQuadrance twoNonzero quadranceNonzero presentation
  exact ⟨first, second, distinct,
    ⟨lineThrough_contains_first first second distinct, firstOnCircle⟩,
    ⟨lineThrough_contains_second first second distinct, secondOnCircle⟩⟩

private theorem point_ne_center_of_circle_quadrance_ne_zero
    (circle : Conic K) (center point : Point K) (circleQuadrance : K)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (pointOnCircle : circle.Contains point) : point ≠ center := by
  have radius : quadrance point center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).1 pointOnCircle
  intro pointEqualsCenter
  apply quadranceNonzero
  calc
    circleQuadrance = quadrance point center := radius.symm
    _ = quadrance center center := by rw [pointEqualsCenter]
    _ = 0 := quadrance_self center

/-- Theorem 105 (Subtended spread): the spread at the third circle point is
fixed by the chord, and the spread at the center is its second spread
polynomial `4s(1-s)`. -/
theorem subtended_spread [Nontrivial K] [DecidableEq K]
    (circle : Conic K) (center first second third : Point K)
    (circleQuadrance : K)
    (firstSecondDistinct : first ≠ second)
    (firstThirdDistinct : first ≠ third)
    (secondThirdDistinct : second ≠ third)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (firstOnCircle : circle.Contains first)
    (secondOnCircle : circle.Contains second)
    (thirdOnCircle : circle.Contains third) :
    let firstCenterDistinct :=
      point_ne_center_of_circle_quadrance_ne_zero circle center first
        circleQuadrance quadranceNonzero presentation firstOnCircle
    let secondCenterDistinct :=
      point_ne_center_of_circle_quadrance_ne_zero circle center second
        circleQuadrance quadranceNonzero presentation secondOnCircle
    let firstThirdNonNull := lineThrough_circle_points_nonNull circle center
      circleQuadrance twoNonzero quadranceNonzero presentation first third
      firstThirdDistinct firstOnCircle thirdOnCircle
    let secondThirdNonNull := lineThrough_circle_points_nonNull circle center
      circleQuadrance twoNonzero quadranceNonzero presentation second third
      secondThirdDistinct secondOnCircle thirdOnCircle
    let firstCenterNonNull :
        ¬ (lineThrough first center firstCenterDistinct).IsNull := by
      intro lineNull
      apply quadranceNonzero
      have radiusZero :=
        (null_line_iff_quadrance_zero first center
          firstCenterDistinct).1 lineNull
      calc
        circleQuadrance = quadrance first center :=
          ((contains_iff_quadrance_eq circle center first circleQuadrance
            presentation).1 firstOnCircle).symm
        _ = 0 := radiusZero
    let secondCenterNonNull :
        ¬ (lineThrough second center secondCenterDistinct).IsNull := by
      intro lineNull
      apply quadranceNonzero
      have radiusZero :=
        (null_line_iff_quadrance_zero second center
          secondCenterDistinct).1 lineNull
      calc
        circleQuadrance = quadrance second center :=
          ((contains_iff_quadrance_eq circle center second circleQuadrance
            presentation).1 secondOnCircle).symm
        _ = 0 := radiusZero
    let firstThirdReversedNonNull :
        ¬ (lineThrough third first firstThirdDistinct.symm).IsNull := by
      rwa [null_line_iff_quadrance_zero,
        quadrance_symm third first,
        ← null_line_iff_quadrance_zero first third firstThirdDistinct]
    let secondThirdReversedNonNull :
        ¬ (lineThrough third second secondThirdDistinct.symm).IsNull := by
      rwa [null_line_iff_quadrance_zero,
        quadrance_symm third second,
        ← null_line_iff_quadrance_zero second third secondThirdDistinct]
    let centralSpread :=
      spread (lineThrough first center firstCenterDistinct)
        (lineThrough second center secondCenterDistinct)
        firstCenterNonNull secondCenterNonNull
    let subtendedSpreadValue :=
      spread (lineThrough third first firstThirdDistinct.symm)
        (lineThrough third second secondThirdDistinct.symm)
        firstThirdReversedNonNull secondThirdReversedNonNull
    subtendedSpreadValue =
        quadrance first second / (4 * circleQuadrance) ∧
      centralSpread =
        4 * subtendedSpreadValue * (1 - subtendedSpreadValue) := by
  dsimp only
  let firstCenterDistinct :=
    point_ne_center_of_circle_quadrance_ne_zero circle center first
      circleQuadrance quadranceNonzero presentation firstOnCircle
  let secondCenterDistinct :=
    point_ne_center_of_circle_quadrance_ne_zero circle center second
      circleQuadrance quadranceNonzero presentation secondOnCircle
  let firstSecondNonNull := lineThrough_circle_points_nonNull circle center
    circleQuadrance twoNonzero quadranceNonzero presentation first second
    firstSecondDistinct firstOnCircle secondOnCircle
  let firstThirdNonNull := lineThrough_circle_points_nonNull circle center
    circleQuadrance twoNonzero quadranceNonzero presentation first third
    firstThirdDistinct firstOnCircle thirdOnCircle
  let secondThirdNonNull := lineThrough_circle_points_nonNull circle center
    circleQuadrance twoNonzero quadranceNonzero presentation second third
    secondThirdDistinct secondOnCircle thirdOnCircle
  let firstSecondReversedNonNull :
      ¬ (lineThrough second first firstSecondDistinct.symm).IsNull := by
    rwa [null_line_iff_quadrance_zero,
      quadrance_symm second first,
      ← null_line_iff_quadrance_zero first second firstSecondDistinct]
  let firstThirdReversedNonNull :
      ¬ (lineThrough third first firstThirdDistinct.symm).IsNull := by
    rwa [null_line_iff_quadrance_zero,
      quadrance_symm third first,
      ← null_line_iff_quadrance_zero first third firstThirdDistinct]
  let secondThirdReversedNonNull :
      ¬ (lineThrough third second secondThirdDistinct.symm).IsNull := by
    rwa [null_line_iff_quadrance_zero,
      quadrance_symm third second,
      ← null_line_iff_quadrance_zero second third secondThirdDistinct]
  let firstCenterNonNull :
      ¬ (lineThrough first center firstCenterDistinct).IsNull := by
    intro lineNull
    apply quadranceNonzero
    have radiusZero :=
      (null_line_iff_quadrance_zero first center firstCenterDistinct).1 lineNull
    calc
      circleQuadrance = quadrance first center :=
        ((contains_iff_quadrance_eq circle center first circleQuadrance
          presentation).1 firstOnCircle).symm
      _ = 0 := radiusZero
  let secondCenterNonNull :
      ¬ (lineThrough second center secondCenterDistinct).IsNull := by
    intro lineNull
    apply quadranceNonzero
    have radiusZero :=
      (null_line_iff_quadrance_zero second center secondCenterDistinct).1 lineNull
    calc
      circleQuadrance = quadrance second center :=
        ((contains_iff_quadrance_eq circle center second circleQuadrance
          presentation).1 secondOnCircle).symm
      _ = 0 := radiusZero
  let firstSpread :=
    spread (lineThrough first second firstSecondDistinct)
      (lineThrough first third firstThirdDistinct)
      firstSecondNonNull firstThirdNonNull
  let secondSpread :=
    spread (lineThrough second first firstSecondDistinct.symm)
      (lineThrough second third secondThirdDistinct)
      firstSecondReversedNonNull secondThirdNonNull
  let subtendedSpreadValue :=
    spread (lineThrough third first firstThirdDistinct.symm)
      (lineThrough third second secondThirdDistinct.symm)
      firstThirdReversedNonNull secondThirdReversedNonNull
  let centralSpread :=
    spread (lineThrough first center firstCenterDistinct)
      (lineThrough second center secondCenterDistinct)
      firstCenterNonNull secondCenterNonNull
  let firstSideQuadrance := quadrance second third
  let secondSideQuadrance := quadrance first third
  let chordQuadrance := quadrance first second
  have firstRadiusFromPoint : quadrance first center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstOnCircle
  have secondRadiusFromPoint : quadrance second center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondOnCircle
  have thirdRadiusFromPoint : quadrance third center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center third circleQuadrance
      presentation).1 thirdOnCircle
  have firstRadius : quadrance center first = circleQuadrance := by
    calc
      quadrance center first = quadrance first center := quadrance_symm center first
      _ = circleQuadrance := firstRadiusFromPoint
  have secondRadius : quadrance center second = circleQuadrance := by
    calc
      quadrance center second = quadrance second center := quadrance_symm center second
      _ = circleQuadrance := secondRadiusFromPoint
  have thirdRadius : quadrance center third = circleQuadrance := by
    calc
      quadrance center third = quadrance third center := quadrance_symm center third
      _ = circleQuadrance := thirdRadiusFromPoint
  have extendedRatios := extended_spread_law first second third center
    firstSecondDistinct firstThirdDistinct secondThirdDistinct
    firstSecondNonNull firstThirdNonNull secondThirdNonNull twoNonzero
    (firstRadius.trans secondRadius.symm)
    (secondRadius.trans thirdRadius.symm)
  dsimp only at extendedRatios
  rw [firstRadius] at extendedRatios
  change firstSpread / firstSideQuadrance =
        secondSpread / secondSideQuadrance ∧
      secondSpread / secondSideQuadrance =
        subtendedSpreadValue / chordQuadrance ∧
      subtendedSpreadValue / chordQuadrance =
        1 / (4 * circleQuadrance) at extendedRatios
  have firstSideNonzero : firstSideQuadrance ≠ 0 := by
    intro sideZero
    exact secondThirdNonNull
      ((null_line_iff_quadrance_zero second third
        secondThirdDistinct).2 sideZero)
  have secondSideNonzero : secondSideQuadrance ≠ 0 := by
    intro sideZero
    exact firstThirdNonNull
      ((null_line_iff_quadrance_zero first third
        firstThirdDistinct).2 sideZero)
  have chordNonzero : chordQuadrance ≠ 0 := by
    intro chordZero
    exact firstSecondNonNull
      ((null_line_iff_quadrance_zero first second
        firstSecondDistinct).2 chordZero)
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    intro fourZero
    apply productNonzero
    calc
      (2 : K) * 2 = 4 := by ring1
      _ = 0 := fourZero
  have fourQuadranceNonzero : 4 * circleQuadrance ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero quadranceNonzero
  have extendedCrossProducts := extended_spread_law_cross_products
    firstSideQuadrance secondSideQuadrance chordQuadrance
    firstSpread secondSpread subtendedSpreadValue circleQuadrance
    firstSideNonzero secondSideNonzero chordNonzero
    fourQuadranceNonzero extendedRatios
  have subtendedCross :
      subtendedSpreadValue * (4 * circleQuadrance) = chordQuadrance :=
    extendedCrossProducts.2.2
  have fixedSubtendedSpread :
      subtendedSpreadValue =
        chordQuadrance / (4 * circleQuadrance) := by
    apply eq_of_mul_eq_mul_right fourQuadranceNonzero
    calc
      subtendedSpreadValue * (4 * circleQuadrance) = chordQuadrance :=
        subtendedCross
      _ = (chordQuadrance / (4 * circleQuadrance)) *
          (4 * circleQuadrance) :=
        (RFAP.ExplicitField.div_mul_cancel chordQuadrance
          fourQuadranceNonzero).symm
  let determinant :=
    (first.y - center.y) * (center.x - second.x) -
      (second.y - center.y) * (center.x - first.x)
  have centralSpreadFormula :
      centralSpread = determinant ^ 2 /
        (circleQuadrance * circleQuadrance) := by
    rw [show centralSpread =
      spread (lineThrough first center firstCenterDistinct)
        (lineThrough second center secondCenterDistinct)
        firstCenterNonNull secondCenterNonNull by rfl]
    rw [spread_from_points first second center firstCenterDistinct
      secondCenterDistinct firstCenterNonNull secondCenterNonNull]
    rw [firstRadiusFromPoint, secondRadiusFromPoint]
  have generalDeterminantIdentity :
      4 * determinant ^ 2 +
          (quadrance first center - quadrance second center) ^ 2 =
        chordQuadrance *
          (2 * quadrance first center + 2 * quadrance second center -
            chordQuadrance) := by
    unfold determinant chordQuadrance quadrance
    ring1
  have determinantIdentity :
      4 * determinant ^ 2 =
        chordQuadrance * (4 * circleQuadrance - chordQuadrance) := by
    calc
      4 * determinant ^ 2 = 4 * determinant ^ 2 +
          (quadrance first center - quadrance second center) ^ 2 := by
        rw [firstRadiusFromPoint, secondRadiusFromPoint]
        ring1
      _ = chordQuadrance *
          (2 * quadrance first center + 2 * quadrance second center -
            chordQuadrance) := generalDeterminantIdentity
      _ = chordQuadrance * (4 * circleQuadrance - chordQuadrance) := by
        rw [firstRadiusFromPoint, secondRadiusFromPoint]
        ring1
  have quadranceSquareNonzero :
      circleQuadrance * circleQuadrance ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero quadranceNonzero quadranceNonzero
  have scalingFactorNonzero :
      4 * (circleQuadrance * circleQuadrance) ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero fourNonzero quadranceSquareNonzero
  have centralScaled :
      centralSpread * (4 * (circleQuadrance * circleQuadrance)) =
        4 * determinant ^ 2 := by
    rw [centralSpreadFormula]
    calc
      (determinant ^ 2 / (circleQuadrance * circleQuadrance)) *
          (4 * (circleQuadrance * circleQuadrance)) =
        4 * ((determinant ^ 2 / (circleQuadrance * circleQuadrance)) *
          (circleQuadrance * circleQuadrance)) := by ring1
      _ = 4 * determinant ^ 2 := by
        rw [RFAP.ExplicitField.div_mul_cancel (determinant ^ 2)
          quadranceSquareNonzero]
  have polynomialScaled :
      (4 * subtendedSpreadValue * (1 - subtendedSpreadValue)) *
          (4 * (circleQuadrance * circleQuadrance)) =
        chordQuadrance * (4 * circleQuadrance - chordQuadrance) := by
    calc
      (4 * subtendedSpreadValue * (1 - subtendedSpreadValue)) *
          (4 * (circleQuadrance * circleQuadrance)) =
        (subtendedSpreadValue * (4 * circleQuadrance)) *
          (4 * circleQuadrance -
            subtendedSpreadValue * (4 * circleQuadrance)) := by ring1
      _ = chordQuadrance * (4 * circleQuadrance - chordQuadrance) := by
        rw [subtendedCross]
  refine ⟨fixedSubtendedSpread, ?_⟩
  apply eq_of_mul_eq_mul_right scalingFactorNonzero
  calc
    centralSpread * (4 * (circleQuadrance * circleQuadrance)) =
        4 * determinant ^ 2 := centralScaled
    _ = chordQuadrance * (4 * circleQuadrance - chordQuadrance) :=
      determinantIdentity
    _ = (4 * subtendedSpreadValue * (1 - subtendedSpreadValue)) *
        (4 * (circleQuadrance * circleQuadrance)) := polynomialScaled.symm

end Conic

end DivineProportions
