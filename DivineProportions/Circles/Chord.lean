import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Circles.RightDiameter
import DivineProportions.Trigonometry.VertexBisector

/-!
# Divine Proportions, §16.1: circle chords

The source introduces a square root of `-1` while excluding null chords.  The
proof here stays constructive: two cleared square identities show directly
that equal-radius points with null separation would force the radius to vanish.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace Conic

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have inverseCancel : factor⁻¹ * factor = (1 : K) := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by ring1
    _ = (factor⁻¹ * factor) * value := by rw [inverseCancel]
    _ = factor⁻¹ * (factor * value) := mul_assoc _ _ _
    _ = 0 := by rw [productZero]; ring1

/-- Two points on a null displayed line have zero mutual quadrance. -/
theorem quadrance_eq_zero_of_null_line_contains [DecidableEq K]
    (line : Line K) (lineNull : line.IsNull)
    (first second : Point K)
    (containsFirst : line.Contains first)
    (containsSecond : line.Contains second) :
    quadrance first second = 0 := by
  have directionEquation :
      line.a * (second.x - first.x) +
        line.b * (second.y - first.y) = 0 := by
    unfold Line.Contains at containsFirst containsSecond
    calc
      line.a * (second.x - first.x) +
          line.b * (second.y - first.y) =
        (line.a * second.x + line.b * second.y + line.c) -
          (line.a * first.x + line.b * first.y + line.c) := by ring1
      _ = 0 := by rw [containsFirst, containsSecond]; ring1
  have aNonzero : line.a ≠ 0 := by
    by_cases aZero : line.a = 0
    · have bSquareZero : line.b * line.b = 0 := by
        calc
          line.b * line.b = line.a ^ 2 + line.b ^ 2 := by
            rw [aZero]
            ring1
          _ = 0 := lineNull
      have bZero : line.b = 0 := by
        by_cases bZero : line.b = 0
        · exact bZero
        · exact False.elim
            ((RFAP.ExplicitField.mul_ne_zero bZero bZero) bSquareZero)
      rcases line.direction_nonzero with aNonzero | bNonzero
      · exact False.elim (aNonzero aZero)
      · exact False.elim (bNonzero bZero)
    · exact aZero
  have aSquareNonzero : line.a ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero aNonzero aNonzero
  have squareProductsEqual :
      line.a ^ 2 * (second.x - first.x) ^ 2 =
        line.b ^ 2 * (second.y - first.y) ^ 2 := by
    have linearEquality :
        line.a * (second.x - first.x) =
          -(line.b * (second.y - first.y)) := by
      calc
        line.a * (second.x - first.x) =
            (line.a * (second.x - first.x) +
              line.b * (second.y - first.y)) -
              line.b * (second.y - first.y) := by ring1
        _ = -(line.b * (second.y - first.y)) := by
          rw [directionEquation]
          ring1
    calc
      line.a ^ 2 * (second.x - first.x) ^ 2 =
          (line.a * (second.x - first.x)) ^ 2 := by ring1
      _ = (-(line.b * (second.y - first.y))) ^ 2 := by rw [linearEquality]
      _ = line.b ^ 2 * (second.y - first.y) ^ 2 := by ring1
  apply eq_zero_of_mul_eq_zero_left aSquareNonzero
  calc
    line.a ^ 2 * quadrance first second =
        line.a ^ 2 * (second.x - first.x) ^ 2 +
          line.a ^ 2 * (second.y - first.y) ^ 2 := by
      unfold quadrance
      ring1
    _ = line.b ^ 2 * (second.y - first.y) ^ 2 +
        line.a ^ 2 * (second.y - first.y) ^ 2 := by
      rw [squareProductsEqual]
    _ = (line.a ^ 2 + line.b ^ 2) *
        (second.y - first.y) ^ 2 := by ring1
    _ = 0 := by rw [lineNull]; ring1

/-- Equal-radius distinct points cannot have null separation unless the common
radius itself is zero. -/
theorem radius_eq_zero_of_equal_radii_and_null_separation [DecidableEq K]
    (first second center : Point K) (radius : K)
    (distinct : first ≠ second) (twoNonzero : (2 : K) ≠ 0)
    (firstRadius : quadrance center first = radius)
    (secondRadius : quadrance center second = radius)
    (separationZero : quadrance first second = 0) :
    radius = 0 := by
  have xDifferenceNonzero : second.x - first.x ≠ 0 := by
    intro xDifferenceZero
    have xEqual : second.x = first.x := by
      calc
        second.x = (second.x - first.x) + first.x := by ring1
        _ = first.x := by rw [xDifferenceZero]; ring1
    have ySquareZero : (second.y - first.y) *
        (second.y - first.y) = 0 := by
      calc
        (second.y - first.y) * (second.y - first.y) =
            quadrance first second := by
          unfold quadrance
          rw [xDifferenceZero]
          ring1
        _ = 0 := separationZero
    have yDifferenceZero : second.y - first.y = 0 := by
      by_cases yDifferenceZero : second.y - first.y = 0
      · exact yDifferenceZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero yDifferenceZero yDifferenceZero)
            ySquareZero)
    have yEqual : second.y = first.y := by
      calc
        second.y = (second.y - first.y) + first.y := by ring1
        _ = first.y := by rw [yDifferenceZero]; ring1
    exact distinct (Point.ext xEqual.symm yEqual.symm)
  have xDifferenceSquareNonzero : (second.x - first.x) ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero xDifferenceNonzero
        xDifferenceNonzero
  have dotProductZero :
      (second.x - first.x) * (first.x - center.x) +
        (second.y - first.y) * (first.y - center.y) = 0 := by
    have twiceDotZero :
        2 * ((second.x - first.x) * (first.x - center.x) +
          (second.y - first.y) * (first.y - center.y)) = 0 := by
      calc
        2 * ((second.x - first.x) * (first.x - center.x) +
            (second.y - first.y) * (first.y - center.y)) =
          (quadrance center second - quadrance center first) -
            quadrance first second := by
              unfold quadrance
              ring1
        _ = 0 := by
          rw [firstRadius, secondRadius, separationZero]
          ring1
    exact eq_zero_of_mul_eq_zero_left twoNonzero twiceDotZero
  have coordinateSquareProductsEqual :
      (second.x - first.x) ^ 2 * (first.x - center.x) ^ 2 =
        (second.y - first.y) ^ 2 * (first.y - center.y) ^ 2 := by
    have coordinateProductEquality :
        (second.x - first.x) * (first.x - center.x) =
          -((second.y - first.y) * (first.y - center.y)) := by
      calc
        (second.x - first.x) * (first.x - center.x) =
            ((second.x - first.x) * (first.x - center.x) +
              (second.y - first.y) * (first.y - center.y)) -
              (second.y - first.y) * (first.y - center.y) := by ring1
        _ = -((second.y - first.y) * (first.y - center.y)) := by
          rw [dotProductZero]
          ring1
    calc
      (second.x - first.x) ^ 2 * (first.x - center.x) ^ 2 =
          ((second.x - first.x) * (first.x - center.x)) ^ 2 := by ring1
      _ = (-((second.y - first.y) *
          (first.y - center.y))) ^ 2 := by rw [coordinateProductEquality]
      _ = (second.y - first.y) ^ 2 *
          (first.y - center.y) ^ 2 := by ring1
  have scaledRadiusZero :
      (second.x - first.x) ^ 2 * quadrance center first = 0 := by
    calc
      (second.x - first.x) ^ 2 * quadrance center first =
          (second.x - first.x) ^ 2 * (first.x - center.x) ^ 2 +
            (second.x - first.x) ^ 2 * (first.y - center.y) ^ 2 := by
        unfold quadrance
        ring1
      _ = (second.y - first.y) ^ 2 * (first.y - center.y) ^ 2 +
          (second.x - first.x) ^ 2 * (first.y - center.y) ^ 2 := by
        rw [coordinateSquareProductsEqual]
      _ = quadrance first second * (first.y - center.y) ^ 2 := by
        unfold quadrance
        ring1
      _ = 0 := by rw [separationZero]; ring1
  have firstRadiusZero := eq_zero_of_mul_eq_zero_left
    xDifferenceSquareNonzero scaledRadiusZero
  calc
    radius = quadrance center first := firstRadius.symm
    _ = 0 := firstRadiusZero

/-- Theorem 104 (Circle chord): a chord of a non-null circle is non-null. -/
theorem circle_chord [DecidableEq K]
    (circle : Conic K) (line : Line K) (center : Point K)
    (circleQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (chord : circle.IsChord line) :
    ¬ line.IsNull := by
  rcases chord with
    ⟨first, second, distinct, firstIntersection, secondIntersection⟩
  have firstRadiusFromPoint : quadrance first center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstIntersection.2
  have secondRadiusFromPoint : quadrance second center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondIntersection.2
  have firstRadius : quadrance center first = circleQuadrance := by
    calc
      quadrance center first = quadrance first center :=
        quadrance_symm center first
      _ = circleQuadrance := firstRadiusFromPoint
  have secondRadius : quadrance center second = circleQuadrance := by
    calc
      quadrance center second = quadrance second center :=
        quadrance_symm center second
      _ = circleQuadrance := secondRadiusFromPoint
  intro lineNull
  have separationZero := quadrance_eq_zero_of_null_line_contains line lineNull
    first second firstIntersection.1 secondIntersection.1
  exact quadranceNonzero
    (radius_eq_zero_of_equal_radii_and_null_separation first second center
      circleQuadrance distinct twoNonzero firstRadius secondRadius
      separationZero)

/-- A diameter supplies a nonzero square witness for the product of its line
norm and the circle quadrance. -/
theorem diameter_norm_mul_quadrance_isNonzeroSquare [DecidableEq K]
    (circle : Conic K) (line : Line K) (center : Point K)
    (circleQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (diameter : circle.IsDiameter line center) :
    IsNonzeroSquare (lineNorm line * circleQuadrance) := by
  have chord := exercise_16_1 circle line center circleQuadrance twoNonzero
    quadranceNonzero presentation diameter
  have lineNonNull := circle_chord circle line center circleQuadrance
    twoNonzero quadranceNonzero presentation chord
  rcases diameter with ⟨centerOnLine, point, pointIntersection⟩
  have pointRadiusFromPoint : quadrance point center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center point circleQuadrance
      presentation).1 pointIntersection.2
  have pointRadius : quadrance center point = circleQuadrance := by
    calc
      quadrance center point = quadrance point center :=
        quadrance_symm center point
      _ = circleQuadrance := pointRadiusFromPoint
  have directionDotZero :
      line.a * (point.x - center.x) +
        line.b * (point.y - center.y) = 0 := by
    have centerEquation := centerOnLine
    have pointEquation := pointIntersection.1
    unfold Line.Contains at centerEquation pointEquation
    calc
      line.a * (point.x - center.x) +
          line.b * (point.y - center.y) =
        (line.a * point.x + line.b * point.y + line.c) -
          (line.a * center.x + line.b * center.y + line.c) := by ring1
      _ = 0 := by rw [pointEquation, centerEquation]; ring1
  let crossValue :=
    line.a * (point.y - center.y) -
      line.b * (point.x - center.x)
  have squareEquation :
      lineNorm line * circleQuadrance = crossValue ^ 2 := by
    calc
      lineNorm line * circleQuadrance =
          lineNorm line * quadrance center point := by rw [pointRadius]
      _ = crossValue ^ 2 +
          (line.a * (point.x - center.x) +
            line.b * (point.y - center.y)) ^ 2 := by
        unfold lineNorm quadrance crossValue
        ring1
      _ = crossValue ^ 2 := by rw [directionDotZero]; ring1
  have productNonzero : lineNorm line * circleQuadrance ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero lineNonNull quadranceNonzero
  have crossNonzero : crossValue ≠ 0 := by
    intro crossZero
    apply productNonzero
    calc
      lineNorm line * circleQuadrance = crossValue ^ 2 := squareEquation
      _ = 0 := by rw [crossZero]; ring1
  exact ⟨crossValue, crossNonzero, squareEquation⟩

/-- Exercise 16.2: two geometrically distinct diameters of a non-null circle
form a square vertex, witnessed here by an explicit vertex bisector. -/
theorem exercise_16_2 [DecidableEq K]
    (circle : Conic K) (firstLine secondLine : Line K)
    (center : Point K) (circleQuadrance : K)
    (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance)
    (firstDiameter : circle.IsDiameter firstLine center)
    (secondDiameter : circle.IsDiameter secondLine center)
    (notEquivalent : ¬ firstLine.Equivalent secondLine) :
    ∃ bisector : Line K,
      IsVertexBisector firstLine secondLine bisector
        (circle_chord circle firstLine center circleQuadrance twoNonzero
          quadranceNonzero presentation
          (exercise_16_1 circle firstLine center circleQuadrance twoNonzero
            quadranceNonzero presentation firstDiameter))
        (circle_chord circle secondLine center circleQuadrance twoNonzero
          quadranceNonzero presentation
          (exercise_16_1 circle secondLine center circleQuadrance twoNonzero
            quadranceNonzero presentation secondDiameter))
        (by
          intro parallel
          exact notEquivalent
            (line_equivalent_of_parallel_and_common_point firstLine secondLine
              center parallel firstDiameter.1 secondDiameter.1)) := by
  let firstNonNull := circle_chord circle firstLine center circleQuadrance
    twoNonzero quadranceNonzero presentation
      (exercise_16_1 circle firstLine center circleQuadrance twoNonzero
        quadranceNonzero presentation firstDiameter)
  let secondNonNull := circle_chord circle secondLine center circleQuadrance
    twoNonzero quadranceNonzero presentation
      (exercise_16_1 circle secondLine center circleQuadrance twoNonzero
        quadranceNonzero presentation secondDiameter)
  have notParallel : ¬ firstLine.Parallel secondLine := by
    intro parallel
    exact notEquivalent
      (line_equivalent_of_parallel_and_common_point firstLine secondLine center
        parallel firstDiameter.1 secondDiameter.1)
  rcases diameter_norm_mul_quadrance_isNonzeroSquare circle firstLine center
      circleQuadrance twoNonzero quadranceNonzero presentation firstDiameter with
    ⟨firstRoot, firstRootNonzero, firstEquation⟩
  rcases diameter_norm_mul_quadrance_isNonzeroSquare circle secondLine center
      circleQuadrance twoNonzero quadranceNonzero presentation secondDiameter with
    ⟨secondRoot, secondRootNonzero, secondEquation⟩
  let root := (firstRoot * secondRoot) / circleQuadrance
  have rootNonzero : root ≠ 0 := by
    unfold root
    exact RFAP.ExplicitField.div_ne_zero
      (RFAP.ExplicitField.mul_ne_zero firstRootNonzero secondRootNonzero)
      quadranceNonzero
  have quadranceCancel :
      circleQuadrance * circleQuadrance⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel circleQuadrance quadranceNonzero
  have rootEquation :
      lineNorm firstLine * lineNorm secondLine = root ^ 2 := by
    unfold root
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      lineNorm firstLine * lineNorm secondLine =
          lineNorm firstLine * lineNorm secondLine *
            (circleQuadrance * circleQuadrance⁻¹) ^ 2 := by
        rw [quadranceCancel]
        ring1
      _ = (lineNorm firstLine * circleQuadrance) *
          (lineNorm secondLine * circleQuadrance) *
            (circleQuadrance⁻¹) ^ 2 := by ring1
      _ = firstRoot ^ 2 * secondRoot ^ 2 *
          (circleQuadrance⁻¹) ^ 2 := by
        rw [firstEquation, secondEquation]
      _ = (firstRoot * secondRoot * circleQuadrance⁻¹) ^ 2 := by ring1
  have normProductSquare :
      IsNonzeroSquare (lineNorm firstLine * lineNorm secondLine) :=
    ⟨root, rootNonzero, rootEquation⟩
  have spreadSquare :=
    (spread_isNonzeroSquare_iff_normProduct_isNonzeroSquare firstLine secondLine
      firstNonNull secondNonNull notParallel).2 normProductSquare
  exact
    (vertex_bisector_exists_iff_spread_isNonzeroSquare firstLine secondLine
      firstNonNull secondNonNull notParallel twoNonzero).2 spreadSquare

/-- Exercise 16.3: a line cannot have three distinct intersections with a
non-null circle. -/
theorem exercise_16_3 [DecidableEq K]
    (circle : Conic K) (line : Line K) (center : Point K)
    (circleQuadrance : K) (twoNonzero : (2 : K) ≠ 0)
    (quadranceNonzero : circleQuadrance ≠ 0)
    (presentation :
      circle.IsCirclePresentation center circleQuadrance) :
    ¬ circle.HasThreeDistinctIntersections line := by
  intro threeIntersections
  rcases threeIntersections with
    ⟨first, second, third, firstSecondDistinct, firstThirdDistinct,
      secondThirdDistinct, firstIntersection, secondIntersection,
      thirdIntersection⟩
  have firstRadiusFromPoint : quadrance first center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center first circleQuadrance
      presentation).1 firstIntersection.2
  have secondRadiusFromPoint : quadrance second center = circleQuadrance :=
    (contains_iff_quadrance_eq circle center second circleQuadrance
      presentation).1 secondIntersection.2
  have separationNonzero : quadrance first second ≠ 0 := by
    intro separationZero
    apply quadranceNonzero
    exact radius_eq_zero_of_equal_radii_and_null_separation
      first second center circleQuadrance firstSecondDistinct twoNonzero
      (by
        calc
          quadrance center first = quadrance first center :=
            quadrance_symm center first
          _ = circleQuadrance := firstRadiusFromPoint)
      (by
        calc
          quadrance center second = quadrance second center :=
            quadrance_symm center second
          _ = circleQuadrance := secondRadiusFromPoint)
      separationZero
  have allLinePoints := conic_line_intersection circle line
    ⟨first, second, third, firstSecondDistinct, firstThirdDistinct,
      secondThirdDistinct, firstIntersection, secondIntersection,
      thirdIntersection⟩
  have testPointOnLine : line.Contains (thalesPoint 2 first second) := by
    have firstOnLine := firstIntersection.1
    have secondOnLine := secondIntersection.1
    unfold Line.Contains at firstOnLine secondOnLine ⊢
    unfold thalesPoint affineCombination
    calc
      line.a * ((1 - 2) * first.x + 2 * second.x) +
          line.b * ((1 - 2) * first.y + 2 * second.y) + line.c =
        (1 - 2) *
            (line.a * first.x + line.b * first.y + line.c) +
          2 * (line.a * second.x + line.b * second.y + line.c) := by ring1
      _ = 0 := by
        rw [firstOnLine, secondOnLine]
        ring1
  have testPointZero :
      circle.evaluate (thalesPoint 2 first second) = 0 :=
    allLinePoints (thalesPoint 2 first second) testPointOnLine
  have firstZero : circle.evaluate first = 0 := firstIntersection.2
  have secondZero : circle.evaluate second = 0 := secondIntersection.2
  have factorNonzero : (2 : K) * (2 - 1) ≠ 0 := by
    intro factorZero
    apply twoNonzero
    calc
      (2 : K) = 2 * (2 - 1) := by ring1
      _ = 0 := factorZero
  have restrictionProductZero :
      ((2 : K) * (2 - 1)) *
        circle.lineRestrictionQuadratic first second = 0 := by
    calc
      ((2 : K) * (2 - 1)) *
          circle.lineRestrictionQuadratic first second =
        circle.evaluate (thalesPoint 2 first second) := by
          rw [evaluate_thalesPoint, firstZero, secondZero]
          ring1
      _ = 0 := testPointZero
  have restrictionZero :=
    eq_zero_of_mul_eq_zero_left factorNonzero restrictionProductZero
  have restrictionFormula :
      circle.lineRestrictionQuadratic first second =
        circle.d * quadrance first second := by
    unfold lineRestrictionQuadratic quadrance
    rw [presentation.1, ← presentation.2.1]
    ring1
  have restrictionNonzero :
      circle.lineRestrictionQuadratic first second ≠ 0 := by
    rw [restrictionFormula]
    exact RFAP.ExplicitField.mul_ne_zero presentation.2.2.1
      separationNonzero
  exact restrictionNonzero restrictionZero

end Conic

end DivineProportions
