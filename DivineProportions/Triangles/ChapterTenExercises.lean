import DivineProportions.Triangles.ChapterFiveExercises
import DivineProportions.Triangles.IsoscelesMedian
import DivineProportions.Triangles.Similarity

/-!
# Divine Proportions, Chapter 10 further exercises

This module contains the equilateral centroid calculations, the unit-
quadrance existence criterion, and the corrected right-altitude formulas.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_left
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : factor * left = factor * right) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = 1 * left := by rw [one_mul]
    _ = (factor * factor⁻¹) * left := by rw [factorCancel]
    _ = factor⁻¹ * (factor * left) := by ring1
    _ = factor⁻¹ * (factor * right) := by rw [productsEqual]
    _ = (factor * factor⁻¹) * right := by ring1
    _ = right := by rw [factorCancel, one_mul]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  apply eq_of_mul_eq_mul_left factorNonzero
  calc
    factor * left = left * factor := by ring1
    _ = right * factor := productsEqual
    _ = factor * right := by ring1

private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel rightDenominator rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
      rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
      rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

/-- Exercise 10.4.  The source's three centroid/median quadrances follow from
the finite median identity and the already-proved `4/9,1/9` centroid ratios. -/
theorem exercise_10_4
    (first second third : Point K) (q : K)
    (twoNonzero : (2 : K) ≠ 0) (threeNonzero : (3 : K) ≠ 0)
    (firstQuadrance : quadrance second third = q)
    (secondQuadrance : quadrance first third = q)
    (thirdQuadrance : quadrance first second = q) :
    quadrance third (centroidPoint first second third) = q / 3 ∧
      quadrance (centroidPoint first second third)
          (midpoint first second) = q / 12 ∧
      quadrance third (midpoint first second) = 3 * q / 4 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have nineNonzero : (9 : K) ≠ 0 := by
    have squareNonzero :=
      RFAP.ExplicitField.mul_ne_zero threeNonzero threeNonzero
    simpa only [show (9 : K) = 3 * 3 by ring1] using squareNonzero
  have twelveNonzero : (12 : K) ≠ 0 := by
    simpa only [show (12 : K) = 4 * 3 by ring1] using
      RFAP.ExplicitField.mul_ne_zero fourNonzero threeNonzero
  let medianQuadrance := quadrance third (midpoint first second)
  have medianCleared : medianQuadrance * 4 = 3 * q := by
    have cleared := median_quadrance_cleared first second third twoNonzero
    change quadrance (midpoint first second) third * 4 =
      2 * quadrance first third + 2 * quadrance second third -
        quadrance first second at cleared
    calc
      medianQuadrance * 4 =
          quadrance (midpoint first second) third * 4 := by
        unfold medianQuadrance
        rw [quadrance_symm third (midpoint first second)]
      _ = 2 * quadrance first third + 2 * quadrance second third -
          quadrance first second := cleared
      _ = 3 * q := by
        rw [firstQuadrance, secondQuadrance, thirdQuadrance]
        ring1
  have medianValue : medianQuadrance = 3 * q / 4 := by
    apply eq_of_mul_eq_mul_right fourNonzero
    calc
      medianQuadrance * 4 = 3 * q := medianCleared
      _ = (3 * q / 4) * 4 :=
        (RFAP.ExplicitField.div_mul_cancel (3 * q) fourNonzero).symm
  have centroidRatios := exercise_5_2 third first second twoNonzero
    threeNonzero
  rw [centroidPoint_cyclic_right first second third] at centroidRatios
  have vertexCentroid :
      quadrance third (centroidPoint first second third) = q / 3 := by
    calc
      quadrance third (centroidPoint first second third) =
          4 * medianQuadrance / 9 := centroidRatios.1
      _ = q / 3 := by
        apply div_eq_div_of_cross_mul nineNonzero threeNonzero
        calc
          (4 * medianQuadrance) * 3 =
              3 * (medianQuadrance * 4) := by ring1
          _ = 3 * (3 * q) := by rw [medianCleared]
          _ = q * 9 := by ring1
  have centroidMidpoint :
      quadrance (centroidPoint first second third)
          (midpoint first second) = q / 12 := by
    calc
      quadrance (centroidPoint first second third)
          (midpoint first second) = medianQuadrance / 9 :=
        centroidRatios.2.1
      _ = q / 12 := by
        apply div_eq_div_of_cross_mul nineNonzero twelveNonzero
        calc
          medianQuadrance * 12 =
              (medianQuadrance * 4) * 3 := by ring1
          _ = (3 * q) * 3 := by rw [medianCleared]
          _ = q * 9 := by ring1
  exact ⟨vertexCentroid, centroidMidpoint, medianValue⟩

/-- Exercise 10.5.  A noncollinear equilateral triangle with unit common
quadrance exists exactly when `3` is displayed as a nonzero square. -/
theorem exercise_10_5 [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    HasTriangleQuadrances (1 : K) 1 1 ↔ IsNonzeroSquare (3 : K) := by
  have criterion := triangle_quadrea (1 : K) 1 1 twoNonzero
  constructor
  · intro triangle
    have data := criterion.1 triangle
    rcases data.2.2.2.2 with ⟨root, rootNonzero, square⟩
    refine ⟨root, rootNonzero, ?_⟩
    calc
      (3 : K) = archimedesFunction 1 1 1 := by
        unfold archimedesFunction
        ring1
      _ = root ^ 2 := square
  · rintro ⟨root, rootNonzero, square⟩
    apply criterion.2
    refine ⟨Or.inl one_ne_zero,
      ⟨1, 0, by ring1⟩, ⟨1, 0, by ring1⟩,
      ⟨1, 0, by ring1⟩, root, rootNonzero, ?_⟩
    calc
      archimedesFunction (1 : K) 1 1 = 3 := by
        unfold archimedesFunction
        ring1
      _ = root ^ 2 := square

/-- The explicit foot from the third vertex to the opposite side. -/
def NonNullTriangle.thirdAltitudeFoot [DecidableEq K]
    (triangle : NonNullTriangle K) : Point K :=
  altitudeFoot triangle.third
    (lineThrough triangle.first triangle.second
      triangle.firstSecondDistinct)
    triangle.firstSecondNonNull

/-- Exercise 10.6, corrected.  Under the source convention
`Q₁=Q(A₂,A₃)`, `Q₂=Q(A₁,A₃)`, the printed first two
numerators are interchanged: `Q(A₁,F)=Q₂²/Q₃` and
`Q(A₂,F)=Q₁²/Q₃`. -/
theorem exercise_10_6_corrected [DecidableEq K]
    (triangle : NonNullTriangle K) (twoNonzero : (2 : K) ≠ 0)
    (rightAtThird :
      (lineThrough triangle.first triangle.third
          triangle.firstThirdDistinct).Perpendicular
        (lineThrough triangle.second triangle.third
          triangle.secondThirdDistinct)) :
    quadrance triangle.first triangle.thirdAltitudeFoot =
        triangle.quadrances.second ^ 2 / triangle.quadrances.third ∧
      quadrance triangle.second triangle.thirdAltitudeFoot =
        triangle.quadrances.first ^ 2 / triangle.quadrances.third ∧
      quadrance triangle.third triangle.thirdAltitudeFoot =
        triangle.quadrances.first * triangle.quadrances.second /
          triangle.quadrances.third := by
  let base := lineThrough triangle.first triangle.second
    triangle.firstSecondDistinct
  let foot := triangle.thirdAltitudeFoot
  have baseContainsFirst : base.Contains triangle.first := by
    unfold base
    exact lineThrough_contains_first triangle.first triangle.second
      triangle.firstSecondDistinct
  have baseContainsSecond : base.Contains triangle.second := by
    unfold base
    exact lineThrough_contains_second triangle.first triangle.second
      triangle.firstSecondDistinct
  have footOnBase : base.Contains foot := by
    unfold foot NonNullTriangle.thirdAltitudeFoot base
    exact altitudeFoot_on_line triangle.third
      (lineThrough triangle.first triangle.second
        triangle.firstSecondDistinct) triangle.firstSecondNonNull
  have footOnAltitude :
      (altitudeThrough triangle.third base).Contains foot := by
    unfold foot NonNullTriangle.thirdAltitudeFoot base
    exact altitudeFoot_on_altitude triangle.third
      (lineThrough triangle.first triangle.second
        triangle.firstSecondDistinct) triangle.firstSecondNonNull
  have thirdFootDistinct : triangle.third ≠ foot := by
    intro equalPoints
    apply triangle.notCollinear
    refine ⟨base, baseContainsFirst, baseContainsSecond, ?_⟩
    rw [equalPoints]
    exact footOnBase
  have cevianParallelAltitude :
      (lineThrough triangle.third foot thirdFootDistinct).Parallel
        (altitudeThrough triangle.third base) :=
    lineThrough_parallel_of_contains (altitudeThrough triangle.third base)
      triangle.third foot thirdFootDistinct
      (altitudeThrough_contains triangle.third base) footOnAltitude
  have firstPythagoras :
      quadrance triangle.third foot + quadrance triangle.first foot =
        quadrance triangle.first triangle.third := by
    by_cases footIsFirst : foot = triangle.first
    · rw [footIsFirst, quadrance_self, add_zero,
        quadrance_symm triangle.third triangle.first]
    · have firstFootDistinct : triangle.first ≠ foot := by
        intro equalPoints
        exact footIsFirst equalPoints.symm
      have firstFootParallel :
          (lineThrough triangle.first foot firstFootDistinct).Parallel base :=
        lineThrough_parallel_of_contains base triangle.first foot
          firstFootDistinct baseContainsFirst footOnBase
      have firstFootPerpendicularAltitude :
          (lineThrough triangle.first foot firstFootDistinct).Perpendicular
            (altitudeThrough triangle.third base) :=
        perpendicular_of_parallel_left base
          (lineThrough triangle.first foot firstFootDistinct)
          (altitudeThrough triangle.third base)
          (Line.parallel_symm firstFootParallel)
          (Line.perpendicular_symm
            (altitudeThrough_perpendicular triangle.third base))
      have cevianPerpendicularFirstFoot :
          (lineThrough triangle.third foot thirdFootDistinct).Perpendicular
            (lineThrough triangle.first foot firstFootDistinct) :=
        perpendicular_of_parallel_left (altitudeThrough triangle.third base)
          (lineThrough triangle.third foot thirdFootDistinct)
          (lineThrough triangle.first foot firstFootDistinct)
          (Line.parallel_symm cevianParallelAltitude)
          (Line.perpendicular_symm firstFootPerpendicularAltitude)
      exact (pythagoras_iff_perpendicular triangle.first triangle.third foot
        firstFootDistinct thirdFootDistinct twoNonzero).2
          (Line.perpendicular_symm cevianPerpendicularFirstFoot)
  have secondPythagoras :
      quadrance triangle.third foot + quadrance triangle.second foot =
        quadrance triangle.second triangle.third := by
    by_cases footIsSecond : foot = triangle.second
    · rw [footIsSecond, quadrance_self, add_zero,
        quadrance_symm triangle.third triangle.second]
    · have secondFootDistinct : triangle.second ≠ foot := by
        intro equalPoints
        exact footIsSecond equalPoints.symm
      have secondFootParallel :
          (lineThrough triangle.second foot secondFootDistinct).Parallel base :=
        lineThrough_parallel_of_contains base triangle.second foot
          secondFootDistinct baseContainsSecond footOnBase
      have secondFootPerpendicularAltitude :
          (lineThrough triangle.second foot secondFootDistinct).Perpendicular
            (altitudeThrough triangle.third base) :=
        perpendicular_of_parallel_left base
          (lineThrough triangle.second foot secondFootDistinct)
          (altitudeThrough triangle.third base)
          (Line.parallel_symm secondFootParallel)
          (Line.perpendicular_symm
            (altitudeThrough_perpendicular triangle.third base))
      have cevianPerpendicularSecondFoot :
          (lineThrough triangle.third foot thirdFootDistinct).Perpendicular
            (lineThrough triangle.second foot secondFootDistinct) :=
        perpendicular_of_parallel_left (altitudeThrough triangle.third base)
          (lineThrough triangle.third foot thirdFootDistinct)
          (lineThrough triangle.second foot secondFootDistinct)
          (Line.parallel_symm cevianParallelAltitude)
          (Line.perpendicular_symm secondFootPerpendicularAltitude)
      exact (pythagoras_iff_perpendicular triangle.second triangle.third foot
        secondFootDistinct thirdFootDistinct twoNonzero).2
          (Line.perpendicular_symm cevianPerpendicularSecondFoot)
  have fourNonzero : (4 : K) ≠ 0 := by
    have squareNonzero :=
      RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using squareNonzero
  have rightArea := right_triangle_quadrea triangle.first triangle.second
    triangle.third triangle.firstThirdDistinct
    triangle.secondThirdDistinct twoNonzero rightAtThird
  have coordinateArea :=
    quadrea_coordinate_formula triangle.first triangle.second triangle.third
  have determinantSquare :
      pointDeterminant triangle.first triangle.second triangle.third ^ 2 =
        triangle.quadrances.first * triangle.quadrances.second := by
    apply eq_of_mul_eq_mul_left fourNonzero
    calc
      4 * pointDeterminant triangle.first triangle.second triangle.third ^ 2 =
          quadrea triangle.first triangle.second triangle.third :=
        coordinateArea.symm
      _ = 4 * quadrance triangle.second triangle.third *
          quadrance triangle.first triangle.third := rightArea
      _ = 4 *
          (triangle.quadrances.first * triangle.quadrances.second) := by
        unfold NonNullTriangle.quadrances triangleQuadrances
        ring1
  have lineValueSquare :
      (base.a * triangle.third.x + base.b * triangle.third.y + base.c) ^ 2 =
        pointDeterminant triangle.first triangle.second triangle.third ^ 2 := by
    unfold base lineThrough pointDeterminant
    ring1
  have heightFormula :
      quadrance triangle.third foot =
        triangle.quadrances.first * triangle.quadrances.second /
          triangle.quadrances.third := by
    have distanceFormula :=
      pointLineQuadrance_formula triangle.third base
        triangle.firstSecondNonNull
    change quadrance triangle.third foot =
      (base.a * triangle.third.x + base.b * triangle.third.y + base.c) ^ 2 /
        lineNorm base at distanceFormula
    calc
      quadrance triangle.third foot =
          (base.a * triangle.third.x + base.b * triangle.third.y +
            base.c) ^ 2 / lineNorm base := distanceFormula
      _ = pointDeterminant triangle.first triangle.second triangle.third ^ 2 /
          triangle.quadrances.third := by
        rw [lineValueSquare]
        unfold base NonNullTriangle.quadrances triangleQuadrances
        rw [lineThrough_norm_eq_quadrance]
      _ = triangle.quadrances.first * triangle.quadrances.second /
          triangle.quadrances.third := by rw [determinantSquare]
  have originalPythagoras :
      triangle.quadrances.first + triangle.quadrances.second =
        triangle.quadrances.third :=
    (pythagoras_iff_perpendicular triangle.first triangle.second
      triangle.third triangle.firstThirdDistinct
      triangle.secondThirdDistinct twoNonzero).2 rightAtThird
  change quadrance triangle.third foot + quadrance triangle.first foot =
    triangle.quadrances.second at firstPythagoras
  change quadrance triangle.third foot + quadrance triangle.second foot =
    triangle.quadrances.first at secondPythagoras
  have firstProjection :
      quadrance triangle.first foot =
        triangle.quadrances.second ^ 2 / triangle.quadrances.third := by
    apply eq_of_mul_eq_mul_right triangle.thirdQuadranceNonzero
    calc
      quadrance triangle.first foot * triangle.quadrances.third =
          (triangle.quadrances.second - quadrance triangle.third foot) *
            triangle.quadrances.third := by
        rw [← firstPythagoras]
        ring1
      _ = (triangle.quadrances.second -
            triangle.quadrances.first * triangle.quadrances.second /
              triangle.quadrances.third) * triangle.quadrances.third := by
        rw [heightFormula]
      _ = triangle.quadrances.second * triangle.quadrances.third -
          triangle.quadrances.first * triangle.quadrances.second := by
        calc
          (triangle.quadrances.second -
                triangle.quadrances.first * triangle.quadrances.second /
                  triangle.quadrances.third) *
              triangle.quadrances.third =
            triangle.quadrances.second * triangle.quadrances.third -
              (triangle.quadrances.first * triangle.quadrances.second /
                triangle.quadrances.third) *
                triangle.quadrances.third := by ring1
          _ = triangle.quadrances.second * triangle.quadrances.third -
              triangle.quadrances.first * triangle.quadrances.second := by
            rw [RFAP.ExplicitField.div_mul_cancel _
              triangle.thirdQuadranceNonzero]
      _ = triangle.quadrances.second ^ 2 := by
        rw [← originalPythagoras]
        ring1
      _ = (triangle.quadrances.second ^ 2 /
          triangle.quadrances.third) * triangle.quadrances.third :=
        (RFAP.ExplicitField.div_mul_cancel _
          triangle.thirdQuadranceNonzero).symm
  have secondProjection :
      quadrance triangle.second foot =
        triangle.quadrances.first ^ 2 / triangle.quadrances.third := by
    apply eq_of_mul_eq_mul_right triangle.thirdQuadranceNonzero
    calc
      quadrance triangle.second foot * triangle.quadrances.third =
          (triangle.quadrances.first - quadrance triangle.third foot) *
            triangle.quadrances.third := by
        rw [← secondPythagoras]
        ring1
      _ = (triangle.quadrances.first -
            triangle.quadrances.first * triangle.quadrances.second /
              triangle.quadrances.third) * triangle.quadrances.third := by
        rw [heightFormula]
      _ = triangle.quadrances.first * triangle.quadrances.third -
          triangle.quadrances.first * triangle.quadrances.second := by
        calc
          (triangle.quadrances.first -
                triangle.quadrances.first * triangle.quadrances.second /
                  triangle.quadrances.third) *
              triangle.quadrances.third =
            triangle.quadrances.first * triangle.quadrances.third -
              (triangle.quadrances.first * triangle.quadrances.second /
                triangle.quadrances.third) *
                triangle.quadrances.third := by ring1
          _ = triangle.quadrances.first * triangle.quadrances.third -
              triangle.quadrances.first * triangle.quadrances.second := by
            rw [RFAP.ExplicitField.div_mul_cancel _
              triangle.thirdQuadranceNonzero]
      _ = triangle.quadrances.first ^ 2 := by
        rw [← originalPythagoras]
        ring1
      _ = (triangle.quadrances.first ^ 2 /
          triangle.quadrances.third) * triangle.quadrances.third :=
        (RFAP.ExplicitField.div_mul_cancel _
          triangle.thirdQuadranceNonzero).symm
  exact ⟨firstProjection, secondProjection, heightFormula⟩

end DivineProportions
