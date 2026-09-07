import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Triangles.Right

/-!
# Divine Proportions, Chapter 10: the isosceles median

The line in Theorem 67 is represented by its vertex and its displayed
intersection with the opposite side.  This keeps all three conditions—altitude,
median, and equal-spread vertex bisector—finite and executable.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_zero_of_mul_eq_zero_left [DecidableEq K]
    {left right : K} (leftNonzero : left ≠ 0)
    (productZero : left * right = 0) : right = 0 := by
  by_cases rightZero : right = 0
  · exact rightZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero leftNonzero rightZero) productZero)

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

private theorem target_sub_half_sum_mul_two
    (left right target : K) (twoNonzero : (2 : K) ≠ 0) :
    (target - (left + right) / 2) * 2 =
      2 * target - left - right := by
  calc
    (target - (left + right) / 2) * 2 =
        target * 2 - ((left + right) / 2) * 2 := by ring1
    _ = target * 2 - (left + right) := by
      rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
    _ = 2 * target - left - right := by ring1

private theorem half_sum_sub_target_mul_two
    (left right target : K) (twoNonzero : (2 : K) ≠ 0) :
    ((left + right) / 2 - target) * 2 =
      left + right - 2 * target := by
  calc
    ((left + right) / 2 - target) * 2 =
        ((left + right) / 2) * 2 - target * 2 := by ring1
    _ = left + right - target * 2 := by
      rw [RFAP.ExplicitField.div_mul_cancel _ twoNonzero]
    _ = left + right - 2 * target := by ring1

theorem lineThrough_parallel_of_contains [DecidableEq K]
    (line : Line K) (first second : Point K) (distinct : first ≠ second)
    (containsFirst : line.Contains first)
    (containsSecond : line.Contains second) :
    (lineThrough first second distinct).Parallel line := by
  unfold Line.Contains at containsFirst containsSecond
  unfold Line.Parallel lineThrough
  calc
    (first.y - second.y) * line.b -
        line.a * (second.x - first.x) =
      (line.a * first.x + line.b * first.y + line.c) -
        (line.a * second.x + line.b * second.y + line.c) := by ring1
    _ = 0 := by rw [containsFirst, containsSecond]; ring1

theorem perpendicular_of_parallel_left [DecidableEq K]
    (source target other : Line K) (parallel : source.Parallel target)
    (sourcePerpendicular : source.Perpendicular other) :
    target.Perpendicular other := by
  rcases direction_scale_of_parallel source target parallel with
    ⟨scale, _scaleNonzero, targetA, targetB⟩
  unfold Line.Perpendicular at sourcePerpendicular ⊢
  rw [targetA, targetB]
  calc
    scale * source.a * other.a + scale * source.b * other.b =
        scale * (source.a * other.a + source.b * other.b) := by ring1
    _ = 0 := by rw [sourcePerpendicular]; ring1

/-- In an isosceles triangle, a displayed cevian is perpendicular to the base
exactly when its intersection with the base is the midpoint.  This is the
altitude/median half of Theorem 67. -/
theorem isosceles_altitude_iff_midpoint [DecidableEq K]
    (first second vertex foot : Point K)
    (firstSecondDistinct : first ≠ second)
    (vertexFootDistinct : vertex ≠ foot)
    (twoNonzero : (2 : K) ≠ 0)
    (baseNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (footOnBase :
      (lineThrough first second firstSecondDistinct).Contains foot)
    (equalVertexQuadrances :
      quadrance vertex first = quadrance vertex second) :
    (lineThrough vertex foot vertexFootDistinct).Perpendicular
        (lineThrough first second firstSecondDistinct) ↔
      foot = midpoint first second := by
  let base := lineThrough first second firstSecondDistinct
  let cevian := lineThrough vertex foot vertexFootDistinct
  have baseContainsFirst : base.Contains first := by
    unfold base
    exact lineThrough_contains_first first second firstSecondDistinct
  have baseContainsSecond : base.Contains second := by
    unfold base
    exact lineThrough_contains_second first second firstSecondDistinct
  constructor
  · intro perpendicular
    have firstPythagoras :
        quadrance vertex foot + quadrance first foot =
          quadrance first vertex := by
      by_cases footIsFirst : foot = first
      · subst foot
        rw [quadrance_self, add_zero, quadrance_symm vertex first]
      · have firstFootDistinct : first ≠ foot := by
          intro equalPoints
          exact footIsFirst equalPoints.symm
        have firstFootParallel :
            (lineThrough first foot firstFootDistinct).Parallel base :=
          lineThrough_parallel_of_contains base first foot firstFootDistinct
            baseContainsFirst footOnBase
        have firstFootPerpendicular :
            (lineThrough first foot firstFootDistinct).Perpendicular cevian :=
          perpendicular_of_parallel_left base
            (lineThrough first foot firstFootDistinct) cevian
            (Line.parallel_symm firstFootParallel)
            (Line.perpendicular_symm perpendicular)
        exact (pythagoras_iff_perpendicular first vertex foot
          firstFootDistinct vertexFootDistinct twoNonzero).2
            firstFootPerpendicular
    have secondPythagoras :
        quadrance vertex foot + quadrance second foot =
          quadrance second vertex := by
      by_cases footIsSecond : foot = second
      · subst foot
        rw [quadrance_self, add_zero, quadrance_symm vertex second]
      · have secondFootDistinct : second ≠ foot := by
          intro equalPoints
          exact footIsSecond equalPoints.symm
        have secondFootParallel :
            (lineThrough second foot secondFootDistinct).Parallel base :=
          lineThrough_parallel_of_contains base second foot secondFootDistinct
            baseContainsSecond footOnBase
        have secondFootPerpendicular :
            (lineThrough second foot secondFootDistinct).Perpendicular cevian :=
          perpendicular_of_parallel_left base
            (lineThrough second foot secondFootDistinct) cevian
            (Line.parallel_symm secondFootParallel)
            (Line.perpendicular_symm perpendicular)
        exact (pythagoras_iff_perpendicular second vertex foot
          secondFootDistinct vertexFootDistinct twoNonzero).2
            secondFootPerpendicular
    have equalReversedVertexQuadrances :
        quadrance first vertex = quadrance second vertex := by
      calc
        quadrance first vertex = quadrance vertex first :=
          quadrance_symm first vertex
        _ = quadrance vertex second := equalVertexQuadrances
        _ = quadrance second vertex := quadrance_symm vertex second
    have equalFootQuadrances :
        quadrance foot first = quadrance foot second := by
      calc
        quadrance foot first = quadrance first foot :=
          quadrance_symm foot first
        _ = quadrance first vertex - quadrance vertex foot := by
          rw [← firstPythagoras]
          ring1
        _ = quadrance second vertex - quadrance vertex foot := by
          rw [equalReversedVertexQuadrances]
        _ = quadrance second foot := by
          rw [← secondPythagoras]
          ring1
        _ = quadrance foot second := quadrance_symm second foot
    exact midpoint_unique_of_equal_quadrance first second foot
      firstSecondDistinct twoNonzero baseNonNull footOnBase
      equalFootQuadrances
  · intro footIsMidpoint
    subst foot
    have vertexOnBisector :
        (perpendicularBisector first second firstSecondDistinct).Contains
          vertex :=
      (equal_quadrance_iff_perpendicularBisector_contains first second vertex
        firstSecondDistinct twoNonzero).1 equalVertexQuadrances
    have midpointOnBisector :
        (perpendicularBisector first second firstSecondDistinct).Contains
          (midpoint first second) :=
      perpendicularBisector_contains_midpoint first second firstSecondDistinct
    have cevianParallelBisector :
        (lineThrough vertex (midpoint first second)
          vertexFootDistinct).Parallel
            (perpendicularBisector first second firstSecondDistinct) :=
      lineThrough_parallel_of_contains
        (perpendicularBisector first second firstSecondDistinct)
        vertex (midpoint first second) vertexFootDistinct
        vertexOnBisector midpointOnBisector
    exact perpendicular_of_parallel_left
      (perpendicularBisector first second firstSecondDistinct)
      (lineThrough vertex (midpoint first second) vertexFootDistinct)
      (lineThrough first second firstSecondDistinct)
      (Line.parallel_symm cevianParallelBisector)
      (perpendicularBisector_perpendicular first second firstSecondDistinct)

/-- The median of an isosceles triangle makes equal spreads with its two
equal sides. -/
theorem isosceles_midpoint_equal_spreads [DecidableEq K]
    (first second vertex : Point K)
    (vertexFirstDistinct : vertex ≠ first)
    (vertexSecondDistinct : vertex ≠ second)
    (vertexMidpointDistinct : vertex ≠ midpoint first second)
    (sideFirstNonNull :
      ¬ (lineThrough vertex first vertexFirstDistinct).IsNull)
    (sideSecondNonNull :
      ¬ (lineThrough vertex second vertexSecondDistinct).IsNull)
    (medianNonNull :
      ¬ (lineThrough vertex (midpoint first second)
        vertexMidpointDistinct).IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (equalVertexQuadrances :
      quadrance vertex first = quadrance vertex second) :
    spread (lineThrough vertex first vertexFirstDistinct)
        (lineThrough vertex (midpoint first second) vertexMidpointDistinct)
        sideFirstNonNull medianNonNull =
      spread (lineThrough vertex second vertexSecondDistinct)
        (lineThrough vertex (midpoint first second) vertexMidpointDistinct)
        sideSecondNonNull medianNonNull := by
  have determinantOpposite :
      (lineThrough vertex first vertexFirstDistinct).a *
          (lineThrough vertex (midpoint first second)
            vertexMidpointDistinct).b -
        (lineThrough vertex (midpoint first second)
            vertexMidpointDistinct).a *
          (lineThrough vertex first vertexFirstDistinct).b =
      -((lineThrough vertex second vertexSecondDistinct).a *
          (lineThrough vertex (midpoint first second)
            vertexMidpointDistinct).b -
        (lineThrough vertex (midpoint first second)
            vertexMidpointDistinct).a *
          (lineThrough vertex second vertexSecondDistinct).b) := by
    apply eq_of_mul_eq_mul_right twoNonzero
    unfold lineThrough midpoint
    calc
      ((vertex.y - first.y) *
            ((first.x + second.x) / 2 - vertex.x) -
          (vertex.y - (first.y + second.y) / 2) *
            (first.x - vertex.x)) * 2 =
        (vertex.y - first.y) *
            (((first.x + second.x) / 2 - vertex.x) * 2) -
          ((vertex.y - (first.y + second.y) / 2) * 2) *
            (first.x - vertex.x) := by ring1
      _ = (vertex.y - first.y) *
            (first.x + second.x - 2 * vertex.x) -
          (2 * vertex.y - first.y - second.y) *
            (first.x - vertex.x) := by
        rw [half_sum_sub_target_mul_two first.x second.x vertex.x
          twoNonzero,
          target_sub_half_sum_mul_two first.y second.y vertex.y
            twoNonzero]
      _ = -((vertex.y - second.y) *
            (first.x + second.x - 2 * vertex.x) -
          (2 * vertex.y - first.y - second.y) *
            (second.x - vertex.x)) := by ring1
      _ = (-((vertex.y - second.y) *
            ((first.x + second.x) / 2 - vertex.x) -
          (vertex.y - (first.y + second.y) / 2) *
            (second.x - vertex.x))) * 2 := by
        rw [show
            (first.x + second.x - 2 * vertex.x) =
              ((first.x + second.x) / 2 - vertex.x) * 2 by
          exact (half_sum_sub_target_mul_two first.x second.x vertex.x
            twoNonzero).symm,
          show
            (2 * vertex.y - first.y - second.y) =
              (vertex.y - (first.y + second.y) / 2) * 2 by
          exact (target_sub_half_sum_mul_two first.y second.y vertex.y
            twoNonzero).symm]
        ring1
  unfold spread
  rw [show
      ((lineThrough vertex first vertexFirstDistinct).a *
          (lineThrough vertex (midpoint first second)
            vertexMidpointDistinct).b -
        (lineThrough vertex (midpoint first second)
            vertexMidpointDistinct).a *
          (lineThrough vertex first vertexFirstDistinct).b) ^ 2 =
      ((lineThrough vertex second vertexSecondDistinct).a *
          (lineThrough vertex (midpoint first second)
            vertexMidpointDistinct).b -
        (lineThrough vertex (midpoint first second)
            vertexMidpointDistinct).a *
          (lineThrough vertex second vertexSecondDistinct).b) ^ 2 by
        rw [determinantOpposite]
        ring1]
  rw [lineThrough_norm_eq_quadrance vertex first vertexFirstDistinct,
    lineThrough_norm_eq_quadrance vertex second vertexSecondDistinct,
    equalVertexQuadrances]

/-- A cevian of a noncollinear isosceles triangle is an equal-spread vertex
bisector exactly when it meets the opposite side at its midpoint. -/
theorem isosceles_bisector_iff_midpoint [Nontrivial K] [DecidableEq K]
    (first second vertex foot : Point K)
    (firstSecondDistinct : first ≠ second)
    (vertexFirstDistinct : vertex ≠ first)
    (vertexSecondDistinct : vertex ≠ second)
    (vertexFootDistinct : vertex ≠ foot)
    (twoNonzero : (2 : K) ≠ 0)
    (sideFirstNonNull :
      ¬ (lineThrough vertex first vertexFirstDistinct).IsNull)
    (sideSecondNonNull :
      ¬ (lineThrough vertex second vertexSecondDistinct).IsNull)
    (cevianNonNull :
      ¬ (lineThrough vertex foot vertexFootDistinct).IsNull)
    (notCollinear : ¬ Collinear first second vertex)
    (footOnBase :
      (lineThrough first second firstSecondDistinct).Contains foot)
    (equalVertexQuadrances :
      quadrance vertex first = quadrance vertex second) :
    spread (lineThrough vertex first vertexFirstDistinct)
        (lineThrough vertex foot vertexFootDistinct)
        sideFirstNonNull cevianNonNull =
      spread (lineThrough vertex second vertexSecondDistinct)
        (lineThrough vertex foot vertexFootDistinct)
        sideSecondNonNull cevianNonNull ↔
      foot = midpoint first second := by
  let sideFirst := lineThrough vertex first vertexFirstDistinct
  let sideSecond := lineThrough vertex second vertexSecondDistinct
  let cevian := lineThrough vertex foot vertexFootDistinct
  let dFirst := sideFirst.a * cevian.b - cevian.a * sideFirst.b
  let dSecond := sideSecond.a * cevian.b - cevian.a * sideSecond.b
  have determinantNonzero : pointDeterminant first second vertex ≠ 0 := by
    intro determinantZero
    exact notCollinear
      ((collinear_iff_pointDeterminant_eq_zero first second vertex).2
        determinantZero)
  constructor
  · intro equalSpreads
    have sideNormEqual : lineNorm sideFirst = lineNorm sideSecond := by
      unfold sideFirst sideSecond
      rw [lineThrough_norm_eq_quadrance vertex first vertexFirstDistinct,
        lineThrough_norm_eq_quadrance vertex second vertexSecondDistinct,
        equalVertexQuadrances]
    have commonDenominatorNonzero :
        lineNorm sideSecond * lineNorm cevian ≠ 0 :=
      RFAP.ExplicitField.mul_ne_zero sideSecondNonNull cevianNonNull
    have equalNumeratorSquares : dFirst ^ 2 = dSecond ^ 2 := by
      unfold spread at equalSpreads
      change dFirst ^ 2 / (lineNorm sideFirst * lineNorm cevian) =
        dSecond ^ 2 / (lineNorm sideSecond * lineNorm cevian) at equalSpreads
      rw [sideNormEqual] at equalSpreads
      have cleared := congrArg
        (fun value : K => value * (lineNorm sideSecond * lineNorm cevian))
        equalSpreads
      rw [RFAP.ExplicitField.div_mul_cancel _ commonDenominatorNonzero,
        RFAP.ExplicitField.div_mul_cancel _ commonDenominatorNonzero]
        at cleared
      exact cleared
    have factorZero : (dFirst - dSecond) * (dFirst + dSecond) = 0 := by
      calc
        (dFirst - dSecond) * (dFirst + dSecond) =
            dFirst ^ 2 - dSecond ^ 2 := by ring1
        _ = 0 := by rw [equalNumeratorSquares]; ring1
    have footOnBaseExpanded :
        (first.y - second.y) * foot.x +
            (second.x - first.x) * foot.y +
            (first.x * second.y - second.x * first.y) = 0 := by
      exact footOnBase
    have determinantDifference :
        dFirst - dSecond = pointDeterminant first second vertex := by
      unfold dFirst dSecond sideFirst sideSecond cevian
      simp only [lineThrough_a, lineThrough_b]
      calc
        ((vertex.y - first.y) * (foot.x - vertex.x) -
              (vertex.y - foot.y) * (first.x - vertex.x)) -
            ((vertex.y - second.y) * (foot.x - vertex.x) -
              (vertex.y - foot.y) * (second.x - vertex.x)) =
          pointDeterminant first second vertex -
            ((first.y - second.y) * foot.x +
              (second.x - first.x) * foot.y +
              (first.x * second.y - second.x * first.y)) := by
                unfold pointDeterminant
                ring1
        _ = pointDeterminant first second vertex := by
          rw [footOnBaseExpanded]
          ring1
    have differenceNonzero : dFirst - dSecond ≠ 0 := by
      rw [determinantDifference]
      exact determinantNonzero
    have determinantSumZero : dFirst + dSecond = 0 := by
      by_cases sumZero : dFirst + dSecond = 0
      · exact sumZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero differenceNonzero sumZero)
            factorZero)
    have xProductZero :
        pointDeterminant first second vertex *
          (2 * foot.x - first.x - second.x) = 0 := by
      calc
        pointDeterminant first second vertex *
            (2 * foot.x - first.x - second.x) =
          (second.x - first.x) * (dFirst + dSecond) -
            (first.x + second.x - 2 * vertex.x) *
              ((first.y - second.y) * foot.x +
                (second.x - first.x) * foot.y +
                (first.x * second.y - second.x * first.y)) := by
            unfold dFirst dSecond sideFirst sideSecond cevian
            simp only [lineThrough_a, lineThrough_b]
            unfold pointDeterminant
            ring1
        _ = 0 := by rw [determinantSumZero, footOnBaseExpanded]; ring1
    have yProductZero :
        pointDeterminant first second vertex *
          (2 * foot.y - first.y - second.y) = 0 := by
      calc
        pointDeterminant first second vertex *
            (2 * foot.y - first.y - second.y) =
          (2 * vertex.y - first.y - second.y) *
              ((first.y - second.y) * foot.x +
                (second.x - first.x) * foot.y +
                (first.x * second.y - second.x * first.y)) -
            (first.y - second.y) * (dFirst + dSecond) := by
            unfold dFirst dSecond sideFirst sideSecond cevian
            simp only [lineThrough_a, lineThrough_b]
            unfold pointDeterminant
            ring1
        _ = 0 := by rw [determinantSumZero, footOnBaseExpanded]; ring1
    have xErrorZero : 2 * foot.x - first.x - second.x = 0 :=
      eq_zero_of_mul_eq_zero_left determinantNonzero xProductZero
    have yErrorZero : 2 * foot.y - first.y - second.y = 0 :=
      eq_zero_of_mul_eq_zero_left determinantNonzero yProductZero
    apply Point.ext
    · change foot.x = (first.x + second.x) / 2
      apply eq_of_mul_eq_mul_right twoNonzero
      calc
        foot.x * 2 = 2 * foot.x := by ring1
        _ = first.x + second.x := by
          calc
            2 * foot.x =
                (2 * foot.x - first.x - second.x) +
                  first.x + second.x := by ring1
            _ = first.x + second.x := by rw [xErrorZero]; ring1
        _ = ((first.x + second.x) / 2) * 2 :=
          (RFAP.ExplicitField.div_mul_cancel _ twoNonzero).symm
    · change foot.y = (first.y + second.y) / 2
      apply eq_of_mul_eq_mul_right twoNonzero
      calc
        foot.y * 2 = 2 * foot.y := by ring1
        _ = first.y + second.y := by
          calc
            2 * foot.y =
                (2 * foot.y - first.y - second.y) +
                  first.y + second.y := by ring1
            _ = first.y + second.y := by rw [yErrorZero]; ring1
        _ = ((first.y + second.y) / 2) * 2 :=
          (RFAP.ExplicitField.div_mul_cancel _ twoNonzero).symm
  · intro footIsMidpoint
    subst foot
    exact isosceles_midpoint_equal_spreads first second vertex
      vertexFirstDistinct vertexSecondDistinct vertexFootDistinct
      sideFirstNonNull sideSecondNonNull cevianNonNull twoNonzero
      equalVertexQuadrances

/-- Theorem 67 (Isosceles median).  For a non-null, noncollinear isosceles
triangle and a non-null line from the vertex to a displayed point of the
opposite side, being the altitude, meeting the side at its midpoint, and
making equal vertex spreads are equivalent. -/
theorem isosceles_median [Nontrivial K] [DecidableEq K]
    (first second vertex foot : Point K)
    (firstSecondDistinct : first ≠ second)
    (vertexFirstDistinct : vertex ≠ first)
    (vertexSecondDistinct : vertex ≠ second)
    (vertexFootDistinct : vertex ≠ foot)
    (twoNonzero : (2 : K) ≠ 0)
    (baseNonNull :
      ¬ (lineThrough first second firstSecondDistinct).IsNull)
    (sideFirstNonNull :
      ¬ (lineThrough vertex first vertexFirstDistinct).IsNull)
    (sideSecondNonNull :
      ¬ (lineThrough vertex second vertexSecondDistinct).IsNull)
    (cevianNonNull :
      ¬ (lineThrough vertex foot vertexFootDistinct).IsNull)
    (notCollinear : ¬ Collinear first second vertex)
    (footOnBase :
      (lineThrough first second firstSecondDistinct).Contains foot)
    (equalVertexQuadrances :
      quadrance vertex first = quadrance vertex second) :
    ((lineThrough vertex foot vertexFootDistinct).Perpendicular
          (lineThrough first second firstSecondDistinct) ↔
        foot = midpoint first second) ∧
      (spread (lineThrough vertex first vertexFirstDistinct)
            (lineThrough vertex foot vertexFootDistinct)
            sideFirstNonNull cevianNonNull =
          spread (lineThrough vertex second vertexSecondDistinct)
            (lineThrough vertex foot vertexFootDistinct)
            sideSecondNonNull cevianNonNull ↔
        foot = midpoint first second) := by
  exact ⟨isosceles_altitude_iff_midpoint first second vertex foot
      firstSecondDistinct vertexFootDistinct twoNonzero baseNonNull
      footOnBase equalVertexQuadrances,
    isosceles_bisector_iff_midpoint first second vertex foot
      firstSecondDistinct vertexFirstDistinct vertexSecondDistinct
      vertexFootDistinct twoNonzero sideFirstNonNull sideSecondNonNull
      cevianNonNull notCollinear footOnBase equalVertexQuadrances⟩

end DivineProportions
