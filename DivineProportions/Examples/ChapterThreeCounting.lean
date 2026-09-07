import DivineProportions.Plane.Incidence

/-!
# Divine Proportions, Exercises 3.2 and 3.13

The source phrases both exercises as cardinalities of complete finite-field
carriers.  Such global enumerations are outside this project's proof boundary.
The incidence content is instead made executable through finite charts:

* every line through a point is either one uniquely determined slope line or
  the vertical line;
* every point on a line is obtained uniquely from one scalar parameter, using
  whichever displayed direction coefficient is nonzero.

These are the constructive bijection data behind the counts `p+1` and `p`.
For triangles, the usual counting proof is retained as exact cleared integer
identities.  It subtracts collinear triples from all triples and, in the null
case, subtracts the double-counted triangles having two null sides.  No list
of all points, lines, or triangles is constructed.
-/

namespace DivineProportions

namespace ChapterThreeCounting

variable {K : Type*} [RFAP.ExplicitField K] [Nontrivial K]

/-- The line of finite slope `slope` through `point`, displayed with second
direction coefficient `-1`. -/
def slopeLineThrough (point : Point K) (slope : K) : Line K where
  a := slope
  b := -1
  c := point.y - slope * point.x
  direction_nonzero := Or.inr (neg_ne_zero.mpr one_ne_zero)

/-- The vertical line through `point`. -/
def verticalLineThrough (point : Point K) : Line K where
  a := 1
  b := 0
  c := -point.x
  direction_nonzero := Or.inl one_ne_zero

theorem slopeLineThrough_contains (point : Point K) (slope : K) :
    (slopeLineThrough point slope).Contains point := by
  unfold slopeLineThrough Line.Contains
  ring1

theorem verticalLineThrough_contains (point : Point K) :
    (verticalLineThrough point).Contains point := by
  unfold verticalLineThrough Line.Contains
  ring1

/-- Two normalized finite-slope representatives are equivalent precisely when
their displayed slopes agree. -/
theorem slopeLineThrough_equivalent_iff
    (point : Point K) (firstSlope secondSlope : K) :
    (slopeLineThrough point firstSlope).Equivalent
        (slopeLineThrough point secondSlope) ↔
      firstSlope = secondSlope := by
  constructor
  · intro equivalent
    have directionEquation := equivalent.1
    unfold slopeLineThrough at directionEquation
    calc
      firstSlope = -(firstSlope * (-1)) := by ring1
      _ = -(secondSlope * (-1)) := by rw [directionEquation]
      _ = secondSlope := by ring1
  · intro slopesEqual
    rw [slopesEqual]
    exact Line.equivalent_refl _

/-- The vertical representative is not equivalent to any finite-slope
representative. -/
theorem verticalLineThrough_not_equivalent_slope
    (point : Point K) (slope : K) :
    ¬ (verticalLineThrough point).Equivalent
        (slopeLineThrough point slope) := by
  intro equivalent
  have directionEquation := equivalent.1
  unfold verticalLineThrough slopeLineThrough at directionEquation
  change (1 : K) * (-1) = slope * 0 at directionEquation
  have negativeOneZero : (-1 : K) = 0 := by
    calc
      (-1 : K) = 1 * (-1) := by ring1
      _ = slope * 0 := directionEquation
      _ = 0 := by ring1
  apply (one_ne_zero : (1 : K) ≠ 0)
  calc
    (1 : K) = -(-1) := by ring1
    _ = -0 := by rw [negativeOneZero]
    _ = 0 := by ring1

/-- Every displayed line through `point` is represented by the vertical chart
or by the explicitly computed slope `-(a/b)`. -/
theorem line_through_point_chart
    [DecidableEq K]
    (point : Point K) (line : Line K) (contains : line.Contains point) :
    (∃ slope : K,
      (slopeLineThrough point slope).Equivalent line) ∨
      (verticalLineThrough point).Equivalent line := by
  by_cases secondZero : line.b = 0
  · right
    have firstNonzero : line.a ≠ 0 := by
      rcases line.direction_nonzero with firstNonzero | secondNonzero
      · exact firstNonzero
      · exact False.elim (secondNonzero secondZero)
    have constantEquation : line.c = -(line.a * point.x) := by
      unfold Line.Contains at contains
      calc
        line.c =
            (line.a * point.x + line.b * point.y + line.c) -
              (line.a * point.x + line.b * point.y) := by ring1
        _ = -(line.a * point.x + line.b * point.y) := by
          rw [contains]
          ring1
        _ = -(line.a * point.x) := by rw [secondZero]; ring1
    unfold Line.Equivalent verticalLineThrough
    exact ⟨by rw [secondZero]; ring1,
      by rw [constantEquation]; ring1,
      by rw [secondZero]; ring1⟩
  · left
    let slope := -(line.a / line.b)
    refine ⟨slope, ?_⟩
    have secondCancel : line.b * line.b⁻¹ = (1 : K) :=
      RFAP.ExplicitField.mul_inv_cancel line.b secondZero
    have secondCancelLeft : line.b⁻¹ * line.b = (1 : K) := by
      calc
        line.b⁻¹ * line.b = line.b * line.b⁻¹ := by ring1
        _ = 1 := secondCancel
    have constantEquation :
        line.c = -(line.a * point.x + line.b * point.y) := by
      unfold Line.Contains at contains
      calc
        line.c =
            (line.a * point.x + line.b * point.y + line.c) -
              (line.a * point.x + line.b * point.y) := by ring1
        _ = -(line.a * point.x + line.b * point.y) := by
          rw [contains]
          ring1
    unfold Line.Equivalent slopeLineThrough
    simp only [slope, RFAP.ExplicitField.div_eq_mul_inv]
    constructor
    · calc
        (-(line.a * line.b⁻¹)) * line.b =
            -(line.a * (line.b * line.b⁻¹)) := by ring1
        _ = line.a * (-1) := by rw [secondCancel]; ring1
    constructor
    · rw [constantEquation]
      calc
        (-(line.a * line.b⁻¹)) *
              (-(line.a * point.x + line.b * point.y)) =
            line.a ^ 2 * line.b⁻¹ * point.x +
              line.a * (line.b⁻¹ * line.b) * point.y := by ring1
        _ = line.a ^ 2 * line.b⁻¹ * point.x +
            line.a * point.y := by rw [secondCancelLeft]; ring1
        _ = line.a *
            (point.y - (-(line.a * line.b⁻¹)) * point.x) := by ring1
    · rw [constantEquation]
      calc
        (-1) * (-(line.a * point.x + line.b * point.y)) =
            line.a * point.x + line.b * point.y := by ring1
        _ = line.a * (line.b * line.b⁻¹) * point.x +
            line.b * point.y := by rw [secondCancel]; ring1
        _ = line.b *
            (point.y - (-(line.a * line.b⁻¹)) * point.x) := by ring1

/-- The complete constructive content of the `p+1` half of Exercise 3.2:
one inequivalent line for each supplied slope, one extra vertical line, and no
other line through the point. -/
theorem exercise_3_2_lines_through_point [DecidableEq K]
    (point : Point K) :
    (∀ slope : K, (slopeLineThrough point slope).Contains point) ∧
      (verticalLineThrough point).Contains point ∧
      (∀ firstSlope secondSlope : K,
        (slopeLineThrough point firstSlope).Equivalent
            (slopeLineThrough point secondSlope) ↔
          firstSlope = secondSlope) ∧
      (∀ slope : K,
        ¬ (verticalLineThrough point).Equivalent
            (slopeLineThrough point slope)) ∧
      ∀ line : Line K, line.Contains point →
        (∃ slope : K,
          (slopeLineThrough point slope).Equivalent line) ∨
          (verticalLineThrough point).Equivalent line := by
  exact ⟨slopeLineThrough_contains point,
    verticalLineThrough_contains point,
    slopeLineThrough_equivalent_iff point,
    verticalLineThrough_not_equivalent_slope point,
    line_through_point_chart point⟩

/-- Parameterize a point of `line` by its first coordinate when `b ≠ 0`. -/
def pointOnLineUsingX (line : Line K) (_secondNonzero : line.b ≠ 0)
    (parameter : K) : Point K :=
  ⟨parameter, -(line.a * parameter + line.c) / line.b⟩

/-- Parameterize a point of `line` by its second coordinate when `a ≠ 0`. -/
def pointOnLineUsingY (line : Line K) (_firstNonzero : line.a ≠ 0)
    (parameter : K) : Point K :=
  ⟨-(line.b * parameter + line.c) / line.a, parameter⟩

omit [Nontrivial K] in
theorem pointOnLineUsingX_contains
    (line : Line K) (secondNonzero : line.b ≠ 0) (parameter : K) :
    line.Contains (pointOnLineUsingX line secondNonzero parameter) := by
  have secondCancel : line.b * line.b⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel line.b secondNonzero
  unfold Line.Contains pointOnLineUsingX
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    line.a * parameter +
          line.b * (-(line.a * parameter + line.c) * line.b⁻¹) +
          line.c =
        (line.a * parameter + line.c) *
          (1 - line.b * line.b⁻¹) := by ring1
    _ = 0 := by rw [secondCancel]; ring1

omit [Nontrivial K] in
theorem pointOnLineUsingY_contains
    (line : Line K) (firstNonzero : line.a ≠ 0) (parameter : K) :
    line.Contains (pointOnLineUsingY line firstNonzero parameter) := by
  have firstCancel : line.a * line.a⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel line.a firstNonzero
  unfold Line.Contains pointOnLineUsingY
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    line.a * (-(line.b * parameter + line.c) * line.a⁻¹) +
          line.b * parameter + line.c =
        (line.b * parameter + line.c) *
          (1 - line.a * line.a⁻¹) := by ring1
    _ = 0 := by rw [firstCancel]; ring1

omit [Nontrivial K] in
theorem pointOnLineUsingX_injective
    (line : Line K) (secondNonzero : line.b ≠ 0) :
    Function.Injective (pointOnLineUsingX line secondNonzero) := by
  intro first second pointsEqual
  exact congrArg Point.x pointsEqual

omit [Nontrivial K] in
theorem pointOnLineUsingY_injective
    (line : Line K) (firstNonzero : line.a ≠ 0) :
    Function.Injective (pointOnLineUsingY line firstNonzero) := by
  intro first second pointsEqual
  exact congrArg Point.y pointsEqual

omit [Nontrivial K] in
theorem pointOnLineUsingX_covers
    (line : Line K) (secondNonzero : line.b ≠ 0)
    (point : Point K) (contains : line.Contains point) :
    pointOnLineUsingX line secondNonzero point.x = point := by
  apply Point.ext
  · rfl
  · have secondCancel : line.b * line.b⁻¹ = (1 : K) :=
      RFAP.ExplicitField.mul_inv_cancel line.b secondNonzero
    have numeratorEquation :
        -(line.a * point.x + line.c) = line.b * point.y := by
      unfold Line.Contains at contains
      calc
        -(line.a * point.x + line.c) =
            line.b * point.y -
              (line.a * point.x + line.b * point.y + line.c) := by ring1
        _ = line.b * point.y := by rw [contains]; ring1
    unfold pointOnLineUsingX
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      -(line.a * point.x + line.c) * line.b⁻¹ =
          (line.b * point.y) * line.b⁻¹ := by rw [numeratorEquation]
      _ = point.y * (line.b * line.b⁻¹) := by ring1
      _ = point.y := by rw [secondCancel, mul_one]

omit [Nontrivial K] in
theorem pointOnLineUsingY_covers
    (line : Line K) (firstNonzero : line.a ≠ 0)
    (point : Point K) (contains : line.Contains point) :
    pointOnLineUsingY line firstNonzero point.y = point := by
  apply Point.ext
  · have firstCancel : line.a * line.a⁻¹ = (1 : K) :=
      RFAP.ExplicitField.mul_inv_cancel line.a firstNonzero
    have numeratorEquation :
        -(line.b * point.y + line.c) = line.a * point.x := by
      unfold Line.Contains at contains
      calc
        -(line.b * point.y + line.c) =
            line.a * point.x -
              (line.a * point.x + line.b * point.y + line.c) := by ring1
        _ = line.a * point.x := by rw [contains]; ring1
    unfold pointOnLineUsingY
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      -(line.b * point.y + line.c) * line.a⁻¹ =
          (line.a * point.x) * line.a⁻¹ := by rw [numeratorEquation]
      _ = point.x * (line.a * line.a⁻¹) := by ring1
      _ = point.x := by rw [firstCancel, mul_one]
  · rfl

omit [Nontrivial K] in
/-- The complete constructive content of the `p` half of Exercise 3.2.  The
line's stored nonzero direction selects an explicit one-scalar chart, which
is injective and covers every incident point. -/
theorem exercise_3_2_points_on_line (line : Line K) :
    (∃ secondNonzero : line.b ≠ 0,
      (∀ parameter : K,
        line.Contains (pointOnLineUsingX line secondNonzero parameter)) ∧
      Function.Injective (pointOnLineUsingX line secondNonzero) ∧
      ∀ point : Point K, line.Contains point →
        pointOnLineUsingX line secondNonzero point.x = point) ∨
    (∃ firstNonzero : line.a ≠ 0,
      (∀ parameter : K,
        line.Contains (pointOnLineUsingY line firstNonzero parameter)) ∧
      Function.Injective (pointOnLineUsingY line firstNonzero) ∧
      ∀ point : Point K, line.Contains point →
        pointOnLineUsingY line firstNonzero point.y = point) := by
  rcases line.direction_nonzero with firstNonzero | secondNonzero
  · right
    exact ⟨firstNonzero, pointOnLineUsingY_contains line firstNonzero,
      pointOnLineUsingY_injective line firstNonzero,
      pointOnLineUsingY_covers line firstNonzero⟩
  · left
    exact ⟨secondNonzero, pointOnLineUsingX_contains line secondNonzero,
      pointOnLineUsingX_injective line secondNonzero,
      pointOnLineUsingX_covers line secondNonzero⟩

namespace ExerciseThreeThirteen

/-- Six times the number of unordered triples selected from `p²` points. -/
def allPointTriplesNumerator (p : Int) : Int :=
  p ^ 2 * (p ^ 2 - 1) * (p ^ 2 - 2)

/-- Six times the collinear-triple incidence count: `p(p+1)` lines, with
`p(p-1)(p-2)` ordered triples on each line. -/
def collinearTriplesNumerator (p : Int) : Int :=
  p * (p + 1) * (p * (p - 1) * (p - 2))

/-- Six times the resulting number of triangles. -/
def triangleCountNumerator (p : Int) : Int :=
  p ^ 3 * (p - 1) * (p ^ 2 - 1)

/-- Exercise 3.13's ordinary triangle count, with the common denominator six
cleared.  Every collinear triple belongs to its unique line, so subtracting
the second numerator from the first leaves `p³(p-1)(p²-1)`. -/
theorem triangle_count_cleared (p : Int) :
    allPointTriplesNumerator p - collinearTriplesNumerator p =
      triangleCountNumerator p := by
  unfold allPointTriplesNumerator collinearTriplesNumerator
    triangleCountNumerator
  ring1

/-- The source's usual triangle-count formula, retained as a finite natural
calculation for any requested input. -/
def triangleCount (p : Nat) : Nat :=
  (p ^ 3 * (p - 1) * (p ^ 2 - 1)) / 6

/-- If `-1` is not square, there are no null directions and hence no null
triangles. -/
def nullTriangleCountWithoutNullLines (_p : Nat) : Nat := 0

/-- If `-1` is square, the null-triangle count after correcting the overlap of
the two null directions is `p²(p-1)³`. -/
def nullTriangleCountWithNullLines (p : Nat) : Nat :=
  p ^ 2 * (p - 1) ^ 3

/-- Twice the null-side incidence count minus twice the overlap count equals
twice `p²(p-1)³`.  The overlap consists exactly of triangles whose two null
sides meet at one vertex. -/
theorem null_triangle_count_cleared (p : Int) :
    (2 * p) * (p * (p - 1)) * (p ^ 2 - p) -
        2 * (p ^ 2 * (p - 1) ^ 2) =
      2 * (p ^ 2 * (p - 1) ^ 3) := by
  ring1

/-- Closed checks of the formulas at the first four odd prime labels.  These
are arithmetic evaluations, not enumerations of their fields. -/
theorem first_count_values :
    triangleCount 3 = 72 ∧ triangleCount 5 = 2000 ∧
      triangleCount 7 = 16464 ∧ triangleCount 11 = 266200 ∧
      nullTriangleCountWithNullLines 5 = 1600 ∧
      nullTriangleCountWithNullLines 13 = 292032 := by
  decide

end ExerciseThreeThirteen

end ChapterThreeCounting

end DivineProportions
