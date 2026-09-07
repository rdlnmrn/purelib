import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Trigonometry.Quadrance
import DivineProportions.Plane.AltitudeFoot

/-!
# Divine Proportions, §5.4: quadrance to a line

Both results are proved directly from the finite coordinate formulas.  They
therefore apply unchanged to finite fields, subject only to the displayed
nonzero denominators.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_zero_of_mul_eq_zero_left [DecidableEq K]
    {left right : K} (leftNonzero : left ≠ 0) (productZero : left * right = 0) :
    right = 0 := by
  by_cases rightZero : right = 0
  · exact rightZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero leftNonzero rightZero) productZero)

/-- Theorem 24 (Equal quadrance to two points): the perpendicular bisector is
exactly the equal-quadrance locus. -/
theorem equal_quadrance_iff_perpendicularBisector_contains [DecidableEq K]
    (first second point : Point K) (distinct : first ≠ second)
    (twoNonzero : (2 : K) ≠ 0) :
    quadrance point first = quadrance point second ↔
      (perpendicularBisector first second distinct).Contains point := by
  have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  let linearValue :=
    (first.x - second.x) * point.x +
      (first.y - second.y) * point.y +
      (second.x ^ 2 - first.x ^ 2 +
        second.y ^ 2 - first.y ^ 2) / 2
  have identity : quadrance point first - quadrance point second =
      -(2 * linearValue) := by
    unfold quadrance linearValue
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      ((first.x - point.x) ^ 2 + (first.y - point.y) ^ 2) -
          ((second.x - point.x) ^ 2 + (second.y - point.y) ^ 2) =
        -(2 * ((first.x - second.x) * point.x +
          (first.y - second.y) * point.y)) -
          (second.x ^ 2 - first.x ^ 2 +
            second.y ^ 2 - first.y ^ 2) := by ring1
      _ = -(2 * ((first.x - second.x) * point.x +
          (first.y - second.y) * point.y)) -
          (2 * (2 : K)⁻¹) *
            (second.x ^ 2 - first.x ^ 2 +
              second.y ^ 2 - first.y ^ 2) := by rw [twoInverse]; ring1
      _ = -(2 * ((first.x - second.x) * point.x +
          (first.y - second.y) * point.y +
          (second.x ^ 2 - first.x ^ 2 +
            second.y ^ 2 - first.y ^ 2) * (2 : K)⁻¹)) := by ring1
  change quadrance point first = quadrance point second ↔ linearValue = 0
  constructor
  · intro equalQuadrances
    have productZero : (2 : K) * linearValue = 0 := by
      have differenceZero : quadrance point first - quadrance point second = 0 := by
        rw [equalQuadrances]
        ring1
      rw [identity] at differenceZero
      calc
        (2 : K) * linearValue = -(-(2 * linearValue)) := by ring1
        _ = 0 := by rw [differenceZero]; exact neg_zero
    exact eq_zero_of_mul_eq_zero_left twoNonzero productZero
  · intro linearZero
    have differenceZero : quadrance point first - quadrance point second = 0 := by
      rw [identity, linearZero]
      ring1
    calc
      quadrance point first =
          (quadrance point first - quadrance point second) +
            quadrance point second := by ring1
      _ = quadrance point second := by rw [differenceZero]; ring1

/-- Quadrance from a point to a displayed non-null line. -/
def pointLineQuadrance (point : Point K) (line : Line K)
    (nonNull : ¬ line.IsNull) : K :=
  quadrance point (altitudeFoot point line nonNull)

/-- Theorem 25 (Quadrance to a line): the altitude-foot construction evaluates
to the source's rational expression. -/
theorem pointLineQuadrance_formula
    (point : Point K) (line : Line K) (nonNull : ¬ line.IsNull) :
    pointLineQuadrance point line nonNull =
      (line.a * point.x + line.b * point.y + line.c) ^ 2 /
        lineNorm line := by
  have normNonzero : lineNorm line ≠ 0 := nonNull
  have normCancel : lineNorm line * (lineNorm line)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ normNonzero
  have xDifference :
      (line.b ^ 2 * point.x - line.a * line.b * point.y -
          line.a * line.c) * (lineNorm line)⁻¹ - point.x =
        -line.a * (line.a * point.x + line.b * point.y + line.c) *
          (lineNorm line)⁻¹ := by
    calc
      (line.b ^ 2 * point.x - line.a * line.b * point.y -
            line.a * line.c) * (lineNorm line)⁻¹ - point.x =
        -line.a * (line.a * point.x + line.b * point.y + line.c) *
            (lineNorm line)⁻¹ -
          point.x * (1 - lineNorm line * (lineNorm line)⁻¹) := by
            unfold lineNorm
            ring1
      _ = -line.a * (line.a * point.x + line.b * point.y + line.c) *
          (lineNorm line)⁻¹ := by rw [normCancel]; ring1
  have yDifference :
      (-line.a * line.b * point.x + line.a ^ 2 * point.y -
          line.b * line.c) * (lineNorm line)⁻¹ - point.y =
        -line.b * (line.a * point.x + line.b * point.y + line.c) *
          (lineNorm line)⁻¹ := by
    calc
      (-line.a * line.b * point.x + line.a ^ 2 * point.y -
            line.b * line.c) * (lineNorm line)⁻¹ - point.y =
        -line.b * (line.a * point.x + line.b * point.y + line.c) *
            (lineNorm line)⁻¹ -
          point.y * (1 - lineNorm line * (lineNorm line)⁻¹) := by
            unfold lineNorm
            ring1
      _ = -line.b * (line.a * point.x + line.b * point.y + line.c) *
          (lineNorm line)⁻¹ := by rw [normCancel]; ring1
  unfold pointLineQuadrance quadrance altitudeFoot
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [xDifference, yDifference]
  calc
    ((-line.a * (line.a * point.x + line.b * point.y + line.c) *
          (lineNorm line)⁻¹) ^ 2 +
      (-line.b * (line.a * point.x + line.b * point.y + line.c) *
          (lineNorm line)⁻¹) ^ 2) =
      (lineNorm line * (lineNorm line)⁻¹) *
        ((line.a * point.x + line.b * point.y + line.c) ^ 2 *
          (lineNorm line)⁻¹) := by
            unfold lineNorm
            ring1
    _ = (line.a * point.x + line.b * point.y + line.c) ^ 2 *
        (lineNorm line)⁻¹ := by rw [normCancel, one_mul]

end DivineProportions
