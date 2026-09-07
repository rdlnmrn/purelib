import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Plane.AltitudeFoot
import DivineProportions.Plane.Affine

/-!
# Divine Proportions, Chapter 4: point reflections

The reflection in a non-null line is defined exactly as in the book: find the
altitude foot and rotate the source point through that foot.  Theorem 13's
coordinate formula and the involution law are then derived by finite field
algebra.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- A point transformation in the finite Cartesian plane. -/
abbrev Transformation (K : Type*) := Point K → Point K

/-- The book's algebraic definition of an affine transformation. -/
def IsAffine (transformation : Transformation K) : Prop :=
  ∀ (first second : Point K) (leftWeight rightWeight : K),
    leftWeight + rightWeight = 1 →
    transformation
        (affineCombination leftWeight first rightWeight second) =
      affineCombination leftWeight (transformation first)
        rightWeight (transformation second)

/-- Rotation in a point: `ρ_A(B) = 2A - B`. -/
def rotateInPoint (center point : Point K) : Point K :=
  ⟨2 * center.x - point.x, 2 * center.y - point.y⟩

/-- Exercise 4.1: rotation in a point is affine. -/
theorem rotateInPoint_affine (center : Point K) :
    IsAffine (rotateInPoint center) := by
  intro first second leftWeight rightWeight weights
  have rightFormula : rightWeight = 1 - leftWeight := by
    calc
      rightWeight = (leftWeight + rightWeight) - leftWeight := by ring1
      _ = 1 - leftWeight := by rw [weights]
  rw [rightFormula]
  apply Point.ext <;>
    unfold rotateInPoint affineCombination <;>
    ring1

/-- Exercise 4.1: rotation in a point is its own inverse. -/
theorem rotateInPoint_involutive (center point : Point K) :
    rotateInPoint center (rotateInPoint center point) = point := by
  apply Point.ext <;>
    unfold rotateInPoint <;>
    ring1

/-- Reflection in a non-null line, defined geometrically through the altitude
foot as in §4.1. -/
def reflectPoint (line : Line K) (nonNull : ¬ line.IsNull)
    (point : Point K) : Point K :=
  rotateInPoint (altitudeFoot point line nonNull) point

/-- The displayed right-hand side of Theorem 13. -/
def reflectionFormula (line : Line K) (point : Point K) : Point K :=
  ⟨(((line.b ^ 2 - line.a ^ 2) * point.x -
      2 * line.a * line.b * point.y - 2 * line.a * line.c) /
      lineNorm line),
    ((-2 * line.a * line.b * point.x +
      (line.a ^ 2 - line.b ^ 2) * point.y - 2 * line.b * line.c) /
      lineNorm line)⟩

/-- Theorem 13 (Reflection of a point in a line): derivation of the printed
coordinate formula from the altitude-foot definition. -/
theorem reflectPoint_formula (line : Line K) (nonNull : ¬ line.IsNull)
    (point : Point K) :
    reflectPoint line nonNull point = reflectionFormula line point := by
  have normNonzero : lineNorm line ≠ 0 := nonNull
  have normCancel : lineNorm line * (lineNorm line)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ normNonzero
  apply Point.ext
  · change
      2 * ((line.b ^ 2 * point.x - line.a * line.b * point.y -
          line.a * line.c) / lineNorm line) - point.x =
        ((line.b ^ 2 - line.a ^ 2) * point.x -
          2 * line.a * line.b * point.y - 2 * line.a * line.c) /
          lineNorm line
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 *
            ((line.b ^ 2 * point.x - line.a * line.b * point.y -
                line.a * line.c) * (lineNorm line)⁻¹) - point.x =
        2 *
            ((line.b ^ 2 * point.x - line.a * line.b * point.y -
                line.a * line.c) * (lineNorm line)⁻¹) -
          point.x * (lineNorm line * (lineNorm line)⁻¹) := by
        rw [normCancel]
        ring1
      _ = ((line.b ^ 2 - line.a ^ 2) * point.x -
          2 * line.a * line.b * point.y - 2 * line.a * line.c) *
          (lineNorm line)⁻¹ := by
        unfold lineNorm
        ring1
  · change
      2 * ((-line.a * line.b * point.x + line.a ^ 2 * point.y -
          line.b * line.c) / lineNorm line) - point.y =
        (-2 * line.a * line.b * point.x +
          (line.a ^ 2 - line.b ^ 2) * point.y - 2 * line.b * line.c) /
          lineNorm line
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      2 *
            ((-line.a * line.b * point.x + line.a ^ 2 * point.y -
                line.b * line.c) * (lineNorm line)⁻¹) - point.y =
        2 *
            ((-line.a * line.b * point.x + line.a ^ 2 * point.y -
                line.b * line.c) * (lineNorm line)⁻¹) -
          point.y * (lineNorm line * (lineNorm line)⁻¹) := by
        rw [normCancel]
        ring1
      _ = (-2 * line.a * line.b * point.x +
          (line.a ^ 2 - line.b ^ 2) * point.y - 2 * line.b * line.c) *
          (lineNorm line)⁻¹ := by
        unfold lineNorm
        ring1

/-- Exercise 4.3, affine half: reflection in a non-null line is affine. -/
theorem reflectPoint_affine (line : Line K) (nonNull : ¬ line.IsNull) :
    IsAffine (reflectPoint line nonNull) := by
  intro first second leftWeight rightWeight weights
  have rightFormula : rightWeight = 1 - leftWeight := by
    calc
      rightWeight = (leftWeight + rightWeight) - leftWeight := by ring1
      _ = 1 - leftWeight := by rw [weights]
  rw [rightFormula]
  rw [reflectPoint_formula, reflectPoint_formula, reflectPoint_formula]
  apply Point.ext <;>
    unfold reflectionFormula affineCombination <;>
    simp only [RFAP.ExplicitField.div_eq_mul_inv] <;>
    ring1

/-- Exercise 4.3, inverse half: reflection in a non-null line is its own
inverse. -/
theorem reflectPoint_involutive (line : Line K) (nonNull : ¬ line.IsNull)
    (point : Point K) :
    reflectPoint line nonNull (reflectPoint line nonNull point) = point := by
  have normNonzero : lineNorm line ≠ 0 := nonNull
  have normCancel : lineNorm line * (lineNorm line)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ normNonzero
  rw [reflectPoint_formula, reflectPoint_formula]
  apply Point.ext
  · change
      (((line.b ^ 2 - line.a ^ 2) *
            (((line.b ^ 2 - line.a ^ 2) * point.x -
              2 * line.a * line.b * point.y - 2 * line.a * line.c) /
              lineNorm line) -
          2 * line.a * line.b *
            ((-2 * line.a * line.b * point.x +
              (line.a ^ 2 - line.b ^ 2) * point.y -
              2 * line.b * line.c) / lineNorm line) -
          2 * line.a * line.c) / lineNorm line) = point.x
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      ((line.b ^ 2 - line.a ^ 2) *
              (((line.b ^ 2 - line.a ^ 2) * point.x -
                2 * line.a * line.b * point.y - 2 * line.a * line.c) *
                (lineNorm line)⁻¹) -
            2 * line.a * line.b *
              ((-2 * line.a * line.b * point.x +
                (line.a ^ 2 - line.b ^ 2) * point.y -
                2 * line.b * line.c) * (lineNorm line)⁻¹) -
            2 * line.a * line.c) * (lineNorm line)⁻¹ =
        point.x * (lineNorm line * (lineNorm line)⁻¹) ^ 2 +
          2 * line.a * line.c * (lineNorm line)⁻¹ *
            (lineNorm line * (lineNorm line)⁻¹ - 1) := by
          unfold lineNorm
          ring1
      _ = point.x := by rw [normCancel]; ring1
  · change
      ((-2 * line.a * line.b *
            (((line.b ^ 2 - line.a ^ 2) * point.x -
              2 * line.a * line.b * point.y - 2 * line.a * line.c) /
              lineNorm line) +
          (line.a ^ 2 - line.b ^ 2) *
            ((-2 * line.a * line.b * point.x +
              (line.a ^ 2 - line.b ^ 2) * point.y -
              2 * line.b * line.c) / lineNorm line) -
          2 * line.b * line.c) / lineNorm line) = point.y
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      (-2 * line.a * line.b *
              (((line.b ^ 2 - line.a ^ 2) * point.x -
                2 * line.a * line.b * point.y - 2 * line.a * line.c) *
                (lineNorm line)⁻¹) +
            (line.a ^ 2 - line.b ^ 2) *
              ((-2 * line.a * line.b * point.x +
                (line.a ^ 2 - line.b ^ 2) * point.y -
                2 * line.b * line.c) * (lineNorm line)⁻¹) -
            2 * line.b * line.c) * (lineNorm line)⁻¹ =
        point.y * (lineNorm line * (lineNorm line)⁻¹) ^ 2 +
          2 * line.b * line.c * (lineNorm line)⁻¹ *
            (lineNorm line * (lineNorm line)⁻¹ - 1) := by
          unfold lineNorm
          ring1
      _ = point.y := by rw [normCancel]; ring1

/-- The line formula associated to rotation in a point (Theorem 14). -/
def rotateLineInPoint (center : Point K) (line : Line K) : Line K where
  a := line.a
  b := line.b
  c := -2 * center.x * line.a - 2 * center.y * line.b - line.c
  direction_nonzero := line.direction_nonzero

/-- Theorem 14 (Rotation of a line in a point): incidence is transported by
the displayed associated lineation formula. -/
theorem rotateLineInPoint_contains_iff (center point : Point K) (line : Line K) :
    (rotateLineInPoint center line).Contains (rotateInPoint center point) ↔
      line.Contains point := by
  constructor
  · intro rotatedContains
    change line.a * (2 * center.x - point.x) +
      line.b * (2 * center.y - point.y) +
      (-2 * center.x * line.a - 2 * center.y * line.b - line.c) = 0
      at rotatedContains
    change line.a * point.x + line.b * point.y + line.c = 0
    calc
      line.a * point.x + line.b * point.y + line.c =
          -(line.a * (2 * center.x - point.x) +
            line.b * (2 * center.y - point.y) +
            (-2 * center.x * line.a - 2 * center.y * line.b - line.c)) := by
        ring1
      _ = 0 := by rw [rotatedContains]; exact neg_zero
  · intro contains
    change line.a * point.x + line.b * point.y + line.c = 0 at contains
    change line.a * (2 * center.x - point.x) +
      line.b * (2 * center.y - point.y) +
      (-2 * center.x * line.a - 2 * center.y * line.b - line.c) = 0
    calc
      line.a * (2 * center.x - point.x) +
          line.b * (2 * center.y - point.y) +
          (-2 * center.x * line.a - 2 * center.y * line.b - line.c) =
        -(line.a * point.x + line.b * point.y + line.c) := by ring1
      _ = 0 := by rw [contains]; exact neg_zero

end DivineProportions
