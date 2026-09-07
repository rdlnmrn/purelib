import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Plane.Reflection

/-!
# Divine Proportions, §4.2: reflection lineations

The reflected line is constructed from the exact three coefficients printed in
Theorem 15.  Its direction proof is not selected by choice: decidable equality
checks the first two displayed coefficients, and the inverse matrix identity
rules out their simultaneous vanishing.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- First direction coefficient in Theorem 15. -/
def reflectedLineA (mirror target : Line K) : K :=
  (mirror.a ^ 2 - mirror.b ^ 2) * target.a +
    2 * mirror.a * mirror.b * target.b

/-- Second direction coefficient in Theorem 15. -/
def reflectedLineB (mirror target : Line K) : K :=
  2 * mirror.a * mirror.b * target.a -
    (mirror.a ^ 2 - mirror.b ^ 2) * target.b

/-- Constant coefficient in Theorem 15. -/
def reflectedLineC (mirror target : Line K) : K :=
  2 * mirror.a * mirror.c * target.a +
    2 * mirror.b * mirror.c * target.b - lineNorm mirror * target.c

private theorem eq_zero_of_mul_eq_zero_left [DecidableEq K]
    {left right : K} (leftNonzero : left ≠ 0) (productZero : left * right = 0) :
    right = 0 := by
  by_cases rightZero : right = 0
  · exact rightZero
  · exact False.elim
      ((RFAP.ExplicitField.mul_ne_zero leftNonzero rightZero) productZero)

/-- The two displayed reflected direction coefficients cannot both vanish
when the mirror is non-null. -/
theorem reflectedLine_direction_nonzero [DecidableEq K]
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull) :
    reflectedLineA mirror target ≠ 0 ∨ reflectedLineB mirror target ≠ 0 := by
  by_cases firstNonzero : reflectedLineA mirror target ≠ 0
  · exact Or.inl firstNonzero
  by_cases secondNonzero : reflectedLineB mirror target ≠ 0
  · exact Or.inr secondNonzero
  have firstZero : reflectedLineA mirror target = 0 := by
    by_cases firstZero : reflectedLineA mirror target = 0
    · exact firstZero
    · exact False.elim (firstNonzero firstZero)
  have secondZero : reflectedLineB mirror target = 0 := by
    by_cases secondZero : reflectedLineB mirror target = 0
    · exact secondZero
    · exact False.elim (secondNonzero secondZero)
  have normNonzero : lineNorm mirror ≠ 0 := mirrorNonNull
  have normSquareNonzero : lineNorm mirror ^ 2 ≠ 0 := by
    intro squareZero
    apply (RFAP.ExplicitField.mul_ne_zero normNonzero normNonzero)
    calc
      lineNorm mirror * lineNorm mirror = lineNorm mirror ^ 2 := by ring1
      _ = 0 := squareZero
  have targetAProduct : lineNorm mirror ^ 2 * target.a = 0 := by
    calc
      lineNorm mirror ^ 2 * target.a =
          (mirror.a ^ 2 - mirror.b ^ 2) * reflectedLineA mirror target +
            2 * mirror.a * mirror.b * reflectedLineB mirror target := by
        unfold lineNorm reflectedLineA reflectedLineB
        ring1
      _ = 0 := by rw [firstZero, secondZero]; ring1
  have targetBProduct : lineNorm mirror ^ 2 * target.b = 0 := by
    calc
      lineNorm mirror ^ 2 * target.b =
          2 * mirror.a * mirror.b * reflectedLineA mirror target -
            (mirror.a ^ 2 - mirror.b ^ 2) * reflectedLineB mirror target := by
        unfold lineNorm reflectedLineA reflectedLineB
        ring1
      _ = 0 := by rw [firstZero, secondZero]; ring1
  have targetAZero := eq_zero_of_mul_eq_zero_left normSquareNonzero targetAProduct
  have targetBZero := eq_zero_of_mul_eq_zero_left normSquareNonzero targetBProduct
  rcases target.direction_nonzero with targetANonzero | targetBNonzero
  · exact False.elim (targetANonzero targetAZero)
  · exact False.elim (targetBNonzero targetBZero)

/-- Theorem 15's reflected-line construction. -/
def reflectLine [DecidableEq K] (mirror target : Line K)
    (mirrorNonNull : ¬ mirror.IsNull) : Line K where
  a := reflectedLineA mirror target
  b := reflectedLineB mirror target
  c := reflectedLineC mirror target
  direction_nonzero :=
    reflectedLine_direction_nonzero mirror target mirrorNonNull

/-- Reflection of displayed lines respects quotient-free equality of both
the mirror and target coefficient triples. -/
theorem reflectLine_equivalent_of_equivalent [DecidableEq K]
    (firstMirror secondMirror firstTarget secondTarget : Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (mirrorEquivalent : firstMirror.Equivalent secondMirror)
    (targetEquivalent : firstTarget.Equivalent secondTarget) :
    (reflectLine firstMirror firstTarget firstMirrorNonNull).Equivalent
      (reflectLine secondMirror secondTarget secondMirrorNonNull) := by
  rcases line_coefficient_scale_of_equivalent
      firstMirror secondMirror mirrorEquivalent with
    ⟨mirrorScale, secondMirrorA, secondMirrorB, secondMirrorC⟩
  rcases line_coefficient_scale_of_equivalent
      firstTarget secondTarget targetEquivalent with
    ⟨targetScale, secondTargetA, secondTargetB, secondTargetC⟩
  unfold Line.Equivalent reflectLine
  change
    reflectedLineA firstMirror firstTarget *
          reflectedLineB secondMirror secondTarget =
        reflectedLineA secondMirror secondTarget *
          reflectedLineB firstMirror firstTarget ∧
      reflectedLineA firstMirror firstTarget *
          reflectedLineC secondMirror secondTarget =
        reflectedLineA secondMirror secondTarget *
          reflectedLineC firstMirror firstTarget ∧
      reflectedLineB firstMirror firstTarget *
          reflectedLineC secondMirror secondTarget =
        reflectedLineB secondMirror secondTarget *
          reflectedLineC firstMirror firstTarget
  unfold reflectedLineA reflectedLineB reflectedLineC lineNorm
  rw [secondMirrorA, secondMirrorB, secondMirrorC,
    secondTargetA, secondTargetB, secondTargetC]
  constructor
  · ring1
  constructor <;> ring1

/-- Theorem 15 (Reflection of a line in a line): reflection of a point on the
source line lies on the line with the printed reflected coefficients. -/
theorem reflectLine_contains_reflectPoint [DecidableEq K]
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (point : Point K) (contains : target.Contains point) :
    (reflectLine mirror target mirrorNonNull).Contains
      (reflectPoint mirror mirrorNonNull point) := by
  have normNonzero : lineNorm mirror ≠ 0 := mirrorNonNull
  have normCancel : lineNorm mirror * (lineNorm mirror)⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel _ normNonzero
  rw [reflectPoint_formula]
  change
    reflectedLineA mirror target *
          ((((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
            2 * mirror.a * mirror.b * point.y -
            2 * mirror.a * mirror.c) / lineNorm mirror)) +
        reflectedLineB mirror target *
          (((-2 * mirror.a * mirror.b * point.x +
            (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
            2 * mirror.b * mirror.c) / lineNorm mirror)) +
        reflectedLineC mirror target = 0
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    reflectedLineA mirror target *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
            2 * mirror.a * mirror.b * point.y -
            2 * mirror.a * mirror.c) * (lineNorm mirror)⁻¹) +
        reflectedLineB mirror target *
          ((-2 * mirror.a * mirror.b * point.x +
            (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
            2 * mirror.b * mirror.c) * (lineNorm mirror)⁻¹) +
        reflectedLineC mirror target =
      -lineNorm mirror *
          (target.a * point.x + target.b * point.y) *
          (lineNorm mirror * (lineNorm mirror)⁻¹) +
        2 * mirror.c * (mirror.a * target.a + mirror.b * target.b) *
          (1 - lineNorm mirror * (lineNorm mirror)⁻¹) -
        lineNorm mirror * target.c := by
      unfold reflectedLineA reflectedLineB reflectedLineC lineNorm
      ring1
    _ = 0 := by
      rw [normCancel]
      unfold Line.Contains at contains
      rw [show target.a * point.x + target.b * point.y = -target.c by
        calc
          target.a * point.x + target.b * point.y =
              (target.a * point.x + target.b * point.y + target.c) -
                target.c := by ring1
          _ = -target.c := by rw [contains]; ring1]
      ring1

/-- Reflection scales line direction quadrance by the square of the mirror's
direction quadrance. -/
theorem reflectLine_norm [DecidableEq K]
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull) :
    lineNorm (reflectLine mirror target mirrorNonNull) =
      lineNorm mirror ^ 2 * lineNorm target := by
  unfold lineNorm reflectLine reflectedLineA reflectedLineB
  ring1

/-- A non-null line remains non-null after reflection in a non-null line. -/
theorem reflectLine_nonNull [DecidableEq K]
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (targetNonNull : ¬ target.IsNull) :
    ¬ (reflectLine mirror target mirrorNonNull).IsNull := by
  intro reflectedNull
  have normZero : lineNorm (reflectLine mirror target mirrorNonNull) = 0 :=
    reflectedNull
  rw [reflectLine_norm] at normZero
  have mirrorNormNonzero : lineNorm mirror ≠ 0 := mirrorNonNull
  have mirrorNormSquareNonzero : lineNorm mirror ^ 2 ≠ 0 := by
    intro squareZero
    apply (RFAP.ExplicitField.mul_ne_zero mirrorNormNonzero mirrorNormNonzero)
    calc
      lineNorm mirror * lineNorm mirror = lineNorm mirror ^ 2 := by ring1
      _ = 0 := squareZero
  have targetNormNonzero : lineNorm target ≠ 0 := targetNonNull
  exact (RFAP.ExplicitField.mul_ne_zero mirrorNormSquareNonzero
    targetNormNonzero) normZero

/-- Reflecting one target in parallel mirrors produces parallel reflected
lines.  Only the mirror directions matter; their offsets may differ. -/
theorem reflectLine_parallel_of_parallel_mirrors [DecidableEq K]
    (firstMirror secondMirror target : Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (parallelMirrors : firstMirror.Parallel secondMirror) :
    (reflectLine firstMirror target firstMirrorNonNull).Parallel
      (reflectLine secondMirror target secondMirrorNonNull) := by
  unfold Line.Parallel at parallelMirrors ⊢
  unfold reflectLine reflectedLineA reflectedLineB
  calc
    ((firstMirror.a ^ 2 - firstMirror.b ^ 2) * target.a +
          2 * firstMirror.a * firstMirror.b * target.b) *
        (2 * secondMirror.a * secondMirror.b * target.a -
          (secondMirror.a ^ 2 - secondMirror.b ^ 2) * target.b) -
      ((secondMirror.a ^ 2 - secondMirror.b ^ 2) * target.a +
          2 * secondMirror.a * secondMirror.b * target.b) *
        (2 * firstMirror.a * firstMirror.b * target.a -
          (firstMirror.a ^ 2 - firstMirror.b ^ 2) * target.b) =
      2 * (target.a ^ 2 + target.b ^ 2) *
        (firstMirror.a * secondMirror.a +
          firstMirror.b * secondMirror.b) *
        (firstMirror.a * secondMirror.b -
          secondMirror.a * firstMirror.b) := by ring1
    _ = 0 := by rw [parallelMirrors]; ring1

/-- A common point of the mirror and target remains on the reflected target.
This is the incidence fact needed by the Spread reflection theorem. -/
theorem reflectLine_contains_common_point [DecidableEq K]
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (point : Point K) (mirrorContains : mirror.Contains point)
    (targetContains : target.Contains point) :
    (reflectLine mirror target mirrorNonNull).Contains point := by
  unfold Line.Contains at mirrorContains targetContains ⊢
  unfold reflectLine
  change
    reflectedLineA mirror target * point.x +
      reflectedLineB mirror target * point.y +
      reflectedLineC mirror target = 0
  calc
    reflectedLineA mirror target * point.x +
        reflectedLineB mirror target * point.y +
        reflectedLineC mirror target =
      2 * (mirror.a * target.a + mirror.b * target.b) *
          (mirror.a * point.x + mirror.b * point.y + mirror.c) -
        lineNorm mirror *
          (target.a * point.x + target.b * point.y + target.c) := by
            unfold reflectedLineA reflectedLineB reflectedLineC lineNorm
            ring1
    _ = 0 := by rw [mirrorContains, targetContains]; ring1

/-- Theorem 17 (Lineation): conjugating the reflection lineation reflects its
mirror.  Equality of book lines is equality of ordered proportions, represented
here by `Line.Equivalent`. -/
theorem lineation_composition [Nontrivial K] [DecidableEq K]
    (firstMirror secondMirror target : Line K)
    (firstNonNull : ¬ firstMirror.IsNull)
    (secondNonNull : ¬ secondMirror.IsNull) :
    (reflectLine secondMirror
        (reflectLine firstMirror target firstNonNull) secondNonNull).Equivalent
      (reflectLine
        (reflectLine secondMirror firstMirror secondNonNull)
        (reflectLine secondMirror target secondNonNull)
        (reflectLine_nonNull secondMirror firstMirror secondNonNull
          firstNonNull)) := by
  unfold Line.Equivalent reflectLine reflectedLineA reflectedLineB reflectedLineC
    lineNorm
  constructor
  · ring1
  constructor <;> ring1

/-- A line perpendicular to the mirror is fixed by the reflection lineation,
the valid forward implication of Exercise 4.4. -/
theorem reflectLine_fixed_of_perpendicular [DecidableEq K]
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (perpendicular : mirror.Perpendicular target) :
    (reflectLine mirror target mirrorNonNull).Equivalent target := by
  unfold Line.Perpendicular at perpendicular
  have reflectedA :
      reflectedLineA mirror target = -lineNorm mirror * target.a := by
    calc
      reflectedLineA mirror target =
          -lineNorm mirror * target.a +
            2 * mirror.a *
              (mirror.a * target.a + mirror.b * target.b) := by
        unfold reflectedLineA lineNorm
        ring1
      _ = -lineNorm mirror * target.a := by rw [perpendicular]; ring1
  have reflectedB :
      reflectedLineB mirror target = -lineNorm mirror * target.b := by
    calc
      reflectedLineB mirror target =
          -lineNorm mirror * target.b +
            2 * mirror.b *
              (mirror.a * target.a + mirror.b * target.b) := by
        unfold reflectedLineB lineNorm
        ring1
      _ = -lineNorm mirror * target.b := by rw [perpendicular]; ring1
  have reflectedC :
      reflectedLineC mirror target = -lineNorm mirror * target.c := by
    calc
      reflectedLineC mirror target =
          -lineNorm mirror * target.c +
            2 * mirror.c *
              (mirror.a * target.a + mirror.b * target.b) := by
        unfold reflectedLineC
        ring1
      _ = -lineNorm mirror * target.c := by rw [perpendicular]; ring1
  unfold Line.Equivalent reflectLine
  change
    reflectedLineA mirror target * target.b =
        target.a * reflectedLineB mirror target ∧
      reflectedLineA mirror target * target.c =
          target.a * reflectedLineC mirror target ∧
        reflectedLineB mirror target * target.c =
          target.b * reflectedLineC mirror target
  rw [reflectedA, reflectedB, reflectedC]
  constructor
  · ring1
  constructor <;> ring1

/-- The mirror line itself is fixed.  Together with
`reflectLine_self_not_perpendicular`, this is the missing counterexample to the
printed converse of Exercise 4.4. -/
theorem reflectLine_self_equivalent [DecidableEq K]
    (mirror : Line K) (mirrorNonNull : ¬ mirror.IsNull) :
    (reflectLine mirror mirror mirrorNonNull).Equivalent mirror := by
  unfold Line.Equivalent reflectLine reflectedLineA reflectedLineB reflectedLineC
    lineNorm
  constructor
  · ring1
  constructor <;> ring1

theorem reflectLine_self_not_perpendicular
    (mirror : Line K) (mirrorNonNull : ¬ mirror.IsNull) :
    ¬ mirror.Perpendicular mirror := by
  intro perpendicular
  apply mirrorNonNull
  unfold Line.Perpendicular at perpendicular
  unfold Line.IsNull
  calc
    mirror.a ^ 2 + mirror.b ^ 2 =
        mirror.a * mirror.a + mirror.b * mirror.b := by ring1
    _ = 0 := perpendicular

/-- Exercise 4.5: reflection lineation is involutive, as equality of ordered
line proportions. -/
theorem reflectLine_involutive [DecidableEq K]
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull) :
    (reflectLine mirror (reflectLine mirror target mirrorNonNull)
      mirrorNonNull).Equivalent target := by
  unfold Line.Equivalent reflectLine reflectedLineA reflectedLineB reflectedLineC
    lineNorm
  constructor
  · ring1
  constructor <;> ring1

/-- If reflecting a target in a mirror leaves its direction parallel to the
target, then the target is parallel or perpendicular to the mirror. -/
theorem parallel_or_perpendicular_of_parallel_reflectLine [DecidableEq K]
    (mirror target : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (twoNonzero : (2 : K) ≠ 0)
    (fixedDirection :
      target.Parallel (reflectLine mirror target mirrorNonNull)) :
    target.Parallel mirror ∨ target.Perpendicular mirror := by
  let determinant := target.a * mirror.b - mirror.a * target.b
  let dot := target.a * mirror.a + target.b * mirror.b
  have twiceProductZero : 2 * (determinant * dot) = 0 := by
    calc
      2 * (determinant * dot) =
          target.a * (reflectLine mirror target mirrorNonNull).b -
            (reflectLine mirror target mirrorNonNull).a * target.b := by
        unfold determinant dot reflectLine reflectedLineA reflectedLineB
        ring1
      _ = 0 := fixedDirection
  have productZero : determinant * dot = 0 := by
    by_cases zero : determinant * dot = 0
    · exact zero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero twoNonzero zero) twiceProductZero)
  by_cases determinantZero : determinant = 0
  · left
    exact determinantZero
  · right
    by_cases dotZero : dot = 0
    · exact dotZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero determinantZero dotZero) productZero)

/-- Exercise 4.6 is not valid as printed.  If the mirror is null, substituting
the mirror itself into the claimed formula produces the forbidden all-zero
coefficient triple. -/
theorem null_reflection_formula_self_zero (mirror : Line K)
    (mirrorNull : mirror.IsNull) :
    reflectedLineA mirror mirror = 0 ∧
      reflectedLineB mirror mirror = 0 ∧
      reflectedLineC mirror mirror = 0 := by
  unfold Line.IsNull at mirrorNull
  constructor
  · calc
      reflectedLineA mirror mirror =
          (mirror.a ^ 2 + mirror.b ^ 2) * mirror.a := by
        unfold reflectedLineA
        ring1
      _ = 0 := by rw [mirrorNull]; ring1
  constructor
  · calc
      reflectedLineB mirror mirror =
          (mirror.a ^ 2 + mirror.b ^ 2) * mirror.b := by
        unfold reflectedLineB
        ring1
      _ = 0 := by rw [mirrorNull]; ring1
  · calc
      reflectedLineC mirror mirror =
          (mirror.a ^ 2 + mirror.b ^ 2) * mirror.c := by
        unfold reflectedLineC lineNorm
        ring1
      _ = 0 := by rw [mirrorNull]; ring1

end DivineProportions
