module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Reflection.Point
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint
import Purelib.Geometry.Plane.Line.Relations

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, §4.2: reflection lineations

The reflected line is constructed from the exact three coefficients printed in
Theorem 15.  Its direction proof is not selected by choice: decidable equality
checks the first two displayed coefficients, and the inverse matrix identity
rules out their simultaneous vanishing.
-/

namespace Purelib.Geometry.Plane.Reflection.Line

variable {K : Type*} [ExplicitField K]

/-- The first coefficient of the target line reflected in the displayed mirror. -/
def reflectedLineA (mirror target : Plane.Line K) : K :=
  (mirror.a ^ 2 - mirror.b ^ 2) * target.a +
    2 * mirror.a * mirror.b * target.b

/-- The second coefficient of the target line reflected in the displayed mirror. -/
def reflectedLineB (mirror target : Plane.Line K) : K :=
  2 * mirror.a * mirror.b * target.a -
    (mirror.a ^ 2 - mirror.b ^ 2) * target.b

/-- The constant coefficient of the target line reflected in the displayed mirror. -/
def reflectedLineC (mirror target : Plane.Line K) : K :=
  2 * mirror.a * mirror.c * target.a +
    2 * mirror.b * mirror.c * target.b - Line.Basic.lineNorm mirror * target.c

/-- The two displayed reflected direction coefficients cannot both vanish when the mirror is non-null. -/
theorem reflectedLine_direction_nonzero [DecidableEq K]
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull) :
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
  have normNonzero : Basic.lineNorm mirror ≠ 0 := mirrorNonNull
  have normSquareNonzero : Basic.lineNorm mirror ^ 2 ≠ 0 := by
    intro squareZero
    apply (ExplicitField.mul_ne_zero normNonzero normNonzero)
    calc
      Basic.lineNorm mirror * Basic.lineNorm mirror = Basic.lineNorm mirror ^ 2 := by ring1
      _ = 0 := squareZero
  have targetAProduct : Basic.lineNorm mirror ^ 2 * target.a = 0 := by
    calc
      Basic.lineNorm mirror ^ 2 * target.a =
          (mirror.a ^ 2 - mirror.b ^ 2) * reflectedLineA mirror target +
            2 * mirror.a * mirror.b * reflectedLineB mirror target := by
        unfold Basic.lineNorm reflectedLineA reflectedLineB
        ring1
      _ = 0 := by rw [firstZero, secondZero]; ring1
  have targetBProduct : Basic.lineNorm mirror ^ 2 * target.b = 0 := by
    calc
      Basic.lineNorm mirror ^ 2 * target.b =
          2 * mirror.a * mirror.b * reflectedLineA mirror target -
            (mirror.a ^ 2 - mirror.b ^ 2) * reflectedLineB mirror target := by
        unfold Basic.lineNorm reflectedLineA reflectedLineB
        ring1
      _ = 0 := by rw [firstZero, secondZero]; ring1
  have targetAZero := ExplicitField.eq_zero_of_mul_eq_zero_left normSquareNonzero targetAProduct
  have targetBZero := ExplicitField.eq_zero_of_mul_eq_zero_left normSquareNonzero targetBProduct
  rcases target.direction_nonzero with targetANonzero | targetBNonzero
  · exact False.elim (targetANonzero targetAZero)
  · exact False.elim (targetBNonzero targetBZero)

/-- Reflect a displayed target line in a certified non-null mirror.

The explicit three coefficients retain their polynomial scaling; the inverse direction identity certifies a nonzero
direction. -/
def reflectLine [DecidableEq K] (mirror target : Plane.Line K)
    (mirrorNonNull : ¬ mirror.IsNull) : Plane.Line K where
  a := reflectedLineA mirror target
  b := reflectedLineB mirror target
  c := reflectedLineC mirror target
  direction_nonzero :=
    reflectedLine_direction_nonzero mirror target mirrorNonNull

/-- Reflection of displayed lines respects quotient-free equality of both the mirror and target coefficient triples. -/
theorem reflectLine_equivalent_of_equivalent [DecidableEq K]
    (firstMirror secondMirror firstTarget secondTarget : Plane.Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (mirrorEquivalent : firstMirror.Equivalent secondMirror)
    (targetEquivalent : firstTarget.Equivalent secondTarget) :
    (reflectLine firstMirror firstTarget firstMirrorNonNull).Equivalent
      (reflectLine secondMirror secondTarget secondMirrorNonNull) := by
  rcases Relations.line_coefficient_scale_of_equivalent
      firstMirror secondMirror mirrorEquivalent with
    ⟨mirrorScale, secondMirrorA, secondMirrorB, secondMirrorC⟩
  rcases Relations.line_coefficient_scale_of_equivalent
      firstTarget secondTarget targetEquivalent with
    ⟨targetScale, secondTargetA, secondTargetB, secondTargetC⟩
  unfold Plane.Line.Equivalent reflectLine
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
  unfold reflectedLineA reflectedLineB reflectedLineC Basic.lineNorm
  rw [secondMirrorA, secondMirrorB, secondMirrorC,
    secondTargetA, secondTargetB, secondTargetC]
  constructor
  · ring1
  constructor <;> ring1

/-- Theorem 15 (Reflection of a line in a line): reflection of a point on the source line lies on the line with the
printed reflected coefficients. -/
theorem reflectLine_contains_reflectPoint [DecidableEq K]
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (point : Plane.Point K) (contains : target.Contains point) :
    (reflectLine mirror target mirrorNonNull).Contains
      (Reflection.Point.reflectPoint mirror mirrorNonNull point) := by
  have normNonzero : Basic.lineNorm mirror ≠ 0 := mirrorNonNull
  have normCancel : Basic.lineNorm mirror * (Basic.lineNorm mirror)⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel _ normNonzero
  rw [Reflection.Point.reflectPoint_formula]
  change
    reflectedLineA mirror target *
          ((((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
            2 * mirror.a * mirror.b * point.y -
            2 * mirror.a * mirror.c) / Basic.lineNorm mirror)) +
        reflectedLineB mirror target *
          (((-2 * mirror.a * mirror.b * point.x +
            (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
            2 * mirror.b * mirror.c) / Basic.lineNorm mirror)) +
        reflectedLineC mirror target = 0
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    reflectedLineA mirror target *
          (((mirror.b ^ 2 - mirror.a ^ 2) * point.x -
            2 * mirror.a * mirror.b * point.y -
            2 * mirror.a * mirror.c) * (Basic.lineNorm mirror)⁻¹) +
        reflectedLineB mirror target *
          ((-2 * mirror.a * mirror.b * point.x +
            (mirror.a ^ 2 - mirror.b ^ 2) * point.y -
            2 * mirror.b * mirror.c) * (Basic.lineNorm mirror)⁻¹) +
        reflectedLineC mirror target =
      -Basic.lineNorm mirror *
          (target.a * point.x + target.b * point.y) *
          (Basic.lineNorm mirror * (Basic.lineNorm mirror)⁻¹) +
        2 * mirror.c * (mirror.a * target.a + mirror.b * target.b) *
          (1 - Basic.lineNorm mirror * (Basic.lineNorm mirror)⁻¹) -
        Basic.lineNorm mirror * target.c := by
      unfold reflectedLineA reflectedLineB reflectedLineC Basic.lineNorm
      ring1
    _ = 0 := by
      rw [normCancel]
      unfold Plane.Line.Contains at contains
      rw [show target.a * point.x + target.b * point.y = -target.c by
        calc
          target.a * point.x + target.b * point.y =
              (target.a * point.x + target.b * point.y + target.c) -
                target.c := by ring1
          _ = -target.c := by rw [contains]; ring1]
      ring1

/-- Reflection scales line direction quadrance by the square of the mirror's direction quadrance. -/
theorem reflectLine_norm [DecidableEq K]
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull) :
    Basic.lineNorm (reflectLine mirror target mirrorNonNull) =
      Basic.lineNorm mirror ^ 2 * Basic.lineNorm target := by
  unfold Basic.lineNorm reflectLine reflectedLineA reflectedLineB
  ring1

/-- A non-null line remains non-null after reflection in a non-null line. -/
theorem reflectLine_nonNull [DecidableEq K]
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (targetNonNull : ¬ target.IsNull) :
    ¬ (reflectLine mirror target mirrorNonNull).IsNull := by
  intro reflectedNull
  have normZero : Line.Basic.lineNorm (reflectLine mirror target mirrorNonNull) = 0 :=
    reflectedNull
  rw [reflectLine_norm] at normZero
  have mirrorNormNonzero : Line.Basic.lineNorm mirror ≠ 0 := mirrorNonNull
  have mirrorNormSquareNonzero : Line.Basic.lineNorm mirror ^ 2 ≠ 0 := by
    intro squareZero
    apply (ExplicitField.mul_ne_zero mirrorNormNonzero mirrorNormNonzero)
    calc
      Line.Basic.lineNorm mirror * Line.Basic.lineNorm mirror = Line.Basic.lineNorm mirror ^ 2 := by ring1
      _ = 0 := squareZero
  have targetNormNonzero : Line.Basic.lineNorm target ≠ 0 := targetNonNull
  exact (ExplicitField.mul_ne_zero mirrorNormSquareNonzero
    targetNormNonzero) normZero

/-- Reflecting one target in parallel mirrors produces parallel reflected lines. Only the mirror directions matter;
their offsets may differ. -/
theorem reflectLine_parallel_of_parallel_mirrors [DecidableEq K]
    (firstMirror secondMirror target : Plane.Line K)
    (firstMirrorNonNull : ¬ firstMirror.IsNull)
    (secondMirrorNonNull : ¬ secondMirror.IsNull)
    (parallelMirrors : firstMirror.Parallel secondMirror) :
    (reflectLine firstMirror target firstMirrorNonNull).Parallel
      (reflectLine secondMirror target secondMirrorNonNull) := by
  unfold Plane.Line.Parallel at parallelMirrors ⊢
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

/-- A common point of the mirror and target remains on the reflected target. This is the incidence fact needed by the
Spread reflection theorem. -/
theorem reflectLine_contains_common_point [DecidableEq K]
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (point : Plane.Point K) (mirrorContains : mirror.Contains point)
    (targetContains : target.Contains point) :
    (reflectLine mirror target mirrorNonNull).Contains point := by
  unfold Plane.Line.Contains at mirrorContains targetContains ⊢
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
        Basic.lineNorm mirror *
          (target.a * point.x + target.b * point.y + target.c) := by
            unfold reflectedLineA reflectedLineB reflectedLineC
              Basic.lineNorm
            ring1
    _ = 0 := by rw [mirrorContains, targetContains]; ring1

/-- Theorem 17 (Lineation): conjugating the reflection lineation reflects its mirror. Equality of book lines is equality
of ordered proportions, represented here by `Line.Equivalent`. -/
theorem lineation_composition [Nontrivial K] [DecidableEq K]
    (firstMirror secondMirror target : Plane.Line K)
    (firstNonNull : ¬ firstMirror.IsNull)
    (secondNonNull : ¬ secondMirror.IsNull) :
    (reflectLine secondMirror
        (reflectLine firstMirror target firstNonNull) secondNonNull).Equivalent
      (reflectLine
        (reflectLine secondMirror firstMirror secondNonNull)
        (reflectLine secondMirror target secondNonNull)
        (reflectLine_nonNull secondMirror firstMirror secondNonNull
          firstNonNull)) := by
  unfold Plane.Line.Equivalent reflectLine reflectedLineA reflectedLineB
    reflectedLineC
    Line.Basic.lineNorm
  constructor
  · ring1
  constructor <;> ring1

/-- A line perpendicular to the mirror is fixed by the reflection lineation, the valid forward implication of Exercise
4.4. -/
theorem reflectLine_fixed_of_perpendicular [DecidableEq K]
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (perpendicular : mirror.Perpendicular target) :
    (reflectLine mirror target mirrorNonNull).Equivalent target := by
  unfold Plane.Line.Perpendicular at perpendicular
  have reflectedA :
      reflectedLineA mirror target = -Basic.lineNorm mirror * target.a := by
    calc
      reflectedLineA mirror target =
          -Basic.lineNorm mirror * target.a +
            2 * mirror.a *
              (mirror.a * target.a + mirror.b * target.b) := by
        unfold reflectedLineA Basic.lineNorm
        ring1
      _ = -Basic.lineNorm mirror * target.a := by rw [perpendicular]; ring1
  have reflectedB :
      reflectedLineB mirror target = -Basic.lineNorm mirror * target.b := by
    calc
      reflectedLineB mirror target =
          -Basic.lineNorm mirror * target.b +
            2 * mirror.b *
              (mirror.a * target.a + mirror.b * target.b) := by
        unfold reflectedLineB Basic.lineNorm
        ring1
      _ = -Basic.lineNorm mirror * target.b := by rw [perpendicular]; ring1
  have reflectedC :
      reflectedLineC mirror target = -Basic.lineNorm mirror * target.c := by
    calc
      reflectedLineC mirror target =
          -Basic.lineNorm mirror * target.c +
            2 * mirror.c *
              (mirror.a * target.a + mirror.b * target.b) := by
        unfold reflectedLineC
        ring1
      _ = -Basic.lineNorm mirror * target.c := by rw [perpendicular]; ring1
  unfold Plane.Line.Equivalent reflectLine
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

/-- The mirror line itself is fixed. Together with `reflectLine_self_not_perpendicular`, this is the missing
counterexample to the printed converse of Exercise 4.4. -/
theorem reflectLine_self_equivalent [DecidableEq K]
    (mirror : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull) :
    (reflectLine mirror mirror mirrorNonNull).Equivalent mirror := by
  unfold Plane.Line.Equivalent reflectLine reflectedLineA reflectedLineB
    reflectedLineC
    Line.Basic.lineNorm
  constructor
  · ring1
  constructor <;> ring1

/-- A non-null mirror is not perpendicular to itself. -/
theorem reflectLine_self_not_perpendicular
    (mirror : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull) :
    ¬ mirror.Perpendicular mirror := by
  intro perpendicular
  apply mirrorNonNull
  unfold Purelib.Geometry.Plane.Line.Perpendicular at perpendicular
  unfold Purelib.Geometry.Plane.Line.IsNull
  calc
    mirror.a ^ 2 + mirror.b ^ 2 =
        mirror.a * mirror.a + mirror.b * mirror.b := by ring1
    _ = 0 := perpendicular

/-- Exercise 4.5: reflection lineation is involutive, as equality of ordered line proportions. -/
theorem reflectLine_involutive [DecidableEq K]
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull) :
    (reflectLine mirror (reflectLine mirror target mirrorNonNull)
      mirrorNonNull).Equivalent target := by
  unfold Plane.Line.Equivalent reflectLine reflectedLineA reflectedLineB
    reflectedLineC
    Line.Basic.lineNorm
  constructor
  · ring1
  constructor <;> ring1

/-- If reflecting a target in a mirror leaves its direction parallel to the target, then the target is parallel or
perpendicular to the mirror. -/
theorem parallel_or_perpendicular_of_parallel_reflectLine [DecidableEq K]
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull)
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
        ((ExplicitField.mul_ne_zero twoNonzero zero) twiceProductZero)
  by_cases determinantZero : determinant = 0
  · left
    exact determinantZero
  · right
    by_cases dotZero : dot = 0
    · exact dotZero
    · exact False.elim
        ((ExplicitField.mul_ne_zero determinantZero dotZero) productZero)

/-- Exercise 4.6 is not valid as printed. If the mirror is null, substituting the mirror itself into the claimed formula
produces the forbidden all-zero coefficient triple. -/
theorem null_reflection_formula_self_zero (mirror : Plane.Line K)
    (mirrorNull : mirror.IsNull) :
    reflectedLineA mirror mirror = 0 ∧
      reflectedLineB mirror mirror = 0 ∧
      reflectedLineC mirror mirror = 0 := by
  unfold Plane.Line.IsNull at mirrorNull
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
        unfold reflectedLineC Basic.lineNorm
        ring1
      _ = 0 := by rw [mirrorNull]; ring1

end Purelib.Geometry.Plane.Reflection.Line

end

end

section
@[expose] public section

/-!
# Divine Proportions, Exercises 15.8 and 15.9

This module constructs a parabola's axis from its focus and directrix, proves
that equation preservation characterizes that axis up to the project's
quotient-free line equivalence, and constructs the unique vertex as the
midpoint of the focus and its altitude foot on the directrix.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [ExplicitField K]

section

/-- A target parallel to a non-null mirror can be fixed by reflection only by coinciding with that mirror.
Characteristic two is the sole cancellation excluded by the affine-offset calculation. -/
theorem equivalent_of_parallel_and_reflectLine_fixed [DecidableEq K]
    (mirror target : Plane.Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (twoNonzero : (2 : K) ≠ 0) (parallel : mirror.Parallel target)
    (fixed : (Geometry.Plane.Reflection.Line.reflectLine mirror target mirrorNonNull).Equivalent target) :
    mirror.Equivalent target := by
  rcases Relations.direction_scale_of_parallel mirror target parallel with
    ⟨scale, scaleNonzero, targetA, targetB⟩
  have normNonzero : Basic.lineNorm mirror ≠ 0 := mirrorNonNull
  have reflectedA :
      Reflection.Line.reflectedLineA mirror target = Basic.lineNorm mirror * target.a := by
    unfold Reflection.Line.reflectedLineA Basic.lineNorm
    rw [targetA, targetB]
    ring1
  have reflectedB :
      Reflection.Line.reflectedLineB mirror target = Basic.lineNorm mirror * target.b := by
    unfold Reflection.Line.reflectedLineB Basic.lineNorm
    rw [targetA, targetB]
    ring1
  have reflectedC :
      Reflection.Line.reflectedLineC mirror target =
        Basic.lineNorm mirror * (2 * scale * mirror.c - target.c) := by
    unfold Reflection.Line.reflectedLineC Basic.lineNorm
    rw [targetA, targetB]
    ring1
  have targetC : target.c = scale * mirror.c := by
    rcases target.direction_nonzero with targetANonzero | targetBNonzero
    · have constantEquation :
          Reflection.Line.reflectedLineA mirror target * target.c =
            target.a * Reflection.Line.reflectedLineC mirror target := fixed.2.1
      rw [reflectedA, reflectedC] at constantEquation
      have factorNonzero : 2 * Basic.lineNorm mirror * target.a ≠ 0 :=
        ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero twoNonzero normNonzero)
          targetANonzero
      apply ExplicitField.eq_of_mul_eq_mul_left factorNonzero
      calc
        (2 * Basic.lineNorm mirror * target.a) * target.c =
            Basic.lineNorm mirror * target.a * target.c +
              Basic.lineNorm mirror * target.a * target.c := by ring1
        _ = target.a *
              (Basic.lineNorm mirror * (2 * scale * mirror.c - target.c)) +
            Basic.lineNorm mirror * target.a * target.c := by
              rw [constantEquation]
        _ = (2 * Basic.lineNorm mirror * target.a) *
            (scale * mirror.c) := by ring1
    · have constantEquation :
          Reflection.Line.reflectedLineB mirror target * target.c =
            target.b * Reflection.Line.reflectedLineC mirror target := fixed.2.2
      rw [reflectedB, reflectedC] at constantEquation
      have factorNonzero : 2 * Basic.lineNorm mirror * target.b ≠ 0 :=
        ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero twoNonzero normNonzero)
          targetBNonzero
      apply ExplicitField.eq_of_mul_eq_mul_left factorNonzero
      calc
        (2 * Basic.lineNorm mirror * target.b) * target.c =
            Basic.lineNorm mirror * target.b * target.c +
              Basic.lineNorm mirror * target.b * target.c := by ring1
        _ = target.b *
              (Basic.lineNorm mirror * (2 * scale * mirror.c - target.c)) +
            Basic.lineNorm mirror * target.b * target.c := by
              rw [constantEquation]
        _ = (2 * Basic.lineNorm mirror * target.b) *
            (scale * mirror.c) := by ring1
  unfold Plane.Line.Equivalent
  rw [targetA, targetB, targetC]
  constructor
  · ring1
  constructor <;> ring1
end

end Purelib.Curves.Plane.Conic

end
