module

import Purelib.Algebra.Field.Ratio
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Line.Spread
public import Purelib.Geometry.Plane.Line.VertexBisector.Basic
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

section
public section

/-!
# Divine Proportions, §6.9: vertex bisectors

An explicit witness `r² = ‖l₁‖‖l₂‖` produces the two normalized
bisectors `r l₁ ± ‖l₁‖ l₂`.  This formulation is equivalent to the
book's longer coefficient display, but is symmetric enough that all finite
field cancellations remain visible.
-/

namespace Purelib.Geometry.Plane.Line.VertexBisector.Construction

variable {K : Type*} [ExplicitField K]

section
open _root_.Purelib.Geometry
/-- The positive bisector coefficient pair is nonzero when the first line is non-null and the lines are nonparallel. -/
private theorem
  positiveBisector_direction_nonzero
  [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second) :
    root * first.a + Line.Basic.lineNorm first * second.a ≠ 0 ∨
      root * first.b + Line.Basic.lineNorm first * second.b ≠ 0 := by
  by_cases aNonzero :
      root * first.a + Line.Basic.lineNorm first * second.a ≠ 0
  · exact Or.inl aNonzero
  · by_cases bNonzero :
        root * first.b + Line.Basic.lineNorm first * second.b ≠ 0
    · exact Or.inr bNonzero
    · have aZero : root * first.a + Line.Basic.lineNorm first * second.a = 0 := by
        by_cases equality : root * first.a + Line.Basic.lineNorm first * second.a = 0
        · exact equality
        · exact False.elim (aNonzero equality)
      have bZero : root * first.b + Line.Basic.lineNorm first * second.b = 0 := by
        by_cases equality : root * first.b + Line.Basic.lineNorm first * second.b = 0
        · exact equality
        · exact False.elim (bNonzero equality)
      have normNonzero : Line.Basic.lineNorm first ≠ 0 := firstNonNull
      have determinantNonzero :=
        Purelib.Geometry.Plane.Line.Basic.determinant_ne_zero_of_not_parallel notParallel
      have productNonzero :=
        ExplicitField.mul_ne_zero normNonzero determinantNonzero
      exact False.elim (productNonzero (by
        calc
          Line.Basic.lineNorm first *
              (first.a * second.b - second.a * first.b) =
            first.a *
                (root * first.b + Line.Basic.lineNorm first * second.b) -
              (root * first.a + Line.Basic.lineNorm first * second.a) * first.b := by ring1
          _ = 0 := by rw [aZero, bZero]; ring1))
/-- The negative bisector coefficient pair is nonzero when the first line is non-null and the lines are nonparallel. -/
private theorem
  negativeBisector_direction_nonzero
  [DecidableEq K]
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second) :
    root * first.a - Line.Basic.lineNorm first * second.a ≠ 0 ∨
      root * first.b - Line.Basic.lineNorm first * second.b ≠ 0 := by
  by_cases aNonzero :
      root * first.a - Line.Basic.lineNorm first * second.a ≠ 0
  · exact Or.inl aNonzero
  · by_cases bNonzero :
        root * first.b - Line.Basic.lineNorm first * second.b ≠ 0
    · exact Or.inr bNonzero
    · have aZero : root * first.a - Line.Basic.lineNorm first * second.a = 0 := by
        by_cases equality : root * first.a - Line.Basic.lineNorm first * second.a = 0
        · exact equality
        · exact False.elim (aNonzero equality)
      have bZero : root * first.b - Line.Basic.lineNorm first * second.b = 0 := by
        by_cases equality : root * first.b - Line.Basic.lineNorm first * second.b = 0
        · exact equality
        · exact False.elim (bNonzero equality)
      have normNonzero : Line.Basic.lineNorm first ≠ 0 := firstNonNull
      have determinantNonzero :=
        Purelib.Geometry.Plane.Line.Basic.determinant_ne_zero_of_not_parallel notParallel
      have productNonzero :=
        ExplicitField.mul_ne_zero normNonzero determinantNonzero
      exact False.elim (productNonzero (by
        calc
          Line.Basic.lineNorm first *
              (first.a * second.b - second.a * first.b) =
            -first.a *
                (root * first.b - Line.Basic.lineNorm first * second.b) +
              (root * first.a - Line.Basic.lineNorm first * second.a) * first.b := by ring1
          _ = 0 := by rw [aZero, bZero]; ring1))
end

/-- The coefficientwise sum of the root-scaled first line and norm-scaled second line.

The first line is non-null and the pair is nonparallel, which certifies a nonzero direction. The square-root equation is
required only by later bisector guarantees. -/
@[expose] def positiveVertexBisector [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second) :
    Plane.Line K where
  a := root * first.a + Line.Basic.lineNorm first * second.a
  b := root * first.b + Line.Basic.lineNorm first * second.b
  c := root * first.c + Line.Basic.lineNorm first * second.c
  direction_nonzero := by
    by_cases aNonzero :
        root * first.a + Line.Basic.lineNorm first * second.a ≠ 0
    · exact Or.inl aNonzero
    · by_cases bNonzero :
          root * first.b + Line.Basic.lineNorm first * second.b ≠ 0
      · exact Or.inr bNonzero
      · have aZero : root * first.a + Line.Basic.lineNorm first * second.a = 0 := by
          by_cases equality : root * first.a + Line.Basic.lineNorm first * second.a = 0
          · exact equality
          · exact False.elim (aNonzero equality)
        have bZero : root * first.b + Line.Basic.lineNorm first * second.b = 0 := by
          by_cases equality : root * first.b + Line.Basic.lineNorm first * second.b = 0
          · exact equality
          · exact False.elim (bNonzero equality)
        have normNonzero : Line.Basic.lineNorm first ≠ 0 := firstNonNull
        have determinantNonzero :
            first.a * second.b - second.a * first.b ≠ 0 := notParallel
        have productNonzero :=
          ExplicitField.mul_ne_zero normNonzero determinantNonzero
        exact False.elim (productNonzero (by
          calc
            Line.Basic.lineNorm first *
                (first.a * second.b - second.a * first.b) =
              first.a *
                  (root * first.b + Line.Basic.lineNorm first * second.b) -
                (root * first.a + Line.Basic.lineNorm first * second.a) * first.b := by ring1
            _ = 0 := by rw [aZero, bZero]; ring1))

/-- The coefficientwise difference of the root-scaled first line and norm-scaled second line.

The first line is non-null and the pair is nonparallel, which certifies a nonzero direction. The square-root equation is
required only by later bisector guarantees. -/
@[expose] def negativeVertexBisector [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second) :
    Plane.Line K where
  a := root * first.a - Line.Basic.lineNorm first * second.a
  b := root * first.b - Line.Basic.lineNorm first * second.b
  c := root * first.c - Line.Basic.lineNorm first * second.c
  direction_nonzero := by
    by_cases aNonzero :
        root * first.a - Line.Basic.lineNorm first * second.a ≠ 0
    · exact Or.inl aNonzero
    · by_cases bNonzero :
          root * first.b - Line.Basic.lineNorm first * second.b ≠ 0
      · exact Or.inr bNonzero
      · have aZero : root * first.a - Line.Basic.lineNorm first * second.a = 0 := by
          by_cases equality : root * first.a - Line.Basic.lineNorm first * second.a = 0
          · exact equality
          · exact False.elim (aNonzero equality)
        have bZero : root * first.b - Line.Basic.lineNorm first * second.b = 0 := by
          by_cases equality : root * first.b - Line.Basic.lineNorm first * second.b = 0
          · exact equality
          · exact False.elim (bNonzero equality)
        have normNonzero : Line.Basic.lineNorm first ≠ 0 := firstNonNull
        have determinantNonzero :
            first.a * second.b - second.a * first.b ≠ 0 := notParallel
        have productNonzero :=
          ExplicitField.mul_ne_zero normNonzero determinantNonzero
        exact False.elim (productNonzero (by
          calc
            Line.Basic.lineNorm first *
                (first.a * second.b - second.a * first.b) =
              -first.a *
                  (root * first.b - Line.Basic.lineNorm first * second.b) +
                (root * first.a - Line.Basic.lineNorm first * second.a) * first.b := by ring1
            _ = 0 := by rw [aZero, bZero]; ring1))

section
open _root_.Purelib.Geometry
/-- A square root of the product of two non-null line norms is nonzero. -/
public theorem root_ne_zero
    (first second : Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second) :
    root ≠ 0 := by
  intro rootZero
  have productNonzero := ExplicitField.mul_ne_zero
    (show Line.Basic.lineNorm first ≠ 0 from firstNonNull)
    (show Line.Basic.lineNorm second ≠ 0 from secondNonNull)
  apply productNonzero
  calc
    Line.Basic.lineNorm first * Line.Basic.lineNorm second = root ^ 2 := rootEquation.symm
    _ = 0 := by rw [rootZero]; ring1
/-- The squared direction determinant plus the squared direction dot product equals the product of the line norms. -/
private theorem
  determinant_square_add_dot_square
    (first second : Line K) :
    (first.a * second.b - second.a * first.b) ^ 2 +
      (first.a * second.a + first.b * second.b) ^ 2 =
        Basic.lineNorm first * Basic.lineNorm second := by
  unfold Basic.lineNorm
  ring1
end

/-- The direction norm of the positive candidate factors as twice the first norm, the root and the sum of the root and
direction dot product.

The supplied root squares to the product of the line norms. -/
theorem positiveVertexBisector_norm [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = Basic.lineNorm first * Basic.lineNorm second) :
    Basic.lineNorm (positiveVertexBisector first second root firstNonNull notParallel) =
      2 * Basic.lineNorm first * root *
        (root + (first.a * second.a + first.b * second.b)) := by
  unfold Basic.lineNorm positiveVertexBisector
  change
    (root * first.a + (first.a ^ 2 + first.b ^ 2) * second.a) ^ 2 +
      (root * first.b + (first.a ^ 2 + first.b ^ 2) * second.b) ^ 2 =
    2 * (first.a ^ 2 + first.b ^ 2) * root *
      (root + (first.a * second.a + first.b * second.b))
  calc
    (root * first.a + (first.a ^ 2 + first.b ^ 2) * second.a) ^ 2 +
        (root * first.b + (first.a ^ 2 + first.b ^ 2) * second.b) ^ 2 =
      root ^ 2 * (first.a ^ 2 + first.b ^ 2) +
        2 * root * (first.a ^ 2 + first.b ^ 2) *
          (first.a * second.a + first.b * second.b) +
        (first.a ^ 2 + first.b ^ 2) ^ 2 *
          (second.a ^ 2 + second.b ^ 2) := by ring1
    _ = 2 * (first.a ^ 2 + first.b ^ 2) *
        (root ^ 2 + root *
          (first.a * second.a + first.b * second.b)) := by
            rw [rootEquation]
            unfold Basic.lineNorm
            ring1
    _ = 2 * (first.a ^ 2 + first.b ^ 2) * root *
        (root + (first.a * second.a + first.b * second.b)) := by ring1

/-- The direction norm of the negative candidate factors as twice the first norm, the root and the difference of the
root and direction dot product.

The supplied root squares to the product of the line norms. -/
theorem negativeVertexBisector_norm [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = Basic.lineNorm first * Basic.lineNorm second) :
    Basic.lineNorm (negativeVertexBisector first second root firstNonNull notParallel) =
      2 * Basic.lineNorm first * root *
        (root - (first.a * second.a + first.b * second.b)) := by
  unfold Basic.lineNorm negativeVertexBisector
  change
    (root * first.a - (first.a ^ 2 + first.b ^ 2) * second.a) ^ 2 +
      (root * first.b - (first.a ^ 2 + first.b ^ 2) * second.b) ^ 2 =
    2 * (first.a ^ 2 + first.b ^ 2) * root *
      (root - (first.a * second.a + first.b * second.b))
  calc
    (root * first.a - (first.a ^ 2 + first.b ^ 2) * second.a) ^ 2 +
        (root * first.b - (first.a ^ 2 + first.b ^ 2) * second.b) ^ 2 =
      root ^ 2 * (first.a ^ 2 + first.b ^ 2) -
        2 * root * (first.a ^ 2 + first.b ^ 2) *
          (first.a * second.a + first.b * second.b) +
        (first.a ^ 2 + first.b ^ 2) ^ 2 *
          (second.a ^ 2 + second.b ^ 2) := by ring1
    _ = 2 * (first.a ^ 2 + first.b ^ 2) *
        (root ^ 2 - root *
          (first.a * second.a + first.b * second.b)) := by
            rw [rootEquation]
            unfold Basic.lineNorm
            ring1
    _ = 2 * (first.a ^ 2 + first.b ^ 2) * root *
        (root - (first.a * second.a + first.b * second.b)) := by ring1

section
open _root_.Purelib.Geometry
/-- For nonparallel lines, a square root of the norm product plus their direction dot product is nonzero. -/
private theorem
  root_add_dot_ne_zero
  [DecidableEq K]
    (first second : Line K) (root : K)
    (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second) :
    root + (first.a * second.a + first.b * second.b) ≠ 0 := by
  intro sumZero
  have determinantNonzero := Purelib.Geometry.Plane.Line.Basic.determinant_ne_zero_of_not_parallel notParallel
  apply (ExplicitField.mul_ne_zero determinantNonzero determinantNonzero)
  have fibonacci :=
    determinant_square_add_dot_square first
    second
  calc
    (first.a * second.b - second.a * first.b) *
        (first.a * second.b - second.a * first.b) =
      (first.a * second.b - second.a * first.b) ^ 2 := by ring1
    _ = Line.Basic.lineNorm first * Line.Basic.lineNorm second -
        (first.a * second.a + first.b * second.b) ^ 2 := by
          calc
            (first.a * second.b - second.a * first.b) ^ 2 =
              ((first.a * second.b - second.a * first.b) ^ 2 +
                (first.a * second.a + first.b * second.b) ^ 2) -
                (first.a * second.a + first.b * second.b) ^ 2 := by ring1
            _ = Line.Basic.lineNorm first * Line.Basic.lineNorm second -
                (first.a * second.a + first.b * second.b) ^ 2 := by rw [fibonacci]
    _ = root ^ 2 - (first.a * second.a + first.b * second.b) ^ 2 := by
      rw [← rootEquation]
    _ = 0 := by
      have dotValue : first.a * second.a + first.b * second.b = -root := by
        calc
          first.a * second.a + first.b * second.b =
              (root + (first.a * second.a + first.b * second.b)) - root := by
                ring1
          _ = -root := by rw [sumZero]; ring1
      rw [dotValue]
      ring1
/-- For nonparallel lines, a square root of the norm product minus their direction dot product is nonzero. -/
private theorem
  root_sub_dot_ne_zero
  [DecidableEq K]
    (first second : Line K) (root : K)
    (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second) :
    root - (first.a * second.a + first.b * second.b) ≠ 0 := by
  intro differenceZero
  have determinantNonzero := Purelib.Geometry.Plane.Line.Basic.determinant_ne_zero_of_not_parallel notParallel
  apply (ExplicitField.mul_ne_zero determinantNonzero determinantNonzero)
  have fibonacci :=
    determinant_square_add_dot_square first
    second
  calc
    (first.a * second.b - second.a * first.b) *
        (first.a * second.b - second.a * first.b) =
      (first.a * second.b - second.a * first.b) ^ 2 := by ring1
    _ = Line.Basic.lineNorm first * Line.Basic.lineNorm second -
        (first.a * second.a + first.b * second.b) ^ 2 := by
          calc
            (first.a * second.b - second.a * first.b) ^ 2 =
              ((first.a * second.b - second.a * first.b) ^ 2 +
                (first.a * second.a + first.b * second.b) ^ 2) -
                (first.a * second.a + first.b * second.b) ^ 2 := by ring1
            _ = Line.Basic.lineNorm first * Line.Basic.lineNorm second -
                (first.a * second.a + first.b * second.b) ^ 2 := by rw [fibonacci]
    _ = root ^ 2 - (first.a * second.a + first.b * second.b) ^ 2 := by
      rw [← rootEquation]
    _ = 0 := by
      have dotValue : first.a * second.a + first.b * second.b = root := by
        calc
          first.a * second.a + first.b * second.b =
              root - (root -
                (first.a * second.a + first.b * second.b)) := by ring1
          _ = root := by rw [differenceZero]; ring1
      rw [dotValue]
      ring1
end

/-- The positive candidate is non-null for non-null, nonparallel input lines.

Two is nonzero and the supplied root squares to the product of the line norms. -/
theorem positiveVertexBisector_nonNull [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second) :
    ¬ (positiveVertexBisector first second root firstNonNull
      notParallel).IsNull := by
  have normNonzero : Line.Basic.lineNorm first ≠ 0 := firstNonNull
  have rootNonzero :=
    root_ne_zero first second root
      firstNonNull secondNonNull rootEquation
  have sumNonzero :=
    root_add_dot_ne_zero first second root
      notParallel rootEquation
  change Line.Basic.lineNorm
    (positiveVertexBisector first second root firstNonNull notParallel) ≠ 0
  have productNonzero := ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero twoNonzero normNonzero) rootNonzero)
    sumNonzero
  intro normZero
  exact productNonzero
    ((positiveVertexBisector_norm first second root firstNonNull notParallel
      rootEquation).symm.trans normZero)

/-- The negative candidate is non-null for non-null, nonparallel input lines.

Two is nonzero and the supplied root squares to the product of the line norms. -/
theorem negativeVertexBisector_nonNull [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second) :
    ¬ (negativeVertexBisector first second root firstNonNull
      notParallel).IsNull := by
  have normNonzero : Line.Basic.lineNorm first ≠ 0 := firstNonNull
  have rootNonzero :=
    root_ne_zero first second root
      firstNonNull secondNonNull rootEquation
  have differenceNonzero :=
    root_sub_dot_ne_zero first second root
      notParallel rootEquation
  change Line.Basic.lineNorm
    (negativeVertexBisector first second root firstNonNull notParallel) ≠ 0
  have productNonzero := ExplicitField.mul_ne_zero
    (ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero twoNonzero normNonzero) rootNonzero)
    differenceNonzero
  intro normZero
  exact productNonzero
    ((negativeVertexBisector_norm first second root firstNonNull notParallel
      rootEquation).symm.trans normZero)

/-- The positive and negative normalized candidates are perpendicular when the supplied root squares to the product of
the line norms. -/
theorem vertexBisectors_perpendicular [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second)
    (rootEquation : root ^ 2 = Basic.lineNorm first * Basic.lineNorm second) :
    (positiveVertexBisector first second root firstNonNull notParallel).Perpendicular
      (negativeVertexBisector first second root firstNonNull notParallel) := by
  unfold Plane.Line.Perpendicular positiveVertexBisector
    negativeVertexBisector
  change
    (root * first.a + Basic.lineNorm first * second.a) *
        (root * first.a - Basic.lineNorm first * second.a) +
      (root * first.b + Basic.lineNorm first * second.b) *
        (root * first.b - Basic.lineNorm first * second.b) = 0
  calc
    (root * first.a + Basic.lineNorm first * second.a) *
          (root * first.a - Basic.lineNorm first * second.a) +
        (root * first.b + Basic.lineNorm first * second.b) *
          (root * first.b - Basic.lineNorm first * second.b) =
      root ^ 2 * Basic.lineNorm first -
        Basic.lineNorm first ^ 2 * Basic.lineNorm second := by
          unfold Basic.lineNorm
          ring1
    _ = 0 := by rw [rootEquation]; ring1

/-- The positive candidate contains every common point of the two input lines. -/
theorem positiveVertexBisector_contains_common_point
  [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second)
    (point : Plane.Point K) (onFirst : first.Contains point)
    (onSecond : second.Contains point) :
    (positiveVertexBisector first second root firstNonNull notParallel).Contains point := by
  unfold Plane.Line.Contains at onFirst onSecond ⊢
  unfold positiveVertexBisector
  calc
    (root * first.a + Line.Basic.lineNorm first * second.a) * point.x +
        (root * first.b + Line.Basic.lineNorm first * second.b) * point.y +
        (root * first.c + Line.Basic.lineNorm first * second.c) =
      root * (first.a * point.x + first.b * point.y + first.c) +
        Line.Basic.lineNorm first *
          (second.a * point.x + second.b * point.y + second.c) := by ring1
    _ = 0 := by rw [onFirst, onSecond]; ring1

/-- The negative candidate contains every common point of the two input lines. -/
theorem negativeVertexBisector_contains_common_point
  [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (notParallel : ¬ first.Parallel second)
    (point : Plane.Point K) (onFirst : first.Contains point)
    (onSecond : second.Contains point) :
    (negativeVertexBisector first second root firstNonNull notParallel).Contains point := by
  unfold Plane.Line.Contains at onFirst onSecond ⊢
  unfold negativeVertexBisector
  calc
    (root * first.a - Line.Basic.lineNorm first * second.a) * point.x +
        (root * first.b - Line.Basic.lineNorm first * second.b) * point.y +
        (root * first.c - Line.Basic.lineNorm first * second.c) =
      root * (first.a * point.x + first.b * point.y + first.c) -
        Line.Basic.lineNorm first *
          (second.a * point.x + second.b * point.y + second.c) := by ring1
    _ = 0 := by rw [onFirst, onSecond]; ring1

/-- The positive candidate makes equal spreads with the two input lines.

Both inputs are non-null and nonparallel, two is nonzero and the supplied root squares to their norm product. -/
theorem positiveVertexBisector_equal_spreads [DecidableEq
  K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second) :
    let bisector := positiveVertexBisector first second root firstNonNull notParallel
    let bisectorNonNull := positiveVertexBisector_nonNull first second
      root
      firstNonNull secondNonNull notParallel twoNonzero rootEquation
    Spread.spread first bisector firstNonNull bisectorNonNull =
      Spread.spread second bisector secondNonNull bisectorNonNull := by
  dsimp only
  let bisector := positiveVertexBisector first second root firstNonNull notParallel
  have bisectorNonNull := positiveVertexBisector_nonNull first second
    root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  have firstDenominatorNonzero : Line.Basic.lineNorm first * Line.Basic.lineNorm bisector ≠ 0 :=
    ExplicitField.mul_ne_zero firstNonNull bisectorNonNull
  have secondDenominatorNonzero : Line.Basic.lineNorm second * Line.Basic.lineNorm bisector ≠ 0 :=
    ExplicitField.mul_ne_zero secondNonNull bisectorNonNull
  have firstNumerator :
      (first.a * bisector.b - bisector.a * first.b) ^ 2 =
        (Line.Basic.lineNorm first *
          (first.a * second.b - second.a * first.b)) ^ 2 := by
    unfold bisector positiveVertexBisector
    ring1
  have secondNumerator :
      (second.a * bisector.b - bisector.a * second.b) ^ 2 =
        (root * (first.a * second.b - second.a * first.b)) ^ 2 := by
    unfold bisector positiveVertexBisector
    ring1
  unfold Spread.spread
  apply (fun {K : Type _} [ExplicitField K] [DecidableEq K] {leftNumerator rightNumerator
    leftDenominator rightDenominator : K} (leftNonzero : leftDenominator ≠ 0) (rightNonzero : rightDenominator ≠ 0)
    (crossProduct : leftNumerator * rightDenominator = rightNumerator * leftDenominator) =>
    (Purelib.Algebra.Field.Ratio.ratio_eq_of_cross_product (K := K) (leftNumerator := leftNumerator) (rightNumerator :=
    rightNumerator) (leftDenominator := leftDenominator) (rightDenominator := rightDenominator) leftNonzero rightNonzero
    crossProduct : leftNumerator / leftDenominator = rightNumerator / rightDenominator))
    firstDenominatorNonzero secondDenominatorNonzero
  rw [firstNumerator, secondNumerator]
  calc
    (Line.Basic.lineNorm first *
          (first.a * second.b - second.a * first.b)) ^ 2 *
        (Line.Basic.lineNorm second * Line.Basic.lineNorm bisector) =
      Line.Basic.lineNorm first ^ 2 * Line.Basic.lineNorm second *
        (first.a * second.b - second.a * first.b) ^ 2 *
          Line.Basic.lineNorm bisector := by ring1
    _ = root ^ 2 * Line.Basic.lineNorm first *
        (first.a * second.b - second.a * first.b) ^ 2 *
          Line.Basic.lineNorm bisector := by rw [rootEquation]; ring1
    _ = (root * (first.a * second.b - second.a * first.b)) ^ 2 *
        (Line.Basic.lineNorm first * Line.Basic.lineNorm bisector) := by ring1

/-- The negative candidate makes equal spreads with the two input lines.

Both inputs are non-null and nonparallel, two is nonzero and the supplied root squares to their norm product. -/
theorem negativeVertexBisector_equal_spreads [DecidableEq
  K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second) :
    let bisector := negativeVertexBisector first second root firstNonNull notParallel
    let bisectorNonNull := negativeVertexBisector_nonNull first second
      root
      firstNonNull secondNonNull notParallel twoNonzero rootEquation
    Spread.spread first bisector firstNonNull bisectorNonNull =
      Spread.spread second bisector secondNonNull bisectorNonNull := by
  dsimp only
  let bisector := negativeVertexBisector first second root firstNonNull notParallel
  have bisectorNonNull := negativeVertexBisector_nonNull first second
    root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  have firstDenominatorNonzero : Line.Basic.lineNorm first * Line.Basic.lineNorm bisector ≠ 0 :=
    ExplicitField.mul_ne_zero firstNonNull bisectorNonNull
  have secondDenominatorNonzero : Line.Basic.lineNorm second * Line.Basic.lineNorm bisector ≠ 0 :=
    ExplicitField.mul_ne_zero secondNonNull bisectorNonNull
  have firstNumerator :
      (first.a * bisector.b - bisector.a * first.b) ^ 2 =
        (Line.Basic.lineNorm first *
          (first.a * second.b - second.a * first.b)) ^ 2 := by
    unfold bisector negativeVertexBisector
    ring1
  have secondNumerator :
      (second.a * bisector.b - bisector.a * second.b) ^ 2 =
        (root * (first.a * second.b - second.a * first.b)) ^ 2 := by
    unfold bisector negativeVertexBisector
    ring1
  unfold Spread.spread
  apply (fun {K : Type _} [ExplicitField K] [DecidableEq K] {leftNumerator rightNumerator
    leftDenominator rightDenominator : K} (leftNonzero : leftDenominator ≠ 0) (rightNonzero : rightDenominator ≠ 0)
    (crossProduct : leftNumerator * rightDenominator = rightNumerator * leftDenominator) =>
    (Purelib.Algebra.Field.Ratio.ratio_eq_of_cross_product (K := K) (leftNumerator := leftNumerator) (rightNumerator :=
    rightNumerator) (leftDenominator := leftDenominator) (rightDenominator := rightDenominator) leftNonzero rightNonzero
    crossProduct : leftNumerator / leftDenominator = rightNumerator / rightDenominator))
    firstDenominatorNonzero secondDenominatorNonzero
  rw [firstNumerator, secondNumerator]
  calc
    (Line.Basic.lineNorm first *
          (first.a * second.b - second.a * first.b)) ^ 2 *
        (Line.Basic.lineNorm second * Line.Basic.lineNorm bisector) =
      Line.Basic.lineNorm first ^ 2 * Line.Basic.lineNorm second *
        (first.a * second.b - second.a * first.b) ^ 2 *
          Line.Basic.lineNorm bisector := by ring1
    _ = root ^ 2 * Line.Basic.lineNorm first *
        (first.a * second.b - second.a * first.b) ^ 2 *
          Line.Basic.lineNorm bisector := by rw [rootEquation]; ring1
    _ = (root * (first.a * second.b - second.a * first.b)) ^ 2 *
        (Line.Basic.lineNorm first * Line.Basic.lineNorm bisector) := by ring1

/-- The positive explicit candidate satisfies the book's bisector definition. -/
theorem positiveVertexBisector_isVertexBisector
  [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second) :
    VertexBisector.Basic.IsVertexBisector first second
      (positiveVertexBisector first second root firstNonNull
        notParallel)
      firstNonNull secondNonNull notParallel := by
  let bisectorNonNull := positiveVertexBisector_nonNull first second
    root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  refine ⟨bisectorNonNull, ?_, ?_⟩
  · exact positiveVertexBisector_contains_common_point first second root
      firstNonNull notParallel (Intersection.lineIntersection first second notParallel)
      (Intersection.lineIntersection_on_first first second notParallel)
      (Intersection.lineIntersection_on_second first second notParallel)
  · exact positiveVertexBisector_equal_spreads first second root
      firstNonNull secondNonNull notParallel twoNonzero rootEquation

/-- The negative explicit candidate satisfies the book's bisector definition. -/
theorem negativeVertexBisector_isVertexBisector
  [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second) :
    VertexBisector.Basic.IsVertexBisector first second
      (negativeVertexBisector first second root firstNonNull
        notParallel)
      firstNonNull secondNonNull notParallel := by
  let bisectorNonNull := negativeVertexBisector_nonNull first second
    root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  refine ⟨bisectorNonNull, ?_, ?_⟩
  · exact negativeVertexBisector_contains_common_point first second root
      firstNonNull notParallel (Intersection.lineIntersection first second notParallel)
      (Intersection.lineIntersection_on_first first second notParallel)
      (Intersection.lineIntersection_on_second first second notParallel)
  · exact negativeVertexBisector_equal_spreads first second root
      firstNonNull secondNonNull notParallel twoNonzero rootEquation

/-- The two constructed bisectors are genuinely distinct ordered proportions. -/
theorem vertexBisectors_not_equivalent [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = Basic.lineNorm first * Basic.lineNorm second) :
    ¬ (positiveVertexBisector first second root firstNonNull
      notParallel).Equivalent
      (negativeVertexBisector first second root firstNonNull
        notParallel) := by
  let positive := positiveVertexBisector first second root
    firstNonNull notParallel
  let negative := negativeVertexBisector first second root
    firstNonNull notParallel
  have positiveNonNull : ¬ positive.IsNull :=
    positiveVertexBisector_nonNull first second root firstNonNull
      secondNonNull
      notParallel twoNonzero rootEquation
  have negativeNonNull : ¬ negative.IsNull :=
    negativeVertexBisector_nonNull first second root firstNonNull
      secondNonNull
      notParallel twoNonzero rootEquation
  have perpendicular : positive.Perpendicular negative :=
    vertexBisectors_perpendicular first second root firstNonNull
      notParallel
      rootEquation
  intro equivalent
  have determinantZero :
      positive.a * negative.b - negative.a * positive.b = 0 := by
    unfold Plane.Line.Equivalent at equivalent
    calc
      positive.a * negative.b - negative.a * positive.b =
          negative.a * positive.b - negative.a * positive.b := by
            rw [equivalent.1]
      _ = 0 := by ring1
  have dotZero : positive.a * negative.a + positive.b * negative.b = 0 := by
    exact perpendicular
  have normProductZero : Basic.lineNorm positive * Basic.lineNorm negative = 0 := by
    calc
      Basic.lineNorm positive * Basic.lineNorm negative =
          (positive.a * negative.b - negative.a * positive.b) ^ 2 +
            (positive.a * negative.a + positive.b * negative.b) ^ 2 := by
              unfold Basic.lineNorm
              ring1
      _ = 0 := by rw [determinantZero, dotZero]; ring1
  exact (ExplicitField.mul_ne_zero positiveNonNull negativeNonNull)
    normProductZero

/-- The constructive existence and perpendicularity clauses of Theorem 45. The square root is input data rather than a
choice-produced root. -/
theorem vertex_bisector_pair [DecidableEq K]
    (first second : Plane.Line K) (root : K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (notParallel : ¬ first.Parallel second)
    (twoNonzero : (2 : K) ≠ 0)
    (rootEquation : root ^ 2 = Line.Basic.lineNorm first * Line.Basic.lineNorm second) :
    let positive := positiveVertexBisector first second root
      firstNonNull notParallel
    let negative := negativeVertexBisector first second root
      firstNonNull notParallel
    ∃ positiveNonNull : ¬ positive.IsNull,
    ∃ negativeNonNull : ¬ negative.IsNull,
      Spread.spread first positive firstNonNull positiveNonNull =
          Spread.spread second positive secondNonNull positiveNonNull ∧
        Spread.spread first negative firstNonNull negativeNonNull =
          Spread.spread second negative secondNonNull negativeNonNull ∧
        positive.Perpendicular negative := by
  dsimp only
  let positiveNonNull := positiveVertexBisector_nonNull first second
    root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  let negativeNonNull := negativeVertexBisector_nonNull first second
    root
    firstNonNull secondNonNull notParallel twoNonzero rootEquation
  exact ⟨positiveNonNull, negativeNonNull,
    positiveVertexBisector_equal_spreads first second root firstNonNull
      secondNonNull notParallel twoNonzero rootEquation,
    negativeVertexBisector_equal_spreads first second root firstNonNull
      secondNonNull notParallel twoNonzero rootEquation,
    vertexBisectors_perpendicular first second root firstNonNull
      notParallel
      rootEquation⟩
end Purelib.Geometry.Plane.Line.VertexBisector.Construction

end
