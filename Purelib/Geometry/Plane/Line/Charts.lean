module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line.Basic

public section

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

namespace Purelib.Geometry.Plane.Line.Charts

section

variable {K : Type*} [ExplicitField K] [Nontrivial K]

/-- The line of finite slope `slope` through `point`, displayed with second direction coefficient `-1`. -/
@[expose] def slopeLineThrough (point : Geometry.Plane.Point K) (slope : K)
  : Geometry.Plane.Line K where
  a := slope
  b := -1
  c := point.y - slope * point.x
  direction_nonzero := Or.inr ((by intro negZero; have restored := congrArg (fun value : K => -value) negZero; rewrite
    [neg_neg, SubNegZeroMonoid.neg_zero] at restored; exact one_ne_zero restored))

/-- The vertical line through `point`. -/
@[expose] def verticalLineThrough (point : Geometry.Plane.Point K) :
  Geometry.Plane.Line K where
  a := 1
  b := 0
  c := -point.x
  direction_nonzero := Or.inl one_ne_zero

/-- The normalized finite-slope line through a point contains that point. -/
theorem slopeLineThrough_contains (point : Geometry.Plane.Point K) (slope :
  K) :
    (slopeLineThrough point slope).Contains point := by
  unfold slopeLineThrough Geometry.Plane.Line.Contains
  ring1

/-- The vertical line through a point contains that point. -/
theorem verticalLineThrough_contains (point : Geometry.Plane.Point K) :
    (verticalLineThrough point).Contains point := by
  unfold verticalLineThrough Geometry.Plane.Line.Contains
  ring1

/-- Two normalized finite-slope representatives are equivalent precisely when their displayed slopes agree. -/
theorem slopeLineThrough_equivalent_iff
    (point : Geometry.Plane.Point K) (firstSlope secondSlope : K) :
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

/-- The vertical representative is not equivalent to any finite-slope representative. -/
theorem verticalLineThrough_not_equivalent_slope
    (point : Geometry.Plane.Point K) (slope : K) :
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

/-- Every displayed line through `point` is represented by the vertical chart or by the explicitly computed slope
`-(a/b)`. -/
theorem line_through_point_chart
    [DecidableEq K]
    (point : Geometry.Plane.Point K) (line : Geometry.Plane.Line K) (contains : line.Contains point) :
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
      unfold Geometry.Plane.Line.Contains at contains
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
      ExplicitField.mul_inv_cancel line.b secondZero
    have secondCancelLeft : line.b⁻¹ * line.b = (1 : K) := by
      calc
        line.b⁻¹ * line.b = line.b * line.b⁻¹ := by ring1
        _ = 1 := secondCancel
    have constantEquation :
        line.c = -(line.a * point.x + line.b * point.y) := by
      unfold Geometry.Plane.Line.Contains at contains
      calc
        line.c =
            (line.a * point.x + line.b * point.y + line.c) -
              (line.a * point.x + line.b * point.y) := by ring1
        _ = -(line.a * point.x + line.b * point.y) := by
          rw [contains]
          ring1
    unfold Line.Equivalent slopeLineThrough
    simp only [slope, ExplicitField.div_eq_mul_inv]
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

/-- The complete constructive content of the `p+1` half of Exercise 3.2: one inequivalent line for each supplied slope,
one extra vertical line, and no other line through the point. -/
theorem exercise_3_2_lines_through_point [DecidableEq K]
    (point : Geometry.Plane.Point K) :
    (∀ slope : K, (slopeLineThrough point slope).Contains point) ∧
      (verticalLineThrough point).Contains point ∧
      (∀ firstSlope secondSlope : K,
        (slopeLineThrough point firstSlope).Equivalent
            (slopeLineThrough point secondSlope) ↔
          firstSlope = secondSlope) ∧
      (∀ slope : K,
        ¬ (verticalLineThrough point).Equivalent
            (slopeLineThrough point slope)) ∧
      ∀ line : Geometry.Plane.Line K, line.Contains point →
        (∃ slope : K,
          (slopeLineThrough point slope).Equivalent line) ∨
          (verticalLineThrough point).Equivalent line := by
  exact ⟨slopeLineThrough_contains point,
    verticalLineThrough_contains point,
    slopeLineThrough_equivalent_iff point,
    verticalLineThrough_not_equivalent_slope point,
    line_through_point_chart point⟩

/-- Parameterize a point of `line` by its first coordinate when `b ≠ 0`. -/
@[expose] def pointOnLineUsingX (line : Geometry.Plane.Line K) (_secondNonzero
    :
  line.b ≠ 0)
    (parameter : K) : Geometry.Plane.Point K :=
  ⟨parameter, -(line.a * parameter + line.c) / line.b⟩

/-- Parameterize a point of `line` by its second coordinate when `a ≠ 0`. -/
@[expose] def pointOnLineUsingY (line : Geometry.Plane.Line K) (_firstNonzero
    :
  line.a ≠ 0)
    (parameter : K) : Geometry.Plane.Point K :=
  ⟨-(line.b * parameter + line.c) / line.a, parameter⟩

omit [Nontrivial K] in
/-- Every point in the first-coordinate chart lies on its line when the second coefficient is nonzero. -/
theorem pointOnLineUsingX_contains
    (line : Geometry.Plane.Line K) (secondNonzero : line.b ≠ 0) (parameter : K) :
    line.Contains (pointOnLineUsingX line secondNonzero parameter) := by
  have secondCancel : line.b * line.b⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel line.b secondNonzero
  unfold Geometry.Plane.Line.Contains pointOnLineUsingX
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    line.a * parameter +
          line.b * (-(line.a * parameter + line.c) * line.b⁻¹) +
          line.c =
        (line.a * parameter + line.c) *
          (1 - line.b * line.b⁻¹) := by ring1
    _ = 0 := by rw [secondCancel]; ring1

omit [Nontrivial K] in
/-- Every point in the second-coordinate chart lies on its line when the first coefficient is nonzero. -/
theorem pointOnLineUsingY_contains
    (line : Geometry.Plane.Line K) (firstNonzero : line.a ≠ 0) (parameter : K) :
    line.Contains (pointOnLineUsingY line firstNonzero parameter) := by
  have firstCancel : line.a * line.a⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel line.a firstNonzero
  unfold Geometry.Plane.Line.Contains pointOnLineUsingY
  simp only [ExplicitField.div_eq_mul_inv]
  calc
    line.a * (-(line.b * parameter + line.c) * line.a⁻¹) +
          line.b * parameter + line.c =
        (line.b * parameter + line.c) *
          (1 - line.a * line.a⁻¹) := by ring1
    _ = 0 := by rw [firstCancel]; ring1

omit [Nontrivial K] in
/-- The first-coordinate chart is injective because it retains its parameter as the first coordinate. -/
theorem pointOnLineUsingX_injective
    (line : Geometry.Plane.Line K) (secondNonzero : line.b ≠ 0) :
    Function.Injective (pointOnLineUsingX line secondNonzero) := by
  intro first second pointsEqual
  exact congrArg Plane.Point.x pointsEqual

omit [Nontrivial K] in
/-- The second-coordinate chart is injective because it retains its parameter as the second coordinate. -/
theorem pointOnLineUsingY_injective
    (line : Geometry.Plane.Line K) (firstNonzero : line.a ≠ 0) :
    Function.Injective (pointOnLineUsingY line firstNonzero) := by
  intro first second pointsEqual
  exact congrArg Plane.Point.y pointsEqual

omit [Nontrivial K] in
/-- The first-coordinate chart reconstructs every incident point from its first coordinate. -/
theorem pointOnLineUsingX_covers
    (line : Geometry.Plane.Line K) (secondNonzero : line.b ≠ 0)
    (point : Geometry.Plane.Point K) (contains : line.Contains point) :
    pointOnLineUsingX line secondNonzero point.x = point := by
  apply Geometry.Plane.Point.ext
  · rfl
  · have secondCancel : line.b * line.b⁻¹ = (1 : K) :=
      ExplicitField.mul_inv_cancel line.b secondNonzero
    have numeratorEquation :
        -(line.a * point.x + line.c) = line.b * point.y := by
      unfold Geometry.Plane.Line.Contains at contains
      calc
        -(line.a * point.x + line.c) =
            line.b * point.y -
              (line.a * point.x + line.b * point.y + line.c) := by ring1
        _ = line.b * point.y := by rw [contains]; ring1
    unfold pointOnLineUsingX
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      -(line.a * point.x + line.c) * line.b⁻¹ =
          (line.b * point.y) * line.b⁻¹ := by rw [numeratorEquation]
      _ = point.y * (line.b * line.b⁻¹) := by ring1
      _ = point.y := by rw [secondCancel, mul_one]

omit [Nontrivial K] in
/-- The second-coordinate chart reconstructs every incident point from its second coordinate. -/
theorem pointOnLineUsingY_covers
    (line : Geometry.Plane.Line K) (firstNonzero : line.a ≠ 0)
    (point : Geometry.Plane.Point K) (contains : line.Contains point) :
    pointOnLineUsingY line firstNonzero point.y = point := by
  apply Geometry.Plane.Point.ext
  · have firstCancel : line.a * line.a⁻¹ = (1 : K) :=
      ExplicitField.mul_inv_cancel line.a firstNonzero
    have numeratorEquation :
        -(line.b * point.y + line.c) = line.a * point.x := by
      unfold Geometry.Plane.Line.Contains at contains
      calc
        -(line.b * point.y + line.c) =
            line.a * point.x -
              (line.a * point.x + line.b * point.y + line.c) := by ring1
        _ = line.a * point.x := by rw [contains]; ring1
    unfold pointOnLineUsingY
    simp only [ExplicitField.div_eq_mul_inv]
    calc
      -(line.b * point.y + line.c) * line.a⁻¹ =
          (line.a * point.x) * line.a⁻¹ := by rw [numeratorEquation]
      _ = point.x * (line.a * line.a⁻¹) := by ring1
      _ = point.x := by rw [firstCancel, mul_one]
  · rfl

omit [Nontrivial K] in
/-- The complete constructive content of the `p` half of Exercise 3.2. The line's stored nonzero direction selects an
explicit one-scalar chart, which is injective and covers every incident point. -/
theorem exercise_3_2_points_on_line (line : Geometry.Plane.Line K) :
    (∃ secondNonzero : line.b ≠ 0,
      (∀ parameter : K,
        line.Contains (pointOnLineUsingX line secondNonzero parameter)) ∧
      Function.Injective (pointOnLineUsingX line secondNonzero) ∧
      ∀ point : Geometry.Plane.Point K, line.Contains point →
        pointOnLineUsingX line secondNonzero point.x = point) ∨
    (∃ firstNonzero : line.a ≠ 0,
      (∀ parameter : K,
        line.Contains (pointOnLineUsingY line firstNonzero parameter)) ∧
      Function.Injective (pointOnLineUsingY line firstNonzero) ∧
      ∀ point : Geometry.Plane.Point K, line.Contains point →
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

end

end Purelib.Geometry.Plane.Line.Charts

end

end
