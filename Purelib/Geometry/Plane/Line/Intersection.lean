module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

@[expose] public section

/-!
# Divine Proportions, Chapter 3: points, lines, and incidence

Lines are finite coefficient records, not sets of points and not quotients.
`Line.Equivalent` records the three cross-product equations expressing equality
of the ordered proportions.  This follows the source's finite algebra while
keeping every construction executable over both finite fields and the
constructive rationals.
-/

namespace Purelib.Geometry.Plane.Line.Intersection

variable {K : Type*}

section Incidence

variable [ExplicitField K]

/-- The explicit intersection point of two nonparallel lines. -/
def lineIntersection (first second : Plane.Line K)
    (_nonparallel : ¬ first.Parallel second) : Plane.Point K :=
  { x := (first.b * second.c - second.b * first.c) /
      (first.a * second.b - second.a * first.b)
    y := (first.c * second.a - second.c * first.a) /
      (first.a * second.b - second.a * first.b) }

section
open _root_.Purelib.Geometry
/-- The direction determinant of two nonparallel displayed lines is nonzero. -/
private theorem nonparallel_denominator_ne_zero
    {first second : Line K} (nonparallel : ¬ first.Parallel second) :
    first.a * second.b - second.a * first.b ≠ 0 := by
  exact nonparallel
end

/-- The explicit intersection of two nonparallel lines lies on the first line. -/
theorem lineIntersection_on_first (first second : Plane.Line K)
    (nonparallel : ¬ first.Parallel second) :
    first.Contains (lineIntersection first second nonparallel) := by
  let denominator := first.a * second.b - second.a * first.b
  have denominatorNonzero : denominator ≠ 0 :=
    nonparallel_denominator_ne_zero nonparallel
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold Plane.Line.Contains lineIntersection
  simp only [ExplicitField.div_eq_mul_inv]
  change first.a * ((first.b * second.c - second.b * first.c) * denominator⁻¹) +
      first.b * ((first.c * second.a - second.c * first.a) * denominator⁻¹) +
      first.c = 0
  calc
    first.a * ((first.b * second.c - second.b * first.c) * denominator⁻¹) +
        first.b * ((first.c * second.a - second.c * first.a) * denominator⁻¹) +
        first.c = -first.c * (denominator * denominator⁻¹) + first.c := by
      unfold denominator
      ring1
    _ = 0 := by rw [denominatorCancel]; ring1

/-- The explicit intersection of two nonparallel lines lies on the second line. -/
theorem lineIntersection_on_second (first second : Plane.Line K)
    (nonparallel : ¬ first.Parallel second) :
    second.Contains (lineIntersection first second nonparallel) := by
  let denominator := first.a * second.b - second.a * first.b
  have denominatorNonzero : denominator ≠ 0 :=
    nonparallel_denominator_ne_zero nonparallel
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold Plane.Line.Contains lineIntersection
  simp only [ExplicitField.div_eq_mul_inv]
  change second.a * ((first.b * second.c - second.b * first.c) * denominator⁻¹) +
      second.b * ((first.c * second.a - second.c * first.a) * denominator⁻¹) +
      second.c = 0
  calc
    second.a * ((first.b * second.c - second.b * first.c) * denominator⁻¹) +
        second.b * ((first.c * second.a - second.c * first.a) * denominator⁻¹) +
        second.c = -second.c * (denominator * denominator⁻¹) + second.c := by
      unfold denominator
      ring1
    _ = 0 := by rw [denominatorCancel]; ring1

/-- If three displayed lines have zero coefficient determinant, the third line contains the explicit intersection of two
nonparallel ones. -/
theorem lineIntersection_on_third_of_determinant_eq_zero
    (first second third : Plane.Line K)
    (nonparallel : ¬ first.Parallel second)
    (determinantZero : Incidence.lineDeterminant first second third = 0) :
    third.Contains (lineIntersection first second nonparallel) := by
  let denominator := first.a * second.b - second.a * first.b
  have denominatorNonzero : denominator ≠ 0 := nonparallel
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold Plane.Line.Contains lineIntersection
  simp only [ExplicitField.div_eq_mul_inv]
  change
    third.a * ((first.b * second.c - second.b * first.c) *
        denominator⁻¹) +
      third.b * ((first.c * second.a - second.c * first.a) *
        denominator⁻¹) + third.c = 0
  calc
    third.a * ((first.b * second.c - second.b * first.c) *
          denominator⁻¹) +
        third.b * ((first.c * second.a - second.c * first.a) *
          denominator⁻¹) + third.c =
      Incidence.lineDeterminant first second third * denominator⁻¹ +
        third.c * (1 - denominator * denominator⁻¹) := by
          unfold Incidence.lineDeterminant denominator
          ring1
    _ = 0 := by rw [determinantZero, denominatorCancel]; ring1

/-- Theorem 5 (Point on two lines), uniqueness of the displayed intersection. -/
theorem lineIntersection_unique (first second : Plane.Line K)
    (nonparallel : ¬ first.Parallel second) (point : Plane.Point K)
    (onFirst : first.Contains point) (onSecond : second.Contains point) :
    point = lineIntersection first second nonparallel := by
  let denominator := first.a * second.b - second.a * first.b
  have denominatorNonzero : denominator ≠ 0 :=
    nonparallel_denominator_ne_zero nonparallel
  have denominatorCancel : denominator * denominator⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel denominator denominatorNonzero
  unfold Plane.Line.Contains at onFirst onSecond
  apply Plane.Point.ext
  · have clearedX :
        denominator * point.x = first.b * second.c - second.b * first.c := by
      unfold denominator
      calc
        (first.a * second.b - second.a * first.b) * point.x =
            second.b * (first.a * point.x + first.b * point.y + first.c) -
              first.b * (second.a * point.x + second.b * point.y + second.c) +
              (first.b * second.c - second.b * first.c) := by ring1
        _ = first.b * second.c - second.b * first.c := by
          rw [onFirst, onSecond]
          ring1
    unfold lineIntersection
    simp only [ExplicitField.div_eq_mul_inv]
    rw [← clearedX]
    calc
      point.x = point.x * 1 := by rw [mul_one]
      _ = point.x * (denominator * denominator⁻¹) := by rw [denominatorCancel]
      _ = denominator * point.x * denominator⁻¹ := by ring1
  · have clearedY :
        denominator * point.y = first.c * second.a - second.c * first.a := by
      unfold denominator
      calc
        (first.a * second.b - second.a * first.b) * point.y =
            first.a * (second.a * point.x + second.b * point.y + second.c) -
              second.a * (first.a * point.x + first.b * point.y + first.c) +
              (first.c * second.a - second.c * first.a) := by ring1
        _ = first.c * second.a - second.c * first.a := by
          rw [onFirst, onSecond]
          ring1
    unfold lineIntersection
    simp only [ExplicitField.div_eq_mul_inv]
    rw [← clearedY]
    calc
      point.y = point.y * 1 := by rw [mul_one]
      _ = point.y * (denominator * denominator⁻¹) := by rw [denominatorCancel]
      _ = denominator * point.y * denominator⁻¹ := by ring1
end Incidence

end Purelib.Geometry.Plane.Line.Intersection

end
