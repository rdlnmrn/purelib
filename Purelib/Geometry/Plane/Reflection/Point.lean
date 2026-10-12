module

import Purelib.Algebra.Field.Characteristic.Nonzero
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.Cancellation
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Line.Altitude
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
public import Purelib.Geometry.Plane.Line.Quadrance
import Purelib.Geometry.Plane.Line.Quadrance.Spread
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Point.Quadrance

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.HalfTurn.Basic
import Purelib.Geometry.Plane.Transformation.Affine
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Algebra.Field
open Purelib.Geometry
open Purelib.Geometry.Plane
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Line.Quadrance
open Purelib.Geometry.Plane.Point
open Purelib.Geometry.Plane.Transformation

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
section
public section

/-!
# Divine Proportions, Chapter 4: point reflections

The reflection in a non-null line is defined exactly as in the book: find the
altitude foot and rotate the source point through that foot.  Theorem 13's
coordinate formula and the involution law are then derived by finite field
algebra.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Reflection.Point

/-- Reflection in a non-null line, defined geometrically through the altitude foot as in §4.1. -/
@[expose] def reflectPoint (line : Line K) (nonNull : ¬ line.IsNull)
    (point : Point K) : Point K :=
  HalfTurn.Basic.rotateInPoint (Altitude.altitudeFoot point line nonNull) point

/-- The rational coordinate formula for reflection in a displayed line.

Its denominator is the line's direction norm; equality with geometric reflection requires that norm to be nonzero. -/
@[expose] def reflectionFormula (line : Line K) (point : Point K) : Point
  K :=
  ⟨(((line.b ^ 2 - line.a ^ 2) * point.x -
      2 * line.a * line.b * point.y - 2 * line.a * line.c) /
      Line.Basic.lineNorm line),
    ((-2 * line.a * line.b * point.x +
      (line.a ^ 2 - line.b ^ 2) * point.y - 2 * line.b * line.c) /
      Line.Basic.lineNorm line)⟩

/-- Theorem 13 (Reflection of a point in a line): derivation of the printed coordinate formula from the altitude-foot
definition. -/
theorem reflectPoint_formula (line : Line K) (nonNull : ¬ line.IsNull)
    (point : Point K) :
    Geometry.Plane.Reflection.Point.reflectPoint line nonNull point = Geometry.Plane.Reflection.Point.reflectionFormula
      line point := by
  have normNonzero : Basic.lineNorm line ≠ 0 := nonNull
  have normCancel : Basic.lineNorm line * (Basic.lineNorm line)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ normNonzero
  apply Point.ext
  · change
      2 * ((line.b ^ 2 * point.x - line.a * line.b * point.y -
          line.a * line.c) / Basic.lineNorm line) - point.x =
        ((line.b ^ 2 - line.a ^ 2) * point.x -
          2 * line.a * line.b * point.y - 2 * line.a * line.c) /
          Basic.lineNorm line
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      2 *
            ((line.b ^ 2 * point.x - line.a * line.b * point.y -
                line.a * line.c) * (Basic.lineNorm line)⁻¹) - point.x =
        2 *
            ((line.b ^ 2 * point.x - line.a * line.b * point.y -
                line.a * line.c) * (Basic.lineNorm line)⁻¹) -
          point.x * (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) := by
        rw [normCancel]
        ring1
      _ = ((line.b ^ 2 - line.a ^ 2) * point.x -
          2 * line.a * line.b * point.y - 2 * line.a * line.c) *
          (Basic.lineNorm line)⁻¹ := by
        unfold Basic.lineNorm
        ring1
  · change
      2 * ((-line.a * line.b * point.x + line.a ^ 2 * point.y -
          line.b * line.c) / Basic.lineNorm line) - point.y =
        (-2 * line.a * line.b * point.x +
          (line.a ^ 2 - line.b ^ 2) * point.y - 2 * line.b * line.c) /
          Basic.lineNorm line
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      2 *
            ((-line.a * line.b * point.x + line.a ^ 2 * point.y -
                line.b * line.c) * (Basic.lineNorm line)⁻¹) - point.y =
        2 *
            ((-line.a * line.b * point.x + line.a ^ 2 * point.y -
                line.b * line.c) * (Basic.lineNorm line)⁻¹) -
          point.y * (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) := by
        rw [normCancel]
        ring1
      _ = (-2 * line.a * line.b * point.x +
          (line.a ^ 2 - line.b ^ 2) * point.y - 2 * line.b * line.c) *
          (Basic.lineNorm line)⁻¹ := by
        unfold Basic.lineNorm
        ring1

/-- Exercise 4.3, affine half: reflection in a non-null line is affine. -/
theorem reflectPoint_affine (line : Line K) (nonNull : ¬ line.IsNull) :
    Affine.IsAffine (Geometry.Plane.Reflection.Point.reflectPoint line nonNull) := by
  intro first second leftWeight rightWeight weights
  have rightFormula : rightWeight = 1 - leftWeight := by
    calc
      rightWeight = (leftWeight + rightWeight) - leftWeight := by ring1
      _ = 1 - leftWeight := by rw [weights]
  rw [rightFormula]
  rw [Geometry.Plane.Reflection.Point.reflectPoint_formula, Geometry.Plane.Reflection.Point.reflectPoint_formula,
    Geometry.Plane.Reflection.Point.reflectPoint_formula]
  apply Point.ext <;>
    unfold Reflection.Point.reflectionFormula Affine.affineCombination <;>
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv] <;>
    ring1

/-- Exercise 4.3, inverse half: reflection in a non-null line is its own inverse. -/
theorem reflectPoint_involutive (line : Line K) (nonNull : ¬ line.IsNull)
    (point : Point K) :
    Geometry.Plane.Reflection.Point.reflectPoint line nonNull (Geometry.Plane.Reflection.Point.reflectPoint line nonNull
      point) = point := by
  have normNonzero : Basic.lineNorm line ≠ 0 := nonNull
  have normCancel : Basic.lineNorm line * (Basic.lineNorm line)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ normNonzero
  rw [Geometry.Plane.Reflection.Point.reflectPoint_formula, Geometry.Plane.Reflection.Point.reflectPoint_formula]
  apply Point.ext
  · change
      (((line.b ^ 2 - line.a ^ 2) *
            (((line.b ^ 2 - line.a ^ 2) * point.x -
              2 * line.a * line.b * point.y - 2 * line.a * line.c) /
              Basic.lineNorm line) -
          2 * line.a * line.b *
            ((-2 * line.a * line.b * point.x +
              (line.a ^ 2 - line.b ^ 2) * point.y -
              2 * line.b * line.c) / Basic.lineNorm line) -
          2 * line.a * line.c) / Basic.lineNorm line) = point.x
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      ((line.b ^ 2 - line.a ^ 2) *
              (((line.b ^ 2 - line.a ^ 2) * point.x -
                2 * line.a * line.b * point.y - 2 * line.a * line.c) *
                (Basic.lineNorm line)⁻¹) -
            2 * line.a * line.b *
              ((-2 * line.a * line.b * point.x +
                (line.a ^ 2 - line.b ^ 2) * point.y -
                2 * line.b * line.c) * (Basic.lineNorm line)⁻¹) -
            2 * line.a * line.c) * (Basic.lineNorm line)⁻¹ =
        point.x * (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) ^ 2 +
          2 * line.a * line.c * (Basic.lineNorm line)⁻¹ *
            (Basic.lineNorm line * (Basic.lineNorm line)⁻¹ - 1) := by
          unfold Basic.lineNorm
          ring1
      _ = point.x := by rw [normCancel]; ring1
  · change
      ((-2 * line.a * line.b *
            (((line.b ^ 2 - line.a ^ 2) * point.x -
              2 * line.a * line.b * point.y - 2 * line.a * line.c) /
              Basic.lineNorm line) +
          (line.a ^ 2 - line.b ^ 2) *
            ((-2 * line.a * line.b * point.x +
              (line.a ^ 2 - line.b ^ 2) * point.y -
              2 * line.b * line.c) / Basic.lineNorm line) -
          2 * line.b * line.c) / Basic.lineNorm line) = point.y
    simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
    calc
      (-2 * line.a * line.b *
              (((line.b ^ 2 - line.a ^ 2) * point.x -
                2 * line.a * line.b * point.y - 2 * line.a * line.c) *
                (Basic.lineNorm line)⁻¹) +
            (line.a ^ 2 - line.b ^ 2) *
              ((-2 * line.a * line.b * point.x +
                (line.a ^ 2 - line.b ^ 2) * point.y -
                2 * line.b * line.c) * (Basic.lineNorm line)⁻¹) -
            2 * line.b * line.c) * (Basic.lineNorm line)⁻¹ =
        point.y * (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) ^ 2 +
          2 * line.b * line.c * (Basic.lineNorm line)⁻¹ *
            (Basic.lineNorm line * (Basic.lineNorm line)⁻¹ - 1) := by
          unfold Basic.lineNorm
          ring1
      _ = point.y := by rw [normCancel]; ring1

end Purelib.Geometry.Plane.Reflection.Point

end

end

end

end

section
public section

/-!
# Divine Proportions, conic axes

An axis is retained as an explicit non-null mirror together with the finite
equation-preservation identity from Exercise 15.8.  The elementary reflection
lemmas below construct the two mirrors used for quadrolas without selecting
any roots or completed geometric object.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Reflection.Point.Axis

/-- A point on a non-null mirror is fixed by the executable reflection map. -/
theorem reflectPoint_fixed_of_contains (line : Line K)
    (nonNull : ¬ line.IsNull) (point : Point K)
    (contains : line.Contains point) :
    Reflection.Point.reflectPoint line nonNull point = point := by
  have pointIsFoot : point = Altitude.altitudeFoot point line nonNull :=
    Altitude.altitudeFoot_unique point line nonNull point contains
      (Construction.altitudeThrough_contains point line)
  unfold Reflection.Point.reflectPoint
  rw [← pointIsFoot]
  apply Point.ext <;> unfold HalfTurn.Basic.rotateInPoint <;> ring1

end Purelib.Geometry.Plane.Reflection.Point.Axis

end

end

section
public section

/-!
# Divine Proportions, Exercise 15.18

The two axes of a grammola are constructed from an explicit square witness
for the product of its diagonal norms.  Reflection in either normalized
vertex bisector swaps the two weighted squared line values, so it preserves
the grammola equation.  Conversely, two finite reflection probes show that
every axis satisfies the equal-spread bisector equation.
-/

section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Reflection.Point

/-- Reflection transports a half-turn by reflecting both its center and its argument. -/
public theorem reflectPoint_rotateInPoint (axis : Line K)
    (axisNonNull : ¬ axis.IsNull) (center point : Point K) :
    Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull (HalfTurn.Basic.rotateInPoint center point) =
      HalfTurn.Basic.rotateInPoint (Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull center)
        (Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull point) := by
  have affine := Geometry.Plane.Reflection.Point.reflectPoint_affine axis axisNonNull center point
    (2 : K) (-1 : K) (by ring1)
  calc
    Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull (HalfTurn.Basic.rotateInPoint center point) =
      Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull
        (Affine.affineCombination 2 center (-1) point) := by
          congr 1
          apply Point.ext <;> unfold HalfTurn.Basic.rotateInPoint Affine.affineCombination <;> ring1
    _ = Affine.affineCombination 2 (Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull center)
        (-1) (Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull point) := affine
    _ = HalfTurn.Basic.rotateInPoint (Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull center)
        (Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull point) := by
          apply Point.ext <;> unfold HalfTurn.Basic.rotateInPoint Affine.affineCombination <;> ring1

/-- A fixed point of reflection lies on its non-null mirror when two is nonzero. -/
public theorem contains_of_reflectPoint_fixed (axis : Line K)
    (axisNonNull : ¬ axis.IsNull) (twoNonzero : (2 : K) ≠ 0)
    (point : Point K) (fixed : Geometry.Plane.Reflection.Point.reflectPoint axis axisNonNull point =
      point) :
    axis.Contains point := by
  have xFixed := congrArg (Point.x (K := K)) fixed
  have yFixed := congrArg (Point.y (K := K)) fixed
  have twiceXZero :
      2 * ((Altitude.altitudeFoot point axis axisNonNull).x - point.x) = 0 := by
    change 2 * (Altitude.altitudeFoot point axis axisNonNull).x - point.x = point.x
      at xFixed
    calc
      2 * ((Altitude.altitudeFoot point axis axisNonNull).x - point.x) =
          (2 * (Altitude.altitudeFoot point axis axisNonNull).x - point.x) -
            point.x := by ring1
      _ = 0 := by rw [xFixed]; ring1
  have twiceYZero :
      2 * ((Altitude.altitudeFoot point axis axisNonNull).y - point.y) = 0 := by
    change 2 * (Altitude.altitudeFoot point axis axisNonNull).y - point.y = point.y
      at yFixed
    calc
      2 * ((Altitude.altitudeFoot point axis axisNonNull).y - point.y) =
          (2 * (Altitude.altitudeFoot point axis axisNonNull).y - point.y) -
            point.y := by ring1
      _ = 0 := by rw [yFixed]; ring1
  have footEqualsPoint : Altitude.altitudeFoot point axis axisNonNull = point := by
    apply Point.ext
    · have differenceZero := Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero twiceXZero
      calc
        (Altitude.altitudeFoot point axis axisNonNull).x =
            ((Altitude.altitudeFoot point axis axisNonNull).x - point.x) + point.x := by
              ring1
        _ = point.x := by rw [differenceZero]; ring1
    · have differenceZero := Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left twoNonzero twiceYZero
      calc
        (Altitude.altitudeFoot point axis axisNonNull).y =
            ((Altitude.altitudeFoot point axis axisNonNull).y - point.y) + point.y := by
              ring1
        _ = point.y := by rw [differenceZero]; ring1
  rw [← footEqualsPoint]
  exact Altitude.altitudeFoot_on_line point axis axisNonNull

end Purelib.Geometry.Plane.Reflection.Point

end

end

end

section
public section

/-!
# Divine Proportions, Exercise 13.3: central reflection mirrors

Reflection in a non-null central line has the book's central-reflection
coordinates.  Conversely, a unit parameter pair constructively determines a
central non-null mirror, unique up to the project's quotient-free
`Line.Equivalent` relation.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Reflection.Point

/-- A point is fixed by reflection in a non-null line exactly when it lies on the mirror. -/
theorem reflectPoint_fixed_iff_contains (line : Line K)
    (nonNull : ¬ line.IsNull) (twoNonzero : (2 : K) ≠ 0)
    (point : Point K) :
    Reflection.Point.reflectPoint line nonNull point = point ↔ line.Contains point := by
  constructor
  · intro fixed
    have xFixed := congrArg (Point.x (K := K)) fixed
    have yFixed := congrArg (Point.y (K := K)) fixed
    change
      2 * (Altitude.altitudeFoot point line nonNull).x - point.x = point.x
      at xFixed
    change
      2 * (Altitude.altitudeFoot point line nonNull).y - point.y = point.y
      at yFixed
    have twiceXZero :
        (2 : K) * ((Altitude.altitudeFoot point line nonNull).x - point.x) = 0 := by
      calc
        (2 : K) * ((Altitude.altitudeFoot point line nonNull).x - point.x) =
            (2 * (Altitude.altitudeFoot point line nonNull).x - point.x) -
              point.x := by ring1
        _ = 0 := by rw [xFixed]; ring1
    have twiceYZero :
        (2 : K) * ((Altitude.altitudeFoot point line nonNull).y - point.y) = 0 := by
      calc
        (2 : K) * ((Altitude.altitudeFoot point line nonNull).y - point.y) =
            (2 * (Altitude.altitudeFoot point line nonNull).y - point.y) -
              point.y := by ring1
        _ = 0 := by rw [yFixed]; ring1
    have footEqualsPoint : Altitude.altitudeFoot point line nonNull = point := by
      apply Point.ext
      · have differenceZero := (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (value : K) (twoNonzero : (2 :
        K) ≠ 0) (twiceZero : (2 : K) * value = 0) =>
        (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero value twiceZero :
        value = 0))
          ((Altitude.altitudeFoot point line nonNull).x - point.x)
          twoNonzero twiceXZero
        calc
          (Altitude.altitudeFoot point line nonNull).x =
              ((Altitude.altitudeFoot point line nonNull).x - point.x) + point.x := by
                ring1
          _ = point.x := by rw [differenceZero]; ring1
      · have differenceZero := (fun {K : Type _} [Purelib.Algebra.Field.ExplicitField K] (value : K) (twoNonzero : (2 :
        K) ≠ 0) (twiceZero : (2 : K) * value = 0) =>
        (Purelib.Algebra.Field.Characteristic.Nonzero.eq_zero_of_two_mul_eq_zero (K := K) twoNonzero value twiceZero :
        value = 0))
          ((Altitude.altitudeFoot point line nonNull).y - point.y)
          twoNonzero twiceYZero
        calc
          (Altitude.altitudeFoot point line nonNull).y =
              ((Altitude.altitudeFoot point line nonNull).y - point.y) + point.y := by
                ring1
          _ = point.y := by rw [differenceZero]; ring1
    rw [← footEqualsPoint]
    exact Altitude.altitudeFoot_on_line point line nonNull
  · intro contains
    have pointEqualsFoot := Altitude.altitudeFoot_unique point line nonNull point
      contains (Construction.altitudeThrough_contains point line)
    unfold Reflection.Point.reflectPoint
    rw [← pointEqualsFoot]
    apply Point.ext <;>
      unfold HalfTurn.Basic.rotateInPoint <;>
      ring1

end Purelib.Geometry.Plane.Reflection.Point

end

end

section
/-!
# Divine Proportions, §13.1: translations, rotations, and reflections

This file gives executable isometries for the coordinate transformations in
Examples 13.1–13.3 and proves the composition calculations requested in
Exercises 13.2, 13.4, and 13.5.
-/

public section

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Reflection.Point

/-- The finite polynomial calculation that reflection in a non-null line preserves quadrance. -/
theorem reflectPoint_preserves_quadrance
    (line : Line K) (nonNull : ¬ line.IsNull) (first second : Point K) :
    Quadrance.quadrance (Geometry.Plane.Reflection.Point.reflectPoint line nonNull first)
        (Geometry.Plane.Reflection.Point.reflectPoint line nonNull second) =
      Quadrance.quadrance first second := by
  have normCancel : Basic.lineNorm line * (Basic.lineNorm line)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ nonNull
  rw [Geometry.Plane.Reflection.Point.reflectPoint_formula, Geometry.Plane.Reflection.Point.reflectPoint_formula]
  unfold Quadrance.quadrance Reflection.Point.reflectionFormula
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    ((((line.b ^ 2 - line.a ^ 2) * second.x -
              2 * line.a * line.b * second.y - 2 * line.a * line.c) *
            (Basic.lineNorm line)⁻¹ -
          ((line.b ^ 2 - line.a ^ 2) * first.x -
              2 * line.a * line.b * first.y - 2 * line.a * line.c) *
            (Basic.lineNorm line)⁻¹) ^ 2 +
        ((-2 * line.a * line.b * second.x +
              (line.a ^ 2 - line.b ^ 2) * second.y -
              2 * line.b * line.c) * (Basic.lineNorm line)⁻¹ -
          (-2 * line.a * line.b * first.x +
              (line.a ^ 2 - line.b ^ 2) * first.y -
              2 * line.b * line.c) * (Basic.lineNorm line)⁻¹) ^ 2) =
      ((second.x - first.x) ^ 2 + (second.y - first.y) ^ 2) *
        (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) ^ 2 := by
          unfold Basic.lineNorm
          ring1
    _ = (second.x - first.x) ^ 2 + (second.y - first.y) ^ 2 := by
      rw [normCancel]
      ring1

end Purelib.Geometry.Plane.Reflection.Point

end

end

end

section
public section

/-!
# Divine Proportions, Theorem 98: polygon corner triangles

The source construction uses only three successive polygon vertices and the
three finite reflections relating them.  `PolygonTriangleConfiguration`
stores precisely that finite window; no polygon indexed by all integers is
introduced.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Reflection.Point

/-- A reflection chord has four times the point-to-mirror quadrance. -/
theorem reflectPoint_chord_quadrance
    (mirror : Line K) (mirrorNonNull : ¬ mirror.IsNull) (point : Point K) :
    Quadrance.quadrance point (Reflection.Point.reflectPoint mirror mirrorNonNull point) =
      4 * Quadrance.pointLineQuadrance point mirror mirrorNonNull := by
  unfold Reflection.Point.reflectPoint Quadrance.pointLineQuadrance HalfTurn.Basic.rotateInPoint Quadrance.quadrance
  ring1

/-- The quadrance of a reflection chord is four times the radial quadrance and its spread with the mirror.

The center lies on the non-null mirror, and the radius has distinct endpoints and a non-null line. -/
theorem reflectPoint_chord_quadrance_eq_spread [DecidableEq K]
    (center point : Point K) (distinct : center ≠ point)
    (radialNonNull : ¬ (Incidence.lineThrough center point distinct).IsNull)
    (mirror : Line K) (mirrorNonNull : ¬ mirror.IsNull)
    (centerOnMirror : mirror.Contains center) :
    Quadrance.quadrance point (Geometry.Plane.Reflection.Point.reflectPoint mirror mirrorNonNull point) =
      4 * Spread.spread (Incidence.lineThrough center point distinct) mirror
        radialNonNull mirrorNonNull * Quadrance.quadrance center point := by
  rw [Geometry.Plane.Reflection.Point.reflectPoint_chord_quadrance mirror mirrorNonNull point,
    Spread.pointLineQuadrance_eq_spread_mul_quadrance center point distinct
      radialNonNull mirror mirrorNonNull centerOnMirror]
  ring1

end Purelib.Geometry.Plane.Reflection.Point

end

end

section
public section

/-!
# Divine Proportions, regular polygon construction

The source uses a doubly infinite reflection sequence.  Here every line and
point is obtained from the already executable natural-number iterator.  A
request for vertex `k` computes exactly the first `k` reflection steps.

The point-reflection product identity below is the finite natural-index form
of Exercise 14.1.  It is then used to prove that the closed formula
`A₂ₖ = σ_{lₖ}(A₀)` agrees with the source's successive construction through
the intervening mirrors `l₂ₖ₊₁`.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Reflection.Point

/-- Point reflection is independent of the chosen nonzero coefficient representative of a line. -/
theorem reflectPoint_eq_of_equivalent [DecidableEq K]
    (first second : Line K)
    (firstNonNull : ¬ first.IsNull) (secondNonNull : ¬ second.IsNull)
    (equivalent : first.Equivalent second) (point : Point K) :
    Geometry.Plane.Reflection.Point.reflectPoint first firstNonNull point =
      Geometry.Plane.Reflection.Point.reflectPoint second secondNonNull point := by
  rcases Relations.line_coefficient_scale_of_equivalent first second equivalent with
    ⟨scale, secondA, secondB, secondC⟩
  have scaleNonzero : scale ≠ 0 := by
    intro scaleZero
    have secondAZero : second.a = 0 := by rw [secondA, scaleZero]; ring1
    have secondBZero : second.b = 0 := by rw [secondB, scaleZero]; ring1
    exact second.direction_nonzero.elim
      (fun nonzero => nonzero secondAZero)
      (fun nonzero => nonzero secondBZero)
  have scaleSquareNonzero : scale ^ 2 ≠ 0 := by
    simpa [pow_two] using
      Algebra.Field.ExplicitField.mul_ne_zero scaleNonzero scaleNonzero
  have secondNorm : Basic.lineNorm second = scale ^ 2 * Basic.lineNorm first := by
    unfold Basic.lineNorm
    rw [secondA, secondB]
    ring1
  let firstXNumerator : K :=
    (first.b ^ 2 - first.a ^ 2) * point.x -
      2 * first.a * first.b * point.y - 2 * first.a * first.c
  let firstYNumerator : K :=
    -2 * first.a * first.b * point.x +
      (first.a ^ 2 - first.b ^ 2) * point.y - 2 * first.b * first.c
  have secondXNumerator :
      (second.b ^ 2 - second.a ^ 2) * point.x -
          2 * second.a * second.b * point.y - 2 * second.a * second.c =
        scale ^ 2 * firstXNumerator := by
    unfold firstXNumerator
    rw [secondA, secondB, secondC]
    ring1
  have secondYNumerator :
      -2 * second.a * second.b * point.x +
          (second.a ^ 2 - second.b ^ 2) * point.y -
            2 * second.b * second.c =
        scale ^ 2 * firstYNumerator := by
    unfold firstYNumerator
    rw [secondA, secondB, secondC]
    ring1
  rw [Geometry.Plane.Reflection.Point.reflectPoint_formula, Geometry.Plane.Reflection.Point.reflectPoint_formula]
  apply Point.ext
  · change
      firstXNumerator / Basic.lineNorm first =
        ((second.b ^ 2 - second.a ^ 2) * point.x -
          2 * second.a * second.b * point.y - 2 * second.a * second.c) /
            Basic.lineNorm second
    have secondNormNonzero : Basic.lineNorm second ≠ 0 := secondNonNull
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right secondNormNonzero
    rw [Algebra.Field.ExplicitField.div_mul_cancel
        (b := Basic.lineNorm second) _ secondNormNonzero,
      secondXNumerator, secondNorm]
    calc
      (firstXNumerator / Basic.lineNorm first) *
          (scale ^ 2 * Basic.lineNorm first) =
        scale ^ 2 *
          ((firstXNumerator / Basic.lineNorm first) * Basic.lineNorm first) := by ring1
      _ = scale ^ 2 * firstXNumerator := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel
          (b := Basic.lineNorm first) _ firstNonNull]
  · change
      firstYNumerator / Basic.lineNorm first =
        (-2 * second.a * second.b * point.x +
          (second.a ^ 2 - second.b ^ 2) * point.y -
            2 * second.b * second.c) / Basic.lineNorm second
    have secondNormNonzero : Basic.lineNorm second ≠ 0 := secondNonNull
    apply Algebra.Field.ExplicitField.eq_of_mul_eq_mul_right secondNormNonzero
    rw [Algebra.Field.ExplicitField.div_mul_cancel
        (b := Basic.lineNorm second) _ secondNormNonzero,
      secondYNumerator, secondNorm]
    calc
      (firstYNumerator / Basic.lineNorm first) *
          (scale ^ 2 * Basic.lineNorm first) =
        scale ^ 2 *
          ((firstYNumerator / Basic.lineNorm first) * Basic.lineNorm first) := by ring1
      _ = scale ^ 2 * firstYNumerator := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel
          (b := Basic.lineNorm first) _ firstNonNull]

end Purelib.Geometry.Plane.Reflection.Point

namespace Purelib.Geometry.Plane.Reflection.Point.RegularConstruction

/-- A point on a mirror is fixed by its reflection. This direct altitude-foot proof does not require characteristic two
to be excluded. -/
theorem reflectPoint_fixed_of_contains_direct
    (line : Line K) (lineNonNull : ¬ line.IsNull)
    (point : Point K) (contains : line.Contains point) :
    Reflection.Point.reflectPoint line lineNonNull point = point := by
  have pointEqualsFoot := Altitude.altitudeFoot_unique point line lineNonNull point
    contains (Construction.altitudeThrough_contains point line)
  unfold Reflection.Point.reflectPoint
  rw [← pointEqualsFoot]
  apply Point.ext <;>
    unfold HalfTurn.Basic.rotateInPoint <;>
    ring1

end Purelib.Geometry.Plane.Reflection.Point.RegularConstruction

end

end

end
