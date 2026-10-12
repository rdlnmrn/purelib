module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation

import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Construction
import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Line.Intersection
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Dot
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Plane
open Purelib.Geometry.Plane.Line
open Purelib.Geometry.Plane.Line.Basic
open Purelib.Geometry.Plane.Point

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

section
public section

/-!
# Divine Proportions, Theorem 117: the nine point circle

All nine points and the circle are explicit finite constructions.  The six
midpoint incidences follow from the cleared Euler relation `2C+O=A₁+A₂+A₃`.
For an altitude foot, the side-midpoint and vertex--orthocenter midpoint form
a diameter: a denominator-cleared dot-product lemma supplies the right-angle
calculation even when the foot coincides with a diameter endpoint.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Altitude

/-- A vector along a non-null line is perpendicular to a vector along an altitude to that line. -/
theorem pointVectorDot_eq_zero_of_line_altitude
    (line : Line K) (altitudeSource sidePoint altitudePoint foot : Point K)
    (lineNonNull : ¬ line.IsNull)
    (sideOnLine : line.Contains sidePoint)
    (footOnLine : line.Contains foot)
    (altitudeOnLine : (Construction.altitudeThrough altitudeSource line).Contains altitudePoint)
    (footOnAltitude : (Construction.altitudeThrough altitudeSource line).Contains foot) :
    Dot.pointVectorDot foot sidePoint altitudePoint = 0 := by
  have sideEquation :
      line.a * (sidePoint.x - foot.x) +
        line.b * (sidePoint.y - foot.y) = 0 := by
    unfold Line.Contains at sideOnLine footOnLine
    calc
      line.a * (sidePoint.x - foot.x) +
          line.b * (sidePoint.y - foot.y) =
        (line.a * sidePoint.x + line.b * sidePoint.y + line.c) -
          (line.a * foot.x + line.b * foot.y + line.c) := by ring1
      _ = 0 := by rw [sideOnLine, footOnLine]; ring1
  have altitudeEquation :
      -line.b * (altitudePoint.x - foot.x) +
        line.a * (altitudePoint.y - foot.y) = 0 := by
    unfold Construction.altitudeThrough Line.Contains at altitudeOnLine footOnAltitude
    calc
      -line.b * (altitudePoint.x - foot.x) +
          line.a * (altitudePoint.y - foot.y) =
        (-line.b * altitudePoint.x + line.a * altitudePoint.y +
            (line.b * altitudeSource.x - line.a * altitudeSource.y)) -
          (-line.b * foot.x + line.a * foot.y +
            (line.b * altitudeSource.x - line.a * altitudeSource.y)) := by ring1
      _ = 0 := by rw [altitudeOnLine, footOnAltitude]; ring1
  apply Algebra.Field.ExplicitField.eq_zero_of_mul_eq_zero_left lineNonNull
  calc
    Basic.lineNorm line * Dot.pointVectorDot foot sidePoint altitudePoint =
      (line.a * (sidePoint.x - foot.x) +
          line.b * (sidePoint.y - foot.y)) *
        (line.a * (altitudePoint.x - foot.x) +
          line.b * (altitudePoint.y - foot.y)) +
      (-line.b * (sidePoint.x - foot.x) +
          line.a * (sidePoint.y - foot.y)) *
        (-line.b * (altitudePoint.x - foot.x) +
          line.a * (altitudePoint.y - foot.y)) := by
            unfold Basic.lineNorm Dot.pointVectorDot
            ring1
    _ = 0 := by rw [sideEquation, altitudeEquation]; ring1

end Purelib.Geometry.Plane.Line.Altitude

end

end

section
public section

/-!
# Divine Proportions, Chapter 19: tangent lines and conics

Translations, Taylor conics, and tangent lines are retained as explicit
finite coefficient records.  A non-singular point carries the disjunction
that one of the two displayed linear coefficients is nonzero, so every line
construction remains executable and choice-free.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

namespace Purelib.Curves.Plane.Conic

/-- The altitude to a non-null line is itself non-null. -/
theorem altitudeThrough_nonNull
    (point : Geometry.Plane.Point K) (line : Line K) (lineNonNull : ¬ line.IsNull) :
    ¬ (Construction.altitudeThrough point line).IsNull := by
  intro altitudeNull
  apply lineNonNull
  unfold Line.IsNull at altitudeNull ⊢
  unfold Construction.altitudeThrough at altitudeNull
  calc
    line.a ^ 2 + line.b ^ 2 =
        (-line.b) ^ 2 + line.a ^ 2 := by ring1
    _ = 0 := altitudeNull

end Purelib.Curves.Plane.Conic

end

end

end

section
public section

/-!
# Divine Proportions, §3.4: the foot of an altitude

The construction is the exact rational formula printed in Theorem 8.  Its only
denominator is the direction quadrance `a² + b²`, so the source's non-null-line
hypothesis is exposed as the precise executable cancellation certificate.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Altitude

/-- The perpendicular projection of a point onto a displayed non-null line.

The coordinates divide the explicit projection numerators by the line's nonzero direction norm. -/
@[expose] def altitudeFoot (point : Point K) (line : Line K)
    (_nonNull : ¬ line.IsNull) : Point K :=
  { x := (line.b ^ 2 * point.x - line.a * line.b * point.y -
      line.a * line.c) / Line.Basic.lineNorm line
    y := (-line.a * line.b * point.x + line.a ^ 2 * point.y -
      line.b * line.c) / Line.Basic.lineNorm line }

/-- The foot given by Theorem 8 lies on the target line. -/
theorem altitudeFoot_on_line (point : Point K) (line : Line K)
    (nonNull : ¬ line.IsNull) :
    line.Contains (Altitude.altitudeFoot point line nonNull) := by
  have normNonzero : Basic.lineNorm line ≠ 0 := Purelib.Geometry.Plane.Line.Basic.lineNorm_ne_zero nonNull
  have normCancel : Basic.lineNorm line * (Basic.lineNorm line)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ normNonzero
  unfold Line.Contains Altitude.altitudeFoot
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    line.a *
          ((line.b ^ 2 * point.x - line.a * line.b * point.y -
              line.a * line.c) * (Basic.lineNorm line)⁻¹) +
        line.b *
          ((-line.a * line.b * point.x + line.a ^ 2 * point.y -
              line.b * line.c) * (Basic.lineNorm line)⁻¹) +
        line.c = -line.c * (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) + line.c := by
      unfold Basic.lineNorm
      ring1
    _ = 0 := by rw [normCancel]; ring1

/-- The foot given by Theorem 8 also lies on the altitude through the point. -/
theorem altitudeFoot_on_altitude (point : Point K) (line : Line K)
    (nonNull : ¬ line.IsNull) :
    (Construction.altitudeThrough point line).Contains (Altitude.altitudeFoot point line nonNull) := by
  have normNonzero : Basic.lineNorm line ≠ 0 := Purelib.Geometry.Plane.Line.Basic.lineNorm_ne_zero nonNull
  have normCancel : Basic.lineNorm line * (Basic.lineNorm line)⁻¹ = (1 : K) :=
    Algebra.Field.ExplicitField.mul_inv_cancel _ normNonzero
  unfold Line.Contains Construction.altitudeThrough Altitude.altitudeFoot
  simp only [Algebra.Field.ExplicitField.div_eq_mul_inv]
  calc
    -line.b *
          ((line.b ^ 2 * point.x - line.a * line.b * point.y -
              line.a * line.c) * (Basic.lineNorm line)⁻¹) +
        line.a *
          ((-line.a * line.b * point.x + line.a ^ 2 * point.y -
              line.b * line.c) * (Basic.lineNorm line)⁻¹) +
        (line.b * point.x - line.a * point.y) =
      (-line.b * point.x + line.a * point.y) *
          (Basic.lineNorm line * (Basic.lineNorm line)⁻¹) +
        (line.b * point.x - line.a * point.y) := by
      unfold Basic.lineNorm
      ring1
    _ = 0 := by rw [normCancel]; ring1

/-- A non-null line and its altitude are not parallel. -/
theorem altitude_not_parallel (point : Point K) (line : Line K)
    (nonNull : ¬ line.IsNull) :
    ¬ (Construction.altitudeThrough point line).Parallel line := by
  intro parallel
  apply nonNull
  unfold Line.Parallel Construction.altitudeThrough at parallel
  unfold Line.IsNull
  calc
    line.a ^ 2 + line.b ^ 2 =
        -((-line.b) * line.b - line.a * line.a) := by ring1
    _ = 0 := by rw [parallel]; exact neg_zero

/-- Theorem 8 (Foot of an altitude): the displayed point is the unique intersection of the target line and the altitude.
-/
theorem altitudeFoot_unique (point : Point K) (line : Line K)
    (nonNull : ¬ line.IsNull) (candidate : Point K)
    (onLine : line.Contains candidate)
    (onAltitude : (Construction.altitudeThrough point line).Contains candidate) :
    candidate = Geometry.Plane.Line.Altitude.altitudeFoot point line nonNull := by
  let nonparallel := Geometry.Plane.Line.Altitude.altitude_not_parallel point line nonNull
  have candidateIntersection :=
    Intersection.lineIntersection_unique (Construction.altitudeThrough point line) line nonparallel
      candidate onAltitude onLine
  have footIntersection :=
    Intersection.lineIntersection_unique (Construction.altitudeThrough point line) line nonparallel
      (Geometry.Plane.Line.Altitude.altitudeFoot point line nonNull)
      (Geometry.Plane.Line.Altitude.altitudeFoot_on_altitude point line nonNull)
      (Geometry.Plane.Line.Altitude.altitudeFoot_on_line point line nonNull)
  exact candidateIntersection.trans footIntersection.symm

end Purelib.Geometry.Plane.Line.Altitude

end

end

end

section
public section

/-!
# Divine Proportions, Exercises 3.3–3.10

These line relations and coordinate formulas use only the three displayed
coefficients of each line.  Parallel directions are related by an explicit
nonzero scale; no slope quotient or projective representative is selected.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Altitude

/-- Exercise 3.10: the printed altitude-foot coordinates for the non-null line through two distinct points. -/
theorem exercise_3_10 [DecidableEq K]
    (point first second : Point K) (distinct : first ≠ second)
    (nonNull : ¬ (Incidence.lineThrough first second distinct).IsNull) :
    Geometry.Plane.Line.Altitude.altitudeFoot point (Incidence.lineThrough first second distinct) nonNull =
      { x :=
          ((second.x - first.x) ^ 2 * point.x -
            (first.y - second.y) * (second.x - first.x) * point.y -
            (first.y - second.y) *
              (first.x * second.y - second.x * first.y)) /
            ((second.x - first.x) ^ 2 + (first.y - second.y) ^ 2)
        y :=
          ((first.y - second.y) ^ 2 * point.y -
            (first.y - second.y) * (second.x - first.x) * point.x -
            (second.x - first.x) *
              (first.x * second.y - second.x * first.y)) /
            ((second.x - first.x) ^ 2 + (first.y - second.y) ^ 2) } := by
  apply Point.ext
  · change
      (((second.x - first.x) ^ 2 * point.x -
        (first.y - second.y) * (second.x - first.x) * point.y -
        (first.y - second.y) *
          (first.x * second.y - second.x * first.y)) /
        ((first.y - second.y) ^ 2 + (second.x - first.x) ^ 2)) = _
    rw [show
      (first.y - second.y) ^ 2 + (second.x - first.x) ^ 2 =
        (second.x - first.x) ^ 2 + (first.y - second.y) ^ 2 by ring1]
  · change
      ((-(first.y - second.y) * (second.x - first.x) * point.x +
        (first.y - second.y) ^ 2 * point.y -
        (second.x - first.x) *
          (first.x * second.y - second.x * first.y)) /
        ((first.y - second.y) ^ 2 + (second.x - first.x) ^ 2)) = _
    rw [show
      -(first.y - second.y) * (second.x - first.x) * point.x +
          (first.y - second.y) ^ 2 * point.y -
          (second.x - first.x) *
            (first.x * second.y - second.x * first.y) =
        (first.y - second.y) ^ 2 * point.y -
          (first.y - second.y) * (second.x - first.x) * point.x -
          (second.x - first.x) *
            (first.x * second.y - second.x * first.y) by ring1,
      show
        (first.y - second.y) ^ 2 + (second.x - first.x) ^ 2 =
          (second.x - first.x) ^ 2 + (first.y - second.y) ^ 2 by ring1]

end Purelib.Geometry.Plane.Line.Altitude

end

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

namespace Purelib.Geometry.Plane.Line.Altitude

/-- The altitude through a point to a non-null line is itself non-null. -/
theorem altitudeThrough_nonNull
    (point : Point K) (line : Line K) (lineNonNull : ¬ line.IsNull) :
    ¬ (Construction.altitudeThrough point line).IsNull := by
  intro altitudeNull
  apply lineNonNull
  unfold Line.IsNull at altitudeNull ⊢
  change (-line.b) ^ 2 + line.a ^ 2 = 0 at altitudeNull
  calc
    line.a ^ 2 + line.b ^ 2 = (-line.b) ^ 2 + line.a ^ 2 := by ring1
    _ = 0 := altitudeNull

end Purelib.Geometry.Plane.Line.Altitude

end

end

end
