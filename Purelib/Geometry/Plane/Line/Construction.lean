module
-- Retained public numeral and subtraction parents use their original operations.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Incidence
import Purelib.Geometry.Plane.Point.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Tactic.Ring

section
open Purelib
open Purelib.Geometry
open Purelib.Geometry.Plane
open Purelib.Geometry.Plane.Line

open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
  Purelib.Data.Nat.successorAtLeastTwo
  Purelib.Algebra.Group.Negation.subNegZeroMonoid

public section

/-!
# Divine Proportions, Chapter 3: points, lines, and incidence

Lines are finite coefficient records, not sets of points and not quotients.
`Line.Equivalent` records the three cross-product equations expressing equality
of the ordered proportions.  This follows the source's finite algebra while
keeping every construction executable over both finite fields and the
constructive rationals.
-/

section

variable {K : Type*}

section Incidence

variable [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Construction

/-- The line through a point with the same displayed direction coefficients. -/
@[expose] def parallelThrough (point : Point K) (line : Line K) : Line K where
  a := line.a
  b := line.b
  c := -(line.a * point.x) - line.b * point.y
  direction_nonzero := line.direction_nonzero

/-- Theorem 6: the constructed parallel contains the requested point. -/
theorem parallelThrough_contains (point : Point K) (line : Line K) :
    (Construction.parallelThrough point line).Contains point := by
  unfold Construction.parallelThrough Contains
  ring1

/-- Theorem 6: the constructed line is parallel to the source line. -/
theorem parallelThrough_parallel (point : Point K) (line : Line K) :
    (Construction.parallelThrough point line).Parallel line := by
  unfold Construction.parallelThrough Parallel
  ring1

/-- Theorem 6 (Parallel to a line), uniqueness after choosing the source line's displayed direction representative. -/
theorem parallelThrough_unique (point : Point K) (line other : Line K)
    (sameA : other.a = line.a) (sameB : other.b = line.b)
    (contains : other.Contains point) :
    other.c = (Construction.parallelThrough point line).c := by
  unfold Contains at contains
  unfold Construction.parallelThrough
  rw [sameA, sameB] at contains
  calc
    other.c = (line.a * point.x + line.b * point.y + other.c) -
        (line.a * point.x + line.b * point.y) := by ring1
    _ = -(line.a * point.x) - line.b * point.y := by rw [contains]; ring1

/-- The altitude through a point to a displayed line. -/
@[expose] def altitudeThrough (point : Point K) (line : Line K) : Line K where
  a := -line.b
  b := line.a
  c := line.b * point.x - line.a * point.y
  direction_nonzero := by
    rcases line.direction_nonzero with aNonzero | bNonzero
    · exact Or.inr aNonzero
    · left
      intro negativeZero
      apply bNonzero
      calc
        line.b = -(-line.b) := by ring1
        _ = -0 := by rw [negativeZero]
        _ = 0 := neg_zero

/-- Theorem 7: the altitude contains its source point. -/
theorem altitudeThrough_contains (point : Point K) (line : Line K) :
    (Construction.altitudeThrough point line).Contains point := by
  unfold Construction.altitudeThrough Contains
  ring1

/-- Theorem 7: the altitude is perpendicular to the source line. -/
theorem altitudeThrough_perpendicular (point : Point K) (line : Line K) :
    (Construction.altitudeThrough point line).Perpendicular line := by
  unfold Construction.altitudeThrough Perpendicular
  ring1

/-- Theorem 7 (Altitude to a line), uniqueness after choosing the displayed perpendicular direction representative. -/
theorem altitudeThrough_unique (point : Point K) (line other : Line K)
    (sameA : other.a = -line.b) (sameB : other.b = line.a)
    (contains : other.Contains point) :
    other.c = (Construction.altitudeThrough point line).c := by
  unfold Contains at contains
  unfold Construction.altitudeThrough
  rw [sameA, sameB] at contains
  calc
    other.c = (-line.b * point.x + line.a * point.y + other.c) -
        (-line.b * point.x + line.a * point.y) := by ring1
    _ = line.b * point.x - line.a * point.y := by rw [contains]; ring1

end Purelib.Geometry.Plane.Line.Construction

end Incidence

end

end

public section

/-!
# Divine Proportions, Exercises 3.3–3.10

These line relations and coordinate formulas use only the three displayed
coefficients of each line.  Parallel directions are related by an explicit
nonzero scale; no slope quotient or projective representative is selected.
-/

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace Purelib.Geometry.Plane.Line.Construction

/-- Exercise 3.8: the printed coefficients of the parallel through `point` to the line through `first` and `second`. -/
theorem exercise_3_8 [DecidableEq K]
    (point first second : Point K) (distinct : first ≠ second) :
    let parallel := Geometry.Plane.Line.Construction.parallelThrough point (Incidence.lineThrough first second distinct)
    parallel.a = first.y - second.y ∧
      parallel.b = second.x - first.x ∧
      parallel.c =
        (second.y - first.y) * point.x +
          (first.x - second.x) * point.y := by
  dsimp only [Geometry.Plane.Line.Construction.parallelThrough, Incidence.lineThrough]
  exact ⟨rfl, rfl, by ring1⟩

/-- Exercise 3.9: the printed coefficients of the altitude through `point` to the line through `first` and `second`. -/
theorem exercise_3_9 [DecidableEq K]
    (point first second : Point K) (distinct : first ≠ second) :
    let altitude := Geometry.Plane.Line.Construction.altitudeThrough point (Incidence.lineThrough first second distinct)
    altitude.a = first.x - second.x ∧
      altitude.b = first.y - second.y ∧
      altitude.c =
        (second.x - first.x) * point.x +
          (second.y - first.y) * point.y := by
  dsimp only [Geometry.Plane.Line.Construction.altitudeThrough, Incidence.lineThrough]
  exact ⟨by ring1, rfl, by ring1⟩

end Purelib.Geometry.Plane.Line.Construction

end

end

end
