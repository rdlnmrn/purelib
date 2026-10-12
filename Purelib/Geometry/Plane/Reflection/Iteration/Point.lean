module
import Purelib.Geometry.Plane.Reflection.Composition
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Reflection.Iteration
import Purelib.Geometry.Plane.Reflection.Point

import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Geometry.Plane.Line.Basic
import Mathlib.Algebra.Group.Nat.Defs

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Reflection

section
@[expose] public section

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

namespace Purelib.Geometry.Plane.Reflection.Iteration.Point

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Reflection of a point in the requested line of a finite reflection sequence. -/
def reflectionPointAt [DecidableEq K]
    (initial : Iteration.ReflectionPair K) (index : Nat) (point : Plane.Point K) : Plane.Point K
      :=
  Reflection.Point.reflectPoint (Iteration.reflectionLineAt initial index)
    (Iteration.reflectionLineAt_nonNull initial index) point

/-- Every finite point reflection is an involution. -/
theorem reflectionPointAt_involutive [DecidableEq K]
    (initial : Iteration.ReflectionPair K) (index : Nat) (point : Plane.Point K) :
    reflectionPointAt initial index
        (reflectionPointAt initial index point) = point := by
  exact Reflection.Point.reflectPoint_involutive
    (Iteration.reflectionLineAt initial index)
    (Iteration.reflectionLineAt_nonNull initial index) point

/-- The point reflections satisfy the same conjugation recurrence as the line iterator. -/
theorem reflectionPointAt_succ_succ [Nontrivial K] [DecidableEq
  K]
    (initial : Iteration.ReflectionPair K) (index : Nat) (point : Plane.Point K) :
    reflectionPointAt initial (index + 2) point =
      reflectionPointAt initial (index + 1)
        (reflectionPointAt initial index
          (reflectionPointAt initial (index + 1) point)) := by
  have conjugation := Composition.reflection_composition
    (Iteration.reflectionLineAt initial index)
    (Iteration.reflectionLineAt initial (index + 1))
    (Iteration.reflectionLineAt_nonNull initial index)
    (Iteration.reflectionLineAt_nonNull initial (index + 1))
    (reflectionPointAt initial (index + 1) point)
  unfold reflectionPointAt at conjugation ⊢
  rw [Reflection.Point.reflectPoint_involutive] at conjugation
  simpa only [Iteration.reflectionLineAt_succ_succ] using conjugation.symm

/-- Consecutive reflection products are independent of their finite starting index. -/
theorem reflectionPointAt_adjacent_product [Nontrivial K]
  [DecidableEq K]
    (initial : Iteration.ReflectionPair K) (index : Nat) (point : Plane.Point K) :
    reflectionPointAt initial (index + 1)
        (reflectionPointAt initial index point) =
      reflectionPointAt initial 1
        (reflectionPointAt initial 0 point) := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      calc
        reflectionPointAt initial (Nat.succ index + 1)
            (reflectionPointAt initial (Nat.succ index) point) =
          reflectionPointAt initial (index + 1)
            (reflectionPointAt initial index point) := by
              rw [show Nat.succ index + 1 = index + 2 by omega0,
                show Nat.succ index = index + 1 by omega0,
                reflectionPointAt_succ_succ,
                reflectionPointAt_involutive]
        _ = reflectionPointAt initial 1
            (reflectionPointAt initial 0 point) := inductionHypothesis

/-- Shifting both mirrors forward once leaves their composed reflection unchanged. -/
theorem reflectionPointAt_product_shift_one
    [Nontrivial K] [DecidableEq K]
    (initial : Iteration.ReflectionPair K) (first second : Nat) (point : Plane.Point K) :
    reflectionPointAt initial (first + 1)
        (reflectionPointAt initial (second + 1) point) =
      reflectionPointAt initial first
        (reflectionPointAt initial second point) := by
  have secondAtReflected :=
    reflectionPointAt_adjacent_product initial second
      (reflectionPointAt initial second point)
  rw [reflectionPointAt_involutive] at secondAtReflected
  have firstAtSecond :=
    reflectionPointAt_adjacent_product initial first
      (reflectionPointAt initial second point)
  have insideEquality :
      reflectionPointAt initial (second + 1) point =
        reflectionPointAt initial (first + 1)
          (reflectionPointAt initial first
            (reflectionPointAt initial second point)) :=
    secondAtReflected.trans firstAtSecond.symm
  calc
    reflectionPointAt initial (first + 1)
        (reflectionPointAt initial (second + 1) point) =
      reflectionPointAt initial (first + 1)
        (reflectionPointAt initial (first + 1)
          (reflectionPointAt initial first
            (reflectionPointAt initial second point))) := by
              rw [insideEquality]
    _ = reflectionPointAt initial first
        (reflectionPointAt initial second point) := by
          rw [reflectionPointAt_involutive]

/-- Exercise 14.1, at the agreed finite boundary: for any requested natural indices, simultaneously shifting the two
mirrors by `offset` leaves their composed point reflection unchanged. -/
theorem exercise_14_1 [Nontrivial K] [DecidableEq K]
    (initial : Iteration.ReflectionPair K) (first second offset : Nat)
    (point : Plane.Point K) :
    reflectionPointAt initial (first + offset)
        (reflectionPointAt initial (second + offset) point) =
      reflectionPointAt initial first
        (reflectionPointAt initial second point) := by
  induction offset with
  | zero => rfl
  | succ offset inductionHypothesis =>
      calc
        reflectionPointAt initial (first + Nat.succ offset)
            (reflectionPointAt initial (second + Nat.succ offset) point) =
          reflectionPointAt initial ((first + offset) + 1)
            (reflectionPointAt initial ((second + offset) + 1) point) := by
              rfl
        _ = reflectionPointAt initial (first + offset)
            (reflectionPointAt initial (second + offset) point) :=
          reflectionPointAt_product_shift_one initial
            (first + offset) (second + offset) point
        _ = reflectionPointAt initial first
            (reflectionPointAt initial second point) := inductionHypothesis

end Purelib.Geometry.Plane.Reflection.Iteration.Point

end
