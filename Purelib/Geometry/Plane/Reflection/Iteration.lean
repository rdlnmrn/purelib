module

import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Reflection.Line

import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.QuotientFreeOmega
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Logic.Nontrivial.Defs
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Reflection

/-!
# Divine Proportions, Theorem 18: finite cyclic reflection

The book states Cyclic reflection for a completed two-sided sequence of lines.
Here a reflection chain is an executable finite iterator.  Given a left index
and an offset, `cyclic_reflection_right` computes only through the corresponding
right index and proves the source's reflection symmetry on that finite window.
The reverse orientation follows from involutivity.  No infinite sequence or
integer-indexed family is introduced.
-/

@[expose] public section

namespace Purelib.Geometry.Plane.Reflection.Iteration

variable {K : Type*} [Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- One finite state of the reflection recurrence, including the certificates needed to execute the next reflection. -/
structure ReflectionPair (K : Type*) [Algebra.Field.ExplicitField K] where
  /-- Earlier line of the adjacent reflection pair. -/ previous : Line K
  /-- Later line of the adjacent reflection pair. -/ current : Line K
  /-- The earlier line has nonzero normal norm. -/ previousNonNull : ¬ previous.IsNull
  /-- The later line has nonzero normal norm, so the next reflection is defined. -/ currentNonNull : ¬ current.IsNull

constructive_injectivity ReflectionPair

namespace ReflectionPair

/-- One executable reflection step `(lₙ,lₙ₊₁) ↦ (lₙ₊₁,lₙ₊₂)`. -/
def step [DecidableEq K] (state : ReflectionPair K) :
  ReflectionPair K where
  previous := state.current
  current := Line.reflectLine state.current state.previous state.currentNonNull
  previousNonNull := state.currentNonNull
  currentNonNull := Line.reflectLine_nonNull state.current state.previous
    state.currentNonNull state.previousNonNull

end ReflectionPair

/-- Iterate only as far as the requested finite index. -/
def reflectionPairAt [DecidableEq K]
    (initial : ReflectionPair K) : Nat →
      ReflectionPair K
  | 0 => initial
  | index + 1 => (Iteration.reflectionPairAt initial index).step

/-- The line `lₙ` extracted from the finite state reached after `n` steps. -/
def reflectionLineAt [DecidableEq K]
    (initial : ReflectionPair K) (index : Nat) : Line K :=
  (reflectionPairAt initial index).previous

/-- Restarting the finite iterator after `start` steps and taking `offset` more steps is the same finite computation as
taking `start + offset` steps at once. -/
theorem reflectionPairAt_add [DecidableEq K]
    (initial : ReflectionPair K) (start offset : Nat) :
    reflectionPairAt initial (start + offset) =
      reflectionPairAt (reflectionPairAt initial
        start) offset := by
  induction offset with
  | zero =>
      rw [Nat.add_zero]
      rfl
  | succ offset inductionHypothesis =>
      rw [Nat.add_succ]
      change
        (reflectionPairAt initial (start + offset)).step =
          (reflectionPairAt (reflectionPairAt
            initial start) offset).step
      rw [inductionHypothesis]

/-- The line at an offset from a finitely reached state is the line at the sum of the two finite indices. -/
theorem reflectionLineAt_add [DecidableEq K]
    (initial : ReflectionPair K) (start offset : Nat) :
    reflectionLineAt (reflectionPairAt initial start) offset =
      reflectionLineAt initial (start + offset) := by
  unfold reflectionLineAt
  rw [reflectionPairAt_add]

/-- The zeroth line of the iterator is the initial previous line. -/
@[simp] theorem reflectionLineAt_zero [DecidableEq K]
    (initial : ReflectionPair K) :
    reflectionLineAt initial 0 = initial.previous := rfl

/-- The next indexed line is the current line of the preceding iterator state. -/
@[simp] theorem reflectionLineAt_succ [DecidableEq K]
    (initial : ReflectionPair K) (index : Nat) :
    reflectionLineAt initial (index + 1) =
      (reflectionPairAt initial index).current := rfl

/-- Every finitely generated line remains non-null. -/
theorem reflectionLineAt_nonNull [DecidableEq K]
    (initial : ReflectionPair K) (index : Nat) :
    ¬ (reflectionLineAt initial index).IsNull :=
  (reflectionPairAt initial index).previousNonNull

/-- The finite iterator realizes exactly the printed reflection recurrence. -/
theorem reflectionLineAt_succ_succ [DecidableEq K]
    (initial : ReflectionPair K) (index : Nat) :
    reflectionLineAt initial (index + 2) =
      Line.reflectLine (reflectionLineAt initial (index + 1))
        (reflectionLineAt initial index)
        (reflectionLineAt_nonNull initial (index + 1)) := by
  rfl

/-- If the two initial lines pass through a point, every requested finite iterate passes through it. -/
theorem reflectionLineAt_contains [DecidableEq K]
    (initial : ReflectionPair K) (point : Point K)
    (previousContains : initial.previous.Contains point)
    (currentContains : initial.current.Contains point) (index : Nat) :
    (reflectionLineAt initial index).Contains point := by
  have allPairs : ∀ currentIndex : Nat,
      (reflectionLineAt initial currentIndex).Contains point ∧
        (reflectionLineAt initial (currentIndex + 1)).Contains point := by
    intro currentIndex
    induction currentIndex with
    | zero => exact ⟨previousContains, currentContains⟩
    | succ currentIndex inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · rw [show Nat.succ currentIndex + 1 = currentIndex + 2 by omega0,
            reflectionLineAt_succ_succ]
          exact Line.reflectLine_contains_common_point
            (reflectionLineAt initial (currentIndex + 1))
            (reflectionLineAt initial currentIndex)
            (reflectionLineAt_nonNull initial (currentIndex + 1)) point
            inductionHypothesis.2 inductionHypothesis.1
  exact (allPairs index).1

/-- Theorem 18 (Cyclic reflection), in its executable finite-prefix form. The center is `leftIndex + offset`; the right
endpoint is the same finite distance beyond it. -/
theorem cyclic_reflection_right [Nontrivial K] [DecidableEq K]
    (initial : ReflectionPair K) (offset leftIndex : Nat) :
    (Line.reflectLine
      (reflectionLineAt initial (leftIndex + offset))
      (reflectionLineAt initial (leftIndex + 2 * offset))
      (reflectionLineAt_nonNull initial (leftIndex + offset))).Equivalent
        (reflectionLineAt initial leftIndex) := by
  have paired : ∀ distance : Nat,
      (∀ left : Nat,
        (Line.reflectLine
          (reflectionLineAt initial (left + distance))
          (reflectionLineAt initial (left + 2 * distance))
          (reflectionLineAt_nonNull initial (left + distance))).Equivalent
            (reflectionLineAt initial left)) ∧
      (∀ left : Nat,
        (Line.reflectLine
          (reflectionLineAt initial (left + (distance + 1)))
          (reflectionLineAt initial (left + 2 * (distance + 1)))
          (reflectionLineAt_nonNull initial (left + (distance + 1)))).Equivalent
            (reflectionLineAt initial left)) := by
    intro distance
    induction distance with
    | zero =>
        constructor
        · intro left
          simpa only [Nat.add_zero, Nat.mul_zero] using
            Line.reflectLine_self_equivalent
              (reflectionLineAt initial left)
              (reflectionLineAt_nonNull initial left)
        · intro left
          have recurrence := reflectionLineAt_succ_succ initial left
          rw [show left + (0 + 1) = left + 1 by omega0,
            show left + 2 * (0 + 1) = left + 2 by omega0,
            recurrence]
          exact Line.reflectLine_involutive
            (reflectionLineAt initial (left + 1))
            (reflectionLineAt initial left)
            (reflectionLineAt_nonNull initial (left + 1))
    | succ distance inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · intro left
          have firstReflected :
              (Line.reflectLine
                (reflectionLineAt initial (left + distance + 2))
                (reflectionLineAt initial (left + 2 * distance + 3))
                (reflectionLineAt_nonNull initial
                  (left + distance + 2))).Equivalent
                (reflectionLineAt initial (left + 1)) := by
            simpa only [show (left + 1) + (distance + 1) =
                left + distance + 2 by omega0,
              show (left + 1) + 2 * (distance + 1) =
                left + 2 * distance + 3 by omega0] using
              inductionHypothesis.2 (left + 1)
          have secondReflected :
              (Line.reflectLine
                (reflectionLineAt initial (left + distance + 2))
                (reflectionLineAt initial (left + 2 * distance + 2))
                (reflectionLineAt_nonNull initial
                  (left + distance + 2))).Equivalent
                (reflectionLineAt initial (left + 2)) := by
            simpa only [show (left + 2) + distance =
                left + distance + 2 by omega0,
              show (left + 2) + 2 * distance =
                left + 2 * distance + 2 by omega0] using
              inductionHypothesis.1 (left + 2)
          have rightRecurrence := reflectionLineAt_succ_succ initial
            (left + 2 * distance + 2)
          have conjugation := Line.lineation_composition
            (reflectionLineAt initial (left + 2 * distance + 3))
            (reflectionLineAt initial (left + distance + 2))
            (reflectionLineAt initial (left + 2 * distance + 2))
            (reflectionLineAt_nonNull initial (left + 2 * distance + 3))
            (reflectionLineAt_nonNull initial (left + distance + 2))
          have reflectedCongruence := Line.reflectLine_equivalent_of_equivalent
            (Line.reflectLine
              (reflectionLineAt initial (left + distance + 2))
              (reflectionLineAt initial (left + 2 * distance + 3))
              (reflectionLineAt_nonNull initial (left + distance + 2)))
            (reflectionLineAt initial (left + 1))
            (Line.reflectLine
              (reflectionLineAt initial (left + distance + 2))
              (reflectionLineAt initial (left + 2 * distance + 2))
              (reflectionLineAt_nonNull initial (left + distance + 2)))
            (reflectionLineAt initial (left + 2))
            (Line.reflectLine_nonNull
              (reflectionLineAt initial (left + distance + 2))
              (reflectionLineAt initial (left + 2 * distance + 3))
              (reflectionLineAt_nonNull initial (left + distance + 2))
              (reflectionLineAt_nonNull initial (left + 2 * distance + 3)))
            (reflectionLineAt_nonNull initial (left + 1))
            firstReflected secondReflected
          have leftRecurrence := reflectionLineAt_succ_succ initial left
          have reflectedBack :
              (Line.reflectLine
                (reflectionLineAt initial (left + 1))
                (reflectionLineAt initial (left + 2))
                (reflectionLineAt_nonNull initial (left + 1))).Equivalent
                (reflectionLineAt initial left) := by
            rw [leftRecurrence]
            exact Line.reflectLine_involutive
              (reflectionLineAt initial (left + 1))
              (reflectionLineAt initial left)
              (reflectionLineAt_nonNull initial (left + 1))
          rw [show left + (Nat.succ distance + 1) =
              left + distance + 2 by omega0,
            show left + 2 * (Nat.succ distance + 1) =
              (left + 2 * distance + 2) + 2 by omega0,
            rightRecurrence]
          exact Relations.line_equivalent_trans conjugation
            (Relations.line_equivalent_trans reflectedCongruence reflectedBack)
  exact (paired offset).1 leftIndex

/-- The reverse half of the same finite reflection symmetry: reflecting the left endpoint across its center produces the
right endpoint. -/
theorem cyclic_reflection_left [Nontrivial K] [DecidableEq K]
    (initial : ReflectionPair K) (offset leftIndex : Nat) :
    (Line.reflectLine
      (reflectionLineAt initial (leftIndex + offset))
      (reflectionLineAt initial leftIndex)
      (reflectionLineAt_nonNull initial (leftIndex + offset))).Equivalent
        (reflectionLineAt initial (leftIndex + 2 * offset)) := by
  have rightReflection := cyclic_reflection_right initial offset leftIndex
  have congruence := Line.reflectLine_equivalent_of_equivalent
    (reflectionLineAt initial (leftIndex + offset))
    (reflectionLineAt initial (leftIndex + offset))
    (Line.reflectLine
      (reflectionLineAt initial (leftIndex + offset))
      (reflectionLineAt initial (leftIndex + 2 * offset))
      (reflectionLineAt_nonNull initial (leftIndex + offset)))
    (reflectionLineAt initial leftIndex)
    (reflectionLineAt_nonNull initial (leftIndex + offset))
    (reflectionLineAt_nonNull initial (leftIndex + offset))
    (Line.equivalent_refl _)
    rightReflection
  exact Relations.line_equivalent_trans
    (Line.equivalent_symm congruence)
    (Line.reflectLine_involutive
      (reflectionLineAt initial (leftIndex + offset))
      (reflectionLineAt initial (leftIndex + 2 * offset))
      (reflectionLineAt_nonNull initial (leftIndex + offset)))

end Purelib.Geometry.Plane.Reflection.Iteration

end
