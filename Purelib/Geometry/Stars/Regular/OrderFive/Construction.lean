module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Reflection.Line
public import Purelib.Geometry.Stars.Regular.OrderFive.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.CharZero.Defs

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Stars.Regular

section
public section

/-!
# Divine Proportions, Theorem 96: regular stars of order five

The five cyclic reflection equations and all ten nonparallel pairs are stored
as finite data.  The executable reflection iterator is then related to these
displayed representatives using quotient-free line congruence.
-/

namespace Purelib.Geometry.Stars.Regular.OrderFive.Construction

variable {K : Type*} [ExplicitField K]

/-- The printed line `⟨v:3-r:0⟩`. -/
@[expose] def orderFiveLine₁ [Nontrivial K] (root
  spreadRoot : K)
    (spreadRootNonzero : spreadRoot ≠ 0) : Plane.Line K where
  a := spreadRoot
  b := 3 - root
  c := 0
  direction_nonzero := Or.inl spreadRootNonzero

/-- The printed line `⟨v(3-r):2-2r:0⟩`. -/
@[expose] def orderFiveLine₂ [Nontrivial K] (root
  spreadRoot : K)
    (spreadRootNonzero : spreadRoot ≠ 0)
    (rootNeThree : (3 : K) - root ≠ 0) : Plane.Line K where
  a := spreadRoot * (3 - root)
  b := 2 - 2 * root
  c := 0
  direction_nonzero := Or.inl
    (ExplicitField.mul_ne_zero spreadRootNonzero rootNeThree)

/-- The printed line `⟨v(r-3):2-2r:0⟩`. -/
@[expose] def orderFiveLine₃ [Nontrivial K] (root
  spreadRoot : K)
    (spreadRootNonzero : spreadRoot ≠ 0)
    (rootMinusThreeNonzero : root - 3 ≠ 0) : Plane.Line K where
  a := spreadRoot * (root - 3)
  b := 2 - 2 * root
  c := 0
  direction_nonzero := Or.inl
    (ExplicitField.mul_ne_zero spreadRootNonzero rootMinusThreeNonzero)

/-- The printed line `⟨-v:3-r:0⟩`. -/
@[expose] def orderFiveLine₄ [Nontrivial K] (root
  spreadRoot : K)
    (spreadRootNonzero : spreadRoot ≠ 0) : Plane.Line K where
  a := -spreadRoot
  b := 3 - root
  c := 0
  direction_nonzero := Or.inl (by
    intro negZero
    apply spreadRootNonzero
    calc
      spreadRoot = -(-spreadRoot) := by ring1
      _ = 0 := by rw [negZero]; ring1)

/-- The five explicit source lines form a regular star from the displayed square witnesses. -/
@[expose] def orderFiveStar [Nontrivial K] [DecidableEq K]
    (root spreadRoot : K) (rootNonzero : root ≠ 0)
    (rootSquare : root ^ 2 = 5)
    (spreadSquare : spreadRoot ^ 2 = 2 * (5 - root))
    (twoNonzero : (2 : K) ≠ 0) : OrderFive.Basic.RegularFiveStar K := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    rw [fourAsProduct]
    exact ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have eightNonzero : (8 : K) ≠ 0 := by
    have eightAsProduct : (8 : K) = 2 * 2 * 2 := by ring1
    rw [eightAsProduct]
    exact ExplicitField.mul_ne_zero
      (ExplicitField.mul_ne_zero twoNonzero twoNonzero) twoNonzero
  have rootNeThree : (3 : K) - root ≠ 0 := by
    intro differenceZero
    have rootEqThree : root = 3 := by
      calc
        root = 3 - (3 - root) := by ring1
        _ = 3 := by rw [differenceZero]; ring1
    apply fourNonzero
    calc
      (4 : K) = root ^ 2 - 5 := by rw [rootEqThree]; ring1
      _ = 0 := by rw [rootSquare]; ring1
  have rootMinusThreeNonzero : root - 3 ≠ 0 := by
    intro differenceZero
    apply rootNeThree
    calc
      (3 : K) - root = -(root - 3) := by ring1
      _ = 0 := by rw [differenceZero]; ring1
  have rootNeTwo : (2 : K) - root ≠ 0 := by
    intro differenceZero
    have rootEqTwo : root = 2 := by
      calc
        root = 2 - (2 - root) := by ring1
        _ = 2 := by rw [differenceZero]; ring1
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 5 - root ^ 2 := by rw [rootEqTwo]; ring1
      _ = 0 := by rw [rootSquare]; ring1
  have rootNeOne : (1 : K) - root ≠ 0 := by
    intro differenceZero
    have rootEqOne : root = 1 := by
      calc
        root = 1 - (1 - root) := by ring1
        _ = 1 := by rw [differenceZero]; ring1
    apply fourNonzero
    calc
      (4 : K) = 5 - root ^ 2 := by rw [rootEqOne]; ring1
      _ = 0 := by rw [rootSquare]; ring1
  have sevenMinusThreeRootNonzero : (7 : K) - 3 * root ≠ 0 := by
    intro differenceZero
    have threeRoot : (3 : K) * root = 7 := by
      calc
        (3 : K) * root = 7 - (7 - 3 * root) := by ring1
        _ = 7 := by rw [differenceZero]; ring1
    apply fourNonzero
    calc
      (4 : K) = 7 ^ 2 - 9 * 5 := by ring1
      _ = (3 * root) ^ 2 - 9 * root ^ 2 := by
        rw [threeRoot, rootSquare]
      _ = 0 := by ring1
  have fiveMinusRootNonzero : (5 : K) - root ≠ 0 := by
    intro differenceZero
    have rootEqFive : root = 5 := by
      calc
        root = 5 - (5 - root) := by ring1
        _ = 5 := by rw [differenceZero]; ring1
    have idempotent : root * (root - 1) = 0 := by
      calc
        root * (root - 1) = root ^ 2 - root := by ring1
        _ = 0 := by rw [rootSquare, rootEqFive]; ring1
    have rootMinusOneZero : root - 1 = 0 := by
      by_cases zero : root - 1 = 0
      · exact zero
      · exact False.elim
          ((ExplicitField.mul_ne_zero rootNonzero zero) idempotent)
    have rootEqOne : root = 1 := by
      calc
        root = (root - 1) + 1 := by ring1
        _ = 1 := by rw [rootMinusOneZero]; ring1
    have fiveEqOne : (5 : K) = 1 := rootEqFive.symm.trans rootEqOne
    apply fourNonzero
    calc
      (4 : K) = 5 - 1 := by ring1
      _ = 1 - 1 := by rw [fiveEqOne]
      _ = 0 := by ring1
  have spreadRootNonzero : spreadRoot ≠ 0 := by
    intro zero
    apply (ExplicitField.mul_ne_zero twoNonzero fiveMinusRootNonzero)
    calc
      (2 : K) * (5 - root) = spreadRoot ^ 2 := spreadSquare.symm
      _ = 0 := by rw [zero]; ring1
  exact
    { line₀ := Purelib.Geometry.Plane.Line.Basic.xAxis
      line₁ := orderFiveLine₁ root spreadRoot spreadRootNonzero
      line₂ := orderFiveLine₂ root spreadRoot spreadRootNonzero
        rootNeThree
      line₃ := orderFiveLine₃ root spreadRoot spreadRootNonzero
        rootMinusThreeNonzero
      line₄ := orderFiveLine₄ root spreadRoot spreadRootNonzero
      line₀NonNull := by
        intro nullNorm
        apply (one_ne_zero : (1 : K) ≠ 0)
        calc
          (1 : K) = 0 ^ 2 + 1 ^ 2 := by ring1
          _ = 0 := nullNorm
      line₁NonNull := by
        intro nullNorm
        apply (ExplicitField.mul_ne_zero eightNonzero rootNeThree)
        calc
          (8 : K) * (3 - root) =
              spreadRoot ^ 2 + (3 - root) ^ 2 -
                (root ^ 2 - 5) := by
                  rw [spreadSquare]
                  ring1
          _ = spreadRoot ^ 2 + (3 - root) ^ 2 := by
                rw [rootSquare]
                ring1
          _ = 0 := nullNorm
      line₂NonNull := by
        intro nullNorm
        apply (ExplicitField.mul_ne_zero
          (show (32 : K) ≠ 0 by
            have thirtyTwoAsProduct : (32 : K) = 2 * 2 * 2 * 2 * 2 := by ring1
            rw [thirtyTwoAsProduct]
            exact ExplicitField.mul_ne_zero
              (ExplicitField.mul_ne_zero
                (ExplicitField.mul_ne_zero
                  (ExplicitField.mul_ne_zero twoNonzero twoNonzero)
                  twoNonzero) twoNonzero) twoNonzero)
          sevenMinusThreeRootNonzero)
        calc
          (32 : K) * (7 - 3 * root) =
              spreadRoot ^ 2 * (3 - root) ^ 2 +
                (2 - 2 * root) ^ 2 -
                (root ^ 2 - 5) * (26 - 2 * root) := by
                  rw [spreadSquare]
                  ring1
          _ = spreadRoot ^ 2 * (3 - root) ^ 2 +
                (2 - 2 * root) ^ 2 := by
                  rw [rootSquare]
                  ring1
          _ = (spreadRoot * (3 - root)) ^ 2 +
                (2 - 2 * root) ^ 2 := by ring1
          _ = 0 := nullNorm
      line₃NonNull := by
        intro nullNorm
        apply (ExplicitField.mul_ne_zero
          (show (32 : K) ≠ 0 by
            have thirtyTwoAsProduct : (32 : K) = 2 * 2 * 2 * 2 * 2 := by ring1
            rw [thirtyTwoAsProduct]
            exact ExplicitField.mul_ne_zero
              (ExplicitField.mul_ne_zero
                (ExplicitField.mul_ne_zero
                  (ExplicitField.mul_ne_zero twoNonzero twoNonzero)
                  twoNonzero) twoNonzero) twoNonzero)
          sevenMinusThreeRootNonzero)
        calc
          (32 : K) * (7 - 3 * root) =
              spreadRoot ^ 2 * (root - 3) ^ 2 +
                (2 - 2 * root) ^ 2 -
                (root ^ 2 - 5) * (26 - 2 * root) := by
                  rw [spreadSquare]
                  ring1
          _ = spreadRoot ^ 2 * (root - 3) ^ 2 +
                (2 - 2 * root) ^ 2 := by
                  rw [rootSquare]
                  ring1
          _ = (spreadRoot * (root - 3)) ^ 2 +
                (2 - 2 * root) ^ 2 := by ring1
          _ = 0 := nullNorm
      line₄NonNull := by
        intro nullNorm
        apply (ExplicitField.mul_ne_zero eightNonzero rootNeThree)
        calc
          (8 : K) * (3 - root) =
              spreadRoot ^ 2 + (3 - root) ^ 2 -
                (root ^ 2 - 5) := by
                  rw [spreadSquare]
                  ring1
          _ = (-spreadRoot) ^ 2 + (3 - root) ^ 2 := by
                rw [rootSquare]
                ring1
          _ = 0 := nullNorm
      line₀Line₁Nonparallel := by
        intro parallel
        apply spreadRootNonzero
        unfold Purelib.Geometry.Plane.Line.Parallel Purelib.Geometry.Plane.Line.Basic.xAxis
          orderFiveLine₁ at parallel
        calc
          spreadRoot = -(0 * (3 - root) - spreadRoot * 1) := by ring1
          _ = 0 := by rw [parallel]; ring1
      line₀Line₂Nonparallel := by
        intro parallel
        apply (ExplicitField.mul_ne_zero spreadRootNonzero rootNeThree)
        unfold Purelib.Geometry.Plane.Line.Parallel Purelib.Geometry.Plane.Line.Basic.xAxis
          orderFiveLine₂ at parallel
        calc
          spreadRoot * (3 - root) =
              -(0 * (2 - 2 * root) - spreadRoot * (3 - root) * 1) := by ring1
          _ = 0 := by rw [parallel]; ring1
      line₀Line₃Nonparallel := by
        intro parallel
        apply (ExplicitField.mul_ne_zero spreadRootNonzero
          rootMinusThreeNonzero)
        unfold Purelib.Geometry.Plane.Line.Parallel Purelib.Geometry.Plane.Line.Basic.xAxis
          orderFiveLine₃ at parallel
        calc
          spreadRoot * (root - 3) =
              -(0 * (2 - 2 * root) - spreadRoot * (root - 3) * 1) := by ring1
          _ = 0 := by rw [parallel]; ring1
      line₀Line₄Nonparallel := by
        intro parallel
        apply spreadRootNonzero
        unfold Purelib.Geometry.Plane.Line.Parallel Purelib.Geometry.Plane.Line.Basic.xAxis
          orderFiveLine₄ at parallel
        calc
          spreadRoot = 0 * (3 - root) - (-spreadRoot) * 1 := by ring1
          _ = 0 := parallel
      line₁Line₂Nonparallel := by
        intro parallel
        have productNonzero := ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero
            (show (4 : K) ≠ 0 from fourNonzero) spreadRootNonzero)
          rootMinusThreeNonzero
        apply productNonzero
        unfold Purelib.Geometry.Plane.Line.Parallel
          orderFiveLine₁
          orderFiveLine₂ at parallel
        calc
          (4 : K) * spreadRoot * (root - 3) =
              spreadRoot * (2 - 2 * root) -
                spreadRoot * (3 - root) * (3 - root) +
                spreadRoot * (root ^ 2 - 5) := by ring1
          _ = 0 := by rw [parallel, rootSquare]; ring1
      line₁Line₃Nonparallel := by
        intro parallel
        apply (ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero eightNonzero spreadRootNonzero)
          rootNeTwo)
        unfold Purelib.Geometry.Plane.Line.Parallel
          orderFiveLine₁
          orderFiveLine₃ at parallel
        calc
          (8 : K) * spreadRoot * (2 - root) =
              spreadRoot * (2 - 2 * root) -
                spreadRoot * (root - 3) * (3 - root) -
                spreadRoot * (root ^ 2 - 5) := by ring1
          _ = 0 := by rw [parallel, rootSquare]; ring1
      line₁Line₄Nonparallel := by
        intro parallel
        apply (ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero twoNonzero spreadRootNonzero)
          rootNeThree)
        unfold Purelib.Geometry.Plane.Line.Parallel
          orderFiveLine₁
          orderFiveLine₄ at parallel
        calc
          (2 : K) * spreadRoot * (3 - root) =
              spreadRoot * (3 - root) - (-spreadRoot) * (3 - root) := by ring1
          _ = 0 := parallel
      line₂Line₃Nonparallel := by
        intro parallel
        apply (ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero
            (ExplicitField.mul_ne_zero fourNonzero spreadRootNonzero)
            rootNeThree) rootNeOne)
        unfold Purelib.Geometry.Plane.Line.Parallel
          orderFiveLine₂
          orderFiveLine₃ at parallel
        calc
          (4 : K) * spreadRoot * (3 - root) * (1 - root) =
              spreadRoot * (3 - root) * (2 - 2 * root) -
                spreadRoot * (root - 3) * (2 - 2 * root) := by ring1
          _ = 0 := parallel
      line₂Line₄Nonparallel := by
        intro parallel
        apply (ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero eightNonzero spreadRootNonzero)
          rootNeTwo)
        unfold Purelib.Geometry.Plane.Line.Parallel
          orderFiveLine₂
          orderFiveLine₄ at parallel
        calc
          (8 : K) * spreadRoot * (2 - root) =
              spreadRoot * (3 - root) * (3 - root) -
                (-spreadRoot) * (2 - 2 * root) -
                spreadRoot * (root ^ 2 - 5) := by ring1
          _ = 0 := by rw [parallel, rootSquare]; ring1
      line₃Line₄Nonparallel := by
        intro parallel
        apply (ExplicitField.mul_ne_zero
          (ExplicitField.mul_ne_zero fourNonzero spreadRootNonzero)
          rootMinusThreeNonzero)
        unfold Purelib.Geometry.Plane.Line.Parallel
          orderFiveLine₃
          orderFiveLine₄ at parallel
        calc
          (4 : K) * spreadRoot * (root - 3) =
              spreadRoot * (root - 3) * (3 - root) -
                (-spreadRoot) * (2 - 2 * root) -
                (-spreadRoot * (root ^ 2 - 5)) := by ring1
          _ = 0 := by rw [parallel, rootSquare]; ring1
      reflectAround₀ := by
        unfold Purelib.Geometry.Plane.Line.Equivalent
        simp only [Line.reflectLine, Line.reflectedLineA, Line.reflectedLineB, Line.reflectedLineC,
          Line.Basic.lineNorm, Purelib.Geometry.Plane.Line.Basic.xAxis,
            orderFiveLine₁,
            orderFiveLine₄]
        constructor
        · ring1
        constructor <;> ring1
      reflectAround₁ := by
        unfold Purelib.Geometry.Plane.Line.Equivalent
        simp only [Line.reflectLine, Line.reflectedLineA, Line.reflectedLineB, Line.reflectedLineC,
          Line.Basic.lineNorm, Purelib.Geometry.Plane.Line.Basic.xAxis,
            orderFiveLine₁,
            orderFiveLine₂]
        constructor
        · apply Group.eq_of_sub_eq_zero
          calc
            _ = (root * spreadRoot - 3 * spreadRoot) *
                  (root ^ 2 - 5) +
                (-root * spreadRoot + 3 * spreadRoot) *
                  (spreadRoot ^ 2 - 2 * (5 - root)) := by ring1
            _ = 0 := by rw [rootSquare, spreadSquare]; ring1
        constructor <;> ring1
      reflectAround₂ := by
        unfold Purelib.Geometry.Plane.Line.Equivalent
        simp only [Line.reflectLine, Line.reflectedLineA, Line.reflectedLineB, Line.reflectedLineC,
          Line.Basic.lineNorm, orderFiveLine₁,
            orderFiveLine₂,
            orderFiveLine₃]
        constructor
        · apply Group.eq_of_sub_eq_zero
          calc
            _ = (2 * root ^ 3 * spreadRoot -
                  10 * root ^ 2 * spreadRoot +
                  6 * root * spreadRoot + 34 * spreadRoot) *
                  (root ^ 2 - 5) +
                (-root ^ 4 * spreadRoot +
                  6 * root ^ 3 * spreadRoot -
                  12 * root ^ 2 * spreadRoot +
                  18 * root * spreadRoot - 27 * spreadRoot) *
                  (spreadRoot ^ 2 - 2 * (5 - root)) := by ring1
            _ = 0 := by rw [rootSquare, spreadSquare]; ring1
        constructor <;> ring1
      reflectAround₃ := by
        unfold Purelib.Geometry.Plane.Line.Equivalent
        simp only [Line.reflectLine, Line.reflectedLineA, Line.reflectedLineB, Line.reflectedLineC,
          Line.Basic.lineNorm, orderFiveLine₂,
            orderFiveLine₃,
            orderFiveLine₄]
        constructor
        · apply Group.eq_of_sub_eq_zero
          calc
            _ = -(2 * root ^ 3 * spreadRoot -
                  10 * root ^ 2 * spreadRoot +
                  6 * root * spreadRoot + 34 * spreadRoot) *
                  (root ^ 2 - 5) -
                (-root ^ 4 * spreadRoot +
                  6 * root ^ 3 * spreadRoot -
                  12 * root ^ 2 * spreadRoot +
                  18 * root * spreadRoot - 27 * spreadRoot) *
                  (spreadRoot ^ 2 - 2 * (5 - root)) := by ring1
            _ = 0 := by rw [rootSquare, spreadSquare]; ring1
        constructor <;> ring1
      reflectAround₄ := by
        unfold Purelib.Geometry.Plane.Line.Equivalent
        simp only [Line.reflectLine, Line.reflectedLineA, Line.reflectedLineB, Line.reflectedLineC,
          Line.Basic.lineNorm, Purelib.Geometry.Plane.Line.Basic.xAxis,
            orderFiveLine₃,
            orderFiveLine₄]
        constructor
        · apply Group.eq_of_sub_eq_zero
          calc
            _ = -(root * spreadRoot - 3 * spreadRoot) *
                  (root ^ 2 - 5) -
                (-root * spreadRoot + 3 * spreadRoot) *
                  (spreadRoot ^ 2 - 2 * (5 - root)) := by ring1
            _ = 0 := by rw [rootSquare, spreadSquare]; ring1
        constructor <;> ring1 }
end Purelib.Geometry.Stars.Regular.OrderFive.Construction

end

end
