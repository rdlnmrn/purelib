module
import Purelib.Data.Nat.Subtraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Point.Basic
import Purelib.Geometry.Plane.Reflection.Iteration
public import Purelib.Geometry.Plane.Reflection.Iteration.Spread
public import Purelib.Geometry.Stars.Regular.OrderSeven.Basic
import Purelib.Polynomial.Recurrence.Spread.Basic
public import Purelib.Polynomial.Recurrence.Spread.Roots.Seven
public import Purelib.Polynomial.Recurrence.Spread.Values
import Init.Data.Nat.Basic
import Init.Prelude
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
import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Ring.Nat

open Purelib.Algebra.Field (ExplicitField)

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Plane.Reflection.Iteration

open Purelib.Geometry.Plane.Reflection.Iteration.Spread

open Purelib.Geometry.Stars.Regular

open Purelib.Polynomial.Recurrence

open Purelib.Polynomial.Recurrence.Spread

section
@[expose] public section

/-!
# Divine Proportions, Theorem 97: regular stars of order seven

Only the seven required lines are quantified over, through `Fin 7`.  Their
coefficients are obtained by the executable finite reflection iterator; the
two closing equations record exactly the wraparound needed for the cyclic
star.  No completed two-sided reflection sequence is introduced.
-/

namespace Purelib.Geometry.Stars.Regular.OrderSeven.Construction

variable {K : Type*} [ExplicitField K]

section
open _root_.Purelib.Geometry
/-- Pairwise nonparallelism of the first seven iterates follows from the six nonzero lower spread polynomials. -/
private theorem
  reflectionLineAt_pairwise_nonparallel_before_seven
    [Nontrivial K] [DecidableEq K]
    (initial : Iteration.ReflectionPair K) (adjacentNonzero : (ReflectionPair.adjacentSpread initial) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (lowerNonzero : ∀ index : Nat, 1 ≤ index → index < 7 →
      Spread.Basic.spreadPolynomial index (ReflectionPair.adjacentSpread initial) ≠ 0)
    (first second : Fin 7) (different : first ≠ second) :
    ¬ (Iteration.reflectionLineAt initial first.val).Parallel
      (Iteration.reflectionLineAt initial second.val) := by
  have valuesDifferent : first.val ≠ second.val := by
    intro equal
    exact different (Fin.ext equal)
  have ordered : ∀ left right : Fin 7, left.val < right.val →
      ¬ (Iteration.reflectionLineAt initial left.val).Parallel
        (Iteration.reflectionLineAt initial right.val) := by
    intro left right leftLessRight parallel
    let offset := right.val - left.val
    have offsetPositive : 1 ≤ offset :=
      Data.Nat.Subtraction.sub_pos_of_lt leftLessRight
    have offsetBelowSeven : offset < 7 :=
      (Nat.sub_le right.val left.val).trans_lt right.isLt
    let shifted := Iteration.reflectionPairAt initial left.val
    have shiftedSpread : (ReflectionPair.adjacentSpread shifted) = (ReflectionPair.adjacentSpread initial) := by
      unfold shifted ReflectionPair.adjacentSpread
      exact Spread.reflectionLineAt_adjacent_spread initial left.val
    have shiftedNotParallel : ¬ shifted.previous.Parallel shifted.current := by
      intro adjacentParallel
      apply adjacentNonzero
      calc
        (ReflectionPair.adjacentSpread initial) = (ReflectionPair.adjacentSpread shifted) := shiftedSpread.symm
        _ = 0 := (Spread.spread_eq_zero_iff_parallel shifted.previous shifted.current
          shifted.previousNonNull shifted.currentNonNull).2 adjacentParallel
    have formula := Spread.consecutive_spreads shifted shiftedNotParallel
      twoNonzero offset
    have indexSum : left.val + offset = right.val :=
      Data.Nat.Subtraction.add_sub_of_le leftLessRight.le
    rw [shiftedSpread] at formula
    unfold shifted at formula
    have formulaAtIndices :
        Spread.spread (Iteration.reflectionLineAt initial left.val)
            (Iteration.reflectionLineAt initial right.val)
            (Iteration.reflectionLineAt_nonNull initial left.val)
            (Iteration.reflectionLineAt_nonNull initial right.val) =
          Spread.Basic.spreadPolynomial offset (ReflectionPair.adjacentSpread initial) := by
      simpa only [Iteration.reflectionLineAt, ← Iteration.reflectionPairAt_add, indexSum]
        using formula
    have spreadZero :
        Spread.spread (Iteration.reflectionLineAt initial left.val)
            (Iteration.reflectionLineAt initial right.val)
            (Iteration.reflectionLineAt_nonNull initial left.val)
            (Iteration.reflectionLineAt_nonNull initial right.val) = 0 :=
      (Spread.spread_eq_zero_iff_parallel
        (Iteration.reflectionLineAt initial left.val)
        (Iteration.reflectionLineAt initial right.val)
        (Iteration.reflectionLineAt_nonNull initial left.val)
        (Iteration.reflectionLineAt_nonNull initial right.val)).2 parallel
    apply lowerNonzero offset offsetPositive offsetBelowSeven
    calc
      Spread.Basic.spreadPolynomial offset (ReflectionPair.adjacentSpread initial) =
          Spread.spread (Iteration.reflectionLineAt initial left.val)
            (Iteration.reflectionLineAt initial right.val)
            (Iteration.reflectionLineAt_nonNull initial left.val)
            (Iteration.reflectionLineAt_nonNull initial right.val) :=
        formulaAtIndices.symm
      _ = 0 := spreadZero
  rcases Nat.lt_or_gt_of_ne valuesDifferent with firstLess | secondLess
  · exact ordered first second firstLess
  · intro parallel
    exact ordered second first secondLess (Plane.Line.parallel_symm parallel)
/-- A zero seventh spread closes any finite reflection orbit whose first two lines pass through a common point. -/
private theorem
  reflectionLineAt_closes_at_seven
  [Nontrivial K]
    [DecidableEq K] (initial : Iteration.ReflectionPair K) (point : Plane.Point K)
    (previousContains : initial.previous.Contains point)
    (currentContains : initial.current.Contains point)
    (adjacentNonzero : (ReflectionPair.adjacentSpread initial) ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (seventhZero : Spread.Basic.spreadPolynomial 7 (ReflectionPair.adjacentSpread initial) = 0)
    (start : Nat) :
    (Iteration.reflectionLineAt initial (start + 7)).Equivalent
      (Iteration.reflectionLineAt initial start) := by
  let shifted := Iteration.reflectionPairAt initial start
  have shiftedSpread : (ReflectionPair.adjacentSpread shifted) = (ReflectionPair.adjacentSpread initial) := by
    unfold shifted ReflectionPair.adjacentSpread
    exact Spread.reflectionLineAt_adjacent_spread initial start
  have shiftedNotParallel : ¬ shifted.previous.Parallel shifted.current := by
    intro adjacentParallel
    apply adjacentNonzero
    calc
      (ReflectionPair.adjacentSpread initial) = (ReflectionPair.adjacentSpread shifted) := shiftedSpread.symm
      _ = 0 := (Spread.spread_eq_zero_iff_parallel shifted.previous shifted.current
        shifted.previousNonNull shifted.currentNonNull).2 adjacentParallel
  have spreadSeven := Spread.consecutive_spreads shifted shiftedNotParallel
    twoNonzero 7
  rw [shiftedSpread, seventhZero] at spreadSeven
  have shiftedParallel :
      shifted.previous.Parallel (Iteration.reflectionLineAt shifted 7) :=
    (Spread.spread_eq_zero_iff_parallel shifted.previous
      (Iteration.reflectionLineAt shifted 7) shifted.previousNonNull
      (Iteration.reflectionLineAt_nonNull shifted 7)).1 spreadSeven
  unfold shifted at shiftedParallel
  rw [Iteration.reflectionLineAt_add initial start 7] at shiftedParallel
  apply Relations.line_equivalent_of_parallel_and_common_point
    (Iteration.reflectionLineAt initial (start + 7))
    (Iteration.reflectionLineAt initial start) point
  · exact Plane.Line.parallel_symm shiftedParallel
  · exact Iteration.reflectionLineAt_contains initial point previousContains
      currentContains (start + 7)
  · exact Iteration.reflectionLineAt_contains initial point previousContains
      currentContains start
end

/-- For a spread number `s` with root `v²=s(1-s)`, the line `⟨s:v:0⟩` has spread `s` from `⟨0:1:0⟩`. -/
def orderSevenLine₁ [Nontrivial K] (value spreadRoot : K)
    (valueNonzero : value ≠ 0) : Plane.Line K where
  a := value
  b := spreadRoot
  c := 0
  direction_nonzero := Or.inl valueNonzero

/-- Build the initial reflection pair from a nonzero spread and its retained square root.

The previous line is the x-axis and the current line has coefficients `⟨value, spreadRoot, 0⟩`; both non-null
certificates are retained. -/
def orderSevenInitialPair [Nontrivial K] (value spreadRoot
  : K)
    (valueNonzero : value ≠ 0)
    (spreadSquare : spreadRoot ^ 2 = value * (1 - value)) :
    Iteration.ReflectionPair K where
  previous := Line.Basic.xAxis
  current := orderSevenLine₁ value spreadRoot valueNonzero
  previousNonNull := by
    intro nullNorm
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = 0 ^ 2 + 1 ^ 2 := by ring1
      _ = 0 := nullNorm
  currentNonNull := by
    intro nullNorm
    apply valueNonzero
    calc
      value = value ^ 2 + spreadRoot ^ 2 := by
        rw [spreadSquare]
        ring1
      _ = 0 := nullNorm

/-- The constructed initial pair has the prescribed adjacent spread.

The nonzero spread value and the supplied square equation justify cancellation of its direction quadrance. -/
theorem orderSevenInitialPair_adjacentSpread [Nontrivial
  K]
    [DecidableEq K] (value spreadRoot : K) (valueNonzero : value ≠ 0)
    (spreadSquare : spreadRoot ^ 2 = value * (1 - value)) :
    (ReflectionPair.adjacentSpread (orderSevenInitialPair value spreadRoot valueNonzero
      spreadSquare)) = value := by
  unfold ReflectionPair.adjacentSpread Spread.spread orderSevenInitialPair
    Line.Basic.xAxis orderSevenLine₁ Line.Basic.lineNorm
  rw [spreadSquare]
  simp only [ExplicitField.div_eq_mul_inv]
  rw [show (0 ^ 2 + 1 ^ 2) *
      (value ^ 2 + value * (1 - value)) = value by ring1]
  calc
    (0 * spreadRoot - value * 1) ^ 2 * value⁻¹ =
        value ^ 2 * value⁻¹ := by ring1
    _ = value * (value * value⁻¹) := by ring1
    _ = value := by
      rw [ExplicitField.mul_inv_cancel value valueNonzero]
      ring1

/-- Construct seven cyclic reflection lines from the cubic and square witnesses.

The nonzero spread solves `7 - 56s + 112s² - 64s³ = 0`, its complementary product has the supplied square root, and two
is nonzero in the field. -/
def orderSevenStar [Nontrivial K] [DecidableEq K]
    (value spreadRoot : K) (valueNonzero : value ≠ 0)
    (cubicZero :
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 = 0)
    (spreadSquare : spreadRoot ^ 2 = value * (1 - value))
    (twoNonzero : (2 : K) ≠ 0) : OrderSeven.Basic.RegularSevenStar K := by
  let initial := orderSevenInitialPair value spreadRoot
    valueNonzero
    spreadSquare
  have adjacentValue : (ReflectionPair.adjacentSpread initial) = value := by
    exact orderSevenInitialPair_adjacentSpread value spreadRoot
      valueNonzero
      spreadSquare
  have adjacentNonzero : (ReflectionPair.adjacentSpread initial) ≠ 0 := by
    rw [adjacentValue]
    exact valueNonzero
  have seventhZero : Spread.Basic.spreadPolynomial 7 (ReflectionPair.adjacentSpread initial) = 0 := by
    rw [adjacentValue, Values.spreadPolynomial_seven_formula, cubicZero]
    ring1
  let origin : Plane.Point K := ⟨0, 0⟩
  have previousContains : initial.previous.Contains origin := by
    unfold initial origin orderSevenInitialPair
      Purelib.Geometry.Plane.Line.Basic.xAxis Purelib.Geometry.Plane.Line.Contains
    ring1
  have currentContains : initial.current.Contains origin := by
    unfold initial origin orderSevenInitialPair
      orderSevenLine₁
      Purelib.Geometry.Plane.Line.Contains
    ring1
  exact
    { initial := initial
      pairwiseNonparallel := by
        intro first second different
        apply
          reflectionLineAt_pairwise_nonparallel_before_seven
          initial
          adjacentNonzero twoNonzero
        · intro index indexPositive indexBelowSeven
          rw [adjacentValue]
          exact Purelib.Polynomial.Recurrence.Spread.Roots.Seven.spreadPolynomial_nonzero_before_seven value
            valueNonzero
            cubicZero twoNonzero index indexPositive indexBelowSeven
        · exact different
      closesAtSeven := by
        simpa only [Nat.zero_add, Purelib.Geometry.Plane.Reflection.Iteration.reflectionLineAt_zero] using
          reflectionLineAt_closes_at_seven initial
            origin previousContains
            currentContains adjacentNonzero twoNonzero seventhZero 0
      closesAtEight := by
        have closing :=
          reflectionLineAt_closes_at_seven initial
          origin
          previousContains currentContains adjacentNonzero twoNonzero
          seventhZero 1
        rw [show 1 + 7 = 8 by decide] at closing
        simpa only [show Iteration.reflectionLineAt initial 1 = initial.current by rfl]
          using closing }
end Purelib.Geometry.Stars.Regular.OrderSeven.Construction

end
