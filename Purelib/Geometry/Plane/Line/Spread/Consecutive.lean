module
public import Purelib.Algebra.Group.Basic
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Geometry.Trigonometry.Spread.Triple
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Triple

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
open Purelib.Algebra
open Purelib.Data

-- These owned adapters retain the complete original operation dictionaries.
attribute [local instance 2000] Group.Negation.subNegZeroMonoid
  Nat.successorNeZero Nat.successorAtLeastTwo

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Trigonometry.Spread.Triple

section
public section

/-!
# Divine Proportions, Chapter 8: spread polynomials

Spread polynomials are primitive-recursive finite expressions.  No sequence
or limit object is introduced: evaluating index `n` performs exactly `n`
finite recurrence steps in the coefficient field.
-/

namespace Purelib.Geometry.Plane.Line.Spread.Consecutive

variable {K : Type*} [ExplicitField K]

/-- Three equal consecutive spreads give endpoint spread s or s times the square of 3 minus 4s.

All four lines are non-null, and the first and third are nonparallel to exclude the degenerate middle spread. -/
theorem three_equal_spreads [DecidableEq K]
    (line₀ line₁ line₂ line₃ : Plane.Line K)
    (line₀NonNull : ¬ line₀.IsNull) (line₁NonNull : ¬ line₁.IsNull)
    (line₂NonNull : ¬ line₂.IsNull) (line₃NonNull : ¬ line₃.IsNull)
    (firstEquality :
      Spread.spread line₀ line₁ line₀NonNull line₁NonNull =
        Spread.spread line₁ line₂ line₁NonNull line₂NonNull)
    (secondEquality :
      Spread.spread line₁ line₂ line₁NonNull line₂NonNull =
        Spread.spread line₂ line₃ line₂NonNull line₃NonNull)
    (notParallel : ¬ line₀.Parallel line₂) :
    let s := Spread.spread line₀ line₁ line₀NonNull line₁NonNull
    let r := Spread.spread line₀ line₃ line₀NonNull line₃NonNull
    r = s ∨ r = s * (3 - 4 * s) ^ 2 := by
  dsimp only
  let s := Spread.spread line₀ line₁ line₀NonNull line₁NonNull
  let q := Spread.spread line₀ line₂ line₀NonNull line₂NonNull
  let r := Spread.spread line₀ line₃ line₀NonNull line₃NonNull
  have middleAlternatives := Triple.equal_spreads line₀ line₁ line₂ line₀NonNull
    line₁NonNull line₂NonNull firstEquality
  change q = 0 ∨ q = 4 * s * (1 - s) at middleAlternatives
  have qNonzero : q ≠ 0 := by
    intro qZero
    apply notParallel
    exact (Spread.spread_eq_zero_iff_parallel line₀ line₂ line₀NonNull
      line₂NonNull).1 qZero
  have qEquation : q = 4 * s * (1 - s) := by
    rcases middleAlternatives with qZero | qValue
    · exact False.elim (qNonzero qZero)
    · exact qValue
  have thirdAdjacent :
      Spread.spread line₂ line₃ line₂NonNull line₃NonNull = s := by
    exact (firstEquality.trans secondEquality).symm
  have triple := Triple.three_lines_form_spreadTriple line₀ line₂ line₃
    line₀NonNull line₂NonNull line₃NonNull
  change TripleSpread.SpreadTriple
    (Spread.spread line₂ line₃ line₂NonNull line₃NonNull) r q at triple
  rw [thirdAdjacent, qEquation] at triple
  have factorProduct :
      (r - s) * (r - s * (3 - 4 * s) ^ 2) = 0 := by
    calc
      (r - s) * (r - s * (3 - 4 * s) ^ 2) =
          -TripleSpread.tripleSpreadFunction s r (4 * s * (1 - s)) := by
            unfold TripleSpread.tripleSpreadFunction
            ring1
      _ = 0 := by
        unfold TripleSpread.SpreadTriple at triple
        rw [triple]
        ring1
  by_cases firstFactorZero : r - s = 0
  · left
    exact Group.eq_of_sub_eq_zero firstFactorZero
  · right
    have secondFactorZero : r - s * (3 - 4 * s) ^ 2 = 0 := by
      by_cases secondFactorCase : r - s * (3 - 4 * s) ^ 2 = 0
      · exact secondFactorCase
      · exact False.elim
          ((ExplicitField.mul_ne_zero firstFactorZero secondFactorCase)
            factorProduct)
    exact Group.eq_of_sub_eq_zero secondFactorZero

/-- A prescribed three-step spread gives the two polynomial alternatives for the next endpoint spread.

The three lines are non-null, their adjacent spread is the supplied value and the preceding endpoint spread is value
times the square of 3 minus 4 times value. -/
theorem exercise_8_1 [DecidableEq K]
    (line₀ line₃ line₄ : Plane.Line K)
    (line₀NonNull : ¬ line₀.IsNull) (line₃NonNull : ¬ line₃.IsNull)
    (line₄NonNull : ¬ line₄.IsNull)
    (value : K)
    (adjacentValue :
      Spread.spread line₃ line₄ line₃NonNull line₄NonNull = value)
    (threeStepValue :
      Spread.spread line₀ line₃ line₀NonNull line₃NonNull =
        value * (3 - 4 * value) ^ 2) :
    let result := Spread.spread line₀ line₄ line₀NonNull line₄NonNull
    result = 4 * value * (1 - value) ∨
      result = 16 * value * (1 - value) * (1 - 2 * value) ^ 2 := by
  dsimp only
  let result := Spread.spread line₀ line₄ line₀NonNull line₄NonNull
  have triple := Triple.three_lines_form_spreadTriple line₀ line₃ line₄
    line₀NonNull line₃NonNull line₄NonNull
  change TripleSpread.SpreadTriple
    (Spread.spread line₃ line₄ line₃NonNull line₄NonNull)
    result
    (Spread.spread line₀ line₃ line₀NonNull line₃NonNull) at triple
  rw [adjacentValue, threeStepValue] at triple
  have factorProduct :
      (result - 4 * value * (1 - value)) *
        (result - 16 * value * (1 - value) * (1 - 2 * value) ^ 2) = 0 := by
    calc
      (result - 4 * value * (1 - value)) *
          (result - 16 * value * (1 - value) * (1 - 2 * value) ^ 2) =
        -TripleSpread.tripleSpreadFunction value result
          (value * (3 - 4 * value) ^ 2) := by
            unfold TripleSpread.tripleSpreadFunction
            ring1
      _ = 0 := by rw [triple]; ring1
  by_cases firstZero : result - 4 * value * (1 - value) = 0
  · left
    exact Group.eq_of_sub_eq_zero firstZero
  · right
    have secondZero :
        result - 16 * value * (1 - value) * (1 - 2 * value) ^ 2 = 0 := by
      by_cases candidateZero :
          result - 16 * value * (1 - value) * (1 - 2 * value) ^ 2 = 0
      · exact candidateZero
      · exact False.elim
          ((ExplicitField.mul_ne_zero firstZero candidateZero)
            factorProduct)
    exact Group.eq_of_sub_eq_zero secondZero
end Purelib.Geometry.Plane.Line.Spread.Consecutive

end

end
