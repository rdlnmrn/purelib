module
import Purelib.Geometry.Plane.Line.Spread.Classification
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Triple
import Purelib.Geometry.Plane.Line.Trigonometry.Conversion
public import Purelib.Geometry.Plane.Reflection.Iteration
import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Spread
import Purelib.Geometry.Trigonometry.Spread.Triple
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Purelib.Polynomial.Recurrence.Spread.Triple
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Plane.Reflection

open Purelib.Geometry.Plane.Reflection.Iteration

open Purelib.Geometry.Trigonometry.Spread

open Purelib.Geometry.Trigonometry.Spread.Triple

open Purelib.Polynomial.Recurrence

open Purelib.Polynomial.Recurrence.Spread

section
@[expose] public section

/-!
# Divine Proportions, Theorem 58: finite reflection chains

The book writes a two-sided infinite reflection sequence.  The constructive
content needed by Theorem 58 is instead an executable finite iterator: after
`n` calls it contains exactly the adjacent pair `(lₙ,lₙ₊₁)`.  No completed
sequence is defined or quantified over.
-/

namespace Purelib.Geometry.Plane.Reflection.Iteration.Spread

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

namespace ReflectionPair

/-- The spread of the adjacent pair carried by a state. -/
def adjacentSpread (state :
  Iteration.ReflectionPair K) : K :=
  Spread.spread state.previous state.current state.previousNonNull state.currentNonNull

open Purelib.Geometry.Plane.Reflection.Iteration.ReflectionPair in
/-- One reflection step preserves the adjacent spread. -/
theorem adjacentSpread_step [DecidableEq K]
  (state : Iteration.ReflectionPair K) :
    (adjacentSpread state.step) = (adjacentSpread state) := by
  unfold adjacentSpread step
  calc
    Spread.spread state.current
        (Line.reflectLine state.current state.previous state.currentNonNull)
        state.currentNonNull
        (Line.reflectLine_nonNull state.current state.previous
          state.currentNonNull state.previousNonNull) =
      Spread.spread (Line.reflectLine state.current state.previous state.currentNonNull)
        state.current
        (Line.reflectLine_nonNull state.current state.previous
          state.currentNonNull state.previousNonNull)
        state.currentNonNull :=
      Spread.spread_symm _ _ _ _
    _ = Spread.spread state.previous state.current state.previousNonNull
        state.currentNonNull :=
      Spread.spread_reflectLine_mirror state.current state.previous
        state.currentNonNull state.previousNonNull

end ReflectionPair

/-- Every adjacent pair in the finite chain has the initial spread. -/
theorem reflectionLineAt_adjacent_spread [DecidableEq K]
    (initial : Iteration.ReflectionPair K) (index : Nat) :
    Spread.spread (Iteration.reflectionLineAt initial index)
        (Iteration.reflectionLineAt initial (index + 1))
        (Iteration.reflectionLineAt_nonNull initial index)
        (Iteration.reflectionLineAt_nonNull initial (index + 1)) =
      (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      calc
        Spread.spread (Iteration.reflectionLineAt initial (Nat.succ index))
            (Iteration.reflectionLineAt initial (Nat.succ index + 1))
            (Iteration.reflectionLineAt_nonNull initial (Nat.succ index))
            (Iteration.reflectionLineAt_nonNull initial (Nat.succ index + 1)) =
          (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread (Iteration.reflectionPairAt initial
            index).step) := by
            rfl
        _ = (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread (Iteration.reflectionPairAt
          initial index)) :=
          Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread_step _
        _ = (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by
          simpa only [Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread,
            Iteration.reflectionLineAt,
            Iteration.reflectionPairAt, ReflectionPair.step] using inductionHypothesis

section
open _root_.Purelib.Geometry
/-- The consecutive-spread identity at one displayed index. The index is an explicit argument so the simultaneous
induction never needs equality of proposition-valued functions. -/
private def
  consecutiveSpreadFormulaAt
  [DecidableEq K]
    (initial : Iteration.ReflectionPair K) (currentIndex : Nat) : Prop :=
  Spread.spread initial.previous (Iteration.reflectionLineAt initial currentIndex)
      initial.previousNonNull
      (Iteration.reflectionLineAt_nonNull initial currentIndex) =
    Spread.Basic.spreadPolynomial currentIndex (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread
      initial)
end

/-- Theorem 58 (Consecutive spreads), stated for the executable finite reflection iterator. Requesting index `n`
constructs only the first `n` reflection steps. -/
theorem consecutive_spreads [DecidableEq K]
    (initial : Iteration.ReflectionPair K)
    (notParallel : ¬ initial.previous.Parallel initial.current)
    (twoNonzero : (2 : K) ≠ 0)
    (index : Nat) :
    Spread.spread initial.previous (Iteration.reflectionLineAt initial index)
        initial.previousNonNull (Iteration.reflectionLineAt_nonNull initial index) =
      Spread.Basic.spreadPolynomial index (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread
        initial) := by
  have allPairs : ∀ currentIndex : Nat,
      consecutiveSpreadFormulaAt initial currentIndex ∧
        consecutiveSpreadFormulaAt initial (currentIndex + 1) := by
    intro currentIndex
    induction currentIndex with
    | zero =>
        constructor
        · unfold consecutiveSpreadFormulaAt
          change Spread.spread initial.previous initial.previous
              initial.previousNonNull initial.previousNonNull = 0
          exact (Spread.spread_eq_zero_iff_parallel initial.previous initial.previous
            initial.previousNonNull initial.previousNonNull).2 (by
              unfold Plane.Line.Parallel
              ring1)
        · unfold consecutiveSpreadFormulaAt
          change (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) =
            Spread.Basic.spreadPolynomial 1 (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread
              initial)
          rw [Spread.Basic.spreadPolynomial_one]
    | succ currentIndex inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · change consecutiveSpreadFormulaAt initial
            (Nat.succ currentIndex + 1)
          have previousValue :
              Spread.spread initial.previous
                  (Iteration.reflectionLineAt initial currentIndex)
                  initial.previousNonNull
                  (Iteration.reflectionLineAt_nonNull initial currentIndex) =
                Spread.Basic.spreadPolynomial currentIndex
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) :=
            inductionHypothesis.1
          have currentValue :
              Spread.spread initial.previous
                  (Iteration.reflectionLineAt initial (currentIndex + 1))
                  initial.previousNonNull
                  (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1)) =
                Spread.Basic.spreadPolynomial (currentIndex + 1)
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) :=
            inductionHypothesis.2
          let previous := Iteration.reflectionLineAt initial currentIndex
          let current := Iteration.reflectionLineAt initial (currentIndex + 1)
          let next := Iteration.reflectionLineAt initial (currentIndex + 2)
          let candidate := Spread.spread initial.previous next
            initial.previousNonNull
            (Iteration.reflectionLineAt_nonNull initial (currentIndex + 2))
          let currentSpread := Spread.spread initial.previous current
            initial.previousNonNull
            (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1))
          have adjacentPrevious :
              Spread.spread previous current
                  (Iteration.reflectionLineAt_nonNull initial currentIndex)
                  (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1)) =
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by
            exact reflectionLineAt_adjacent_spread initial currentIndex
          have adjacentNext :
              Spread.spread current next
                  (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1))
                  (Iteration.reflectionLineAt_nonNull initial (currentIndex + 2)) =
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by
            exact reflectionLineAt_adjacent_spread initial (currentIndex + 1)
          have adjacentNotParallel : ¬ previous.Parallel current := by
            intro parallel
            have adjacentZero :
                Spread.spread previous current
                    (Iteration.reflectionLineAt_nonNull initial currentIndex)
                    (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1)) = 0 :=
              (Spread.spread_eq_zero_iff_parallel previous current
                (Iteration.reflectionLineAt_nonNull initial currentIndex)
                (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1))).2 parallel
            have initialZero : (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) = 0 :=
              by
              calc
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) =
                    Spread.spread previous current
                      (Iteration.reflectionLineAt_nonNull initial currentIndex)
                      (Iteration.reflectionLineAt_nonNull initial
                        (currentIndex + 1)) := adjacentPrevious.symm
                _ = 0 := adjacentZero
            apply notParallel
            exact (Spread.spread_eq_zero_iff_parallel initial.previous initial.current
              initial.previousNonNull initial.currentNonNull).1 initialZero
          have rawCandidateTriple := Triple.three_lines_form_spreadTriple
            initial.previous current next initial.previousNonNull
            (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1))
            (Iteration.reflectionLineAt_nonNull initial (currentIndex + 2))
          have candidateTriple :
              TripleSpread.SpreadTriple currentSpread
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) candidate := by
            unfold currentSpread candidate
            unfold TripleSpread.SpreadTriple TripleSpread.tripleSpreadFunction at rawCandidateTriple ⊢
            calc
              (Spread.spread initial.previous current initial.previousNonNull
                    (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1)) +
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) +
                  Spread.spread initial.previous next initial.previousNonNull
                    (Iteration.reflectionLineAt_nonNull initial
                      (currentIndex + 2))) ^ 2 -
                    2 *
                      ((Spread.spread initial.previous current
                          initial.previousNonNull
                          (Iteration.reflectionLineAt_nonNull initial
                            (currentIndex + 1))) ^ 2 +
                        (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) ^ 2 +
                        (Spread.spread initial.previous next
                          initial.previousNonNull
                          (Iteration.reflectionLineAt_nonNull initial
                            (currentIndex + 2))) ^ 2) -
                    4 *
                      Spread.spread initial.previous current initial.previousNonNull
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 1)) *
                      (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) *
                      Spread.spread initial.previous next initial.previousNonNull
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 2)) =
                (Spread.spread current next
                      (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1))
                      (Iteration.reflectionLineAt_nonNull initial (currentIndex + 2)) +
                    Spread.spread initial.previous next initial.previousNonNull
                      (Iteration.reflectionLineAt_nonNull initial
                        (currentIndex + 2)) +
                    Spread.spread initial.previous current initial.previousNonNull
                      (Iteration.reflectionLineAt_nonNull initial
                        (currentIndex + 1))) ^ 2 -
                  2 *
                    ((Spread.spread current next
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 1))
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 2))) ^ 2 +
                      (Spread.spread initial.previous next initial.previousNonNull
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 2))) ^ 2 +
                      (Spread.spread initial.previous current initial.previousNonNull
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 1))) ^ 2) -
                  4 *
                    Spread.spread current next
                      (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1))
                      (Iteration.reflectionLineAt_nonNull initial (currentIndex + 2)) *
                    Spread.spread initial.previous next initial.previousNonNull
                      (Iteration.reflectionLineAt_nonNull initial
                        (currentIndex + 2)) *
                    Spread.spread initial.previous current initial.previousNonNull
                      (Iteration.reflectionLineAt_nonNull initial
                        (currentIndex + 1)) := by
                          rw [adjacentNext]
                          ring1
              _ = 0 := rawCandidateTriple
          have currentValueNamed :
              currentSpread = Spread.Basic.spreadPolynomial (currentIndex + 1)
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by
            exact currentValue
          have candidatePolynomialTriple :
              TripleSpread.SpreadTriple
                (Spread.Basic.spreadPolynomial (currentIndex + 1)
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial))
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) candidate := by
            rw [← currentValueNamed]
            exact candidateTriple
          have sumEquation :
              Spread.Basic.spreadPolynomial currentIndex
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) +
                  Spread.Basic.spreadPolynomial (currentIndex + 2)
                    (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) =
                2 *
                  (Spread.Basic.spreadPolynomial (currentIndex + 1)
                      (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) +
                    (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) -
                    2 * Spread.Basic.spreadPolynomial (currentIndex + 1)
                      (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) *
                        (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial)) := by
            rw [Spread.Basic.spreadPolynomial_succ_succ]
            ring1
          have alternatives :
              candidate = Spread.Basic.spreadPolynomial currentIndex
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) ∨
                candidate = Spread.Basic.spreadPolynomial (currentIndex + 2)
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) :=
            Purelib.Geometry.Trigonometry.Spread.Triple.spreadTriple_recursive_alternatives
              (Spread.Basic.spreadPolynomial currentIndex
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial))
              (Spread.Basic.spreadPolynomial (currentIndex + 1)
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial))
              (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial)
              (Spread.Basic.spreadPolynomial (currentIndex + 2)
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial))
              candidate
              (Triple.recursive_spreads currentIndex
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial))
              candidatePolynomialTriple sumEquation
          have expectedTriple :
              TripleSpread.SpreadTriple currentSpread
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial)
                (Spread.Basic.spreadPolynomial (currentIndex + 2)
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial)) := by
            rw [currentValueNamed]
            simpa only [show currentIndex + 2 =
              (currentIndex + 1) + 1 by rfl] using
                (Triple.recursive_spreads (currentIndex + 1)
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial))
          have candidateEqualsExpectedOfSpecial
              (special : currentSpread = 0 ∨ currentSpread = 1) :
              candidate = Spread.Basic.spreadPolynomial (currentIndex + 2)
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by
            rcases special with currentZero | currentOne
            · have candidateAtZero := candidateTriple
              rw [currentZero] at candidateAtZero
              have candidateEqualsStep : candidate =
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) :=
                (Triple.spreadTriple_zero_iff candidate
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial)).1
                  (Triple.spreadTriple_swap_first_third candidateAtZero)
              have expectedAtZero := expectedTriple
              rw [currentZero] at expectedAtZero
              have expectedEqualsStep :
                  Spread.Basic.spreadPolynomial (currentIndex + 2)
                      (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) =
                        (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) :=
                (Triple.spreadTriple_zero_iff
                  (Spread.Basic.spreadPolynomial (currentIndex + 2)
                    (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial))
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial)).1
                    (Triple.spreadTriple_swap_first_third expectedAtZero)
              exact candidateEqualsStep.trans expectedEqualsStep.symm
            · have candidateAtOne := candidateTriple
              rw [currentOne] at candidateAtOne
              have candidateSum :
                  candidate + (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) = 1 :=
                (Triple.spreadTriple_one_iff candidate
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial)).1
                  (Triple.spreadTriple_swap_first_third candidateAtOne)
              have expectedAtOne := expectedTriple
              rw [currentOne] at expectedAtOne
              have expectedSum :
                  Spread.Basic.spreadPolynomial (currentIndex + 2)
                      (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) +
                        (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) = 1 :=
                (Triple.spreadTriple_one_iff
                  (Spread.Basic.spreadPolynomial (currentIndex + 2)
                    (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial))
                  (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial)).1
                    (Triple.spreadTriple_swap_first_third expectedAtOne)
              calc
                candidate =
                    (candidate + (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial)) -
                      (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by ring1
                _ = 1 - (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by
                  rw [candidateSum]
                _ = (Spread.Basic.spreadPolynomial (currentIndex + 2)
                      (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) +
                        (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial)) -
                    (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by rw
                      [expectedSum]
                _ = Spread.Basic.spreadPolynomial (currentIndex + 2)
                    (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by ring1
          have candidateEqualsExpected :
              candidate = Spread.Basic.spreadPolynomial (currentIndex + 2)
                (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by
            rcases alternatives with candidatePrevious | candidateExpected
            · have previousCandidateEqual :
                  Spread.spread initial.previous previous initial.previousNonNull
                      (Iteration.reflectionLineAt_nonNull initial currentIndex) =
                    candidate := by
                calc
                  Spread.spread initial.previous previous initial.previousNonNull
                        (Iteration.reflectionLineAt_nonNull initial currentIndex) =
                      Spread.Basic.spreadPolynomial currentIndex
                        (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) :=
                    previousValue
                  _ = candidate := candidatePrevious.symm
              by_cases previousNextDeterminantZero :
                  previous.a * next.b - next.a * previous.b = 0
              · have previousNextParallel : previous.Parallel next :=
                  previousNextDeterminantZero
                have fixedDirection :
                    previous.Parallel
                      (Line.reflectLine current previous
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 1))) := by
                  rw [← Iteration.reflectionLineAt_succ_succ initial currentIndex]
                  exact previousNextParallel
                rcases Line.parallel_or_perpendicular_of_parallel_reflectLine
                    current previous
                    (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1))
                    twoNonzero fixedDirection with
                  previousCurrentParallel | previousCurrentPerpendicular
                · exact False.elim
                    (adjacentNotParallel previousCurrentParallel)
                · have stepOne : (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) = 1
                    := by
                    calc
                      (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) =
                          Spread.spread previous current
                          (Iteration.reflectionLineAt_nonNull initial currentIndex)
                          (Iteration.reflectionLineAt_nonNull initial
                            (currentIndex + 1)) := adjacentPrevious.symm
                      _ = 1 := Trigonometry.Conversion.spread_eq_one_of_perpendicular previous current
                        (Iteration.reflectionLineAt_nonNull initial currentIndex)
                        (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1))
                        previousCurrentPerpendicular
                  have candidateAtStepOne := candidateTriple
                  rw [stepOne] at candidateAtStepOne
                  have candidateSum : candidate + currentSpread = 1 :=
                    (Triple.spreadTriple_one_iff candidate currentSpread).1
                      (Triple.spreadTriple_rotate
                        (Triple.spreadTriple_rotate candidateAtStepOne))
                  have expectedAtStepOne := expectedTriple
                  rw [stepOne] at expectedAtStepOne
                  have expectedSumAtOne :
                      Spread.Basic.spreadPolynomial (currentIndex + 2) 1 +
                          currentSpread = 1 :=
                    (Triple.spreadTriple_one_iff
                      (Spread.Basic.spreadPolynomial (currentIndex + 2)
                        1) currentSpread).1
                        (Triple.spreadTriple_rotate
                          (Triple.spreadTriple_rotate expectedAtStepOne))
                  have expectedSum :
                      Spread.Basic.spreadPolynomial (currentIndex + 2)
                          (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) +
                            currentSpread = 1 := by
                    rw [stepOne]
                    exact expectedSumAtOne
                  calc
                    candidate = candidate + currentSpread - currentSpread := by
                      ring1
                    _ = 1 - currentSpread := by rw [candidateSum]
                    _ = Spread.Basic.spreadPolynomial (currentIndex + 2)
                          (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) +
                            currentSpread -
                        currentSpread := by rw [expectedSum]
                    _ = Spread.Basic.spreadPolynomial (currentIndex + 2)
                        (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) := by ring1
              · have previousNextNotParallel : ¬ previous.Parallel next :=
                  previousNextDeterminantZero
                have leftEqual :
                    Spread.spread previous initial.previous
                        (Iteration.reflectionLineAt_nonNull initial currentIndex)
                        initial.previousNonNull =
                      Spread.spread next initial.previous
                        (Iteration.reflectionLineAt_nonNull initial (currentIndex + 2))
                        initial.previousNonNull := by
                  calc
                    Spread.spread previous initial.previous
                        (Iteration.reflectionLineAt_nonNull initial currentIndex)
                        initial.previousNonNull =
                      Spread.spread initial.previous previous initial.previousNonNull
                        (Iteration.reflectionLineAt_nonNull initial currentIndex) :=
                      Spread.spread_symm _ _ _ _
                    _ = candidate := previousCandidateEqual
                    _ = Spread.spread initial.previous next initial.previousNonNull
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 2)) := rfl
                    _ = Spread.spread next initial.previous
                        (Iteration.reflectionLineAt_nonNull initial (currentIndex + 2))
                        initial.previousNonNull :=
                      (Spread.spread_symm _ _ _ _).symm
                have rightEqual :
                    Spread.spread previous current
                        (Iteration.reflectionLineAt_nonNull initial currentIndex)
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 1)) =
                      Spread.spread next current
                        (Iteration.reflectionLineAt_nonNull initial (currentIndex + 2))
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 1)) := by
                  calc
                    Spread.spread previous current
                        (Iteration.reflectionLineAt_nonNull initial currentIndex)
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 1)) =
                            (Geometry.Plane.Reflection.Iteration.Spread.ReflectionPair.adjacentSpread initial) :=
                      adjacentPrevious
                    _ = Spread.spread current next
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 1))
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 2)) := adjacentNext.symm
                    _ = Spread.spread next current
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 2))
                        (Iteration.reflectionLineAt_nonNull initial
                          (currentIndex + 1)) :=
                      (Spread.spread_symm _ _ _ _).symm
                rcases Classification.equal_spread_lines_parallel_or_perpendicular
                    previous next initial.previous current
                    (Iteration.reflectionLineAt_nonNull initial currentIndex)
                    (Iteration.reflectionLineAt_nonNull initial (currentIndex + 2))
                    initial.previousNonNull
                    (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1))
                    previousNextNotParallel twoNonzero leftEqual rightEqual with
                  initialCurrentParallel | initialCurrentPerpendicular
                · have currentZero : currentSpread = 0 := by
                    exact (Spread.spread_eq_zero_iff_parallel initial.previous current
                      initial.previousNonNull
                      (Iteration.reflectionLineAt_nonNull initial
                        (currentIndex + 1))).2 initialCurrentParallel
                  exact candidateEqualsExpectedOfSpecial (Or.inl currentZero)
                · have currentOne : currentSpread = 1 :=
                    Trigonometry.Conversion.spread_eq_one_of_perpendicular initial.previous current
                      initial.previousNonNull
                      (Iteration.reflectionLineAt_nonNull initial (currentIndex + 1))
                      initialCurrentPerpendicular
                  exact candidateEqualsExpectedOfSpecial (Or.inr currentOne)
            · exact candidateExpected
          unfold consecutiveSpreadFormulaAt
          rw [show Nat.succ currentIndex + 1 = currentIndex + 2 by rfl]
          exact candidateEqualsExpected
  exact (allPairs index).1

end Purelib.Geometry.Plane.Reflection.Iteration.Spread

end
