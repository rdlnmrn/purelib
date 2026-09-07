import DivineProportions.Plane.CyclicReflection
import DivineProportions.Trigonometry.SpreadPolynomial
import DivineProportions.Trigonometry.VertexBisector

/-!
# Divine Proportions, Theorem 58: finite reflection chains

The book writes a two-sided infinite reflection sequence.  The constructive
content needed by Theorem 58 is instead an executable finite iterator: after
`n` calls it contains exactly the adjacent pair `(lₙ,lₙ₊₁)`.  No completed
sequence is defined or quantified over.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

namespace ReflectionPair

/-- The spread of the adjacent pair carried by a state. -/
def adjacentSpread (state : ReflectionPair K) : K :=
  spread state.previous state.current state.previousNonNull state.currentNonNull

/-- One reflection step preserves the adjacent spread. -/
theorem adjacentSpread_step [DecidableEq K] (state : ReflectionPair K) :
    state.step.adjacentSpread = state.adjacentSpread := by
  unfold adjacentSpread step
  calc
    spread state.current
        (reflectLine state.current state.previous state.currentNonNull)
        state.currentNonNull
        (reflectLine_nonNull state.current state.previous
          state.currentNonNull state.previousNonNull) =
      spread (reflectLine state.current state.previous state.currentNonNull)
        state.current
        (reflectLine_nonNull state.current state.previous
          state.currentNonNull state.previousNonNull)
        state.currentNonNull :=
      spread_symm _ _ _ _
    _ = spread state.previous state.current state.previousNonNull
        state.currentNonNull :=
      spread_reflectLine_mirror state.current state.previous
        state.currentNonNull state.previousNonNull

end ReflectionPair

/-- Every adjacent pair in the finite chain has the initial spread. -/
theorem reflectionLineAt_adjacent_spread [DecidableEq K]
    (initial : ReflectionPair K) (index : Nat) :
    spread (reflectionLineAt initial index)
        (reflectionLineAt initial (index + 1))
        (reflectionLineAt_nonNull initial index)
        (reflectionLineAt_nonNull initial (index + 1)) =
      initial.adjacentSpread := by
  induction index with
  | zero => rfl
  | succ index inductionHypothesis =>
      calc
        spread (reflectionLineAt initial (Nat.succ index))
            (reflectionLineAt initial (Nat.succ index + 1))
            (reflectionLineAt_nonNull initial (Nat.succ index))
            (reflectionLineAt_nonNull initial (Nat.succ index + 1)) =
          (reflectionPairAt initial index).step.adjacentSpread := by
            rfl
        _ = (reflectionPairAt initial index).adjacentSpread :=
          ReflectionPair.adjacentSpread_step _
        _ = initial.adjacentSpread := by
          simpa only [ReflectionPair.adjacentSpread, reflectionLineAt,
            reflectionPairAt, ReflectionPair.step] using inductionHypothesis

/-- A finite quadratic-root lemma used in the induction for Theorem 58. -/
private theorem spreadTriple_recursive_alternatives [DecidableEq K]
    (previous current step next candidate : K)
    (previousTriple : SpreadTriple previous step current)
    (candidateTriple : SpreadTriple current step candidate)
    (sumEquation :
      previous + next = 2 * (current + step - 2 * current * step)) :
    candidate = previous ∨ candidate = next := by
  have nextResolved :
      next = 2 * (current + step - 2 * current * step) - previous := by
    calc
      next = previous + next - previous := by ring1
      _ = 2 * (current + step - 2 * current * step) - previous := by
        rw [sumEquation]
  have productZero : (candidate - previous) * (candidate - next) = 0 := by
    rw [nextResolved]
    calc
      (candidate - previous) *
          (candidate -
            (2 * (current + step - 2 * current * step) - previous)) =
        -tripleSpreadFunction current step candidate +
          tripleSpreadFunction previous step current := by
            unfold tripleSpreadFunction
            ring1
      _ = 0 := by
        unfold SpreadTriple at previousTriple candidateTriple
        rw [previousTriple, candidateTriple]
        ring1
  by_cases firstFactorZero : candidate - previous = 0
  · left
    exact sub_eq_zero.mp firstFactorZero
  · right
    have secondFactorZero : candidate - next = 0 := by
      by_cases factorZero : candidate - next = 0
      · exact factorZero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero firstFactorZero factorZero)
            productZero)
    exact sub_eq_zero.mp secondFactorZero

/-- The consecutive-spread identity at one displayed index.  The index is an
explicit argument so the simultaneous induction never needs equality of
proposition-valued functions. -/
private def consecutiveSpreadFormulaAt [DecidableEq K]
    (initial : ReflectionPair K) (currentIndex : Nat) : Prop :=
  spread initial.previous (reflectionLineAt initial currentIndex)
      initial.previousNonNull
      (reflectionLineAt_nonNull initial currentIndex) =
    spreadPolynomial currentIndex initial.adjacentSpread

/-- Theorem 58 (Consecutive spreads), stated for the executable finite
reflection iterator.  Requesting index `n` constructs only the first `n`
reflection steps. -/
theorem consecutive_spreads [DecidableEq K]
    (initial : ReflectionPair K)
    (notParallel : ¬ initial.previous.Parallel initial.current)
    (twoNonzero : (2 : K) ≠ 0)
    (index : Nat) :
    spread initial.previous (reflectionLineAt initial index)
        initial.previousNonNull (reflectionLineAt_nonNull initial index) =
      spreadPolynomial index initial.adjacentSpread := by
  have allPairs : ∀ currentIndex : Nat,
      consecutiveSpreadFormulaAt initial currentIndex ∧
        consecutiveSpreadFormulaAt initial (currentIndex + 1) := by
    intro currentIndex
    induction currentIndex with
    | zero =>
        constructor
        · unfold consecutiveSpreadFormulaAt
          change spread initial.previous initial.previous
              initial.previousNonNull initial.previousNonNull = 0
          exact (spread_eq_zero_iff_parallel initial.previous initial.previous
            initial.previousNonNull initial.previousNonNull).2 (by
              unfold Line.Parallel
              ring1)
        · unfold consecutiveSpreadFormulaAt
          change initial.adjacentSpread =
            spreadPolynomial 1 initial.adjacentSpread
          rw [spreadPolynomial_one]
    | succ currentIndex inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · change consecutiveSpreadFormulaAt initial
            (Nat.succ currentIndex + 1)
          have previousValue :
              spread initial.previous
                  (reflectionLineAt initial currentIndex)
                  initial.previousNonNull
                  (reflectionLineAt_nonNull initial currentIndex) =
                spreadPolynomial currentIndex initial.adjacentSpread :=
            inductionHypothesis.1
          have currentValue :
              spread initial.previous
                  (reflectionLineAt initial (currentIndex + 1))
                  initial.previousNonNull
                  (reflectionLineAt_nonNull initial (currentIndex + 1)) =
                spreadPolynomial (currentIndex + 1)
                  initial.adjacentSpread :=
            inductionHypothesis.2
          let previous := reflectionLineAt initial currentIndex
          let current := reflectionLineAt initial (currentIndex + 1)
          let next := reflectionLineAt initial (currentIndex + 2)
          let candidate := spread initial.previous next
            initial.previousNonNull
            (reflectionLineAt_nonNull initial (currentIndex + 2))
          let currentSpread := spread initial.previous current
            initial.previousNonNull
            (reflectionLineAt_nonNull initial (currentIndex + 1))
          have adjacentPrevious :
              spread previous current
                  (reflectionLineAt_nonNull initial currentIndex)
                  (reflectionLineAt_nonNull initial (currentIndex + 1)) =
                initial.adjacentSpread := by
            exact reflectionLineAt_adjacent_spread initial currentIndex
          have adjacentNext :
              spread current next
                  (reflectionLineAt_nonNull initial (currentIndex + 1))
                  (reflectionLineAt_nonNull initial (currentIndex + 2)) =
                initial.adjacentSpread := by
            exact reflectionLineAt_adjacent_spread initial (currentIndex + 1)
          have adjacentNotParallel : ¬ previous.Parallel current := by
            intro parallel
            have adjacentZero :
                spread previous current
                    (reflectionLineAt_nonNull initial currentIndex)
                    (reflectionLineAt_nonNull initial (currentIndex + 1)) = 0 :=
              (spread_eq_zero_iff_parallel previous current
                (reflectionLineAt_nonNull initial currentIndex)
                (reflectionLineAt_nonNull initial (currentIndex + 1))).2 parallel
            have initialZero : initial.adjacentSpread = 0 := by
              calc
                initial.adjacentSpread =
                    spread previous current
                      (reflectionLineAt_nonNull initial currentIndex)
                      (reflectionLineAt_nonNull initial
                        (currentIndex + 1)) := adjacentPrevious.symm
                _ = 0 := adjacentZero
            apply notParallel
            exact (spread_eq_zero_iff_parallel initial.previous initial.current
              initial.previousNonNull initial.currentNonNull).1 initialZero
          have rawCandidateTriple := three_lines_form_spreadTriple
            initial.previous current next initial.previousNonNull
            (reflectionLineAt_nonNull initial (currentIndex + 1))
            (reflectionLineAt_nonNull initial (currentIndex + 2))
          have candidateTriple :
              SpreadTriple currentSpread initial.adjacentSpread candidate := by
            unfold currentSpread candidate
            unfold SpreadTriple tripleSpreadFunction at rawCandidateTriple ⊢
            calc
              (spread initial.previous current initial.previousNonNull
                    (reflectionLineAt_nonNull initial (currentIndex + 1)) +
                  initial.adjacentSpread +
                  spread initial.previous next initial.previousNonNull
                    (reflectionLineAt_nonNull initial
                      (currentIndex + 2))) ^ 2 -
                    2 *
                      ((spread initial.previous current
                          initial.previousNonNull
                          (reflectionLineAt_nonNull initial
                            (currentIndex + 1))) ^ 2 +
                        initial.adjacentSpread ^ 2 +
                        (spread initial.previous next
                          initial.previousNonNull
                          (reflectionLineAt_nonNull initial
                            (currentIndex + 2))) ^ 2) -
                    4 *
                      spread initial.previous current initial.previousNonNull
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 1)) *
                      initial.adjacentSpread *
                      spread initial.previous next initial.previousNonNull
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 2)) =
                (spread current next
                      (reflectionLineAt_nonNull initial (currentIndex + 1))
                      (reflectionLineAt_nonNull initial (currentIndex + 2)) +
                    spread initial.previous next initial.previousNonNull
                      (reflectionLineAt_nonNull initial
                        (currentIndex + 2)) +
                    spread initial.previous current initial.previousNonNull
                      (reflectionLineAt_nonNull initial
                        (currentIndex + 1))) ^ 2 -
                  2 *
                    ((spread current next
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 1))
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 2))) ^ 2 +
                      (spread initial.previous next initial.previousNonNull
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 2))) ^ 2 +
                      (spread initial.previous current initial.previousNonNull
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 1))) ^ 2) -
                  4 *
                    spread current next
                      (reflectionLineAt_nonNull initial (currentIndex + 1))
                      (reflectionLineAt_nonNull initial (currentIndex + 2)) *
                    spread initial.previous next initial.previousNonNull
                      (reflectionLineAt_nonNull initial
                        (currentIndex + 2)) *
                    spread initial.previous current initial.previousNonNull
                      (reflectionLineAt_nonNull initial
                        (currentIndex + 1)) := by
                          rw [adjacentNext]
                          ring1
              _ = 0 := rawCandidateTriple
          have currentValueNamed :
              currentSpread = spreadPolynomial (currentIndex + 1)
                initial.adjacentSpread := by
            exact currentValue
          have candidatePolynomialTriple :
              SpreadTriple
                (spreadPolynomial (currentIndex + 1)
                  initial.adjacentSpread)
                initial.adjacentSpread candidate := by
            rw [← currentValueNamed]
            exact candidateTriple
          have sumEquation :
              spreadPolynomial currentIndex initial.adjacentSpread +
                  spreadPolynomial (currentIndex + 2)
                    initial.adjacentSpread =
                2 *
                  (spreadPolynomial (currentIndex + 1)
                      initial.adjacentSpread +
                    initial.adjacentSpread -
                    2 * spreadPolynomial (currentIndex + 1)
                      initial.adjacentSpread * initial.adjacentSpread) := by
            rw [spreadPolynomial_succ_succ]
            ring1
          have alternatives :
              candidate = spreadPolynomial currentIndex
                  initial.adjacentSpread ∨
                candidate = spreadPolynomial (currentIndex + 2)
                  initial.adjacentSpread :=
            spreadTriple_recursive_alternatives
              (spreadPolynomial currentIndex initial.adjacentSpread)
              (spreadPolynomial (currentIndex + 1)
                initial.adjacentSpread)
              initial.adjacentSpread
              (spreadPolynomial (currentIndex + 2)
                initial.adjacentSpread)
              candidate
              (recursive_spreads currentIndex initial.adjacentSpread)
              candidatePolynomialTriple sumEquation
          have expectedTriple :
              SpreadTriple currentSpread initial.adjacentSpread
                (spreadPolynomial (currentIndex + 2)
                  initial.adjacentSpread) := by
            rw [currentValueNamed]
            simpa only [show currentIndex + 2 =
              (currentIndex + 1) + 1 by rfl] using
                (recursive_spreads (currentIndex + 1)
                  initial.adjacentSpread)
          have candidateEqualsExpectedOfSpecial
              (special : currentSpread = 0 ∨ currentSpread = 1) :
              candidate = spreadPolynomial (currentIndex + 2)
                initial.adjacentSpread := by
            rcases special with currentZero | currentOne
            · have candidateAtZero := candidateTriple
              rw [currentZero] at candidateAtZero
              have candidateEqualsStep : candidate = initial.adjacentSpread :=
                (spreadTriple_zero_iff candidate initial.adjacentSpread).1
                  (spreadTriple_swap_first_third candidateAtZero)
              have expectedAtZero := expectedTriple
              rw [currentZero] at expectedAtZero
              have expectedEqualsStep :
                  spreadPolynomial (currentIndex + 2)
                      initial.adjacentSpread = initial.adjacentSpread :=
                (spreadTriple_zero_iff
                  (spreadPolynomial (currentIndex + 2)
                    initial.adjacentSpread)
                  initial.adjacentSpread).1
                    (spreadTriple_swap_first_third expectedAtZero)
              exact candidateEqualsStep.trans expectedEqualsStep.symm
            · have candidateAtOne := candidateTriple
              rw [currentOne] at candidateAtOne
              have candidateSum :
                  candidate + initial.adjacentSpread = 1 :=
                (spreadTriple_one_iff candidate initial.adjacentSpread).1
                  (spreadTriple_swap_first_third candidateAtOne)
              have expectedAtOne := expectedTriple
              rw [currentOne] at expectedAtOne
              have expectedSum :
                  spreadPolynomial (currentIndex + 2)
                      initial.adjacentSpread + initial.adjacentSpread = 1 :=
                (spreadTriple_one_iff
                  (spreadPolynomial (currentIndex + 2)
                    initial.adjacentSpread)
                  initial.adjacentSpread).1
                    (spreadTriple_swap_first_third expectedAtOne)
              calc
                candidate =
                    (candidate + initial.adjacentSpread) -
                      initial.adjacentSpread := by ring1
                _ = 1 - initial.adjacentSpread := by rw [candidateSum]
                _ = (spreadPolynomial (currentIndex + 2)
                      initial.adjacentSpread + initial.adjacentSpread) -
                    initial.adjacentSpread := by rw [expectedSum]
                _ = spreadPolynomial (currentIndex + 2)
                    initial.adjacentSpread := by ring1
          have candidateEqualsExpected :
              candidate = spreadPolynomial (currentIndex + 2)
                initial.adjacentSpread := by
            rcases alternatives with candidatePrevious | candidateExpected
            · have previousCandidateEqual :
                  spread initial.previous previous initial.previousNonNull
                      (reflectionLineAt_nonNull initial currentIndex) =
                    candidate := by
                calc
                  spread initial.previous previous initial.previousNonNull
                        (reflectionLineAt_nonNull initial currentIndex) =
                      spreadPolynomial currentIndex initial.adjacentSpread :=
                    previousValue
                  _ = candidate := candidatePrevious.symm
              by_cases previousNextDeterminantZero :
                  previous.a * next.b - next.a * previous.b = 0
              · have previousNextParallel : previous.Parallel next :=
                  previousNextDeterminantZero
                have fixedDirection :
                    previous.Parallel
                      (reflectLine current previous
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 1))) := by
                  rw [← reflectionLineAt_succ_succ initial currentIndex]
                  exact previousNextParallel
                rcases parallel_or_perpendicular_of_parallel_reflectLine
                    current previous
                    (reflectionLineAt_nonNull initial (currentIndex + 1))
                    twoNonzero fixedDirection with
                  previousCurrentParallel | previousCurrentPerpendicular
                · exact False.elim
                    (adjacentNotParallel previousCurrentParallel)
                · have stepOne : initial.adjacentSpread = 1 := by
                    calc
                      initial.adjacentSpread =
                          spread previous current
                          (reflectionLineAt_nonNull initial currentIndex)
                          (reflectionLineAt_nonNull initial
                            (currentIndex + 1)) := adjacentPrevious.symm
                      _ = 1 := spread_eq_one_of_perpendicular previous current
                        (reflectionLineAt_nonNull initial currentIndex)
                        (reflectionLineAt_nonNull initial (currentIndex + 1))
                        previousCurrentPerpendicular
                  have candidateAtStepOne := candidateTriple
                  rw [stepOne] at candidateAtStepOne
                  have candidateSum : candidate + currentSpread = 1 :=
                    (spreadTriple_one_iff candidate currentSpread).1
                      (spreadTriple_rotate
                        (spreadTriple_rotate candidateAtStepOne))
                  have expectedAtStepOne := expectedTriple
                  rw [stepOne] at expectedAtStepOne
                  have expectedSumAtOne :
                      spreadPolynomial (currentIndex + 2) 1 +
                          currentSpread = 1 :=
                    (spreadTriple_one_iff
                      (spreadPolynomial (currentIndex + 2)
                        1) currentSpread).1
                        (spreadTriple_rotate
                          (spreadTriple_rotate expectedAtStepOne))
                  have expectedSum :
                      spreadPolynomial (currentIndex + 2)
                          initial.adjacentSpread + currentSpread = 1 := by
                    rw [stepOne]
                    exact expectedSumAtOne
                  calc
                    candidate = candidate + currentSpread - currentSpread := by
                      ring1
                    _ = 1 - currentSpread := by rw [candidateSum]
                    _ = spreadPolynomial (currentIndex + 2)
                          initial.adjacentSpread + currentSpread -
                        currentSpread := by rw [expectedSum]
                    _ = spreadPolynomial (currentIndex + 2)
                        initial.adjacentSpread := by ring1
              · have previousNextNotParallel : ¬ previous.Parallel next :=
                  previousNextDeterminantZero
                have leftEqual :
                    spread previous initial.previous
                        (reflectionLineAt_nonNull initial currentIndex)
                        initial.previousNonNull =
                      spread next initial.previous
                        (reflectionLineAt_nonNull initial (currentIndex + 2))
                        initial.previousNonNull := by
                  calc
                    spread previous initial.previous
                        (reflectionLineAt_nonNull initial currentIndex)
                        initial.previousNonNull =
                      spread initial.previous previous initial.previousNonNull
                        (reflectionLineAt_nonNull initial currentIndex) :=
                      spread_symm _ _ _ _
                    _ = candidate := previousCandidateEqual
                    _ = spread initial.previous next initial.previousNonNull
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 2)) := rfl
                    _ = spread next initial.previous
                        (reflectionLineAt_nonNull initial (currentIndex + 2))
                        initial.previousNonNull :=
                      (spread_symm _ _ _ _).symm
                have rightEqual :
                    spread previous current
                        (reflectionLineAt_nonNull initial currentIndex)
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 1)) =
                      spread next current
                        (reflectionLineAt_nonNull initial (currentIndex + 2))
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 1)) := by
                  calc
                    spread previous current
                        (reflectionLineAt_nonNull initial currentIndex)
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 1)) = initial.adjacentSpread :=
                      adjacentPrevious
                    _ = spread current next
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 1))
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 2)) := adjacentNext.symm
                    _ = spread next current
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 2))
                        (reflectionLineAt_nonNull initial
                          (currentIndex + 1)) :=
                      (spread_symm _ _ _ _).symm
                rcases equal_spread_lines_parallel_or_perpendicular
                    previous next initial.previous current
                    (reflectionLineAt_nonNull initial currentIndex)
                    (reflectionLineAt_nonNull initial (currentIndex + 2))
                    initial.previousNonNull
                    (reflectionLineAt_nonNull initial (currentIndex + 1))
                    previousNextNotParallel twoNonzero leftEqual rightEqual with
                  initialCurrentParallel | initialCurrentPerpendicular
                · have currentZero : currentSpread = 0 := by
                    exact (spread_eq_zero_iff_parallel initial.previous current
                      initial.previousNonNull
                      (reflectionLineAt_nonNull initial
                        (currentIndex + 1))).2 initialCurrentParallel
                  exact candidateEqualsExpectedOfSpecial (Or.inl currentZero)
                · have currentOne : currentSpread = 1 :=
                    spread_eq_one_of_perpendicular initial.previous current
                      initial.previousNonNull
                      (reflectionLineAt_nonNull initial (currentIndex + 1))
                      initialCurrentPerpendicular
                  exact candidateEqualsExpectedOfSpecial (Or.inr currentOne)
            · exact candidateExpected
          unfold consecutiveSpreadFormulaAt
          rw [show Nat.succ currentIndex + 1 = currentIndex + 2 by rfl]
          exact candidateEqualsExpected
  exact (allPairs index).1

end DivineProportions
