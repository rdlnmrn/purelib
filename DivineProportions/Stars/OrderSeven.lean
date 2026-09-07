import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Stars.OrderFive

/-!
# Divine Proportions, Theorem 97: regular stars of order seven

Only the seven required lines are quantified over, through `Fin 7`.  Their
coefficients are obtained by the executable finite reflection iterator; the
two closing equations record exactly the wraparound needed for the cyclic
star.  No completed two-sided reflection sequence is introduced.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- A regular order-seven star represented by one finite reflection orbit.
Pairwise nonparallelism ranges over the finite type `Fin 7`, and the two
closing representatives make the recurrence cyclic. -/
structure RegularSevenStar (K : Type*) [RFAP.ExplicitField K]
    [DecidableEq K] where
  initial : ReflectionPair K
  pairwiseNonparallel :
    ∀ first second : Fin 7, first ≠ second →
      ¬ (reflectionLineAt initial first.val).Parallel
        (reflectionLineAt initial second.val)
  closesAtSeven :
    (reflectionLineAt initial 7).Equivalent initial.previous
  closesAtEight :
    (reflectionLineAt initial 8).Equivalent initial.current

/-- The scalar conditions printed in Theorem 97. -/
def OrderSevenStarParameters : Prop :=
  ∃ value : K, value ≠ 0 ∧
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 = 0 ∧
    IsSquare (value * (1 - value))

/-- The explicit factorization
`S₇(s)=s(7-56s+112s²-64s³)²`. -/
theorem spreadPolynomial_seven_formula (value : K) :
    spreadPolynomial 7 value =
      value *
        (7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3) ^ 2 := by
  simp only [spreadPolynomial]
  ring1

private theorem spreadPolynomial_two_formula (value : K) :
    spreadPolynomial 2 value = 4 * value * (1 - value) := by
  simp only [spreadPolynomial]
  ring1

private theorem spreadPolynomial_three_formula (value : K) :
    spreadPolynomial 3 value = value * (3 - 4 * value) ^ 2 := by
  simp only [spreadPolynomial]
  ring1

private theorem spreadPolynomial_four_formula (value : K) :
    spreadPolynomial 4 value =
      16 * value * (1 - value) * (1 - 2 * value) ^ 2 := by
  simp only [spreadPolynomial]
  ring1

private theorem spreadPolynomial_six_formula (value : K) :
    spreadPolynomial 6 value =
      4 * value * (1 - value) *
        (3 - 16 * value + 16 * value ^ 2) ^ 2 := by
  simp only [spreadPolynomial]
  ring1

private theorem square_ne_zero {value : K} (valueNonzero : value ≠ 0) :
    value ^ 2 ≠ 0 := by
  simpa [pow_two] using
    RFAP.ExplicitField.mul_ne_zero valueNonzero valueNonzero

/-- An explicitly bounded positive natural below seven is one of the six
displayed possibilities. -/
private theorem index_eq_one_through_six
    (index : Nat) (positive : 1 ≤ index) (below : index < 7) :
    index = 1 ∨ index = 2 ∨ index = 3 ∨
      index = 4 ∨ index = 5 ∨ index = 6 := by
  cases index with
  | zero => exact False.elim (Nat.not_succ_le_zero 0 positive)
  | succ index =>
      cases index with
      | zero => exact Or.inl rfl
      | succ index =>
          cases index with
          | zero => exact Or.inr (Or.inl rfl)
          | succ index =>
              cases index with
              | zero => exact Or.inr (Or.inr (Or.inl rfl))
              | succ index =>
                  cases index with
                  | zero => exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
                  | succ index =>
                      cases index with
                      | zero =>
                          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
                      | succ index =>
                          cases index with
                          | zero =>
                              exact Or.inr (Or.inr (Or.inr
                                (Or.inr (Or.inr rfl))))
                          | succ index =>
                              exact False.elim
                                ((Nat.not_lt_of_ge
                                  (Nat.le_add_left 7 index)) below)

/-- The cubic factor for seven is coprime, by five explicit Bezout
identities, to every additional factor occurring in `S₁,...,S₆`. -/
private theorem spreadPolynomial_nonzero_before_seven [Nontrivial K]
    (value : K) (valueNonzero : value ≠ 0)
    (cubicZero :
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 = 0)
    (twoNonzero : (2 : K) ≠ 0) (index : Nat)
    (indexPositive : 1 ≤ index) (indexBelowSeven : index < 7) :
    spreadPolynomial index value ≠ 0 := by
  let cubic :=
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3
  have cubicIsZero : cubic = 0 := cubicZero
  have oneMinusValueNonzero : (1 : K) - value ≠ 0 := by
    intro factorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = -cubic +
          (8 - 48 * value + 64 * value ^ 2) * (1 - value) := by
        unfold cubic
        ring1
      _ = 0 := by rw [cubicIsZero, factorZero]; ring1
  have threeMinusFourValueNonzero : (3 : K) - 4 * value ≠ 0 := by
    intro factorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = cubic +
          (-2 + 16 * value - 16 * value ^ 2) * (3 - 4 * value) := by
        unfold cubic
        ring1
      _ = 0 := by rw [cubicIsZero, factorZero]; ring1
  have oneMinusTwoValueNonzero : (1 : K) - 2 * value ≠ 0 := by
    intro factorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = -cubic +
          (8 - 40 * value + 32 * value ^ 2) * (1 - 2 * value) := by
        unfold cubic
        ring1
      _ = 0 := by rw [cubicIsZero, factorZero]; ring1
  have fiveFactorNonzero :
      (5 : K) - 20 * value + 16 * value ^ 2 ≠ 0 := by
    intro factorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = (-2 + 4 * value) * cubic +
          (3 - 16 * value + 16 * value ^ 2) *
            (5 - 20 * value + 16 * value ^ 2) := by
        unfold cubic
        ring1
      _ = 0 := by rw [cubicIsZero, factorZero]; ring1
  have sixFactorNonzero :
      (3 : K) - 16 * value + 16 * value ^ 2 ≠ 0 := by
    intro factorZero
    apply (one_ne_zero : (1 : K) ≠ 0)
    calc
      (1 : K) = (-2 + 4 * value) * cubic +
          (5 - 20 * value + 16 * value ^ 2) *
            (3 - 16 * value + 16 * value ^ 2) := by
        unfold cubic
        ring1
      _ = 0 := by rw [cubicIsZero, factorZero]; ring1
  have fourNonzero : (4 : K) ≠ 0 := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have sixteenNonzero : (16 : K) ≠ 0 := by
    have sixteenAsProduct : (16 : K) = 4 * 4 := by ring1
    rw [sixteenAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero fourNonzero fourNonzero
  have spreadOneNonzero : spreadPolynomial 1 value ≠ 0 := by
    rw [spreadPolynomial_one]
    exact valueNonzero
  have spreadTwoNonzero : spreadPolynomial 2 value ≠ 0 := by
    rw [spreadPolynomial_two_formula]
    exact RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero fourNonzero valueNonzero)
      oneMinusValueNonzero
  have spreadThreeNonzero : spreadPolynomial 3 value ≠ 0 := by
    rw [spreadPolynomial_three_formula]
    exact RFAP.ExplicitField.mul_ne_zero valueNonzero
      (square_ne_zero threeMinusFourValueNonzero)
  have spreadFourNonzero : spreadPolynomial 4 value ≠ 0 := by
    rw [spreadPolynomial_four_formula]
    exact RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero sixteenNonzero valueNonzero)
        oneMinusValueNonzero)
      (square_ne_zero oneMinusTwoValueNonzero)
  have spreadFiveNonzero : spreadPolynomial 5 value ≠ 0 := by
    rw [spreadPolynomial_five_formula]
    exact RFAP.ExplicitField.mul_ne_zero valueNonzero
      (square_ne_zero fiveFactorNonzero)
  have spreadSixNonzero : spreadPolynomial 6 value ≠ 0 := by
    rw [spreadPolynomial_six_formula]
    exact RFAP.ExplicitField.mul_ne_zero
      (RFAP.ExplicitField.mul_ne_zero
        (RFAP.ExplicitField.mul_ne_zero fourNonzero valueNonzero)
        oneMinusValueNonzero)
      (square_ne_zero sixFactorNonzero)
  have possibilities :
      index = 1 ∨ index = 2 ∨ index = 3 ∨
        index = 4 ∨ index = 5 ∨ index = 6 :=
    index_eq_one_through_six index indexPositive indexBelowSeven
  rcases possibilities with first | second | third | fourth | fifth | sixth
  · subst index
    exact spreadOneNonzero
  · subst index
    exact spreadTwoNonzero
  · subst index
    exact spreadThreeNonzero
  · subst index
    exact spreadFourNonzero
  · subst index
    exact spreadFiveNonzero
  · subst index
    exact spreadSixNonzero

/-- Pairwise nonparallelism of the first seven iterates follows from the six
nonzero lower spread polynomials. -/
private theorem reflectionLineAt_pairwise_nonparallel_before_seven
    [Nontrivial K] [DecidableEq K]
    (initial : ReflectionPair K) (adjacentNonzero : initial.adjacentSpread ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (lowerNonzero : ∀ index : Nat, 1 ≤ index → index < 7 →
      spreadPolynomial index initial.adjacentSpread ≠ 0)
    (first second : Fin 7) (different : first ≠ second) :
    ¬ (reflectionLineAt initial first.val).Parallel
      (reflectionLineAt initial second.val) := by
  have valuesDifferent : first.val ≠ second.val := by
    intro equal
    exact different (Fin.ext equal)
  have ordered : ∀ left right : Fin 7, left.val < right.val →
      ¬ (reflectionLineAt initial left.val).Parallel
        (reflectionLineAt initial right.val) := by
    intro left right leftLessRight parallel
    let offset := right.val - left.val
    have offsetPositive : 1 ≤ offset :=
      Nat.sub_pos_of_lt leftLessRight
    have offsetBelowSeven : offset < 7 :=
      (Nat.sub_le right.val left.val).trans_lt right.isLt
    let shifted := reflectionPairAt initial left.val
    have shiftedSpread : shifted.adjacentSpread = initial.adjacentSpread := by
      unfold shifted ReflectionPair.adjacentSpread
      exact reflectionLineAt_adjacent_spread initial left.val
    have shiftedNotParallel : ¬ shifted.previous.Parallel shifted.current := by
      intro adjacentParallel
      apply adjacentNonzero
      calc
        initial.adjacentSpread = shifted.adjacentSpread := shiftedSpread.symm
        _ = 0 := (spread_eq_zero_iff_parallel shifted.previous shifted.current
          shifted.previousNonNull shifted.currentNonNull).2 adjacentParallel
    have formula := consecutive_spreads shifted shiftedNotParallel
      twoNonzero offset
    have indexSum : left.val + offset = right.val :=
      Nat.add_sub_of_le leftLessRight.le
    rw [shiftedSpread] at formula
    unfold shifted at formula
    have formulaAtIndices :
        spread (reflectionLineAt initial left.val)
            (reflectionLineAt initial right.val)
            (reflectionLineAt_nonNull initial left.val)
            (reflectionLineAt_nonNull initial right.val) =
          spreadPolynomial offset initial.adjacentSpread := by
      simpa only [reflectionLineAt, ← reflectionPairAt_add, indexSum]
        using formula
    have spreadZero :
        spread (reflectionLineAt initial left.val)
            (reflectionLineAt initial right.val)
            (reflectionLineAt_nonNull initial left.val)
            (reflectionLineAt_nonNull initial right.val) = 0 :=
      (spread_eq_zero_iff_parallel
        (reflectionLineAt initial left.val)
        (reflectionLineAt initial right.val)
        (reflectionLineAt_nonNull initial left.val)
        (reflectionLineAt_nonNull initial right.val)).2 parallel
    apply lowerNonzero offset offsetPositive offsetBelowSeven
    calc
      spreadPolynomial offset initial.adjacentSpread =
          spread (reflectionLineAt initial left.val)
            (reflectionLineAt initial right.val)
            (reflectionLineAt_nonNull initial left.val)
            (reflectionLineAt_nonNull initial right.val) :=
        formulaAtIndices.symm
      _ = 0 := spreadZero
  rcases Nat.lt_or_gt_of_ne valuesDifferent with firstLess | secondLess
  · exact ordered first second firstLess
  · intro parallel
    exact ordered second first secondLess (Line.parallel_symm parallel)

/-- A zero seventh spread closes any finite reflection orbit whose first two
lines pass through a common point. -/
private theorem reflectionLineAt_closes_at_seven [Nontrivial K]
    [DecidableEq K] (initial : ReflectionPair K) (point : Point K)
    (previousContains : initial.previous.Contains point)
    (currentContains : initial.current.Contains point)
    (adjacentNonzero : initial.adjacentSpread ≠ 0)
    (twoNonzero : (2 : K) ≠ 0)
    (seventhZero : spreadPolynomial 7 initial.adjacentSpread = 0)
    (start : Nat) :
    (reflectionLineAt initial (start + 7)).Equivalent
      (reflectionLineAt initial start) := by
  let shifted := reflectionPairAt initial start
  have shiftedSpread : shifted.adjacentSpread = initial.adjacentSpread := by
    unfold shifted ReflectionPair.adjacentSpread
    exact reflectionLineAt_adjacent_spread initial start
  have shiftedNotParallel : ¬ shifted.previous.Parallel shifted.current := by
    intro adjacentParallel
    apply adjacentNonzero
    calc
      initial.adjacentSpread = shifted.adjacentSpread := shiftedSpread.symm
      _ = 0 := (spread_eq_zero_iff_parallel shifted.previous shifted.current
        shifted.previousNonNull shifted.currentNonNull).2 adjacentParallel
  have spreadSeven := consecutive_spreads shifted shiftedNotParallel
    twoNonzero 7
  rw [shiftedSpread, seventhZero] at spreadSeven
  have shiftedParallel :
      shifted.previous.Parallel (reflectionLineAt shifted 7) :=
    (spread_eq_zero_iff_parallel shifted.previous
      (reflectionLineAt shifted 7) shifted.previousNonNull
      (reflectionLineAt_nonNull shifted 7)).1 spreadSeven
  unfold shifted at shiftedParallel
  rw [reflectionLineAt_add initial start 7] at shiftedParallel
  apply line_equivalent_of_parallel_and_common_point
    (reflectionLineAt initial (start + 7))
    (reflectionLineAt initial start) point
  · exact Line.parallel_symm shiftedParallel
  · exact reflectionLineAt_contains initial point previousContains
      currentContains (start + 7)
  · exact reflectionLineAt_contains initial point previousContains
      currentContains start

/-- The line `⟨0:1:0⟩` used to start the converse construction. -/
def orderSevenLine₀ [Nontrivial K] : Line K where
  a := 0
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

/-- For a spread number `s` with root `v²=s(1-s)`, the line
`⟨s:v:0⟩` has spread `s` from `⟨0:1:0⟩`. -/
def orderSevenLine₁ [Nontrivial K] (value spreadRoot : K)
    (valueNonzero : value ≠ 0) : Line K where
  a := value
  b := spreadRoot
  c := 0
  direction_nonzero := Or.inl valueNonzero

/-- The executable initial pair for the order-seven converse. -/
def orderSevenInitialPair [Nontrivial K] (value spreadRoot : K)
    (valueNonzero : value ≠ 0)
    (spreadSquare : spreadRoot ^ 2 = value * (1 - value)) :
    ReflectionPair K where
  previous := orderSevenLine₀
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

theorem orderSevenInitialPair_adjacentSpread [Nontrivial K]
    [DecidableEq K] (value spreadRoot : K) (valueNonzero : value ≠ 0)
    (spreadSquare : spreadRoot ^ 2 = value * (1 - value)) :
    (orderSevenInitialPair value spreadRoot valueNonzero
      spreadSquare).adjacentSpread = value := by
  unfold ReflectionPair.adjacentSpread spread orderSevenInitialPair
    orderSevenLine₀ orderSevenLine₁ lineNorm
  rw [spreadSquare]
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  rw [show (0 ^ 2 + 1 ^ 2) *
      (value ^ 2 + value * (1 - value)) = value by ring1]
  calc
    (0 * spreadRoot - value * 1) ^ 2 * value⁻¹ =
        value ^ 2 * value⁻¹ := by ring1
    _ = value * (value * value⁻¹) := by ring1
    _ = value := by
      rw [RFAP.ExplicitField.mul_inv_cancel value valueNonzero]
      ring1

/-- The finite reflection construction in the converse of Theorem 97. -/
def orderSevenStar [Nontrivial K] [DecidableEq K]
    (value spreadRoot : K) (valueNonzero : value ≠ 0)
    (cubicZero :
      7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3 = 0)
    (spreadSquare : spreadRoot ^ 2 = value * (1 - value))
    (twoNonzero : (2 : K) ≠ 0) : RegularSevenStar K := by
  let initial := orderSevenInitialPair value spreadRoot valueNonzero
    spreadSquare
  have adjacentValue : initial.adjacentSpread = value := by
    exact orderSevenInitialPair_adjacentSpread value spreadRoot valueNonzero
      spreadSquare
  have adjacentNonzero : initial.adjacentSpread ≠ 0 := by
    rw [adjacentValue]
    exact valueNonzero
  have seventhZero : spreadPolynomial 7 initial.adjacentSpread = 0 := by
    rw [adjacentValue, spreadPolynomial_seven_formula, cubicZero]
    ring1
  let origin : Point K := ⟨0, 0⟩
  have previousContains : initial.previous.Contains origin := by
    unfold initial origin orderSevenInitialPair orderSevenLine₀ Line.Contains
    ring1
  have currentContains : initial.current.Contains origin := by
    unfold initial origin orderSevenInitialPair orderSevenLine₁ Line.Contains
    ring1
  exact
    { initial := initial
      pairwiseNonparallel := by
        intro first second different
        apply reflectionLineAt_pairwise_nonparallel_before_seven initial
          adjacentNonzero twoNonzero
        · intro index indexPositive indexBelowSeven
          rw [adjacentValue]
          exact spreadPolynomial_nonzero_before_seven value valueNonzero
            cubicZero twoNonzero index indexPositive indexBelowSeven
        · exact different
      closesAtSeven := by
        simpa only [Nat.zero_add, reflectionLineAt_zero] using
          reflectionLineAt_closes_at_seven initial origin previousContains
            currentContains adjacentNonzero twoNonzero seventhZero 0
      closesAtEight := by
        have closing := reflectionLineAt_closes_at_seven initial origin
          previousContains currentContains adjacentNonzero twoNonzero
          seventhZero 1
        rw [show 1 + 7 = 8 by decide] at closing
        simpa only [show reflectionLineAt initial 1 = initial.current by rfl]
          using closing }

/-- The necessary direction of Theorem 97. -/
theorem order_seven_star_parameters [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0)
    (star : RegularSevenStar K) : OrderSevenStarParameters (K := K) := by
  let value := star.initial.adjacentSpread
  have adjacentNonparallel :
      ¬ star.initial.previous.Parallel star.initial.current := by
    have firstSecond := star.pairwiseNonparallel
      (0 : Fin 7) (1 : Fin 7) (by decide)
    have zeroValue : (0 : Fin 7).val = 0 := rfl
    have oneValue : (1 : Fin 7).val = 1 := rfl
    rw [zeroValue, oneValue] at firstSecond
    simpa only [reflectionLineAt_zero,
      show reflectionLineAt star.initial 1 = star.initial.current by rfl]
      using firstSecond
  have valueNonzero : value ≠ 0 := by
    intro valueZero
    apply adjacentNonparallel
    exact (spread_eq_zero_iff_parallel star.initial.previous
      star.initial.current star.initial.previousNonNull
      star.initial.currentNonNull).1 valueZero
  have closingParallel :
      star.initial.previous.Parallel (reflectionLineAt star.initial 7) := by
    apply Line.parallel_symm
    exact line_parallel_of_equivalent star.closesAtSeven
  have closingSpreadZero :
      spread star.initial.previous (reflectionLineAt star.initial 7)
          star.initial.previousNonNull
          (reflectionLineAt_nonNull star.initial 7) = 0 :=
    (spread_eq_zero_iff_parallel star.initial.previous
      (reflectionLineAt star.initial 7) star.initial.previousNonNull
      (reflectionLineAt_nonNull star.initial 7)).2 closingParallel
  have polynomialValue := consecutive_spreads star.initial
    adjacentNonparallel twoNonzero 7
  have polynomialZero : spreadPolynomial 7 value = 0 := by
    calc
      spreadPolynomial 7 value =
          spread star.initial.previous (reflectionLineAt star.initial 7)
            star.initial.previousNonNull
            (reflectionLineAt_nonNull star.initial 7) := polynomialValue.symm
      _ = 0 := closingSpreadZero
  rw [spreadPolynomial_seven_formula] at polynomialZero
  let cubic :=
    7 - 56 * value + 112 * value ^ 2 - 64 * value ^ 3
  have cubicSquareZero : cubic ^ 2 = 0 := by
    by_cases zero : cubic ^ 2 = 0
    · exact zero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero valueNonzero zero) polynomialZero)
  have cubicZero : cubic = 0 := by
    by_cases zero : cubic = 0
    · exact zero
    · exact False.elim ((square_ne_zero zero) cubicSquareZero)
  rcases spread_isSpreadNumber star.initial.previous star.initial.current
      star.initial.previousNonNull star.initial.currentNonNull with
    ⟨spreadRoot, spreadSquare⟩
  exact ⟨value, valueNonzero, cubicZero, spreadRoot, spreadSquare⟩

/-- Theorem 97 (Order seven star): a regular seven-star exists exactly when
the printed cubic has a nonzero root `s` and `s(1-s)` is a square. -/
theorem order_seven_star [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (RegularSevenStar K) ↔ OrderSevenStarParameters (K := K) := by
  constructor
  · rintro ⟨star⟩
    exact order_seven_star_parameters twoNonzero star
  · rintro ⟨value, valueNonzero, cubicZero, spreadRoot, spreadSquare⟩
    exact ⟨orderSevenStar value spreadRoot valueNonzero cubicZero
      spreadSquare.symm twoNonzero⟩

end DivineProportions
