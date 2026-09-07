import mathlib.Tactic.QuotientFreeRing
import DivineProportions.Stars.OrderThree
import DivineProportions.Trigonometry.ConsecutiveSpreads

/-!
# Divine Proportions, Theorem 96: regular stars of order five

The five cyclic reflection equations and all ten nonparallel pairs are stored
as finite data.  The executable reflection iterator is then related to these
displayed representatives using quotient-free line congruence.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- A regular star of order five, with the cyclic indexing written out. -/
structure RegularFiveStar (K : Type*) [RFAP.ExplicitField K] [DecidableEq K] where
  line₀ : Line K
  line₁ : Line K
  line₂ : Line K
  line₃ : Line K
  line₄ : Line K
  line₀NonNull : ¬ line₀.IsNull
  line₁NonNull : ¬ line₁.IsNull
  line₂NonNull : ¬ line₂.IsNull
  line₃NonNull : ¬ line₃.IsNull
  line₄NonNull : ¬ line₄.IsNull
  line₀Line₁Nonparallel : ¬ line₀.Parallel line₁
  line₀Line₂Nonparallel : ¬ line₀.Parallel line₂
  line₀Line₃Nonparallel : ¬ line₀.Parallel line₃
  line₀Line₄Nonparallel : ¬ line₀.Parallel line₄
  line₁Line₂Nonparallel : ¬ line₁.Parallel line₂
  line₁Line₃Nonparallel : ¬ line₁.Parallel line₃
  line₁Line₄Nonparallel : ¬ line₁.Parallel line₄
  line₂Line₃Nonparallel : ¬ line₂.Parallel line₃
  line₂Line₄Nonparallel : ¬ line₂.Parallel line₄
  line₃Line₄Nonparallel : ¬ line₃.Parallel line₄
  reflectAround₀ :
    (reflectLine line₀ line₄ line₀NonNull).Equivalent line₁
  reflectAround₁ :
    (reflectLine line₁ line₀ line₁NonNull).Equivalent line₂
  reflectAround₂ :
    (reflectLine line₂ line₁ line₂NonNull).Equivalent line₃
  reflectAround₃ :
    (reflectLine line₃ line₂ line₃NonNull).Equivalent line₄
  reflectAround₄ :
    (reflectLine line₄ line₃ line₄NonNull).Equivalent line₀

namespace RegularFiveStar

variable [DecidableEq K]

/-- The initial adjacent pair for the finite reflection iterator. -/
def initialPair (star : RegularFiveStar K) : ReflectionPair K where
  previous := star.line₀
  current := star.line₁
  previousNonNull := star.line₀NonNull
  currentNonNull := star.line₁NonNull

theorem lineAtTwo_equivalent (star : RegularFiveStar K) :
    (reflectionLineAt star.initialPair 2).Equivalent star.line₂ := by
  rw [show (2 : Nat) = 0 + 2 by decide,
    reflectionLineAt_succ_succ star.initialPair 0]
  exact star.reflectAround₁

theorem lineAtThree_equivalent (star : RegularFiveStar K) :
    (reflectionLineAt star.initialPair 3).Equivalent star.line₃ := by
  rw [show (3 : Nat) = 1 + 2 by decide,
    reflectionLineAt_succ_succ star.initialPair 1]
  have congruent := reflectLine_equivalent_of_equivalent
    (reflectionLineAt star.initialPair 2) star.line₂
    (reflectionLineAt star.initialPair 1) star.line₁
    (reflectionLineAt_nonNull star.initialPair 2) star.line₂NonNull
    star.lineAtTwo_equivalent (Line.equivalent_refl star.line₁)
  exact line_equivalent_trans congruent star.reflectAround₂

theorem lineAtFour_equivalent (star : RegularFiveStar K) :
    (reflectionLineAt star.initialPair 4).Equivalent star.line₄ := by
  rw [show (4 : Nat) = 2 + 2 by decide,
    reflectionLineAt_succ_succ star.initialPair 2]
  have congruent := reflectLine_equivalent_of_equivalent
    (reflectionLineAt star.initialPair 3) star.line₃
    (reflectionLineAt star.initialPair 2) star.line₂
    (reflectionLineAt_nonNull star.initialPair 3) star.line₃NonNull
    star.lineAtThree_equivalent star.lineAtTwo_equivalent
  exact line_equivalent_trans congruent star.reflectAround₃

theorem lineAtFive_equivalent (star : RegularFiveStar K) :
    (reflectionLineAt star.initialPair 5).Equivalent star.line₀ := by
  rw [show (5 : Nat) = 3 + 2 by decide,
    reflectionLineAt_succ_succ star.initialPair 3]
  have congruent := reflectLine_equivalent_of_equivalent
    (reflectionLineAt star.initialPair 4) star.line₄
    (reflectionLineAt star.initialPair 3) star.line₃
    (reflectionLineAt_nonNull star.initialPair 4) star.line₄NonNull
    star.lineAtFour_equivalent star.lineAtThree_equivalent
  exact line_equivalent_trans congruent star.reflectAround₄

end RegularFiveStar

/-- The explicit factorization `S₅(s)=s(5-20s+16s²)²`. -/
theorem spreadPolynomial_five_formula (value : K) :
    spreadPolynomial 5 value = value * (5 - 20 * value + 16 * value ^ 2) ^ 2 := by
  simp only [spreadPolynomial]
  ring1

private theorem eight_ne_zero (twoNonzero : (2 : K) ≠ 0) : (8 : K) ≠ 0 := by
  have eightAsProduct : (8 : K) = 2 * 2 * 2 := by ring1
  rw [eightAsProduct]
  exact RFAP.ExplicitField.mul_ne_zero
    (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero) twoNonzero

private theorem square_zero_implies_zero [DecidableEq K] (value : K)
    (squareZero : value ^ 2 = 0) : value = 0 := by
  by_cases valueZero : value = 0
  · exact valueZero
  · have squareNonzero : value ^ 2 ≠ 0 := by
      simpa [pow_two] using RFAP.ExplicitField.mul_ne_zero valueZero valueZero
    exact False.elim (squareNonzero squareZero)

/-- The scalar conditions in Theorem 96. -/
def OrderFiveStarParameters : Prop :=
  ∃ root : K, root ≠ 0 ∧ root ^ 2 = 5 ∧ IsSquare (2 * (5 - root))

/-- The first printed line in the order-five converse. -/
def orderFiveLine₀ [Nontrivial K] : Line K where
  a := 0
  b := 1
  c := 0
  direction_nonzero := Or.inr (one_ne_zero : (1 : K) ≠ 0)

/-- The printed line `⟨v:3-r:0⟩`. -/
def orderFiveLine₁ [Nontrivial K] (root spreadRoot : K)
    (spreadRootNonzero : spreadRoot ≠ 0) : Line K where
  a := spreadRoot
  b := 3 - root
  c := 0
  direction_nonzero := Or.inl spreadRootNonzero

/-- The printed line `⟨v(3-r):2-2r:0⟩`. -/
def orderFiveLine₂ [Nontrivial K] (root spreadRoot : K)
    (spreadRootNonzero : spreadRoot ≠ 0)
    (rootNeThree : (3 : K) - root ≠ 0) : Line K where
  a := spreadRoot * (3 - root)
  b := 2 - 2 * root
  c := 0
  direction_nonzero := Or.inl
    (RFAP.ExplicitField.mul_ne_zero spreadRootNonzero rootNeThree)

/-- The printed line `⟨v(r-3):2-2r:0⟩`. -/
def orderFiveLine₃ [Nontrivial K] (root spreadRoot : K)
    (spreadRootNonzero : spreadRoot ≠ 0)
    (rootMinusThreeNonzero : root - 3 ≠ 0) : Line K where
  a := spreadRoot * (root - 3)
  b := 2 - 2 * root
  c := 0
  direction_nonzero := Or.inl
    (RFAP.ExplicitField.mul_ne_zero spreadRootNonzero rootMinusThreeNonzero)

/-- The printed line `⟨-v:3-r:0⟩`. -/
def orderFiveLine₄ [Nontrivial K] (root spreadRoot : K)
    (spreadRootNonzero : spreadRoot ≠ 0) : Line K where
  a := -spreadRoot
  b := 3 - root
  c := 0
  direction_nonzero := Or.inl (by
    intro negZero
    apply spreadRootNonzero
    calc
      spreadRoot = -(-spreadRoot) := by ring1
      _ = 0 := by rw [negZero]; ring1)

/-- The five explicit source lines form a regular star from the displayed
square witnesses. -/
def orderFiveStar [Nontrivial K] [DecidableEq K]
    (root spreadRoot : K) (rootNonzero : root ≠ 0)
    (rootSquare : root ^ 2 = 5)
    (spreadSquare : spreadRoot ^ 2 = 2 * (5 - root))
    (twoNonzero : (2 : K) ≠ 0) : RegularFiveStar K := by
  have fourNonzero : (4 : K) ≠ 0 := by
    have fourAsProduct : (4 : K) = 2 * 2 := by ring1
    rw [fourAsProduct]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have eightNonzero := eight_ne_zero twoNonzero
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
          ((RFAP.ExplicitField.mul_ne_zero rootNonzero zero) idempotent)
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
    apply (RFAP.ExplicitField.mul_ne_zero twoNonzero fiveMinusRootNonzero)
    calc
      (2 : K) * (5 - root) = spreadRoot ^ 2 := spreadSquare.symm
      _ = 0 := by rw [zero]; ring1
  exact
    { line₀ := orderFiveLine₀
      line₁ := orderFiveLine₁ root spreadRoot spreadRootNonzero
      line₂ := orderFiveLine₂ root spreadRoot spreadRootNonzero rootNeThree
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
        apply (RFAP.ExplicitField.mul_ne_zero eightNonzero rootNeThree)
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
        apply (RFAP.ExplicitField.mul_ne_zero
          (show (32 : K) ≠ 0 by
            have thirtyTwoAsProduct : (32 : K) = 2 * 2 * 2 * 2 * 2 := by ring1
            rw [thirtyTwoAsProduct]
            exact RFAP.ExplicitField.mul_ne_zero
              (RFAP.ExplicitField.mul_ne_zero
                (RFAP.ExplicitField.mul_ne_zero
                  (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero)
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
        apply (RFAP.ExplicitField.mul_ne_zero
          (show (32 : K) ≠ 0 by
            have thirtyTwoAsProduct : (32 : K) = 2 * 2 * 2 * 2 * 2 := by ring1
            rw [thirtyTwoAsProduct]
            exact RFAP.ExplicitField.mul_ne_zero
              (RFAP.ExplicitField.mul_ne_zero
                (RFAP.ExplicitField.mul_ne_zero
                  (RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero)
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
        apply (RFAP.ExplicitField.mul_ne_zero eightNonzero rootNeThree)
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
        unfold Line.Parallel orderFiveLine₀ orderFiveLine₁ at parallel
        calc
          spreadRoot = -(0 * (3 - root) - spreadRoot * 1) := by ring1
          _ = 0 := by rw [parallel]; ring1
      line₀Line₂Nonparallel := by
        intro parallel
        apply (RFAP.ExplicitField.mul_ne_zero spreadRootNonzero rootNeThree)
        unfold Line.Parallel orderFiveLine₀ orderFiveLine₂ at parallel
        calc
          spreadRoot * (3 - root) =
              -(0 * (2 - 2 * root) - spreadRoot * (3 - root) * 1) := by ring1
          _ = 0 := by rw [parallel]; ring1
      line₀Line₃Nonparallel := by
        intro parallel
        apply (RFAP.ExplicitField.mul_ne_zero spreadRootNonzero
          rootMinusThreeNonzero)
        unfold Line.Parallel orderFiveLine₀ orderFiveLine₃ at parallel
        calc
          spreadRoot * (root - 3) =
              -(0 * (2 - 2 * root) - spreadRoot * (root - 3) * 1) := by ring1
          _ = 0 := by rw [parallel]; ring1
      line₀Line₄Nonparallel := by
        intro parallel
        apply spreadRootNonzero
        unfold Line.Parallel orderFiveLine₀ orderFiveLine₄ at parallel
        calc
          spreadRoot = 0 * (3 - root) - (-spreadRoot) * 1 := by ring1
          _ = 0 := parallel
      line₁Line₂Nonparallel := by
        intro parallel
        have productNonzero := RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero
            (show (4 : K) ≠ 0 from fourNonzero) spreadRootNonzero)
          rootMinusThreeNonzero
        apply productNonzero
        unfold Line.Parallel orderFiveLine₁ orderFiveLine₂ at parallel
        calc
          (4 : K) * spreadRoot * (root - 3) =
              spreadRoot * (2 - 2 * root) -
                spreadRoot * (3 - root) * (3 - root) +
                spreadRoot * (root ^ 2 - 5) := by ring1
          _ = 0 := by rw [parallel, rootSquare]; ring1
      line₁Line₃Nonparallel := by
        intro parallel
        apply (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero eightNonzero spreadRootNonzero)
          rootNeTwo)
        unfold Line.Parallel orderFiveLine₁ orderFiveLine₃ at parallel
        calc
          (8 : K) * spreadRoot * (2 - root) =
              spreadRoot * (2 - 2 * root) -
                spreadRoot * (root - 3) * (3 - root) -
                spreadRoot * (root ^ 2 - 5) := by ring1
          _ = 0 := by rw [parallel, rootSquare]; ring1
      line₁Line₄Nonparallel := by
        intro parallel
        apply (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero twoNonzero spreadRootNonzero)
          rootNeThree)
        unfold Line.Parallel orderFiveLine₁ orderFiveLine₄ at parallel
        calc
          (2 : K) * spreadRoot * (3 - root) =
              spreadRoot * (3 - root) - (-spreadRoot) * (3 - root) := by ring1
          _ = 0 := parallel
      line₂Line₃Nonparallel := by
        intro parallel
        apply (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero
            (RFAP.ExplicitField.mul_ne_zero fourNonzero spreadRootNonzero)
            rootNeThree) rootNeOne)
        unfold Line.Parallel orderFiveLine₂ orderFiveLine₃ at parallel
        calc
          (4 : K) * spreadRoot * (3 - root) * (1 - root) =
              spreadRoot * (3 - root) * (2 - 2 * root) -
                spreadRoot * (root - 3) * (2 - 2 * root) := by ring1
          _ = 0 := parallel
      line₂Line₄Nonparallel := by
        intro parallel
        apply (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero eightNonzero spreadRootNonzero)
          rootNeTwo)
        unfold Line.Parallel orderFiveLine₂ orderFiveLine₄ at parallel
        calc
          (8 : K) * spreadRoot * (2 - root) =
              spreadRoot * (3 - root) * (3 - root) -
                (-spreadRoot) * (2 - 2 * root) -
                spreadRoot * (root ^ 2 - 5) := by ring1
          _ = 0 := by rw [parallel, rootSquare]; ring1
      line₃Line₄Nonparallel := by
        intro parallel
        apply (RFAP.ExplicitField.mul_ne_zero
          (RFAP.ExplicitField.mul_ne_zero fourNonzero spreadRootNonzero)
          rootMinusThreeNonzero)
        unfold Line.Parallel orderFiveLine₃ orderFiveLine₄ at parallel
        calc
          (4 : K) * spreadRoot * (root - 3) =
              spreadRoot * (root - 3) * (3 - root) -
                (-spreadRoot) * (2 - 2 * root) -
                (-spreadRoot * (root ^ 2 - 5)) := by ring1
          _ = 0 := by rw [parallel, rootSquare]; ring1
      reflectAround₀ := by
        unfold Line.Equivalent
        simp only [reflectLine, reflectedLineA, reflectedLineB, reflectedLineC,
          lineNorm, orderFiveLine₀, orderFiveLine₁, orderFiveLine₄]
        constructor
        · ring1
        constructor <;> ring1
      reflectAround₁ := by
        unfold Line.Equivalent
        simp only [reflectLine, reflectedLineA, reflectedLineB, reflectedLineC,
          lineNorm, orderFiveLine₀, orderFiveLine₁, orderFiveLine₂]
        constructor
        · apply sub_eq_zero.mp
          calc
            _ = (root * spreadRoot - 3 * spreadRoot) *
                  (root ^ 2 - 5) +
                (-root * spreadRoot + 3 * spreadRoot) *
                  (spreadRoot ^ 2 - 2 * (5 - root)) := by ring1
            _ = 0 := by rw [rootSquare, spreadSquare]; ring1
        constructor <;> ring1
      reflectAround₂ := by
        unfold Line.Equivalent
        simp only [reflectLine, reflectedLineA, reflectedLineB, reflectedLineC,
          lineNorm, orderFiveLine₁, orderFiveLine₂, orderFiveLine₃]
        constructor
        · apply sub_eq_zero.mp
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
        unfold Line.Equivalent
        simp only [reflectLine, reflectedLineA, reflectedLineB, reflectedLineC,
          lineNorm, orderFiveLine₂, orderFiveLine₃, orderFiveLine₄]
        constructor
        · apply sub_eq_zero.mp
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
        unfold Line.Equivalent
        simp only [reflectLine, reflectedLineA, reflectedLineB, reflectedLineC,
          lineNorm, orderFiveLine₀, orderFiveLine₃, orderFiveLine₄]
        constructor
        · apply sub_eq_zero.mp
          calc
            _ = -(root * spreadRoot - 3 * spreadRoot) *
                  (root ^ 2 - 5) -
                (-root * spreadRoot + 3 * spreadRoot) *
                  (spreadRoot ^ 2 - 2 * (5 - root)) := by ring1
            _ = 0 := by rw [rootSquare, spreadSquare]; ring1
        constructor <;> ring1 }

/-- The necessary direction of Theorem 96, following the source through
`S₅(s)=0`, completion of the square, and the spread-number witness. -/
theorem order_five_star_parameters [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0)
    (star : RegularFiveStar K) : OrderFiveStarParameters (K := K) := by
  let initial := star.initialPair
  let s := initial.adjacentSpread
  have sNonzero : s ≠ 0 := by
    intro sZero
    apply star.line₀Line₁Nonparallel
    exact (spread_eq_zero_iff_parallel star.line₀ star.line₁
      star.line₀NonNull star.line₁NonNull).1 sZero
  have closingParallel :
      initial.previous.Parallel (reflectionLineAt initial 5) := by
    apply Line.parallel_symm
    exact line_parallel_of_equivalent star.lineAtFive_equivalent
  have closingSpreadZero :
      spread initial.previous (reflectionLineAt initial 5)
          initial.previousNonNull (reflectionLineAt_nonNull initial 5) = 0 :=
    (spread_eq_zero_iff_parallel initial.previous
      (reflectionLineAt initial 5) initial.previousNonNull
      (reflectionLineAt_nonNull initial 5)).2 closingParallel
  have polynomialValue := consecutive_spreads initial
    star.line₀Line₁Nonparallel twoNonzero 5
  have polynomialZero : spreadPolynomial 5 s = 0 := by
    calc
      spreadPolynomial 5 s =
          spread initial.previous (reflectionLineAt initial 5)
            initial.previousNonNull (reflectionLineAt_nonNull initial 5) :=
        polynomialValue.symm
      _ = 0 := closingSpreadZero
  rw [spreadPolynomial_five_formula] at polynomialZero
  have factorSquareZero : (5 - 20 * s + 16 * s ^ 2) ^ 2 = 0 := by
    by_cases zero : (5 - 20 * s + 16 * s ^ 2) ^ 2 = 0
    · exact zero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero sNonzero zero) polynomialZero)
  have factorZero := square_zero_implies_zero
    (5 - 20 * s + 16 * s ^ 2) factorSquareZero
  let root := 8 * s - 5
  have rootSquare : root ^ 2 = 5 := by
    calc
      root ^ 2 = 5 + 4 * (5 - 20 * s + 16 * s ^ 2) := by
        unfold root
        ring1
      _ = 5 := by rw [factorZero]; ring1
  have eightNonzero := eight_ne_zero twoNonzero
  have eightS : (8 : K) * s = 5 + root := by
    unfold root
    ring1
  have rootNonzero : root ≠ 0 := by
    intro rootZero
    have fiveZero : (5 : K) = 0 := by
      calc
        (5 : K) = root ^ 2 := rootSquare.symm
        _ = 0 := by rw [rootZero]; ring1
    apply (RFAP.ExplicitField.mul_ne_zero eightNonzero sNonzero)
    calc
      (8 : K) * s = 5 + root := eightS
      _ = 0 := by rw [fiveZero, rootZero]; ring1
  rcases spread_isSpreadNumber initial.previous initial.current
      initial.previousNonNull initial.currentNonNull with
    ⟨spreadRoot, spreadSquare⟩
  change s * (1 - s) = spreadRoot ^ 2 at spreadSquare
  have parameterSquare :
      2 * (5 - root) = (8 * spreadRoot) ^ 2 := by
    calc
      2 * (5 - root) =
          64 * (s * (1 - s)) +
            4 * (5 - 20 * s + 16 * s ^ 2) := by
              unfold root
              ring1
      _ = 64 * (s * (1 - s)) := by rw [factorZero]; ring1
      _ = 64 * spreadRoot ^ 2 := by rw [spreadSquare]
      _ = (8 * spreadRoot) ^ 2 := by ring1
  exact ⟨root, rootNonzero, rootSquare,
    ⟨8 * spreadRoot, parameterSquare⟩⟩

/-- Theorem 96 (Order five star): a regular five-star exists exactly when
there is a nonzero square root `r` of `5` for which `2(5-r)` is a square.
Characteristic two is excluded explicitly because the five printed line
representatives then collapse. -/
theorem order_five_star [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (RegularFiveStar K) ↔ OrderFiveStarParameters (K := K) := by
  constructor
  · rintro ⟨star⟩
    exact order_five_star_parameters twoNonzero star
  · rintro ⟨root, rootNonzero, rootSquare, spreadRoot,
      parameterSquare⟩
    exact ⟨orderFiveStar root spreadRoot rootNonzero rootSquare
      parameterSquare.symm twoNonzero⟩

end DivineProportions
