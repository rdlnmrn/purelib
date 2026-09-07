import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadChebyshev
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 8: constructive rational spread bounds

Exercise 8.3 is retained over the source's rational field.  The proof uses a
finite Chebyshev square invariant and the project-owned constructive order on
explicit fractions; it introduces neither completed real numbers nor limits.
-/

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- The polynomial usually written `U_(n-1)`, with its exceptional initial
value incorporated into a primitive-recursive sequence. -/
def chebyshevSecondPrevious : Nat → K → K
  | 0, _ => 0
  | 1, _ => 1
  | index + 2, value =>
      2 * value * chebyshevSecondPrevious (index + 1) value -
        chebyshevSecondPrevious index value

@[simp] theorem chebyshevSecondPrevious_zero (value : K) :
    chebyshevSecondPrevious 0 value = 0 := rfl

@[simp] theorem chebyshevSecondPrevious_one (value : K) :
    chebyshevSecondPrevious 1 value = 1 := rfl

@[simp] theorem chebyshevSecondPrevious_succ_succ
    (index : Nat) (value : K) :
    chebyshevSecondPrevious (index + 2) value =
      2 * value * chebyshevSecondPrevious (index + 1) value -
        chebyshevSecondPrevious index value := rfl

/-- The two first-order transitions underlying the Chebyshev square
invariant.  They are proved together by finite induction. -/
theorem chebyshevFirst_secondPrevious_transitions
    (index : Nat) (value : K) :
    chebyshevFirst (index + 1) value =
        value * chebyshevFirst index value -
          (1 - value ^ 2) * chebyshevSecondPrevious index value ∧
      chebyshevSecondPrevious (index + 1) value =
        chebyshevFirst index value +
          value * chebyshevSecondPrevious index value := by
  induction index with
  | zero =>
      constructor <;>
        unfold chebyshevFirst chebyshevSecondPrevious <;> ring1
  | succ index inductionHypothesis =>
      rcases inductionHypothesis with ⟨firstTransition, secondTransition⟩
      constructor
      · rw [show Nat.succ index + 1 = index + 2 by omega0]
        rw [chebyshevFirst_succ_succ, firstTransition, secondTransition]
        ring1
      · rw [show Nat.succ index + 1 = index + 2 by omega0]
        rw [chebyshevSecondPrevious_succ_succ, firstTransition,
          secondTransition]
        ring1

/-- The finite polynomial identity
`T_n(x)^2 + (1-x^2) U_(n-1)(x)^2 = 1`. -/
theorem chebyshevFirst_square_invariant (index : Nat) (value : K) :
    chebyshevFirst index value ^ 2 +
        (1 - value ^ 2) * chebyshevSecondPrevious index value ^ 2 = 1 := by
  induction index with
  | zero =>
      unfold chebyshevFirst chebyshevSecondPrevious
      ring1
  | succ index inductionHypothesis =>
      rcases chebyshevFirst_secondPrevious_transitions index value with
        ⟨firstTransition, secondTransition⟩
      rw [firstTransition, secondTransition]
      calc
        (value * chebyshevFirst index value -
              (1 - value ^ 2) *
                chebyshevSecondPrevious index value) ^ 2 +
            (1 - value ^ 2) *
              (chebyshevFirst index value +
                value * chebyshevSecondPrevious index value) ^ 2 =
          chebyshevFirst index value ^ 2 +
            (1 - value ^ 2) *
              chebyshevSecondPrevious index value ^ 2 := by ring1
        _ = 1 := inductionHypothesis

namespace ExerciseEightThree

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- A Chebyshev value at a constructive rational input in `[-1,1]` remains
in `[-1,1]`.  The square invariant supplies both bounds directly. -/
theorem chebyshevFirst_mem_unitInterval
    (index : Nat) (value : Rational)
    (lowerBound : -1 ≤ value) (upperBound : value ≤ 1) :
    -1 ≤ chebyshevFirst index value ∧
      chebyshevFirst index value ≤ 1 := by
  have leftFactorNonnegative : 0 ≤ (1 : Rational) - value :=
    RFAP.ConstructiveFraction.sub_nonneg_direct upperBound
  have rightFactorNonnegative : 0 ≤ (1 : Rational) + value := by
    have shifted :=
      RFAP.ConstructiveFraction.sub_nonneg_direct lowerBound
    calc
      0 ≤ value - (-1 : Rational) := shifted
      _ = 1 + value := by ring1
  have radialFactorNonnegative : 0 ≤ (1 : Rational) - value ^ 2 := by
    calc
      0 ≤ (1 - value) * (1 + value) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct
          leftFactorNonnegative rightFactorNonnegative
      _ = 1 - value ^ 2 := by ring1
  have residualNonnegative :
      0 ≤ ((1 : Rational) - value ^ 2) *
        chebyshevSecondPrevious index value ^ 2 :=
    RFAP.ConstructiveFraction.mul_nonneg_direct radialFactorNonnegative
      (RFAP.ConstructiveFraction.sq_nonneg_direct _)
  have squareDifferenceNonnegative :
      0 ≤ (1 : Rational) - chebyshevFirst index value ^ 2 := by
    calc
      0 ≤ ((1 : Rational) - value ^ 2) *
          chebyshevSecondPrevious index value ^ 2 := residualNonnegative
      _ = 1 - chebyshevFirst index value ^ 2 := by
        calc
          ((1 : Rational) - value ^ 2) *
                chebyshevSecondPrevious index value ^ 2 =
              (chebyshevFirst index value ^ 2 +
                  (1 - value ^ 2) *
                    chebyshevSecondPrevious index value ^ 2) -
                chebyshevFirst index value ^ 2 := by ring1
          _ = 1 - chebyshevFirst index value ^ 2 := by
            rw [chebyshevFirst_square_invariant]
  have squareBound :
      chebyshevFirst index value ^ 2 ≤ (1 : Rational) ^ 2 := by
    have raw := RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
      squareDifferenceNonnegative
    simpa only [one_pow] using raw
  have oneNonnegative : (0 : Rational) ≤ 1 := by decide
  exact ⟨
    RFAP.ConstructiveFraction.neg_le_of_sq_le_sq_direct
      oneNonnegative squareBound,
    RFAP.ConstructiveFraction.le_of_sq_le_sq_direct
      oneNonnegative squareBound⟩

/-- Exercise 8.3 over the exact constructive rational field: every requested
finite spread-polynomial evaluation maps `[0,1]` into `[0,1]`. -/
theorem exercise_8_3
    (index : Nat) (value : Rational)
    (lowerBound : 0 ≤ value) (upperBound : value ≤ 1) :
    0 ≤ spreadPolynomial index value ∧
      spreadPolynomial index value ≤ 1 := by
  have twoNonnegative : (0 : Rational) ≤ 2 := by decide
  have oneMinusValueNonnegative : 0 ≤ (1 : Rational) - value :=
    RFAP.ConstructiveFraction.sub_nonneg_direct upperBound
  have transformedUpper : (1 : Rational) - 2 * value ≤ 1 := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (2 : Rational) * value :=
        RFAP.ConstructiveFraction.mul_nonneg_direct twoNonnegative lowerBound
      _ = 1 - (1 - 2 * value) := by ring1
  have transformedLower : (-1 : Rational) ≤ 1 - 2 * value := by
    apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    calc
      0 ≤ (2 : Rational) * (1 - value) :=
        RFAP.ConstructiveFraction.mul_nonneg_direct twoNonnegative
          oneMinusValueNonnegative
      _ = (1 - 2 * value) - (-1) := by ring1
  rcases chebyshevFirst_mem_unitInterval index (1 - 2 * value)
      transformedLower transformedUpper with
    ⟨chebyshevLower, chebyshevUpper⟩
  have cleared := exercise_8_4_cleared index value
  have twoPositive : (0 : Rational) < 2 := by decide
  constructor
  · apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct _
      twoPositive
    calc
      (0 : Rational) * 2 = 0 := by ring1
      _ ≤ 1 - chebyshevFirst index (1 - 2 * value) :=
        RFAP.ConstructiveFraction.sub_nonneg_direct chebyshevUpper
      _ = spreadPolynomial index value * 2 := by rw [← cleared]; ring1
  · apply RFAP.ConstructiveFraction.le_of_mul_le_mul_right_direct _
      twoPositive
    calc
      spreadPolynomial index value * 2 =
          1 - chebyshevFirst index (1 - 2 * value) := by rw [← cleared]; ring1
      _ ≤ 2 := by
        apply RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
        have shifted :=
          RFAP.ConstructiveFraction.sub_nonneg_direct chebyshevLower
        calc
          0 ≤ chebyshevFirst index (1 - 2 * value) - (-1 : Rational) :=
            shifted
          _ = 2 - (1 - chebyshevFirst index (1 - 2 * value)) := by ring1
      _ = (1 : Rational) * 2 := by ring1

end ExerciseEightThree

end DivineProportions
