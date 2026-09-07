import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadPolynomial
import mathlib.RFAP.FiniteBinomial

/-!
# Divine Proportions, Chapter 8: the spread coefficient array

Exercise 8.9 writes every spread polynomial as a finite binomial-coefficient
sum.  Its displayed coefficient contains a quotient.  We first identify it
with the integral entry obtained by adding two shifted copies of Pascal's
triangle.  This gives a division-free theorem over every commutative ring;
the source's quotient notation is recovered only when its finitely many
denominators are supplied as nonzero.
-/

namespace DivineProportions

/-- The entry in the spread array at row `row` and exponent `exponent`.
It is the sum of the corresponding entries in Pascal's triangle and the
same triangle shifted down by two places. -/
def spreadArrayCoefficient (row exponent : Nat) : Nat :=
  (row + exponent).choose (exponent + exponent) +
    (row + exponent - 1).choose (exponent + exponent)

@[simp] theorem spreadArrayCoefficient_zero (row : Nat) :
    spreadArrayCoefficient row 0 = 2 := by
  unfold spreadArrayCoefficient
  simp only [Nat.add_zero, Nat.choose_zero_right]

theorem spreadArrayCoefficient_eq_zero_of_lt
    {row exponent : Nat} (outside : row < exponent) :
    spreadArrayCoefficient row exponent = 0 := by
  unfold spreadArrayCoefficient
  rw [Nat.choose_eq_zero_of_lt (by omega0),
    Nat.choose_eq_zero_of_lt (by omega0), Nat.zero_add]

private theorem choose_spread_wave (top lower : Nat) :
    (top + 3).choose (lower + 2) +
          (top + 2).choose (lower + 2) +
        ((top + 1).choose (lower + 2) + top.choose (lower + 2)) =
      2 * ((top + 2).choose (lower + 2) +
          (top + 1).choose (lower + 2)) +
        ((top + 1).choose lower + top.choose lower) := by
  have firstMiddle :
      (top + 1).choose (lower + 1) =
        top.choose lower + top.choose (lower + 1) :=
    Nat.choose_succ_succ' top lower
  have firstUpper :
      (top + 1).choose (lower + 2) =
        top.choose (lower + 1) + top.choose (lower + 2) := by
    simpa only [Nat.add_assoc] using
      Nat.choose_succ_succ' top (lower + 1)
  have secondMiddle :
      (top + 2).choose (lower + 1) =
        (top + 1).choose lower + (top + 1).choose (lower + 1) := by
    simpa only [Nat.add_assoc] using
      Nat.choose_succ_succ' (top + 1) lower
  have secondUpper :
      (top + 2).choose (lower + 2) =
        (top + 1).choose (lower + 1) +
          (top + 1).choose (lower + 2) := by
    simpa only [Nat.add_assoc] using
      Nat.choose_succ_succ' (top + 1) (lower + 1)
  have thirdUpper :
      (top + 3).choose (lower + 2) =
        (top + 2).choose (lower + 1) +
          (top + 2).choose (lower + 2) := by
    simpa only [Nat.add_assoc] using
      Nat.choose_succ_succ' (top + 2) (lower + 1)
  omega0

/-- Pascal's recursion survives the two-row addition defining the spread
array.  The exponent-zero entry is retained explicitly on the right. -/
theorem spreadArrayCoefficient_recurrence
    (row exponent : Nat) :
    spreadArrayCoefficient (row + 2) (exponent + 1) +
        spreadArrayCoefficient row (exponent + 1) =
      2 * spreadArrayCoefficient (row + 1) (exponent + 1) +
        spreadArrayCoefficient (row + 1) exponent := by
  unfold spreadArrayCoefficient
  have wave := choose_spread_wave (row + exponent) (exponent + exponent)
  rw [show (exponent + 1) + (exponent + 1) =
        exponent + exponent + 2 by omega0,
    show row + 2 + (exponent + 1) - 1 =
        row + exponent + 2 by omega0,
    show row + 2 + (exponent + 1) =
        row + exponent + 3 by omega0,
    show row + (exponent + 1) - 1 = row + exponent by omega0,
    show row + (exponent + 1) = row + exponent + 1 by omega0,
    show row + 1 + (exponent + 1) - 1 =
        row + exponent + 1 by omega0,
    show row + 1 + (exponent + 1) =
        row + exponent + 2 by omega0,
    show row + 1 + exponent - 1 = row + exponent by omega0,
    show row + 1 + exponent = row + exponent + 1 by omega0]
  exact wave

/-- The division-free finite sum in Exercise 8.9, ordered by increasing
power of `-4s`. -/
def spreadCoefficientExpansion
    {R : Type*} [CommRing R] (row : Nat) (value : R) : R :=
  RFAP.finitePrefixSum row (fun index =>
    (spreadArrayCoefficient row (index + 1) : R) * value *
      (-4 * value) ^ index)

@[simp] theorem spreadCoefficientExpansion_zero
    {R : Type*} [CommRing R] (value : R) :
    spreadCoefficientExpansion 0 value = 0 := rfl

@[simp] theorem spreadCoefficientExpansion_one
    {R : Type*} [CommRing R] (value : R) :
    spreadCoefficientExpansion 1 value = value := by
  unfold spreadCoefficientExpansion
  rw [RFAP.finitePrefixSum_succ, RFAP.finitePrefixSum_zero, add_zero]
  change ((spreadArrayCoefficient 1 1 : Nat) : R) * value *
    (-4 * value) ^ 0 = value
  have coefficient : spreadArrayCoefficient 1 1 = 1 := rfl
  rw [coefficient, Nat.cast_one, one_mul, pow_zero, mul_one]

/-- The spread-array sum obeys the same second-order recurrence as the
spread polynomials. -/
theorem spreadCoefficientExpansion_recurrence
    {R : Type*} [CommRing R] (row : Nat) (value : R) :
    spreadCoefficientExpansion (row + 2) value =
      2 * (1 - 2 * value) *
          spreadCoefficientExpansion (row + 1) value -
        spreadCoefficientExpansion row value + 2 * value := by
  let term : Nat → Nat → R := fun current index =>
    (spreadArrayCoefficient current (index + 1) : R) * value *
      (-4 * value) ^ index
  let shifted : Nat → R := fun index =>
    match index with
    | 0 => 2 * value
    | previous + 1 => (-4 * value) * term (row + 1) previous
  have pointwise : ∀ index : Nat,
      term (row + 2) index + term row index =
        2 * term (row + 1) index + shifted index := by
    intro index
    have coefficientRecurrence :=
      spreadArrayCoefficient_recurrence row index
    have castRecurrence := congrArg
      (fun coefficient : Nat => (coefficient : R)) coefficientRecurrence
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at castRecurrence
    cases index with
    | zero =>
        simp only [term, shifted, pow_zero]
        calc
          (spreadArrayCoefficient (row + 2) (0 + 1) : R) * value * 1 +
                (spreadArrayCoefficient row (0 + 1) : R) * value * 1 =
              ((spreadArrayCoefficient (row + 2) (0 + 1) : R) +
                (spreadArrayCoefficient row (0 + 1) : R)) * value := by
            ring1
          _ = (2 * (spreadArrayCoefficient (row + 1) (0 + 1) : R) +
                (spreadArrayCoefficient (row + 1) 0 : R)) * value := by
            rw [castRecurrence]
          _ = 2 *
                ((spreadArrayCoefficient (row + 1) (0 + 1) : R) *
                  value * 1) +
              2 * value := by
            rw [spreadArrayCoefficient_zero]
            simp only [Nat.cast_ofNat]
            ring1
    | succ previous =>
        simp only [term, shifted, pow_succ]
        calc
          (spreadArrayCoefficient (row + 2) (previous + 1 + 1) : R) *
                  value * ((-4 * value) ^ previous * (-4 * value)) +
                (spreadArrayCoefficient row (previous + 1 + 1) : R) *
                  value * ((-4 * value) ^ previous * (-4 * value)) =
              ((spreadArrayCoefficient (row + 2)
                    (previous + 1 + 1) : R) +
                (spreadArrayCoefficient row
                    (previous + 1 + 1) : R)) *
                  value * ((-4 * value) ^ previous * (-4 * value)) := by
            ring1
          _ = (2 * (spreadArrayCoefficient (row + 1)
                    (previous + 1 + 1) : R) +
                (spreadArrayCoefficient (row + 1)
                    (previous + 1) : R)) *
                  value * ((-4 * value) ^ previous * (-4 * value)) := by
            rw [castRecurrence]
          _ = 2 *
                ((spreadArrayCoefficient (row + 1)
                    (previous + 1 + 1) : R) * value *
                      ((-4 * value) ^ previous * (-4 * value))) +
              (-4 * value) *
                ((spreadArrayCoefficient (row + 1)
                    (previous + 1) : R) * value *
                      (-4 * value) ^ previous) := by
            ring1
  have previousPadding :
      RFAP.finitePrefixSum (row + 2) (term row) =
        RFAP.finitePrefixSum row (term row) := by
    rw [show row + 2 = (row + 1) + 1 by omega0,
      RFAP.finitePrefixSum_succ_last,
      RFAP.finitePrefixSum_succ_last]
    dsimp only [term]
    rw [spreadArrayCoefficient_eq_zero_of_lt (by omega0 : row < row + 1),
      spreadArrayCoefficient_eq_zero_of_lt (by omega0 : row < row + 2)]
    simp only [Nat.cast_zero, zero_mul, add_zero]
  have currentPadding :
      RFAP.finitePrefixSum (row + 2) (term (row + 1)) =
        RFAP.finitePrefixSum (row + 1) (term (row + 1)) := by
    rw [show row + 2 = (row + 1) + 1 by omega0,
      RFAP.finitePrefixSum_succ_last]
    dsimp only [term]
    rw [spreadArrayCoefficient_eq_zero_of_lt
      (by omega0 : row + 1 < row + 2)]
    simp only [Nat.cast_zero, zero_mul, add_zero]
  have shiftedSum :
      RFAP.finitePrefixSum (row + 2) shifted =
        2 * value +
          (-4 * value) *
            RFAP.finitePrefixSum (row + 1) (term (row + 1)) := by
    change
      2 * value +
          RFAP.finitePrefixSum (row + 1)
            (fun index => (-4 * value) * term (row + 1) index) = _
    rw [RFAP.finitePrefixSum_mul_left]
  have sumEquation :
      RFAP.finitePrefixSum (row + 2) (term (row + 2)) +
          RFAP.finitePrefixSum (row + 2) (term row) =
        2 * RFAP.finitePrefixSum (row + 2) (term (row + 1)) +
          RFAP.finitePrefixSum (row + 2) shifted := by
    calc
      RFAP.finitePrefixSum (row + 2) (term (row + 2)) +
            RFAP.finitePrefixSum (row + 2) (term row) =
          RFAP.finitePrefixSum (row + 2)
            (fun index => term (row + 2) index + term row index) :=
        (RFAP.finitePrefixSum_add _ _ _).symm
      _ = RFAP.finitePrefixSum (row + 2)
            (fun index =>
              2 * term (row + 1) index + shifted index) := by
          apply RFAP.finitePrefixSum_congr
          intro index indexBound
          exact pointwise index
      _ = RFAP.finitePrefixSum (row + 2)
              (fun index => 2 * term (row + 1) index) +
            RFAP.finitePrefixSum (row + 2) shifted :=
        RFAP.finitePrefixSum_add _ _ _
      _ = 2 * RFAP.finitePrefixSum (row + 2) (term (row + 1)) +
            RFAP.finitePrefixSum (row + 2) shifted := by
        rw [RFAP.finitePrefixSum_mul_left]
  unfold spreadCoefficientExpansion
  change
    RFAP.finitePrefixSum (row + 2) (term (row + 2)) = _
  rw [previousPadding, currentPadding, shiftedSum] at sumEquation
  change
    RFAP.finitePrefixSum (row + 2) (term (row + 2)) =
      2 * (1 - 2 * value) *
          RFAP.finitePrefixSum (row + 1) (term (row + 1)) -
        RFAP.finitePrefixSum row (term row) + 2 * value
  calc
    RFAP.finitePrefixSum (row + 2) (term (row + 2)) =
        (RFAP.finitePrefixSum (row + 2) (term (row + 2)) +
            RFAP.finitePrefixSum row (term row)) -
          RFAP.finitePrefixSum row (term row) := by ring1
    _ = (2 * RFAP.finitePrefixSum (row + 1) (term (row + 1)) +
          (2 * value +
            (-4 * value) *
              RFAP.finitePrefixSum (row + 1) (term (row + 1)))) -
        RFAP.finitePrefixSum row (term row) := by rw [sumEquation]
    _ = 2 * (1 - 2 * value) *
          RFAP.finitePrefixSum (row + 1) (term (row + 1)) -
        RFAP.finitePrefixSum row (term row) + 2 * value := by ring1

/-- Exercise 8.9 in its stronger integral-coefficient form.  Every requested
index is evaluated by a finite prefix, and no denominator or characteristic
hypothesis is needed. -/
theorem exercise_8_9_integer_coefficients
    {R : Type*} [CommRing R] (row : Nat) (value : R) :
    spreadPolynomial row value = spreadCoefficientExpansion row value := by
  let agreesAt := fun current : Nat =>
    spreadPolynomial current value =
      spreadCoefficientExpansion current value
  have allPairs : ∀ current : Nat,
      agreesAt current ∧ agreesAt (current + 1) := by
    intro current
    induction current with
    | zero =>
        constructor
        · rfl
        · unfold agreesAt
          simp only [Nat.zero_add, spreadPolynomial_one,
            spreadCoefficientExpansion_one]
    | succ current inductionHypothesis =>
        constructor
        · simpa only [Nat.succ_eq_add_one] using inductionHypothesis.2
        · unfold agreesAt
          rw [show Nat.succ current + 1 = current + 2 by omega0,
            spreadPolynomial_succ_succ,
            spreadCoefficientExpansion_recurrence,
            inductionHypothesis.1, inductionHypothesis.2]
  exact (allPairs row).1

private theorem spreadArrayCoefficient_cross_product
    (row exponent : Nat) (positive : 0 < exponent)
    (within : exponent ≤ row) :
    exponent * spreadArrayCoefficient row exponent =
      row * (row + exponent - 1).choose (exponent + exponent - 1) := by
  let top := row + exponent - 1
  let lower := exponent + exponent - 1
  have firstRelation := Nat.add_one_mul_choose_eq top lower
  have secondRelation := Nat.choose_succ_right_eq top lower
  have topSucc : top + 1 = row + exponent := by
    unfold top
    omega0
  have lowerSucc : lower + 1 = exponent + exponent := by
    unfold lower
    omega0
  have remainder : top - lower = row - exponent := by
    unfold top lower
    omega0
  rw [topSucc, lowerSucc] at firstRelation
  rw [lowerSucc, remainder] at secondRelation
  apply Nat.mul_left_cancel (n := 2) (by decide)
  unfold spreadArrayCoefficient
  change
    2 * (exponent *
      ((row + exponent).choose (exponent + exponent) +
        top.choose (exponent + exponent))) =
      2 * (row * top.choose lower)
  rw [show 2 * (exponent *
      ((row + exponent).choose (exponent + exponent) +
        top.choose (exponent + exponent))) =
      (row + exponent).choose (exponent + exponent) *
      (exponent + exponent) +
        top.choose (exponent + exponent) *
          (exponent + exponent) by ring1]
  rw [← firstRelation, secondRelation]
  have reconstruction : row - exponent + exponent = row := by omega0
  calc
    (row + exponent) * top.choose lower +
          top.choose lower * (row - exponent) =
        (row - exponent + exponent + exponent) * top.choose lower +
          top.choose lower * (row - exponent) := by
      rw [reconstruction]
    _ = 2 * ((row - exponent + exponent) * top.choose lower) := by
      ring1
    _ = 2 * (row * top.choose lower) := by rw [reconstruction]

private theorem spreadArrayCoefficient_source_cross_product
    (row index : Nat) (indexBound : index < row) :
    (row - index) * spreadArrayCoefficient row (row - index) =
      row * (2 * row - 1 - index).choose index := by
  have positive : 0 < row - index := by omega0
  have within : row - index ≤ row := Nat.sub_le row index
  have crossProduct := spreadArrayCoefficient_cross_product
    row (row - index) positive within
  have topEquality : row + (row - index) - 1 = 2 * row - 1 - index := by
    omega0
  have lowerEquality :
      (row - index) + (row - index) - 1 =
        (2 * row - 1 - index) - index := by
    omega0
  calc
    (row - index) * spreadArrayCoefficient row (row - index) =
        row * (row + (row - index) - 1).choose
          ((row - index) + (row - index) - 1) := crossProduct
    _ = row * (2 * row - 1 - index).choose
          ((2 * row - 1 - index) - index) := by
      rw [topEquality, lowerEquality]
    _ = row * (2 * row - 1 - index).choose index := by
      rw [RFAP.finite_choose_symm (by omega0)]

private theorem mul_right_cancel_explicit
    {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productEquality : left * factor = right * factor) :
    left = right := by
  by_cases equality : left = right
  · exact equality
  have differenceNonzero : left - right ≠ 0 := sub_ne_zero.mpr equality
  have productNonzero :=
    RFAP.ExplicitField.mul_ne_zero differenceNonzero factorNonzero
  apply False.elim
  apply productNonzero
  calc
    (left - right) * factor = left * factor - right * factor := by ring1
    _ = 0 := sub_eq_zero.mpr productEquality

/-- The spread-array integer is the quotient coefficient printed in
Exercise 8.9.  Only this presentation needs the corresponding natural cast
to be nonzero in the coefficient field. -/
theorem spreadArrayCoefficient_eq_source_quotient
    {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]
    (row index : Nat) (indexBound : index < row)
    (denominatorNonzero : ((row - index : Nat) : K) ≠ 0) :
    (spreadArrayCoefficient row (row - index) : K) =
      (row : K) / (row - index : Nat) *
        ((2 * row - 1 - index).choose index : K) := by
  have naturalCrossProduct :=
    spreadArrayCoefficient_source_cross_product row index indexBound
  have castCrossProduct := congrArg
    (fun coefficient : Nat => (coefficient : K)) naturalCrossProduct
  simp only [Nat.cast_mul] at castCrossProduct
  apply mul_right_cancel_explicit denominatorNonzero
  calc
    (spreadArrayCoefficient row (row - index) : K) *
          (row - index : Nat) =
        (row - index : Nat) *
          (spreadArrayCoefficient row (row - index) : K) := by ring1
    _ = (row : K) * ((2 * row - 1 - index).choose index : K) :=
      castCrossProduct
    _ = (((row : K) / (row - index : Nat)) *
          (row - index : Nat)) *
        ((2 * row - 1 - index).choose index : K) := by
      rw [RFAP.ExplicitField.div_mul_cancel _ denominatorNonzero]
    _ = ((row : K) / (row - index : Nat) *
          ((2 * row - 1 - index).choose index : K)) *
        (row - index : Nat) := by ring1

/-- Exercise 8.9 exactly in the source's descending-index quotient notation.
The premise lists only the finitely many denominators that the displayed sum
actually uses. -/
theorem exercise_8_9
    {K : Type*} [RFAP.ExplicitField K] [DecidableEq K]
    (row : Nat) (value : K)
    (denominatorsNonzero : ∀ index : Nat, index < row →
      ((row - index : Nat) : K) ≠ 0) :
    spreadPolynomial row value =
      value * RFAP.finitePrefixSum row (fun index =>
        ((row : K) / (row - index : Nat)) *
          ((2 * row - 1 - index).choose index : K) *
            (-4 * value) ^ (row - index - 1)) := by
  rw [exercise_8_9_integer_coefficients]
  unfold spreadCoefficientExpansion
  rw [RFAP.finitePrefixSum_reverse]
  rw [← RFAP.finitePrefixSum_mul_left]
  apply RFAP.finitePrefixSum_congr
  intro index indexBound
  have coefficientIndex : row - 1 - index + 1 = row - index := by
    omega0
  have powerIndex : row - 1 - index = row - index - 1 := by
    omega0
  rw [coefficientIndex, powerIndex]
  rw [spreadArrayCoefficient_eq_source_quotient row index indexBound
    (denominatorsNonzero index indexBound)]
  ring1

/-- The first four rows displayed in the source's spread array. -/
theorem spreadArray_first_four_rows :
    spreadArrayCoefficient 1 1 = 1 ∧
      (spreadArrayCoefficient 2 1 = 4 ∧
        spreadArrayCoefficient 2 2 = 1) ∧
      (spreadArrayCoefficient 3 1 = 9 ∧
        spreadArrayCoefficient 3 2 = 6 ∧
        spreadArrayCoefficient 3 3 = 1) ∧
      (spreadArrayCoefficient 4 1 = 16 ∧
        spreadArrayCoefficient 4 2 = 20 ∧
        spreadArrayCoefficient 4 3 = 8 ∧
        spreadArrayCoefficient 4 4 = 1) := by
  decide

/-- The source's worked scaled-polynomial example
`S₃*(r) = 4S₃(r/4) = 9r - 6r² + r³`. -/
theorem scaledSpreadPolynomial_three
    {K : Type*} [RFAP.ExplicitField K]
    (value : K) (fourNonzero : (4 : K) ≠ 0) :
    4 * spreadPolynomial 3 (value / 4) =
      9 * value - 6 * value ^ 2 + value ^ 3 := by
  let quarter := value / 4
  have recoverValue : value = 4 * quarter := by
    unfold quarter
    calc
      value = value / 4 * 4 :=
        (RFAP.ExplicitField.div_mul_cancel value fourNonzero).symm
      _ = 4 * (value / 4) := by ring1
  change 4 * spreadPolynomial 3 quarter =
    9 * value - 6 * value ^ 2 + value ^ 3
  rw [recoverValue]
  simp only [spreadPolynomial]
  ring1

end DivineProportions
