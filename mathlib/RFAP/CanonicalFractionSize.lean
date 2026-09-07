import mathlib.RFAP.CanonicalFractionOrder

/-!
# Calculation-size bounds for canonical fractions

These bounds describe the integer and natural records actually formed by the
reduction-aware operations.  They retain the RFAP-2 discipline that a final
normalization must not hide an unnecessarily inflated intermediate product.
-/

namespace RFAP.CanonicalFraction

theorem normalize_numerator_le (fraction : RawFraction) :
    (normalize fraction).num.natAbs ≤ fraction.num.natAbs := by
  let result := CanonicalGCD.compute fraction.num.natAbs fraction.den
  have specification :=
    CanonicalGCD.compute_spec fraction.num.natAbs fraction.den
  have divisorPositive : 0 < result.gcd :=
    CanonicalGCD.compute_gcd_positive_right fraction.num.natAbs
      fraction.den_pos
  change (fraction.num / (result.gcd : Int)).natAbs ≤ fraction.num.natAbs
  rw [natAbs_ediv_of_dvd divisorPositive specification.2.1]
  exact Nat.div_le_self _ _

theorem normalize_denominator_le (fraction : RawFraction) :
    (normalize fraction).den ≤ fraction.den := by
  let result := CanonicalGCD.compute fraction.num.natAbs fraction.den
  change fraction.den / result.gcd ≤ fraction.den
  exact Nat.div_le_self _ _

theorem additionLeftQuotient_le (left right : Rational) :
    additionLeftQuotient left right ≤ left.den :=
  Nat.div_le_self _ _

theorem additionRightQuotient_le (left right : Rational) :
    additionRightQuotient left right ≤ right.den :=
  Nat.div_le_self _ _

theorem addRaw_denominator_le (left right : Rational) :
    (addRaw left right).den ≤ left.den * right.den := by
  change additionLeftQuotient left right * right.den ≤
    left.den * right.den
  exact Nat.mul_le_mul_right right.den (additionLeftQuotient_le left right)

theorem addRaw_numerator_le (left right : Rational) :
    (addRaw left right).num.natAbs ≤
      left.num.natAbs * right.den + right.num.natAbs * left.den := by
  change
    (left.num * (additionRightQuotient left right : Int) +
      right.num * (additionLeftQuotient left right : Int)).natAbs ≤ _
  calc
    _ ≤ (left.num * (additionRightQuotient left right : Int)).natAbs +
          (right.num * (additionLeftQuotient left right : Int)).natAbs :=
      Int.natAbs_add_le _ _
    _ = left.num.natAbs * additionRightQuotient left right +
        right.num.natAbs * additionLeftQuotient left right := by
      simp only [Int.natAbs_mul, Int.natAbs_natCast]
    _ ≤ left.num.natAbs * right.den + right.num.natAbs * left.den :=
      Nat.add_le_add
        (Nat.mul_le_mul_left left.num.natAbs
          (additionRightQuotient_le left right))
        (Nat.mul_le_mul_left right.num.natAbs
          (additionLeftQuotient_le left right))

theorem mulRaw_denominator_le (left right : Rational) :
    (mulRaw left right).den ≤ left.den * right.den := by
  change
    cancelNatural left.den (multiplicationRightCommon left right) *
        cancelNatural right.den (multiplicationLeftCommon left right) ≤
      left.den * right.den
  exact Nat.mul_le_mul (Nat.div_le_self _ _) (Nat.div_le_self _ _)

theorem cancelInteger_natAbs_le (value : Int) {divisor : Nat}
    (divisorPositive : 0 < divisor) (divides : divisor ∣ value.natAbs) :
    (cancelInteger value divisor).natAbs ≤ value.natAbs := by
  change (value / (divisor : Int)).natAbs ≤ value.natAbs
  rw [natAbs_ediv_of_dvd divisorPositive divides]
  exact Nat.div_le_self _ _

theorem mulRaw_numerator_le (left right : Rational) :
    (mulRaw left right).num.natAbs ≤
      left.num.natAbs * right.num.natAbs := by
  have leftSpecification :=
    CanonicalGCD.compute_spec left.num.natAbs right.den
  have rightSpecification :=
    CanonicalGCD.compute_spec right.num.natAbs left.den
  change
    (cancelInteger left.num (multiplicationLeftCommon left right) *
      cancelInteger right.num (multiplicationRightCommon left right)).natAbs ≤ _
  rw [Int.natAbs_mul]
  exact Nat.mul_le_mul
    (cancelInteger_natAbs_le left.num
      (multiplicationLeftCommon_pos left right) leftSpecification.2.1)
    (cancelInteger_natAbs_le right.num
      (multiplicationRightCommon_pos left right) rightSpecification.2.1)

theorem add_denominator_le (left right : Rational) :
    (left + right).den ≤ left.den * right.den :=
  (normalize_denominator_le (addRaw left right)).trans
    (addRaw_denominator_le left right)

theorem add_numerator_le (left right : Rational) :
    (left + right).num.natAbs ≤
      left.num.natAbs * right.den + right.num.natAbs * left.den :=
  (normalize_numerator_le (addRaw left right)).trans
    (addRaw_numerator_le left right)

theorem mul_denominator_le (left right : Rational) :
    (left * right).den ≤ left.den * right.den :=
  (normalize_denominator_le (mulRaw left right)).trans
    (mulRaw_denominator_le left right)

theorem mul_numerator_le (left right : Rational) :
    (left * right).num.natAbs ≤ left.num.natAbs * right.num.natAbs :=
  (normalize_numerator_le (mulRaw left right)).trans
    (mulRaw_numerator_le left right)

@[simp] theorem neg_denominator (source : Rational) :
    (-source).den = source.den := rfl

@[simp] theorem neg_numerator_natAbs (source : Rational) :
    (-source).num.natAbs = source.num.natAbs :=
  Int.natAbs_neg source.num

/-- Maximum magnitude of either stored component. -/
def componentMagnitude (source : Rational) : Nat :=
  max source.num.natAbs source.den

theorem numerator_le_componentMagnitude (source : Rational) :
    source.num.natAbs ≤ componentMagnitude source :=
  le_max_left _ _

theorem denominator_le_componentMagnitude (source : Rational) :
    source.den ≤ componentMagnitude source :=
  le_max_right _ _

/-- Source-only envelope for addition's returned components. -/
def addComponentEnvelope (left right : Rational) : Nat :=
  max
    (left.num.natAbs * right.den + right.num.natAbs * left.den)
    (left.den * right.den)

/-- Source-only envelope for multiplication's returned components. -/
def mulComponentEnvelope (left right : Rational) : Nat :=
  max (left.num.natAbs * right.num.natAbs) (left.den * right.den)

theorem componentMagnitude_add_le (left right : Rational) :
    componentMagnitude (left + right) ≤ addComponentEnvelope left right := by
  apply max_le
  · exact (add_numerator_le left right).trans (le_max_left _ _)
  · exact (add_denominator_le left right).trans (le_max_right _ _)

theorem componentMagnitude_mul_le (left right : Rational) :
    componentMagnitude (left * right) ≤ mulComponentEnvelope left right := by
  apply max_le
  · exact (mul_numerator_le left right).trans (le_max_left _ _)
  · exact (mul_denominator_le left right).trans (le_max_right _ _)

theorem componentMagnitude_neg (source : Rational) :
    componentMagnitude (-source) = componentMagnitude source := by
  simp only [componentMagnitude, neg_numerator_natAbs, neg_denominator]

theorem componentMagnitude_inv_le (source : Rational) :
    componentMagnitude source⁻¹ ≤ componentMagnitude source := by
  by_cases numeratorZero : source.num = 0
  · have sourceZero : source = 0 :=
      (eq_zero_iff_num_zero source).mpr numeratorZero
    rw [sourceZero, inv_zero]
  · by_cases numeratorPositive : 0 < source.num
    · simpa only [componentMagnitude, Inv.inv, inv, numeratorZero,
        numeratorPositive, ↓reduceDIte, Int.natAbs_natCast] using
        Nat.le_of_eq (max_comm source.den source.num.natAbs)
    · simpa only [componentMagnitude, Inv.inv, inv, numeratorZero,
        numeratorPositive, ↓reduceDIte, Int.natAbs_neg,
        Int.natAbs_natCast] using
        Nat.le_of_eq (max_comm source.den source.num.natAbs)

/-- The explicit recursion fuel consumed by one certified gcd call. -/
def gcdFuel (_leftInput rightInput : Nat) : Nat := rightInput + 1

theorem gcdFuel_pos (leftInput rightInput : Nat) :
    0 < gcdFuel leftInput rightInput :=
  Nat.zero_lt_succ rightInput

/-- Coarse, explicit arithmetic-step account for normalized addition: one
denominator gcd, the final normalization gcd, and fixed quotient/product/sum
work. -/
def addSteps (left right : Rational) : Nat :=
  gcdFuel left.den right.den + gcdFuel (addRaw left right).num.natAbs
    (addRaw left right).den + 8

/-- Coarse, explicit arithmetic-step account for normalized multiplication:
two cross-cancellation gcds, the final normalization gcd, and fixed
quotient/product work. -/
def mulSteps (left right : Rational) : Nat :=
  gcdFuel left.num.natAbs right.den +
    gcdFuel right.num.natAbs left.den +
    gcdFuel (mulRaw left right).num.natAbs (mulRaw left right).den + 8

/-- Negation and reciprocal only rearrange already reduced components. -/
def negSteps (_source : Rational) : Nat := 1
def invSteps (_source : Rational) : Nat := 2

end RFAP.CanonicalFraction
