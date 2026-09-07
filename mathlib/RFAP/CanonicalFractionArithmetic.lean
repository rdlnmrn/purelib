import mathlib.Tactic.QuotientFreeRing
import mathlib.RFAP.CanonicalFraction

/-!
# Reduction-aware arithmetic on canonical fractions

The operations in this module return the quotient-free canonical carrier.
Addition removes the common denominator factor before forming products, and
multiplication cross-cancels both numerator/denominator pairs.  The final
normalization is therefore a uniqueness boundary, not a substitute for
controlling the size of the intermediate calculation.
-/

namespace RFAP.CanonicalFraction

/-- The ordinary common-denominator display used to state addition
correctness. -/
def referenceAddRaw (left right : Rational) : RawFraction :=
  ⟨left.num * (right.den : Int) + right.num * (left.den : Int),
    left.den * right.den, Nat.mul_pos left.den_pos right.den_pos⟩

/-- The ordinary product display used to state multiplication correctness. -/
def referenceMulRaw (left right : Rational) : RawFraction :=
  ⟨left.num * right.num, left.den * right.den,
    Nat.mul_pos left.den_pos right.den_pos⟩

/-- Certified common denominator factor used by addition. -/
def additionCommon (left right : Rational) : Nat :=
  (CanonicalGCD.compute left.den right.den).gcd

/-- Left denominator after removal of the common factor. -/
def additionLeftQuotient (left right : Rational) : Nat :=
  left.den / additionCommon left right

/-- Right denominator after removal of the common factor. -/
def additionRightQuotient (left right : Rational) : Nat :=
  right.den / additionCommon left right

theorem additionCommon_pos (left right : Rational) :
    0 < additionCommon left right :=
  CanonicalGCD.compute_gcd_positive_right left.den right.den_pos

theorem additionLeftQuotient_pos (left right : Rational) :
    0 < additionLeftQuotient left right := by
  have specification := CanonicalGCD.compute_spec left.den right.den
  exact Nat.div_pos (Nat.le_of_dvd left.den_pos specification.2.1)
    (additionCommon_pos left right)

theorem additionRightQuotient_pos (left right : Rational) :
    0 < additionRightQuotient left right := by
  have specification := CanonicalGCD.compute_spec left.den right.den
  exact Nat.div_pos (Nat.le_of_dvd right.den_pos specification.2.2)
    (additionCommon_pos left right)

/-- Addition display with an lcm-sized denominator before final
normalization. -/
def addRaw (left right : Rational) : RawFraction :=
  ⟨left.num * (additionRightQuotient left right : Int) +
      right.num * (additionLeftQuotient left right : Int),
    additionLeftQuotient left right * right.den,
    Nat.mul_pos (additionLeftQuotient_pos left right) right.den_pos⟩

theorem additionLeftReconstruct (left right : Rational) :
    additionLeftQuotient left right * additionCommon left right = left.den :=
  Nat.div_mul_cancel
    (CanonicalGCD.compute_spec left.den right.den).2.1

theorem additionRightReconstruct (left right : Rational) :
    additionRightQuotient left right * additionCommon left right = right.den :=
  Nat.div_mul_cancel
    (CanonicalGCD.compute_spec left.den right.den).2.2

/-- The reduced-denominator addition display represents the ordinary sum
display. -/
theorem addRaw_equivalent (left right : Rational) :
    Equivalent (addRaw left right) (referenceAddRaw left right) := by
  have leftReconstruct :
      (additionLeftQuotient left right : Int) *
          (additionCommon left right : Int) = (left.den : Int) := by
    rw [← Int.natCast_mul]
    exact congrArg (fun value : Nat => (value : Int))
      (additionLeftReconstruct left right)
  have rightReconstruct :
      (additionRightQuotient left right : Int) *
          (additionCommon left right : Int) = (right.den : Int) := by
    rw [← Int.natCast_mul]
    exact congrArg (fun value : Nat => (value : Int))
      (additionRightReconstruct left right)
  dsimp only [Equivalent, addRaw, referenceAddRaw]
  change
    (left.num * (additionRightQuotient left right : Int) +
          right.num * (additionLeftQuotient left right : Int)) *
        ((left.den : Int) * (right.den : Int)) =
      (left.num * (right.den : Int) + right.num * (left.den : Int)) *
        ((additionLeftQuotient left right : Int) * (right.den : Int))
  conv_lhs =>
    rhs
    rw [← leftReconstruct, ← rightReconstruct]
  conv_rhs =>
    lhs
    rw [← leftReconstruct, ← rightReconstruct]
  conv_rhs =>
    rhs
    rw [← rightReconstruct]
  ring1

/-- First certified cross-cancellation factor for multiplication. -/
def multiplicationLeftCommon (left right : Rational) : Nat :=
  (CanonicalGCD.compute left.num.natAbs right.den).gcd

/-- Second certified cross-cancellation factor for multiplication. -/
def multiplicationRightCommon (left right : Rational) : Nat :=
  (CanonicalGCD.compute right.num.natAbs left.den).gcd

theorem multiplicationLeftCommon_pos (left right : Rational) :
    0 < multiplicationLeftCommon left right :=
  CanonicalGCD.compute_gcd_positive_right left.num.natAbs right.den_pos

theorem multiplicationRightCommon_pos (left right : Rational) :
    0 < multiplicationRightCommon left right :=
  CanonicalGCD.compute_gcd_positive_right right.num.natAbs left.den_pos

def cancelInteger (value : Int) (divisor : Nat) : Int :=
  value / (divisor : Int)

def cancelNatural (value divisor : Nat) : Nat :=
  value / divisor

theorem cancelInteger_reconstruct {value : Int} {divisor : Nat}
    (divides : divisor ∣ value.natAbs) :
    cancelInteger value divisor * (divisor : Int) = value := by
  apply Int.ediv_mul_cancel
  rw [← Int.dvd_natAbs, Int.ofNat_dvd]
  exact divides

theorem cancelNatural_reconstruct {value divisor : Nat}
    (divides : divisor ∣ value) :
    cancelNatural value divisor * divisor = value :=
  Nat.div_mul_cancel divides

/-- Cross-cancelled multiplication display. -/
def mulRaw (left right : Rational) : RawFraction := by
  let leftCommon := multiplicationLeftCommon left right
  let rightCommon := multiplicationRightCommon left right
  let leftNumerator := cancelInteger left.num leftCommon
  let rightDenominator := cancelNatural right.den leftCommon
  let rightNumerator := cancelInteger right.num rightCommon
  let leftDenominator := cancelNatural left.den rightCommon
  have leftSpecification :=
    CanonicalGCD.compute_spec right.num.natAbs left.den
  have rightSpecification :=
    CanonicalGCD.compute_spec left.num.natAbs right.den
  have leftDenominatorPositive : 0 < leftDenominator :=
    Nat.div_pos (Nat.le_of_dvd left.den_pos leftSpecification.2.2)
      (multiplicationRightCommon_pos left right)
  have rightDenominatorPositive : 0 < rightDenominator :=
    Nat.div_pos (Nat.le_of_dvd right.den_pos rightSpecification.2.2)
      (multiplicationLeftCommon_pos left right)
  exact
    ⟨leftNumerator * rightNumerator,
      leftDenominator * rightDenominator,
      Nat.mul_pos leftDenominatorPositive rightDenominatorPositive⟩

/-- The cross-cancelled multiplication display represents the ordinary
product display. -/
theorem mulRaw_equivalent (left right : Rational) :
    Equivalent (mulRaw left right) (referenceMulRaw left right) := by
  let leftCommon := multiplicationLeftCommon left right
  let rightCommon := multiplicationRightCommon left right
  have leftSpecification :=
    CanonicalGCD.compute_spec left.num.natAbs right.den
  have rightSpecification :=
    CanonicalGCD.compute_spec right.num.natAbs left.den
  have leftNumerator := cancelInteger_reconstruct leftSpecification.2.1
  have rightDenominator := cancelNatural_reconstruct leftSpecification.2.2
  have rightNumerator := cancelInteger_reconstruct rightSpecification.2.1
  have leftDenominator := cancelNatural_reconstruct rightSpecification.2.2
  change cancelInteger left.num leftCommon * (leftCommon : Int) = left.num
    at leftNumerator
  change cancelNatural right.den leftCommon * leftCommon = right.den
    at rightDenominator
  change cancelInteger right.num rightCommon * (rightCommon : Int) = right.num
    at rightNumerator
  change cancelNatural left.den rightCommon * rightCommon = left.den
    at leftDenominator
  have rightDenominatorCast :
      (cancelNatural right.den leftCommon : Int) * (leftCommon : Int) =
        (right.den : Int) := by
    rw [← Int.natCast_mul]
    exact congrArg (fun value : Nat => (value : Int)) rightDenominator
  have leftDenominatorCast :
      (cancelNatural left.den rightCommon : Int) * (rightCommon : Int) =
        (left.den : Int) := by
    rw [← Int.natCast_mul]
    exact congrArg (fun value : Nat => (value : Int)) leftDenominator
  dsimp only [Equivalent, mulRaw, referenceMulRaw]
  change
    (cancelInteger left.num leftCommon * cancelInteger right.num rightCommon) *
        ((left.den : Int) * (right.den : Int)) =
      (left.num * right.num) *
        ((cancelNatural left.den rightCommon : Int) *
          (cancelNatural right.den leftCommon : Int))
  conv_lhs =>
    rhs
    rw [← leftDenominatorCast, ← rightDenominatorCast]
  conv_rhs =>
    lhs
    rw [← leftNumerator, ← rightNumerator]
  ring1

/-- Reduction-aware canonical addition. -/
def add (left right : Rational) : Rational :=
  normalize (addRaw left right)

/-- Negation preserves the positive denominator and the reducedness
certificate. -/
def neg (source : Rational) : Rational :=
  ⟨-source.num, source.den, source.den_pos, by
    simpa only [Reduced, Int.natAbs_neg] using source.reduced⟩

/-- Reduction-aware canonical multiplication. -/
def mul (left right : Rational) : Rational :=
  normalize (mulRaw left right)

/-- Sign-canonical total reciprocal.  Zero maps to zero; a nonzero input
swaps the already-coprime numerator magnitude and denominator. -/
def inv (source : Rational) : Rational := by
  if zeroNumerator : source.num = 0 then
    exact zero
  else if positiveNumerator : 0 < source.num then
    refine
      ⟨(source.den : Int), source.num.natAbs,
        Int.natAbs_pos.mpr zeroNumerator, ?_⟩
    rcases source.reduced with ⟨certificate⟩
    exact ⟨by
      simpa only [Int.natAbs_natCast] using certificate.symm⟩
  else
    refine
      ⟨-(source.den : Int), source.num.natAbs,
        Int.natAbs_pos.mpr zeroNumerator, ?_⟩
    rcases source.reduced with ⟨certificate⟩
    exact ⟨by
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using certificate.symm⟩

def sub (left right : Rational) : Rational :=
  add left (neg right)

def div (left right : Rational) : Rational :=
  mul left (inv right)

def one : Rational :=
  ⟨1, 1, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

instance : Zero Rational := ⟨zero⟩
instance : One Rational := ⟨one⟩
instance : Add Rational := ⟨add⟩
instance : Neg Rational := ⟨neg⟩
instance : Mul Rational := ⟨mul⟩
instance : Inv Rational := ⟨inv⟩
instance : Sub Rational := ⟨sub⟩
instance : Div Rational := ⟨div⟩

/-- Canonical addition has the ordinary common-denominator meaning. -/
theorem add_equivalent (left right : Rational) :
    Equivalent (add left right).toRaw (referenceAddRaw left right) :=
  equivalent_trans (normalize_equivalent (addRaw left right))
    (addRaw_equivalent left right)

/-- Canonical multiplication has the ordinary product meaning. -/
theorem mul_equivalent (left right : Rational) :
    Equivalent (mul left right).toRaw (referenceMulRaw left right) :=
  equivalent_trans (normalize_equivalent (mulRaw left right))
    (mulRaw_equivalent left right)

/-- Small executable checks exercise denominator reduction and both
cross-cancellation paths. -/
theorem add_one_half_one_third :
    (⟨1, 2, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) +
        (⟨1, 3, by decide, ⟨⟨1, 0, by decide⟩⟩⟩ : Rational) =
      (⟨5, 6, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) := by
  decide

theorem mul_two_thirds_nine_tenths :
    (⟨2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) *
        (⟨9, 10, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) =
      (⟨3, 5, by decide, ⟨⟨2, -1, by decide⟩⟩⟩ : Rational) := by
  decide

end RFAP.CanonicalFraction
