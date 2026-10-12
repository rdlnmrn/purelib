module
public import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Group.Nat.Defs
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Nat.GCD.Coprime
public import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.SignedFraction.Normalization

import Purelib.Data.Nat.Coprime.Arithmetic
import Purelib.Data.Nat.GCD.Scalar
import Purelib.Data.Rat.Fraction

-- Exposed arithmetic records retain these natural divisibility certificates.
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Divisibility
-- Exposed cancellation records retain these exact signed certificates.
import Purelib.Data.Int.Division
import Purelib.Data.Int.Divisibility
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Nat.Multiplication

open Purelib.Data.Nat
open Purelib.Data.Rat

section
@[expose] public section

/-!
# Reduction-aware arithmetic on canonical fractions

The operations in this module return the quotient-free canonical carrier.
Addition removes the common denominator factor before forming products, and
multiplication cross-cancels both numerator/denominator pairs.  The product
is already reduced; addition removes any remaining factor using only the
original denominator gcd.  Neither operation normalizes against the large
assembled denominator.  Explicit coprimality proofs are erased at runtime.
-/

namespace Purelib.Data.Rat.Fraction

open Purelib.Data.Nat.Coprime.Arithmetic
open Purelib.Data
open Purelib.Data.Nat

/-- The ordinary common-denominator display used to state addition correctness. -/
def referenceAddRaw (left right : Rational) : RawFraction :=
  ⟨left.num * (right.den : Int) + right.num * (left.den : Int),
    left.den * right.den, Nat.mul_pos left.den_pos right.den_pos⟩

/-- The ordinary product display used to state multiplication correctness. -/
def referenceMulRaw (left right : Rational) : RawFraction :=
  ⟨left.num * right.num, left.den * right.den,
    Nat.mul_pos left.den_pos right.den_pos⟩

/-- Certified common denominator factor used by addition. -/
def additionCommon (left right : Rational) : Nat :=
  GCD.Scalar.gcd left.den right.den

/-- Left denominator after removal of the common factor. -/
def additionLeftQuotient (left right : Rational) : Nat :=
  left.den / additionCommon left right

/-- Right denominator after removal of the common factor. -/
def additionRightQuotient (left right : Rational) : Nat :=
  right.den / additionCommon left right

/-- The gcd of two positive canonical denominators is positive. -/
theorem additionCommon_pos (left right : Rational) :
    0 < additionCommon left right :=
  GCD.Scalar.gcd_positive_right left.den right.den_pos

/-- Dividing the left positive denominator by the shared gcd leaves a positive quotient. -/
theorem additionLeftQuotient_pos (left right : Rational) :
    0 < additionLeftQuotient left right := by
  have specification := GCD.Scalar.gcd_dvd left.den right.den
  exact Division.div_pos (Divisibility.le_of_dvd left.den_pos specification.1)
    (additionCommon_pos left right)

/-- Dividing the right positive denominator by the shared gcd leaves a positive quotient. -/
theorem additionRightQuotient_pos (left right : Rational) :
    0 < additionRightQuotient left right := by
  have specification := GCD.Scalar.gcd_dvd left.den right.den
  exact Division.div_pos (Divisibility.le_of_dvd right.den_pos specification.2)
    (additionCommon_pos left right)

/-- Addition display with an lcm-sized denominator before final normalization. -/
def addRaw (left right : Rational) : RawFraction :=
  let common := additionCommon left right
  let leftQuotient := left.den / common
  let rightQuotient := right.den / common
  ⟨left.num * (rightQuotient : Int) + right.num * (leftQuotient : Int),
    leftQuotient * right.den,
    Nat.mul_pos (additionLeftQuotient_pos left right) right.den_pos⟩

/-- The left denominator quotient times the shared gcd recovers the original left denominator. -/
theorem additionLeftReconstruct (left right : Rational) :
    additionLeftQuotient left right * additionCommon left right = left.den :=
  Division.div_mul_cancel
    (GCD.Scalar.gcd_dvd left.den right.den).1

/-- The right denominator quotient times the shared gcd recovers the original right denominator. -/
theorem additionRightReconstruct (left right : Rational) :
    additionRightQuotient left right * additionCommon left right = right.den :=
  Division.div_mul_cancel
    (GCD.Scalar.gcd_dvd left.den right.den).2

/-- The reduced-denominator addition display represents the ordinary sum display. -/
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
  GCD.Scalar.gcd left.num.natAbs right.den

/-- Second certified cross-cancellation factor for multiplication. -/
def multiplicationRightCommon (left right : Rational) : Nat :=
  GCD.Scalar.gcd right.num.natAbs left.den

/-- The gcd used to cancel the left numerator against the right positive denominator is positive. -/
theorem multiplicationLeftCommon_pos (left right : Rational) :
    0 < multiplicationLeftCommon left right :=
  GCD.Scalar.gcd_positive_right left.num.natAbs right.den_pos

/-- The gcd used to cancel the right numerator against the left positive denominator is positive. -/
theorem multiplicationRightCommon_pos (left right : Rational) :
    0 < multiplicationRightCommon left right :=
  GCD.Scalar.gcd_positive_right right.num.natAbs left.den_pos

/-- Divide an integer by the displayed natural factor using Euclidean division. -/
def cancelInteger (value : Int) (divisor : Nat) : Int :=
  value / (divisor : Int)

/-- Divide a natural number by the displayed natural factor. -/
def cancelNatural (value divisor : Nat) : Nat :=
  value / divisor

/-- Cancelling a natural divisor of the magnitude reconstructs the integer.

The exact signed quotient is multiplied by the cast divisor. The retained
magnitude divisibility witness certifies that this division has no remainder. -/
theorem cancelInteger_reconstruct {value : Int} {divisor : Nat}
    (divides : divisor ∣ value.natAbs) :
    cancelInteger value divisor * (divisor : Int) = value := by
  exact Int.Division.ediv_mul_cancel (Int.Divisibility.of_natAbs divides)

/-- Multiplying a natural quotient by its supplied divisor recovers the original natural number. -/
theorem cancelNatural_reconstruct {value divisor : Nat}
    (divides : divisor ∣ value) :
    cancelNatural value divisor * divisor = value :=
  Division.div_mul_cancel divides

/-- Compute the original rational product by cross-cancelling its displayed factors.

Each numerator is cancelled against the other denominator using the retained
Euclidean quotient data. The resulting positive-denominator display has the
original product value. -/
def mulRaw (left right : Rational) : RawFraction := by
  let leftCommon := multiplicationLeftCommon left right
  let rightCommon := multiplicationRightCommon left right
  let leftNumerator := cancelInteger left.num leftCommon
  let rightDenominator := cancelNatural right.den leftCommon
  let rightNumerator := cancelInteger right.num rightCommon
  let leftDenominator := cancelNatural left.den rightCommon
  have leftSpecification :=
    GCD.Scalar.gcd_dvd right.num.natAbs left.den
  have rightSpecification :=
    GCD.Scalar.gcd_dvd left.num.natAbs right.den
  have leftDenominatorPositive : 0 < leftDenominator :=
    Division.div_pos (Divisibility.le_of_dvd left.den_pos leftSpecification.2)
      (multiplicationRightCommon_pos left right)
  have rightDenominatorPositive : 0 < rightDenominator :=
    Division.div_pos (Divisibility.le_of_dvd right.den_pos rightSpecification.2)
      (multiplicationLeftCommon_pos left right)
  exact
    ⟨leftNumerator * rightNumerator,
      leftDenominator * rightDenominator,
      Nat.mul_pos leftDenominatorPositive rightDenominatorPositive⟩

/-- The cross-cancelled multiplication display represents the ordinary product display. -/
theorem mulRaw_equivalent (left right : Rational) :
    Equivalent (mulRaw left right) (referenceMulRaw left right) := by
  let leftCommon := multiplicationLeftCommon left right
  let rightCommon := multiplicationRightCommon left right
  have leftSpecification :=
    GCD.Scalar.gcd_dvd left.num.natAbs right.den
  have rightSpecification :=
    GCD.Scalar.gcd_dvd right.num.natAbs left.den
  have leftNumerator := cancelInteger_reconstruct leftSpecification.1
  have rightDenominator := cancelNatural_reconstruct leftSpecification.2
  have rightNumerator := cancelInteger_reconstruct rightSpecification.1
  have leftDenominator := cancelNatural_reconstruct rightSpecification.2
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

/-- Cross-cancellation produces a reduced rational multiplication display.

The input reducedness certificates and the two cross-cancellation certificates
supply all four coprimality relations. Their product certifies the displayed
numerator and denominator without another normalization. -/
theorem mulRaw_reduced (left right : Rational) :
    Reduced (mulRaw left right).num.natAbs (mulRaw left right).den := by
  let first := multiplicationLeftCommon left right
  let second := multiplicationRightCommon left right
  have firstDivides := GCD.Scalar.gcd_dvd left.num.natAbs right.den
  have secondDivides := GCD.Scalar.gcd_dvd right.num.natAbs left.den
  have leftNumeratorDivides : left.num.natAbs / first ∣ left.num.natAbs :=
    ⟨first, (Division.div_mul_cancel firstDivides.1).symm⟩
  have rightDenominatorDivides : right.den / first ∣ right.den :=
    ⟨first, (Division.div_mul_cancel firstDivides.2).symm⟩
  have rightNumeratorDivides : right.num.natAbs / second ∣ right.num.natAbs :=
    ⟨second, (Division.div_mul_cancel secondDivides.1).symm⟩
  have leftDenominatorDivides : left.den / second ∣ left.den :=
    ⟨second, (Division.div_mul_cancel secondDivides.2).symm⟩
  have firstCross : Coprime.Basic.CoprimeCertificate
      (left.num.natAbs / first) (right.den / first) := by
    dsimp only [first, multiplicationLeftCommon]
    rw [GCD.Scalar.gcd_eq_compute]
    exact GCD.Coprime.quotientCoprimeCertificate left.num.natAbs right.den_pos
  have secondCross : Coprime.Basic.CoprimeCertificate
      (right.num.natAbs / second) (left.den / second) := by
    dsimp only [second, multiplicationRightCommon]
    rw [GCD.Scalar.gcd_eq_compute]
    exact GCD.Coprime.quotientCoprimeCertificate right.num.natAbs left.den_pos
  rcases left.reduced with ⟨leftCoprime⟩
  rcases right.reduced with ⟨rightCoprime⟩
  let retainedLeft :=
    Coprime.Arithmetic.of_dvd_right (Coprime.Arithmetic.of_dvd_left leftCoprime leftNumeratorDivides)
      leftDenominatorDivides
  let retainedRight :=
    Coprime.Arithmetic.of_dvd_right (Coprime.Arithmetic.of_dvd_left rightCoprime rightNumeratorDivides)
      rightDenominatorDivides
  change Reduced
    ((left.num / (first : Int)) * (right.num / (second : Int))).natAbs
    ((left.den / second) * (right.den / first))
  rw [Int.Arithmetic.natAbs_mul,
    natAbs_ediv_of_dvd (multiplicationLeftCommon_pos left right) firstDivides.1,
    natAbs_ediv_of_dvd (multiplicationRightCommon_pos left right) secondDivides.1]
  exact ⟨Coprime.Arithmetic.mul_mul
    retainedLeft firstCross secondCross retainedRight⟩

/-- Remove the remaining common factor from the retained addition display.

The numerator and the original common denominator factor share one computed gcd.
Dividing both by that factor retains the same sum and a positive denominator. -/
def reducedAddRaw (left right : Rational) : RawFraction :=
  let common := additionCommon left right
  let first := left.den / common
  let second := right.den / common
  let numerator := left.num * (second : Int) + right.num * (first : Int)
  let remaining := GCD.Scalar.gcd numerator.natAbs common
  have remainingPositive : 0 < remaining :=
    GCD.Scalar.gcd_positive_right numerator.natAbs (additionCommon_pos left right)
  have remainingDividesRight : remaining ∣ right.den :=
    Divisibility.trans (GCD.Scalar.gcd_dvd numerator.natAbs common).2
      (GCD.Scalar.gcd_dvd left.den right.den).2
  ⟨numerator / (remaining : Int), first * (right.den / remaining),
    Nat.mul_pos (additionLeftQuotient_pos left right)
      (Division.div_pos (Divisibility.le_of_dvd right.den_pos remainingDividesRight) remainingPositive)⟩

/-- The cancelled addition display retains coprime numerator and denominator.

The assembled numerator is coprime to both original denominator quotients.
Removing its common factor with the original shared denominator therefore
certifies a reduced display. -/
theorem reducedAddRaw_reduced (left right : Rational) :
    Reduced (reducedAddRaw left right).num.natAbs (reducedAddRaw left right).den := by
  let common := additionCommon left right
  let first := left.den / common
  let second := right.den / common
  let numerator := left.num * (second : Int) + right.num * (first : Int)
  let remaining := GCD.Scalar.gcd numerator.natAbs common
  have commonPositive : 0 < common := additionCommon_pos left right
  have commonDivides := GCD.Scalar.gcd_dvd left.den right.den
  have firstDivides : first ∣ left.den :=
    ⟨common, (Division.div_mul_cancel commonDivides.1).symm⟩
  have secondDivides : second ∣ right.den :=
    ⟨common, (Division.div_mul_cancel commonDivides.2).symm⟩
  have denominatorsCoprime : Coprime.Basic.CoprimeCertificate first second := by
    dsimp only [first, second, common, additionCommon]
    rw [GCD.Scalar.gcd_eq_compute]
    exact GCD.Coprime.quotientCoprimeCertificate left.den right.den_pos
  have remainingPositive : 0 < remaining :=
    GCD.Scalar.gcd_positive_right numerator.natAbs commonPositive
  have remainingDivides := GCD.Scalar.gcd_dvd numerator.natAbs common
  have numeratorQuotientDivides : numerator.natAbs / remaining ∣ numerator.natAbs :=
    ⟨remaining, (Division.div_mul_cancel remainingDivides.1).symm⟩
  have remainingCoprime : Coprime.Basic.CoprimeCertificate
      (numerator.natAbs / remaining) (common / remaining) := by
    dsimp only [remaining]
    rw [GCD.Scalar.gcd_eq_compute]
    exact GCD.Coprime.quotientCoprimeCertificate numerator.natAbs commonPositive
  have rightReconstruct : remaining * (second * (common / remaining)) = right.den := by
    calc
      _ = second * ((common / remaining) * remaining) := by ring1
      _ = second * common := by rw [Division.div_mul_cancel remainingDivides.2]
      _ = right.den := Division.div_mul_cancel commonDivides.2
  have rightQuotient : right.den / remaining = second * (common / remaining) := by
    calc
      _ = (remaining * (second * (common / remaining))) / remaining :=
        congrArg (fun value : Nat => value / remaining) rightReconstruct.symm
      _ = second * (common / remaining) := Division.mul_div_cancel_left _ remainingPositive
  rcases left.reduced with ⟨leftCoprime⟩
  rcases right.reduced with ⟨rightCoprime⟩
  have firstTerm : Coprime.Basic.CoprimeCertificate
      (left.num * (second : Int)).natAbs first := by
    rw [Int.Arithmetic.natAbs_mul, Int.natAbs_natCast]
    exact Coprime.Arithmetic.mul_left (Coprime.Arithmetic.of_dvd_right leftCoprime firstDivides)
      denominatorsCoprime.symm
  have secondTerm : Coprime.Basic.CoprimeCertificate
      (right.num * (first : Int)).natAbs second := by
    rw [Int.Arithmetic.natAbs_mul, Int.natAbs_natCast]
    exact Coprime.Arithmetic.mul_left (Coprime.Arithmetic.of_dvd_right rightCoprime secondDivides) denominatorsCoprime
  have firstSum : Coprime.Basic.CoprimeCertificate numerator.natAbs first :=
    Coprime.Arithmetic.add_int_mul firstTerm (value := left.num * (second : Int)) right.num
  have secondSum : Coprime.Basic.CoprimeCertificate numerator.natAbs second := by
    have result := Coprime.Arithmetic.add_int_mul secondTerm (value := right.num * (first : Int)) left.num
    rw [Int.Arithmetic.add_comm] at result
    exact result
  change Reduced (numerator / (remaining : Int)).natAbs (first * (right.den / remaining))
  rw [natAbs_ediv_of_dvd remainingPositive remainingDivides.1, rightQuotient]
  have product := Coprime.Arithmetic.mul_right
    (Coprime.Arithmetic.mul_right (Coprime.Arithmetic.of_dvd_left firstSum numeratorQuotientDivides)
      (Coprime.Arithmetic.of_dvd_left secondSum numeratorQuotientDivides)) remainingCoprime
  exact ⟨by simpa only [Multiplication.mul_assoc] using product⟩

/-- Dividing the numerator and denominator by the same displayed factor preserves the original reduced-denominator
addition display.

The retained factor divides both displayed components. Their exact quotients
satisfy the original addition cross-product equation. -/
theorem reducedAddRaw_equivalent (left right : Rational) :
    Equivalent (reducedAddRaw left right) (addRaw left right) := by
  let common := additionCommon left right
  let first := left.den / common
  let second := right.den / common
  let numerator := left.num * (second : Int) + right.num * (first : Int)
  let remaining := GCD.Scalar.gcd numerator.natAbs common
  have remainingDivides := GCD.Scalar.gcd_dvd numerator.natAbs common
  have dividesRight : remaining ∣ right.den :=
    Divisibility.trans remainingDivides.2 (GCD.Scalar.gcd_dvd left.den right.den).2
  have numeratorReconstruct : (numerator / (remaining : Int)) * (remaining : Int) = numerator :=
    cancelInteger_reconstruct remainingDivides.1
  have denominatorReconstruct :
      ((right.den / remaining : Nat) : Int) * (remaining : Int) = (right.den : Int) := by
    rw [← Int.natCast_mul]
    exact congrArg (fun value : Nat => (value : Int)) (Division.div_mul_cancel dividesRight)
  change (numerator / (remaining : Int)) * ((first * right.den : Nat) : Int) =
    numerator * ((first * (right.den / remaining) : Nat) : Int)
  rw [Int.natCast_mul, Int.natCast_mul]
  conv_lhs =>
    rhs
    rw [← denominatorReconstruct]
  conv_rhs =>
    lhs
    rw [← numeratorReconstruct]
  ring1

/-- Compute reduction-aware canonical addition on the retained reduced carrier.

The original arithmetic removes the denominator gcd before assembling the sum, then removes only the remaining
common-factor gcd. The readback alias retains that same operation. -/
def add (left right : Rational) : Rational :=
  let raw := reducedAddRaw left right
  ⟨raw.num, raw.den, raw.den_pos, reducedAddRaw_reduced left right⟩

/-- Compute canonical negation on the identical reduced working carrier. -/
def neg (source : Rational) : Rational :=
  ⟨-source.num, source.den, source.den_pos, by
    simpa only [Reduced, Int.natAbs_neg] using source.reduced⟩

/-- Compute cross-cancelled canonical multiplication on the retained reduced carrier.

The original arithmetic cancels each numerator against the opposite denominator before forming products. The resulting
record is already reduced, and the readback alias retains that operation. -/
def mul (left right : Rational) : Rational :=
  let raw := mulRaw left right
  ⟨raw.num, raw.den, raw.den_pos, mulRaw_reduced left right⟩

/-- Exact canonical equality with normalizing the lcm-sized sum display. -/
theorem add_eq_normalize (left right : Rational) :
    add left right = normalize (addRaw left right) := by
  apply eq_of_cross
  exact equivalent_trans (reducedAddRaw_equivalent left right)
    (equivalent_symm (normalize_equivalent (addRaw left right)))

/-- Cross-cancellation already returns the unique normalized product record. -/
theorem mul_eq_normalize (left right : Rational) :
    mul left right = normalize (mulRaw left right) := by
  apply eq_of_cross
  exact equivalent_symm (normalize_equivalent (mulRaw left right))

/-- Compute the sign-canonical total reciprocal of a reduced rational.

Zero maps to zero. A nonzero input exchanges its coprime numerator magnitude and denominator, moves the numerator sign
to the new numerator, and retains the swapped reducedness witness. -/
def inv (source : Rational) : Rational := by
  if zeroNumerator : source.num = 0 then
    exact zero
  else if positiveNumerator : 0 < source.num then
    refine
      ⟨(source.den : Int), source.num.natAbs,
        Int.Arithmetic.natAbs_pos_of_ne_zero zeroNumerator, ?_⟩
    rcases source.reduced with ⟨certificate⟩
    exact ⟨by
      simpa only [Int.natAbs_natCast] using certificate.symm⟩
  else
    refine
      ⟨-(source.den : Int), source.num.natAbs,
        Int.Arithmetic.natAbs_pos_of_ne_zero zeroNumerator, ?_⟩
    rcases source.reduced with ⟨certificate⟩
    exact ⟨by
      simpa only [Int.natAbs_neg, Int.natAbs_natCast] using certificate.symm⟩

/-- Compute canonical subtraction on the identical reduced working carrier. -/
def sub (left right : Rational) : Rational :=
  add left (neg right)

/-- Compute canonical division with total reciprocal on the identical reduced working carrier. -/
def div (left right : Rational) : Rational :=
  mul left (inv right)

/-- The canonical fraction with numerator and denominator both one. -/
def one : Rational :=
  ⟨1, 1, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

/-- Use the original canonical zero operation as the rational arithmetic instance. -/
instance : Zero Rational := ⟨zero⟩
/-- Use the original canonical one operation as the rational arithmetic instance. -/
instance : One Rational := ⟨one⟩
/-- Use the original canonical addition operation as the rational arithmetic instance. -/
instance : Add Rational := ⟨add⟩
/-- Use the original canonical negation operation as the rational arithmetic instance. -/
instance : Neg Rational := ⟨neg⟩
/-- Use the original canonical multiplication operation as the rational arithmetic instance. -/
instance : Mul Rational := ⟨mul⟩
/-- Use the original canonical total reciprocal operation as the rational arithmetic instance. -/
instance : Inv Rational := ⟨inv⟩
/-- Use the original canonical subtraction operation as the rational arithmetic instance. -/
instance : Sub Rational := ⟨sub⟩
/-- Use the original canonical division operation as the rational arithmetic instance. -/
instance : Div Rational := ⟨div⟩

/-- Canonical addition has the ordinary common-denominator meaning. -/
theorem add_equivalent (left right : Rational) :
    Equivalent (add left right).toRaw (referenceAddRaw left right) :=
  equivalent_trans (reducedAddRaw_equivalent left right)
    (addRaw_equivalent left right)

/-- Canonical multiplication has the ordinary product meaning. -/
theorem mul_equivalent (left right : Rational) :
    Equivalent (mul left right).toRaw (referenceMulRaw left right) :=
  mulRaw_equivalent left right

/-- Canonical addition computes one half plus one third as five sixths. -/
theorem add_one_half_one_third :
    (⟨1, 2, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) +
        (⟨1, 3, by decide, ⟨⟨1, 0, by decide⟩⟩⟩ : Rational) =
      (⟨5, 6, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) := by
  decide

/-- Cross-cancelled multiplication computes two thirds times nine tenths as three fifths. -/
theorem mul_two_thirds_nine_tenths :
    (⟨2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) *
        (⟨9, 10, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩ : Rational) =
      (⟨3, 5, by decide, ⟨⟨2, -1, by decide⟩⟩⟩ : Rational) := by
  decide

end Purelib.Data.Rat.Fraction

end

end

section
@[expose] public section

/-!
# Compatibility surface for canonical fractions

This module provides the compatibility operations now owned by
`Purelib.Data.Rat.Fraction.Compatibility` over the quotient-free rational carrier.  All operations use the canonical
structural rational carrier.

The signed-denominator `SignedFraction` record remains available as input syntax.
Its positivity proof makes conversion to the canonical natural-denominator
display total and executable.  Semantic rationals themselves are reduced
structural records; `representative` therefore exposes data already present
in the value rather than selecting a member of a quotient.
-/

namespace Purelib.Data.Rat.Fraction.Arithmetic

/-- Canonical subtraction is definitionally addition of the negated right operand. -/
theorem sub_eq_add_neg_direct (left right : Fraction.Rational) :
    left - right = left + -right := rfl
end Purelib.Data.Rat.Fraction.Arithmetic

end

end

section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Rat.Fraction.Arithmetic
open Purelib.Data.Rat.Fraction.Basic (value Rational ReducedFraction)
open Purelib.Data
open Purelib.Data.Nat

/-- The denominator gcd used by reduction-aware addition. -/
def additionCommon (left right : Fraction.Basic.ReducedFraction) : Nat :=
  Fraction.additionCommon left right

/-- Left denominator after removing the shared denominator gcd. -/
def additionLeftQuotient (left right : Fraction.Basic.ReducedFraction) : Nat
  :=
  Fraction.additionLeftQuotient left right

/-- Right denominator after removing the shared denominator gcd. -/
def additionRightQuotient (left right : Fraction.Basic.ReducedFraction) :
  Nat :=
  Fraction.additionRightQuotient left right

/-- The gcd of two positive canonical denominators is positive. -/
theorem additionCommon_pos (left right : Fraction.Basic.ReducedFraction) :
    0 < additionCommon left right :=
  Fraction.additionCommon_pos left right

/-- Dividing the left positive denominator by the shared gcd leaves a positive quotient. -/
theorem additionLeftQuotient_pos (left right :
  Fraction.Basic.ReducedFraction) :
    0 < additionLeftQuotient left right :=
  Fraction.additionLeftQuotient_pos left right

/-- The retained left denominator quotient and shared gcd reconstruct the original denominator. -/
private theorem addition_left_reconstruct (left right :
  Fraction.Basic.ReducedFraction) :
    additionLeftQuotient left right * additionCommon left right = left.den := by
  exact Fraction.additionLeftReconstruct left right

/-- The retained right denominator quotient and shared gcd reconstruct the original denominator. -/
private theorem addition_right_reconstruct (left right :
  Fraction.Basic.ReducedFraction) :
    additionRightQuotient left right * additionCommon left right = right.den :=
      by
  exact Fraction.additionRightReconstruct left right

/-- First cross-cancellation divisor for multiplication. -/
def multiplicationLeftCommon (left right : Fraction.Basic.ReducedFraction) :
  Nat :=
  Fraction.multiplicationLeftCommon left right

/-- Second cross-cancellation divisor for multiplication. -/
def multiplicationRightCommon (left right : Fraction.Basic.ReducedFraction)
  : Nat :=
  Fraction.multiplicationRightCommon left right

/-- The gcd used to cancel the left numerator against the right positive denominator is positive. -/
theorem multiplicationLeftCommon_pos (left right :
  Fraction.Basic.ReducedFraction) :
    0 < multiplicationLeftCommon left right :=
  Fraction.multiplicationLeftCommon_pos left right

/-- The gcd used to cancel the right numerator against the left positive denominator is positive. -/
theorem multiplicationRightCommon_pos (left right :
  Fraction.Basic.ReducedFraction) :
    0 < multiplicationRightCommon left right :=
  Fraction.multiplicationRightCommon_pos left right

/-- Divide an integer by the displayed natural factor using Euclidean division. -/
private def cancelInteger (value : Int) (divisor : Nat) : Int :=
  value / (divisor : Int)

/-- Divide a natural number by the displayed natural factor. -/
private def cancelNatural (value divisor : Nat) : Nat :=
  value / divisor

/-- Cancelling a natural divisor of the magnitude reconstructs the integer.

The exact signed quotient is multiplied by the cast divisor. The retained
magnitude divisibility witness certifies that this division has no remainder. -/
private theorem cancelInteger_reconstruct {value : Int} {divisor : Nat}
    (divides : divisor ∣ value.natAbs) :
    cancelInteger value divisor * (divisor : Int) = value := by
  exact Int.Division.ediv_mul_cancel (Int.Divisibility.of_natAbs divides)

/-- Multiplying a natural quotient by its supplied divisor recovers the original natural number. -/
private theorem cancelNatural_reconstruct {value divisor : Nat}
    (divides : divisor ∣ value) :
    cancelNatural value divisor * divisor = value :=
  Division.div_mul_cancel divides

/-! ## Normalized working operations -/

/-- Compute reduction-aware canonical addition on the retained reduced carrier.

The original arithmetic removes the denominator gcd before assembling the sum, then removes only the remaining
common-factor gcd. The readback alias retains that same operation. -/
def add (left right : Fraction.Basic.ReducedFraction) : ReducedFraction :=
  left + right

/-- Compute canonical negation on the identical reduced working carrier. -/
def neg (source : Fraction.Basic.ReducedFraction) : ReducedFraction :=
  -source

/-- Compute canonical subtraction on the identical reduced working carrier. -/
def sub (left right : Fraction.Basic.ReducedFraction) : ReducedFraction :=
  left - right

/-- Compute cross-cancelled canonical multiplication on the retained reduced carrier.

The original arithmetic cancels each numerator against the opposite denominator before forming products. The resulting
record is already reduced, and the readback alias retains that operation. -/
def mul (left right : Fraction.Basic.ReducedFraction) : ReducedFraction :=
  left * right

/-- Compute the sign-canonical total reciprocal of a reduced rational.

Zero maps to zero. A nonzero input exchanges its coprime numerator magnitude and denominator, moves the numerator sign
to the new numerator, and retains the swapped reducedness witness. -/
def inv (source : Fraction.Basic.ReducedFraction) : ReducedFraction :=
  source⁻¹

/-- Compute canonical division with total reciprocal on the identical reduced working carrier. -/
def div (left right : Fraction.Basic.ReducedFraction) : ReducedFraction :=
  left / right

/-- Reading back a reduced addition agrees with the same canonical rational operation. -/
theorem value_add (left right : Fraction.Basic.ReducedFraction) :
    value (add left right) = value left + value right := rfl

/-- Reading back a reduced negation agrees with the same canonical rational operation. -/
theorem value_neg (source : Fraction.Basic.ReducedFraction) :
    value (neg source) = -value source := rfl

/-- Reading back a reduced subtraction agrees with the same canonical rational operation. -/
theorem value_sub (left right : Fraction.Basic.ReducedFraction) :
    value (sub left right) = value left - value right := rfl

/-- Reading back a reduced multiplication agrees with the same canonical rational operation. -/
theorem value_mul (left right : Fraction.Basic.ReducedFraction) :
    value (mul left right) = value left * value right := rfl

/-- Reading back a reduced total reciprocal agrees with the same canonical rational operation. -/
theorem value_inv (source : Fraction.Basic.ReducedFraction) :
    value (inv source) = (value source)⁻¹ := rfl

/-- Reading back a reduced division with total reciprocal agrees with the same canonical rational operation. -/
theorem value_div (left right : Fraction.Basic.ReducedFraction) :
    value (div left right) = value left / value right := rfl

/-! ## Quotient-valued entry points

These functions make normalization available to existing RFAP algorithms
without replacing their algebraic statement type. -/

/-- Compute canonical addition through the retained reduced-record readback. -/
def normalizedAdd (left right : Fraction.Rational) : Fraction.Basic.Rational :=
  value (add (Fraction.Basic.ofRational left) (Fraction.Basic.ofRational right))

/-- Compute canonical negation through the retained reduced-record readback. -/
def normalizedNeg (source : Fraction.Rational) : Fraction.Basic.Rational :=
  value (neg (Fraction.Basic.ofRational source))

/-- Compute canonical subtraction through the retained reduced-record readback. -/
def normalizedSub (left right : Fraction.Rational) : Fraction.Basic.Rational :=
  value (sub (Fraction.Basic.ofRational left) (Fraction.Basic.ofRational right))

/-- Compute canonical multiplication through the retained reduced-record readback. -/
def normalizedMul (left right : Fraction.Rational) : Fraction.Basic.Rational :=
  value (mul (Fraction.Basic.ofRational left) (Fraction.Basic.ofRational right))

/-- Compute canonical total reciprocal through the retained reduced-record readback. -/
def normalizedInv (source : Fraction.Rational) : Fraction.Basic.Rational :=
  value (inv (Fraction.Basic.ofRational source))

/-- Compute canonical division with total reciprocal through the retained reduced-record readback. -/
def normalizedDiv (left right : Fraction.Rational) : Fraction.Basic.Rational :=
  value (div (Fraction.Basic.ofRational left) (Fraction.Basic.ofRational right))

/-- Reduced-record addition agrees with the original canonical rational operation. -/
@[simp] theorem normalizedAdd_eq (left right : Fraction.Rational) :
    normalizedAdd left right = left + right := by
  rw [normalizedAdd, value_add, Fraction.Basic.value_ofRational,
    Fraction.Basic.value_ofRational]

/-- Reduced-record negation agrees with the original canonical rational operation. -/
@[simp] theorem normalizedNeg_eq (source : Fraction.Rational) :
    normalizedNeg source = -source := by
  rw [normalizedNeg, value_neg, Fraction.Basic.value_ofRational]

/-- Reduced-record subtraction agrees with the original canonical rational operation. -/
@[simp] theorem normalizedSub_eq (left right : Fraction.Rational) :
    normalizedSub left right = left - right := by
  rw [normalizedSub, value_sub, Fraction.Basic.value_ofRational,
    Fraction.Basic.value_ofRational]

/-- Reduced-record multiplication agrees with the original canonical rational operation. -/
@[simp] theorem normalizedMul_eq (left right : Fraction.Rational) :
    normalizedMul left right = left * right := by
  rw [normalizedMul, value_mul, Fraction.Basic.value_ofRational,
    Fraction.Basic.value_ofRational]

/-- Reduced-record total reciprocal agrees with the original canonical rational operation. -/
@[simp] theorem normalizedInv_eq (source : Fraction.Rational) :
    normalizedInv source = source⁻¹ := by
  rw [normalizedInv, value_inv, Fraction.Basic.value_ofRational]

/-- Reduced-record division with total reciprocal agrees with the original canonical rational operation. -/
@[simp] theorem normalizedDiv_eq (left right : Fraction.Rational) :
    normalizedDiv left right = left / right := by
  rw [normalizedDiv, value_div, Fraction.Basic.value_ofRational,
    Fraction.Basic.value_ofRational]

/-- The reduced record of canonical addition is the result of that same reduced operation. -/
theorem ofRational_normalizedAdd (left right : Fraction.Rational) :
    Fraction.Basic.ofRational (normalizedAdd left right) =
      add (Fraction.Basic.ofRational left) (Fraction.Basic.ofRational right) := by
  exact SignedFraction.Normalization.representative_value _

/-- The reduced record of canonical negation is the result of that same reduced operation. -/
theorem ofRational_normalizedNeg (source : Fraction.Rational) :
    Fraction.Basic.ofRational (normalizedNeg source) = neg
      (Fraction.Basic.ofRational source) := by
  exact SignedFraction.Normalization.representative_value _

/-- The reduced record of canonical subtraction is the result of that same reduced operation. -/
theorem ofRational_normalizedSub (left right : Fraction.Rational) :
    Fraction.Basic.ofRational (normalizedSub left right) =
      sub (Fraction.Basic.ofRational left) (Fraction.Basic.ofRational right) := by
  exact SignedFraction.Normalization.representative_value _

/-- The reduced record of canonical multiplication is the result of that same reduced operation. -/
theorem ofRational_normalizedMul (left right : Fraction.Rational) :
    Fraction.Basic.ofRational (normalizedMul left right) =
      mul (Fraction.Basic.ofRational left) (Fraction.Basic.ofRational right) := by
  exact SignedFraction.Normalization.representative_value _

/-- The reduced record of canonical total reciprocal is the result of that same reduced operation. -/
theorem ofRational_normalizedInv (source : Fraction.Rational) :
    Fraction.Basic.ofRational (normalizedInv source) = inv
      (Fraction.Basic.ofRational source) := by
  exact SignedFraction.Normalization.representative_value _

/-- The reduced record of canonical division with total reciprocal is the result of that same reduced operation. -/
theorem ofRational_normalizedDiv (left right : Fraction.Rational) :
    Fraction.Basic.ofRational (normalizedDiv left right) =
      div (Fraction.Basic.ofRational left) (Fraction.Basic.ofRational right) := by
  exact SignedFraction.Normalization.representative_value _
end Purelib.Data.Rat.Fraction.Arithmetic

end

section
@[expose] public section

/-!
# Explicit field compatibility for canonical normalized arithmetic

Normalized fractions and Gaussian rationals now are the canonical semantic
carriers themselves.  Their existing `CommRing` and `Purelib.Algebra.Field.ExplicitField`
instances therefore already govern the named normalized operations.  This
module retains the erasure-map theorems used by generic finite polynomial
programs without installing duplicate arithmetic instances for the same
carrier.
-/

namespace Purelib.Data.Rat.Fraction.Arithmetic
open Purelib.Data.Rat.Fraction.Basic (value Rational ReducedFraction)

/-- The value readback from reduced records is injective because it retains the same carrier. -/
theorem value_injective : Function.Injective value := by
  intro left right equal
  exact equal

/-- Reading back the canonical zero record gives zero. -/
@[simp] theorem value_zero : Fraction.Basic.value (0 :
  Fraction.Basic.ReducedFraction) = 0 := rfl

/-- Reading back the canonical one record gives one. -/
@[simp] theorem value_one : Fraction.Basic.value (1 :
  Fraction.Basic.ReducedFraction) = 1 := rfl

/-- The reduced-record value map preserves the canonical addition instance. -/
@[simp] theorem value_add_instance (left right :
  Fraction.Basic.ReducedFraction) :
    Fraction.Basic.value (left + right) = Fraction.Basic.value left + Fraction.Basic.value right := rfl

/-- The reduced-record value map preserves the canonical negation instance. -/
@[simp] theorem value_neg_instance (source : Fraction.Basic.ReducedFraction)
  :
    Fraction.Basic.value (-source) = -Fraction.Basic.value source := rfl

/-- The reduced-record value map preserves the canonical subtraction instance. -/
@[simp] theorem value_sub_instance (left right :
  Fraction.Basic.ReducedFraction) :
    Fraction.Basic.value (left - right) = Fraction.Basic.value left - Fraction.Basic.value right := rfl

/-- The reduced-record value map preserves the canonical multiplication instance. -/
@[simp] theorem value_mul_instance (left right :
  Fraction.Basic.ReducedFraction) :
    Fraction.Basic.value (left * right) = Fraction.Basic.value left * Fraction.Basic.value right := rfl

/-- The reduced-record value map preserves the canonical total reciprocal instance. -/
@[simp] theorem value_inv_instance (source : Fraction.Basic.ReducedFraction)
  :
    Fraction.Basic.value source⁻¹ = (Fraction.Basic.value source)⁻¹ := rfl

/-- The reduced-record value map preserves the canonical division with total reciprocal instance. -/
@[simp] theorem value_div_instance (left right :
  Fraction.Basic.ReducedFraction) :
    Fraction.Basic.value (left / right) = Fraction.Basic.value left / Fraction.Basic.value right := rfl

end Purelib.Data.Rat.Fraction.Arithmetic

end
