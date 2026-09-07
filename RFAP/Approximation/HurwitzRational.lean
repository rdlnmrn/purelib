import mathlib.Tactic.QuotientFreeOmega
import mathlib.Tactic.QuotientFreeRing
import RFAP.Approximation.HurwitzNearest

/-!
# Executable Hurwitz continued fractions for displayed Gaussian rationals

This module introduces an uncancelled Gaussian-integer numerator/denominator
record and proves that nearest-Gaussian-integer division strictly decreases
the natural quadrance of its denominator.  The resulting digit recursion is
therefore a total finite program on every displayed Gaussian rational.
-/

namespace RFAP.ConstructiveGaussianHeight.GaussianInt

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian

@[simp] theorem toGaussian_neg (value : GaussianInt) :
    toGaussian (-value) = -toGaussian value := by
  ext <;> simp only [toGaussian, neg_re, neg_im,
    RFAP.ConstructiveGaussian.Gaussian.neg_re,
    RFAP.ConstructiveGaussian.Gaussian.neg_im, Int.cast_neg]

@[simp] theorem toGaussian_sub (left right : GaussianInt) :
    toGaussian (left - right) = toGaussian left - toGaussian right := by
  ext <;> simp only [toGaussian, sub_re, sub_im,
    RFAP.ConstructiveGaussian.Gaussian.sub_re,
    RFAP.ConstructiveGaussian.Gaussian.sub_im, Int.cast_sub]

theorem toGaussian_injective : Function.Injective toGaussian := by
  intro left right equal
  apply GaussianInt.ext
  · exact RFAP.ConstructiveFraction.intCast_injective_direct
      (congrArg RFAP.ConstructiveGaussian.Gaussian.re equal)
  · exact RFAP.ConstructiveFraction.intCast_injective_direct
      (congrArg RFAP.ConstructiveGaussian.Gaussian.im equal)

end RFAP.ConstructiveGaussianHeight.GaussianInt

namespace RFAP.HurwitzRational

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianInt := RFAP.ConstructiveGaussianHeight.GaussianInt

open RFAP.ConstructiveGaussian.Gaussian
open RFAP.ConstructiveGaussianHeight.GaussianInt

/-- An uncancelled fraction over the Gaussian integers.  The squared norm of
`denominator` is its intrinsic displayed denominator height. -/
structure Fraction where
  numerator : GaussianInt
  denominator : GaussianInt
  denominatorNonzero : denominator ≠ 0
deriving Repr

namespace Fraction

/-- The exact constructive Gaussian value of a displayed integral fraction. -/
def value (fraction : Fraction) : Gaussian :=
  toGaussian fraction.numerator * (toGaussian fraction.denominator)⁻¹

theorem denominatorGaussianNonzero (fraction : Fraction) :
    toGaussian fraction.denominator ≠ 0 := by
  intro zero
  exact fraction.denominatorNonzero (toGaussian_eq_zero.mp zero)

/-- Cross-multiplication recovers the displayed numerator. -/
theorem value_mul_denominator (fraction : Fraction) :
    fraction.value * toGaussian fraction.denominator =
      toGaussian fraction.numerator := by
  dsimp only [value]
  rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
    RFAP.ConstructiveGaussian.Gaussian.inv_eq,
    RFAP.ConstructiveGaussian.Gaussian.inv_mul _
      fraction.denominatorGaussianNonzero,
    RFAP.ConstructiveGaussian.Gaussian.mul_one]

theorem value_ne_zero (fraction : Fraction)
    (numeratorNonzero : fraction.numerator ≠ 0) : fraction.value ≠ 0 := by
  intro valueZero
  have productZero := congrArg
    (fun value => value * toGaussian fraction.denominator) valueZero
  rw [fraction.value_mul_denominator,
    RFAP.ConstructiveGaussian.Gaussian.zero_mul] at productZero
  exact numeratorNonzero (toGaussian_eq_zero.mp productZero)

/-- Exact squared norm of the displayed Gaussian denominator. -/
def height (fraction : Fraction) : Nat :=
  normNat fraction.denominator

end Fraction

/-- Current nearest-Gaussian-integer partial quotient. -/
def digit (fraction : Fraction) : GaussianInt :=
  RFAP.HurwitzNearest.nearest fraction.value

/-- Current half-square residual. -/
def residual (fraction : Fraction) : Gaussian :=
  RFAP.HurwitzNearest.remainder fraction.value

/-- Splitting off the selected digit recovers the exact complete quotient. -/
theorem value_eq_digit_add_residual (fraction : Fraction) :
    fraction.value = toGaussian (digit fraction) + residual fraction := by
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [residual, digit, RFAP.HurwitzNearest.remainder,
      RFAP.ConstructiveGaussian.Gaussian.add_re,
      RFAP.ConstructiveGaussian.Gaussian.add_im,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im] <;>
    ring1

/-- Integral remainder obtained without division. -/
def remainder (fraction : Fraction) : GaussianInt :=
  fraction.numerator - digit fraction * fraction.denominator

/-- The integer Euclidean division identity. -/
theorem digit_mul_denominator_add_remainder (fraction : Fraction) :
    digit fraction * fraction.denominator + remainder fraction =
      fraction.numerator := by
  apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
    simp only [remainder,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_re,
      RFAP.ConstructiveGaussianHeight.GaussianInt.mul_im] <;>
    ring1

/-- Embedding the integral remainder agrees with the half-square residual
times the old denominator. -/
theorem remainder_toGaussian (fraction : Fraction) :
    toGaussian (remainder fraction) =
      residual fraction * toGaussian fraction.denominator := by
  rw [remainder, toGaussian_sub, toGaussian_mul]
  rw [← fraction.value_mul_denominator]
  apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
    simp only [residual, digit, RFAP.HurwitzNearest.remainder,
      RFAP.ConstructiveGaussian.Gaussian.sub_re,
      RFAP.ConstructiveGaussian.Gaussian.sub_im,
      RFAP.ConstructiveGaussian.Gaussian.mul_re,
      RFAP.ConstructiveGaussian.Gaussian.mul_im] <;>
    ring1

theorem residual_ne_zero {fraction : Fraction}
    (remainderNonzero : remainder fraction ≠ 0) :
    residual fraction ≠ 0 := by
  intro residualZero
  have identity := remainder_toGaussian fraction
  rw [residualZero, RFAP.ConstructiveGaussian.Gaussian.zero_mul] at identity
  exact remainderNonzero (toGaussian_eq_zero.mp identity)

/-- One nonterminal Hurwitz transition, `z ↦ 1/(z-nearest(z))`. -/
def next (fraction : Fraction)
    (remainderNonzero : remainder fraction ≠ 0) : Fraction :=
  ⟨fraction.denominator, remainder fraction, remainderNonzero⟩

@[simp] theorem next_numerator (fraction : Fraction)
    (remainderNonzero : remainder fraction ≠ 0) :
    (next fraction remainderNonzero).numerator = fraction.denominator := rfl

@[simp] theorem next_denominator (fraction : Fraction)
    (remainderNonzero : remainder fraction ≠ 0) :
    (next fraction remainderNonzero).denominator = remainder fraction := rfl

/-- Exact semantic transition of one nonterminal Hurwitz clause. -/
theorem next_value (fraction : Fraction)
    (remainderNonzero : remainder fraction ≠ 0) :
    (next fraction remainderNonzero).value = (residual fraction)⁻¹ := by
  have remainderGaussianNonzero : toGaussian (remainder fraction) ≠ 0 := by
    intro zero
    exact remainderNonzero (toGaussian_eq_zero.mp zero)
  apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
    remainderGaussianNonzero
  calc
    (next fraction remainderNonzero).value * toGaussian (remainder fraction) =
        toGaussian fraction.denominator :=
      (next fraction remainderNonzero).value_mul_denominator
    _ = (residual fraction)⁻¹ * toGaussian (remainder fraction) := by
      rw [remainder_toGaussian,
        ← RFAP.ConstructiveGaussian.Gaussian.mul_assoc,
        RFAP.ConstructiveGaussian.Gaussian.inv_eq,
        RFAP.ConstructiveGaussian.Gaussian.inv_mul _
          (residual_ne_zero remainderNonzero),
        RFAP.ConstructiveGaussian.Gaussian.one_mul]

/-- Exact natural-norm relation for the integral remainder. -/
theorem remainder_norm_identity (fraction : Fraction) :
    (normNat (remainder fraction) : Coordinate) =
      normSq (residual fraction) *
        (normNat fraction.denominator : Coordinate) := by
  rw [← normSq_toGaussian, remainder_toGaussian, normSq_mul,
    normSq_toGaussian]

/-- The integral remainder quadrance is at most half the old denominator
quadrance.  This is the natural-number form used to count the recursion. -/
theorem twice_remainder_norm_le_denominator (fraction : Fraction) :
    2 * normNat (remainder fraction) ≤ normNat fraction.denominator := by
  apply (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
  have denominatorNonnegative : (0 : Coordinate) ≤
      (normNat fraction.denominator : Coordinate) := by
    exact RFAP.ConstructiveFraction.natCast_le_direct (Nat.zero_le _)
  have residualBound :=
    RFAP.HurwitzNearest.remainder_normSq_le_half fraction.value
  have scaledBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      residualBound denominatorNonnegative
  calc
    ((2 * normNat (remainder fraction) : Nat) : Coordinate) =
        2 * (normNat (remainder fraction) : Coordinate) := by
      rw [Nat.cast_mul, Nat.cast_ofNat]
    _ = 2 *
        (normSq (residual fraction) *
          (normNat fraction.denominator : Coordinate)) := by
      rw [remainder_norm_identity]
    _ ≤ 2 *
        ((1 / 2 : Coordinate) *
          (normNat fraction.denominator : Coordinate)) := by
      exact RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_left_direct
        scaledBound (by decide)
    _ = ((2 : Coordinate) * (1 / 2)) *
        (normNat fraction.denominator : Coordinate) := by ring1
    _ = (normNat fraction.denominator : Coordinate) := by
      have twoHalf : (2 : Coordinate) * (1 / 2) = 1 := by decide
      rw [twoHalf, RFAP.ConstructiveFraction.one_mul]

/-- Nearest-Gaussian-integer division strictly decreases denominator
quadrance in one step. -/
theorem remainder_norm_lt_denominator (fraction : Fraction) :
    normNat (remainder fraction) < normNat fraction.denominator := by
  have denominatorPositive :
      (0 : Coordinate) < (normNat fraction.denominator : Coordinate) :=
    RFAP.ConstructiveFraction.natCast_pos_direct
      (normNat_pos fraction.denominatorNonzero)
  have residualBound :=
    RFAP.HurwitzNearest.remainder_normSq_le_half fraction.value
  have scaledBound :=
    RFAP.ConstructiveFraction.mul_le_mul_of_nonneg_right_direct
      residualBound denominatorPositive.le
  have halfStrict :=
    RFAP.ConstructiveFraction.mul_lt_mul_of_pos_right_direct
      (show (1 / 2 : Coordinate) < 1 by decide) denominatorPositive
  have castStrict :
      (normNat (remainder fraction) : Coordinate) <
        (normNat fraction.denominator : Coordinate) := by
    calc
      (normNat (remainder fraction) : Coordinate) =
          normSq (residual fraction) *
            (normNat fraction.denominator : Coordinate) :=
        remainder_norm_identity fraction
      _ ≤ (1 / 2 : Coordinate) *
          (normNat fraction.denominator : Coordinate) := scaledBound
      _ < 1 * (normNat fraction.denominator : Coordinate) := halfStrict
      _ = (normNat fraction.denominator : Coordinate) := by ring1
  exact (RFAP.ConstructiveFraction.natCast_lt_iff_direct).1 castStrict

/-- A direct quadrance bound for the digit selected in one Euclidean step. -/
theorem digit_norm_le (fraction : Fraction) :
    normNat (digit fraction) ≤
      2 * (normNat fraction.numerator + normNat fraction.denominator) := by
  have productBound :
      normNat (digit fraction) * normNat fraction.denominator ≤
        2 * (normNat fraction.numerator + normNat (remainder fraction)) := by
    apply (RFAP.ConstructiveFraction.natCast_le_iff_direct).1
    calc
      ((normNat (digit fraction) * normNat fraction.denominator : Nat) :
          Coordinate) =
          normSq
            (toGaussian (digit fraction) *
              toGaussian fraction.denominator) := by
        rw [Nat.cast_mul, ← normSq_toGaussian, ← normSq_toGaussian,
          normSq_mul]
      _ = normSq
          (toGaussian fraction.numerator -
            toGaussian (remainder fraction)) := by
        have division := digit_mul_denominator_add_remainder fraction
        have rearranged :
            digit fraction * fraction.denominator =
              fraction.numerator - remainder fraction := by
          calc
            digit fraction * fraction.denominator =
                (digit fraction * fraction.denominator + remainder fraction) -
                  remainder fraction := by
              apply RFAP.ConstructiveGaussianHeight.GaussianInt.ext <;>
                simp only [
                  RFAP.ConstructiveGaussianHeight.GaussianInt.add_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.add_im,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.sub_re,
                  RFAP.ConstructiveGaussianHeight.GaussianInt.sub_im] <;>
                ring1
            _ = fraction.numerator - remainder fraction := by rw [division]
        rw [← toGaussian_mul, rearranged, toGaussian_sub]
      _ ≤ 2 *
          (normSq (toGaussian fraction.numerator) +
            normSq (toGaussian (remainder fraction))) :=
        normSq_sub_le_two _ _
      _ = ((2 *
          (normNat fraction.numerator + normNat (remainder fraction)) : Nat) :
            Coordinate) := by
        rw [normSq_toGaussian, normSq_toGaussian, Nat.cast_mul,
          Nat.cast_add, Nat.cast_ofNat]
  have remainderLe :
      normNat (remainder fraction) ≤ normNat fraction.denominator :=
    (remainder_norm_lt_denominator fraction).le
  have denominatorPositive := normNat_pos fraction.denominatorNonzero
  calc
    normNat (digit fraction) ≤
        normNat (digit fraction) * normNat fraction.denominator := by
      exact Nat.le_mul_of_pos_right _ denominatorPositive
    _ ≤ 2 *
        (normNat fraction.numerator + normNat (remainder fraction)) :=
      productBound
    _ ≤ 2 *
        (normNat fraction.numerator + normNat fraction.denominator) := by
      exact Nat.mul_le_mul_left 2 (Nat.add_le_add_left remainderLe _)

/-- A source-only quadrance envelope for every digit generated from this
fraction. -/
def digitNormBudget (fraction : Fraction) : Nat :=
  max
    (2 * (normNat fraction.numerator + normNat fraction.denominator))
    (4 * normNat fraction.denominator)

theorem digit_norm_le_budget (fraction : Fraction) :
    normNat (digit fraction) ≤ digitNormBudget fraction :=
  (digit_norm_le fraction).trans (le_max_left _ _)

theorem next_digitNormBudget_le {fraction : Fraction}
    (nonterminal : remainder fraction ≠ 0) :
    digitNormBudget (next fraction nonterminal) ≤ digitNormBudget fraction := by
  have remainderLe :
      normNat (remainder fraction) ≤ normNat fraction.denominator :=
    (remainder_norm_lt_denominator fraction).le
  apply max_le
  · calc
      2 *
          (normNat (next fraction nonterminal).numerator +
            normNat (next fraction nonterminal).denominator) =
          2 *
            (normNat fraction.denominator +
              normNat (remainder fraction)) := rfl
      _ ≤ 4 * normNat fraction.denominator := by omega
      _ ≤ digitNormBudget fraction := le_max_right _ _
  · calc
      4 * normNat (next fraction nonterminal).denominator =
          4 * normNat (remainder fraction) := rfl
      _ ≤ 4 * normNat fraction.denominator :=
        Nat.mul_le_mul_left 4 remainderLe
      _ ≤ digitNormBudget fraction := le_max_right _ _

theorem remainder_width_step {fraction : Fraction}
    (nonterminal : remainder fraction ≠ 0) :
    Nat.log2 (normNat (remainder fraction)) + 1 ≤
      Nat.log2 (normNat fraction.denominator) := by
  have remainderPositive := normNat_pos nonterminal
  have denominatorPositive := normNat_pos fraction.denominatorNonzero
  exact (Nat.le_log2 (Nat.ne_of_gt denominatorPositive)).2
    (calc
      2 ^ (Nat.log2 (normNat (remainder fraction)) + 1) =
          2 * 2 ^ Nat.log2 (normNat (remainder fraction)) := by
        rw [pow_succ, Nat.mul_comm]
      _ ≤ 2 * normNat (remainder fraction) :=
        Nat.mul_le_mul_left 2
          (Nat.log2_self_le (Nat.ne_of_gt remainderPositive))
      _ ≤ normNat fraction.denominator :=
        twice_remainder_norm_le_denominator fraction)

/-- Integral numerator/denominator pair of a finite continued fraction. -/
structure ConvergentPair where
  numerator : GaussianInt
  denominator : GaussianInt
deriving DecidableEq, Repr

/-- Add one partial quotient to the front of a tail continuant. -/
def prepend (head : GaussianInt) (tail : ConvergentPair) : ConvergentPair :=
  ⟨head * tail.numerator + tail.denominator, tail.numerator⟩

/-- Standard finite continuant, with the empty tail represented by infinity
`1/0`.  Thus `continuant [a] = a/1`. -/
def continuant : List GaussianInt → ConvergentPair
  | [] => ⟨1, 0⟩
  | head :: tail => prepend head (continuant tail)

@[simp] theorem continuant_nil : continuant [] = ⟨1, 0⟩ := rfl

@[simp] theorem continuant_cons (head : GaussianInt)
    (tail : List GaussianInt) :
    continuant (head :: tail) = prepend head (continuant tail) := rfl

/-- A finite digit list together with its exact reconstruction of the source
Gaussian rational. -/
structure Encoding (source : Fraction) where
  digits : List GaussianInt
  nonempty : digits ≠ []
  length_le_width :
    digits.length ≤ Nat.log2 (normNat source.denominator) + 1
  digit_norm_le : ∀ candidate ∈ digits,
    normNat candidate ≤ digitNormBudget source
  denominatorNonzero : (continuant digits).denominator ≠ 0
  reconstruct :
    source.value * toGaussian (continuant digits).denominator =
      toGaussian (continuant digits).numerator

/-- Total finite Hurwitz encoding with an exact continuant certificate. -/
def encodeResult (fraction : Fraction) : Encoding fraction := by
  if terminal : remainder fraction = 0 then
    have integerIdentity :
        digit fraction * fraction.denominator = fraction.numerator := by
      have division := digit_mul_denominator_add_remainder fraction
      rw [terminal] at division
      simpa only [RFAP.ConstructiveGaussianHeight.GaussianInt.add_zero]
        using division
    have valueDigit : fraction.value = toGaussian (digit fraction) := by
      apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
        fraction.denominatorGaussianNonzero
      calc
        fraction.value * toGaussian fraction.denominator =
            toGaussian fraction.numerator :=
          fraction.value_mul_denominator
        _ = toGaussian (digit fraction * fraction.denominator) := by
          rw [integerIdentity]
        _ = toGaussian (digit fraction) *
            toGaussian fraction.denominator := toGaussian_mul _ _
    exact
      { digits := [digit fraction]
        nonempty := by simp
        length_le_width := by
          simp only [List.length_cons, List.length_nil]
          omega
        digit_norm_le := by
          intro candidate member
          simp only [List.mem_singleton] at member
          rw [member]
          exact digit_norm_le_budget fraction
        denominatorNonzero := by
          intro oneZero
          have realZero := congrArg
            RFAP.ConstructiveGaussianHeight.GaussianInt.re oneZero
          exact (show (1 : Int) ≠ 0 by decide) realZero
        reconstruct := by
          simpa only [continuant, prepend, toGaussian_one,
            RFAP.ConstructiveGaussian.Gaussian.mul_one,
            RFAP.ConstructiveGaussianHeight.GaussianInt.mul_one,
            RFAP.ConstructiveGaussianHeight.GaussianInt.add_zero]
            using valueDigit }
  else
    let nextFraction := next fraction terminal
    let tail := encodeResult nextFraction
    let tailPair := continuant tail.digits
    have tailDenominatorGaussianNonzero :
        toGaussian tailPair.denominator ≠ 0 := by
      intro zero
      exact tail.denominatorNonzero (toGaussian_eq_zero.mp zero)
    have nextValueNonzero : nextFraction.value ≠ 0 :=
      nextFraction.value_ne_zero fraction.denominatorNonzero
    have tailNumeratorNonzero : tailPair.numerator ≠ 0 := by
      intro numeratorZero
      apply nextValueNonzero
      apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
        tailDenominatorGaussianNonzero
      calc
        nextFraction.value * toGaussian tailPair.denominator =
            toGaussian tailPair.numerator := tail.reconstruct
        _ = 0 := by rw [numeratorZero, toGaussian_zero]
        _ = 0 * toGaussian tailPair.denominator := by
          rw [RFAP.ConstructiveGaussian.Gaussian.zero_mul]
    have residualMulNumerator :
        residual fraction * toGaussian tailPair.numerator =
          toGaussian tailPair.denominator := by
      calc
        residual fraction * toGaussian tailPair.numerator =
            residual fraction *
              (nextFraction.value * toGaussian tailPair.denominator) := by
          rw [tail.reconstruct]
        _ = residual fraction *
            ((residual fraction)⁻¹ * toGaussian tailPair.denominator) := by
          rw [next_value]
        _ = (residual fraction * (residual fraction)⁻¹) *
            toGaussian tailPair.denominator := by
          rw [RFAP.ConstructiveGaussian.Gaussian.mul_assoc]
        _ = toGaussian tailPair.denominator := by
          rw [RFAP.ConstructiveGaussian.Gaussian.inv_eq,
            RFAP.ConstructiveGaussian.Gaussian.mul_inv _
              (residual_ne_zero terminal),
            RFAP.ConstructiveGaussian.Gaussian.one_mul]
    exact
      { digits := digit fraction :: tail.digits
        nonempty := by simp
        length_le_width := by
          simp only [List.length_cons]
          calc
            tail.digits.length + 1 ≤
                (Nat.log2 (normNat (remainder fraction)) + 1) + 1 := by
              exact Nat.add_le_add_right tail.length_le_width 1
            _ ≤ Nat.log2 (normNat fraction.denominator) + 1 := by
              exact Nat.add_le_add_right (remainder_width_step terminal) 1
        digit_norm_le := by
          intro candidate member
          simp only [List.mem_cons] at member
          rcases member with head | tailMember
          · rw [head]
            exact digit_norm_le_budget fraction
          · exact (tail.digit_norm_le candidate tailMember).trans
              (next_digitNormBudget_le terminal)
        denominatorNonzero := by
          exact tailNumeratorNonzero
        reconstruct := by
          change fraction.value * toGaussian tailPair.numerator =
            toGaussian
              (digit fraction * tailPair.numerator + tailPair.denominator)
          calc
            fraction.value * toGaussian tailPair.numerator =
                (toGaussian (digit fraction) + residual fraction) *
                  toGaussian tailPair.numerator := by
              rw [value_eq_digit_add_residual]
            _ = toGaussian (digit fraction) *
                  toGaussian tailPair.numerator +
                residual fraction * toGaussian tailPair.numerator :=
              RFAP.ConstructiveGaussian.Gaussian.right_distrib _ _ _
            _ = toGaussian (digit fraction * tailPair.numerator) +
                toGaussian tailPair.denominator := by
              rw [toGaussian_mul, residualMulNumerator]
            _ = toGaussian
                (digit fraction * tailPair.numerator + tailPair.denominator) :=
              (toGaussian_add _ _).symm }
termination_by normNat fraction.denominator
decreasing_by exact remainder_norm_lt_denominator fraction

/-- The executable finite Hurwitz digit list. -/
def encode (fraction : Fraction) : List GaussianInt :=
  (encodeResult fraction).digits

theorem encode_nonempty (fraction : Fraction) : encode fraction ≠ [] :=
  (encodeResult fraction).nonempty

theorem encode_length_le_width (fraction : Fraction) :
    (encode fraction).length ≤
      Nat.log2 (normNat fraction.denominator) + 1 :=
  (encodeResult fraction).length_le_width

theorem encode_digit_norm_le (fraction : Fraction) {candidate : GaussianInt}
    (member : candidate ∈ encode fraction) :
    normNat candidate ≤ digitNormBudget fraction :=
  (encodeResult fraction).digit_norm_le candidate member

theorem encode_denominatorNonzero (fraction : Fraction) :
    (continuant (encode fraction)).denominator ≠ 0 :=
  (encodeResult fraction).denominatorNonzero

theorem encode_reconstruct (fraction : Fraction) :
    fraction.value * toGaussian (continuant (encode fraction)).denominator =
      toGaussian (continuant (encode fraction)).numerator :=
  (encodeResult fraction).reconstruct

end RFAP.HurwitzRational
