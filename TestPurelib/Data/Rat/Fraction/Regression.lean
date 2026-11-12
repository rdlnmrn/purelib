module
public import Purelib.Examples.Data.Rat.Fraction.Presentation
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Nat.Coprime.Presentation
meta import Purelib.Data.Nat.Coprime.Presentation
import Purelib.Data.Rat.Fraction.Canonical.Presentation
meta import Purelib.Data.Rat.Fraction.Canonical.Presentation
import Purelib.Data.Rat.Fraction
meta import Purelib.Data.Rat.Fraction

@[expose] public section

/-!
# Executable regression table for canonical fractions

These closed checks cover scalar normalization and arithmetic. Each equality is
decided by the kernel over structural canonical records; building the module also compiles the underlying executable
normalizers and arithmetic operations.
-/

namespace TestPurelib.Data.Rat.Fraction.Regression

open Purelib.Data.Rat.Fraction
open Purelib.Data.Nat
open Purelib.Examples.Data.Rat.Fraction.Presentation

private def sixNinths : RawFraction := ⟨6, 9, by decide⟩

example (fraction : RawFraction) :
    Canonical.Presentation.read
        (Canonical.Presentation.quote (normalize fraction) (normalizeCertificate fraction)) =
      normalize fraction :=
  Canonical.Presentation.read_quote _ _

example (left right : Canonical.Presentation.Display) (same : left.val.1 = right.val.1) :
    Canonical.Presentation.read left = Canonical.Presentation.read right :=
  (Canonical.Presentation.same_iff_read_eq left right).mp same

/-- info: (true, true, true, true) -/
#guard_msgs in
#eval (let certificate := normalizeCertificate sixNinths
  let code : Canonical.Presentation.Code := ((2, 3), (certificate.left, certificate.right))
  ((match Canonical.Presentation.check code with
      | .valid positive identity =>
        Canonical.Presentation.read ⟨code, positive, identity⟩ == normalize sixNinths
      | _ => false),
    (match Canonical.Presentation.check ((2, 0), (0, 0)) with
      | .zeroDenominator _ => true | _ => false),
    (match Canonical.Presentation.check ((2, 3), (0, 0)) with
      | .invalidCoefficients _ _ => true | _ => false),
    (match Canonical.Presentation.check ((2, 3), (-1, 1)),
        Canonical.Presentation.check ((2, 3), (2, -1)) with
      | .valid p₁ h₁, .valid p₂ h₂ =>
        Canonical.Presentation.read ⟨((2, 3), (-1, 1)), p₁, h₁⟩ ==
          Canonical.Presentation.read ⟨((2, 3), (2, -1)), p₂, h₂⟩
      | _, _ => false)))

/-- info: (true, true) -/
#guard_msgs in
#eval (match Canonical.Presentation.check ((2, 3), (-1, 1)),
    Canonical.Presentation.check ((2, 3), (2, -1)),
    Canonical.Presentation.check ((1, 2), (1, 0)) with
  | .valid p₁ h₁, .valid p₂ h₂, .valid p₃ h₃ =>
    let left : Canonical.Presentation.Display := ⟨((2, 3), (-1, 1)), p₁, h₁⟩
    let equal : Canonical.Presentation.Display := ⟨((2, 3), (2, -1)), p₂, h₂⟩
    let different : Canonical.Presentation.Display := ⟨((1, 2), (1, 0)), p₃, h₃⟩
    ((match Canonical.Presentation.compare left equal with
      | .isTrue _ => true | .isFalse _ => false),
     (match Canonical.Presentation.compare left different with
      | .isTrue _ => false | .isFalse _ => true))
  | _, _, _ => (false, false))

example (left : Nat) {right : Nat} (positive : 0 < right) :
    Coprime.Presentation.read
        (Coprime.Presentation.quote (GCD.Coprime.quotientCoprimeCertificate left positive)) =
      GCD.Coprime.quotientCoprimeCertificate left positive :=
  Coprime.Presentation.read_quote _

example : Coprime.Presentation.read
    (Coprime.Presentation.quote (normalizeCertificate sixNinths)) =
      normalizeCertificate sixNinths :=
  Coprime.Presentation.read_quote _

/-- info: (true, true, true, true, true) -/
#guard_msgs in
#eval (let quotient := GCD.Coprime.quotientCoprimeCertificate 6 (rightInput := 9) (by decide)
  let original := GCD.Extended.compute 6 9
  let normalized := normalizeCertificate sixNinths
  let code := (Coprime.Presentation.quote quotient).val
  ((match Coprime.Presentation.check 2 3 code with
      | .valid _ => true | .invalid _ => false),
    (match Coprime.Presentation.check 6 9 code with
      | .invalid _ => true | .valid _ => false),
    quotient.left == original.left && quotient.right == original.right,
    normalized.left == quotient.left && normalized.right == quotient.right,
    (normalize sixNinths).num == 2 && (normalize sixNinths).den == 3))

/-- Read the answer of a proof-bearing decision without discarding its computation. -/
private def decisionResult {proposition : Prop} : Decidable proposition → Bool
  | .isTrue _ => true
  | .isFalse _ => false

/-- The public comparison accepts distinct equivalent fraction displays. -/
example : decisionResult (Presentation.compare half twoQuarters) = true := by decide

/-- The named presentation exposes the same cross-product decision. -/
example : decisionResult (Presentation.fraction.compare half twoQuarters) = true := by decide

/-- Direct and named recognition return proof-bearing acceptance and rejection. -/
example : decisionResult (Presentation.recognize (-1, 2)) = true ∧
    decisionResult (Presentation.fraction.recognize (1, 2)) = true ∧
    decisionResult (Presentation.fraction.recognize (1, 0)) = false := by decide

/-- The public comparison rejects unequal positive-denominator displays. -/
example : decisionResult (Presentation.compare half ⟨(2, 3), by decide⟩) = false := by decide

/-- Negative numerators pass the actual positive-denominator checker. -/
example : (match Presentation.check (-1, 2) with
    | .valid _ => true
    | .zeroDenominator _ => false) = true := by decide

/-- Different positive denominators present the same canonical zero. -/
example : Presentation.read ⟨(0, 1), by decide⟩ = Presentation.read ⟨(0, 9), by decide⟩ :=
  (Presentation.same_iff_read_eq _ _).mp (by decide)

/-- Both zero displays read back to the original canonical zero. -/
example : Presentation.read ⟨(0, 1), by decide⟩ = zero ∧
    Presentation.read ⟨(0, 9), by decide⟩ = zero :=
  ⟨normalize_zero, normalize_zero_ninths⟩

/-- The checker identifies denominator zero as its specific invalidity. -/
example : (match Presentation.check (1, 0) with
    | .valid _ => false
    | .zeroDenominator _ => true) = true := by decide

/-- The original gcd normalization reduces the unreduced display to one half. -/
example : (Presentation.normalized twoQuarters).val = (1, 2) := by decide

/-- Quoting an original rational retains its exact readback. -/
example : Presentation.read (Presentation.quote halfValue) = halfValue :=
  Presentation.read_quote halfValue

/-- The canonical rational one thirtieth. -/
private def oneThirtieth : Rational :=
  ⟨1, 30, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

/-- The canonical rational one forty-second. -/
private def oneFortySecond : Rational :=
  ⟨1, 42, by decide, ⟨⟨1, 0, by decide⟩⟩⟩

/-- The canonical rational two thirty-fifths. -/
private def twoThirtyFifths : Rational :=
  ⟨2, 35, by decide, ⟨⟨18, -1, by decide⟩⟩⟩

/-- The canonical rational two thirds. -/
private def twoThirds : Rational :=
  ⟨2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩

/-- The canonical rational three halves. -/
private def threeHalves : Rational :=
  ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩

/-- The canonical rational negative two thirds. -/
private def negativeTwoThirds : Rational :=
  ⟨-2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩

/-- The canonical rational negative three halves. -/
private def negativeThreeHalves : Rational :=
  ⟨-3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩

/-- Kernel evaluation adds one thirtieth and one forty-second to two thirty-fifths. -/
theorem regression_shared_denominator_addition :
    let oneThirtieth : Rational :=
      ⟨1, 30, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
    let oneFortySecond : Rational :=
      ⟨1, 42, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
    let twoThirtyFifths : Rational :=
      ⟨2, 35, by decide, ⟨⟨18, -1, by decide⟩⟩⟩
    oneThirtieth + oneFortySecond = twoThirtyFifths := by decide

/-- Kernel evaluation inverts two thirds to three halves. -/
theorem regression_positive_inverse :
    let twoThirds : Rational :=
      ⟨2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩
    let threeHalves : Rational :=
      ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩
    twoThirds⁻¹ = threeHalves := by decide

/-- Kernel evaluation inverts negative two thirds to negative three halves. -/
theorem regression_negative_inverse :
    let negativeTwoThirds : Rational :=
      ⟨-2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩
    let negativeThreeHalves : Rational :=
      ⟨-3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩
    negativeTwoThirds⁻¹ = negativeThreeHalves := by decide

/-- The total canonical rational reciprocal maps zero to zero. -/
theorem regression_zero_inverse : (0 : Rational)⁻¹ = 0 := by decide

/-- Normalizing six eighths and three quarters yields the identical canonical rational. -/
theorem regression_equivalent_displays :
    normalize ⟨6, 8, by decide⟩ = normalize ⟨3, 4, by decide⟩ := by decide

/-- The integer embedding of negative seven is below the natural embedding of two. -/
theorem regression_cast_and_order :
    ((-7 : Int) : Rational) < ((2 : Nat) : Rational) := by decide

/-- Check the complete canonical outputs of integer and mixed-denominator arithmetic.

The table covers signed, zero, unit and cancelling integer inputs, followed by
both argument orders of addition and multiplication with a nonunit denominator. -/
def denominatorOneArithmeticPassed : Bool :=
  let zero := Cast.fromInt 0
  let one := Cast.fromInt 1
  let negativeOne := Cast.fromInt (-1)
  let negative := Cast.fromInt (-7)
  let positive := Cast.fromInt 3
  let two := Cast.fromInt 2
  let negativeTwo := Cast.fromInt (-2)
  let half := normalize ⟨1, 2, by decide⟩
  let fiveHalves := normalize ⟨5, 2, by decide⟩
  let negativeThreeHalves := normalize ⟨-3, 2, by decide⟩
  decide (negative + positive = Cast.fromInt (-4)) &&
    decide (positive + negative = Cast.fromInt (-4)) &&
    decide (negative + Cast.fromInt 7 = zero) &&
    decide (zero + negative = negative) && decide (negative + zero = negative) &&
    decide (negative * positive = Cast.fromInt (-21)) &&
    decide (positive * negative = Cast.fromInt (-21)) &&
    decide (negative * negativeOne = Cast.fromInt 7) &&
    decide (negativeOne * negative = Cast.fromInt 7) &&
    decide (one * negative = negative) && decide (negative * one = negative) &&
    decide (zero * negative = zero) && decide (negative * zero = zero) &&
    decide (two + half = fiveHalves) && decide (half + two = fiveHalves) &&
    decide (two * half = one) && decide (half * two = one) &&
    decide (negativeTwo + half = negativeThreeHalves) &&
    decide (half + negativeTwo = negativeThreeHalves) &&
    decide (negativeTwo * half = negativeOne) && decide (half * negativeTwo = negativeOne) &&
    decide (zero + half = half) && decide (half + zero = half) &&
    decide (zero * half = zero) && decide (half * zero = zero)

/-- Kernel evaluation checks the small denominator-one and general-fallback arithmetic table. -/
theorem regression_denominator_one_arithmetic : denominatorOneArithmeticPassed = true := by
  decide +kernel

/-- One executable Boolean used by the compiled regression runner. -/
def compiledRegressionPassed : Bool :=
  let twoThirdsDisplay : Presentation.Display := ⟨(2, 3), by decide⟩
  let oneThirtieth : Rational :=
    ⟨1, 30, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
  let oneFortySecond : Rational :=
    ⟨1, 42, by decide, ⟨⟨1, 0, by decide⟩⟩⟩
  let twoThirtyFifths : Rational :=
    ⟨2, 35, by decide, ⟨⟨18, -1, by decide⟩⟩⟩
  let twoThirds : Rational :=
    ⟨2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩
  let threeHalves : Rational :=
    ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩
  let negativeTwoThirds : Rational :=
    ⟨-2, 3, by decide, ⟨⟨-1, 1, by decide⟩⟩⟩
  let negativeThreeHalves : Rational :=
    ⟨-3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩
  denominatorOneArithmeticPassed &&
    (match Presentation.compare half twoQuarters with
      | .isTrue _ => true
      | .isFalse _ => false) &&
    (match Presentation.fraction.compare half twoQuarters with
      | .isTrue _ => true
      | .isFalse _ => false) &&
    (match Presentation.compare half twoThirdsDisplay with
      | .isTrue _ => false
      | .isFalse _ => true) &&
    (match Presentation.recognize (-1, 2) with
      | .isTrue _ => true
      | .isFalse _ => false) &&
    (match Presentation.fraction.recognize (1, 0) with
      | .isTrue _ => false
      | .isFalse _ => true) &&
    (match Presentation.check (-1, 2) with
      | .valid _ => true
      | .zeroDenominator _ => false) &&
    (match Presentation.check (1, 0) with
      | .valid _ => false
      | .zeroDenominator _ => true) &&
    decide (Presentation.read ⟨(0, 1), by decide⟩ =
      Presentation.read ⟨(0, 9), by decide⟩) &&
    decide ((Presentation.normalized twoQuarters).val = (1, 2)) &&
    decide (Presentation.read (Presentation.quote halfValue) = halfValue) &&
    decide (oneThirtieth + oneFortySecond = twoThirtyFifths) &&
    decide (twoThirds⁻¹ = threeHalves) &&
    decide (negativeTwoThirds⁻¹ = negativeThreeHalves) &&
    decide ((0 : Rational)⁻¹ = 0) &&
    decide (normalize ⟨6, 8, by decide⟩ = normalize ⟨3, 4, by decide⟩) &&
    decide (((-7 : Int) : Rational) < ((2 : Nat) : Rational))

/-- The executable canonical rational arithmetic and order regression table passes. -/
theorem compiledRegressionPassed_eq_true : compiledRegressionPassed = true := by
  decide

end TestPurelib.Data.Rat.Fraction.Regression
