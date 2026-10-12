module
public import Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant
public import Purelib.Data.ComplexContinuedFraction.Hurwitz.Step
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Division.Nearest
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Embedding
import Purelib.Data.Gaussian.Field
import Purelib.Data.GaussianInt.Pair.Basic
public import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
public import Mathlib.Tactic.NormNum.Result

meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.List.Membership

/-!
# Certified finite Hurwitz encoding

The nearest-integer step retains its exact selected successor and cached tail.
The installed natural fixpoint uses the retained logarithmic denominator width.
The digit and continuant accounts retain their original statements; evaluator
measure setup is a separate cost.
-/

open Purelib.Data Purelib.Data.ComplexContinuedFraction Purelib.Data.Gaussian

public section
namespace Purelib.Data.ComplexContinuedFraction.Hurwitz

set_option genInjectivity false in
/-- Retain a finite Hurwitz digit list with length, digit-size and exact reconstruction evidence.

The list is nonempty, its length is bounded by the source denominator norm's binary logarithm plus one, and every digit
meets the source budget. Its exact continuant has nonzero denominator and reconstructs the original Gaussian readback.
-/
structure Encoding (source : GaussianInt.Fraction) where
  /-- The retained nonempty list of Gaussian-integer Hurwitz digits. -/ digits : List
    GaussianInt.Fraction.Basic.Integer
  /-- Evidence that the exact retained digit list is not empty. -/ nonempty : digits ≠ []
  /-- The retained list length is at most the source denominator norm's binary logarithm plus one. -/ length_le_width :
    digits.length ≤ Nat.log2 (GaussianInt.normNat source.denominator) + 1
  /-- Every member of the retained digit list satisfies the original source digit budget. -/ digit_norm_le : ∀ candidate
    ∈ digits,
    GaussianInt.normNat candidate ≤ Hurwitz.Step.digitNormBudget source
  /-- Evidence that the exact retained list's continuant denominator is nonzero. -/ denominatorNonzero :
    (Hurwitz.Continuant.continuant digits).denominator ≠ 0
  /-- The original source value times the embedded continuant denominator equals its embedded numerator. -/ reconstruct
    :
    source.value * GaussianInt.toGaussian (Hurwitz.Continuant.continuant digits).denominator =
      GaussianInt.toGaussian (Hurwitz.Continuant.continuant digits).numerator

constructive_injectivity Encoding

namespace Encoding

/-- Assemble one certified nearest-integer step with its retained successor callback.

A zero remainder retains one selected digit. Otherwise the callback supplies the
same successor's complete tail record, whose continuant and bounds are reused.
The relation and decrease evidence constrain only that callback. -/
@[expose] def step
    (relation : GaussianInt.Fraction → GaussianInt.Fraction → Prop)
    (fraction : GaussianInt.Fraction)
    (decreases : ∀ nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0,
      relation (Hurwitz.Step.next fraction nonterminal) fraction)
    (recurse : ∀ next : GaussianInt.Fraction,
      relation next fraction → Encoding next) :
    Encoding fraction := by
  if terminal : GaussianInt.Division.Nearest.remainder fraction = 0 then
    have integerIdentity :
        GaussianInt.Division.Nearest.digit fraction * fraction.denominator = fraction.numerator := by
      have division := GaussianInt.Division.Nearest.digit_mul_denominator_add_remainder fraction
      rw [terminal] at division
      simpa only [GaussianInt.add_zero]
        using division
    have valueDigit : fraction.value = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit fraction) := by
      apply Field.mul_right_cancel_of_ne
        fraction.denominatorGaussianNonzero
      calc
        fraction.value * GaussianInt.toGaussian fraction.denominator =
            GaussianInt.toGaussian fraction.numerator :=
          fraction.value_mul_denominator
        _ = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit fraction * fraction.denominator) := by
          rw [integerIdentity]
        _ = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit fraction) *
            GaussianInt.toGaussian fraction.denominator := GaussianInt.toGaussian_mul _ _
    exact
      { digits := [GaussianInt.Division.Nearest.digit fraction]
        nonempty := by intro impossible; nomatch impossible
        length_le_width := by
          simp only [List.length_cons, List.length_nil]
          omega
        digit_norm_le := by
          intro candidate member
          have member := List.Membership.mem_singleton.mp member
          rw [member]
          exact Hurwitz.Step.digit_norm_le_budget fraction
        denominatorNonzero := by
          intro oneZero
          have realZero := congrArg
            GaussianInt.re oneZero
          exact (show (1 : Int) ≠ 0 by decide) realZero
        reconstruct := by
          simpa only [Hurwitz.Continuant.continuant, Hurwitz.Continuant.prepend, GaussianInt.toGaussian_one,
            Basic.mul_one,
            GaussianInt.mul_one,
            GaussianInt.add_zero]
            using valueDigit }
  else
    let nextFraction := Hurwitz.Step.next fraction terminal
    let tail := recurse nextFraction (decreases terminal)
    let tailPair := Hurwitz.Continuant.continuant tail.digits
    have tailDenominatorGaussianNonzero :
        GaussianInt.toGaussian tailPair.denominator ≠ 0 := by
      intro zero
      exact tail.denominatorNonzero (GaussianInt.toGaussian_eq_zero.mp zero)
    have nextValueNonzero : nextFraction.value ≠ 0 :=
      nextFraction.value_ne_zero fraction.denominatorNonzero
    have tailNumeratorNonzero : tailPair.numerator ≠ 0 := by
      intro numeratorZero
      apply nextValueNonzero
      apply Field.mul_right_cancel_of_ne
        tailDenominatorGaussianNonzero
      calc
        nextFraction.value * GaussianInt.toGaussian tailPair.denominator =
            GaussianInt.toGaussian tailPair.numerator := tail.reconstruct
        _ = 0 := by rw [numeratorZero, GaussianInt.toGaussian_zero]
        _ = 0 * GaussianInt.toGaussian tailPair.denominator := by
          rw [Basic.zero_mul]
    have residualMulNumerator :
        GaussianInt.Division.Nearest.residual fraction * GaussianInt.toGaussian tailPair.numerator =
          GaussianInt.toGaussian tailPair.denominator := by
      calc
        GaussianInt.Division.Nearest.residual fraction * GaussianInt.toGaussian tailPair.numerator =
            GaussianInt.Division.Nearest.residual fraction *
              (nextFraction.value * GaussianInt.toGaussian tailPair.denominator) := by
          rw [tail.reconstruct]
        _ = GaussianInt.Division.Nearest.residual fraction *
            ((GaussianInt.Division.Nearest.residual fraction)⁻¹ * GaussianInt.toGaussian tailPair.denominator) := by
          rw [Hurwitz.Step.next_value]
        _ = (GaussianInt.Division.Nearest.residual fraction * (GaussianInt.Division.Nearest.residual fraction)⁻¹) *
            GaussianInt.toGaussian tailPair.denominator := by
          rw [Basic.mul_assoc]
        _ = GaussianInt.toGaussian tailPair.denominator := by
          rw [Field.inv_eq,
            Field.mul_inv _
              (GaussianInt.Division.Nearest.residual_ne_zero terminal),
            Basic.one_mul]
    exact
      { digits := GaussianInt.Division.Nearest.digit fraction :: tail.digits
        nonempty := by intro impossible; nomatch impossible
        length_le_width := by
          simp only [List.length_cons]
          calc
            tail.digits.length + 1 ≤
                (Nat.log2 (GaussianInt.normNat (GaussianInt.Division.Nearest.remainder fraction)) + 1) + 1 := by
              exact Nat.add_le_add_right tail.length_le_width 1
            _ ≤ Nat.log2 (GaussianInt.normNat fraction.denominator) + 1 := by
              exact Nat.add_le_add_right (Hurwitz.Step.remainder_width_step terminal) 1
        digit_norm_le := by
          intro candidate member
          rcases List.Membership.mem_cons.mp member with head | tailMember
          · rw [head]
            exact Hurwitz.Step.digit_norm_le_budget fraction
          · exact Nat.le_trans (tail.digit_norm_le candidate tailMember)
              (Hurwitz.Step.next_digitNormBudget_le terminal)
        denominatorNonzero := by
          exact tailNumeratorNonzero
        reconstruct := by
          change fraction.value * GaussianInt.toGaussian tailPair.numerator =
            GaussianInt.toGaussian
              (GaussianInt.Division.Nearest.digit fraction * tailPair.numerator + tailPair.denominator)
          calc
            fraction.value * GaussianInt.toGaussian tailPair.numerator =
                (GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit fraction) +
                  GaussianInt.Division.Nearest.residual fraction) *
                  GaussianInt.toGaussian tailPair.numerator := by
              rw [GaussianInt.Division.Nearest.value_eq_digit_add_residual]
            _ = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit fraction) *
                  GaussianInt.toGaussian tailPair.numerator +
                GaussianInt.Division.Nearest.residual fraction * GaussianInt.toGaussian tailPair.numerator :=
              Basic.right_distrib _ _ _
            _ = GaussianInt.toGaussian (GaussianInt.Division.Nearest.digit fraction * tailPair.numerator) +
                GaussianInt.toGaussian tailPair.denominator := by
              rw [GaussianInt.toGaussian_mul, residualMulNumerator]
            _ = GaussianInt.toGaussian
                (GaussianInt.Division.Nearest.digit fraction * tailPair.numerator + tailPair.denominator) :=
              (GaussianInt.toGaussian_add _ _).symm }

/-- Equal retained digits determine the complete certified Encoding record. -/
private theorem record_eq {source : GaussianInt.Fraction}
    {left right : Encoding source}
    (same : left.digits = right.digits) : left = right := by
  cases left
  cases right
  cases same
  rfl

/-- Compare only the callback invocation at the original selected next fraction. -/
private theorem step_congr
    (firstRelation secondRelation : GaussianInt.Fraction → GaussianInt.Fraction → Prop)
    (fraction : GaussianInt.Fraction)
    (firstDecrease : ∀ h : GaussianInt.Division.Nearest.remainder fraction ≠ 0,
      firstRelation (Hurwitz.Step.next fraction h) fraction)
    (secondDecrease : ∀ h : GaussianInt.Division.Nearest.remainder fraction ≠ 0,
      secondRelation (Hurwitz.Step.next fraction h) fraction)
    (left : ∀ next, firstRelation next fraction → Encoding next)
    (right : ∀ next, secondRelation next fraction → Encoding next)
    (agree : ∀ h : GaussianInt.Division.Nearest.remainder fraction ≠ 0,
      left (Hurwitz.Step.next fraction h) (firstDecrease h) =
      right (Hurwitz.Step.next fraction h) (secondDecrease h)) :
    step firstRelation fraction firstDecrease left =
      step secondRelation fraction secondDecrease right := by
  apply record_eq
  unfold step
  split
  · rfl
  · rename_i nonterminal
    dsimp only
    exact congrArg
      (fun tail : Encoding (Hurwitz.Step.next fraction nonterminal) =>
        GaussianInt.Division.Nearest.digit fraction :: tail.digits)
      (agree nonterminal)

/-- The step specializes only its erased bound relation and proof witness. -/
private def measuredStep (measure : GaussianInt.Fraction → Nat)
    (decreases : ∀ fraction, ∀ h : GaussianInt.Division.Nearest.remainder fraction ≠ 0,
      measure (Hurwitz.Step.next fraction h) < measure fraction)
    (fraction : GaussianInt.Fraction)
    (recurse : ∀ next, measure next < measure fraction → Encoding next) :
    Encoding fraction :=
  step (fun next source => measure next < measure source) fraction (decreases fraction) recurse

/-- The original natural fixpoint, specialized to the retained descent measure. -/
private def fixed (measure : GaussianInt.Fraction → Nat)
    (decreases : ∀ fraction, ∀ h : GaussianInt.Division.Nearest.remainder fraction ≠ 0,
      measure (Hurwitz.Step.next fraction h) < measure fraction)
    (fraction : GaussianInt.Fraction) : Encoding fraction :=
  WellFounded.Nat.fix measure (measuredStep measure decreases) fraction

/-- Fuel sufficiency leaves the complete original selected record unchanged. -/
private theorem go_fuel_eq (measure : GaussianInt.Fraction → Nat)
    (decreases : ∀ fraction, ∀ h : GaussianInt.Division.Nearest.remainder fraction ≠ 0,
      measure (Hurwitz.Step.next fraction h) < measure fraction)
    (firstFuel : Nat) :
    ∀ (fraction : GaussianInt.Fraction) (secondFuel : Nat)
      (firstBound : measure fraction < firstFuel)
      (secondBound : measure fraction < secondFuel),
    WellFounded.Nat.fix.go measure (measuredStep measure decreases) firstFuel fraction firstBound =
      WellFounded.Nat.fix.go measure (measuredStep measure decreases) secondFuel fraction secondBound := by
  induction firstFuel with
  | zero =>
    intro fraction secondFuel firstBound secondBound
    exact False.elim (Nat.not_lt_zero _ firstBound)
  | succ firstFuel ih =>
    intro fraction secondFuel firstBound secondBound
    cases secondFuel with
    | zero => exact False.elim (Nat.not_lt_zero _ secondBound)
    | succ secondFuel =>
      delta WellFounded.Nat.fix.go measuredStep
      apply step_congr
      intro nonterminal
      exact ih (Hurwitz.Step.next fraction nonterminal) secondFuel _ _

/-- The retained fueled evaluator agrees with its complete fixpoint record. -/
private theorem go_eq_fixed (measure : GaussianInt.Fraction → Nat)
    (decreases : ∀ fraction, ∀ h : GaussianInt.Division.Nearest.remainder fraction ≠ 0,
      measure (Hurwitz.Step.next fraction h) < measure fraction)
    (fraction : GaussianInt.Fraction) (fuel : Nat) (bound : measure fraction < fuel) :
    WellFounded.Nat.fix.go measure (measuredStep measure decreases) fuel fraction bound =
      fixed measure decreases fraction := by
  delta fixed WellFounded.Nat.fix
  exact go_fuel_eq measure decreases fuel fraction _ bound _

/-- Unroll the complete selected record without extensionality. -/
private theorem fixed_unroll (measure : GaussianInt.Fraction → Nat)
    (decreases : ∀ fraction, ∀ h : GaussianInt.Division.Nearest.remainder fraction ≠ 0,
      measure (Hurwitz.Step.next fraction h) < measure fraction)
    (fraction : GaussianInt.Fraction) :
    fixed measure decreases fraction =
      measuredStep measure decreases fraction (fun next _ => fixed measure decreases next) := by
  have fixStep : fixed measure decreases fraction =
      measuredStep measure decreases fraction (fun next smaller =>
        WellFounded.Nat.fix.go measure (measuredStep measure decreases)
          (measure fraction) next smaller) := by
    have changeFuel {left right : Nat} (same : left = right)
        (leftBound : measure fraction < left) (rightBound : measure fraction < right) :
        WellFounded.Nat.fix.go measure (measuredStep measure decreases) left fraction leftBound =
          WellFounded.Nat.fix.go measure (measuredStep measure decreases) right fraction rightBound := by
      cases same
      rfl
    exact (changeFuel (WellFounded.Nat.eager_eq (measure fraction + 1))
      (WellFounded.Nat.eager_eq _ ▸ Nat.lt_add_one _) (Nat.lt_add_one _)).trans rfl
  apply fixStep.trans
  delta measuredStep
  apply step_congr
  intro nonterminal
  exact go_eq_fixed measure decreases (Hurwitz.Step.next fraction nonterminal) _ _

/-- The original retained logarithm determines the new evaluator's measure. -/
private def logMeasure (fraction : GaussianInt.Fraction) : Nat :=
  Nat.log2 (GaussianInt.normNat fraction.denominator)

/-- Original logarithmic descent at the same selected next fraction. -/
theorem width_decreases (fraction : GaussianInt.Fraction)
    (nonterminal : GaussianInt.Division.Nearest.remainder fraction ≠ 0) :
    Nat.log2 (GaussianInt.normNat (Hurwitz.Step.next fraction nonterminal).denominator) <
      Nat.log2 (GaussianInt.normNat fraction.denominator) :=
  Nat.lt_of_succ_le (Hurwitz.Step.remainder_width_step nonterminal)

/-- Compute the complete finite Hurwitz record with retained logarithmic descent.

Each recursive call receives the exact selected successor and caches its tail
and continuant once. The initial denominator norm and binary width are evaluator
setup; they do not extend the original arithmetic-step account. -/
@[expose] def encodeResult (fraction : GaussianInt.Fraction) : Encoding fraction :=
  WellFounded.Nat.fix
    (fun source : GaussianInt.Fraction => Nat.log2 (GaussianInt.normNat source.denominator))
    (fun source recurse => step
      (fun next parent => Nat.log2 (GaussianInt.normNat next.denominator) <
        Nat.log2 (GaussianInt.normNat parent.denominator))
      source (width_decreases source) recurse) fraction

/-- Unroll the complete retained record at exactly its selected successor.

The pointwise fuel comparison preserves the callback's complete nominal record,
including its original digit list, continuant, bounds and certificate fields. -/
theorem encodeResult_unroll (fraction : GaussianInt.Fraction) :
    encodeResult fraction =
      step (fun next parent => Nat.log2 (GaussianInt.normNat next.denominator) <
        Nat.log2 (GaussianInt.normNat parent.denominator))
        fraction (width_decreases fraction) (fun next _ => encodeResult next) := by
  exact fixed_unroll logMeasure width_decreases fraction

/-- Read the digit list from the certified finite Hurwitz encoding. -/
@[expose] def encode (fraction : GaussianInt.Fraction) : List Data.GaussianInt :=
  (Hurwitz.Encoding.encodeResult fraction).digits

/-- The continuant denominator of the computed Hurwitz encoding is nonzero. -/
theorem encode_denominatorNonzero (fraction : GaussianInt.Fraction) :
    (Hurwitz.Continuant.continuant (Hurwitz.Encoding.encode fraction)).denominator ≠ 0 :=
  (Hurwitz.Encoding.encodeResult fraction).denominatorNonzero

/-- Every retained output digit meets the original source fraction's norm budget. -/
theorem encode_digit_norm_le (fraction : GaussianInt.Fraction) {candidate : GaussianInt.Fraction.Basic.Integer}
    (member : candidate ∈ Hurwitz.Encoding.encode fraction) :
    GaussianInt.normNat candidate ≤ Hurwitz.Step.digitNormBudget fraction :=
  (Hurwitz.Encoding.encodeResult fraction).digit_norm_le candidate member

/-- The computed Hurwitz list length is at most the source denominator norm's binary logarithm plus one. -/
theorem encode_length_le_width (fraction : GaussianInt.Fraction) :
    (Hurwitz.Encoding.encode fraction).length ≤
      Nat.log2 (GaussianInt.normNat fraction.denominator) + 1 :=
  (Hurwitz.Encoding.encodeResult fraction).length_le_width

/-- The computed finite Hurwitz encoding is nonempty. -/
theorem encode_nonempty (fraction : GaussianInt.Fraction) : Hurwitz.Encoding.encode fraction ≠ [] :=
  (Hurwitz.Encoding.encodeResult fraction).nonempty

/-- The original fraction value times the encoded continuant denominator equals its numerator after Gaussian embedding.
-/
theorem encode_reconstruct (fraction : GaussianInt.Fraction) :
    fraction.value * GaussianInt.toGaussian (Hurwitz.Continuant.continuant (Hurwitz.Encoding.encode
      fraction)).denominator =
      GaussianInt.toGaussian (Hurwitz.Continuant.continuant (Hurwitz.Encoding.encode fraction)).numerator :=
  (Hurwitz.Encoding.encodeResult fraction).reconstruct

end Encoding
end Purelib.Data.ComplexContinuedFraction.Hurwitz
