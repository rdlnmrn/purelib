module
import Purelib.Data.Nat.Multiplication
import Purelib.Data.List.Membership
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Continuant
public import Purelib.Data.ComplexContinuedFraction.Hurwitz.Encoding
import Purelib.Data.ComplexContinuedFraction.Hurwitz.Step
import Purelib.Data.GaussianInt.Pair.Basic

import Purelib.Data.GaussianInt.Basic
import Purelib.Data.GaussianInt.Fraction.Basic
import Purelib.Data.GaussianInt.Norm.Basic
import Purelib.Data.GaussianInt.Norm.Bounds
public import Purelib.Data.Nat.BitWidth

import Purelib.Tactic.Ring
import Mathlib.Order.Basic

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

open Purelib in
/-- Count two Gaussian-integer arithmetic operations per retained continuant digit. -/
def continuantArithmeticSteps (digits : List
  Data.GaussianInt) : Nat :=
  2 * digits.length
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

/-! ## Hurwitz recursion and continuants -/

/-- Compute the norm envelope as two times digit bound plus one, raised to the retained length. -/
def continuantNormEnvelope (digitBound length : Nat) : Nat
  :=
  (2 * (digitBound + 1)) ^ length
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

open Purelib in
open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction in
/-- List the exact continuant pair of every retained suffix, including the empty suffix.

The original list comes first and recursion removes one head at each step. Each pair is computed from that exact suffix;
this definition does not claim cached reuse of earlier continuants. -/
def continuantTrace : List Data.GaussianInt → List
  GaussianInt.Pair.Basic.ConvergentPair
  | [] => [Hurwitz.Continuant.continuant []]
  | digits@(_ :: remaining) =>
      Hurwitz.Continuant.continuant digits :: continuantTrace
        remaining
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

open Purelib in
open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction in
/-- A uniform digit norm bound bounds both continuant coordinates by the retained exponential norm envelope. -/
theorem continuant_norm_le_envelope
    {digits : List Data.GaussianInt} {digitBound : Nat}
    (bounded : ∀ candidate ∈ digits, normNat candidate ≤ digitBound) :
    normNat (Hurwitz.Continuant.continuant digits).numerator ≤
        continuantNormEnvelope digitBound digits.length ∧
      normNat (Hurwitz.Continuant.continuant digits).denominator ≤
        continuantNormEnvelope digitBound digits.length := by
  induction digits with
  | nil => exact ⟨le_refl 1, Nat.zero_le 1⟩
  | cons digit digits inductionHypothesis =>
      have digitLe := bounded digit List.mem_cons_self
      have tailBounded : ∀ candidate ∈ digits,
          normNat candidate ≤ digitBound := by
        intro candidate member
        exact bounded candidate (List.mem_cons_of_mem _ member)
      have tail := inductionHypothesis tailBounded
      let envelope := continuantNormEnvelope digitBound digits.length
      have productLe :
          normNat digit *
              normNat (Hurwitz.Continuant.continuant digits).numerator ≤
            digitBound * envelope :=
        Nat.mul_le_mul digitLe tail.1
      have sumLe :
          normNat digit *
                normNat (Hurwitz.Continuant.continuant digits).numerator +
              normNat (Hurwitz.Continuant.continuant digits).denominator ≤
            digitBound * envelope + envelope :=
        Nat.add_le_add productLe tail.2
      have envelopeStep :
          continuantNormEnvelope digitBound (digit :: digits).length =
            2 * (digitBound * envelope + envelope) := by
        simp only [continuantNormEnvelope, List.length_cons, pow_succ, envelope]
        change envelope * (2 * (digitBound + 1)) = 2 * (digitBound * envelope + envelope)
        rw [Nat.mul_comm envelope, Purelib.Data.Nat.Multiplication.mul_assoc,
          Purelib.Data.Nat.Multiplication.right_distrib, Nat.one_mul]
      constructor
      · rw [Hurwitz.Continuant.continuant_cons]
        change normNat
            (digit * (Hurwitz.Continuant.continuant digits).numerator +
              (Hurwitz.Continuant.continuant digits).denominator) ≤ _
        rw [envelopeStep]
        exact (GaussianInt.Norm.Bounds.normNat_add_le_two _ _).trans
          (Nat.mul_le_mul_left 2 (by
            rw [normNat_mul]
            exact sumLe))
      · rw [Hurwitz.Continuant.continuant_cons]
        change normNat (Hurwitz.Continuant.continuant digits).numerator ≤ _
        rw [envelopeStep]
        have envelopeLeSum :
            envelope ≤ digitBound * envelope + envelope :=
          Nat.le_add_left envelope (digitBound * envelope)
        have sumLeDouble : digitBound * envelope + envelope ≤
            2 * (digitBound * envelope + envelope) := by
          have scaled := Nat.mul_le_mul_right
            (digitBound * envelope + envelope) (show 1 ≤ 2 by decide)
          simpa only [Nat.one_mul, Nat.two_mul] using scaled
        exact tail.1.trans (envelopeLeSum.trans sumLeDouble)
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

open Purelib in
open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction in
/-- Every pair in the exact suffix continuant trace meets the full-list norm envelope. -/
theorem continuantTrace_norm_le_envelope
    {digits : List Data.GaussianInt} {digitBound : Nat}
    (bounded : ∀ candidate ∈ digits, normNat candidate ≤ digitBound)
    {pair : GaussianInt.Pair.Basic.ConvergentPair} (member : pair ∈ continuantTrace digits) :
    normNat pair.numerator ≤ continuantNormEnvelope digitBound digits.length ∧
      normNat pair.denominator ≤
        continuantNormEnvelope digitBound digits.length := by
  induction digits with
  | nil =>
      simp only [-eq_self, -iff_self, continuantTrace] at member
      have member := Purelib.Data.List.Membership.mem_singleton.mp member
      rw [member]
      exact ⟨le_refl 1, Nat.zero_le 1⟩
  | cons digit digits inductionHypothesis =>
      simp only [-eq_self, -iff_self, continuantTrace] at member
      have member := Purelib.Data.List.Membership.mem_cons.mp member
      rcases member with head | tail
      · rw [head]
        exact continuant_norm_le_envelope bounded
      · have tailBounded : ∀ candidate ∈ digits,
            normNat candidate ≤ digitBound := by
          intro candidate candidateMember
          exact bounded candidate (List.mem_cons_of_mem _ candidateMember)
        have tailResult := inductionHypothesis tailBounded tail
        have basePositive : 0 < 2 * (digitBound + 1) :=
          Nat.mul_pos (by decide) (Nat.zero_lt_succ _)
        have envelopeLe :
            continuantNormEnvelope digitBound digits.length ≤
              continuantNormEnvelope digitBound (digit :: digits).length := by
          exact Nat.pow_le_pow_right basePositive (Nat.le_succ _)
        exact ⟨tailResult.1.trans envelopeLe,
          tailResult.2.trans envelopeLe⟩
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction in
open Purelib.Data.Nat in
/-- Compute the continuant norm budget from the source digit budget and retained denominator-norm bit width. -/
def hurwitzContinuantNormBudget (fraction :
  GaussianInt.Fraction) : Nat :=
  continuantNormEnvelope (Hurwitz.Step.digitNormBudget fraction)
    (BitWidth.natWidth (normNat fraction.denominator))
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction in
/-- Both coordinates of the computed Hurwitz continuant meet the source-specific norm budget. -/
theorem encodedContinuant_norm_le_budget (fraction :
  GaussianInt.Fraction) :
    normNat
          (Hurwitz.Continuant.continuant
            (Hurwitz.Encoding.encode fraction)).numerator ≤
        hurwitzContinuantNormBudget fraction ∧
      normNat
          (Hurwitz.Continuant.continuant
            (Hurwitz.Encoding.encode fraction)).denominator ≤
        hurwitzContinuantNormBudget fraction := by
  have actual := continuant_norm_le_envelope
    (fun candidate member =>
      Hurwitz.Encoding.encode_digit_norm_le fraction member)
  have lengthLe := Hurwitz.Encoding.encode_length_le_width fraction
  have basePositive : 0 <
      2 * (Hurwitz.Step.digitNormBudget fraction + 1) :=
    Nat.mul_pos (by decide) (Nat.zero_lt_succ _)
  have envelopeLe :
      continuantNormEnvelope (Hurwitz.Step.digitNormBudget fraction)
          (Hurwitz.Encoding.encode fraction).length ≤
        hurwitzContinuantNormBudget fraction := by
    exact Nat.pow_le_pow_right basePositive lengthLe
  exact ⟨actual.1.trans envelopeLe, actual.2.trans envelopeLe⟩
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

open Purelib.Data in
open Purelib.Data.Nat in
/-- Read the natural bit width of the retained source denominator norm as the Hurwitz step budget. -/
def hurwitzStepBudget (fraction : GaussianInt.Fraction) :
  Nat :=
  BitWidth.natWidth (normNat fraction.denominator)
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction in
/-- Double the retained Hurwitz step budget to bound continuant arithmetic operations. -/
def hurwitzContinuantStepBudget (fraction :
  GaussianInt.Fraction) : Nat :=
  2 * hurwitzStepBudget fraction
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction in
/-- The exact Hurwitz output length is bounded by the source denominator-width step budget. -/
theorem hurwitz_length_le_stepBudget (fraction :
  GaussianInt.Fraction) :
    (Hurwitz.Encoding.encode fraction).length ≤
      hurwitzStepBudget fraction :=
  Hurwitz.Encoding.encode_length_le_width fraction
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end

section
@[expose] public section

/-!
# Explicit arithmetic envelopes for RFAP-II

This module bounds the finite post-processing performed in the second RFAP
paper.  It covers the square-threshold request, displayed grid record,
homogeneous Gaussian-integer evaluation, and finite Hurwitz recursion.  The
eliminant, Sturm, and repeated-subdivision costs used to produce the imported
RFAP-I Newton state are deliberately outside this module.
-/

namespace Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

open Purelib.Data.GaussianInt (normNat normNat_mul)

open Purelib.Data in
open Purelib.Data.ComplexContinuedFraction in
/-- The exact output's continuant arithmetic count is bounded by twice the source step budget. -/
theorem encodedContinuant_steps_le_budget (fraction :
  GaussianInt.Fraction) :
    continuantArithmeticSteps (Hurwitz.Encoding.encode fraction) ≤
      hurwitzContinuantStepBudget fraction :=
  Nat.mul_le_mul_left 2 (hurwitz_length_le_stepBudget fraction)
end Purelib.Data.ComplexContinuedFraction.Hurwitz.Resource

end
