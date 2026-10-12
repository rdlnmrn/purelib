module
public import Purelib.Data.Nat.Search.First
public import Purelib.Data.Nat.Search.LastConsecutive

import Purelib.Tactic.QuotientFreeOmega
-- Public bounds retain the original natural-power data with owned monoid laws.
public import Purelib.Algebra.Semiring.Nat
import Purelib.Data.Nat.Multiplication
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Bounded binary normalization

The three normalization exponents are found by transparent recursion with an
explicit natural-number fuel bound.  No finite set, extremum operator, or
unbounded search is used.
-/

public section

namespace Purelib.Data.Nat.BinaryNormalization

open Purelib.Data.Nat
open Purelib.Data.Nat.Search

/-- A natural successor does not exceed the corresponding power of two.

The estimate holds at zero and is preserved by doubling the preceding binary
power. -/
theorem succ_le_two_pow (n : Nat) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => exact Nat.le_refl 1
  | succ n inductionHypothesis =>
      rw [Nat.pow_succ]
      have step : n + 2 ≤ 2 * (n + 1) := by omega0
      have scaled := Nat.mul_le_mul_left 2 inductionHypothesis
      rw [Nat.mul_comm 2 (2 ^ n)] at scaled
      exact Nat.le_trans step scaled

set_option genInjectivity false in
/-- A positive binary exponent bracketing a natural numerator by a scaled denominator.

The certificate retains exponent ≥ 1, the lower bound 2^exponent * denominatorNorm ≤
numeratorNorm, and the strict upper bound at the next exponent. -/
structure HighResult (numeratorNorm denominatorNorm : Nat) where
  /-- The selected binary exponent. -/ exponent : Nat
  /-- The selected exponent is at least one. -/ positive : 1 ≤ exponent
  /-- The denominator scaled by the selected power of two does not exceed the numerator. -/ lower : 2 ^ exponent *
    denominatorNorm ≤ numeratorNorm
  /-- The numerator is strictly below the denominator scaled by the next power of two. -/ upper : numeratorNorm < 2 ^
    (exponent + 1) * denominatorNorm

constructive_injectivity HighResult

set_option genInjectivity false in
/-- A binary exponent scaling a natural numerator into a denominator-width interval.

The retained lower and strict upper bounds place 2^exponent * numeratorNorm between
denominatorNorm inclusive and twice denominatorNorm exclusive. -/
structure LowResult (numeratorNorm denominatorNorm : Nat) where
  /-- The selected binary exponent. -/ exponent : Nat
  /-- The numerator scaled by the selected power of two reaches the denominator. -/ lower : denominatorNorm ≤ 2 ^
    exponent * numeratorNorm
  /-- The scaled numerator is strictly below twice the denominator. -/ upper : 2 ^ exponent * numeratorNorm < 2 *
    denominatorNorm

constructive_injectivity LowResult

set_option genInjectivity false in
/-- A binary exponent with a strict lower and weak upper scaled-denominator bound.

The numerator is strictly above 2^exponent * denominatorNorm and at most the same
expression at the next exponent. -/
structure LoopResult (numeratorNorm denominatorNorm : Nat) where
  /-- The selected binary exponent. -/ exponent : Nat
  /-- The denominator scaled by the selected power of two is strictly below the numerator. -/ lower : 2 ^ exponent *
    denominatorNorm < numeratorNorm
  /-- The numerator does not exceed the denominator scaled by the next power of two. -/ upper : numeratorNorm ≤ 2 ^
    (exponent + 1) * denominatorNorm

constructive_injectivity LoopResult

/-- Increasing a binary exponent preserves weak order after natural scaling.

Multiplication by the same natural factor preserves the weak order between
the two powers of two. -/
private theorem pow_mul_mono_exponent (factor left right : Nat)
    (order : left ≤ right) :
    2 ^ left * factor ≤ 2 ^ right * factor :=
  Nat.mul_le_mul_right factor
    (Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) order)

/-- The two adjacent power bounds determine a high-normalization exponent uniquely.

Concrete certificates can therefore avoid reducing the search that originally found
the exponent. -/
theorem HighResult.exponent_eq_of_bounds
    {numeratorNorm denominatorNorm candidate : Nat}
    (result : HighResult numeratorNorm denominatorNorm)
    (candidateLower :
      2 ^ candidate * denominatorNorm ≤ numeratorNorm)
    (candidateUpper :
      numeratorNorm < 2 ^ (candidate + 1) * denominatorNorm) :
    result.exponent = candidate := by
  have resultLower := result.lower
  have resultUpper := result.upper
  apply Nat.le_antisymm
  · have order : result.exponent ≤ candidate ∨
        candidate + 1 ≤ result.exponent := by omega0
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := BinaryNormalization.pow_mul_mono_exponent denominatorNorm
        (candidate + 1) result.exponent nextLe
      omega0
  · have order : candidate ≤ result.exponent ∨
        result.exponent + 1 ≤ candidate := by omega0
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := BinaryNormalization.pow_mul_mono_exponent denominatorNorm
        (result.exponent + 1) candidate nextLe
      omega0

/-- The adjacent bounds determine a low-normalization exponent uniquely.

Any candidate that scales the numerator into the same half-open interval has
the retained exponent. -/
theorem LowResult.exponent_eq_of_bounds
    {numeratorNorm denominatorNorm candidate : Nat}
    (result : LowResult numeratorNorm denominatorNorm)
    (candidateLower :
      denominatorNorm ≤ 2 ^ candidate * numeratorNorm)
    (candidateUpper :
      2 ^ candidate * numeratorNorm < 2 * denominatorNorm) :
    result.exponent = candidate := by
  have resultLower := result.lower
  have resultUpper := result.upper
  apply Nat.le_antisymm
  · have order : result.exponent ≤ candidate ∨
        candidate + 1 ≤ result.exponent := by omega0
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := BinaryNormalization.pow_mul_mono_exponent numeratorNorm
        (candidate + 1) result.exponent nextLe
      have twiceDenominatorLe :
          2 * denominatorNorm ≤ 2 ^ (candidate + 1) * numeratorNorm := by
        calc
          2 * denominatorNorm ≤
              2 * (2 ^ candidate * numeratorNorm) :=
            Nat.mul_le_mul_left 2 candidateLower
          _ = 2 ^ (candidate + 1) * numeratorNorm := by
            rw [Nat.pow_succ]
            rw [← Multiplication.mul_assoc 2 _ numeratorNorm, Nat.mul_comm 2 _]
      have impossible := Nat.le_trans twiceDenominatorLe powerLe
      omega0
  · have order : candidate ≤ result.exponent ∨
        result.exponent + 1 ≤ candidate := by omega0
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := BinaryNormalization.pow_mul_mono_exponent numeratorNorm
        (result.exponent + 1) candidate nextLe
      have twiceDenominatorLe :
          2 * denominatorNorm ≤
            2 ^ (result.exponent + 1) * numeratorNorm := by
        calc
          2 * denominatorNorm ≤
              2 * (2 ^ result.exponent * numeratorNorm) :=
            Nat.mul_le_mul_left 2 resultLower
          _ = 2 ^ (result.exponent + 1) * numeratorNorm := by
            rw [Nat.pow_succ]
            rw [← Multiplication.mul_assoc 2 _ numeratorNorm, Nat.mul_comm 2 _]
      have impossible := Nat.le_trans twiceDenominatorLe powerLe
      omega0

/-- The adjacent bounds determine a loop-normalization exponent uniquely.

The strict lower and weak upper endpoints force any candidate satisfying
those same bounds to have the retained exponent. -/
theorem LoopResult.exponent_eq_of_bounds
    {numeratorNorm denominatorNorm candidate : Nat}
    (result : LoopResult numeratorNorm denominatorNorm)
    (candidateLower :
      2 ^ candidate * denominatorNorm < numeratorNorm)
    (candidateUpper :
      numeratorNorm ≤ 2 ^ (candidate + 1) * denominatorNorm) :
    result.exponent = candidate := by
  have resultLower := result.lower
  have resultUpper := result.upper
  apply Nat.le_antisymm
  · have order : result.exponent ≤ candidate ∨
        candidate + 1 ≤ result.exponent := by omega0
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := BinaryNormalization.pow_mul_mono_exponent denominatorNorm
        (candidate + 1) result.exponent nextLe
      omega0
  · have order : candidate ≤ result.exponent ∨
        result.exponent + 1 ≤ candidate := by omega0
    rcases order with direct | nextLe
    · exact direct
    · have powerLe := BinaryNormalization.pow_mul_mono_exponent denominatorNorm
        (result.exponent + 1) candidate nextLe
      omega0

/-- Find the last binary exponent satisfying the weak lower normalization bound.

A positive denominator and numerator at least twice that denominator justify the scan
starting at one. A finite terminal bound certifies the returned adjacent power
inequalities. -/
@[expose] def high (numeratorNorm denominatorNorm : Nat)
    (denominatorPositive : 0 < denominatorNorm)
    (highBranch : 2 * denominatorNorm ≤ numeratorNorm) :
    HighResult numeratorNorm denominatorNorm := by
  let predicate := fun exponent : Nat =>
    2 ^ exponent * denominatorNorm ≤ numeratorNorm
  have starts : predicate 1 := by
    change (1 * 2) * denominatorNorm ≤ numeratorNorm
    rw [Nat.one_mul]
    exact highBranch
  have terminalFailure :
      ¬predicate (1 + numeratorNorm + 1) := by
    intro terminalHolds
    have powerBound : numeratorNorm + 3 ≤ 2 ^ (numeratorNorm + 2) :=
      BinaryNormalization.succ_le_two_pow (numeratorNorm + 2)
    have denominatorAtLeastOne : 1 ≤ denominatorNorm := denominatorPositive
    have productBound :
        2 ^ (numeratorNorm + 2) ≤
          2 ^ (numeratorNorm + 2) * denominatorNorm := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (2 ^ (numeratorNorm + 2)) denominatorAtLeastOne
    have impossible : numeratorNorm + 3 ≤ numeratorNorm := by
      exact Nat.le_trans powerBound (Nat.le_trans productBound (by
        simpa only [predicate, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
          using terminalHolds))
    have successorLeSelf : Nat.succ numeratorNorm ≤ numeratorNorm := by
      simpa only [Nat.succ_eq_add_one] using
        Nat.le_trans
          (Nat.add_le_add_left (by decide : 1 ≤ 3) numeratorNorm) impossible
    exact (Nat.not_succ_le_self numeratorNorm successorLeSelf).elim
  let result := LastConsecutive.scanLast predicate (fun _ => inferInstance) 1 numeratorNorm
    starts terminalFailure
  refine ⟨result.exponent, result.start_le, result.holds, ?_⟩
  exact Nat.lt_of_not_ge result.next_fails

/-- Find the first binary exponent that scales the numerator above the denominator.

Positive inputs and numerator less than twice denominatorNorm yield a finite
first-true scan starting at zero, with the scaled result still strictly below twice
the denominator. -/
@[expose] def low (numeratorNorm denominatorNorm : Nat)
    (numeratorPositive : 0 < numeratorNorm)
    (_denominatorPositive : 0 < denominatorNorm)
    (lowBranch : numeratorNorm < 2 * denominatorNorm) :
    LowResult numeratorNorm denominatorNorm := by
  let predicate := fun exponent : Nat =>
    denominatorNorm ≤ 2 ^ exponent * numeratorNorm
  have powerBound : denominatorNorm + 1 ≤ 2 ^ denominatorNorm :=
    BinaryNormalization.succ_le_two_pow denominatorNorm
  have numeratorAtLeastOne : 1 ≤ numeratorNorm := numeratorPositive
  have terminalHolds : predicate (0 + denominatorNorm) := by
    have denominatorLePower : denominatorNorm ≤ 2 ^ denominatorNorm :=
      Nat.le_trans (Nat.le_add_right denominatorNorm 1) powerBound
    have powerLeProduct :
        2 ^ denominatorNorm ≤ 2 ^ denominatorNorm * numeratorNorm := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (2 ^ denominatorNorm) numeratorAtLeastOne
    simpa only [predicate, Nat.zero_add] using
      Nat.le_trans denominatorLePower powerLeProduct
  let result := First.scanFirst predicate (fun _ => inferInstance) 0 denominatorNorm
    terminalHolds
  refine ⟨result.exponent, result.holds, ?_⟩
  cases exponentIdentity : result.exponent with
  | zero =>
      simpa only [exponentIdentity, Nat.pow_zero, Nat.one_mul] using lowBranch
  | succ previous =>
      have previousFails :
          ¬denominatorNorm ≤ 2 ^ previous * numeratorNorm := by
        have previousLtExponent : previous < result.exponent := by
          rw [exponentIdentity]
          exact Nat.lt_succ_self previous
        exact result.before_fails previous (Nat.zero_le previous)
          previousLtExponent
      have previousLt :
          2 ^ previous * numeratorNorm < denominatorNorm :=
        Nat.lt_of_not_ge previousFails
      calc
        2 ^ (previous + 1) * numeratorNorm =
            2 * (2 ^ previous * numeratorNorm) := by
          rw [Nat.pow_succ]
          rw [Nat.mul_comm (2 ^ previous) 2, Multiplication.mul_assoc]
        _ < 2 * denominatorNorm :=
          by
            have doubled := Nat.add_lt_add previousLt previousLt
            rw [← Nat.two_mul, ← Nat.two_mul] at doubled
            exact doubled

/-- Find the last binary exponent satisfying the strict lower normalization bound.

A positive denominator strictly below the numerator permits a finite
last-consecutive-true scan starting at zero; the next exponent supplies the weak
upper bound. -/
@[expose] def loop (numeratorNorm denominatorNorm : Nat)
    (denominatorPositive : 0 < denominatorNorm)
    (strictBranch : denominatorNorm < numeratorNorm) :
    LoopResult numeratorNorm denominatorNorm := by
  let predicate := fun exponent : Nat =>
    2 ^ exponent * denominatorNorm < numeratorNorm
  have starts : predicate 0 := by
    simpa only [predicate, Nat.pow_zero, Nat.one_mul] using strictBranch
  have terminalFailure : ¬predicate (0 + numeratorNorm + 1) := by
    intro terminalHolds
    have powerBound : numeratorNorm + 2 ≤ 2 ^ (numeratorNorm + 1) :=
      BinaryNormalization.succ_le_two_pow (numeratorNorm + 1)
    have denominatorAtLeastOne : 1 ≤ denominatorNorm := denominatorPositive
    have productBound :
        2 ^ (numeratorNorm + 1) ≤
          2 ^ (numeratorNorm + 1) * denominatorNorm := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_left (2 ^ (numeratorNorm + 1)) denominatorAtLeastOne
    have impossible : numeratorNorm + 2 < numeratorNorm := by
      exact Nat.lt_of_le_of_lt powerBound (Nat.lt_of_le_of_lt productBound (by
        simpa only [predicate, Nat.zero_add] using terminalHolds))
    exact (Nat.not_lt_of_ge (Nat.le_add_right numeratorNorm 2) impossible).elim
  let result := LastConsecutive.scanLast predicate (fun _ => inferInstance) 0 numeratorNorm
    starts terminalFailure
  refine ⟨result.exponent, result.holds, ?_⟩
  exact Nat.le_of_not_gt result.next_fails

set_option genInjectivity false in
/-- A binary scale placing a natural ratio between one inclusive and two exclusive.

The retained exponent brackets numerator between 2^exponent times denominator and the
next binary multiple, without forming a rational quotient. -/
structure CLScale (numerator denominator : Nat) where
  /-- The selected binary scaling exponent. -/ exponent : Nat
  /-- The denominator scaled by this power of two does not exceed the numerator. -/ lower : 2 ^ exponent * denominator ≤
    numerator
  /-- The numerator is strictly below the denominator scaled by the next power of two. -/ upper : numerator < 2 ^
    (exponent + 1) * denominator

constructive_injectivity CLScale

/-- Construct a certified binary scale for an ordered positive-denominator ratio.

If numerator is at least twice denominator, reuse high normalization. Otherwise
exponent zero already satisfies the required two adjacent bounds. -/
@[expose] def clScale (numerator denominator : Nat) (positive : 0 < denominator)
    (ordered : denominator ≤ numerator) : CLScale numerator denominator := by
  if highBranch : 2 * denominator ≤ numerator then
    let result := BinaryNormalization.high numerator denominator
      positive highBranch
    exact ⟨result.exponent, result.lower, result.upper⟩
  else
    exact ⟨0, by simpa only [Nat.pow_zero, Nat.one_mul] using ordered,
      by
        change numerator < 2 * denominator
        exact Nat.lt_of_not_ge highBranch⟩

/-- A value below twice a natural bound leaves at most that bound after subtraction.

Truncated subtraction retains the displayed inequality whether or not the
value reaches the subtrahend. -/
theorem difference_le_of_lt_two_mul {numerator normalized : Nat}
    (upper : numerator < 2 * normalized) :
    numerator - normalized ≤ normalized := by
  rw [Nat.two_mul] at upper
  omega0
end Purelib.Data.Nat.BinaryNormalization

end
