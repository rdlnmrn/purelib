module
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Subtraction
public import Purelib.Data.Nat.Divisors.Indices

/-!
# Signed finite divisor lists

The retained positive-divisor indices are mapped to both integer signs.
Positive occurrences precede negative occurrences, with their original order
and multiplicities preserved.
-/
namespace Purelib.Data.Int.Divisors

open Purelib.Data.List
open Purelib.Data.Nat.Divisors

open Purelib.Data.Nat

/-- Enumerate both signs of every positive divisor of a natural number.

The finite positive-divisor index list is mapped first to positive integers and then
to negative integers, retaining that order in their concatenation. -/
@[expose] public def signedDivisors (value : Nat) : List Int :=
  (Indices.positiveDivisorIndices value).map
      (fun index => ((index + 1 : Nat) : Int)) ++
    (Indices.positiveDivisorIndices value).map
      (fun index => -((index + 1 : Nat) : Int))

/-- Every nonzero signed divisor of a positive natural number occurs in its divisor list.

The positive number bounds the divisor magnitude, while the nonzero numerator
determines a positive divisor index and the appropriate sign in the concatenated
list. -/
public theorem mem_signedDivisors {numerator : Int} {value : Nat}
    (valuePositive : 0 < value) (numeratorNonzero : numerator ≠ 0)
    (divides : numerator.natAbs ∣ value) :
    numerator ∈ signedDivisors value := by
  cases numerator with
  | ofNat magnitude =>
      have magnitudeDivides : magnitude ∣ value := by
        change magnitude ∣ value at divides
        exact divides
      have magnitudePositive : 0 < magnitude := by
        cases magnitude with
        | zero => exact (numeratorNonzero rfl).elim
        | succ predecessor => exact Nat.zero_lt_succ predecessor
      have magnitudeBound : magnitude ≤ value :=
        Divisibility.le_of_dvd valuePositive divides
      let index := magnitude - 1
      have indexBound : index < value := by
        dsimp only [index]
        exact Nat.lt_of_lt_of_le
          (Nat.sub_lt_of_pos_le (by decide) magnitudePositive) magnitudeBound
      have indexIdentity : index + 1 = magnitude := by
        dsimp only [index]
        exact (Nat.add_comm _ 1).trans (Subtraction.add_sub_of_le magnitudePositive)
      apply Membership.mem_append.mpr
      left
      apply Map.mem_map.mpr
      refine ⟨index,
        Indices.mem_positiveDivisorIndices indexBound ?_, ?_⟩
      · rewrite [indexIdentity]
        exact magnitudeDivides
      · exact congrArg Int.ofNat indexIdentity
  | negSucc predecessor =>
      have magnitudeBound : predecessor + 1 ≤ value :=
        Divisibility.le_of_dvd valuePositive divides
      have indexBound : predecessor < value :=
        Nat.lt_of_succ_le magnitudeBound
      apply Membership.mem_append.mpr
      right
      apply Map.mem_map.mpr
      refine ⟨predecessor,
        Indices.mem_positiveDivisorIndices indexBound ?_, ?_⟩
      · exact divides
      · rfl

/-- The signed divisor list has twice as many entries as its positive divisor indices.

Each original index contributes one positive and one negative occurrence.
The two retained maps and their concatenation determine the exact count. -/
@[simp] public theorem signedDivisors_length (value : Nat) :
    (signedDivisors value).length =
      2 * (Indices.positiveDivisorIndices value).length := by
  unfold signedDivisors
  rewrite [Append.length_append, Map.length_map, Map.length_map]
  exact (Nat.two_mul _).symm
end Purelib.Data.Int.Divisors
