module
import Purelib.Data.Int.Order
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Int.Interval
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Range.Basic
public import Purelib.Data.Rat.Enumeration.Displayed
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.SignedFraction.Normalization
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

section
public section

/-!
# Finite candidates for constructive rational roots

This file implements the finite part of the rational-root theorem for the
project's explicit dense polynomials.  It clears the finitely many displayed
coefficient denominators, obtains numerator and denominator bounds from the
first and last nonzero integer coefficients, and enumerates only the bounded
canonical fractions.  It never forms a carrier-wide collection of rational
numbers.
-/

namespace Purelib.Data.Rat.Enumeration.Bounded

open Purelib.Data.Nat

open Purelib.Data.Int in
open Purelib.Data.Rat in
/-- Enumerate rational fractions with successor denominators up to the bound and signed numerators of bounded magnitude.

For each denominator index below the bound, enumerate the original signed-numerator list and normalize using denominator
index plus one. The list retains repetitions; the completeness statement uses the actual reduced representative bounds.
-/
@[expose] def boundedFractions (bound : Nat) : List Fraction.Rational :=
  (List.range bound).flatMap fun denominatorIndex =>
    (Interval.signedComponents bound).map fun numerator =>
      Enumeration.Displayed.displayedFraction numerator denominatorIndex

open Purelib.Data.Int
open Purelib.Data.List
open Purelib.Data.Rat
/-- The bounded rational fraction enumeration has length twice the bound times its successor.

Every original denominator index retains the complete signed-numerator list.
Counting these same ordered fibers preserves all repeated occurrences. -/
@[simp] theorem boundedFractions_length (bound : Nat) :
    (Enumeration.Bounded.boundedFractions bound).length = 2 * bound * (bound + 1) := by
  rw [Enumeration.Bounded.boundedFractions, Flatten.length_flatMap_map]
  simp only [Range.Basic.length_range, Interval.signedComponents_length]
  ring1

/-- A rational whose reduced numerator magnitude and denominator meet the supplied bound occurs in the finite
enumeration.

Its original reduced representative supplies an explicit signed numerator and
positive denominator. Their retained bounds locate that exact normalized value. -/
theorem mem_boundedFractions_of_representative_bounds
    (point : Fraction.Rational) (bound : Nat)
    (numeratorBound : (Fraction.Basic.representative point).num.natAbs ≤ bound)
    (denominatorBound : (Fraction.Basic.representative point).den ≤ bound) :
    point ∈ Enumeration.Bounded.boundedFractions bound := by
  let reduced := Fraction.Basic.representative point
  let denominatorIndex := reduced.den - 1
  have denominatorIndexMem : denominatorIndex ∈ List.range bound := by
    apply Range.Basic.mem_range.mpr
    change reduced.den ≤ bound at denominatorBound
    exact (Nat.sub_lt_of_pos_le (by decide) reduced.den_pos).trans_le
      denominatorBound
  have denominatorIdentity : denominatorIndex + 1 = reduced.den := by
    exact (Nat.add_comm _ _).trans
      (Subtraction.add_sub_of_le reduced.den_pos)
  apply Flatten.mem_flatMap.mpr
  refine ⟨denominatorIndex, denominatorIndexMem, ?_⟩
  apply Map.mem_map.mpr
  refine ⟨reduced.num, Interval.mem_signedComponents numeratorBound, ?_⟩
  rw [Enumeration.Displayed.displayedFraction]
  calc
    SignedFraction.Normalization.ofFraction ⟨reduced.num, (denominatorIndex + 1 : Nat), by
        exact Order.natCast_pos (Nat.zero_lt_succ denominatorIndex)⟩ =
        SignedFraction.Normalization.ofFraction (SignedFraction.Normalization.toFraction reduced) := by
      apply SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change reduced.num * (reduced.den : Int) =
        reduced.num * (denominatorIndex + 1 : Nat)
      rw [denominatorIdentity]
    _ = point := SignedFraction.Normalization.representative_spec point
end Purelib.Data.Rat.Enumeration.Bounded

end
