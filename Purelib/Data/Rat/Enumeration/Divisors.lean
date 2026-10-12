module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Int.Divisors
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.Nat.Divisors.Indices
public import Purelib.Data.Rat.Enumeration.Displayed
import Purelib.Data.Rat.Fraction.Basic
import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.Polynomial.Dense.Rational.Denominator
public import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Divisibility
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Int.Order

/-!
# Ordered endpoint-divisor fraction enumeration

The original positive denominator indices and signed numerator divisors form
the retained ordered fraction table. Exact canonical witnesses establish
membership without changing any enumerated coefficient or normalization.
-/

namespace Purelib.Data.Rat.Enumeration.Divisors

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Algebra
open Purelib.Data.List
open Purelib.Data
open Purelib.Polynomial.Dense.Rational

/-- Enumerate rational fractions formed from signed numerator divisors and positive denominator divisors.

Enumerate positive denominator-divisor indices and signed numerator divisors, preserving their original list order.
Normalize each displayed fraction with the corresponding positive denominator; completeness requires nonzero input and
positive supplied magnitudes. -/
@[expose] public def divisorFractions (numeratorMagnitude denominatorMagnitude : Nat) :
    List Fraction.Rational :=
  (Nat.Divisors.Indices.positiveDivisorIndices denominatorMagnitude).flatMap
    (fun denominatorIndex =>
      (Int.Divisors.signedDivisors numeratorMagnitude).map
        (fun numerator => Enumeration.Displayed.displayedFraction numerator denominatorIndex))

/-- The divisor-based fraction enumeration has length at most twice the product of the supplied magnitudes.

The exact original denominator-index list supplies each ordered numerator fiber.
Their retained lengths bound the same finite product without removing duplicates. -/
public theorem divisorFractions_length_le
    (numeratorMagnitude denominatorMagnitude : Nat) :
    (divisorFractions numeratorMagnitude denominatorMagnitude).length ≤
      2 * numeratorMagnitude * denominatorMagnitude := by
  rw [divisorFractions, Flatten.length_flatMap_map, Int.Divisors.signedDivisors_length]
  have numeratorBound :=
    Nat.Divisors.Indices.positiveDivisorIndices_length_le numeratorMagnitude
  have denominatorBound :=
    Nat.Divisors.Indices.positiveDivisorIndices_length_le denominatorMagnitude
  calc
    (Nat.Divisors.Indices.positiveDivisorIndices denominatorMagnitude).length *
          (2 * (Nat.Divisors.Indices.positiveDivisorIndices numeratorMagnitude).length) ≤
        denominatorMagnitude * (2 * numeratorMagnitude) :=
      Nat.mul_le_mul denominatorBound (Nat.mul_le_mul_left 2 numeratorBound)
    _ = 2 * numeratorMagnitude * denominatorMagnitude := by ring1

/-- A nonzero rational belongs to the divisor enumeration when its reduced numerator and denominator divide the supplied
positive magnitudes.

The canonical positive denominator supplies the original predecessor index.
The exact signed numerator occurrence and that same denominator occurrence
read back the supplied rational through their original normalization witness. -/
public theorem mem_divisorFractions_of_representative_divisors
    (point : Fraction.Rational) (numeratorMagnitude denominatorMagnitude : Nat)
    (pointNonzero : point ≠ 0)
    (numeratorMagnitudePositive : 0 < numeratorMagnitude)
    (denominatorMagnitudePositive : 0 < denominatorMagnitude)
    (numeratorDivides :
      (Fraction.Basic.representative point).num.natAbs ∣ numeratorMagnitude)
    (denominatorDivides :
      (Fraction.Basic.representative point).den ∣ denominatorMagnitude) :
    point ∈ divisorFractions numeratorMagnitude denominatorMagnitude := by
  let reduced := Fraction.Basic.representative point
  let denominatorIndex := reduced.den - 1
  have denominatorBound : reduced.den ≤ denominatorMagnitude :=
    Nat.Divisibility.le_of_dvd denominatorMagnitudePositive denominatorDivides
  have denominatorIdentity : denominatorIndex + 1 = reduced.den :=
    (Nat.add_comm denominatorIndex 1).trans
      (Nat.Subtraction.add_sub_of_le reduced.den_pos)
  have denominatorIndexBound : denominatorIndex < denominatorMagnitude := by
    change denominatorIndex + 1 ≤ denominatorMagnitude
    rewrite [denominatorIdentity]
    exact denominatorBound
  have denominatorIndexMember :
      denominatorIndex ∈ Nat.Divisors.Indices.positiveDivisorIndices denominatorMagnitude := by
    apply Nat.Divisors.Indices.mem_positiveDivisorIndices denominatorIndexBound
    rewrite [denominatorIdentity]
    exact denominatorDivides
  have numeratorMember : reduced.num ∈ Int.Divisors.signedDivisors numeratorMagnitude :=
    Int.Divisors.mem_signedDivisors numeratorMagnitudePositive
      (Denominator.representative_num_ne_zero pointNonzero) numeratorDivides
  rw [divisorFractions]
  apply Flatten.mem_flatMap.mpr
  refine ⟨denominatorIndex, denominatorIndexMember, ?_⟩
  apply Map.mem_map.mpr
  refine ⟨reduced.num, numeratorMember, ?_⟩
  rw [Enumeration.Displayed.displayedFraction]
  calc
    SignedFraction.Normalization.ofFraction ⟨reduced.num, (denominatorIndex + 1 : Nat), by
        exact Int.Order.natCast_pos (Nat.zero_lt_succ denominatorIndex)⟩ =
        SignedFraction.Normalization.ofFraction (SignedFraction.Normalization.toFraction reduced) := by
      apply SignedFraction.Normalization.ofFraction_eq_of_equivalent
      change reduced.num * (reduced.den : Int) =
        reduced.num * (denominatorIndex + 1 : Nat)
      rewrite [denominatorIdentity]
      exact Eq.refl _
    _ = point := SignedFraction.Normalization.representative_spec point

end Purelib.Data.Rat.Enumeration.Divisors
