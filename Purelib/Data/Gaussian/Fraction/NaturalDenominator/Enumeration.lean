module
public import Purelib.Data.Gaussian.Fraction.NaturalDenominator
import Purelib.Data.GaussianInt.Basic
public import Purelib.Data.Int.Interval
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.Range.Basic
import Purelib.Data.Nat.Subtraction

section
@[expose] public section

/-!
# Exact finite best-residual search

For fixed numerator and denominator bounds there are only finitely many
displayed common-denominator Gaussian fractions.  This module enumerates that
finite rectangle and selects a sample of least polynomial residual by direct
comparison.
-/

namespace Purelib.Data.Gaussian.Fraction.NaturalDenominator.Enumeration

open Purelib.Data.Gaussian in
open Purelib.Data.Int in
/-- Enumerate Gaussian fractions with bounded signed numerator coordinates and positive denominators up to the supplied
bound.

For each positive denominator up to the supplied bound, traverse the signed numerator list independently for real and
imaginary coordinates. Keep the original nested list order and explicit positivity witness; the result is not
deduplicated. -/
def candidates (numeratorBound denominatorBound :
  Nat) : List Basic.Canonical.Fraction.NaturalDenominator :=
  (List.range denominatorBound).flatMap fun denominatorIndex =>
    (Interval.signedComponents
      numeratorBound).flatMap fun real =>
      (Interval.signedComponents
        numeratorBound).map fun imaginary =>
        Basic.Canonical.Fraction.NaturalDenominator.grid real imaginary
          (denominatorIndex + 1) (Nat.zero_lt_succ denominatorIndex)

open Purelib.Data.Gaussian in
open Purelib.Data.Int in
open Purelib.Data.List in
open Purelib.Data.Nat in
/-- A retained Gaussian fraction belongs to the candidate list when both numerator coordinates and its denominator meet
the supplied bounds. -/
theorem mem_candidates {fraction :
  Basic.Canonical.Fraction.NaturalDenominator}
    {numeratorBound denominatorBound : Nat}
    (realBound : fraction.numerator.re.natAbs ≤ numeratorBound)
    (imaginaryBound : fraction.numerator.im.natAbs ≤ numeratorBound)
    (denominatorBounded : fraction.denominator ≤ denominatorBound) :
    fraction ∈ candidates numeratorBound denominatorBound := by
  let denominatorIndex := fraction.denominator - 1
  have denominatorIdentity : denominatorIndex + 1 = fraction.denominator := by
    dsimp only [denominatorIndex]
    exact Subtraction.sub_add_cancel
      (Nat.succ_le_iff.mpr fraction.denominatorPositive)
  have indexBound : denominatorIndex < denominatorBound := by
    calc
      denominatorIndex < denominatorIndex + 1 := Nat.lt_succ_self _
      _ = fraction.denominator := denominatorIdentity
      _ ≤ denominatorBound := denominatorBounded
  rw [candidates]
  apply Flatten.mem_flatMap.mpr
  refine ⟨denominatorIndex, Range.Basic.mem_range.mpr indexBound, ?_⟩
  apply Flatten.mem_flatMap.mpr
  refine ⟨fraction.numerator.re,
    Interval.mem_signedComponents realBound, ?_⟩
  apply Map.mem_map.mpr
  refine ⟨fraction.numerator.im,
    Interval.mem_signedComponents imaginaryBound,
    ?_⟩
  cases fraction with
  | mk numerator denominator positive =>
    cases numerator with
    | mk real imaginary =>
      dsimp only [Basic.Canonical.Fraction.NaturalDenominator.grid]
      have assemble (left right : Nat) (leftPositive : 0 < left)
          (rightPositive : 0 < right) (same : left = right) :
          ({ numerator := ⟨real, imaginary⟩, denominator := left,
             denominatorPositive := leftPositive } : Basic.Canonical.Fraction.NaturalDenominator) =
            { numerator := ⟨real, imaginary⟩, denominator := right,
              denominatorPositive := rightPositive } := by
        cases same
        rfl
      exact assemble (denominatorIndex + 1) denominator
        (Nat.zero_lt_succ denominatorIndex) positive denominatorIdentity
end Purelib.Data.Gaussian.Fraction.NaturalDenominator.Enumeration

end
