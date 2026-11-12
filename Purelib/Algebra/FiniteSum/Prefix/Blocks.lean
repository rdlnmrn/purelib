module

public import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Algebra.NatCast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Consecutive blocks of the original rational prefix sum

The block positions retain their original natural indices. No list or
summand is sorted, deduplicated or reconstructed by an unrelated sum.
-/

public section

namespace Purelib.Algebra.FiniteSum.Prefix

open Purelib.Algebra
open Purelib.Data.Rat.Fraction (Rational)

/-- A constant original rational prefix is its actual count times the same entry. -/
theorem coordinateSum_constant (value : Rational) (count : Nat) :
    coordinateSum (fun _ => value) count = (count : Rational) * value := by
  induction count with
  | zero =>
      change (0 : Rational) = (0 : Rational) * value
      ring1
  | succ count prior =>
      exact (congrArg (fun total : Rational => total + value) prior).trans
        ((congrArg (fun scalar : Rational => scalar * value)
          (NatCast.add count 1)).trans (by rewrite [Nat.cast_one]; ring1)).symm

/-- Split the original rational prefix into its two consecutive indexed blocks. -/
theorem coordinateSum_append (values : Nat → Rational) (first last : Nat) :
    coordinateSum values (first + last) = coordinateSum values first +
      coordinateSum (fun index => values (first + index)) last := by
  induction last with
  | zero =>
      change coordinateSum values first = coordinateSum values first + 0
      ring1
  | succ last prior =>
      change coordinateSum values (first + last) + values (first + last) =
        coordinateSum values first +
          (coordinateSum (fun index => values (first + index)) last + values (first + last))
      exact (congrArg (fun total : Rational => total + values (first + last)) prior).trans (by ring1)

/-- Group the same ordered rational prefix into equal consecutive blocks.

The inner position is exactly `block * width + index`. Repeated original
entries remain separate occurrences, including zero block counts or widths.
-/
theorem coordinateSum_blocks (values : Nat → Rational) (blocks width : Nat) :
    coordinateSum values (blocks * width) = coordinateSum (fun block =>
      coordinateSum (fun index => values (block * width + index)) width) blocks := by
  induction blocks with
  | zero =>
      rewrite [Nat.zero_mul]
      rfl
  | succ blocks prior =>
      have split := coordinateSum_append values (blocks * width) width
      exact (congrArg (coordinateSum values) (Nat.succ_mul blocks width)).trans
        (split.trans (congrArg (fun total : Rational => total +
          coordinateSum (fun index => values (blocks * width + index)) width) prior))

end Purelib.Algebra.FiniteSum.Prefix

end
