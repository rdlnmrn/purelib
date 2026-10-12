module
import Purelib.Data.Nat.Subtraction
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Data.List.Append
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.OfFn.Basic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Entrywise linearity of the complete dyadic increment path. -/
namespace Purelib.Integration.Path.DyadicPrimitiveLinearReadback

open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Algebra
open Purelib.Integration.Path.Dyadic
open Purelib.Data.List
open Purelib.Data.Nat
open Purelib.Integration.Path

open Purelib.Geometry.Rectangle.Partition

/-- The canonical Gaussian carrier for source values and coefficients. -/
private abbrev Gaussian := Basic.Canonical

/-- Every retained dyadic increment of the weighted source is the weighted sum of the original row increments.

The same column index and its explicit depth bound select all entries, including both midpoint-subdivision branches. -/
private theorem linear_entry {size : Nat} (values : Fin size → Fraction.Rational → Basic.Canonical)
    (coefficients : Fin size → Basic.Canonical) (depth : Nat) (first last : Fraction.Rational)
    (column : Nat) (inside : column < 2 ^ depth) :
    (DyadicPrimitivePaths.dyadicIncrements (fun parameter => FiniteSum.Fin.sumFin (fun row => coefficients row * values
      row parameter)) depth first last)[column]'((DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ inside) =
    FiniteSum.Fin.sumFin (fun row => coefficients row * (DyadicPrimitivePaths.dyadicIncrements (values row) depth first
      last)[column]'((DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ inside)) := by
  induction depth generalizing first last column with
  | zero =>
      have zero : column = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ inside)
      subst column
      change FiniteSum.Fin.sumFin (fun row => coefficients row * values row last) -
        FiniteSum.Fin.sumFin (fun row => coefficients row * values row first) =
        FiniteSum.Fin.sumFin (fun row => coefficients row * (values row last - values row first))
      rw [← FiniteSum.Fin.sumFin_sub]
      exact FiniteSum.Fin.sumFin_congr (fun row => by ring1)
  | succ depth ih =>
      let middle := PreparedBoxPartitions.midpoint first last
      have leftRead (source : Fraction.Rational → Basic.Canonical)
          (retained : column < 2 ^ depth) :
          (DyadicPrimitivePaths.dyadicIncrements source (depth + 1) first
            last)[column]'((DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ inside) =
            (DyadicPrimitivePaths.dyadicIncrements source depth first
              middle)[column]'((DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ retained) :=
        Append.getElem_append_left _ _ column
          ((DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ retained) _
      by_cases left : column < 2 ^ depth
      · exact (leftRead _ left).trans
          ((ih first middle column left).trans (FiniteSum.Fin.sumFin_congr
            (fun row => congrArg (fun value => coefficients row * value)
              (leftRead (values row) left).symm)))
      · have right : 2 ^ depth ≤ column := Nat.le_of_not_gt left
        have capacity : 2 ^ (depth + 1) = 2 ^ depth + 2 ^ depth := by
          change 2 ^ depth * 2 = 2 ^ depth + 2 ^ depth
          exact Nat.mul_two _
        have shifted : 2 ^ depth + (column - 2 ^ depth) < 2 ^ depth + 2 ^ depth :=
          (Subtraction.add_sub_of_le right).symm ▸ (capacity ▸ inside)
        have remaining : column - 2 ^ depth < 2 ^ depth :=
          Nat.lt_of_add_lt_add_left shifted
        have rightRead (source : Fraction.Rational → Basic.Canonical) :
            (DyadicPrimitivePaths.dyadicIncrements source (depth + 1) first
              last)[column]'((DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ inside) =
              (DyadicPrimitivePaths.dyadicIncrements source depth middle last)[column - 2 ^
                depth]'((DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ remaining) := by
          let earlier := DyadicPrimitivePaths.dyadicIncrements source depth first middle
          let later := DyadicPrimitivePaths.dyadicIncrements source depth middle last
          have lengthEq : earlier.length = 2 ^ depth := DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _
          have past : earlier.length ≤ column := lengthEq.symm ▸ right
          have tailBound : column - earlier.length < later.length :=
            (congrArg (fun length => column - length < later.length) lengthEq).mpr
              ((DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ remaining)
          have combined : column < (earlier ++ later).length :=
            (DyadicPrimitivePaths.dyadicIncrements_length source (depth + 1) first last).symm ▸ inside
          have shiftedBound : earlier.length + (column - earlier.length) < (earlier ++ later).length :=
            (Subtraction.add_sub_of_le past).symm ▸ combined
          exact ((getElem_congr (Eq.refl (earlier ++ later))
              (Subtraction.add_sub_of_le past).symm combined).trans
            (Append.getElem_append_right earlier later _ tailBound shiftedBound)).trans
              (getElem_congr (Eq.refl later)
                (congrArg (fun length => column - length) lengthEq) tailBound)
        exact (rightRead _).trans
          ((ih middle last _ remaining).trans (FiniteSum.Fin.sumFin_congr
            (fun row => congrArg (fun value => coefficients row * value)
              (rightRead (values row)).symm)))

/-- Reading a retained list through its exact length-indexed function reconstructs the original list. -/
private theorem ofFn_readback (values : List Basic.Canonical) (size : Nat) (length_eq : values.length = size) :
    List.ofFn (fun column : Fin size => values[column.val]'(length_eq.symm ▸ column.isLt)) = values := by
  subst size
  exact OfFn.Basic.ofFn_getElem values

/-- The original indexed weighted dyadic increments equal the dyadic increment list of the weighted source.

Each finite column carries its retained index bound and reads the same original source rows with unchanged coefficients.
-/
theorem dyadicIncrements_linear {size : Nat} (values : Fin size → Fraction.Rational → Basic.Canonical)
    (coefficients : Fin size → Basic.Canonical) (depth : Nat) (first last : Fraction.Rational) :
    List.ofFn (fun column : Fin (2 ^ depth) => FiniteSum.Fin.sumFin (fun row => coefficients row *
      (DyadicPrimitivePaths.dyadicIncrements (values row) depth first
        last)[column.val]'((DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ column.isLt))) =
    DyadicPrimitivePaths.dyadicIncrements (fun parameter => FiniteSum.Fin.sumFin (fun row => coefficients row * values
      row parameter)) depth first last := by
  calc
    _ = List.ofFn (fun column : Fin (2 ^ depth) =>
      (DyadicPrimitivePaths.dyadicIncrements (fun parameter => FiniteSum.Fin.sumFin (fun row => coefficients row *
        values row parameter)) depth first last)[column.val]'(
        (DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _).symm ▸ column.isLt)) :=
      OfFn.Basic.ofFn_congr (fun column => (DyadicPrimitiveLinearReadback.linear_entry values coefficients depth first
        last column.val column.isLt).symm)
    _ = _ := DyadicPrimitiveLinearReadback.ofFn_readback _ _ (DyadicPrimitivePaths.dyadicIncrements_length _ _ _ _)

end Purelib.Integration.Path.DyadicPrimitiveLinearReadback

end
