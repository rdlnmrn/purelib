module
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
public import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

public section

/-! Linearity of concatenated dyadic paths, without identifying row functions
or choosing a row to determine the length of an empty basis. -/
namespace Purelib.Integration.Path.DyadicBlockLinearReadback
open Purelib.Algebra
open Purelib.Integration.Path.Dyadic
open Purelib.Integration.Path
open Purelib.Data.Gaussian
open Purelib.Data.Rat

open Purelib.Data.List

/-- The rational carrier for original source parameters. -/
private abbrev Coordinate := Fraction.Rational
/-- The canonical Gaussian carrier for source values and coefficients. -/
private abbrev Gaussian := Basic.Canonical

open Purelib.Geometry.Rectangle.Partition in
/-- Build columns of exact source increments on the retained dyadic subdivision.

Each column keeps every original row at the same interval, and recursive midpoint subdivision preserves left-to-right
ordering. -/
private def dyadicColumns {size : Nat} (values : Fin size → Fraction.Rational → Basic.Canonical) :
    Nat → Fraction.Rational → Fraction.Rational → List (Fin size → Basic.Canonical)
  | 0, first, last => [fun row => values row last - values row first]
  | depth + 1, first, last =>
      let middle := PreparedBoxPartitions.midpoint first last
      Purelib.Integration.Path.DyadicBlockLinearReadback.dyadicColumns values depth first middle ++
        Purelib.Integration.Path.DyadicBlockLinearReadback.dyadicColumns values depth middle last

/-- The original dyadic column list has two to the retained depth entries.

Each retained midpoint subdivision concatenates its original left and right column lists. Their structural lengths add
to the next exact dyadic count. -/
private theorem columns_length {size : Nat} (values : Fin size → Fraction.Rational → Basic.Canonical)
    (depth : Nat) (first last : Fraction.Rational) : (DyadicBlockLinearReadback.dyadicColumns values depth first
      last).length = 2 ^ depth := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [DyadicBlockLinearReadback.dyadicColumns, Append.length_append, ih, ih, pow_succ, Nat.mul_two]

/-- Reading one retained row of each dyadic column gives that source's exact dyadic increments.

Reading a fixed original row commutes with the retained ordered concatenation. The scalar head and structural tails
recover that source's exact increments. -/
private theorem columns_row {size : Nat} (values : Fin size → Fraction.Rational → Basic.Canonical)
    (depth : Nat) (first last : Fraction.Rational) (row : Fin size) :
    (DyadicBlockLinearReadback.dyadicColumns values depth first last).map (fun column => column row) =
      DyadicPrimitivePaths.dyadicIncrements (values row) depth first last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih =>
    rw [DyadicBlockLinearReadback.dyadicColumns, Map.map_append, ih, ih, DyadicPrimitivePaths.dyadicIncrements]

/-- Weighted sums of original dyadic columns equal the dyadic increments of the weighted source.

The finite weighted sum distributes over the original scalar endpoint difference. The retained left and right midpoint
tails keep the same column order. -/
private theorem columns_weighted {size : Nat} (values : Fin size → Fraction.Rational → Basic.Canonical)
    (coefficients : Fin size → Basic.Canonical) (depth : Nat) (first last : Fraction.Rational) :
    (DyadicBlockLinearReadback.dyadicColumns values depth first last).map (fun column => FiniteSum.Fin.sumFin (fun row
      => coefficients row * column row)) =
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => FiniteSum.Fin.sumFin (fun row => coefficients row * values
        row parameter)) depth first last := by
  induction depth generalizing first last with
  | zero =>
      apply congrArg List.singleton
      change FiniteSum.Fin.sumFin _ = FiniteSum.Fin.sumFin _ - FiniteSum.Fin.sumFin _
      rw [← FiniteSum.Fin.sumFin_sub]
      exact FiniteSum.Fin.sumFin_congr (fun row => by ring1)
  | succ depth ih =>
    rw [DyadicBlockLinearReadback.dyadicColumns, Map.map_append, ih, ih, DyadicPrimitivePaths.dyadicIncrements]

/-- Concatenate the original blocks' dyadic column lists at their common retained depth.

The block order and each row's original source function remain unchanged in the resulting column list. -/
private def blockColumns {size : Nat} (depth : Nat) :
    List (Fin size → Fraction.Rational → Basic.Canonical) → List (Fin size → Basic.Canonical)
  | [] => []
  | values :: remaining => DyadicBlockLinearReadback.dyadicColumns values depth 0 1 ++
    Purelib.Integration.Path.DyadicBlockLinearReadback.blockColumns depth remaining

/-- The concatenated column count is the original block count times two to the retained depth.

Each original block contributes its exact dyadic column count. Structural concatenation retains those counts and their
original list order. -/
private theorem blocks_length {size : Nat} (blocks : List (Fin size → Fraction.Rational → Basic.Canonical)) (depth :
  Nat) :
    (DyadicBlockLinearReadback.blockColumns depth blocks).length = blocks.length * 2 ^ depth := by
  induction blocks with
  | nil => exact (Nat.zero_mul _).symm
  | cons values blocks ih =>
      rw [DyadicBlockLinearReadback.blockColumns, Append.length_append, DyadicBlockLinearReadback.columns_length, ih,
        List.length_cons, Nat.succ_mul, Nat.add_comm]

/-- Reading an original row from block columns gives the concatenated dyadic increments of that row.

Each original block keeps the selected row's full dyadic increments. Structural concatenation reads the same block spine
without equating row functions. -/
private theorem blocks_row {size : Nat} (blocks : List (Fin size → Fraction.Rational → Basic.Canonical))
    (depth : Nat) (row : Fin size) :
    (DyadicBlockLinearReadback.blockColumns depth blocks).map (fun column => column row) =
      (blocks.map (fun values => DyadicPrimitivePaths.dyadicIncrements (values row) depth 0 1)).flatten := by
  induction blocks with
  | nil => rfl
  | cons values blocks ih =>
      rw [DyadicBlockLinearReadback.blockColumns, Map.map_append, DyadicBlockLinearReadback.columns_row, ih]
      rfl

/-- Weighted block-column readings equal the concatenated dyadic increments of the weighted original sources.

The retained coefficient family weights each original column pointwise. Each block preserves that finite readback before
the ordered lists are concatenated. -/
private theorem blocks_weighted {size : Nat} (blocks : List (Fin size → Fraction.Rational → Basic.Canonical))
    (coefficients : Fin size → Basic.Canonical) (depth : Nat) :
    (DyadicBlockLinearReadback.blockColumns depth blocks).map (fun column => FiniteSum.Fin.sumFin (fun row =>
      coefficients row * column row)) =
      (blocks.map (fun values => DyadicPrimitivePaths.dyadicIncrements
        (fun parameter => FiniteSum.Fin.sumFin (fun row => coefficients row * values row parameter)) depth 0 1)).flatten
          := by
  induction blocks with
  | nil => rfl
  | cons values blocks ih =>
      rw [DyadicBlockLinearReadback.blockColumns, Map.map_append, DyadicBlockLinearReadback.columns_weighted, ih]
      rfl

/-- Equal-length column lists with equal original row readbacks have equal weighted readback lists.

The proof compares each retained scalar entry directly and preserves the supplied coefficient family without equating
functions. -/
theorem weighted_map_eq {size : Nat} (coefficients : Fin size → Basic.Canonical)
    (left right : List (Fin size → Basic.Canonical)) (lengths : left.length = right.length)
    (rows : ∀ row, left.map (fun column => column row) = right.map (fun column => column row)) :
    left.map (fun column => FiniteSum.Fin.sumFin (fun row => coefficients row * column row)) =
      right.map (fun column => FiniteSum.Fin.sumFin (fun row => coefficients row * column row)) := by
  induction left generalizing right with
  | nil => cases right with
    | nil => rfl
    | cons => cases lengths
  | cons head left ih => cases right with
    | nil => cases lengths
    | cons other right =>
        have entry (row : Fin size) : head row = other row ∧
            left.map (fun column => column row) = right.map (fun column => column row) :=
          List.cons.inj (rows row)
        apply congrArg₂ List.cons
        · exact FiniteSum.Fin.sumFin_congr (fun row => congrArg (fun value => coefficients row * value) (entry row).1)
        · exact ih right (Nat.succ.inj lengths) (fun row => (entry row).2)

/-- Recover the exact weighted dyadic block increments from retained column length and row certificates.

The given columns need not be reconstructed; their original row readbacks certify the weighted result against the same
ordered block sources. -/
theorem dyadicBlocks_linear_readback {size : Nat} (blocks : List (Fin size → Fraction.Rational → Basic.Canonical))
    (coefficients : Fin size → Basic.Canonical) (depth : Nat) (columns : List (Fin size → Basic.Canonical))
    (lengths : columns.length = blocks.length * 2 ^ depth)
    (rows : ∀ row, columns.map (fun column => column row) =
      (blocks.map (fun values => DyadicPrimitivePaths.dyadicIncrements (values row) depth 0 1)).flatten) :
    columns.map (fun column => FiniteSum.Fin.sumFin (fun row => coefficients row * column row)) =
      (blocks.map (fun values => DyadicPrimitivePaths.dyadicIncrements
        (fun parameter => FiniteSum.Fin.sumFin (fun row => coefficients row * values row parameter)) depth 0 1)).flatten
          := by
  exact (DyadicBlockLinearReadback.weighted_map_eq coefficients columns (DyadicBlockLinearReadback.blockColumns depth
    blocks)
    (lengths.trans (DyadicBlockLinearReadback.blocks_length blocks depth).symm)
    (fun row => (rows row).trans (DyadicBlockLinearReadback.blocks_row blocks depth row).symm)).trans
      (DyadicBlockLinearReadback.blocks_weighted blocks coefficients depth)

end Purelib.Integration.Path.DyadicBlockLinearReadback

end
