module
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
public import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
public import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Literal increment paths underlying dyadic primitive area

These finite lists retain every intermediate primitive excursion. Their
path area is exactly the existing dyadic boundary area after anchoring, and
grouping them by a coarser dyadic mesh preserves the complete path.
-/

namespace Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths

open Purelib.Data.Rat
open Purelib.Data.Gaussian
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic
open Purelib.Riemann.Branches

open Purelib.Data.List

/-- The rational carrier for dyadic path parameters. -/
private abbrev Coordinate := Fraction.Rational
/-- The canonical Gaussian carrier for retained path increments. -/
private abbrev Gaussian := Basic.Canonical

open Purelib.Data.Gaussian.Basic.Canonical

/-- List the original value increments along the ordered depth-indexed midpoint subdivision.

Each successor depth concatenates the left and right midpoint branches in that
order, retaining the same source values and endpoint parameters. -/
@[expose] def dyadicIncrements (value : Fraction.Rational → Basic.Canonical) : Nat → Fraction.Rational →
  Fraction.Rational → List Basic.Canonical
  | 0, first, last => [value last - value first]
  | depth + 1, first, last =>
      let middle := PreparedBoxPartitions.midpoint first last
      Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements value depth first middle ++
        Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths.dyadicIncrements value depth middle last

/-- The ordered dyadic increments sum to the exact original endpoint displacement.

The midpoint contributions cancel at every successor depth, with each retained
increment read in its original branch order. -/
theorem dyadicIncrements_sum (value : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last :
  Fraction.Rational) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (DyadicPrimitivePaths.dyadicIncrements value depth first last) = value
      last - value
      first := by
  induction depth generalizing first last with
  | zero =>
      change (value last - value first) + 0 = value last - value first
      exact Basic.add_zero _
  | succ depth ih => rw [DyadicPrimitivePaths.dyadicIncrements, IncrementArea.sum_append, ih, ih]; ring1

/-- The original dyadic increment list has exactly two to the depth entries.

Each subdivision doubles the retained list length by concatenating its two
midpoint branches; neither values nor endpoint coincidences affect that count. -/
theorem dyadicIncrements_length (value : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last :
  Fraction.Rational) :
    (DyadicPrimitivePaths.dyadicIncrements value depth first last).length = 2 ^ depth := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih =>
      rewrite [DyadicPrimitivePaths.dyadicIncrements, Append.length_append, ih, ih, pow_succ]
      exact (Nat.mul_two _).symm

/-- Subtracting a fixed Gaussian constant from all original values preserves the exact increment list. -/
theorem dyadicIncrements_sub_constant (value : Fraction.Rational → Basic.Canonical) (constant : Basic.Canonical)
    (depth : Nat) (first last : Fraction.Rational) :
    DyadicPrimitivePaths.dyadicIncrements (fun parameter => value parameter - constant) depth first last =
      DyadicPrimitivePaths.dyadicIncrements value depth first last := by
  induction depth generalizing first last with
  | zero =>
      change [(value last - constant) - (value first - constant)] = [value last - value first]
      rw [show (value last - constant) - (value first - constant) = value last - value first by ring1]
  | succ depth ih => rw [DyadicPrimitivePaths.dyadicIncrements, DyadicPrimitivePaths.dyadicIncrements, ih, ih]

/-- Tracing the dyadic increments from the original first value recovers their finite dyadic area. -/
theorem traceArea_dyadicIncrements (value : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last :
  Fraction.Rational) :
    IncrementArea.traceArea (value first) (DyadicPrimitivePaths.dyadicIncrements value depth first last) =
      DyadicBoundaryRibbon.dyadicArea value depth first last := by
  induction depth generalizing first last with
  | zero =>
      rw [DyadicPrimitivePaths.dyadicIncrements, IncrementArea.traceArea, IncrementArea.traceArea, Basic.add_zero,
        show value first + (value last - value first) = value last by ring1]
      rfl
  | succ depth ih =>
      rw [DyadicPrimitivePaths.dyadicIncrements, IncrementArea.traceArea_append,
        DyadicPrimitivePaths.dyadicIncrements_sum,
        show value first + (value (PreparedBoxPartitions.midpoint first last) - value first) =
          value (PreparedBoxPartitions.midpoint first last) by ring1, ih, ih]
      rfl

/-- An original zero initial value identifies zero-start increment area with finite dyadic area. -/
theorem pathArea_dyadicIncrements (value : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last :
  Fraction.Rational)
    (initial : value first = 0) : IncrementArea.pathArea (DyadicPrimitivePaths.dyadicIncrements value depth first last)
      = DyadicBoundaryRibbon.dyadicArea value depth first last := by
  have equal := DyadicPrimitivePaths.traceArea_dyadicIncrements value depth first last
  rw [initial] at equal
  exact equal

/-- Flattening fine increment lists over the original coarse dyadic edges equals subdivision at the summed depth.

The exact original endpoint owners and edge order remain fixed, and the two midpoint conventions are identified
arithmetically. -/
theorem dyadicEdges_flatten_increments (value : Fraction.Rational → Basic.Canonical) (coarse fine : Nat) (first last :
  ClearSheetContinuation.Subdivision.Endpoint) :
    ((ClearSheetContinuation.Subdivision.dyadicEdges coarse first last).map (fun edge =>
      DyadicPrimitivePaths.dyadicIncrements value fine edge.left.parameter edge.right.parameter)).flatten =
      DyadicPrimitivePaths.dyadicIncrements value (coarse + fine) first.parameter last.parameter := by
  induction coarse generalizing first last with
  | zero =>
      change DyadicPrimitivePaths.dyadicIncrements value fine first.parameter last.parameter ++ [] = _
      rewrite [Nat.zero_add]
      exact Append.append_nil _
  | succ coarse ih =>
      rw [ClearSheetContinuation.Subdivision.dyadicEdges, Map.map_append, Flatten.flatten_append, ih, ih, Nat.succ_add,
        DyadicPrimitivePaths.dyadicIncrements]
      have middle : ClearSheetContinuation.midpoint first.parameter last.parameter =
          PreparedBoxPartitions.midpoint first.parameter last.parameter := by
        unfold ClearSheetContinuation.midpoint PreparedBoxPartitions.midpoint
        apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
        calc
          _ = first.parameter + last.parameter := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
          _ = first.parameter * 2 + ((last.parameter - first.parameter) / 2) * 2 := by
            rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]; ring1
          _ = _ := by ring1
      change dyadicIncrements value (coarse + fine) first.parameter
          (ClearSheetContinuation.midpoint first.parameter last.parameter) ++
        dyadicIncrements value (coarse + fine)
          (ClearSheetContinuation.midpoint first.parameter last.parameter) last.parameter = _
      exact congrArg₂ List.append
        (congrArg (fun midpoint => dyadicIncrements value (coarse + fine) first.parameter midpoint) middle)
        (congrArg (fun midpoint => dyadicIncrements value (coarse + fine) midpoint last.parameter) middle)

end Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths

end
