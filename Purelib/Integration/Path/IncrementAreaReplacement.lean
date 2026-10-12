module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.IncrementAreaJoins
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Replacing an internal path while retaining its exterior corrections

The two explicit endpoint corrections use cached totals and areas. Equal
internal totals make every cross term with the surrounding path identical.
-/

namespace Purelib.Integration.Path.IncrementAreaReplacement

open Purelib.Integration.Path.IncrementArea
open Purelib.Integration.Path.IncrementArea.Summary

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Integration.Path.BoundaryRibbon (area area_bound)

variable {increments : List Purelib.Integration.Path.IncrementArea.Gaussian}

section
open Purelib.Integration.Path
/-- Bracket the original increment summary with the exact first and last connectors.

The retained summary is reused between a prepended connector and an appended singleton, preserving the original ordered
increments. -/
def bracket (summary : IncrementArea.Summary increments) (first last : IncrementArea.Gaussian) : IncrementArea.Summary
  (first :: (increments ++ [last])) :=
  ((IncrementAreaJoins.Summary.prepend summary first)).append (IncrementArea.Summary.build [last])

/-- The bracketed total is the first connector plus the original total plus the last connector. -/
theorem bracket_total (summary : IncrementArea.Summary increments) (first last : IncrementArea.Gaussian) :
    ((IncrementAreaReplacement.bracket summary first last)).total = first + summary.total + last := by
  change (first + summary.total) + (last + 0) = _
  ring1

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- The bracketed area is the original area plus the two directed connector-area contributions.

The first and last connectors are composed with the retained summary in their original order, including the contribution
from the first connector to the final endpoint. -/
theorem bracket_area (summary : IncrementArea.Summary increments) (first last : IncrementArea.Gaussian) :
    ((IncrementAreaReplacement.bracket summary first last)).area = summary.area + BoundaryRibbon.area first
      summary.total + BoundaryRibbon.area (first + summary.total) last := by
  change (summary.area + BoundaryRibbon.area first summary.total) + (0 + BoundaryRibbon.area last 0) +
    BoundaryRibbon.area (first + summary.total) (last + 0) = _
  simp only [IncrementArea.area_zero_right, Basic.add_zero, -eq_self, -iff_self]
  rfl

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Two connectors bounded by the same error change area by at most 24 times error times total bound plus 16 times error
squared. -/
theorem bracket_area_error (summary : IncrementArea.Summary increments) (first last : IncrementArea.Gaussian) {error
  bound : IncrementArea.Coordinate}
    (firstSmall : Data.Gaussian.Norm.Basic.normSq first ≤ error) (lastSmall : Data.Gaussian.Norm.Basic.normSq last ≤
      error)
      (bounded : Data.Gaussian.Norm.Basic.normSq summary.total ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (((IncrementAreaReplacement.bracket summary first last)).area - summary.area) ≤ 24 *
      error * bound + 16 * error ^ 2 := by
  have firstArea := IncrementAreaJoins.Summary.prepend_area_error summary first firstSmall bounded
  have totalBound := IncrementAreaJoins.Summary.prepend_total_bound summary first firstSmall bounded
  have lastArea : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area ((IncrementAreaJoins.Summary.prepend summary
    first)).total last) ≤ 4 * (2 * (error + bound)) * error := by
    have product := Fraction.Order.Arithmetic.mul_le_mul_direct totalBound lastSmall (Norm.Basic.normSq_nonneg _)
      ((Norm.Basic.normSq_nonneg _).trans totalBound)
    calc
      _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq ((IncrementAreaJoins.Summary.prepend summary first)).total *
        Data.Gaussian.Norm.Basic.normSq last := BoundaryRibbon.area_bound _ _
      _ = 4 * (Data.Gaussian.Norm.Basic.normSq ((IncrementAreaJoins.Summary.prepend summary first)).total *
        Data.Gaussian.Norm.Basic.normSq last) := by
        ring1
      _ ≤ 4 * (2 * (error + bound) * error) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by
        decide)
      _ = _ := by ring1
  have difference : ((IncrementAreaReplacement.bracket summary first last)).area - ((IncrementAreaJoins.Summary.prepend
    summary first)).area =
      BoundaryRibbon.area ((IncrementAreaJoins.Summary.prepend summary first)).total last := by
    rw [IncrementAreaReplacement.bracket_area]
    change summary.area + BoundaryRibbon.area first summary.total + BoundaryRibbon.area (first + summary.total) last -
      (summary.area + BoundaryRibbon.area first summary.total) = BoundaryRibbon.area (first + summary.total) last
    ring1
  have lastPaid : Data.Gaussian.Norm.Basic.normSq (((IncrementAreaReplacement.bracket summary first last)).area -
    ((IncrementAreaJoins.Summary.prepend summary first)).area) ≤ 4 * (2 * (error + bound)) * error := by
    rw [difference]; exact lastArea
  exact ((Norm.Bounds.normSq_sub_le_via ((IncrementAreaReplacement.bracket summary first last)).area
    ((IncrementAreaJoins.Summary.prepend summary first)).area summary.area).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add lastPaid firstArea) (by decide))).trans_eq
      (by ring1)

open Purelib.Integration.Path in
/-- Bracketing two equal-total summaries with the same connectors preserves their exact area difference. -/
theorem bracket_area_difference {leftPath rightPath : List IncrementArea.Gaussian} (left : IncrementArea.Summary
  leftPath) (right : IncrementArea.Summary rightPath)
    (same : left.total = right.total) (first last : IncrementArea.Gaussian) :
    ((IncrementAreaReplacement.bracket left first last)).area - ((IncrementAreaReplacement.bracket right first
      last)).area = left.area - right.area := by
  rw [IncrementAreaReplacement.bracket_area, IncrementAreaReplacement.bracket_area, same]
  ring1

end Purelib.Integration.Path.IncrementAreaReplacement
