module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.IncrementAreaReplacement
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Pay all four endpoint corrections without discarding their polygon area. -/
namespace Purelib.Integration.Path.IncrementAreaDoubleRestoration

open Purelib.Integration.Path.IncrementArea
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

variable {increments : List Purelib.Integration.Path.IncrementArea.Gaussian}

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path
/-- Bound the total of an original summary bracketed by two error-bounded increments.

The resulting squared norm is at most four times the original total bound plus six times the common endpoint error. -/
theorem bracket_total_bound (summary : IncrementArea.Summary increments) (first last : IncrementArea.Gaussian)
    {error bound : IncrementArea.Coordinate} (firstSmall : Data.Gaussian.Norm.Basic.normSq first ≤ error) (lastSmall :
      Data.Gaussian.Norm.Basic.normSq last ≤ error)
    (bounded : Data.Gaussian.Norm.Basic.normSq summary.total ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (IncrementAreaReplacement.bracket summary first last).total ≤ 4 * bound + 6 * error
      := by
  rw [IncrementAreaReplacement.bracket_total]
  have incoming := (Norm.Bounds.normSq_add_le_two first summary.total).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct firstSmall
      bounded) (by decide : (0 : IncrementArea.Coordinate) ≤ 2))
  exact ((Norm.Bounds.normSq_add_le_two (first + summary.total) last).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct incoming
      lastSmall) (by decide : (0 : IncrementArea.Coordinate) ≤ 2))).trans_eq (by ring1)

/-- Two successive endpoint brackets change the original total by at most sixteen times the common squared-norm error.
-/
theorem doubleBracket_total_error (summary : IncrementArea.Summary increments) (first last incoming outgoing :
  IncrementArea.Gaussian)
    {error : IncrementArea.Coordinate} (firstSmall : Data.Gaussian.Norm.Basic.normSq first ≤ error) (lastSmall :
      Data.Gaussian.Norm.Basic.normSq last ≤ error)
    (incomingSmall : Data.Gaussian.Norm.Basic.normSq incoming ≤ error) (outgoingSmall : Data.Gaussian.Norm.Basic.normSq
      outgoing ≤
      error) :
    Data.Gaussian.Norm.Basic.normSq ((IncrementAreaReplacement.bracket (IncrementAreaReplacement.bracket summary first
      last)
      incoming outgoing).total - summary.total) ≤ 16 * error := by
  rw [IncrementAreaReplacement.bracket_total, IncrementAreaReplacement.bracket_total]
  have left := (Norm.Bounds.normSq_add_le_two incoming first).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
      incomingSmall firstSmall) (by decide : (0 : IncrementArea.Coordinate) ≤ 2))
  have right := (Norm.Bounds.normSq_add_le_two last outgoing).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct lastSmall
      outgoingSmall) (by decide : (0 : IncrementArea.Coordinate) ≤ 2))
  rw [show incoming + (first + summary.total + last) + outgoing - summary.total =
    (incoming + first) + (last + outgoing) by ring1]
  exact ((Norm.Bounds.normSq_add_le_two (incoming + first) (last + outgoing)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct left right)
      (by decide : (0 : IncrementArea.Coordinate) ≤ 2))).trans_eq (by ring1)

/-- Two successive endpoint brackets have area error bounded using the original total and four endpoint errors.

The explicit estimate is 240 times error times the original total bound plus 352 times squared error. -/
theorem doubleBracket_area_error (summary : IncrementArea.Summary increments) (first last incoming outgoing :
  IncrementArea.Gaussian)
    {error bound : IncrementArea.Coordinate} (firstSmall : Data.Gaussian.Norm.Basic.normSq first ≤ error) (lastSmall :
      Data.Gaussian.Norm.Basic.normSq last ≤ error)
    (incomingSmall : Data.Gaussian.Norm.Basic.normSq incoming ≤ error) (outgoingSmall : Data.Gaussian.Norm.Basic.normSq
      outgoing ≤
      error)
    (bounded : Data.Gaussian.Norm.Basic.normSq summary.total ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq ((IncrementAreaReplacement.bracket (IncrementAreaReplacement.bracket summary first
      last)
      incoming outgoing).area - summary.area) ≤
      240 * error * bound + 352 * error^2 := by
  have inner := IncrementAreaReplacement.bracket_area_error summary first last firstSmall lastSmall bounded
  have outer := IncrementAreaReplacement.bracket_area_error (IncrementAreaReplacement.bracket summary first last)
    incoming outgoing incomingSmall outgoingSmall
    (IncrementAreaDoubleRestoration.bracket_total_bound summary first last firstSmall lastSmall bounded)
  exact ((Norm.Bounds.normSq_sub_le_via (IncrementAreaReplacement.bracket (IncrementAreaReplacement.bracket summary
    first last) incoming outgoing).area
    (IncrementAreaReplacement.bracket summary first last).area summary.area).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct outer
      inner) (by decide : (0 : IncrementArea.Coordinate) ≤ 2))).trans_eq (by ring1)

end Purelib.Integration.Path.IncrementAreaDoubleRestoration
