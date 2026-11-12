module
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

public section

/-! One computable tolerance pays both area joins and endpoint accumulation. -/
namespace Purelib.Integration.Budget.Path.Aggregation
open Purelib.Data.Rat
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior in
open Purelib.Riemann.Normalization in
/-- The smaller of one and the retained fragment-local tolerance for the original count, bound and target. -/
@[expose] def aggregationTolerance (count : Nat) (bound target : Coordinate) : Coordinate :=
  min 1 (PairedFragmentBlocks.fragmentLocalTolerance count bound target)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior in
open Purelib.Integration in
open Purelib.Riemann.Normalization in
/-- A nonnegative original bound and positive target give a positive aggregation tolerance. -/
theorem aggregationTolerance_positive (count : Nat) {bound target : Coordinate}
    (boundNN : 0 ≤ bound) (positive : 0 < target) :
    0 < aggregationTolerance count bound target :=
  Basic.lt_min (by decide +kernel) (PairedFragmentBlocks.fragmentLocalTolerance_positive count boundNN
    positive)

open Purelib.Integration in
open Purelib.Riemann.Normalization in
/-- The retained aggregation tolerance is at most one. -/
theorem aggregationTolerance_le_one (count : Nat) (bound target : Coordinate) :
    aggregationTolerance count bound target ≤ 1 :=
      Basic.min_le_left ..

open Purelib.Data.Rat in
open Purelib.Riemann.Normalization in
/-- The explicit squared-count and fourth-power interaction cost is nonnegative under the original nonnegative bound. -/
private theorem cost_nonnegative (count : Nat) {bound : Coordinate} (boundNN : 0 ≤ bound) :
    0 ≤ 2 * ((count : Coordinate)^2 + 16 * (count : Coordinate)^4 * bound)
      :=
  Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg
    (Arithmetic.sq_nonneg_direct _)
    (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
        boundNN))

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Riemann.Normalization in
/-- The retained aggregation tolerance makes the full count-dependent area cost strictly smaller than the positive
target. -/
theorem aggregationTolerance_area_paid (count : Nat) {bound target : Coordinate}
    (boundNN : 0 ≤ bound) (positive : 0 < target) :
    2 * ((count : Coordinate)^2 + 16 * (count : Coordinate)^4 * bound) *
      aggregationTolerance count bound target < target := by
  have costNN := cost_nonnegative count boundNN
  have denominator := Arithmetic.add_pos_of_nonneg_of_pos_direct costNN (by
      decide : (0 : Coordinate) < 1)
  have localPos := PairedFragmentBlocks.fragmentLocalTolerance_positive count boundNN positive
  have paid : (2 * ((count : Coordinate)^2 + 16 * (count : Coordinate)^4 *
    bound) + 1) *
      PairedFragmentBlocks.fragmentLocalTolerance count bound target = target := by
    rw [Fraction.Field.mul_comm]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ denominator.ne'
  have strict := Arithmetic.add_lt_add_left_direct localPos
    (2 * ((count : Coordinate)^2 + 16 * (count : Coordinate)^4 * bound) *
      PairedFragmentBlocks.fragmentLocalTolerance count bound target)
  rw [Fraction.Field.add_comm _ (0 : Coordinate), Fraction.Field.zero_add] at strict
  have exactPaid := strict.trans_eq ((show
    2 * ((count : Coordinate)^2 + 16 * (count : Coordinate)^4 * bound) *
      PairedFragmentBlocks.fragmentLocalTolerance count bound target +
      PairedFragmentBlocks.fragmentLocalTolerance count bound target =
    (2 * ((count : Coordinate)^2 + 16 * (count : Coordinate)^4 * bound) + 1)
      *
      PairedFragmentBlocks.fragmentLocalTolerance count bound target by ring1).trans paid)
  exact (Arithmetic.mul_le_mul_of_nonneg_left_direct (Basic.min_le_right ..)
    costNN).trans_lt exactPaid

open Purelib.Data.Rat
open Purelib.Integration
open Purelib.Riemann.Normalization
/-- The retained aggregation tolerance makes the squared-count total cost strictly smaller than the positive target. -/
theorem aggregationTolerance_total_paid (count : Nat) {bound target : Coordinate}
    (boundNN : 0 ≤ bound) (positive : 0 < target) :
    (count : Coordinate)^2 * aggregationTolerance count bound target <
      target := by
  have extraNN : 0 ≤ (count : Coordinate)^2 + 32 * (count : Coordinate)^4 *
    bound :=
    add_nonneg (Arithmetic.sq_nonneg_direct _) (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (Arithmetic.pow_nonneg_direct
        (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4)) boundNN)
  have costLe : (count : Coordinate)^2 ≤ 2 * ((count : Coordinate)^2 + 16 *
    (count : Coordinate)^4 * bound) :=
    (show (count : Coordinate)^2 ≤ (count : Coordinate)^2 +
      ((count : Coordinate)^2 + 32 * (count : Coordinate)^4 * bound) from
        le_add_of_nonneg_right extraNN).trans_eq (by ring1)
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct costLe
    (aggregationTolerance_positive count boundNN positive).le).trans_lt
      (aggregationTolerance_area_paid count boundNN positive)

/-- The original area cost remains bounded by the target after scaling by the retained mass squared.

The local-area and total-interaction contributions retain their distinct mass factors and exact numerical coefficients.
-/
theorem aggregationTolerance_area_scaled (count : Nat) {bound target : Coordinate}
    (boundNN : 0 ≤ bound) (positive : 0 < target) (mass : Coordinate) :
    2 * ((count : Coordinate)^2 * (aggregationTolerance count bound target
      * mass^2) +
      16 * (count : Coordinate)^4 * (aggregationTolerance count bound
        target * mass) * (bound * mass)) ≤
      target * mass^2 := by
  have estimate := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (aggregationTolerance_area_paid count boundNN positive).le
      (Arithmetic.sq_nonneg_direct mass)
  exact (show 2 * ((count : Coordinate)^2 * (aggregationTolerance count
    bound target * mass^2) +
      16 * (count : Coordinate)^4 * (aggregationTolerance count bound
        target * mass) * (bound * mass)) =
    (2 * ((count : Coordinate)^2 + 16 * (count : Coordinate)^4 * bound) *
      aggregationTolerance count bound target) * mass^2 by ring1).trans_le estimate

/-- For nonnegative mass, the scaled squared-count total cost meets the original target times that mass. -/
theorem aggregationTolerance_total_scaled (count : Nat) {bound target mass : Coordinate}
    (boundNN : 0 ≤ bound) (positive : 0 < target) (massNN : 0 ≤ mass) :
    (count : Coordinate)^2 * (aggregationTolerance count bound target *
      mass) ≤ target * mass :=
  (show (count : Coordinate)^2 * (aggregationTolerance count bound target
    * mass) =
    ((count : Coordinate)^2 * aggregationTolerance count bound target) *
      mass by ring1).trans_le
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (aggregationTolerance_total_paid count boundNN positive).le massNN)

end Purelib.Integration.Budget.Path.Aggregation
