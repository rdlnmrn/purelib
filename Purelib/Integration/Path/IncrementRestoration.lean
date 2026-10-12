module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.IncrementAreaReplacement
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Exact endpoint restoration and its finite triangle costs

The incoming connector is merged with the first source correction, as in
the retained cap path. The signed formula keeps that missing intermediate
vertex explicit, together with both source/chart endpoint triangles.
-/

namespace Purelib.Integration.Path.IncrementRestoration

open Purelib.Integration.Path.IncrementArea (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Integration.Path
/-- Add the directed chart-to-endpoint area to the retained radial value. -/
def potential (radial chart endpoint : IncrementArea.Gaussian) : Gaussian := radial + BoundaryRibbon.area chart endpoint

/-- The signed sum of the two endpoint detours minus the incoming connector-area correction.

The first and last chart, source and old points, and the previous point, retain their distinct roles in all three area
terms. -/
def detour (firstChart lastChart firstSource lastSource firstOld lastOld previous : IncrementArea.Gaussian) : Gaussian
  :=
  BoundaryRibbon.area (firstSource - firstOld) (firstChart - firstSource) +
    BoundaryRibbon.area (lastSource - lastChart) (lastOld - lastSource) -
    BoundaryRibbon.area (firstOld - previous) (firstSource - firstOld)

end

open Purelib.Integration.Path.IncrementRestoration in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- Express the restored source-path trace using the original summary area and explicit chart, old-point and detour
contributions.

The retained summary total must equal the original chart displacement; the restored path preserves the exact ordered
connectors and increments. -/
theorem trace_restored {path : List IncrementArea.Gaussian} (summary : IncrementArea.Summary path)
    (firstChart lastChart firstSource lastSource firstOld lastOld previous : IncrementArea.Gaussian)
    (total : summary.total = lastChart - firstChart) :
    IncrementArea.traceArea previous ((firstSource - previous) :: (((firstChart - firstSource) ::
      (path ++ [lastSource - lastChart])) ++ [lastOld - lastSource])) =
      summary.area + BoundaryRibbon.area firstChart lastChart + BoundaryRibbon.area firstOld firstChart +
        BoundaryRibbon.area lastChart lastOld +
        BoundaryRibbon.area previous firstOld + detour firstChart lastChart firstSource lastSource firstOld lastOld
          previous := by
  rw [IncrementArea.traceArea, show previous + (firstSource - previous) = firstSource by ring1,
    IncrementArea.traceArea_append, IncrementArea.traceArea,
    show firstSource + (firstChart - firstSource) = firstChart by ring1,
    IncrementArea.traceArea_append, ← summary.total_eq, total,
    show firstChart + (lastChart - firstChart) = lastChart by ring1,
    IncrementArea.traceArea, show lastChart + (lastSource - lastChart) = lastSource by ring1, IncrementArea.traceArea]
  have totalRestored : Data.Gaussian.Norm.Sum.Basic.gaussianSum ((firstChart - firstSource) :: (path ++ [lastSource -
    lastChart])) =
      lastSource - firstSource := by
    change firstChart - firstSource + Data.Gaussian.Norm.Sum.Basic.gaussianSum (path ++ [lastSource - lastChart]) = _
    rw [IncrementArea.sum_append, ← summary.total_eq, total]
    change _ + (_ + (_ + 0)) = _
    ring1
  rw [totalRestored, show firstSource + (lastSource - firstSource) = lastSource by ring1,
    IncrementArea.traceArea, show lastSource + (lastOld - lastSource) = lastOld by ring1, IncrementArea.traceArea,
    IncrementArea.traceArea_eq, ← summary.area_eq, ← summary.total_eq, total,
    BoundaryRibbon.area_sub_self_right]
  apply Basic.ext <;> simp only [detour, BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.add_re, Basic.add_im,
    Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.zero_re, Basic.zero_im] <;> ring1

open Purelib.Integration.Path.IncrementRestoration in
open Purelib.Integration.Path in
/-- Split restored energy discrepancy into original cell discrepancy, endpoint detour and incoming potential mismatch.

The identity retains all chart/source/old endpoints and the previous potential rather than replacing their separate
correction terms. -/
theorem restored_discrepancy {path : List IncrementArea.Gaussian} (summary : IncrementArea.Summary path)
    (firstChart lastChart firstSource lastSource firstOld lastOld previous firstRadial lastRadial previousPotential
      energy : IncrementArea.Gaussian)
    (total : summary.total = lastChart - firstChart) :
    energy - (-IncrementArea.traceArea previous ((firstSource - previous) :: (((firstChart - firstSource) ::
      (path ++ [lastSource - lastChart])) ++ [lastOld - lastSource])) + IncrementRestoration.potential lastRadial
        lastChart lastOld - previousPotential) =
      (energy - (-summary.area - BoundaryRibbon.area firstChart lastChart + lastRadial - firstRadial)) +
        detour firstChart lastChart firstSource lastSource firstOld lastOld previous -
        (IncrementRestoration.potential firstRadial firstChart firstOld - previousPotential - BoundaryRibbon.area
          previous firstOld) := by
  rw [IncrementRestoration.trace_restored summary firstChart lastChart firstSource lastSource firstOld lastOld previous
    total]
  have reversed : BoundaryRibbon.area firstOld firstChart = -BoundaryRibbon.area firstChart firstOld := by
    unfold BoundaryRibbon.area
    ring1
  rw [reversed]
  unfold IncrementRestoration.potential
  ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Squared-norm bounds on two Gaussian values bound their area by four times the product of those bounds. -/
private theorem area_le {first last : IncrementArea.Gaussian} {a b : IncrementArea.Coordinate} (firstBound :
  Data.Gaussian.Norm.Basic.normSq first ≤ a) (lastBound : Data.Gaussian.Norm.Basic.normSq last ≤ b) :
    Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area first last) ≤ 4 * a * b := by
  have product : Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq last ≤ a * b :=
    Fraction.Order.Arithmetic.mul_le_mul_direct firstBound lastBound
    (Norm.Basic.normSq_nonneg last) ((Norm.Basic.normSq_nonneg first).trans firstBound)
  calc
    _ ≤ 4 * Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq last := BoundaryRibbon.area_bound
      first last
    _ = 4 * (Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq last) := by ring1
    _ ≤ 4 * (a * b) := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide : (0 :
      IncrementArea.Coordinate) ≤ 4)
    _ = _ := by ring1

open Purelib.Integration.Path.IncrementRestoration in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The restored endpoint detour has squared norm at most 128 times the target plus eight times the joining bound.

The joining bound is at most one, the target is nonnegative, and separate source, chart and incoming displacement bounds
are retained. -/
theorem detour_bound {firstChart lastChart firstSource lastSource firstOld lastOld previous : IncrementArea.Gaussian}
  {target joining : IncrementArea.Coordinate}
    (targetNonnegative : 0 ≤ target) (joiningSmall : joining ≤ 1)
    (firstSourceBound : Data.Gaussian.Norm.Basic.normSq (firstSource - firstOld) ≤ joining)
    (lastSourceBound : Data.Gaussian.Norm.Basic.normSq (lastOld - lastSource) ≤ joining)
    (firstChartBound : Data.Gaussian.Norm.Basic.normSq (firstChart - firstSource) ≤ 4 * target)
    (lastChartBound : Data.Gaussian.Norm.Basic.normSq (lastSource - lastChart) ≤ 4 * target)
    (incomingBound : Data.Gaussian.Norm.Basic.normSq (firstOld - previous) ≤ joining) :
    Data.Gaussian.Norm.Basic.normSq (detour firstChart lastChart firstSource lastSource firstOld lastOld previous) ≤
      128 *
      target + 8 * joining := by
  have joiningNonnegative := (Norm.Basic.normSq_nonneg _).trans incomingBound
  have first : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area (firstSource - firstOld) (firstChart -
    firstSource)) ≤ 16
    * target :=
    (IncrementRestoration.area_le firstSourceBound firstChartBound).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct joiningSmall (by decide))
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) targetNonnegative)).trans_eq (by ring1))
  have last : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area (lastSource - lastChart) (lastOld - lastSource)) ≤
    16 *
    target :=
    (IncrementRestoration.area_le lastChartBound lastSourceBound).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct joiningSmall
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        targetNonnegative))).trans_eq (by ring1))
  have incoming : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area (firstOld - previous) (firstSource - firstOld))
    ≤ 4 *
    joining :=
    (IncrementRestoration.area_le incomingBound firstSourceBound).trans
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct joiningSmall
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) joiningNonnegative)).trans_eq (by ring1))
  have ends := (Norm.Bounds.normSq_add_le_two _ _).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add first last) (by decide))
  exact (Norm.Bounds.normSq_sub_le_two _ _).trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add ends incoming) (by decide)).trans_eq (by ring1))

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- Bound the restored potential mismatch by 80 times the target plus twice the joining bound.

The radial mismatch, both chart-to-old displacements, last displacement size and old-endpoint gap have separate retained
certificates. -/
theorem potential_join_bound {firstChart lastChart firstOld lastOld firstRadial lastRadial : IncrementArea.Gaussian}
  {target joining : IncrementArea.Coordinate}
    (base : Data.Gaussian.Norm.Basic.normSq (lastRadial - firstRadial - BoundaryRibbon.area firstChart lastChart) ≤
      joining)
    (firstBound : Data.Gaussian.Norm.Basic.normSq (firstChart - firstOld) ≤ target) (lastBound :
      Data.Gaussian.Norm.Basic.normSq
      (lastChart - lastOld) ≤ target)
    (lastSmall : Data.Gaussian.Norm.Basic.normSq (lastChart - lastOld) ≤ 1) (gapSmall : Data.Gaussian.Norm.Basic.normSq
      (lastOld -
      firstOld) ≤ 1) :
    Data.Gaussian.Norm.Basic.normSq (IncrementRestoration.potential lastRadial lastChart lastOld -
      IncrementRestoration.potential firstRadial firstChart firstOld - BoundaryRibbon.area firstOld lastOld) ≤
      80 * target + 2 * joining := by
  let u := firstChart - firstOld
  let v := lastChart - lastOld
  let d := lastOld - firstOld
  have identity : IncrementRestoration.potential lastRadial lastChart lastOld - IncrementRestoration.potential
    firstRadial firstChart firstOld - BoundaryRibbon.area firstOld lastOld =
      (lastRadial - firstRadial - BoundaryRibbon.area firstChart lastChart) + (BoundaryRibbon.area u d +
        BoundaryRibbon.area u v + BoundaryRibbon.area v d) := by
    apply Basic.ext <;> simp only [IncrementRestoration.potential, u, v, d, BoundaryRibbon.area,
      Data.Gaussian.Basic.conj,
      Basic.add_re, Basic.add_im, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
  have first : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area u d) ≤ 4 * target := (IncrementRestoration.area_le
    firstBound gapSmall).trans_eq (by ring1)
  have middle : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area u v) ≤ 4 * target := (IncrementRestoration.area_le
    firstBound lastSmall).trans_eq (by ring1)
  have last : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area v d) ≤ 4 * target := (IncrementRestoration.area_le
    lastBound gapSmall).trans_eq (by ring1)
  have pair := (Norm.Bounds.normSq_add_le_two _ _).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add first middle) (by decide))
  have quad := (Norm.Bounds.normSq_add_le_two _ _).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add pair last) (by decide))
  rw [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add base quad) (by decide)).trans_eq (by ring1))

open Purelib.Integration.Path.IncrementRestoration in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
/-- The combined cell, detour and joining errors fit 1024 times the sum of target and joining budgets.

The target and joining budgets are nonnegative and each of the three original Gaussian errors obeys its stated bound. -/
theorem combined_bound {cell detour join : IncrementArea.Gaussian} {target joining : IncrementArea.Coordinate}
    (targetNonnegative : 0 ≤ target) (joinNonnegative : 0 ≤ joining)
    (cellBound : Data.Gaussian.Norm.Basic.normSq cell ≤ target) (detourBound : Data.Gaussian.Norm.Basic.normSq detour ≤
      128 *
      target + 8 * joining)
    (joinBound : Data.Gaussian.Norm.Basic.normSq join ≤ 80 * target + 2 * joining) :
    Data.Gaussian.Norm.Basic.normSq (cell + detour - join) ≤ 1024 * (target + joining) := by
  have first := (Norm.Bounds.normSq_add_le_two _ _).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add cellBound detourBound) (by decide))
  have estimate := (Norm.Bounds.normSq_sub_le_two _ _).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (add_le_add first joinBound) (by decide))
  apply estimate.trans
  apply Fraction.Order.Arithmetic.le_of_sub_nonneg_direct
  exact (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : IncrementArea.Coordinate) ≤
    348) targetNonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : IncrementArea.Coordinate) ≤ 988)
      joinNonnegative)).trans_eq (by ring1)

end Purelib.Integration.Path.IncrementRestoration
