module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Integration.Path.IncrementRestoration
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-! Homogeneous endpoint restoration without normalizing the coefficient vector. -/
namespace Purelib.Integration.Path.HomogeneousIncrementRestoration

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path
/-- Squared-norm bounds on two Gaussian values bound their directed area by four times their product. -/
private theorem homogeneous_area_le {first last : IncrementArea.Gaussian} {a b : IncrementArea.Coordinate}
    (firstBound : Data.Gaussian.Norm.Basic.normSq first ≤ a) (lastBound : Data.Gaussian.Norm.Basic.normSq last ≤ b) :
    Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area first last) ≤ 4 * a * b := by
  have product := Fraction.Order.Arithmetic.mul_le_mul_direct firstBound lastBound (Norm.Basic.normSq_nonneg last)
    ((Norm.Basic.normSq_nonneg first).trans firstBound)
  exact (BoundaryRibbon.area_bound first last).trans
    ((show 4 * Data.Gaussian.Norm.Basic.normSq first * Data.Gaussian.Norm.Basic.normSq last = 4 *
      (Data.Gaussian.Norm.Basic.normSq
      first * Data.Gaussian.Norm.Basic.normSq last) by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct product (by decide)).trans_eq (by ring1)))

/-- The restored detour obeys the target-and-joining estimate multiplied by the square of the retained weight.

The source, chart and incoming bounds carry their original linear weight factors; the joining allowance is nonnegative
and at most one. -/
theorem detour_bound_homogeneous
    {firstChart lastChart firstSource lastSource firstOld lastOld previous : IncrementArea.Gaussian}
    {target joining weight : IncrementArea.Coordinate}
    (targetNonnegative : 0 ≤ target) (joiningNonnegative : 0 ≤ joining) (joiningSmall : joining ≤ 1)
    (firstSourceBound : Data.Gaussian.Norm.Basic.normSq (firstSource - firstOld) ≤ joining * weight)
    (lastSourceBound : Data.Gaussian.Norm.Basic.normSq (lastOld - lastSource) ≤ joining * weight)
    (firstChartBound : Data.Gaussian.Norm.Basic.normSq (firstChart - firstSource) ≤ 4 * target * weight)
    (lastChartBound : Data.Gaussian.Norm.Basic.normSq (lastSource - lastChart) ≤ 4 * target * weight)
    (incomingBound : Data.Gaussian.Norm.Basic.normSq (firstOld - previous) ≤ joining * weight) :
    Data.Gaussian.Norm.Basic.normSq (IncrementRestoration.detour firstChart lastChart firstSource lastSource firstOld
      lastOld
      previous) ≤
      (128 * target + 8 * joining) * weight ^ 2 := by
  have targetWeight : 0 ≤ 16 * target * weight ^ 2 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      targetNonnegative) (Fraction.Order.Arithmetic.sq_nonneg_direct _)
  have first : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area (firstSource - firstOld) (firstChart -
    firstSource)) ≤ 16
    * target * weight ^ 2 :=
    (HomogeneousIncrementRestoration.homogeneous_area_le firstSourceBound firstChartBound).trans
      ((show 4 * (joining * weight) * (4 * target * weight) = (16 * target * weight ^ 2) * joining by ring1).trans_le
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct joiningSmall targetWeight).trans_eq (by ring1)))
  have last : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area (lastSource - lastChart) (lastOld - lastSource)) ≤
    16 *
    target * weight ^ 2 :=
    (HomogeneousIncrementRestoration.homogeneous_area_le lastChartBound lastSourceBound).trans
      ((show 4 * (4 * target * weight) * (joining * weight) = (16 * target * weight ^ 2) * joining by ring1).trans_le
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct joiningSmall targetWeight).trans_eq (by ring1)))
  have incoming : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area (firstOld - previous) (firstSource - firstOld))
    ≤ 4 *
    joining * weight ^ 2 :=
    (HomogeneousIncrementRestoration.homogeneous_area_le incomingBound firstSourceBound).trans
      ((show 4 * (joining * weight) * (joining * weight) = (4 * joining * weight ^ 2) * joining by ring1).trans_le
        ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct joiningSmall
          (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
            joiningNonnegative) (Fraction.Order.Arithmetic.sq_nonneg_direct _))).trans_eq (by ring1)))
  have ends := (Norm.Bounds.normSq_add_le_two _ _).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct first last)
      (by decide))
  exact (Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct ends
      incoming) (by decide)).trans_eq (by ring1))

/-- The restored potential mismatch is bounded by the original target-and-joining cost times weight squared.

The radial mismatch carries a squared weight, while chart and gap displacement bounds retain their separate linear
weight factors. -/
theorem potential_join_bound_homogeneous
    {firstChart lastChart firstOld lastOld firstRadial lastRadial : IncrementArea.Gaussian} {target joining weight :
      IncrementArea.Coordinate}
    (base : Data.Gaussian.Norm.Basic.normSq (lastRadial - firstRadial - BoundaryRibbon.area firstChart lastChart) ≤
      joining *
      weight ^ 2)
    (firstBound : Data.Gaussian.Norm.Basic.normSq (firstChart - firstOld) ≤ target * weight)
    (lastBound : Data.Gaussian.Norm.Basic.normSq (lastChart - lastOld) ≤ target * weight)
    (lastSmall : Data.Gaussian.Norm.Basic.normSq (lastChart - lastOld) ≤ weight) (gapSmall :
      Data.Gaussian.Norm.Basic.normSq
      (lastOld - firstOld) ≤ weight) :
    Data.Gaussian.Norm.Basic.normSq (IncrementRestoration.potential lastRadial lastChart lastOld -
      IncrementRestoration.potential firstRadial firstChart firstOld - BoundaryRibbon.area firstOld lastOld) ≤
      (80 * target + 2 * joining) * weight ^ 2 := by
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
  have first : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area u d) ≤ 4 * target * weight ^ 2 :=
    (HomogeneousIncrementRestoration.homogeneous_area_le firstBound gapSmall).trans_eq (by ring1)
  have middle : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area u v) ≤ 4 * target * weight ^ 2 :=
    (HomogeneousIncrementRestoration.homogeneous_area_le firstBound lastSmall).trans_eq (by ring1)
  have last : Data.Gaussian.Norm.Basic.normSq (BoundaryRibbon.area v d) ≤ 4 * target * weight ^ 2 :=
    (HomogeneousIncrementRestoration.homogeneous_area_le lastBound gapSmall).trans_eq (by ring1)
  have pair := (Norm.Bounds.normSq_add_le_two _ _).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct first middle) (by decide))
  have quad := (Norm.Bounds.normSq_add_le_two _ _).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct pair last) (by decide))
  rw [identity]
  exact (Norm.Bounds.normSq_add_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct base quad)
      (by decide)).trans_eq (by ring1))

end Purelib.Integration.Path.HomogeneousIncrementRestoration
