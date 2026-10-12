module
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Affine
import Purelib.Integration.Energy.Polygon

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
public import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Ribbon bounds on the actual recursively refined rectangle sides

The boundary implementation is the existing horizontal subdivision, viewed
as a sum on a rational parameter interval.  Each binary split doubles the
number of terms and halves their step.  The proof pays both effects together,
so its final bound is independent of the spatial depth.  Open endpoint
corrections are retained explicitly.
-/

namespace Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon

open Purelib.Data.Rat in
/-- The rational carrier for dyadic parameters and ribbon bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian carrier for dyadic values and areas. -/
private abbrev Gaussian := Basic.Canonical
open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Energy in
/-- Read the finite dyadic area of the original Gaussian-valued parameter path.

The exact depth and ordered rational endpoints determine the retained midpoint subdivision. -/
def dyadicArea (values : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last : Fraction.Rational) :
  Basic.Canonical :=
  PreparedBoxBoundary.horizontalBoundary (fun point => Polygon.energyPrimitivePoint (values point.re)) depth first last
    0

open Purelib.Integration.Path in
/-- At depth zero, dyadic area is the directed area of the two original endpoint values. -/
theorem dyadicArea_zero (values : Fraction.Rational → Basic.Canonical) (first last : Fraction.Rational) :
    dyadicArea values 0 first last = BoundaryRibbon.area (values first) (values last) := rfl

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Integration.Path in
/-- One dyadic refinement splits the original area at its exact midpoint. -/
theorem dyadicArea_succ (values : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last : Fraction.Rational) :
    dyadicArea values (depth + 1) first last = dyadicArea values
      depth first (PreparedBoxPartitions.midpoint first last) +
      dyadicArea values depth (PreparedBoxPartitions.midpoint first last) last := rfl

open Purelib.Integration.Path in
/-- Pointwise equality of the original parameter values preserves their finite dyadic area. -/
theorem dyadicArea_congr {left right : Fraction.Rational → Basic.Canonical} (equal : ∀ parameter, left parameter = right
  parameter)
    (depth : Nat) (first last : Fraction.Rational) : dyadicArea left depth first last =
      dyadicArea right depth first last := by
  induction depth generalizing first last with
  | zero => rw [dyadicArea_zero, dyadicArea_zero, equal, equal]
  | succ depth ih =>
    rw [dyadicArea_succ, dyadicArea_succ, ih, ih]

open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Energy
open Purelib.Integration.Path
/-- A horizontal paired-energy boundary is the dyadic area of the original values at the fixed height. -/
theorem horizontalBoundary_eq_dyadicArea (values : Basic.Canonical → Basic.Canonical)
    (depth : Nat) (first last height : Fraction.Rational) :
    PreparedBoxBoundary.horizontalBoundary (fun point => Polygon.energyPrimitivePoint (values point)) depth first last
      height =
      dyadicArea (fun coordinate => values ⟨coordinate, height⟩) depth first last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [PreparedBoxBoundary.horizontalBoundary, dyadicArea_succ, ih, ih]

/-- A vertical paired-energy boundary is the dyadic area of the original values at the fixed horizontal coordinate. -/
theorem verticalBoundary_eq_dyadicArea (values : Basic.Canonical → Basic.Canonical)
    (depth : Nat) (first last horizontal : Fraction.Rational) :
    PreparedBoxBoundary.verticalBoundary (fun point => Polygon.energyPrimitivePoint (values point)) depth first last
      horizontal =
      dyadicArea (fun coordinate => values ⟨horizontal, coordinate⟩) depth first last := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih => rw [PreparedBoxBoundary.verticalBoundary, dyadicArea_succ, ih, ih]

end

open Purelib.Data.Rat in
open Purelib.Geometry.Rectangle.Partition in
/-- An affine rational parameter change commutes with the exact retained midpoint. -/
theorem midpoint_affine (origin slope first last : Fraction.Rational) :
    PreparedBoxPartitions.midpoint (origin + slope * first) (origin + slope * last) = origin + slope *
      PreparedBoxPartitions.midpoint first last := by
  unfold PreparedBoxPartitions.midpoint
  rw [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  ring1

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path in
/-- An affine parameter change transports finite dyadic area to the exact transformed endpoints. -/
theorem dyadicArea_affine (values : Fraction.Rational → Basic.Canonical) (origin slope : Fraction.Rational)
    (depth : Nat) (first last : Fraction.Rational) :
    dyadicArea (fun parameter => values (origin + slope * parameter)) depth first last =
      dyadicArea values depth (origin + slope * first) (origin + slope * last) := by
  induction depth generalizing first last with
  | zero => rfl
  | succ depth ih =>
      rw [dyadicArea_succ, dyadicArea_succ, ih, ih,
        midpoint_affine]

section
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Energy
open Purelib.Integration.Path
/-- The horizontal boundary equals dyadic area along its exact unit-interval affine segment. -/
theorem horizontalBoundary_eq_lineArea (values : Basic.Canonical → Basic.Canonical)
    (depth : Nat) (first last height : Fraction.Rational) :
    PreparedBoxBoundary.horizontalBoundary (fun point => Polygon.energyPrimitivePoint (values point)) depth first last
      height =
      dyadicArea (fun parameter => values (Affine.line ⟨first, height⟩ (⟨last, height⟩ -
        ⟨first, height⟩) parameter)) depth 0 1 := by
  have lineEq (parameter : Fraction.Rational) :
      Affine.line ⟨first, height⟩ (⟨last, height⟩ - ⟨first, height⟩) parameter =
        ⟨first + (last - first) * parameter, height⟩ := by
    apply Basic.ext <;> simp only [Affine.line, Cast.Path.ofCoordinate, Basic.add_re, Basic.add_im, Basic.mul_re,
      Basic.mul_im, Basic.sub_re, Basic.sub_im] <;> ring1
  have affine := dyadicArea_affine (fun coordinate => values ⟨coordinate, height⟩) first
    (last - first) depth 0 1
  rw [Fraction.Field.mul_zero_direct, _root_.add_zero,
    Fraction.Field.mul_one_direct, show first + (last - first) = last by ring1] at affine
  exact (horizontalBoundary_eq_dyadicArea values depth first last height).trans
    (affine.symm.trans (dyadicArea_congr (fun parameter => congrArg values (lineEq
      parameter).symm) depth 0 1))

/-- The vertical boundary equals dyadic area along its exact unit-interval affine segment. -/
theorem verticalBoundary_eq_lineArea (values : Basic.Canonical → Basic.Canonical)
    (depth : Nat) (first last horizontal : Fraction.Rational) :
    PreparedBoxBoundary.verticalBoundary (fun point => Polygon.energyPrimitivePoint (values point)) depth first last
      horizontal =
      dyadicArea (fun parameter => values (Affine.line ⟨horizontal, first⟩ (⟨horizontal,
        last⟩ - ⟨horizontal, first⟩) parameter)) depth 0 1 := by
  have lineEq (parameter : Fraction.Rational) :
      Affine.line ⟨horizontal, first⟩ (⟨horizontal, last⟩ - ⟨horizontal, first⟩) parameter =
        ⟨horizontal, first + (last - first) * parameter⟩ := by
    apply Basic.ext <;> simp only [Affine.line, Cast.Path.ofCoordinate, Basic.add_re, Basic.add_im, Basic.mul_re,
      Basic.mul_im, Basic.sub_re, Basic.sub_im] <;> ring1
  have affine := dyadicArea_affine (fun coordinate => values ⟨horizontal, coordinate⟩) first
    (last - first) depth 0 1
  rw [Fraction.Field.mul_zero_direct, _root_.add_zero,
    Fraction.Field.mul_one_direct, show first + (last - first) = last by ring1] at affine
  exact (verticalBoundary_eq_dyadicArea values depth first last horizontal).trans
    (affine.symm.trans (dyadicArea_congr (fun parameter => congrArg values (lineEq
      parameter).symm) depth 0 1))

end

open Purelib.Integration.Path in
/-- Subtract the two original dyadic areas and their exact endpoint ribbon correction.

The endpoint correction uses the right path values and the original left-minus-right displacement at both endpoints. -/
def dyadicDifference (left right : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last : Fraction.Rational) :
  Basic.Canonical :=
  dyadicArea left depth first last - dyadicArea right depth
    first last -
    (BoundaryRibbon.area (right last) (left last - right last) - BoundaryRibbon.area (right first) (left first - right
      first))

open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Path
/-- The endpoint-corrected dyadic area difference splits exactly at the original midpoint. -/
theorem dyadicDifference_succ (left right : Fraction.Rational → Basic.Canonical) (depth : Nat) (first last :
  Fraction.Rational) :
    dyadicDifference left right (depth + 1) first last =
      dyadicDifference left right depth first (PreparedBoxPartitions.midpoint first last) +
        dyadicDifference left right depth (PreparedBoxPartitions.midpoint first last) last
          := by
  simp only [dyadicDifference, dyadicArea_succ]
  ring1

/-- Uniform value error, right-path movement and difference drift bound the corrected dyadic area discrepancy.

Both ordered endpoints lie in the original interval; the estimate preserves the distinct slope and drift contributions
and is independent of subdivision depth. -/
theorem dyadicDifference_bound (left right : Fraction.Rational → Basic.Canonical) {lower upper error slope drift :
  Fraction.Rational}
    (errorNonnegative : 0 ≤ error)
    (errorLe : ∀ parameter, lower ≤ parameter ∧ parameter ≤ upper → Data.Gaussian.Norm.Basic.normSq (left parameter -
      right
      parameter) ≤ error)
    (rightLe : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      Data.Gaussian.Norm.Basic.normSq (right last - right first) ≤ slope * (last - first) ^ 2)
    (driftLe : ∀ first last, lower ≤ first ∧ first ≤ upper → lower ≤ last ∧ last ≤ upper →
      Data.Gaussian.Norm.Basic.normSq ((left last - right last) - (left first - right first)) ≤ drift * (last - first)
        ^ 2)
    (depth : Nat) {first last : Fraction.Rational} (firstInside : lower ≤ first ∧ first ≤ upper)
    (lastInside : lower ≤ last ∧ last ≤ upper) (ordered : first ≤ last) :
    Data.Gaussian.Norm.Basic.normSq (dyadicDifference left right depth first last) ≤ 8 *
      error *
      (4 * slope + drift) * (last - first) ^ 2 := by
  induction depth generalizing first last with
  | zero =>
      rw [dyadicDifference, dyadicArea_zero,
        dyadicArea_zero, BoundaryRibbon.area_difference, add_sub_cancel_right]
      exact BoundaryRibbon.correction_bound errorNonnegative (errorLe first firstInside) (errorLe last lastInside)
        (rightLe first last firstInside lastInside) (driftLe first last firstInside lastInside)
  | succ depth ih =>
      have between := PreparedBoxPartitions.midpoint_between ordered
      have middleInside := And.intro (firstInside.1.trans between.1) (between.2.trans lastInside.2)
      have firstBound := ih firstInside middleInside between.1
      have lastBound := ih middleInside lastInside between.2
      have twiceHalf : ((last - first) / 2) * 2 = last - first :=
        Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
      have leftHalf : PreparedBoxPartitions.midpoint first last - first = (last - first) / 2 := by
        unfold PreparedBoxPartitions.midpoint; ring1
      have rightHalf : last - PreparedBoxPartitions.midpoint first last = (last - first) / 2 := by
        calc
          _ = (last - first) - (last - first) / 2 := by unfold PreparedBoxPartitions.midpoint; ring1
          _ = ((last - first) / 2) * 2 - (last - first) / 2 := by rw [twiceHalf]
          _ = _ := by ring1
      rw [dyadicDifference_succ]
      calc
        _ ≤ 2 * (Data.Gaussian.Norm.Basic.normSq (dyadicDifference left right depth first
          (PreparedBoxPartitions.midpoint first last)) +
            Data.Gaussian.Norm.Basic.normSq (dyadicDifference left right depth
              (PreparedBoxPartitions.midpoint first last) last)) := Norm.Bounds.normSq_add_le_two _ _
        _ ≤ 2 * (8 * error * (4 * slope + drift) * (PreparedBoxPartitions.midpoint first last - first) ^ 2 +
            8 * error * (4 * slope + drift) * (last - PreparedBoxPartitions.midpoint first last) ^ 2) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add firstBound lastBound) (by decide)
        _ = 8 * error * (4 * slope + drift) * (((last - first) / 2) * 2) ^ 2 := by rw [leftHalf, rightHalf]; ring1
        _ = _ := by rw [twiceHalf]

end

end Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
