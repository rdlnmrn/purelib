module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.RectangularUniformGeometry
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.Ring

/-!
# Exact geometric cuts of affine edges by a rectangular model grid

The parameter partition includes every crossing of a cached grid coordinate.
Its adjacent pieces have computably located coarse cells, including reversed,
stationary and boundary-aligned edges. The exact coordinate specification links
each crossing parameter to its original cut and bounds each adjacent segment
endpoint through the same retained cell boundaries.
-/

public section

namespace Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle.Partition
open Purelib.Riemann.Normalization

open Purelib.Riemann.Integration
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Box)
open Purelib.Riemann.Normalization.RectangularInverseModels (Axis Geometry)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Data.Gaussian.Basic (add_re add_im mul_re mul_im sub_re sub_im)

/-- Evaluate the affine segment between two Gaussian rational endpoints. -/
@[expose] def point (first last : InverseRootPolynomial.Gaussian) (parameter : InverseRootPolynomial.Coordinate) :
  Gaussian :=
  ⟨first.re + parameter * (last.re - first.re), first.im + parameter * (last.im - first.im)⟩

/-- The segment at parameter zero is its first endpoint. -/
theorem point_zero (first last : InverseRootPolynomial.Gaussian) : PreparedSegmentCuts.point first last 0 = first := by
  apply Data.Gaussian.Basic.ext <;> change _ + 0 * _ = _ <;> ring1

/-- The segment at parameter one is its last endpoint. -/
theorem point_one (first last : InverseRootPolynomial.Gaussian) : PreparedSegmentCuts.point first last 1 = last := by
  apply Data.Gaussian.Basic.ext <;> change _ + 1 * (_ - _) = _ <;> ring1

/-- The coordinate segment agrees with the Gaussian affine-line expression. -/
theorem point_eq_line (first last : InverseRootPolynomial.Gaussian) (parameter : InverseRootPolynomial.Coordinate) :
    PreparedSegmentCuts.point first last parameter = Affine.line first (last - first) parameter := by
  apply Data.Gaussian.Basic.ext <;>
    simp only [PreparedSegmentCuts.point, Affine.line, Gaussian.Cast.ofCoordinate_re,
      Gaussian.Cast.ofCoordinate_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1

/-- Restricting the parameter interval agrees with the segment between its evaluated endpoints. -/
theorem point_affine (first last : InverseRootPolynomial.Gaussian) (lower upper parameter :
  InverseRootPolynomial.Coordinate) :
    PreparedSegmentCuts.point first last (lower + parameter * (upper - lower)) =
      PreparedSegmentCuts.point (PreparedSegmentCuts.point first last lower) (PreparedSegmentCuts.point first last
        upper) parameter := by
  apply Data.Gaussian.Basic.ext <;> dsimp only [PreparedSegmentCuts.point] <;> ring1

/-- Compute the parameter of each axis-cut crossing for a nonzero velocity.

A stationary coordinate returns an empty crossing list; moving coordinates retain every supplied cut through exact
rational division. -/
@[expose] def crossings (start velocity : InverseRootPolynomial.Coordinate) (cuts : List
  InverseRootPolynomial.Coordinate) : List Coordinate :=
  if velocity = 0 then [] else cuts.map fun cut => (cut - start) / velocity

/-- The crossing list has no more entries than its cut list.

A stationary coordinate returns no entries; for a moving coordinate the original map contributes exactly one crossing
per supplied cut. -/
theorem crossings_length (start velocity : InverseRootPolynomial.Coordinate) (cuts : List
  InverseRootPolynomial.Coordinate) :
    (PreparedSegmentCuts.crossings start velocity cuts).length ≤ cuts.length := by
  unfold PreparedSegmentCuts.crossings
  split
  · exact Nat.zero_le _
  · rw [Map.length_map]

/-- Including more coordinate cuts includes all previous crossing parameters.

A stationary velocity has no crossings. Otherwise each original cut witness is transferred to the larger cut list while
its exact division readback remains unchanged. -/
theorem crossings_mono (start velocity : InverseRootPolynomial.Coordinate) {first last : List
  InverseRootPolynomial.Coordinate}
    (included : ∀ cut ∈ first, cut ∈ last) :
    ∀ parameter ∈ PreparedSegmentCuts.crossings start velocity first, parameter ∈ PreparedSegmentCuts.crossings start
      velocity last := by
  intro parameter member
  unfold PreparedSegmentCuts.crossings at member ⊢
  by_cases zero : velocity = 0
  · rewrite [if_pos zero] at member
    exact (List.not_mem_nil member).elim
  · rewrite [if_neg zero] at member ⊢
    obtain ⟨cut, present, equal⟩ := Map.mem_map.mp member
    exact Map.mem_map.mpr ⟨cut, included cut present, equal⟩

/-- A computed crossing parameter evaluates exactly to its coordinate cut. -/
private theorem crossing_eq (start velocity cut : InverseRootPolynomial.Coordinate) (nonzero : velocity ≠ 0) :
    start + ((cut - start) / velocity) * velocity = cut := by
  rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ _ nonzero]
  ring1

/-- The midpoint of a proper parameter interval lies strictly between its endpoints. -/
theorem midpoint_bounds (interval : Interval) :
    interval.lower < (interval.lower + interval.upper) / 2 ∧
      (interval.lower + interval.upper) / 2 < interval.upper := by
  have ordered : interval.lower < interval.upper := interval.ordered
  constructor
  · apply (Rat.Fraction.Order.Field.lt_div_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)).mpr
    exact (show interval.lower * 2 = interval.lower + interval.lower by ring1).trans_lt
      (Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct ordered interval.lower)
  · apply (Rat.Fraction.Order.Field.div_lt_iff_pos (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)).mpr
    exact (Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct ordered interval.upper).trans_eq
      (show interval.upper + interval.upper = interval.upper * 2 by ring1)

/-- For positive velocity, midpoint containment and absence of boundary crossings imply containment of both endpoints.

The supplied crossing equations and outside disjunctions retain the exact lower and upper cell boundaries. -/
private theorem increasing_bounds {start velocity lower upper lowCut highCut : InverseRootPolynomial.Coordinate}
    (positive : 0 < velocity) (interval : Interval)
    (lowEq : start + lowCut * velocity = lower) (highEq : start + highCut * velocity = upper)
    (lowOutside : lowCut ≤ interval.lower ∨ interval.upper ≤ lowCut)
    (highOutside : highCut ≤ interval.lower ∨ interval.upper ≤ highCut)
    (middleInside : lower ≤ start + ((interval.lower + interval.upper) / 2) * velocity ∧
      start + ((interval.lower + interval.upper) / 2) * velocity ≤ upper) :
    (lower ≤ start + interval.lower * velocity ∧ start + interval.lower * velocity ≤ upper) ∧
      (lower ≤ start + interval.upper * velocity ∧ start + interval.upper * velocity ≤ upper) := by
  have mid := PreparedSegmentCuts.midpoint_bounds interval
  have lowerBound : lower ≤ start + interval.lower * velocity := by
    rcases lowOutside with before | after
    · exact lowEq.symm.trans_le (Rat.Fraction.Order.Arithmetic.add_le_add_direct (Rat.Fraction.Order.Basic.le_refl
        start)
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct before positive.le))
    · have crossed := (Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct
        (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (mid.2.trans_le after) positive) start).trans_eq
          lowEq
      exact (not_lt_of_ge middleInside.1 crossed).elim
  have upperBound : start + interval.upper * velocity ≤ upper := by
    rcases highOutside with before | after
    · have crossed := highEq.symm.trans_lt (Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct
        (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct (before.trans_lt mid.1) positive) start)
      exact (not_lt_of_ge middleInside.2 crossed).elim
    · exact (Rat.Fraction.Order.Arithmetic.add_le_add_direct (Rat.Fraction.Order.Basic.le_refl start)
        (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct after positive.le)).trans_eq highEq
  have ordered : start + interval.lower * velocity ≤ start + interval.upper * velocity :=
    Rat.Fraction.Order.Arithmetic.add_le_add_direct (Rat.Fraction.Order.Basic.le_refl start)
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct interval.ordered.le positive.le)
  exact ⟨⟨lowerBound, ordered.trans upperBound⟩, ⟨lowerBound.trans ordered, upperBound⟩⟩

/-- A retained midpoint location bounds both closed interval endpoints.

Every crossing of either original cell boundary belongs to the retained cut
list, so the partition excludes internal boundary crossings. Stationary and
both signed velocity cases preserve those exact boundaries and parameters. -/
theorem coordinate_bounds {cuts : List InverseRootPolynomial.Coordinate}
    (partition : AxisPartition 0 1 cuts) {interval : Interval}
    (member : interval ∈ partition.intervals) (start velocity lower upper : InverseRootPolynomial.Coordinate)
    (included : ∀ cut ∈ [lower, upper], ∀ parameter ∈ PreparedSegmentCuts.crossings start velocity [cut], parameter ∈
      cuts)
    (middleInside : lower ≤ start + ((interval.lower + interval.upper) / 2) * velocity ∧
      start + ((interval.lower + interval.upper) / 2) * velocity ≤ upper) :
    (lower ≤ start + interval.lower * velocity ∧ start + interval.lower * velocity ≤ upper) ∧
      (lower ≤ start + interval.upper * velocity ∧ start + interval.upper * velocity ≤ upper) := by
  if zero : velocity = 0 then
    have scalar (parameter : Coordinate) : start + parameter * velocity = start := by
      rewrite [zero]
      exact show start + parameter * (0 : Coordinate) = start from by ring1
    rewrite [scalar] at middleInside
    rewrite [scalar, scalar]
    exact ⟨middleInside, middleInside⟩
  else
    have outside (cut : InverseRootPolynomial.Coordinate) (present : cut ∈ [lower, upper]) :
        (cut - start) / velocity ≤ interval.lower ∨ interval.upper ≤ (cut - start) / velocity := by
      apply partition.cut_outside member
      apply included cut present
      unfold PreparedSegmentCuts.crossings
      rewrite [if_neg zero]
      exact Map.mem_map.mpr ⟨cut, List.mem_cons_self, rfl⟩
    have low := outside lower (by exact List.mem_cons_self)
    have high := outside upper (by exact List.mem_cons_of_mem _ List.mem_cons_self)
    rcases lt_trichotomy 0 velocity with positive | equal | negative
    · exact PreparedSegmentCuts.increasing_bounds positive interval (PreparedSegmentCuts.crossing_eq start velocity
        lower zero)
        (PreparedSegmentCuts.crossing_eq start velocity upper zero) low high middleInside
    · exact (zero equal.symm).elim
    · have reflected (parameter : Coordinate) :
          -start + parameter * (-velocity) = -(start + parameter * velocity) := by ring1
      have lowEq : -start + ((upper - start) / velocity) * (-velocity) = -upper :=
        (reflected _).trans (congrArg Neg.neg (PreparedSegmentCuts.crossing_eq start velocity upper zero))
      have highEq : -start + ((lower - start) / velocity) * (-velocity) = -lower :=
        (reflected _).trans (congrArg Neg.neg (PreparedSegmentCuts.crossing_eq start velocity lower zero))
      have negativeMiddle : -upper ≤ -start + ((interval.lower + interval.upper) / 2) * (-velocity) ∧
          -start + ((interval.lower + interval.upper) / 2) * (-velocity) ≤ -lower := by
        rewrite [reflected]
        exact ⟨Rat.Fraction.Order.Arithmetic.neg_le_neg_direct middleInside.2,
          Rat.Fraction.Order.Arithmetic.neg_le_neg_direct middleInside.1⟩
      have positive : 0 < -velocity := by
        have flipped := Rat.Fraction.Order.Arithmetic.neg_lt_neg_direct negative
        have zeroNeg : -(0 : Coordinate) = 0 := by ring1
        rewrite [zeroNeg] at flipped
        exact flipped
      have reversed := PreparedSegmentCuts.increasing_bounds positive interval lowEq highEq high low negativeMiddle
      rewrite [reflected, reflected] at reversed
      exact ⟨⟨(Rat.Fraction.Order.Arithmetic.neg_le_neg_iff_direct _ _).mp reversed.1.2,
          (Rat.Fraction.Order.Arithmetic.neg_le_neg_iff_direct _ _).mp reversed.1.1⟩,
        ⟨(Rat.Fraction.Order.Arithmetic.neg_le_neg_iff_direct _ _).mp reversed.2.2,
          (Rat.Fraction.Order.Arithmetic.neg_le_neg_iff_direct _ _).mp reversed.2.1⟩⟩

end Purelib.Geometry.Rectangle.Partition.PreparedSegmentCuts

end
