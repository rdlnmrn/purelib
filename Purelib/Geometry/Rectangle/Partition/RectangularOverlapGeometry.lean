module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Affine

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Riemann.Normalization.RectangularInverseModels
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Riemann.Normalization

open Purelib.Riemann.Normalization.RectangularInverseModels

/-!
# Closed-cell overlaps on a strictly ordered rectangular grid

Two intervals containing the same point are equal or adjacent.  This
finite geometric fact lets a finer triangulation use the fixed coarse
model bank: its vertices need not be corners of the original grid.
-/

@[expose] public section

namespace Purelib.Geometry.Rectangle.Partition.RectangularOverlapGeometry

open scoped Purelib.Data.Nat

open Purelib.Riemann.Normalization.InverseRootPolynomial
open Purelib.Data.Gaussian.Basic.Canonical

namespace Axis

variable {steps : Nat}

/-- The cached axis coordinates preserve weak index order.

Finite induction follows the original ordered coordinate array; each successive step transports the retained
adjacent-coordinate inequality. -/
theorem coordinate_mono (axis : RectangularInverseModels.Axis steps) (first last : Fin (steps + 2)) (order : first ≤
  last) :
    axis.coordinates first ≤ axis.coordinates last := by
  induction last using Data.Fin.induction with
  | zero =>
      have equal : first = ⟨0, Nat.zero_lt_succ (steps + 1)⟩ := Fin.ext (Nat.eq_zero_of_le_zero order)
      rw [equal]
  | succ last ih =>
      by_cases equal : first = last.succ
      · rw [equal]
      · have earlier : first ≤ last.castSucc := by
          have different : first.val ≠ last.val + 1 := fun same => equal (Fin.ext same)
          change first.val ≤ last.val
          change first.val ≤ last.val + 1 at order
          omega
        exact (ih earlier).trans (axis.ordered last).le

/-- The cached axis coordinates preserve strict index order.

An original strictly later coordinate has a predecessor in the same retained finite array, whose adjacent step supplies
strictness. -/
theorem coordinate_lt (axis : RectangularInverseModels.Axis steps) (first last : Fin (steps + 2)) (order : first < last)
  :
    axis.coordinates first < axis.coordinates last := by
  revert order
  refine Data.Fin.cases_induction ?_ (fun last order => ?_) last
  · intro order
    exact (Nat.not_lt_zero _ order).elim
  · exact (Geometry.Rectangle.Partition.RectangularOverlapGeometry.Axis.coordinate_mono axis first last.castSucc
      (Nat.le_of_lt_succ order)).trans_lt (axis.ordered last)

/-- Only boundary points can have a different containing cell. -/
theorem unique_cell (axis : RectangularInverseModels.Axis steps) (first last : Fin (steps + 1)) {point :
  InverseRootPolynomial.Coordinate}
    (firstInside : axis.coordinates first.castSucc < point ∧ point < axis.coordinates first.succ)
    (lastInside : axis.coordinates last.castSucc ≤ point ∧ point ≤ axis.coordinates last.succ) : first = last := by
  rcases Nat.lt_trichotomy first.val last.val with before | equal | after
  · have ordered := Geometry.Rectangle.Partition.RectangularOverlapGeometry.Axis.coordinate_mono axis first.succ
      last.castSucc (Nat.succ_le_of_lt before)
    exact (not_lt_of_ge (ordered.trans lastInside.1) firstInside.2).elim
  · exact Fin.ext equal
  · have ordered := Geometry.Rectangle.Partition.RectangularOverlapGeometry.Axis.coordinate_mono axis last.succ
      first.castSucc (Nat.succ_le_of_lt after)
    exact (not_lt_of_ge (lastInside.2.trans ordered) firstInside.1).elim

/-- A common point in two increasing cells forces their shared endpoint and their consecutive finite indices. -/
theorem shared_boundary (axis : RectangularInverseModels.Axis steps) (first last : Fin (steps + 1)) {point :
  InverseRootPolynomial.Coordinate}
    (firstInside : axis.coordinates first.castSucc ≤ point ∧ point ≤ axis.coordinates first.succ)
    (lastInside : axis.coordinates last.castSucc ≤ point ∧ point ≤ axis.coordinates last.succ)
    (order : first < last) :
    ∃ edge : Fin steps, first = edge.castSucc ∧ last = edge.succ ∧ point = axis.coordinates edge.castSucc.succ := by
  have consecutive : last.val = first.val + 1 := by
    have upper : last.val ≤ first.val + 1 := by
      apply Nat.le_of_not_gt
      intro gap
      have separated := Geometry.Rectangle.Partition.RectangularOverlapGeometry.Axis.coordinate_lt axis first.succ
        last.castSucc gap
      exact (not_lt_of_ge (lastInside.1.trans firstInside.2) separated)
    change first.val < last.val at order
    omega
  have edgeBound : first.val < steps := by
    have lastBound := last.isLt
    omega
  let edge : Fin steps := ⟨first.val, edgeBound⟩
  have firstEq : first = edge.castSucc := Fin.ext rfl
  have lastEq : last = edge.succ := Fin.ext consecutive
  refine ⟨edge, firstEq, lastEq, ?_⟩
  rw [firstEq] at firstInside
  rw [lastEq] at lastInside
  exact le_antisymm firstInside.2 lastInside.1

end Axis

set_option genInjectivity false in
/-- A retained rational parameter for a point on a closed nondegenerate axis segment.

The unit-interval bound and affine equality certify the original lower and upper coordinates at the supplied point. -/
structure SegmentParameter (lower upper point : InverseRootPolynomial.Coordinate) where
  /-- The retained rational segment parameter. -/ value : InverseRootPolynomial.Coordinate
  /-- The parameter lies in the closed unit interval. -/ inside : 0 ≤ value ∧ value ≤ 1
  /-- The affine segment evaluation equals the requested coordinate. -/ equation : lower + value * (upper - lower) =
    point

constructive_injectivity SegmentParameter

namespace SegmentParameter

/-- Compute a closed segment parameter by dividing by its positive width.

The retained inequalities place the quotient in the unit interval and its affine evaluation equals the original point.
-/
def build (lower upper point : InverseRootPolynomial.Coordinate) (ordered : lower < upper)
    (inside : lower ≤ point ∧ point ≤ upper) : Geometry.Rectangle.Partition.RectangularOverlapGeometry.SegmentParameter
      lower upper point :=
  let width := upper - lower
  have widthPositive := Fraction.Order.Arithmetic.sub_pos_direct ordered
  let value := (point - lower) / width
  { value := value
    inside :=
      ⟨Fraction.Order.Field.div_nonneg_direct (Fraction.Order.Arithmetic.sub_nonneg_direct inside.1) widthPositive.le,
        (Fraction.Order.Field.div_le_iff_pos widthPositive).2 (by
          rw [Fraction.Field.one_mul]
          exact Fraction.Order.Arithmetic.sub_le_sub_direct inside.2 le_rfl)⟩
    equation := by
      rw [Fraction.Field.div_mul_cancel_of_ne _ _ widthPositive.ne']
      ring1 }

end SegmentParameter

section Geometry

variable {columns rows : Nat}

/-- A point strictly inside one grid cell has no other closed-cell owner. -/
theorem unique_owner (geometry : RectangularInverseModels.Geometry columns rows)
    (firstColumn lastColumn : Fin (columns + 1)) (firstRow lastRow : Fin (rows + 1)) {point :
      InverseRootPolynomial.Gaussian}
    (firstInside : (geometry.box firstColumn firstRow).StrictContains point)
    (lastInside : (geometry.box lastColumn lastRow).Contains point) :
    firstColumn = lastColumn ∧ firstRow = lastRow :=
  ⟨Geometry.Rectangle.Partition.RectangularOverlapGeometry.Axis.unique_cell geometry.x firstColumn lastColumn
    ⟨firstInside.1, firstInside.2.1⟩ ⟨lastInside.1, lastInside.2.1⟩,
    Geometry.Rectangle.Partition.RectangularOverlapGeometry.Axis.unique_cell geometry.y firstRow lastRow firstInside.2.2
      lastInside.2.2⟩

/-- Parameterize a point on a vertical shared edge by its rational height.

The horizontal coordinate is fixed at the shared cut and the vertical coordinate lies in the closed row interval. -/
theorem horizontal_parameter (geometry : RectangularInverseModels.Geometry columns rows) (column : Fin columns) (row :
  Fin (rows + 1))
    {point : InverseRootPolynomial.Gaussian} (horizontal : point.re = geometry.x.coordinates column.castSucc.succ)
    (vertical : geometry.y.coordinates row.castSucc ≤ point.im ∧ point.im ≤ geometry.y.coordinates row.succ) :
    ∃ parameter : InverseRootPolynomial.Coordinate, (0 ≤ parameter ∧ parameter ≤ 1) ∧
      Affine.line (geometry.vertex column.castSucc.succ row.castSucc)
        (geometry.vertex column.castSucc.succ row.succ - geometry.vertex column.castSucc.succ row.castSucc) parameter =
          point := by
  let parameter := Geometry.Rectangle.Partition.RectangularOverlapGeometry.SegmentParameter.build _ _ _
    (geometry.y.ordered row) vertical
  refine ⟨parameter.value, parameter.inside, ?_⟩
  apply Data.Gaussian.Basic.ext
  · simp only [Affine.line, Geometry.vertex, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.mul_re,
      Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
      Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
    rw [horizontal]
    ring1
  · simp only [Affine.line, Geometry.vertex, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_im,
      Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
      Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
    exact (by ring1 : geometry.y.coordinates row.castSucc +
      (parameter.value * (geometry.y.coordinates row.succ - geometry.y.coordinates row.castSucc) +
        0 * (geometry.x.coordinates column.castSucc.succ - geometry.x.coordinates column.castSucc.succ)) =
      geometry.y.coordinates row.castSucc + parameter.value * (geometry.y.coordinates row.succ - geometry.y.coordinates
        row.castSucc)).trans parameter.equation

/-- Parameterize a point on a horizontal shared edge by its rational width.

The vertical coordinate is fixed at the shared cut and the horizontal coordinate lies in the closed column interval. -/
theorem vertical_parameter (geometry : RectangularInverseModels.Geometry columns rows) (column : Fin (columns + 1)) (row
  : Fin rows)
    {point : InverseRootPolynomial.Gaussian} (horizontal : geometry.x.coordinates column.castSucc ≤ point.re ∧ point.re
      ≤ geometry.x.coordinates column.succ)
    (vertical : point.im = geometry.y.coordinates row.castSucc.succ) :
    ∃ parameter : InverseRootPolynomial.Coordinate, (0 ≤ parameter ∧ parameter ≤ 1) ∧
      Affine.line (geometry.vertex column.castSucc row.castSucc.succ)
        (geometry.vertex column.succ row.castSucc.succ - geometry.vertex column.castSucc row.castSucc.succ) parameter =
          point := by
  let parameter := Geometry.Rectangle.Partition.RectangularOverlapGeometry.SegmentParameter.build _ _ _
    (geometry.x.ordered column) horizontal
  refine ⟨parameter.value, parameter.inside, ?_⟩
  apply Data.Gaussian.Basic.ext
  · simp only [Affine.line, Geometry.vertex, Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.mul_re,
      Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
      Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
    exact (by ring1 : geometry.x.coordinates column.castSucc +
      (parameter.value * (geometry.x.coordinates column.succ - geometry.x.coordinates column.castSucc) -
        0 * (geometry.y.coordinates row.castSucc.succ - geometry.y.coordinates row.castSucc.succ)) =
      geometry.x.coordinates column.castSucc + parameter.value * (geometry.x.coordinates column.succ -
        geometry.x.coordinates column.castSucc)).trans parameter.equation
  · simp only [Affine.line, Geometry.vertex, Data.Gaussian.Basic.add_im, Data.Gaussian.Basic.mul_im,
      Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
      Data.Gaussian.Cast.ofCoordinate_re, Data.Gaussian.Cast.ofCoordinate_im]
    rw [vertical]
    ring1

end Geometry

end Purelib.Geometry.Rectangle.Partition.RectangularOverlapGeometry
