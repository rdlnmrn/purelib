module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces
import Purelib.Polynomial.Geometry.Grid.Axis.Partial
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.Axis

open Purelib.Polynomial.Geometry.Grid.ClearGrid
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

@[expose] public section

/-! Identify the complete containing edge of two distinct retained queries.
The result permits either orientation and does not assume the builder's choice. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Interval HorizontalLine VerticalLine)
open Purelib.Polynomial.Geometry.Grid.ClearGrid.Interval (Before)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (EdgePoint)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {ambient : Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid
    curve.polynomial ambient}

namespace EdgePoint

/-- Complement the actual parameter when reading an oppositely presented edge. -/
def unreverse {start finish point : Data.Gaussian.Basic.Canonical} {edge : Walks.Edge grid start finish}
    (location : RegularFaces.EdgePoint (.reverse edge) point) : RegularFaces.EdgePoint edge point := by
  refine ⟨1 - location.parameter, ⟨Fraction.Order.Arithmetic.sub_nonneg_direct location.inside.2, ?_⟩, ?_⟩
  · have bound := Fraction.Order.Arithmetic.sub_le_sub_left_direct location.inside.1 1
    exact bound.trans_eq (by ring1)
  · exact (ClearSegment.reverse_pointAt edge.segment location.parameter).symm.trans location.point_eq

/-- The original retained point on a horizontal grid edge has its certified transverse bounds and exact fixed imaginary
coordinate. -/
theorem horizontal_bounds
    {span : ClearGrid.Interval (VerticalLine.coordinate (polynomial := curve.polynomial) (ambient := ambient))}
    {member : span ∈ grid.xIntervals} {line : ClearGrid.HorizontalLine curve.polynomial ambient} {onLine : line ∈
      grid.horizontal}
    {point : Data.Gaussian.Basic.Canonical} (location : RegularFaces.EdgePoint (.horizontal span member line onLine)
      point) :
    span.lower.coordinate ≤ point.re ∧ point.re ≤ span.upper.coordinate ∧ point.im = line.coordinate := by
  have inside := location.contained (box := ⟨span.lower.coordinate, span.upper.coordinate, line.coordinate,
    line.coordinate, span.ordered.le, le_rfl⟩)
    ⟨le_rfl, span.ordered.le, le_rfl, le_rfl⟩ ⟨span.ordered.le, le_rfl, le_rfl, le_rfl⟩
  exact ⟨inside.1, inside.2.1, le_antisymm inside.2.2.2 inside.2.2.1⟩

/-- The original retained point on a vertical grid edge has its certified transverse bounds and exact fixed real
coordinate. -/
theorem vertical_bounds
    {span : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := curve.polynomial) (ambient := ambient))}
    {member : span ∈ grid.yIntervals} {line : ClearGrid.VerticalLine curve.polynomial ambient} {onLine : line ∈
      grid.vertical}
    {point : Data.Gaussian.Basic.Canonical} (location : RegularFaces.EdgePoint (.vertical span member line onLine)
      point) :
    span.lower.coordinate ≤ point.im ∧ point.im ≤ span.upper.coordinate ∧ point.re = line.coordinate := by
  have inside := location.contained (box := ⟨line.coordinate, line.coordinate, span.lower.coordinate,
    span.upper.coordinate, le_rfl, span.ordered.le⟩)
    ⟨le_rfl, le_rfl, le_rfl, span.ordered.le⟩ ⟨le_rfl, le_rfl, span.ordered.le, le_rfl⟩
  exact ⟨inside.2.2.1, inside.2.2.2, le_antisymm inside.2.1 inside.1⟩

end EdgePoint

/-- Two intervals in the original separated interval list containing the same two distinct rational points are equal. -/
private theorem interval_eq_of_two_points {Alpha : Type} {key : Alpha → Fraction.Rational}
    {intervals : List (ClearGrid.Interval key)} (separated : intervals.Pairwise Interval.Before)
    {left right : ClearGrid.Interval key} (leftMember : left ∈ intervals) (rightMember : right ∈ intervals)
    {first last : Fraction.Rational} (different : first ≠ last)
    (leftFirst : key left.lower ≤ first ∧ first ≤ key left.upper)
    (leftLast : key left.lower ≤ last ∧ last ≤ key left.upper)
    (rightFirst : key right.lower ≤ first ∧ first ≤ key right.upper)
    (rightLast : key right.lower ≤ last ∧ last ≤ key right.upper) : left = right := by
  rcases lt_or_gt_of_ne different with forward | backward
  · exact Partial.eq_of_right_overlap separated leftMember rightMember
      ⟨leftFirst.1, forward.trans_le leftLast.2⟩ ⟨rightFirst.1, forward.trans_le rightLast.2⟩
  · exact Partial.eq_of_right_overlap separated leftMember rightMember
      ⟨leftLast.1, backward.trans_le leftFirst.2⟩ ⟨rightLast.1, backward.trans_le rightFirst.2⟩

namespace Edge

/-- Two queries with distinct real coordinates identify the exact horizontal adjacent interval and fixed line, up to
presentation reversal. -/
theorem horizontal_endpoints
    {span : ClearGrid.Interval (VerticalLine.coordinate (polynomial := curve.polynomial) (ambient := ambient))}
    (member : span ∈ grid.xIntervals) {first last : Data.Gaussian.Basic.Canonical}
    (different : first.re ≠ last.re)
    (firstInside : span.lower.coordinate ≤ first.re ∧ first.re ≤ span.upper.coordinate)
    (lastInside : span.lower.coordinate ≤ last.re ∧ last.re ≤ span.upper.coordinate)
    {start finish : Data.Gaussian.Basic.Canonical} (edge : Walks.Edge grid start finish)
    (firstPoint : RegularFaces.EdgePoint edge first) (lastPoint : RegularFaces.EdgePoint edge last) :
    (start = Components.Basic.point span.lower.coordinate first.im ∧ finish = Components.Basic.point
      span.upper.coordinate first.im) ∨
    (finish = Components.Basic.point span.lower.coordinate first.im ∧ start = Components.Basic.point
      span.upper.coordinate first.im) := by
  induction edge with
  | horizontal interval adjacent line onLine =>
      have a := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.horizontal_bounds firstPoint
      have b := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.horizontal_bounds lastPoint
      have same := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.interval_eq_of_two_points
        (Interval.adjacent_pairwise grid.vertical grid.vertical_ordered)
        adjacent member different ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩ firstInside lastInside
      exact Or.inl ⟨congrArg₂ Components.Basic.point (congrArg (fun span => span.lower.coordinate) same) a.2.2.symm,
        congrArg₂ Components.Basic.point (congrArg (fun span => span.upper.coordinate) same) a.2.2.symm⟩
  | vertical interval adjacent line onLine =>
      exact (different ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.vertical_bounds
        firstPoint).2.2.trans (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.vertical_bounds
        lastPoint).2.2.symm)).elim
  | reverse edge ih =>
      exact (ih (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.unreverse firstPoint)
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.unreverse lastPoint)).symm

/-- The vertical version reads the same retained query parameters. -/
theorem vertical_endpoints
    {span : ClearGrid.Interval (HorizontalLine.coordinate (polynomial := curve.polynomial) (ambient := ambient))}
    (member : span ∈ grid.yIntervals) {first last : Data.Gaussian.Basic.Canonical}
    (different : first.im ≠ last.im)
    (firstInside : span.lower.coordinate ≤ first.im ∧ first.im ≤ span.upper.coordinate)
    (lastInside : span.lower.coordinate ≤ last.im ∧ last.im ≤ span.upper.coordinate)
    {start finish : Data.Gaussian.Basic.Canonical} (edge : Walks.Edge grid start finish)
    (firstPoint : RegularFaces.EdgePoint edge first) (lastPoint : RegularFaces.EdgePoint edge last) :
    (start = Components.Basic.point first.re span.lower.coordinate ∧ finish = Components.Basic.point first.re
      span.upper.coordinate) ∨
    (finish = Components.Basic.point first.re span.lower.coordinate ∧ start = Components.Basic.point first.re
      span.upper.coordinate) := by
  induction edge with
  | horizontal interval adjacent line onLine =>
      exact (different ((Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.horizontal_bounds
        firstPoint).2.2.trans
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.horizontal_bounds
        lastPoint).2.2.symm)).elim
  | vertical interval adjacent line onLine =>
      have a := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.vertical_bounds firstPoint
      have b := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.vertical_bounds lastPoint
      have same := Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.interval_eq_of_two_points
        (Interval.adjacent_pairwise grid.horizontal grid.horizontal_ordered)
        adjacent member different ⟨a.1, a.2.1⟩ ⟨b.1, b.2.1⟩ firstInside lastInside
      exact Or.inl ⟨congrArg₂ Components.Basic.point a.2.2.symm (congrArg (fun span => span.lower.coordinate) same),
        congrArg₂ Components.Basic.point a.2.2.symm (congrArg (fun span => span.upper.coordinate) same)⟩
  | reverse edge ih =>
      exact (ih (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.unreverse firstPoint)
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry.EdgePoint.unreverse lastPoint)).symm

end Edge
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.EdgeGeometry
