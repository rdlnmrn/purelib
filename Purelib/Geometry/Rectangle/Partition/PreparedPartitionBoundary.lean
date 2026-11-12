module
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Topology.Polygon.Stokes
public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Data

open Purelib

open Purelib.Geometry.Rectangle.Partition

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.AxisWalks

open Purelib.Topology.Polygon

public section

/-! Exact cancellation of shared sides in a finite rectangular partition.
The exterior keeps the partition cuts and each side's dyadic subdivision. -/

namespace Purelib.Geometry.Rectangle

open Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions (Gaussian Box)

open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (horizontalBoundary verticalBoundary rectangleBoundary)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Integration
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)
open Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts (rectangles intervalBox)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

namespace Partition.PreparedPartitionBoundary

/-- The Gaussian sum is additive over concatenation. -/
private theorem sum_append (first last : List Gaussian) :
    gaussianSum (first ++ last) = gaussianSum first
      + gaussianSum last := by
  induction first with
  | nil =>
    change gaussianSum last = 0 + gaussianSum last;
      ring1
  | cons head tail ih =>
      change head + gaussianSum (tail ++ last) = (head +
        gaussianSum tail) + gaussianSum last
      rw [ih]
      ring1

/-- Reindex the Cartesian rectangle-boundary sum as nested axis sums. -/
private theorem rectangle_sum (primitive : Gaussian → PrimitivePoint) (depth : Nat)
    (horizontal vertical : List Interval) :
    gaussianSum ((rectangles horizontal vertical).map
      (rectangleBoundary primitive depth)) =
      gaussianSum (horizontal.map (fun x =>
        gaussianSum
        (vertical.map (fun y => rectangleBoundary primitive depth (intervalBox
          x y))))) := by
  induction horizontal with
  | nil => rfl
  | cons x rest ih =>
      simp only [rectangles, List.Flatten.flatMap_cons, List.Map.map_append, List.Map.map_map] at
        *
      rw [sum_append, ih]
      rfl

/-- Internal horizontal sides cancel along a retained vertical walk.

The remaining terms are the lower and upper horizontal sides and the two vertical side sums. -/
private theorem row_boundary (primitive : Gaussian → PrimitivePoint) (depth : Nat)
    (x : Interval) {intervals : List Interval} :
    {first last : Coordinate} → (walk : IncreasingWalk intervals first last) →
    gaussianSum (walk.edges.map (fun y => rectangleBoundary
      primitive depth (intervalBox x y))) =
      horizontalBoundary primitive depth x.lower x.upper first -
        horizontalBoundary primitive depth x.lower x.upper last +
      gaussianSum (walk.edges.map (fun y => verticalBoundary
        primitive depth y.lower y.upper x.upper)) -
      gaussianSum (walk.edges.map (fun y => verticalBoundary
        primitive depth y.lower y.upper x.lower))
  | _, _, .nil _ => by
    simp only [IncreasingWalk.edges, List.map_nil, gaussianSum]; ring1
  | _, _, .cons y _ tail => by
      simp only [IncreasingWalk.edges, List.map_cons, gaussianSum]
      rw [row_boundary primitive depth x tail]
      simp only [rectangleBoundary, intervalBox, id_eq]
      ring1

/-- Internal vertical sides cancel along a retained horizontal walk.

The result preserves both original axis walks and their dyadically subdivided exterior sides. -/
private theorem columns_boundary (primitive : Gaussian → PrimitivePoint) (depth : Nat)
    {vertical horizontal : List Interval} {bottom top : Coordinate}
    (yWalk : IncreasingWalk vertical bottom top) :
    {first last : Coordinate} → (xWalk : IncreasingWalk horizontal first last) →
    gaussianSum (xWalk.edges.map (fun x =>
      gaussianSum
      (yWalk.edges.map (fun y => rectangleBoundary primitive depth
        (intervalBox x y))))) =
      gaussianSum (xWalk.edges.map (fun x =>
        horizontalBoundary primitive depth x.lower x.upper bottom -
          horizontalBoundary primitive depth x.lower x.upper top)) +
      gaussianSum (yWalk.edges.map (fun y => verticalBoundary
        primitive depth y.lower y.upper last)) -
      gaussianSum (yWalk.edges.map (fun y => verticalBoundary
        primitive depth y.lower y.upper first))
  | _, _, .nil _ => by
    simp only [IncreasingWalk.edges, List.map_nil, gaussianSum]; ring1
  | _, _, .cons x _ tail => by
      simp only [IncreasingWalk.edges, List.map_cons, gaussianSum]
      rw [row_boundary primitive depth x yWalk,
        columns_boundary primitive depth yWalk tail]
      simp only [id_eq]
      ring1

end Partition.PreparedPartitionBoundary

namespace CutPartition

/-- The four exterior sides, segmented at the original partition cuts. -/
@[expose] def boundary
    {box : Box} {points : List Gaussian}
    (partition : CutPartition box points)
    (primitive : Gaussian → PrimitivePoint) (depth : Nat) : Gaussian :=
  gaussianSum (partition.x.intervals.map (fun x =>
    horizontalBoundary primitive depth x.lower x.upper box.yLower -
      horizontalBoundary primitive depth x.lower x.upper box.yUpper)) +
  gaussianSum (partition.y.intervals.map (fun y =>
    verticalBoundary primitive depth y.lower y.upper box.xUpper)) -
  gaussianSum (partition.y.intervals.map (fun y =>
    verticalBoundary primitive depth y.lower y.upper box.xLower))

/-- The sum of cached rectangle boundaries equals the retained segmented exterior boundary. -/
theorem boundary_eq_sum
    {box : Box} {points : List Gaussian}
    (partition : CutPartition box points)
    (primitive : Gaussian → PrimitivePoint) (depth : Nat) :
    gaussianSum (partition.boxes.map (rectangleBoundary primitive
      depth)) = partition.boundary primitive depth := by
  rw [partition.boxes_eq, PreparedPartitionBoundary.rectangle_sum]
  have equal := PreparedPartitionBoundary.columns_boundary primitive depth partition.y.walk
    partition.x.walk
  rw [partition.x.walk_edges, partition.y.walk_edges] at equal
  exact equal

end CutPartition

end Purelib.Geometry.Rectangle
