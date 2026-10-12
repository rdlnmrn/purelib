module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic

/-!
# Certified walks on the actual common grid edges

An edge retains one adjacent coordinate interval and its fixed clear line.
Endpoint-indexed walks concatenate and reverse these actual edges.  Converting
to `ClearPath` consumes the stored line certificates, and all paths remain
inside the original ambient rectangle.
-/

namespace Purelib.Polynomial.Geometry.Grid.Walks

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial

public section

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

set_option genInjectivity false in
/-- One oriented adjacent grid edge, with the line payload retained. -/
inductive Edge (grid : ClearGrid polynomial ambient) : Gaussian.Basic.Canonical →
  Gaussian.Basic.Canonical → Type
  /-- An increasing horizontal edge along a retained horizontal line and an actual adjacent horizontal-coordinate
    interval. -/ | horizontal (interval : Geometry.Grid.ClearGrid.Interval
    (Geometry.Grid.ClearGrid.VerticalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
      (adjacent : interval ∈ grid.xIntervals) (line : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member
        : line ∈ grid.horizontal) :
      Purelib.Polynomial.Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point interval.lower.coordinate
        line.coordinate) (Gaussian.Components.Basic.point interval.upper.coordinate line.coordinate)
  /-- An increasing vertical edge along a retained vertical line and an actual adjacent vertical-coordinate interval. -/
    | vertical (interval : Geometry.Grid.ClearGrid.Interval (Geometry.Grid.ClearGrid.HorizontalLine.coordinate
    (polynomial := polynomial) (ambient := ambient)))
      (adjacent : interval ∈ grid.yIntervals) (line : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member :
        line ∈ grid.vertical) :
      Purelib.Polynomial.Geometry.Grid.Walks.Edge grid (Gaussian.Components.Basic.point line.coordinate
        interval.lower.coordinate) (Gaussian.Components.Basic.point line.coordinate interval.upper.coordinate)
  /-- The same retained edge traversed with its endpoints reversed. -/ | reverse {start finish :
    Gaussian.Basic.Canonical} (edge : Purelib.Polynomial.Geometry.Grid.Walks.Edge grid start finish) :
    Purelib.Polynomial.Geometry.Grid.Walks.Edge grid finish start

constructive_injectivity Edge

namespace Edge

variable {grid : ClearGrid polynomial ambient}

/-- Read an oriented grid edge as a clear segment using its original retained line clearance. -/
@[expose] def segment : {start finish : Gaussian.Basic.Canonical} → Geometry.Grid.Walks.Edge grid start finish →
  Geometry.ClearPath.ClearSegment polynomial ambient start finish
  | _, _, .horizontal interval _ line _ =>
      .horizontal interval.lower.coordinate interval.upper.coordinate line.coordinate
        interval.lower.inside.1 interval.lower.inside.2 interval.upper.inside.1 interval.upper.inside.2 line.clearance
  | _, _, .vertical interval _ line _ =>
      .vertical line.coordinate interval.lower.coordinate interval.upper.coordinate
        interval.lower.inside.1 interval.lower.inside.2 interval.upper.inside.1 interval.upper.inside.2 line.clearance
  | _, _, .reverse edge => Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse edge.segment

/-- Every retained edge's clear segment lies in the original ambient box. -/
theorem withinAmbient : {start finish : Gaussian.Basic.Canonical} → (edge : Geometry.Grid.Walks.Edge grid start finish)
  → edge.segment.WithinAmbient
  | _, _, .horizontal _ _ line _ => line.inside
  | _, _, .vertical _ _ line _ => line.inside
  | _, _, .reverse edge => Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse_withinAmbient edge.segment
    edge.withinAmbient

/-- Both endpoints of a retained edge belong to the original grid coordinate banks. -/
theorem vertices : {start finish : Gaussian.Basic.Canonical} → (edge : Geometry.Grid.Walks.Edge grid start finish) →
    FromStates.ContainsVertex grid start ∧ FromStates.ContainsVertex grid finish
  | _, _, .horizontal interval adjacent line member =>
      let endpoints := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ grid.vertical_ordered adjacent
      ⟨⟨List.Map.mem_map_of_mem endpoints.1, List.Map.mem_map_of_mem member⟩,
        ⟨List.Map.mem_map_of_mem endpoints.2, List.Map.mem_map_of_mem member⟩⟩
  | _, _, .vertical interval adjacent line member =>
      let endpoints := Geometry.Grid.ClearGrid.Interval.endpoints_mem _ grid.horizontal_ordered adjacent
      ⟨⟨List.Map.mem_map_of_mem member, List.Map.mem_map_of_mem endpoints.1⟩,
        ⟨List.Map.mem_map_of_mem member, List.Map.mem_map_of_mem endpoints.2⟩⟩
  | _, _, .reverse edge => ⟨edge.vertices.2, edge.vertices.1⟩

end Edge

set_option genInjectivity false in
/-- An endpoint-indexed finite walk through actual retained grid edges.

Each step keeps its adjacency witness and original clear-line payload; the empty walk preserves its endpoint. -/
inductive Walk (grid : ClearGrid polynomial ambient) : Gaussian.Basic.Canonical →
  Gaussian.Basic.Canonical → Type
  /-- The empty walk at the displayed point. -/ | nil (point : Gaussian.Basic.Canonical) :
    Purelib.Polynomial.Geometry.Grid.Walks.Walk grid point point
  /-- Prepend a retained edge to a walk beginning at its exact finishing endpoint. -/ | cons {start middle finish :
    Gaussian.Basic.Canonical} (edge : Geometry.Grid.Walks.Edge grid start middle) (tail :
    Purelib.Polynomial.Geometry.Grid.Walks.Walk grid middle finish) :
      Purelib.Polynomial.Geometry.Grid.Walks.Walk grid start finish

constructive_injectivity Walk

namespace Walk

variable {grid : ClearGrid polynomial ambient}

/-- Concatenate two retained grid walks with a shared middle endpoint. -/
@[expose] def append : {start middle finish : Gaussian.Basic.Canonical} → Geometry.Grid.Walks.Walk grid start middle →
  Geometry.Grid.Walks.Walk grid middle finish → Geometry.Grid.Walks.Walk grid start finish
  | _, _, _, .nil _, second => second
  | _, _, _, .cons edge tail, second => .cons edge (tail.append second)

/-- Reverse into an existing suffix, allocating every retained edge once. -/
@[expose] def reverseOnto : {start middle finish : Gaussian.Basic.Canonical} → Geometry.Grid.Walks.Walk grid start
  middle → Geometry.Grid.Walks.Walk grid start finish → Geometry.Grid.Walks.Walk grid middle finish
  | _, _, _, .nil _, suffix => suffix
  | _, _, _, .cons edge tail, suffix => tail.reverseOnto (.cons (.reverse edge) suffix)

/-- Reverse a retained walk using the accumulator construction and the same original edges. -/
@[expose] def reverse {start finish : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish) :
  Geometry.Grid.Walks.Walk grid finish start :=
  walk.reverseOnto (.nil start)

/-- Transport a retained walk along exact equalities of its two endpoints. -/
@[expose] def castEndpoints {start finish first last : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid
  start finish)
    (startEq : start = first) (finishEq : finish = last) : Geometry.Grid.Walks.Walk grid first last := by
  cases startEq
  cases finishEq
  exact walk

/-- Read a retained grid walk as a clear path using each edge's stored clearance. -/
@[expose] def path : {start finish : Gaussian.Basic.Canonical} → Geometry.Grid.Walks.Walk grid start finish →
  ClearPath polynomial ambient start finish
  | _, _, .nil point => .nil point
  | _, _, .cons edge tail => .cons edge.segment tail.path

/-- The clear path read from a retained walk stays inside the original ambient box. -/
theorem withinAmbient : {start finish : Gaussian.Basic.Canonical} → (walk : Geometry.Grid.Walks.Walk grid start finish)
  → walk.path.WithinAmbient
  | _, _, .nil point => .nil point
  | _, _, .cons edge tail => .cons edge.withinAmbient tail.withinAmbient

/-- Count the retained oriented edges of a finite grid walk. -/
@[expose] def edgeCount : {start finish : Gaussian.Basic.Canonical} → Geometry.Grid.Walks.Walk grid start finish → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ tail => tail.edgeCount + 1

/-- Reading a walk as a clear path preserves its exact edge count as the segment count. -/
theorem path_segmentCount : {start finish : Gaussian.Basic.Canonical} → (walk : Geometry.Grid.Walks.Walk grid start
  finish) →
    walk.path.segmentCount = walk.edgeCount
  | _, _, .nil _ => rfl
  | _, _, .cons _ tail => congrArg (fun count => count + 1) tail.path_segmentCount

/-- A retained walk whose final point is a grid vertex has every clear-path vertex in the same grid. -/
theorem vertices : {start finish : Gaussian.Basic.Canonical} → (walk : Geometry.Grid.Walks.Walk grid start finish) →
    FromStates.ContainsVertex grid finish → FromStates.ContainsPathVertices grid
      walk.path
  | _, _, .nil _, last => last
  | _, _, .cons edge tail, last => ⟨edge.vertices.1, tail.vertices last⟩

/-- Convert the monotone axis spine directly, preserving its actual adjacent
intervals and the same retained horizontal-line certificate on every edge. -/
@[expose] def horizontalIncreasing (line : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal) :
    {start finish : Fraction.Rational} → Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals start finish →
      Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point start line.coordinate)
        (Gaussian.Components.Basic.point finish line.coordinate)
  | _, _, .nil coordinate => .nil (Gaussian.Components.Basic.point coordinate line.coordinate)
  | _, _, .cons interval adjacent tail => .cons (.horizontal interval adjacent line member)
    (Purelib.Polynomial.Geometry.Grid.Walks.Walk.horizontalIncreasing line member tail)

/-- Lift an increasing vertical-axis walk using one retained vertical line clearance.

The result preserves the original adjacent intervals and uses the same fixed-line payload for every edge. -/
@[expose] def verticalIncreasing (line : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical) :
    {start finish : Fraction.Rational} → Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals start finish →
      Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point line.coordinate start)
        (Gaussian.Components.Basic.point line.coordinate finish)
  | _, _, .nil coordinate => .nil (Gaussian.Components.Basic.point line.coordinate coordinate)
  | _, _, .cons interval adjacent tail => .cons (.vertical interval adjacent line member)
    (Purelib.Polynomial.Geometry.Grid.Walks.Walk.verticalIncreasing line member tail)

/-- Lift either orientation without repeating the axis search. -/
@[expose] def horizontalAxis (line : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal)
    {start finish : Fraction.Rational} : Geometry.Grid.AxisWalks.Walk grid.xIntervals start finish →
      Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point start line.coordinate)
        (Gaussian.Components.Basic.point finish line.coordinate)
  | .forward increasing => Geometry.Grid.Walks.Walk.horizontalIncreasing line member increasing
  | .backward increasing => (Geometry.Grid.Walks.Walk.horizontalIncreasing line member increasing).reverse

/-- Lift either orientation of an existing vertical-axis walk without repeating the axis search. -/
@[expose] def verticalAxis (line : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical)
    {start finish : Fraction.Rational} : Geometry.Grid.AxisWalks.Walk grid.yIntervals start finish →
      Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point line.coordinate start)
        (Gaussian.Components.Basic.point line.coordinate finish)
  | .forward increasing => Geometry.Grid.Walks.Walk.verticalIncreasing line member increasing
  | .backward increasing => (Geometry.Grid.Walks.Walk.verticalIncreasing line member increasing).reverse

end Walk

/-- A horizontal segment split at every intermediate grid coordinate.
The fixed-line lookup returns the original retained clearance payload. -/
@[expose] def horizontalWalk (grid : ClearGrid polynomial ambient) (start finish y :
  Fraction.Rational)
    (startMember : start ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (finishMember : finish ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (lineMember : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) : Geometry.Grid.Walks.Walk
      grid (Gaussian.Components.Basic.point start y) (Gaussian.Components.Basic.point finish y) :=
  let line := Geometry.Grid.AxisWalks.lookup y grid.horizontal lineMember
  let axis := Geometry.Grid.AxisWalks.walk grid.vertical grid.vertical_ordered start finish startMember finishMember
  let walk := Geometry.Grid.Walks.Walk.horizontalAxis line.entry line.member axis
  walk.castEndpoints (congrArg (Gaussian.Components.Basic.point start) line.coordinate_eq) (congrArg
    (Gaussian.Components.Basic.point finish) line.coordinate_eq)

/-- Split a vertical segment at every intermediate retained grid coordinate.

The finite line lookup supplies the original clearance payload, and the axis walk preserves the requested direction and
endpoints. -/
@[expose] def verticalWalk (grid : ClearGrid polynomial ambient) (x start finish : Fraction.Rational)
    (lineMember : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    (startMember : start ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    (finishMember : finish ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
      Geometry.Grid.Walks.Walk grid (Gaussian.Components.Basic.point x start) (Gaussian.Components.Basic.point x finish)
      :=
  let line := Geometry.Grid.AxisWalks.lookup x grid.vertical lineMember
  let axis := Geometry.Grid.AxisWalks.walk grid.horizontal grid.horizontal_ordered start finish startMember finishMember
  let walk := Geometry.Grid.Walks.Walk.verticalAxis line.entry line.member axis
  walk.castEndpoints (congrArg (fun value => Gaussian.Components.Basic.point value start) line.coordinate_eq)
    (congrArg (fun value => Gaussian.Components.Basic.point value finish) line.coordinate_eq)

/-- Replace one original clear segment, possibly certified in a smaller
ambient box, by adjacent shared-grid edges with exactly the same endpoints. -/
@[expose] def splitSegment (grid : ClearGrid polynomial ambient) {pathAmbient : Box}
  :
    {start finish : Gaussian.Basic.Canonical} → (segment : Geometry.ClearPath.ClearSegment polynomial pathAmbient start
      finish) →
      FromStates.ContainsVertex grid start → FromStates.ContainsVertex grid finish
        → Geometry.Grid.Walks.Walk grid start finish
  | _, _, .horizontal xStart xFinish y _ _ _ _ _, first, last =>
      Geometry.Grid.Walks.horizontalWalk grid xStart xFinish y first.1 last.1 first.2
  | _, _, .vertical x yStart yFinish _ _ _ _ _, first, last =>
      Geometry.Grid.Walks.verticalWalk grid x yStart yFinish first.1 first.2 last.2

/-- Split the complete path using the retained grid.  Each segment keeps its
own traversal direction; stationary original segments contribute no motion. -/
@[expose] def splitPath (grid : ClearGrid polynomial ambient) {pathAmbient : Box} :
    {start finish : Gaussian.Basic.Canonical} → (path : ClearPath polynomial pathAmbient start
      finish) →
      FromStates.ContainsPathVertices grid path → Geometry.Grid.Walks.Walk grid start finish
  | _, _, .nil point, _ => .nil point
  | _, _, .cons head tail, onGrid =>
      (Geometry.Grid.Walks.splitSegment grid head onGrid.1 (FromStates.ContainsPathVertices.start
        grid tail onGrid.2)).append
        (Purelib.Polynomial.Geometry.Grid.Walks.splitPath grid tail onGrid.2)

end

end Purelib.Polynomial.Geometry.Grid.Walks
