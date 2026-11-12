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

open Purelib.Data.Gaussian.Components

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

variable {polynomial : ClearPath.GaussianPolynomial} {ambient : Box}

set_option genInjectivity false in
/-- One oriented adjacent grid edge, with the line payload retained. -/
inductive Edge (grid : ClearGrid polynomial ambient) : Gaussian.Basic.Canonical →
  Gaussian.Basic.Canonical → Type
  /-- An increasing horizontal edge along a retained horizontal line and an actual adjacent horizontal-coordinate
    interval. -/ | horizontal (interval : ClearGrid.Interval
    (ClearGrid.VerticalLine.coordinate (polynomial := polynomial) (ambient := ambient)))
      (adjacent : interval ∈ grid.xIntervals) (line : ClearGrid.HorizontalLine polynomial ambient) (member
        : line ∈ grid.horizontal) :
      Walks.Edge grid (Basic.point interval.lower.coordinate
        line.coordinate) (Basic.point interval.upper.coordinate line.coordinate)
  /-- An increasing vertical edge along a retained vertical line and an actual adjacent vertical-coordinate interval. -/
    | vertical (interval : ClearGrid.Interval (ClearGrid.HorizontalLine.coordinate
    (polynomial := polynomial) (ambient := ambient)))
      (adjacent : interval ∈ grid.yIntervals) (line : ClearGrid.VerticalLine polynomial ambient) (member :
        line ∈ grid.vertical) :
      Walks.Edge grid (Basic.point line.coordinate
        interval.lower.coordinate) (Basic.point line.coordinate interval.upper.coordinate)
  /-- The same retained edge traversed with its endpoints reversed. -/ | reverse {start finish :
    Gaussian.Basic.Canonical} (edge : Walks.Edge grid start finish) :
    Walks.Edge grid finish start

constructive_injectivity Edge

namespace Edge

variable {grid : ClearGrid polynomial ambient}

/-- Read an oriented grid edge as a clear segment using its original retained line clearance. -/
@[expose] def segment : {start finish : Gaussian.Basic.Canonical} → Edge grid start finish →
  ClearPath.ClearSegment polynomial ambient start finish
  | _, _, .horizontal interval _ line _ =>
      .horizontal interval.lower.coordinate interval.upper.coordinate line.coordinate
        interval.lower.inside.1 interval.lower.inside.2 interval.upper.inside.1 interval.upper.inside.2 line.clearance
  | _, _, .vertical interval _ line _ =>
      .vertical line.coordinate interval.lower.coordinate interval.upper.coordinate
        interval.lower.inside.1 interval.lower.inside.2 interval.upper.inside.1 interval.upper.inside.2 line.clearance
  | _, _, .reverse edge => Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse edge.segment

/-- Every retained edge's clear segment lies in the original ambient box. -/
theorem withinAmbient : {start finish : Gaussian.Basic.Canonical} → (edge : Edge grid start finish)
  → edge.segment.WithinAmbient
  | _, _, .horizontal _ _ line _ => line.inside
  | _, _, .vertical _ _ line _ => line.inside
  | _, _, .reverse edge => Curves.Hyperelliptic.Branches.BranchCutLifts.ClearSegment.reverse_withinAmbient edge.segment
    edge.withinAmbient

/-- Both endpoints of a retained edge belong to the original grid coordinate banks. -/
theorem vertices : {start finish : Gaussian.Basic.Canonical} → (edge : Edge grid start finish) →
    FromStates.ContainsVertex grid start ∧ FromStates.ContainsVertex grid finish
  | _, _, .horizontal interval adjacent line member =>
      let endpoints := ClearGrid.Interval.endpoints_mem _ grid.vertical_ordered adjacent
      ⟨⟨List.Map.mem_map_of_mem endpoints.1, List.Map.mem_map_of_mem member⟩,
        ⟨List.Map.mem_map_of_mem endpoints.2, List.Map.mem_map_of_mem member⟩⟩
  | _, _, .vertical interval adjacent line member =>
      let endpoints := ClearGrid.Interval.endpoints_mem _ grid.horizontal_ordered adjacent
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
    Walks.Walk grid point point
  /-- Prepend a retained edge to a walk beginning at its exact finishing endpoint. -/ | cons {start middle finish :
    Gaussian.Basic.Canonical} (edge : Edge grid start middle) (tail :
    Walks.Walk grid middle finish) :
      Walks.Walk grid start finish

constructive_injectivity Walk

namespace Walk

variable {grid : ClearGrid polynomial ambient}

/-- Concatenate two retained grid walks with a shared middle endpoint. -/
@[expose] def append : {start middle finish : Gaussian.Basic.Canonical} → Walk grid start middle →
  Walk grid middle finish → Walk grid start finish
  | _, _, _, .nil _, second => second
  | _, _, _, .cons edge tail, second => .cons edge (tail.append second)

/-- Reverse into an existing suffix, allocating every retained edge once. -/
@[expose] def reverseOnto : {start middle finish : Gaussian.Basic.Canonical} → Walk grid start
  middle → Walk grid start finish → Walk grid middle finish
  | _, _, _, .nil _, suffix => suffix
  | _, _, _, .cons edge tail, suffix => tail.reverseOnto (.cons (.reverse edge) suffix)

/-- Reverse a retained walk using the accumulator construction and the same original edges. -/
@[expose] def reverse {start finish : Gaussian.Basic.Canonical} (walk : Walk grid start finish) :
  Walk grid finish start :=
  walk.reverseOnto (.nil start)

/-- Transport a retained walk along exact equalities of its two endpoints. -/
@[expose] def castEndpoints {start finish first last : Gaussian.Basic.Canonical} (walk : Walk grid
  start finish)
    (startEq : start = first) (finishEq : finish = last) : Walk grid first last := by
  cases startEq
  cases finishEq
  exact walk

/-- Read a retained grid walk as a clear path using each edge's stored clearance. -/
@[expose] def path : {start finish : Gaussian.Basic.Canonical} → Walk grid start finish →
  ClearPath polynomial ambient start finish
  | _, _, .nil point => .nil point
  | _, _, .cons edge tail => .cons edge.segment tail.path

/-- Reading two concatenated retained grid walks preserves their exact clear-path concatenation. -/
theorem path_append : {start middle finish : Gaussian.Basic.Canonical} →
    (first : Walk grid start middle) → (second : Walk grid middle finish) →
      (first.append second).path = first.path.append second.path
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons edge tail, second =>
      congrArg (ClearPath.cons edge.segment) (tail.path_append second)

/-- Endpoint transport commutes with concatenation of the identical two retained Walks. -/
theorem castEndpoints_append {start middle finish first point last : Gaussian.Basic.Canonical}
    (left : Walk grid start middle) (right : Walk grid middle finish)
    (sourceEq : start = first) (middleEq : middle = point) (finishEq : finish = last) :
    (left.append right).castEndpoints sourceEq finishEq =
      (left.castEndpoints sourceEq middleEq).append (right.castEndpoints middleEq finishEq) := by
  cases sourceEq
  cases middleEq
  cases finishEq
  rfl

/-- Reversing both exact endpoint transports retains the complete original Walk. -/
theorem castEndpoints_cancel {start finish first last : Gaussian.Basic.Canonical}
    (walk : Walk grid start finish) (sourceEq : start = first) (finishEq : finish = last) :
    (walk.castEndpoints sourceEq finishEq).castEndpoints sourceEq.symm finishEq.symm = walk := by
  cases sourceEq
  cases finishEq
  rfl

/-- The clear path read from a retained walk stays inside the original ambient box. -/
theorem withinAmbient : {start finish : Gaussian.Basic.Canonical} → (walk : Walk grid start finish)
  → walk.path.WithinAmbient
  | _, _, .nil point => .nil point
  | _, _, .cons edge tail => .cons edge.withinAmbient tail.withinAmbient

/-- Count the retained oriented edges of a finite grid walk. -/
@[expose] def edgeCount : {start finish : Gaussian.Basic.Canonical} → Walk grid start finish → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ tail => tail.edgeCount + 1

/-- Retain the original ordered prefix ending at one bounded vertex occurrence.

Only walk metadata is constructed. Every head is the SAME original Edge;
no line, root row, query, Point or observation is prepared or classified.
-/
@[expose] def take : {start finish : Gaussian.Basic.Canonical} → (walk : Walk grid start finish) →
    Fin (walk.edgeCount + 1) → (point : Gaussian.Basic.Canonical) × Walk grid start point
  | _, _, .nil point, _ => ⟨point, .nil point⟩
  | first, _, .cons edge tail, position =>
      Fin.cases ⟨first, .nil first⟩ (fun next =>
        let retained := tail.take next
        ⟨retained.1, .cons edge retained.2⟩) position

/-- The original prefix at occurrence zero is the empty walk at its actual source. -/
theorem take_zero {start finish : Gaussian.Basic.Canonical} (walk : Walk grid start finish) :
    walk.take ⟨0, Nat.zero_lt_succ _⟩ = ⟨start, .nil start⟩ := by
  cases walk <;> rfl

/-- A positive prefix occurrence retains the SAME head and original recursive tail prefix. -/
theorem take_succ {start middle finish : Gaussian.Basic.Canonical} (edge : Edge grid start middle)
    (tail : Walk grid middle finish) (position : Nat) (bound : position + 1 < tail.edgeCount + 1 + 1) :
    (Walk.cons edge tail).take ⟨position + 1, bound⟩ =
      (let retained := tail.take ⟨position, Nat.lt_of_succ_lt_succ bound⟩
       ⟨retained.1, .cons edge retained.2⟩) := by rfl

/-- Read one literal oriented edge from the retained walk without rebuilding its prefix or tail.

The dependent pair retains the exact endpoint types and original Edge
payload, including reversed traversal. The bounded empty case is eliminated.
-/
def edgeAt : {start finish : Gaussian.Basic.Canonical} → (walk : Walk grid start finish) →
    Fin walk.edgeCount → Σ first : Gaussian.Basic.Canonical, Σ last : Gaussian.Basic.Canonical, Edge grid first last
  | _, _, .nil _, index => Fin.elim0 index
  | start, _, .cons (middle := middle) edge _, ⟨0, _⟩ => ⟨start, middle, edge⟩
  | _, _, .cons _ tail, ⟨index + 1, bound⟩ => tail.edgeAt ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- A retained walk's actual vertex incidence pays both endpoints of its literal selected edge. -/
theorem edgeAt_vertices {otherAmbient : Box} (other : ClearGrid polynomial otherAmbient) :
    ∀ {start finish : Gaussian.Basic.Canonical} (walk : Walk grid start finish)
      (_ : FromStates.ContainsPathVertices other walk.path) (index : Fin walk.edgeCount),
      FromStates.ContainsVertex other (walk.edgeAt index).1 ∧
        FromStates.ContainsVertex other (walk.edgeAt index).2.1
  | _, _, .nil _, _, index => Fin.elim0 index
  | _, _, .cons _ tail, vertices, ⟨0, _⟩ =>
      ⟨vertices.1, FromStates.ContainsPathVertices.start other tail.path vertices.2⟩
  | _, _, .cons _ tail, vertices, ⟨index + 1, bound⟩ =>
      edgeAt_vertices other tail vertices.2 ⟨index, Nat.lt_of_succ_lt_succ bound⟩

/-- Reading a walk as a clear path preserves its exact edge count as the segment count. -/
theorem path_segmentCount : {start finish : Gaussian.Basic.Canonical} → (walk : Walk grid start
  finish) →
    walk.path.segmentCount = walk.edgeCount
  | _, _, .nil _ => rfl
  | _, _, .cons _ tail => congrArg (fun count => count + 1) tail.path_segmentCount

/-- A retained walk whose final point is a grid vertex has every clear-path vertex in the same grid. -/
theorem vertices : {start finish : Gaussian.Basic.Canonical} → (walk : Walk grid start finish) →
    FromStates.ContainsVertex grid finish → FromStates.ContainsPathVertices grid
      walk.path
  | _, _, .nil _, last => last
  | _, _, .cons edge tail, last => ⟨edge.vertices.1, tail.vertices last⟩

/-- Convert the monotone axis spine directly, preserving its actual adjacent
intervals and the same retained horizontal-line certificate on every edge. -/
@[expose] def horizontalIncreasing (line : ClearGrid.HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal) :
    {start finish : Fraction.Rational} → AxisWalks.IncreasingWalk grid.xIntervals start finish →
      Walk grid (Basic.point start line.coordinate)
        (Basic.point finish line.coordinate)
  | _, _, .nil coordinate => .nil (Basic.point coordinate line.coordinate)
  | _, _, .cons interval adjacent tail => .cons (.horizontal interval adjacent line member)
    (Walk.horizontalIncreasing line member tail)

/-- Lift an increasing vertical-axis walk using one retained vertical line clearance.

The result preserves the original adjacent intervals and uses the same fixed-line payload for every edge. -/
@[expose] def verticalIncreasing (line : ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical) :
    {start finish : Fraction.Rational} → AxisWalks.IncreasingWalk grid.yIntervals start finish →
      Walk grid (Basic.point line.coordinate start)
        (Basic.point line.coordinate finish)
  | _, _, .nil coordinate => .nil (Basic.point line.coordinate coordinate)
  | _, _, .cons interval adjacent tail => .cons (.vertical interval adjacent line member)
    (Walk.verticalIncreasing line member tail)

/-- Lift either orientation without repeating the axis search. -/
@[expose] def horizontalAxis (line : ClearGrid.HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal)
    {start finish : Fraction.Rational} : AxisWalks.Walk grid.xIntervals start finish →
      Walk grid (Basic.point start line.coordinate)
        (Basic.point finish line.coordinate)
  | .forward increasing => horizontalIncreasing line member increasing
  | .backward increasing => (horizontalIncreasing line member increasing).reverse

/-- Lift either orientation of an existing vertical-axis walk without repeating the axis search. -/
@[expose] def verticalAxis (line : ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical)
    {start finish : Fraction.Rational} : AxisWalks.Walk grid.yIntervals start finish →
      Walk grid (Basic.point line.coordinate start)
        (Basic.point line.coordinate finish)
  | .forward increasing => verticalIncreasing line member increasing
  | .backward increasing => (verticalIncreasing line member increasing).reverse

end Walk

/-- A horizontal segment split at every intermediate grid coordinate.
The fixed-line lookup returns the original retained clearance payload. -/
@[expose] def horizontalWalk (grid : ClearGrid polynomial ambient) (start finish y :
  Fraction.Rational)
    (startMember : start ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (finishMember : finish ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (lineMember : y ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate) : Walk
      grid (Basic.point start y) (Basic.point finish y) :=
  let line := AxisWalks.lookup y grid.horizontal lineMember
  let axis := AxisWalks.walk grid.vertical grid.vertical_ordered start finish startMember finishMember
  let walk := Walk.horizontalAxis line.entry line.member axis
  walk.castEndpoints (congrArg (Basic.point start) line.coordinate_eq) (congrArg
    (Basic.point finish) line.coordinate_eq)

/-- Split a vertical segment at every intermediate retained grid coordinate.

The finite line lookup supplies the original clearance payload, and the axis walk preserves the requested direction and
endpoints. -/
@[expose] def verticalWalk (grid : ClearGrid polynomial ambient) (x start finish : Fraction.Rational)
    (lineMember : x ∈ grid.vertical.map ClearGrid.VerticalLine.coordinate)
    (startMember : start ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate)
    (finishMember : finish ∈ grid.horizontal.map ClearGrid.HorizontalLine.coordinate) :
      Walk grid (Basic.point x start) (Basic.point x finish)
      :=
  let line := AxisWalks.lookup x grid.vertical lineMember
  let axis := AxisWalks.walk grid.horizontal grid.horizontal_ordered start finish startMember finishMember
  let walk := Walk.verticalAxis line.entry line.member axis
  walk.castEndpoints (congrArg (fun value => Basic.point value start) line.coordinate_eq)
    (congrArg (fun value => Basic.point value finish) line.coordinate_eq)

/-- Replace one original clear segment, possibly certified in a smaller
ambient box, by adjacent shared-grid edges with exactly the same endpoints. -/
@[expose] def splitSegment (grid : ClearGrid polynomial ambient) {pathAmbient : Box}
  :
    {start finish : Gaussian.Basic.Canonical} → (segment : ClearPath.ClearSegment polynomial pathAmbient start
      finish) →
      FromStates.ContainsVertex grid start → FromStates.ContainsVertex grid finish
        → Walk grid start finish
  | _, _, .horizontal xStart xFinish y _ _ _ _ _, first, last =>
      horizontalWalk grid xStart xFinish y first.1 last.1 first.2
  | _, _, .vertical x yStart yFinish _ _ _ _ _, first, last =>
      verticalWalk grid x yStart yFinish first.1 first.2 last.2

/-- Split the complete path using the retained grid.  Each segment keeps its
own traversal direction; stationary original segments contribute no motion. -/
@[expose] def splitPath (grid : ClearGrid polynomial ambient) {pathAmbient : Box} :
    {start finish : Gaussian.Basic.Canonical} → (path : ClearPath polynomial pathAmbient start
      finish) →
      FromStates.ContainsPathVertices grid path → Walk grid start finish
  | _, _, .nil point, _ => .nil point
  | _, _, .cons head tail, onGrid =>
      (splitSegment grid head onGrid.1 (FromStates.ContainsPathVertices.start
        grid tail onGrid.2)).append
        (Walks.splitPath grid tail onGrid.2)

end

end Purelib.Polynomial.Geometry.Grid.Walks
