module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Nodup
import Purelib.Data.List.Append
import Purelib.Data.List.Membership
import Purelib.Data.List.Reverse
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Riemann.Meshes.GridLiftedBoundarySimplicity
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryCounts

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

public section

/-!
# Simplicity of the actual subdivided exterior

Opposite sides reuse the retained increasing axis walks. Source coordinates
use half-open sides, so each corner occurs once even after reversing the top
and left walks. No replacement four-edge rectangle is used.
-/

namespace Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk

variable {Alpha : Type} {key : Alpha → Fraction.Rational} {intervals : List (Geometry.Grid.ClearGrid.Interval key)}

open Purelib.Polynomial.Geometry.Grid.AxisWalks
/-- A strictly increasing walk contains at least one interval. -/
theorem edges_length_pos {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals
  start finish)
    (strict : start < finish) : 0 < walk.edges.length := by
  cases walk with
  | nil => exact ((lt_irrefl _) strict).elim
  | cons => exact Nat.zero_lt_succ _

/-- The lower endpoints of an increasing walk have no duplicates.

Each ordered interval starts strictly before every later retained interval,
so its lower coordinate cannot equal a later lower coordinate. -/
theorem lowerCoordinates_nodup : ∀ {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk
  intervals start finish),
    (walk.edges.map (fun interval => key interval.lower)).Nodup
  | _, _, .nil _ => .nil
  | _, _, .cons first _ tail => by
      refine List.pairwise_cons.mpr ⟨?_, tail.lowerCoordinates_nodup⟩
      intro value member same
      cases same
      rcases Purelib.Data.List.Map.mem_map.mp member with ⟨interval, member, equal⟩
      have strict := first.ordered.trans_le (tail.edge_bounds interval member).1
      rw [equal] at strict
      exact (lt_irrefl _) strict

/-- The upper endpoints of an increasing walk have no duplicates.

Every later interval finishes strictly beyond the preceding upper endpoint,
which excludes duplicate upper coordinates in the retained walk. -/
theorem upperCoordinates_nodup : ∀ {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk
  intervals start finish),
    (walk.edges.map (fun interval => key interval.upper)).Nodup
  | _, _, .nil _ => .nil
  | _, _, .cons first _ tail => by
      refine List.pairwise_cons.mpr ⟨?_, tail.upperCoordinates_nodup⟩
      intro value member same
      cases same
      rcases Purelib.Data.List.Map.mem_map.mp member with ⟨interval, member, equal⟩
      have strict := (tail.edge_bounds interval member).1.trans_lt interval.ordered
      rw [equal] at strict
      exact (lt_irrefl _) strict

end Purelib.Polynomial.Geometry.Grid.AxisWalks.IncreasingWalk

namespace Purelib.Polynomial.Geometry.Grid.Walks.Walk

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

/-- Transporting a walk's endpoint indices preserves its finishing-coordinate list. -/
theorem finishCoordinates_castEndpoints {start finish first last : Gaussian.Basic.Canonical} (walk :
  Geometry.Grid.Walks.Walk grid start finish)
    (startEq : start = first) (finishEq : finish = last) :
    (walk.castEndpoints startEq finishEq).finishCoordinates = walk.finishCoordinates := by
  cases startEq
  cases finishEq
  rfl

/-- The starts of the horizontal increasing walk are its axis intervals' lower endpoints lifted to the fixed grid line.
-/
theorem horizontalIncreasing_starts (line : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : line ∈
  grid.horizontal) :
    ∀ {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals start finish),
      (Geometry.Grid.Walks.Walk.horizontalIncreasing line member walk).startCoordinates =
        (walk.edges.map (fun interval => interval.lower.coordinate)).map (fun x => Gaussian.Components.Basic.point x
          line.coordinate)
  | _, _, .nil _ => rfl
  | _, _, .cons _ _ tail => congrArg (List.cons _)
    (Purelib.Polynomial.Geometry.Grid.Walks.Walk.horizontalIncreasing_starts line member tail)

/-- The finishes of the horizontal increasing walk are its axis intervals' upper endpoints lifted to the fixed grid
line. -/
theorem horizontalIncreasing_finishes (line : Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : line
  ∈ grid.horizontal) :
    ∀ {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals start finish),
      (Geometry.Grid.Walks.Walk.horizontalIncreasing line member walk).finishCoordinates =
        (walk.edges.map (fun interval => interval.upper.coordinate)).map (fun x => Gaussian.Components.Basic.point x
          line.coordinate)
  | _, _, .nil _ => rfl
  | _, _, .cons _ _ tail => congrArg (List.cons _)
    (Purelib.Polynomial.Geometry.Grid.Walks.Walk.horizontalIncreasing_finishes line member tail)

/-- The starts of the vertical increasing walk are its axis intervals' lower endpoints lifted to the fixed grid line. -/
theorem verticalIncreasing_starts (line : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical) :
    ∀ {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals start finish),
      (Geometry.Grid.Walks.Walk.verticalIncreasing line member walk).startCoordinates =
        (walk.edges.map (fun interval => interval.lower.coordinate)).map (fun y => Gaussian.Components.Basic.point
          line.coordinate y)
  | _, _, .nil _ => rfl
  | _, _, .cons _ _ tail => congrArg (List.cons _)
    (Purelib.Polynomial.Geometry.Grid.Walks.Walk.verticalIncreasing_starts line member tail)

/-- The finishes of the vertical increasing walk are its axis intervals' upper endpoints lifted to the fixed grid line.
-/
theorem verticalIncreasing_finishes (line : Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member : line ∈
  grid.vertical) :
    ∀ {start finish : Fraction.Rational} (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals start finish),
      (Geometry.Grid.Walks.Walk.verticalIncreasing line member walk).finishCoordinates =
        (walk.edges.map (fun interval => interval.upper.coordinate)).map (fun y => Gaussian.Components.Basic.point
          line.coordinate y)
  | _, _, .nil _ => rfl
  | _, _, .cons _ _ tail => congrArg (List.cons _)
    (Purelib.Polynomial.Geometry.Grid.Walks.Walk.verticalIncreasing_finishes line member tail)

end Purelib.Polynomial.Geometry.Grid.Walks.Walk

namespace Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame.Axes

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

section
open Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame
/-- Read the horizontal walk's starts from the cached axis intervals and the retained fixed coordinate. -/
theorem horizontal_starts (axes : Axes grid) (y : Fraction.Rational)
  (member : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
    (axes.horizontal y member).startCoordinates =
      (axes.x.edges.map (fun interval => interval.lower.coordinate)).map (fun x => Gaussian.Components.Basic.point x y)
        := by
  dsimp only [horizontal]
  rw [Geometry.Grid.Walks.Walk.startCoordinates_castEndpoints, Geometry.Grid.Walks.Walk.horizontalIncreasing_starts,
    (Geometry.Grid.AxisWalks.lookup y grid.horizontal member).coordinate_eq]

/-- Read the horizontal walk's finishes from the cached axis intervals and the retained fixed coordinate. -/
theorem horizontal_finishes (axes : Axes grid) (y : Fraction.Rational)
  (member : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
    (axes.horizontal y member).finishCoordinates =
      (axes.x.edges.map (fun interval => interval.upper.coordinate)).map (fun x => Gaussian.Components.Basic.point x y)
        := by
  dsimp only [horizontal]
  rw [Geometry.Grid.Walks.Walk.finishCoordinates_castEndpoints, Geometry.Grid.Walks.Walk.horizontalIncreasing_finishes,
    (Geometry.Grid.AxisWalks.lookup y grid.horizontal member).coordinate_eq]

/-- Read the vertical walk's starts from the cached axis intervals and the retained fixed coordinate. -/
theorem vertical_starts (axes : Axes grid) (x : Fraction.Rational)
  (member : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate) :
    (axes.vertical x member).startCoordinates =
      (axes.y.edges.map (fun interval => interval.lower.coordinate)).map (fun y => Gaussian.Components.Basic.point x y)
        := by
  dsimp only [vertical]
  rw [Geometry.Grid.Walks.Walk.startCoordinates_castEndpoints, Geometry.Grid.Walks.Walk.verticalIncreasing_starts,
    (Geometry.Grid.AxisWalks.lookup x grid.vertical member).coordinate_eq]

/-- Read the vertical walk's finishes from the cached axis intervals and the retained fixed coordinate. -/
theorem vertical_finishes (axes : Axes grid) (x : Fraction.Rational)
  (member : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate) :
    (axes.vertical x member).finishCoordinates =
      (axes.y.edges.map (fun interval => interval.upper.coordinate)).map (fun y => Gaussian.Components.Basic.point x y)
        := by
  dsimp only [vertical]
  rw [Geometry.Grid.Walks.Walk.finishCoordinates_castEndpoints, Geometry.Grid.Walks.Walk.verticalIncreasing_finishes,
    (Geometry.Grid.AxisWalks.lookup x grid.vertical member).coordinate_eq]

/-- The horizontal walk's starts have no duplicate coordinates. -/
theorem horizontal_starts_simple (axes : Axes grid) (y :
  Fraction.Rational) (member : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
    (axes.horizontal y member).startCoordinates.Nodup := open Purelib in by
  rw [axes.horizontal_starts]
  exact Data.List.Nodup.nodup_map_of_injective (fun _ _ equal => congrArg (fun value : Gaussian.Basic.Canonical =>
    value.re) equal) axes.x.lowerCoordinates_nodup

/-- The horizontal walk's finishes have no duplicate coordinates. -/
theorem horizontal_finishes_simple (axes : Axes grid) (y :
  Fraction.Rational) (member : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
    (axes.horizontal y member).finishCoordinates.Nodup := open Purelib in by
  rw [axes.horizontal_finishes]
  exact Data.List.Nodup.nodup_map_of_injective (fun _ _ equal => congrArg (fun value : Gaussian.Basic.Canonical =>
    value.re) equal) axes.x.upperCoordinates_nodup

/-- The vertical walk's starts have no duplicate coordinates. -/
theorem vertical_starts_simple (axes : Axes grid) (x :
  Fraction.Rational) (member : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate) :
    (axes.vertical x member).startCoordinates.Nodup := open Purelib in by
  rw [axes.vertical_starts]
  exact Data.List.Nodup.nodup_map_of_injective (fun _ _ equal => congrArg (fun value : Gaussian.Basic.Canonical =>
    value.im) equal) axes.y.lowerCoordinates_nodup

/-- The vertical walk's finishes have no duplicate coordinates. -/
theorem vertical_finishes_simple (axes : Axes grid) (x :
  Fraction.Rational) (member : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate) :
    (axes.vertical x member).finishCoordinates.Nodup := open Purelib in by
  rw [axes.vertical_finishes]
  exact Data.List.Nodup.nodup_map_of_injective (fun _ _ equal => congrArg (fun value : Gaussian.Basic.Canonical =>
    value.im) equal) axes.y.upperCoordinates_nodup

/-- Every horizontal start coordinate lies on its fixed grid line and includes the lower ambient endpoint and excludes
the upper endpoint. -/
theorem horizontal_start_bounds (axes : Axes grid) (y :
  Fraction.Rational) (line : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    {vertex : Gaussian.Basic.Canonical} (member : vertex ∈ (axes.horizontal y line).startCoordinates) :
    ambient.xLower ≤ vertex.re ∧ vertex.re < ambient.xUpper ∧ vertex.im = y := open Purelib in by
  rw [axes.horizontal_starts] at member
  rcases Data.List.Map.mem_map.mp member with ⟨x, coordinateMember, rfl⟩
  rcases Data.List.Map.mem_map.mp coordinateMember with ⟨interval, intervalMember, rfl⟩
  exact ⟨(axes.x.edge_bounds interval intervalMember).1, interval.ordered.trans_le (axes.x.edge_bounds interval
    intervalMember).2, rfl⟩

/-- Every horizontal finish coordinate lies on its fixed grid line and excludes the lower ambient endpoint and includes
the upper endpoint. -/
theorem horizontal_finish_bounds (axes : Axes grid) (y :
  Fraction.Rational) (line : y ∈ grid.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate)
    {vertex : Gaussian.Basic.Canonical} (member : vertex ∈ (axes.horizontal y line).finishCoordinates) :
    ambient.xLower < vertex.re ∧ vertex.re ≤ ambient.xUpper ∧ vertex.im = y := open Purelib in by
  rw [axes.horizontal_finishes] at member
  rcases Data.List.Map.mem_map.mp member with ⟨x, coordinateMember, rfl⟩
  rcases Data.List.Map.mem_map.mp coordinateMember with ⟨interval, intervalMember, rfl⟩
  exact ⟨(axes.x.edge_bounds interval intervalMember).1.trans_lt interval.ordered, (axes.x.edge_bounds interval
    intervalMember).2, rfl⟩

/-- Every vertical start coordinate lies on its fixed grid line and includes the lower ambient endpoint and excludes the
upper endpoint. -/
theorem vertical_start_bounds (axes : Axes grid) (x : Fraction.Rational)
  (line : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    {vertex : Gaussian.Basic.Canonical} (member : vertex ∈ (axes.vertical x line).startCoordinates) :
    ambient.yLower ≤ vertex.im ∧ vertex.im < ambient.yUpper ∧ vertex.re = x := open Purelib in by
  rw [axes.vertical_starts] at member
  rcases Data.List.Map.mem_map.mp member with ⟨y, coordinateMember, rfl⟩
  rcases Data.List.Map.mem_map.mp coordinateMember with ⟨interval, intervalMember, rfl⟩
  exact ⟨(axes.y.edge_bounds interval intervalMember).1, interval.ordered.trans_le (axes.y.edge_bounds interval
    intervalMember).2, rfl⟩

/-- Every vertical finish coordinate lies on its fixed grid line and excludes the lower ambient endpoint and includes
the upper endpoint. -/
theorem vertical_finish_bounds (axes : Axes grid) (x :
  Fraction.Rational) (line : x ∈ grid.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate)
    {vertex : Gaussian.Basic.Canonical} (member : vertex ∈ (axes.vertical x line).finishCoordinates) :
    ambient.yLower < vertex.im ∧ vertex.im ≤ ambient.yUpper ∧ vertex.re = x := open Purelib in by
  rw [axes.vertical_finishes] at member
  rcases Data.List.Map.mem_map.mp member with ⟨y, coordinateMember, rfl⟩
  rcases Data.List.Map.mem_map.mp coordinateMember with ⟨interval, intervalMember, rfl⟩
  exact ⟨(axes.y.edge_bounds interval intervalMember).1.trans_lt interval.ordered, (axes.y.edge_bounds interval
    intervalMember).2, rfl⟩

end

end Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame.Axes

namespace Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  ClearGrid polynomial ambient}

/-- Reversing a list preserves the absence of duplicate entries.

The original head becomes the final singleton after the reversed tail.
Its retained freshness certificate excludes every cross-list duplicate. -/
private theorem nodup_reverse {Alpha : Type} : ∀ {values : List Alpha}, values.Nodup → values.reverse.Nodup
  | [], _ => .nil
  | head :: tail, simple => by
      rw [List.Reverse.reverse_cons]
      apply Purelib.Data.List.Nodup.nodup_append
        (nodup_reverse (List.pairwise_cons.mp
        simple).2)
        (Purelib.Data.List.Nodup.nodup_singleton head)
      intro first firstMember last lastMember same
      have equal := same.trans (List.Membership.mem_singleton.mp lastMember)
      exact (List.pairwise_cons.mp simple).1 head (equal ▸ (List.Reverse.mem_reverse _).mp firstMember) rfl

/-- Read the four ordered starting-coordinate lists of the framed boundary.

The top and left lists reverse their respective axis walks, matching the positive boundary orientation. -/
theorem boundary_starts (frame : AmbientFrame grid) :
    frame.boundary.startCoordinates =
      (frame.axes.horizontal ambient.yLower frame.yLower).startCoordinates ++
      (frame.axes.vertical ambient.xUpper frame.xUpper).startCoordinates ++
      (frame.axes.horizontal ambient.yUpper frame.yUpper).finishCoordinates.reverse ++
      (frame.axes.vertical ambient.xLower frame.xLower).finishCoordinates.reverse := by
  simp only [boundary, Geometry.Grid.Walks.Walk.startCoordinates_append,
    Geometry.Grid.Walks.Walk.startCoordinates_reverse, List.Append.append_assoc, -eq_self, -iff_self]
  rfl

/-- The subdivided boundary of a proper ambient box visits each starting vertex once.

The four half-open side lists include each corner on exactly one side. -/
theorem boundary_simple (frame : AmbientFrame grid) (proper : ambient.Proper) :
  frame.boundary.startCoordinates.Nodup := open Purelib in by
  rw [frame.boundary_starts]
  let bottom := (frame.axes.horizontal ambient.yLower frame.yLower).startCoordinates
  let right := (frame.axes.vertical ambient.xUpper frame.xUpper).startCoordinates
  let top := (frame.axes.horizontal ambient.yUpper frame.yUpper).finishCoordinates.reverse
  let left := (frame.axes.vertical ambient.xLower frame.xLower).finishCoordinates.reverse
  have bottomBounds : ∀ {vertex : Gaussian.Basic.Canonical}, vertex ∈ bottom →
      ambient.xLower ≤ vertex.re ∧ vertex.re < ambient.xUpper ∧ vertex.im = ambient.yLower :=
    fun member => frame.axes.horizontal_start_bounds _ _ member
  have rightBounds : ∀ {vertex : Gaussian.Basic.Canonical}, vertex ∈ right →
      ambient.yLower ≤ vertex.im ∧ vertex.im < ambient.yUpper ∧ vertex.re = ambient.xUpper :=
    fun member => frame.axes.vertical_start_bounds _ _ member
  have topBounds : ∀ vertex ∈ top, ambient.xLower < vertex.re ∧ vertex.re ≤ ambient.xUpper ∧ vertex.im = ambient.yUpper
    :=
    fun _ member => frame.axes.horizontal_finish_bounds _ _ ((List.Reverse.mem_reverse _).mp member)
  have leftBounds : ∀ vertex ∈ left, ambient.yLower < vertex.im ∧ vertex.im ≤ ambient.yUpper ∧ vertex.re =
    ambient.xLower :=
    fun _ member => frame.axes.vertical_finish_bounds _ _ ((List.Reverse.mem_reverse _).mp member)
  have bottomRight : ∀ a ∈ bottom, ∀ b ∈ right, a ≠ b := by
    intro a ha b hb same
    have bound := (bottomBounds ha).2.1
    rw [same, (rightBounds hb).2.2] at bound
    exact (lt_irrefl _) bound
  have bottomTop : ∀ a ∈ bottom, ∀ b ∈ top, a ≠ b := by
    intro a ha b hb same
    have equal := (bottomBounds ha).2.2.symm.trans ((congrArg (fun value : Gaussian.Basic.Canonical => value.im)
      same).trans (topBounds b hb).2.2)
    exact proper.2.ne equal
  have bottomLeft : ∀ a ∈ bottom, ∀ b ∈ left, a ≠ b := by
    intro a ha b hb same
    have bound := (leftBounds b hb).1
    rw [← same, (bottomBounds ha).2.2] at bound
    exact (lt_irrefl _) bound
  have rightTop : ∀ a ∈ right, ∀ b ∈ top, a ≠ b := by
    intro a ha b hb same
    have bound := (rightBounds ha).2.1
    rw [same, (topBounds b hb).2.2] at bound
    exact (lt_irrefl _) bound
  have rightLeft : ∀ a ∈ right, ∀ b ∈ left, a ≠ b := by
    intro a ha b hb same
    have equal := (rightBounds ha).2.2.symm.trans ((congrArg (fun value : Gaussian.Basic.Canonical => value.re)
      same).trans (leftBounds b hb).2.2)
    exact proper.1.ne equal.symm
  have topLeft : ∀ a ∈ top, ∀ b ∈ left, a ≠ b := by
    intro a ha b hb same
    have bound := (topBounds a ha).1
    rw [same, (leftBounds b hb).2.2] at bound
    exact (lt_irrefl _) bound
  have bottomSimple := frame.axes.horizontal_starts_simple ambient.yLower frame.yLower
  have rightSimple := frame.axes.vertical_starts_simple ambient.xUpper frame.xUpper
  have topSimple : top.Nodup := nodup_reverse
    (frame.axes.horizontal_finishes_simple ambient.yUpper frame.yUpper)
  have leftSimple : left.Nodup := nodup_reverse
    (frame.axes.vertical_finishes_simple ambient.xLower frame.xLower)
  exact Data.List.Nodup.nodup_append
    (Data.List.Nodup.nodup_append (Data.List.Nodup.nodup_append bottomSimple rightSimple bottomRight) topSimple
      (fun _ member => (List.Membership.mem_append.mp member).elim (fun member => bottomTop _ member) (fun member =>
        rightTop _ member)))
    leftSimple (fun _ member => (List.Membership.mem_append.mp member).elim
      (fun member => (List.Membership.mem_append.mp member).elim (fun member => bottomLeft _ member) (fun member =>
        rightLeft _ member))
      (fun member => topLeft _ member))

/-- Every boundary starting vertex lies on one of the four ambient side coordinates.

Membership follows the four retained half-open side lists. Reversal changes
the traversal order while retaining each original side coordinate. -/
theorem boundary_start_on_side (frame : AmbientFrame grid) {vertex :
  Gaussian.Basic.Canonical}
    (member : vertex ∈ frame.boundary.startCoordinates) :
    vertex.re = ambient.xLower ∨ vertex.re = ambient.xUpper ∨ vertex.im = ambient.yLower ∨ vertex.im = ambient.yUpper :=
      by
  rw [frame.boundary_starts] at member
  rcases List.Membership.mem_append.mp member with member | member
  · rcases List.Membership.mem_append.mp member with member | member
    · rcases List.Membership.mem_append.mp member with member | member
      · exact .inr (.inr (.inl (frame.axes.horizontal_start_bounds _ _ member).2.2))
      · exact .inr (.inl (frame.axes.vertical_start_bounds _ _ member).2.2)
    · exact .inr (.inr (.inr (frame.axes.horizontal_finish_bounds _ _ ((List.Reverse.mem_reverse _).mp member)).2.2))
  · exact .inl (frame.axes.vertical_finish_bounds _ _ ((List.Reverse.mem_reverse _).mp member)).2.2

/-- The boundary of a proper framed box has at least four subdivided edges. -/
theorem boundary_edgeCount_ge_four (frame : AmbientFrame grid) (proper :
  ambient.Proper) :
    4 ≤ frame.boundary.edgeCount := by
  have xPositive := frame.axes.x.edges_length_pos proper.1
  have yPositive := frame.axes.y.edges_length_pos proper.2
  rw [frame.axes.x_edges] at xPositive
  rw [frame.axes.y_edges] at yPositive
  rw [frame.boundary_edgeCount]
  omega

end Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame
