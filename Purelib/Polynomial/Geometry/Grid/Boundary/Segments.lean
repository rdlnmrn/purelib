module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Polynomial.Geometry.Grid.WindowBoundary
public import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

@[expose] public section

/-!
# Side certificates for the literal subdivided window boundary

Every original grid segment, including reversed and repeated occurrences,
has endpoints in the box and on a common side. These certificates feed the
Newton comparison of its retained integration parents without new geometry.
-/

namespace Purelib

namespace Riemann.Paths.PreparedBoundarySegments.SameSide

/-- Exchanging two endpoints preserves their membership on a common box side. -/
theorem reverse
    {box : Box} {first last : Gaussian.Basic.Canonical}
    (side : Riemann.Paths.PreparedBoundarySegments.SameSide box first last) :
      Riemann.Paths.PreparedBoundarySegments.SameSide box last first := by
  rcases side with side | side | side | side
  · exact Or.inl side.symm
  · exact Or.inr (Or.inl side.symm)
  · exact Or.inr (Or.inr (Or.inl side.symm))
  · exact Or.inr (Or.inr (Or.inr side.symm))

end Riemann.Paths.PreparedBoundarySegments.SameSide

namespace Polynomial.Geometry.Grid.Boundary.Segments.PreparedBoundarySegments

/-- A proposition about the actual segment spine, not a replacement path. -/
def OnBoundary (box : Box) {polynomial : GaussianPolynomial} {ambient :
  Box} :
    {start finish : Gaussian.Basic.Canonical} → ClearPath polynomial ambient start finish → Prop
  | _, _, .nil _ => True
  | start, _, .cons (middle := middle) _ tail =>
      box.Contains start ∧ box.Contains middle ∧ Riemann.Paths.PreparedBoundarySegments.SameSide box start middle ∧
        OnBoundary box tail

end Polynomial.Geometry.Grid.Boundary.Segments.PreparedBoundarySegments

end Purelib

namespace Purelib.Polynomial.Geometry.Grid.Boundary.Segments.Walk

variable {polynomial : GaussianPolynomial} {ambient box : Box} {grid :
  ClearGrid polynomial ambient}

section Walk

/-- Appending two boundary walks preserves containment and common-side evidence for every actual segment. -/
theorem boundary_append : {start middle finish :
  Gaussian.Basic.Canonical} →
    (first : Geometry.Grid.Walks.Walk grid start middle) → (second : Geometry.Grid.Walks.Walk grid middle finish) →
    Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box first.path →
      Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box second.path →
      Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box (first.append second).path
  | _, _, _, .nil _, _, _, bounded => bounded
  | _, _, _, .cons _ tail, second, bounded, rest =>
      ⟨bounded.1, bounded.2.1, bounded.2.2.1,
        boundary_append tail second bounded.2.2.2 rest⟩

/-- Reversing a boundary walk onto a boundary suffix preserves every segment's boundary evidence. -/
theorem boundary_reverseOnto : {start middle finish
  : Gaussian.Basic.Canonical} →
    (walk : Geometry.Grid.Walks.Walk grid start middle) → (suffix : Geometry.Grid.Walks.Walk grid start finish) →
    Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box walk.path →
      Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box suffix.path →
      Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box (walk.reverseOnto suffix).path
  | _, _, _, .nil _, _, _, bounded => bounded
  | _, _, _, .cons edge tail, suffix, bounded, rest =>
      boundary_reverseOnto tail (.cons (.reverse edge)
        suffix) bounded.2.2.2
        ⟨bounded.2.1, bounded.1, bounded.2.2.1.reverse, rest⟩

/-- Reversing a walk preserves its actual segments' boundary certificates. -/
theorem boundary_reverse {start finish :
  Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish)
    (bounded : Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box walk.path) :
      Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box walk.reverse.path :=
  boundary_reverseOnto walk (.nil start) bounded trivial

/-- Transporting endpoint indices preserves the segment boundary certificates. -/
theorem boundary_castEndpoints {start finish first
  last : Gaussian.Basic.Canonical} (walk : Geometry.Grid.Walks.Walk grid start finish)
    (firstEq : start = first) (lastEq : finish = last) (bounded :
      Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box walk.path) :
    Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box (walk.castEndpoints firstEq lastEq).path :=
      by
  cases firstEq
  cases lastEq
  exact bounded

/-- A bounded increasing horizontal walk on a box-side coordinate lies on that boundary side. -/
theorem horizontalIncreasing_boundary (line :
  Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient) (member : line ∈ grid.horizontal)
    (side : line.coordinate = box.yLower ∨ line.coordinate = box.yUpper) :
    {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.xIntervals start finish) →
    box.xLower ≤ start → finish ≤ box.xUpper →
    Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box
      (Geometry.Grid.Walks.Walk.horizontalIncreasing line member walk).path
  | _, _, .nil _, _, _ => trivial
  | _, _, .cons interval adjacent tail, first, last => by
      have y : box.yLower ≤ line.coordinate ∧ line.coordinate ≤ box.yUpper := by
        rcases side with equal | equal <;> rw [equal]
        · exact ⟨le_rfl, box.y_valid⟩
        · exact ⟨box.y_valid, le_rfl⟩
      refine ⟨⟨first, interval.ordered.le.trans (tail.ordered.trans last), y⟩,
        ⟨first.trans interval.ordered.le, tail.ordered.trans last, y⟩, ?_,
        horizontalIncreasing_boundary line member side tail
          (first.trans interval.ordered.le) last⟩
      rcases side with equal | equal
      · exact Or.inr (Or.inr (Or.inl ⟨equal, equal⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨equal, equal⟩))

/-- A bounded increasing vertical walk on a box-side coordinate lies on that boundary side. -/
theorem verticalIncreasing_boundary (line :
  Geometry.Grid.ClearGrid.VerticalLine polynomial ambient) (member : line ∈ grid.vertical)
    (side : line.coordinate = box.xLower ∨ line.coordinate = box.xUpper) :
    {start finish : Fraction.Rational} → (walk : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals start finish) →
    box.yLower ≤ start → finish ≤ box.yUpper →
    Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box (Geometry.Grid.Walks.Walk.verticalIncreasing
      line member walk).path
  | _, _, .nil _, _, _ => trivial
  | _, _, .cons interval adjacent tail, first, last => by
      have x : box.xLower ≤ line.coordinate ∧ line.coordinate ≤ box.xUpper := by
        rcases side with equal | equal <;> rw [equal]
        · exact ⟨le_rfl, box.x_valid⟩
        · exact ⟨box.x_valid, le_rfl⟩
      refine ⟨⟨x.1, x.2, first, interval.ordered.le.trans (tail.ordered.trans last)⟩,
        ⟨x.1, x.2, first.trans interval.ordered.le, tail.ordered.trans last⟩, ?_,
        verticalIncreasing_boundary line member side tail
          (first.trans interval.ordered.le) last⟩
      rcases side with equal | equal
      · exact Or.inl ⟨equal, equal⟩
      · exact Or.inr (Or.inl ⟨equal, equal⟩)

end Walk
end Purelib.Polynomial.Geometry.Grid.Boundary.Segments.Walk

namespace Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window

open Purelib.Polynomial.Geometry.Grid.Boundary.Segments.Walk

variable {polynomial : GaussianPolynomial} {ambient box : Box}
  {grid : ClearGrid polynomial ambient}

/-- The window's horizontal subdivision lies on its chosen top or bottom side. -/
theorem horizontal_boundary (window : Window grid box) {y : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.HorizontalLine.coordinate) grid.horizontal y)
    (side : y = box.yLower ∨ y = box.yUpper) : Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box
      (window.horizontal line).path := by
  apply Boundary.Segments.Walk.boundary_castEndpoints
  exact Boundary.Segments.Walk.horizontalIncreasing_boundary line.entry line.member
    (by simpa only [line.coordinate_eq] using side) window.x le_rfl le_rfl

/-- The window's vertical subdivision lies on its chosen left or right side. -/
theorem vertical_boundary (window : Window grid box) {x : Fraction.Rational}
    (line : Geometry.Grid.AxisWalks.Lookup (key := Geometry.Grid.ClearGrid.VerticalLine.coordinate) grid.vertical x)
    (side : x = box.xLower ∨ x = box.xUpper) : Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box
      (window.vertical line).path := by
  apply Boundary.Segments.Walk.boundary_castEndpoints
  exact Boundary.Segments.Walk.verticalIncreasing_boundary line.entry line.member
    (by simpa only [line.coordinate_eq] using side) window.y le_rfl le_rfl

/-- Every segment of the actual window boundary has endpoints in the box and on a common side.

The certificates follow the retained subdivisions, including reversed top and left occurrences. -/
theorem boundary_segments (window : Window grid box) :
  Geometry.Grid.Boundary.Segments.PreparedBoundarySegments.OnBoundary box window.boundary.path :=
  Boundary.Segments.Walk.boundary_append _ _ (window.horizontal_boundary window.bottom (Or.inl rfl))
    (Boundary.Segments.Walk.boundary_append _ _ (window.vertical_boundary window.right (Or.inr rfl))
      (Boundary.Segments.Walk.boundary_append _ _
        (Boundary.Segments.Walk.boundary_reverse (window.horizontal window.top)
        (window.horizontal_boundary window.top (Or.inr rfl)))
        (Boundary.Segments.Walk.boundary_reverse (window.vertical window.left)
          (window.vertical_boundary window.left (Or.inl rfl)))))

end Purelib.Polynomial.Geometry.Grid.WindowBoundary.Window
