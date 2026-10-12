module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.ClearGridCoverage
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Riemann.Paths.PreparedPathWinding
public import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Polynomial.Geometry.Grid.Axis.Full
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Tactic.Ring

open Purelib.Polynomial.Clearance.Box.Boundary.Basic (BoundaryClearance)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (EdgeValues)
open Purelib.Polynomial.Geometry.Grid.ClearGrid (HorizontalLine VerticalLine)
open Purelib.Polynomial.Geometry.Grid.Extension (CoordinateInclusion)

/-!
# A certified ambient frame around an extended clear grid

Reuse one boundary-clearance calculation for the four exterior lines.  Add
those lines and the sides of retained smaller branch states to the old grid.
The resulting cache preserves every old coordinate and supplies an actual
subdivided exterior walk, not four replacement chords.
-/

namespace Purelib.Polynomial.Geometry.Grid.FramedClearGrid

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib

public section

open Purelib.Data.Gaussian.Components.Basic (point)

open Purelib.Polynomial.Geometry.Grid.FromStates
  (BranchState verticalSides horizontalSides)

open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid
  (build_vertical_coordinates build_horizontal_coordinates)
open Purelib.Polynomial.Geometry.Grid.Axis.Full

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- Build the two vertical ambient frame lines using the same retained clearance bound. -/
@[expose] def frameVertical (clearance : BoundaryClearance polynomial ambient) :
    List (VerticalLine polynomial ambient) :=
  [⟨ambient.xLower, ⟨le_rfl, ambient.x_valid⟩,
    ⟨clearance.bound, clearance.positive, fun y lower upper =>
      clearance.lower (point ambient.xLower y) ⟨⟨le_rfl, ambient.x_valid, lower, upper⟩, Or.inl rfl⟩⟩⟩,
   ⟨ambient.xUpper, ⟨ambient.x_valid, le_rfl⟩,
    ⟨clearance.bound, clearance.positive, fun y lower upper =>
      clearance.lower (point ambient.xUpper y) ⟨⟨ambient.x_valid, le_rfl, lower, upper⟩, Or.inr (Or.inl rfl)⟩⟩⟩]

/-- Build the two horizontal ambient frame lines using the same retained clearance bound. -/
@[expose] def frameHorizontal (clearance : BoundaryClearance polynomial ambient) :
    List (HorizontalLine polynomial ambient) :=
  [⟨ambient.yLower, ⟨le_rfl, ambient.y_valid⟩,
    ⟨clearance.bound, clearance.positive, fun x lower upper =>
      clearance.lower (point x ambient.yLower) ⟨⟨lower, upper, le_rfl, ambient.y_valid⟩, Or.inr (Or.inr (Or.inl
        rfl))⟩⟩⟩,
   ⟨ambient.yUpper, ⟨ambient.y_valid, le_rfl⟩,
    ⟨clearance.bound, clearance.positive, fun x lower upper =>
      clearance.lower (point x ambient.yUpper) ⟨⟨lower, upper, ambient.y_valid, le_rfl⟩, Or.inr (Or.inr (Or.inr
        rfl))⟩⟩⟩]

section Grid

-- Retain the original framed-grid nominal API.

/-- All four ambient sides occur in the retained sorted axes.  Since every
line is inside the ambient box, these are the actual exterior coordinates. -/
structure AmbientFrame (grid : ClearGrid polynomial ambient) : Prop where
  /-- The ambient left coordinate occurs in the horizontal grid axis. -/ xLower : ambient.xLower ∈ grid.vertical.map
    VerticalLine.coordinate
  /-- The ambient right coordinate occurs in the horizontal grid axis. -/ xUpper : ambient.xUpper ∈ grid.vertical.map
    VerticalLine.coordinate
  /-- The ambient bottom coordinate occurs in the vertical grid axis. -/ yLower : ambient.yLower ∈ grid.horizontal.map
    HorizontalLine.coordinate
  /-- The ambient top coordinate occurs in the vertical grid axis. -/ yUpper : ambient.yUpper ∈ grid.horizontal.map
    HorizontalLine.coordinate

namespace AmbientFrame

variable {grid : ClearGrid polynomial ambient}

/-- Identify the full horizontal axis span with the ambient box bounds. -/
@[expose] def xSpan (frame : AmbientFrame grid) :
    Geometry.Grid.Axis.Full.Interval.Span (key := VerticalLine.coordinate) grid.vertical
      ambient.xLower ambient.xUpper :=
  .ofBounds grid.vertical grid.vertical_ordered (fun line _ => line.inside) frame.xLower frame.xUpper

/-- Identify the full vertical axis span with the ambient box bounds. -/
@[expose] def ySpan (frame : AmbientFrame grid) :
    Geometry.Grid.Axis.Full.Interval.Span (key := HorizontalLine.coordinate) grid.horizontal
      ambient.yLower ambient.yUpper :=
  .ofBounds grid.horizontal grid.horizontal_ordered (fun line _ => line.inside) frame.yLower frame.yUpper

set_option genInjectivity false in
/-- Share the two full adjacent-axis spines between opposite exterior sides. -/
structure Axes (grid : ClearGrid polynomial ambient) where
  /-- The cached increasing walk across the horizontal axis. -/ x : Geometry.Grid.AxisWalks.IncreasingWalk
    grid.xIntervals ambient.xLower ambient.xUpper
  /-- The cached horizontal walk uses exactly the original horizontal intervals. -/ x_edges : x.edges = grid.xIntervals
  /-- The cached increasing walk across the vertical axis. -/ y : Geometry.Grid.AxisWalks.IncreasingWalk grid.yIntervals
    ambient.yLower ambient.yUpper
  /-- The cached vertical walk uses exactly the original vertical intervals. -/ y_edges : y.edges = grid.yIntervals

constructive_injectivity Axes

/-- Compute and retain the two increasing axis walks of the framed grid.

Their edge lists are the original grid intervals, so all boundary walks reuse these exact subdivisions. -/
@[expose] def axes (frame : AmbientFrame grid) :
  Axes grid :=
  ⟨frame.xSpan.walk grid.vertical_ordered, frame.xSpan.walk_edges grid.vertical_ordered,
    frame.ySpan.walk grid.horizontal_ordered, frame.ySpan.walk_edges grid.horizontal_ordered⟩

namespace Axes

open Purelib.Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame
/-- Lift the cached horizontal axis walk along a retained clear grid line. -/
@[expose] def horizontal (axes : Axes grid) (y : Fraction.Rational)
  (member : y ∈ grid.horizontal.map HorizontalLine.coordinate) :
    Geometry.Grid.Walks.Walk grid (point ambient.xLower y) (point ambient.xUpper y) :=
  let line := Geometry.Grid.AxisWalks.lookup y grid.horizontal member
  (Geometry.Grid.Walks.Walk.horizontalIncreasing line.entry line.member axes.x).castEndpoints
    (congrArg (point ambient.xLower) line.coordinate_eq) (congrArg (point ambient.xUpper) line.coordinate_eq)

/-- Lift the cached vertical axis walk along a retained clear grid line. -/
@[expose] def vertical (axes : Axes grid) (x : Fraction.Rational)
  (member : x ∈ grid.vertical.map VerticalLine.coordinate) :
    Geometry.Grid.Walks.Walk grid (point x ambient.yLower) (point x ambient.yUpper) :=
  let line := Geometry.Grid.AxisWalks.lookup x grid.vertical member
  (Geometry.Grid.Walks.Walk.verticalIncreasing line.entry line.member axes.y).castEndpoints
    (congrArg (fun x => point x ambient.yLower) line.coordinate_eq) (congrArg (fun x => point x ambient.yUpper)
      line.coordinate_eq)

/-- The cached horizontal subdivision has the doubled winding of its full oriented side. -/
theorem horizontal_winding (axes : Axes grid) (y : Fraction.Rational)
  (member : y ∈ grid.horizontal.map HorizontalLine.coordinate) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (axes.horizontal y member).path =
      (Dense.Gaussian.Path.Box.Sides.horizontalEdge polynomial y ambient.xLower ambient.xUpper).doubledWinding := by
  dsimp only [horizontal]
  rw [Geometry.Grid.Winding.Walk.castEndpoints_winding,
    Geometry.Grid.Winding.Walk.horizontalIncreasing_winding,
    (Geometry.Grid.AxisWalks.lookup y grid.horizontal member).coordinate_eq]

/-- The cached vertical subdivision has the doubled winding of its full oriented side. -/
theorem vertical_winding (axes : Axes grid) (x : Fraction.Rational)
  (member : x ∈ grid.vertical.map VerticalLine.coordinate) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (axes.vertical x member).path =
      (Dense.Gaussian.Path.Box.Sides.verticalEdge polynomial x ambient.yLower ambient.yUpper).doubledWinding := by
  dsimp only [vertical]
  rw [Geometry.Grid.Winding.Walk.castEndpoints_winding,
    Geometry.Grid.Winding.Walk.verticalIncreasing_winding,
    (Geometry.Grid.AxisWalks.lookup x grid.vertical member).coordinate_eq]

/-- Read the horizontal walk as the sum over its original grid intervals. -/
theorem horizontal_value (axes : Axes grid) (y : Fraction.Rational)
  (member : y ∈ grid.horizontal.map HorizontalLine.coordinate)
    (values : EdgeValues) : values.walk (axes.horizontal y member) =
      Geometry.Grid.CellBoundary.sumValues (fun interval => values.horizontal interval.lower.coordinate
        interval.upper.coordinate y) grid.xIntervals := by
  dsimp only [horizontal]
  rw [Geometry.Grid.Axis.Full.EdgeValues.walk_castEndpoints,
    Geometry.Grid.Axis.Full.EdgeValues.walk_horizontalIncreasing, axes.x_edges,
    (Geometry.Grid.AxisWalks.lookup y grid.horizontal member).coordinate_eq]

/-- Read the vertical walk as the sum over its original grid intervals. -/
theorem vertical_value (axes : Axes grid) (x : Fraction.Rational)
  (member : x ∈ grid.vertical.map VerticalLine.coordinate)
    (values : EdgeValues) : values.walk (axes.vertical x member) =
      Geometry.Grid.CellBoundary.sumValues (fun interval => values.vertical x interval.lower.coordinate
        interval.upper.coordinate) grid.yIntervals := by
  dsimp only [vertical]
  rw [Geometry.Grid.Axis.Full.EdgeValues.walk_castEndpoints,
    Geometry.Grid.Axis.Full.EdgeValues.walk_verticalIncreasing, axes.y_edges,
    (Geometry.Grid.AxisWalks.lookup x grid.vertical member).coordinate_eq]

end Axes

/-- Construct the subdivided, positively oriented ambient boundary.

The bottom and right walks run forward, while the top and left walks reverse the same retained axis subdivisions. -/
@[expose] def boundary (frame : AmbientFrame grid) :
    Geometry.Grid.Walks.Walk grid (point ambient.xLower ambient.yLower) (point ambient.xLower ambient.yLower) :=
  let axes := frame.axes
  let bottom := axes.horizontal ambient.yLower frame.yLower
  let right := axes.vertical ambient.xUpper frame.xUpper
  let top := axes.horizontal ambient.yUpper frame.yUpper
  let left := axes.vertical ambient.xLower frame.xLower
  bottom.append (right.append (top.reverse.append left.reverse))

/-- The subdivided framed boundary has the same raw winding as the ambient box. -/
theorem boundary_winding (frame : AmbientFrame grid) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding frame.boundary.path = Winding.Box.Basic.quadrupledBoxWinding
      polynomial ambient := by
  dsimp only [boundary]
  rw [Geometry.Grid.Winding.Walk.append_winding,
    Geometry.Grid.Winding.Walk.append_winding,
    Geometry.Grid.Winding.Walk.append_winding,
    Geometry.Grid.Winding.Walk.reverse_winding,
    Geometry.Grid.Winding.Walk.reverse_winding, Axes.horizontal_winding,
      Axes.horizontal_winding,
    Axes.vertical_winding,
      Axes.vertical_winding, Winding.Box.Basic.quadrupledBoxWinding_eq]
  have top : (Dense.Gaussian.Path.Box.Sides.horizontalEdge polynomial ambient.yUpper ambient.xUpper
    ambient.xLower).doubledWinding =
      -(Dense.Gaussian.Path.Box.Sides.horizontalEdge polynomial ambient.yUpper ambient.xLower
        ambient.xUpper).doubledWinding :=
    Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _
  have left : (Dense.Gaussian.Path.Box.Sides.verticalEdge polynomial ambient.xLower ambient.yUpper
    ambient.yLower).doubledWinding =
      -(Dense.Gaussian.Path.Box.Sides.verticalEdge polynomial ambient.xLower ambient.yLower
        ambient.yUpper).doubledWinding :=
    Dense.Rational.CauchyIndex.Basic.cauchyIndex2_reverse _ _ _ _
  rw [top, left]
  ring1

/-- The mesh's algebraic exterior is the actual subdivided enclosing walk,
for arbitrary oriented edge readings, not just for winding. -/
theorem boundary_value (frame : AmbientFrame grid) (values :
  EdgeValues) :
    values.walk frame.boundary = values.perimeter grid := by
  dsimp only [boundary]
  rw [values.walk_append, values.walk_append, values.walk_append,
    values.walk_reverse, values.walk_reverse, Axes.horizontal_value,
      Axes.horizontal_value,
    Axes.vertical_value,
      Axes.vertical_value]
  unfold EdgeValues.perimeter
  rw [frame.xSpan.entries_eq, frame.ySpan.entries_eq]
  dsimp only
  rw [frame.xSpan.lower_eq, frame.xSpan.upper_eq, frame.ySpan.lower_eq, frame.ySpan.upper_eq,
    Geometry.Grid.CellBoundary.sumValues_sub, Geometry.Grid.CellBoundary.sumValues_sub]
  ring1

/-- Locate an ambient point in a cell of a proper framed grid.

Membership of all four frame coordinates supplies the two axis searches and retains their original grid cell witness. -/
@[expose] def locate (frame : AmbientFrame grid) (proper : ambient.Proper) (point :
  Gaussian.Basic.Canonical) (inside : ambient.Contains point) :
    ClearGridCoverage.Located grid point :=
  ClearGridCoverage.locate grid point
    (FromStates.spanned_of_keys _ _ frame.xLower frame.xUpper proper.1 ⟨inside.1, inside.2.1⟩)
    (FromStates.spanned_of_keys _ _ frame.yLower frame.yUpper proper.2 inside.2.2)

end AmbientFrame

/-- Extend the grid by its ambient boundary and the retained state coordinates.

The new clear lines reuse the given frame clearances and existing state certificates. -/
@[expose] def withFrame (grid : ClearGrid polynomial ambient) (clearance :
  BoundaryClearance polynomial ambient)
    (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient)) : ClearGrid polynomial
      ambient :=
  Geometry.Grid.Extension.extend grid (frameVertical clearance ++ states.flatMap
    Geometry.Grid.FromStates.verticalSides)
    (frameHorizontal clearance ++ states.flatMap Geometry.Grid.FromStates.horizontalSides)

/-- Every coordinate of the original grid occurs in its framed extension. -/
theorem withFrame_inclusion (grid : ClearGrid polynomial ambient) (clearance :
  BoundaryClearance polynomial ambient)
    (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient)) :
      CoordinateInclusion grid (withFrame grid clearance
      states) :=
  Geometry.Grid.Extension.extend_inclusion grid _ _

/-- The framed extension contains every retained state coordinate. -/
theorem withFrame_states (grid : ClearGrid polynomial ambient) (clearance :
  BoundaryClearance polynomial ambient)
    (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient)) :
      CoordinateInclusion (Geometry.Grid.FromStates.ofStates states)
      (withFrame grid clearance states) where
  vertical := by
    intro coordinate member
    apply Geometry.Grid.Extension.extend_vertical grid
    rw [List.Map.map_append]
    exact List.mem_append_right _ ((Geometry.Grid.ClearGrid.build_vertical_coordinates _ _ _).1 member)
  horizontal := by
    intro coordinate member
    apply Geometry.Grid.Extension.extend_horizontal grid
    rw [List.Map.map_append]
    exact List.mem_append_right _ ((Geometry.Grid.ClearGrid.build_horizontal_coordinates _ _ _).1 member)

/-- The framed extension contains all four ambient boundary coordinates. -/
theorem withFrame_frame (grid : ClearGrid polynomial ambient) (clearance :
  BoundaryClearance polynomial ambient)
    (states : List (Geometry.Grid.FromStates.BranchState polynomial ambient)) :
      AmbientFrame (withFrame grid clearance
      states) where
  xLower := by
    apply Geometry.Grid.Extension.extend_vertical grid
    rw [List.Map.map_append]
    exact List.mem_append_left _ List.mem_cons_self
  xUpper := by
    apply Geometry.Grid.Extension.extend_vertical grid
    rw [List.Map.map_append]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)
  yLower := by
    apply Geometry.Grid.Extension.extend_horizontal grid
    rw [List.Map.map_append]
    exact List.mem_append_left _ List.mem_cons_self
  yUpper := by
    apply Geometry.Grid.Extension.extend_horizontal grid
    rw [List.Map.map_append]
    exact List.mem_append_left _ (List.mem_cons_of_mem _ List.mem_cons_self)

set_option genInjectivity false in
/-- Retain one enlarged grid and its exact semantic coverage.  Generated
axes may use different ordering witnesses or clearance margins. -/
structure FramedExtension (original : ClearGrid polynomial ambient) (states : List
  (Geometry.Grid.FromStates.BranchState polynomial ambient)) where
  /-- The extended clear grid on the original ambient box. -/ grid : ClearGrid polynomial ambient
  /-- Every original grid coordinate remains in the extension. -/ originalIncluded :
    CoordinateInclusion original grid
  /-- Every retained state coordinate belongs to the extended grid. -/ statesIncluded :
    CoordinateInclusion (FromStates.ofStates states) grid
  /-- The extended grid contains all ambient boundary coordinates. -/ frame :
    AmbientFrame grid

constructive_injectivity FramedExtension

namespace FramedExtension

/-- Build a framed extension together with its coordinate inclusions.

All certificates refer to the same computed grid, including the original grid, retained states and ambient boundary. -/
@[expose] def build (original : ClearGrid polynomial ambient)
    (clearance : BoundaryClearance polynomial ambient) (states : List
      (Geometry.Grid.FromStates.BranchState polynomial ambient)) :
    FramedExtension original states :=
  ⟨withFrame original clearance states, withFrame_inclusion original clearance
    states,
    withFrame_states original clearance states,
      withFrame_frame original clearance states⟩

end FramedExtension

end Grid

end

end Purelib.Polynomial.Geometry.Grid.FramedClearGrid
