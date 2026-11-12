module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Polynomial.Geometry.Grid.FromStates
public import Purelib.Polynomial.Elimination.Axis.Gap
public import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
public import Purelib.Riemann.Paths.ClearBoxPaths

import Purelib.Polynomial.Geometry.Grid.ClearGrid
public import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Polynomial.Geometry.Grid.Winding

/-!
# Coordinate-preserving extensions of a retained clear grid

Adding certified lines may subdivide old edges, but preserves every old
vertex and path.  The inclusion is semantic: an enlarged generated grid need
not equal the output of one particular sort or frame constructor.
-/

namespace Purelib.Polynomial.Geometry.Grid.Extension

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Riemann

public section

open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (VerticalLine HorizontalLine)
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid
  (build build_vertical_coordinates build_horizontal_coordinates)

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

/-- Coordinate inclusion between two clear grids for the same polynomial and ambient box.

Every coordinate of the first grid occurs in the second; line certificates and sorted list representations need not be
identical. -/
structure CoordinateInclusion (first second : ClearGrid polynomial ambient) : Prop where
  /-- Every original vertical-line coordinate occurs in the second grid. -/ vertical : ∀ coordinate, coordinate ∈
    first.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate →
    coordinate ∈ second.vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate
  /-- Every original horizontal-line coordinate occurs in the second grid. -/ horizontal : ∀ coordinate, coordinate ∈
    first.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate →
    coordinate ∈ second.horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate

namespace CoordinateInclusion

variable {first second third : ClearGrid polynomial ambient}

/-- A grid includes all of its own coordinates. -/
theorem refl (grid : ClearGrid polynomial ambient) : CoordinateInclusion grid
  grid :=
  ⟨fun _ member => member, fun _ member => member⟩

/-- Compose coordinate inclusions through an intermediate grid. -/
theorem trans (left : CoordinateInclusion first second) (right :
  CoordinateInclusion second third) :
    CoordinateInclusion first third :=
  ⟨fun coordinate member => right.vertical coordinate (left.vertical coordinate member),
    fun coordinate member => right.horizontal coordinate (left.horizontal coordinate member)⟩

/-- Coordinate inclusion preserves membership of a displayed grid vertex. -/
theorem vertex (included : CoordinateInclusion first second) {point : Gaussian.Basic.Canonical}
    (member : FromStates.ContainsVertex first point) : FromStates.ContainsVertex
      second point :=
  ⟨included.vertical _ member.1, included.horizontal _ member.2⟩

section
open Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion
/-- Coordinate inclusion preserves every vertex of a retained clear path. -/
theorem path (included : CoordinateInclusion first second) {pathAmbient : Box} :
    ∀ {start finish : Gaussian.Basic.Canonical} (path : ClearPath polynomial pathAmbient start
      finish),
      FromStates.ContainsPathVertices first path → FromStates.ContainsPathVertices
        second path
  | _, _, .nil _, member => included.vertex member
  | _, _, .cons _ tail, member => ⟨included.vertex member.1, included.path tail member.2⟩

/-- Coordinate inclusion preserves the vertices of all four retained paths of a closed boundary tour. -/
theorem tour {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {first second : ClearGrid curve.polynomial ambient} (included :
      CoordinateInclusion first second)
    (tour : Readings.PreparedBoundaryClosure.ClosedBoundaryDoublePath curve) (onGrid :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid.ContainsTourVertices first tour) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid.ContainsTourVertices second tour :=
  ⟨included.path _ onGrid.1, included.path _ onGrid.2.1,
    included.path _ onGrid.2.2.1, included.path _ onGrid.2.2.2⟩

end

/-- Re-split the actual old walk at the new lines.  Its original endpoints
and exact winding are preserved; equality of period integrals is separate. -/
@[expose] def resplit (included : CoordinateInclusion first second) {start finish :
  Gaussian.Basic.Canonical}
    (walk : Geometry.Grid.Walks.Walk first start finish) (finishMember : FromStates.ContainsVertex
      first finish) : Geometry.Grid.Walks.Walk second start finish :=
  Geometry.Grid.Walks.splitPath second walk.path (included.path walk.path (walk.vertices finishMember))

/-- Resplitting a retained walk in the larger grid preserves its exact raw winding. -/
theorem resplit_winding (included : CoordinateInclusion first second) {start finish :
  Gaussian.Basic.Canonical}
    (walk : Geometry.Grid.Walks.Walk first start finish) (finishMember : FromStates.ContainsVertex
      first finish) :
    Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding (included.resplit walk finishMember).path =
      Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding walk.path :=
  Geometry.Grid.Winding.splitPath_winding second walk.path _

end CoordinateInclusion

section

open Purelib.Polynomial.Elimination.Axis
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider (AxisClearances)

/-- Select an eliminant-safe point strictly inside the supplied proper rational box.

The two original central scans depend only on the retained eliminant and
the numerical box endpoints. Local ambient and clearance proofs do not
change the selected point, including at repeated source occurrences.
-/
def gapPoint {degreeBound : Nat}
    (elimination : AxisEliminationCertificate polynomial degreeBound)
    (inner : Box) (proper : inner.Proper) : Gaussian.Basic.Canonical :=
  Gaussian.Basic.point (Gap.verticalGapCoordinate elimination proper.1)
    (Gap.horizontalGapCoordinate elimination proper.2)

/-- The selected point retains both original nonzero eliminant readings and strict box bounds. -/
theorem gapPoint_spec {degreeBound : Nat}
    (elimination : AxisEliminationCertificate polynomial degreeBound)
    (inner : Box) (proper : inner.Proper) :
    elimination.vertical.eval (gapPoint elimination inner proper).re ≠ 0 ∧
      elimination.horizontal.eval (gapPoint elimination inner proper).im ≠ 0 ∧
      inner.StrictContains (gapPoint elimination inner proper) := by
  have vertical := Gap.verticalGapCoordinate_spec elimination proper.1
  have horizontal := Gap.horizontalGapCoordinate_spec elimination proper.2
  exact ⟨vertical.1, horizontal.1, vertical.2.1, vertical.2.2, horizontal.2.1, horizontal.2.2⟩

/-- Select two original certified clear-line payloads meeting strictly inside the supplied proper subbox.

Each eliminant-safe coordinate is computed once. The supplied original axis
provider consumes that literal coordinate and its exact nonzero certificate;
neither old source coordinate is asserted to be globally clear.
-/
@[expose] def gapLines {degreeBound : Nat}
    (elimination : AxisEliminationCertificate polynomial degreeBound)
    (clearances : AxisClearances elimination) (inner : Box) (proper : inner.Proper)
    (refines : inner.Refines ambient) : VerticalLine polynomial ambient × HorizontalLine polynomial ambient :=
  let point := gapPoint elimination inner proper
  have retained := gapPoint_spec elimination inner proper
  (⟨point.re, ⟨refines.1.trans retained.2.2.1.le, retained.2.2.2.1.le.trans refines.2.1⟩,
      clearances.vertical ambient point.re retained.1⟩,
    ⟨point.im, ⟨refines.2.2.1.trans retained.2.2.2.2.1.le, retained.2.2.2.2.2.le.trans refines.2.2.2⟩,
      clearances.horizontal ambient point.im retained.2.1⟩)

/-- The actual two cached line payloads intersect at the same original selected point. -/
theorem gapLines_point {degreeBound : Nat}
    (elimination : AxisEliminationCertificate polynomial degreeBound)
    (clearances : AxisClearances elimination) (inner : Box) (proper : inner.Proper)
    (refines : inner.Refines ambient) :
    Gaussian.Basic.point (gapLines elimination clearances inner proper refines).1.coordinate
      (gapLines elimination clearances inner proper refines).2.coordinate =
      gapPoint elimination inner proper := (rfl)

/-- The intersection of the actual two selected line payloads lies strictly inside the original supplied subbox.

Both coordinate inequalities are the retained central-search specifications
for those same two line payloads, including their original eliminants.
-/
theorem gapLines_strictContains {degreeBound : Nat}
    (elimination : AxisEliminationCertificate polynomial degreeBound)
    (clearances : AxisClearances elimination) (inner : Box) (proper : inner.Proper)
    (refines : inner.Refines ambient) :
    inner.StrictContains (Gaussian.Basic.point
      (gapLines elimination clearances inner proper refines).1.coordinate
      (gapLines elimination clearances inner proper refines).2.coordinate) := by
  have vertical := Gap.verticalGapCoordinate_spec elimination proper.1
  have horizontal := Gap.horizontalGapCoordinate_spec elimination proper.2
  exact ⟨vertical.2.1, vertical.2.2, horizontal.2.1, horizontal.2.2⟩

/-- The literal retained clear-box route uses only endpoint coordinates from the same grid.

Its whole factory equation reduces the original zero, one or two-edge
construction. The actual possible corner combines the retained target's
real coordinate with the source's imaginary coordinate. No containing-edge
claim is inferred from box containment, and the supplied route is unchanged.
-/
theorem route_vertices {box : Box} (grid : ClearGrid polynomial ambient)
    (clearance : Clearance.Box.Region.RegionClearance polynomial box)
    (source target : Gaussian.Basic.Canonical) (first : box.Contains source) (last : box.Contains target)
    (route : Paths.ClearBoxPaths.Route polynomial box source target)
    (route_eq : route = Paths.ClearBoxPaths.Route.build clearance source target first last)
    (sourceOn : FromStates.ContainsVertex grid source) (targetOn : FromStates.ContainsVertex grid target) :
    FromStates.ContainsPathVertices grid route.path := by
  cases route_eq
  unfold Paths.ClearBoxPaths.Route.build
  split
  · rename_i same
    cases same
    exact sourceOn
  · dsimp only
    split
    · change FromStates.ContainsVertex grid source ∧ FromStates.ContainsVertex grid target
      exact ⟨sourceOn, targetOn⟩
    · split
      · change FromStates.ContainsVertex grid source ∧ FromStates.ContainsVertex grid target
        exact ⟨sourceOn, targetOn⟩
      · change FromStates.ContainsVertex grid source ∧
          FromStates.ContainsVertex grid (Gaussian.Components.Basic.point target.re source.im) ∧
          FromStates.ContainsVertex grid target
        exact ⟨sourceOn, ⟨targetOn.1, sourceOn.2⟩, targetOn⟩

end

/-- Extend a clear grid with two displayed lists of certified lines.

Rebuild the ordered grid from the old and new lines while retaining the same polynomial and ambient box. -/
@[expose] def extend (grid : ClearGrid polynomial ambient) (vertical : List
  (Geometry.Grid.ClearGrid.VerticalLine polynomial ambient))
    (horizontal : List (Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient)) : ClearGrid
      polynomial ambient :=
  ClearGrid.build (grid.vertical ++ vertical) (grid.horizontal ++ horizontal)

/-- Extending a grid preserves every original coordinate. -/
theorem extend_inclusion (grid : ClearGrid polynomial ambient) (vertical : List
  (Geometry.Grid.ClearGrid.VerticalLine polynomial ambient))
    (horizontal : List (Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient)) :
      CoordinateInclusion grid (extend grid vertical horizontal) where
  vertical := by
    intro coordinate member
    apply (ClearGrid.build_vertical_coordinates _ _ _).2
    rw [List.Map.map_append]
    exact List.mem_append_left _ member
  horizontal := by
    intro coordinate member
    apply (ClearGrid.build_horizontal_coordinates _ _ _).2
    rw [List.Map.map_append]
    exact List.mem_append_left _ member

/-- Every supplied additional vertical coordinate occurs in the extended grid. -/
theorem extend_vertical (grid : ClearGrid polynomial ambient) (vertical : List
  (Geometry.Grid.ClearGrid.VerticalLine polynomial ambient))
    (horizontal : List (Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient)) {coordinate : Fraction.Rational}
    (member : coordinate ∈ vertical.map Geometry.Grid.ClearGrid.VerticalLine.coordinate) :
    coordinate ∈ (extend grid vertical horizontal).vertical.map VerticalLine.coordinate := by
  apply (ClearGrid.build_vertical_coordinates _ _ _).2
  rw [List.Map.map_append]
  exact List.mem_append_right _ member

/-- Every supplied additional horizontal coordinate occurs in the extended grid. -/
theorem extend_horizontal (grid : ClearGrid polynomial ambient) (vertical : List
  (Geometry.Grid.ClearGrid.VerticalLine polynomial ambient))
    (horizontal : List (Geometry.Grid.ClearGrid.HorizontalLine polynomial ambient)) {coordinate : Fraction.Rational}
    (member : coordinate ∈ horizontal.map Geometry.Grid.ClearGrid.HorizontalLine.coordinate) :
    coordinate ∈ (extend grid vertical horizontal).horizontal.map HorizontalLine.coordinate :=
      by
  apply (ClearGrid.build_horizontal_coordinates _ _ _).2
  rw [List.Map.map_append]
  exact List.mem_append_right _ member

end

end Purelib.Polynomial.Geometry.Grid.Extension
