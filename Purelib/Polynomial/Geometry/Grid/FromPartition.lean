module

public import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Polynomial.Geometry.Grid.Extension
public import Purelib.Polynomial.Clearance.Box.Region
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Data.List.Attach
import Purelib.Data.List.Map
import Purelib.Data.List.Pairwise

/-! # Cleared axis walks on the original retained rectangular cut coordinates

Each original cached coordinate receives its line certificate from the
same closed-box clearance. The axes are not sorted or sampled again.
Existing grid walks preserve the actual adjacent intervals and orientation.
-/

public section

namespace Purelib.Polynomial.Geometry.Grid.ClearGrid

open Purelib
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial ClearSegment)
open Purelib.Riemann.Paths

variable {polynomial : GaussianPolynomial} {box : Box} {points : List Canonical}

/-- Certify the SAME retained rectangular coordinate axes from one original closed-box clearance.

Only the existing coordinate lists are traversed. Each line copies the
actual positive clearance bound; no root, query, Point or path preparation
is performed and no coordinate sort or geometric classification is repeated.
-/
def ofPartition (partition : CutPartition box points) (clearance : RegionClearance polynomial box) :
    Grid.ClearGrid polynomial box :=
  let vertical : List (VerticalLine polynomial box) := partition.x.coordinates.attach.map fun entry =>
    ⟨entry.val, partition.x.coordinate_bounds entry.property,
      ClearBoxPaths.vertical clearance entry.val (partition.x.coordinate_bounds entry.property)⟩
  let horizontal : List (HorizontalLine polynomial box) := partition.y.coordinates.attach.map fun entry =>
    ⟨entry.val, partition.y.coordinate_bounds entry.property,
      ClearBoxPaths.horizontal clearance entry.val (partition.y.coordinate_bounds entry.property)⟩
  have x : vertical.map VerticalLine.coordinate = partition.x.coordinates := by
    dsimp only [vertical]
    rewrite [Map.map_map]
    exact attach_map_subtype_val partition.x.coordinates
  have y : horizontal.map HorizontalLine.coordinate = partition.y.coordinates := by
    dsimp only [horizontal]
    rewrite [Map.map_map]
    exact attach_map_subtype_val partition.y.coordinates
  ⟨vertical, horizontal,
    Pairwise.pairwise_map.mp (Eq.mp (congrArg (fun coordinates : List Data.Rat.Fraction.Rational =>
      coordinates.Pairwise (fun first last => first < last)) x.symm) partition.x.ordered),
    Pairwise.pairwise_map.mp (Eq.mp (congrArg (fun coordinates : List Data.Rat.Fraction.Rational =>
      coordinates.Pairwise (fun first last => first < last)) y.symm) partition.y.ordered)⟩

/-- The new vertical certificates retain exactly the original cached horizontal coordinates and order. -/
theorem ofPartition_vertical (partition : CutPartition box points) (clearance : RegionClearance polynomial box) :
    (ofPartition partition clearance).vertical.map VerticalLine.coordinate = partition.x.coordinates := by
  unfold ofPartition
  rewrite [Map.map_map]
  exact attach_map_subtype_val partition.x.coordinates

/-- The new horizontal certificates retain exactly the original cached vertical coordinates and order. -/
theorem ofPartition_horizontal (partition : CutPartition box points) (clearance : RegionClearance polynomial box) :
    (ofPartition partition clearance).horizontal.map HorizontalLine.coordinate = partition.y.coordinates := by
  unfold ofPartition
  rewrite [Map.map_map]
  exact attach_map_subtype_val partition.y.coordinates

/-- Both retained endpoints of each partition axis occur in the SAME cleared coordinate grid. -/
theorem ofPartition_bounds (partition : CutPartition box points) (clearance : RegionClearance polynomial box) :
    box.xLower ∈ (ofPartition partition clearance).vertical.map VerticalLine.coordinate ∧
    box.xUpper ∈ (ofPartition partition clearance).vertical.map VerticalLine.coordinate ∧
    box.yLower ∈ (ofPartition partition clearance).horizontal.map HorizontalLine.coordinate ∧
    box.yUpper ∈ (ofPartition partition clearance).horizontal.map HorizontalLine.coordinate := by
  rewrite [ofPartition_vertical, ofPartition_horizontal]
  exact ⟨partition.x.lower_mem, partition.x.upper_mem, partition.y.lower_mem, partition.y.upper_mem⟩

/-- A whole retained fine-grid factory transports those four actual axis endpoint occurrences. -/
theorem ofPartition_bounds_of_eq (partition : CutPartition box points) (clearance : RegionClearance polynomial box)
    {fine : Grid.ClearGrid polynomial box} (factory : fine = ofPartition partition clearance) :
    box.xLower ∈ fine.vertical.map VerticalLine.coordinate ∧ box.xUpper ∈ fine.vertical.map VerticalLine.coordinate ∧
    box.yLower ∈ fine.horizontal.map HorizontalLine.coordinate ∧
      box.yUpper ∈ fine.horizontal.map HorizontalLine.coordinate :=
  Eq.mpr (congrArg (fun value : Grid.ClearGrid polynomial box =>
    box.xLower ∈ value.vertical.map VerticalLine.coordinate ∧ box.xUpper ∈ value.vertical.map VerticalLine.coordinate ∧
    box.yLower ∈ value.horizontal.map HorizontalLine.coordinate ∧
      box.yUpper ∈ value.horizontal.map HorizontalLine.coordinate)
    factory) (ofPartition_bounds partition clearance)

/-- A retained requested point inside this SAME box is an actual vertex of its cleared cut grid. -/
theorem ofPartition_contains (partition : CutPartition box points) (clearance : RegionClearance polynomial box)
    (point : Canonical) (member : point ∈ points) (inside : box.Contains point) :
    FromStates.ContainsVertex (ofPartition partition clearance) point := by
  constructor
  · rewrite [ofPartition_vertical]
    exact partition.x.cut_mem (Map.mem_map.mpr ⟨point, member, rfl⟩) ⟨inside.1, inside.2.1⟩
  · rewrite [ofPartition_horizontal]
    exact partition.y.cut_mem (Map.mem_map.mpr ⟨point, member, rfl⟩) inside.2.2

/-- Actual cleared-grid vertex incidence gives both original partition coordinate memberships. -/
theorem ofPartition_coordinates (partition : CutPartition box points) (clearance : RegionClearance polynomial box)
    {point : Canonical} (member : FromStates.ContainsVertex (ofPartition partition clearance) point) :
    point.re ∈ partition.x.coordinates ∧ point.im ∈ partition.y.coordinates :=
  ⟨Eq.mp (congrArg (fun coordinates : List Data.Rat.Fraction.Rational => point.re ∈ coordinates)
    (ofPartition_vertical partition clearance)) member.1,
   Eq.mp (congrArg (fun coordinates : List Data.Rat.Fraction.Rational => point.im ∈ coordinates)
    (ofPartition_horizontal partition clearance)) member.2⟩

/-- A retained whole grid-factory equation transports vertex incidence without constructing that grid again. -/
theorem ofPartition_contains_of_eq (partition : CutPartition box points)
    (clearance : RegionClearance polynomial box) {grid : Grid.ClearGrid polynomial box}
    (factory : grid = ofPartition partition clearance) (point : Canonical) (member : point ∈ points)
    (inside : box.Contains point) : FromStates.ContainsVertex grid point :=
  Eq.mp (congrArg (fun grid : Grid.ClearGrid polynomial box => FromStates.ContainsVertex grid point) factory.symm)
    (ofPartition_contains partition clearance point member inside)

/-- The same whole factory law reads coordinate membership from the actual retained grid. -/
theorem ofPartition_coordinates_of_eq (partition : CutPartition box points)
    (clearance : RegionClearance polynomial box) {grid : Grid.ClearGrid polynomial box}
    (factory : grid = ofPartition partition clearance) {point : Canonical}
    (member : FromStates.ContainsVertex grid point) :
    point.re ∈ partition.x.coordinates ∧ point.im ∈ partition.y.coordinates :=
  ofPartition_coordinates partition clearance (Eq.mp
    (congrArg (fun grid : Grid.ClearGrid polynomial box => FromStates.ContainsVertex grid point) factory) member)

/-- Equal original coordinate lists give equal adjacent intervals with their unchanged ordered payloads. -/
private theorem adjacent_eq {first last : List Data.Rat.Fraction.Rational} (equal : first = last)
    (firstOrdered : first.Pairwise (fun left right => left < right))
    (lastOrdered : last.Pairwise (fun left right => left < right)) :
    Interval.adjacent (key := id) first firstOrdered = Interval.adjacent last lastOrdered := by
  cases equal
  rfl

/-- The SAME original horizontal adjacent-interval bank is retained by the certified vertical-line payloads. -/
theorem ofPartition_xIntervals (partition : CutPartition box points) (clearance : RegionClearance polynomial box) :
    (ofPartition partition clearance).xIntervals.map Interval.coordinates = partition.x.intervals := by
  let grid := ofPartition partition clearance
  have mapped : (grid.vertical.map VerticalLine.coordinate).Pairwise (fun first last => first < last) :=
    Pairwise.pairwise_map.mpr grid.vertical_ordered
  exact (Interval.coordinates_adjacent grid.vertical grid.vertical_ordered mapped).trans
    ((adjacent_eq (ofPartition_vertical partition clearance) mapped partition.x.ordered).trans
      partition.x.intervals_eq.symm)

/-- The SAME original vertical adjacent-interval bank is retained by the certified horizontal-line payloads. -/
theorem ofPartition_yIntervals (partition : CutPartition box points) (clearance : RegionClearance polynomial box) :
    (ofPartition partition clearance).yIntervals.map Interval.coordinates = partition.y.intervals := by
  let grid := ofPartition partition clearance
  have mapped : (grid.horizontal.map HorizontalLine.coordinate).Pairwise (fun first last => first < last) :=
    Pairwise.pairwise_map.mpr grid.horizontal_ordered
  exact (Interval.coordinates_adjacent grid.horizontal grid.horizontal_ordered mapped).trans
    ((adjacent_eq (ofPartition_horizontal partition clearance) mapped partition.y.ordered).trans
      partition.y.intervals_eq.symm)

/-- Read actual horizontal adjacency through the retained whole grid factory. -/
theorem ofPartition_xInterval_of_eq (partition : CutPartition box points)
    (clearance : RegionClearance polynomial box) {grid : Grid.ClearGrid polynomial box}
    (factory : grid = ofPartition partition clearance)
    {interval : Interval (VerticalLine.coordinate (polynomial := polynomial) (ambient := box))}
    (member : interval ∈ grid.xIntervals) : interval.coordinates ∈ partition.x.intervals :=
  Eq.mp (congrArg (fun intervals => interval.coordinates ∈ intervals)
    ((congrArg (fun grid : Grid.ClearGrid polynomial box => grid.xIntervals.map Interval.coordinates) factory).trans
      (ofPartition_xIntervals partition clearance))) (Map.mem_map_of_mem member)

/-- Read actual vertical adjacency through the retained whole grid factory. -/
theorem ofPartition_yInterval_of_eq (partition : CutPartition box points)
    (clearance : RegionClearance polynomial box) {grid : Grid.ClearGrid polynomial box}
    (factory : grid = ofPartition partition clearance)
    {interval : Interval (HorizontalLine.coordinate (polynomial := polynomial) (ambient := box))}
    (member : interval ∈ grid.yIntervals) : interval.coordinates ∈ partition.y.intervals :=
  Eq.mp (congrArg (fun intervals => interval.coordinates ∈ intervals)
    ((congrArg (fun grid : Grid.ClearGrid polynomial box => grid.yIntervals.map Interval.coordinates) factory).trans
      (ofPartition_yIntervals partition clearance))) (Map.mem_map_of_mem member)

namespace Cell

variable {ambient : Box} (cell : Cell polynomial ambient)

/-- The actual same-cell cut partition includes both original restricted side coordinates on each axis.

The retained partition endpoints supply the inclusion. New interior lines
are certified only on this SAME clear cell ambient; no ambient extension
through other branch cells is inferred.
-/
theorem grid_inclusion (partition : CutPartition cell.box points)
    (clearance : RegionClearance polynomial cell.box) :
    Extension.CoordinateInclusion cell.grid (ofPartition partition clearance) where
  vertical := by
    intro coordinate member
    have actual := Eq.mp (congrArg (fun values : List Data.Rat.Fraction.Rational => coordinate ∈ values)
      cell.grid_vertical_coordinates) member
    rewrite [ofPartition_vertical]
    rcases Membership.mem_cons.mp actual with lower | upper
    · exact Eq.mpr (congrArg (fun value => value ∈ partition.x.coordinates) lower) partition.x.lower_mem
    · exact Eq.mpr (congrArg (fun value => value ∈ partition.x.coordinates)
        (Membership.mem_singleton.mp upper)) partition.x.upper_mem
  horizontal := by
    intro coordinate member
    have actual := Eq.mp (congrArg (fun values : List Data.Rat.Fraction.Rational => coordinate ∈ values)
      cell.grid_horizontal_coordinates) member
    rewrite [ofPartition_horizontal]
    rcases Membership.mem_cons.mp actual with lower | upper
    · exact Eq.mpr (congrArg (fun value => value ∈ partition.y.coordinates) lower) partition.y.lower_mem
    · exact Eq.mpr (congrArg (fun value => value ∈ partition.y.coordinates)
        (Membership.mem_singleton.mp upper)) partition.y.upper_mem

/-- A complete cached fine-grid factory retains that SAME derived coordinate inclusion without executing the factory. -/
theorem grid_inclusion_of_eq (partition : CutPartition cell.box points)
    (clearance : RegionClearance polynomial cell.box) {fine : Grid.ClearGrid polynomial cell.box}
    (factory : fine = ofPartition partition clearance) : Extension.CoordinateInclusion cell.grid fine :=
  Eq.mpr (congrArg (fun value : Grid.ClearGrid polynomial cell.box =>
    Extension.CoordinateInclusion cell.grid value) factory) (cell.grid_inclusion partition clearance)

end Cell

end Purelib.Polynomial.Geometry.Grid.ClearGrid

end
