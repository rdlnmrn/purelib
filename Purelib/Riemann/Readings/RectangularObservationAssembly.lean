module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Subtraction
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic

import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleIndices
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Polynomial.Geometry.Grid.AxisWalks
public import Purelib.Riemann.Readings.RectangularObservationOwners
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleSums
public import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Readings.RectangularClippedLocalBoundary
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Riemann

public section

/-! Assemble actual clipped cell boundaries using their retained model owners. -/
section

open Purelib.Data.Nat
open Purelib.Riemann.Normalization.InverseRootPolynomial (Box Gaussian)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Meshes.RectangularObservationMesh (ObservationPieces ObservationMesh)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts)
open _root_.Purelib.Geometry.Rectangle renaming AxisPartition -> Partition
open Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly (Sides)
open Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary (rectangleBoundary horizontalBoundary verticalBoundary)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)

variable {columns rows : Nat} {geometry : Geometry columns rows}

section

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

open Purelib.Algebra in
open Purelib.Geometry.Rectangle.Partition in
/-- The original owner-indexed box boundary equals the nested horizontal and vertical interval sum. -/
theorem localBoundary_eq_rows (horizontal
  vertical : List PreparedAxisPartitions.Interval)
    (pieces : ObservationPieces geometry (PreparedRectangleCuts.rectangles horizontal vertical))
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) (depth : Nat) :
    pieces.localBoundary values depth = FiniteSum.Fin.sumFin (fun column : Fin horizontal.length => FiniteSum.Fin.sumFin
      (fun row : Fin vertical.length =>
      PreparedBoxBoundary.rectangleBoundary (values (pieces.ownerAtRectangle horizontal vertical column row).column
        (pieces.ownerAtRectangle horizontal vertical column row).row) depth
        (PreparedRectangleCuts.intervalBox horizontal[column] vertical[row]))) := by
  rw [pieces.localBoundary_eq_indexed, PreparedRectangleSums.sumFin_rectangles]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  apply FiniteSum.Fin.sumFin_congr
  intro row
  exact congrArg (PreparedBoxBoundary.rectangleBoundary
    (values (pieces.owner (PreparedRectangleIndices.rectangleIndex horizontal vertical column row)).column
      (pieces.owner (PreparedRectangleIndices.rectangleIndex horizontal vertical column row)).row) depth)
    (PreparedRectangleIndices.rectangle_at horizontal vertical column row)

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationPieces

namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationPieces

/-- Transporting an observation-piece list along equality preserves its exact local boundary. -/
private theorem localBoundary_cast {first last : List Box} (equal : first = last)
    (pieces : ObservationPieces geometry first)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) (depth : Nat) :
    (equal ▸ pieces).localBoundary values depth = pieces.localBoundary values depth := by
  cases equal
  rfl

end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationPieces

end

section

variable {cuts : GridCuts geometry} {box : Box}

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

open Purelib.Algebra in
open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.Meshes in
/-- The original owner-indexed box boundary equals the nested horizontal and vertical interval sum. -/
theorem localBoundary_eq_rows (mesh :
  ObservationMesh cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) :
    mesh.pieces.localBoundary values mesh.depth =
      FiniteSum.Fin.sumFin (fun column : Fin mesh.partition.x.intervals.length => FiniteSum.Fin.sumFin (fun row : Fin
        mesh.partition.y.intervals.length =>
        PreparedBoxBoundary.rectangleBoundary (values (mesh.ownerAt column row).column (mesh.ownerAt column row).row)
          mesh.depth
          (PreparedRectangleCuts.intervalBox mesh.partition.x.intervals[column] mesh.partition.y.intervals[row]))) := by
  let pieces : ObservationPieces geometry
      (PreparedRectangleCuts.rectangles mesh.partition.x.intervals mesh.partition.y.intervals) :=
    mesh.partition.boxes_eq ▸ mesh.pieces
  have equal := RectangularObservationMesh.ObservationPieces.localBoundary_eq_rows mesh.partition.x.intervals
    mesh.partition.y.intervals pieces values mesh.depth
  dsimp only [pieces] at equal
  rw [Readings.RectangularObservationAssembly.ObservationPieces.localBoundary_cast] at equal
  exact equal

open Purelib.Geometry.Rectangle.Partition in
/-- Read the four original primitive boundary sides of one retained observation cell. -/
@[expose] def cellSides (mesh : ObservationMesh
  cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint)
    (column : Fin mesh.partition.x.intervals.length) (row : Fin mesh.partition.y.intervals.length) : Sides :=
  let owner := mesh.ownerAt column row
  let primitive := values owner.column owner.row
  let x := mesh.partition.x.intervals[column]
  let y := mesh.partition.y.intervals[row]
  ⟨horizontalBoundary primitive mesh.depth x.lower x.upper y.lower,
    PreparedBoxBoundary.verticalBoundary primitive mesh.depth y.lower y.upper x.upper,
    PreparedBoxBoundary.horizontalBoundary primitive mesh.depth x.lower x.upper y.upper,
    PreparedBoxBoundary.verticalBoundary primitive mesh.depth y.lower y.upper x.lower⟩

open Purelib.Algebra in
/-- The original local boundary equals the signed sum of retained cell sides. -/
theorem localBoundary_eq_sides (mesh :
  ObservationMesh cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) :
    mesh.pieces.localBoundary values mesh.depth =
      FiniteSum.Fin.sumFin (fun column : Fin mesh.partition.x.intervals.length => FiniteSum.Fin.sumFin (fun row : Fin
        mesh.partition.y.intervals.length =>
        (mesh.cellSides values column row).bottom + (mesh.cellSides values column row).right -
          (mesh.cellSides values column row).top - (mesh.cellSides values column row).left)) :=
  mesh.localBoundary_eq_rows values

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Polynomial in
open Purelib.Riemann.Normalization in
/-- An increasing walk between strictly ordered endpoints contains at least one edge. -/
private theorem walk_positive {intervals : List PreparedAxisPartitions.Interval} {first last :
  InverseRootPolynomial.Coordinate}
    (walk : Geometry.Grid.AxisWalks.IncreasingWalk intervals first last) (proper : first < last) : 0 < walk.edges.length
      := by
  cases walk with
  | nil => exact (lt_irrefl _ proper).elim
  | cons interval member tail => exact Nat.succ_pos _

open Purelib.Geometry.Rectangle.Partition in
open Purelib.Riemann.Normalization in
/-- A proper original axis partition contains at least one interval. -/
private theorem axis_positive {first last : InverseRootPolynomial.Coordinate} {points : List
  InverseRootPolynomial.Coordinate}
    (partition : Geometry.Rectangle.AxisPartition first last points) : 0 < partition.intervals.length := by
  rw [← partition.walk_edges]
  exact walk_positive partition.walk partition.proper

end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

/-- The retained horizontal interval count minus one for the boundary-grid index convention. -/
@[expose] def boundaryColumns (mesh :
  ObservationMesh cuts box) : Nat := mesh.partition.x.intervals.length - 1
/-- The retained vertical interval count minus one for the boundary-grid index convention. -/
@[expose] def boundaryRows (mesh :
  ObservationMesh cuts box) : Nat := mesh.partition.y.intervals.length - 1

/-- The boundary-column count plus one equals the original horizontal interval count.

Properness supplies a nonempty retained axis partition. Bounded natural
subtraction therefore recovers its exact original interval count. -/
theorem boundaryColumns_eq (mesh :
  ObservationMesh cuts box) : mesh.boundaryColumns + 1 = mesh.partition.x.intervals.length :=
  by
  change mesh.partition.x.intervals.length - 1 + 1 = mesh.partition.x.intervals.length
  rw [Nat.add_comm]
  exact Subtraction.add_sub_of_le
    (Nat.succ_le_of_lt (Readings.RectangularObservationAssembly.ObservationMesh.axis_positive mesh.partition.x))

/-- The boundary-row count plus one equals the original vertical interval count.

Properness supplies a nonempty retained axis partition. Bounded natural
subtraction therefore recovers its exact original interval count. -/
theorem boundaryRows_eq (mesh : ObservationMesh
  cuts box) : mesh.boundaryRows + 1 = mesh.partition.y.intervals.length :=
  by
  change mesh.partition.y.intervals.length - 1 + 1 = mesh.partition.y.intervals.length
  rw [Nat.add_comm]
  exact Subtraction.add_sub_of_le
    (Nat.succ_le_of_lt (Readings.RectangularObservationAssembly.ObservationMesh.axis_positive mesh.partition.y))

open Purelib.Integration.Polynomial.Rectangle in
/-- Read the original owner-indexed cell sides through the exact boundary-grid index casts. -/
@[expose] def sideGrid (mesh : ObservationMesh
  cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) :
    Boundary.Assembly.SideGrid mesh.boundaryColumns mesh.boundaryRows :=
  fun column row => mesh.cellSides values (Fin.cast mesh.boundaryColumns_eq column) (Fin.cast mesh.boundaryRows_eq row)

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh

open Purelib.Algebra in
/-- Transporting the finite index count along equality preserves the exact finite sum. -/
private theorem sumFin_cast {first last : Nat} (equal : first = last) (values : Fin first → Gaussian) :
    FiniteSum.Fin.sumFin values = FiniteSum.Fin.sumFin (fun index : Fin last => values (Fin.cast equal.symm index)) :=
      by
  cases equal
  rfl

end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh

namespace Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

open Purelib.Algebra in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Meshes in
/-- The original observation-piece boundary equals its exact retained side-grid boundary. -/
theorem localBoundary_eq_grid (mesh :
  ObservationMesh cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) :
    mesh.pieces.localBoundary values mesh.depth = Boundary.Assembly.localBoundary (mesh.sideGrid values) := by
  rw [mesh.localBoundary_eq_sides values]
  unfold Boundary.Assembly.localBoundary RectangularObservationMesh.ObservationMesh.sideGrid
  rw [Readings.RectangularObservationAssembly.ObservationMesh.sumFin_cast mesh.boundaryColumns_eq.symm]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  exact Readings.RectangularObservationAssembly.ObservationMesh.sumFin_cast mesh.boundaryRows_eq.symm _

open Purelib.Riemann.Periods in
/-- Read the four primitive corner values from one retained observation cell's original owner. -/
@[expose] def cornerGrid (mesh :
  ObservationMesh cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint)
    (column : Fin (mesh.boundaryColumns + 1)) (row : Fin (mesh.boundaryRows + 1)) : BilinearGridBoundary.CornerValues :=
  let xIndex := Fin.cast mesh.boundaryColumns_eq column
  let yIndex := Fin.cast mesh.boundaryRows_eq row
  let owner := mesh.ownerAt xIndex yIndex
  let primitive := values owner.column owner.row
  let x := mesh.partition.x.intervals[xIndex]
  let y := mesh.partition.y.intervals[yIndex]
  ⟨primitive ⟨x.lower, y.lower⟩, primitive ⟨x.upper, y.lower⟩,
    primitive ⟨x.lower, y.upper⟩, primitive ⟨x.upper, y.upper⟩⟩

end Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh

namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh

open Purelib.Data in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Periods in
set_option genInjectivity false in
/-- Cached original cell sides and corners with the exact exterior, seam and corner decomposition.

The cache equations retain the observation mesh, primitive values and original depth; the local total splits into three
separately stored contributions. -/
structure ClippedAssembly (mesh : ObservationMesh cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) where
  /-- The cached original rectangular grid of primitive side values. -/ sides : Data.Vector
    (Data.Vector Boundary.Assembly.Sides (mesh.boundaryRows + 1)) (mesh.boundaryColumns + 1)
  /-- Each cached side record equals the exact original owner-indexed grid readback. -/ sides_eq : ∀ column row, sides
    column row = mesh.sideGrid values column row
  /-- The cached original rectangular grid of primitive corner values. -/ corners : BilinearGridBoundary.Values
    mesh.boundaryColumns mesh.boundaryRows
  /-- Each cached corner record equals the exact original owner-indexed readback. -/ corners_eq : ∀ column row, corners
    column row = mesh.cornerGrid values column row
  /-- The cached original sum of local observation-box boundaries. -/ localTotal : Gaussian
  /-- The local-total cache equals the original observation-piece boundary. -/ localTotal_eq : localTotal =
    mesh.pieces.localBoundary values mesh.depth
  /-- The cached stitched exterior contribution. -/ exterior : Gaussian
  /-- The exterior cache equals the original outer side sum plus exact exterior joins. -/ exterior_eq : exterior =
    Boundary.Assembly.exteriorSides (fun column row => sides column row) +
    BilinearGridBoundary.exteriorJoins corners
  /-- The cached corrected internal-seam contribution. -/ seams : Gaussian
  /-- The seam cache equals the exact corrected seam sum of the retained side and corner grids. -/ seams_eq : seams =
    BilinearGridBoundary.correctedSeamSum (fun column row => sides column row) corners
  /-- The cached internal-corner contribution. -/ cornerTotal : Gaussian
  /-- The corner cache equals the exact retained grid-corner sum. -/ cornerTotal_eq : cornerTotal =
    BilinearGridBoundary.cornerSum corners
  /-- The original local total equals the separate exterior, seam and corner contributions. -/ decomposition :
    localTotal = exterior + seams + cornerTotal

constructive_injectivity ClippedAssembly

end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh

section

namespace Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

open Purelib.Algebra in
open Purelib.Data in
open Purelib.Integration.Polynomial.Rectangle in
open Purelib.Riemann.Periods in
/-- Cache the original observation side and corner grids and certify their exact boundary decomposition.

Pointwise vector readbacks identify the same retained owners, while the stitched-exterior identity supplies the separate
seam and corner terms. -/
@[expose] def build (mesh : ObservationMesh cuts box)
    (values : Fin (columns + 1) → Fin (rows + 1) → Gaussian → PrimitivePoint) : ClippedAssembly mesh values := by
  let sides := Vector.Basic.vectorOfFn fun column =>
    Vector.Basic.vectorOfFn fun row => mesh.sideGrid values column row
  have readback (column : Fin (mesh.boundaryColumns + 1)) (row : Fin (mesh.boundaryRows + 1)) :
      sides column row = mesh.sideGrid values column row := by
    dsimp only [sides]
    rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
  have original : Boundary.Assembly.localBoundary (fun column row => sides column row) =
      mesh.pieces.localBoundary values mesh.depth := by
    rw [mesh.localBoundary_eq_grid]
    unfold Boundary.Assembly.localBoundary
    apply FiniteSum.Fin.sumFin_congr
    intro column
    apply FiniteSum.Fin.sumFin_congr
    intro row
    dsimp only
    rw [readback]
  let corners := Vector.Basic.vectorOfFn fun column =>
    Vector.Basic.vectorOfFn fun row => mesh.cornerGrid values column row
  have cornerReadback (column : Fin (mesh.boundaryColumns + 1)) (row : Fin (mesh.boundaryRows + 1)) :
      corners column row = mesh.cornerGrid values column row := by
    dsimp only [corners]
    rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply]
  refine ⟨sides, readback, corners, cornerReadback,
    Boundary.Assembly.localBoundary (fun column row => sides column row), original,
    Boundary.Assembly.exteriorSides (fun column row => sides column row) + BilinearGridBoundary.exteriorJoins corners,
      rfl,
    BilinearGridBoundary.correctedSeamSum (fun column row => sides column row) corners, rfl,
    BilinearGridBoundary.cornerSum corners, rfl, ?_⟩
  have equal := BilinearGridBoundary.localBoundary_sub_stitchedExterior (fun column row => sides column row) corners
  calc
    _ = (Boundary.Assembly.localBoundary (fun column row => sides column row) -
        (Boundary.Assembly.exteriorSides (fun column row => sides column row) + BilinearGridBoundary.exteriorJoins
          corners)) +
        (Boundary.Assembly.exteriorSides (fun column row => sides column row) + BilinearGridBoundary.exteriorJoins
          corners) := by ring1
    _ = _ := by rw [equal]; ring1

end Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

end

end
end

end
