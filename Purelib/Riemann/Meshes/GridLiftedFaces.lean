module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Content
public import Purelib.Integration.Energy.AffineTriangle
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Roots.Walk

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
public import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Geometry.Grid.FromStates

public section

/-!
# Two actual lifted quadrilaterals above each regular grid face

The four corner sheets are calculated along the shared edge bank and cached.
Actual zero-winding return closes the fourth side.  Global vertex indices
retain those sheets, and the two-triangle subdivision has the same literal
indexed perimeter as the root-lifted grid walk.
-/

open
  Purelib.Riemann.RootContinuation

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

open Purelib.Topology.Polygon.Stokes (OrientedEdge)

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient} {frames : RootFrames grid}

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Index the original directed grid edge at its source sheet and exactly transported target sheet.

The source index retains the supplied original sheet. The target index uses the same cached root-edge transport and the
original endpoint membership witnesses. -/
@[expose] def indexedEdge (edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
  SquareRoot.Grid.LiftedVertices.VertexBank grid) {start finish : Basic.Canonical}
    (edge : Geometry.Grid.Walks.Edge grid start finish) (sheet : Fin 2) : OrientedEdge vertices.count :=
  ⟨vertices.index start edge.vertices.1 sheet,
    vertices.index finish edge.vertices.2 ((edges.edge edge).forward.target sheet)⟩

open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
open Purelib.RootIsolation in
/-- Reversing the original grid edge reverses its indexed lifted edge after transporting the source sheet.

The retained edge bijection carries both endpoint owners. Its backward-forward equation identifies the starting sheet
after the original reversed transport. -/
theorem indexedEdge_reverse (edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
  SquareRoot.Grid.LiftedVertices.VertexBank grid) {start finish : Basic.Canonical}
    (edge : Geometry.Grid.Walks.Edge grid start finish) (first : OwnerLoopMonodromy.WindingOneLoop polynomial start)
    (last : OwnerLoopMonodromy.WindingOneLoop polynomial finish) (sheet : Fin 2) :
    edges.indexedEdge vertices (.reverse edge) ((edges.edge edge).forward.target sheet) =
      (edges.indexedEdge vertices edge sheet).reverse :=
  congrArg (fun finalSheet => (⟨vertices.index finish edge.vertices.2 ((edges.edge edge).forward.target sheet),
      vertices.index start edge.vertices.1 finalSheet⟩ : OrientedEdge vertices.count))
    (((edges.edge edge).bijection first last).backward_forward sheet)

open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.RootIsolation
/-- List the indexed lifts of the original grid walk in order, passing each transported sheet to the exact tail.

Each original walk edge contributes its exact indexed lift, and its transported sheet is passed to the same retained
tail. The original edge order and endpoint witnesses remain unchanged. -/
@[expose] def indexedEdges (edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
  SquareRoot.Grid.LiftedVertices.VertexBank grid) :
    {start finish : Basic.Canonical} → Geometry.Grid.Walks.Walk grid start finish → Fin 2 → List (OrientedEdge
      vertices.count)
  | _, _, .nil _, _ => []
  | _, _, .cons edge tail, sheet =>
      edges.indexedEdge vertices edge sheet :: edges.indexedEdges vertices tail ((edges.edge edge).forward.target sheet)

/-- The indexed original lifted walk contains exactly one edge per original walk edge.

The empty walk contributes no indices. Each retained head edge contributes one original indexed lift and preserves the
exact tail edge count. -/
theorem indexedEdges_length (edges : Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames) (vertices :
  SquareRoot.Grid.LiftedVertices.VertexBank grid) :
    {start finish : Basic.Canonical} → (walk : Geometry.Grid.Walks.Walk grid start finish) → (sheet : Fin 2) →
      (edges.indexedEdges vertices walk sheet).length = walk.edgeCount
  | _, _, .nil _, _ => rfl
  | _, _, .cons edge tail, sheet => congrArg Nat.succ (edges.indexedEdges_length vertices tail ((edges.edge
    edge).forward.target sheet))

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

namespace Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : ClearGrid polynomial
  ambient}

section
open Purelib.Data.Gaussian
open Purelib.Polynomial
/-- The original cell's bottom grid edge, directed from lower left to lower right.

The retained horizontal interval and lower vertical endpoint determine this directed edge. Their original
grid-membership witnesses certify both original lower corners. -/
@[expose] def bottomSide (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) :
    Geometry.Grid.Walks.Edge grid cell.box.anchor (Components.Basic.point cell.box.xUpper cell.box.yLower) :=
  let intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem cell member
  .horizontal cell.horizontal intervals.1 cell.vertical.lower (Geometry.Grid.ClearGrid.Interval.endpoints_mem _
    grid.horizontal_ordered intervals.2).1

/-- The original cell's right grid edge, directed from lower right to upper right.

The retained vertical interval and upper horizontal endpoint determine this directed edge. Their original
grid-membership witnesses certify the original right-hand corners. -/
@[expose] def rightSide (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) :
    Geometry.Grid.Walks.Edge grid (Components.Basic.point cell.box.xUpper cell.box.yLower) (Components.Basic.point
      cell.box.xUpper cell.box.yUpper) :=
  let intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem cell member
  .vertical cell.vertical intervals.2 cell.horizontal.upper (Geometry.Grid.ClearGrid.Interval.endpoints_mem _
    grid.vertical_ordered intervals.1).2

/-- The original cell's top grid edge, directed from upper right to upper left.

The original horizontal edge at the upper vertical endpoint is reversed. Its retained interval and endpoint witnesses
preserve the two upper corners and their orientation. -/
@[expose] def topSide (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) :
    Geometry.Grid.Walks.Edge grid (Components.Basic.point cell.box.xUpper cell.box.yUpper) (Components.Basic.point
      cell.box.xLower cell.box.yUpper) :=
  let intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem cell member
  .reverse (.horizontal cell.horizontal intervals.1 cell.vertical.upper (Geometry.Grid.ClearGrid.Interval.endpoints_mem
    _ grid.horizontal_ordered intervals.2).2)

/-- The original cell's left grid edge, directed from upper left to lower left.

The original vertical edge at the lower horizontal endpoint is reversed. Its retained interval and endpoint witnesses
preserve the two left-hand corners and their orientation. -/
@[expose] def leftSide (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) :
    Geometry.Grid.Walks.Edge grid (Components.Basic.point cell.box.xLower cell.box.yUpper) cell.box.anchor :=
  let intervals := Geometry.Grid.CellBoundary.Cell.intervals_mem cell member
  .reverse (.vertical cell.vertical intervals.2 cell.horizontal.lower (Geometry.Grid.ClearGrid.Interval.endpoints_mem _
    grid.vertical_ordered intervals.1).1)

end

open Purelib.Polynomial in
/-- The original cell boundary walk is exactly its bottom, right, top and left sides in order.

The same retained cell supplies all four directed sides. Their original endpoint witnesses compose in
bottom-right-top-left order and return to its exact anchor. -/
theorem boundaryWalk_sides (cell : Geometry.Grid.ClearGrid.Cell polynomial ambient) (member : cell ∈ grid.cells) :
    Geometry.Grid.CellBoundary.Cell.boundaryWalk cell member = .cons (cell.bottomSide member) (.cons (cell.rightSide
      member)
      (.cons (cell.topSide member) (.cons (cell.leftSide member) (.nil cell.box.anchor)))) := rfl

end Purelib.Polynomial.Geometry.Grid.ClearGrid.Cell

namespace Purelib.Riemann.Meshes.GridLiftedFaces

open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell Interval)
open Purelib.Polynomial.Geometry.Grid.Walks (Edge Walk)
open _root_.Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)

namespace BranchCellBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A lifted regular face retaining exact sheet transport and its indexed quadrilateral.

The four corners use the original vertex bank. Three transported corner sheets and the closing equation retain the
original root-edge bank's complete boundary transport. -/
structure LiftedFace (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (edges :
  RootEdgeBank frames)
    (face : RegularFace bank) (sheet : Fin 2) where
  /-- The retained transported sheet at the original lower-right corner. -/ lowerRight : Fin 2
  /-- The retained transported sheet at the original upper-right corner. -/ upperRight : Fin 2
  /-- The retained transported sheet at the original upper-left corner. -/ upperLeft : Fin 2
  /-- The lower-right sheet equals original bottom-side transport. -/ bottom_eq : lowerRight = (edges.edge
    (face.cell.bottomSide face.member)).forward.target sheet
  /-- The upper-right sheet equals original right-side transport. -/ right_eq : upperRight = (edges.edge
    (face.cell.rightSide face.member)).forward.target lowerRight
  /-- The upper-left sheet equals original top-side transport. -/ top_eq : upperLeft = (edges.edge (face.cell.topSide
    face.member)).forward.target upperRight
  /-- Original left-side transport returns to the exact starting sheet. -/ closed : (edges.edge (face.cell.leftSide
    face.member)).forward.target upperLeft = sheet
  /-- The retained quadrilateral over the original vertex-bank indices. -/ quad :
    Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral vertices.count
  /-- The first corner is the exact original anchor index on the starting sheet. -/ first_eq : quad.first =
    vertices.index face.cell.box.anchor (Geometry.Grid.ClearGrid.Cell.anchor_mem face.cell face.member) sheet
  /-- The second corner is the original lower-right index on its retained sheet. -/ second_eq : quad.second =
    vertices.index (Components.Basic.point face.cell.box.xUpper face.cell.box.yLower)
    (face.cell.bottomSide face.member).vertices.2 lowerRight
  /-- The third corner is the original upper-right index on its retained sheet. -/ third_eq : quad.third =
    vertices.index (Components.Basic.point face.cell.box.xUpper face.cell.box.yUpper)
    (face.cell.rightSide face.member).vertices.2 upperRight
  /-- The fourth corner is the original upper-left index on its retained sheet. -/ fourth_eq : quad.fourth =
    vertices.index (Components.Basic.point face.cell.box.xLower face.cell.box.yUpper)
    (face.cell.topSide face.member).vertices.2 upperLeft

constructive_injectivity LiftedFace

namespace LiftedFace

variable {vertices : VertexBank bank.grid} {edges :
  RootEdgeBank frames} {face : RegularFace bank} {sheet : Fin 2}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Transport along an original grid edge is injective on its retained two-element sheet index. -/
private theorem edge_injective {start finish : Basic.Canonical} (edges :
  RootEdgeBank
  frames)
    (edge : Geometry.Grid.Walks.Edge bank.grid start finish) : Function.Injective (edges.edge edge).forward.target :=
  ((edges.edge edge).bijection (Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt bank start
    edge.vertices.1).toLoop
    (Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt bank finish
      edge.vertices.2).toLoop).forward_injective

open Purelib.Curves.Hyperelliptic in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Lift the original regular face from the supplied starting sheet through its exact root-edge bank.

The corner sheets are computed successively along the original sides; regular-face transport closes the boundary, and
the quadrilateral retains the exact vertex-bank indices. -/
@[expose] def build (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (edges :
  RootEdgeBank frames) (face : RegularFace bank) (sheet : Fin 2) :
    LiftedFace vertices edges face sheet :=
  let lowerRight := (edges.edge (face.cell.bottomSide face.member)).forward.target sheet
  let upperRight := (edges.edge (face.cell.rightSide face.member)).forward.target lowerRight
  let upperLeft := (edges.edge (face.cell.topSide face.member)).forward.target upperRight
  { lowerRight := lowerRight
    upperRight := upperRight
    upperLeft := upperLeft
    bottom_eq := rfl
    right_eq := rfl
    top_eq := rfl
    closed :=
      RootContinuation.GridRootWalks.BranchCellBank.RegularFace.sharedTransport_identity
      face edges sheet
    quad := ⟨vertices.index face.cell.box.anchor (Geometry.Grid.ClearGrid.Cell.anchor_mem face.cell face.member) sheet,
      vertices.index _ (face.cell.bottomSide face.member).vertices.2 lowerRight,
      vertices.index _ (face.cell.rightSide face.member).vertices.2 upperRight,
      vertices.index _ (face.cell.topSide face.member).vertices.2 upperLeft⟩
    first_eq := rfl
    second_eq := rfl
    third_eq := rfl
    fourth_eq := rfl }

open Purelib.Data.Gaussian in
/-- The retained lifted quadrilateral has exactly the four coordinates of its original regular cell. -/
theorem coordinates (lifted : LiftedFace vertices edges face sheet) :
    vertices.coordinate lifted.quad.first = face.cell.box.anchor ∧
      vertices.coordinate lifted.quad.second = Components.Basic.point face.cell.box.xUpper face.cell.box.yLower ∧
      vertices.coordinate lifted.quad.third = Components.Basic.point face.cell.box.xUpper face.cell.box.yUpper ∧
      vertices.coordinate lifted.quad.fourth = Components.Basic.point face.cell.box.xLower face.cell.box.yUpper := by
  rw [lifted.first_eq, lifted.second_eq, lifted.third_eq, lifted.fourth_eq]
  exact ⟨vertices.coordinate_index _ _ _, vertices.coordinate_index _ _ _,
    vertices.coordinate_index _ _ _, vertices.coordinate_index _ _ _⟩

/-- The retained quadrilateral's corner sheet readbacks equal the original starting and transported sheets. -/
theorem corner_sheets (lifted : LiftedFace vertices edges face sheet) :
    vertices.sheet lifted.quad.first = sheet ∧ vertices.sheet lifted.quad.second = lifted.lowerRight ∧
      vertices.sheet lifted.quad.third = lifted.upperRight ∧ vertices.sheet lifted.quad.fourth = lifted.upperLeft := by
  rw [lifted.first_eq, lifted.second_eq, lifted.third_eq, lifted.fourth_eq]
  exact ⟨vertices.sheet_index _ _ _, vertices.sheet_index _ _ _, vertices.sheet_index _ _ _, vertices.sheet_index _ _ _⟩

/-- The two original sheet lifts of a regular face have distinct indices at every corresponding corner. -/
theorem opposite_corners (zero : LiftedFace vertices edges face 0) (one : LiftedFace vertices edges face 1) :
    zero.quad.first ≠ one.quad.first ∧ zero.quad.second ≠ one.quad.second ∧
      zero.quad.third ≠ one.quad.third ∧ zero.quad.fourth ≠ one.quad.fourth := by
  have different : (0 : Fin 2) ≠ 1 := by decide
  have lowerRight : zero.lowerRight ≠ one.lowerRight := by
    intro same
    rw [zero.bottom_eq, one.bottom_eq] at same
    exact different (edge_injective edges _ same)
  have upperRight : zero.upperRight ≠ one.upperRight := by
    intro same
    rw [zero.right_eq, one.right_eq] at same
    exact lowerRight (edge_injective edges _ same)
  have upperLeft : zero.upperLeft ≠ one.upperLeft := by
    intro same
    rw [zero.top_eq, one.top_eq] at same
    exact upperRight (edge_injective edges _ same)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro same
    exact different (zero.corner_sheets.1.symm.trans ((congrArg vertices.sheet same).trans one.corner_sheets.1))
  · intro same
    exact lowerRight (zero.corner_sheets.2.1.symm.trans ((congrArg vertices.sheet same).trans one.corner_sheets.2.1))
  · intro same
    exact upperRight (zero.corner_sheets.2.2.1.symm.trans ((congrArg vertices.sheet same).trans
      one.corner_sheets.2.2.1))
  · intro same
    exact upperLeft (zero.corner_sheets.2.2.2.symm.trans ((congrArg vertices.sheet same).trans one.corner_sheets.2.2.2))

section
open Purelib.Geometry.Rational
open Purelib.Geometry.Rectangle.Partition
open Purelib.Integration.Energy
/-- The first retained lifted triangle has coordinate area equal to half the original cell content. -/
theorem firstTriangle_area (lifted : LiftedFace vertices edges face sheet) :
    AffineTriangle.coordinateTriangleArea (vertices.coordinate lifted.quad.first)
      (vertices.coordinate lifted.quad.second) (vertices.coordinate lifted.quad.third) =
      Box.Content.boxContent face.cell.box / 2 := by
  rw [lifted.coordinates.1, lifted.coordinates.2.1, lifted.coordinates.2.2.1]
  exact PreparedBoxTriangulation.lowerTriangle_area face.cell.box

/-- The second retained lifted triangle has coordinate area equal to half the original cell content. -/
theorem secondTriangle_area (lifted : LiftedFace vertices edges face sheet) :
    AffineTriangle.coordinateTriangleArea (vertices.coordinate lifted.quad.first)
      (vertices.coordinate lifted.quad.third) (vertices.coordinate lifted.quad.fourth) =
      Box.Content.boxContent face.cell.box / 2 := by
  rw [lifted.coordinates.1, lifted.coordinates.2.2.1, lifted.coordinates.2.2.2]
  exact PreparedBoxTriangulation.upperTriangle_area face.cell.box

end

section
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Integration.Energy
/-- The first retained lifted triangle has strictly positive coordinate area. -/
theorem firstTriangle_positive (lifted : LiftedFace vertices edges face sheet) :
    0 < AffineTriangle.coordinateTriangleArea (vertices.coordinate lifted.quad.first)
      (vertices.coordinate lifted.quad.second) (vertices.coordinate lifted.quad.third) := by
  rw [lifted.firstTriangle_area]
  exact Fraction.Order.Field.div_pos_direct (Box.Content.boxContent_pos_of_proper face.cell.box_proper) (by decide)

/-- The second retained lifted triangle has strictly positive coordinate area. -/
theorem secondTriangle_positive (lifted : LiftedFace vertices edges face sheet) :
    0 < AffineTriangle.coordinateTriangleArea (vertices.coordinate lifted.quad.first)
      (vertices.coordinate lifted.quad.third) (vertices.coordinate lifted.quad.fourth) := by
  rw [lifted.secondTriangle_area]
  exact Fraction.Order.Field.div_pos_direct (Box.Content.boxContent_pos_of_proper face.cell.box_proper) (by decide)

end

open Purelib in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The retained quadrilateral boundary is exactly the indexed lift of the original face boundary walk. -/
theorem boundary_eq (lifted : LiftedFace vertices edges face sheet) :
    lifted.quad.boundary = edges.indexedEdges vertices face.boundary sheet := by
  have closed := lifted.closed
  rw [lifted.top_eq, lifted.right_eq, lifted.bottom_eq] at closed
  simp only [Topology.Mesh.IndexedQuadrilaterals.IndexedQuadrilateral.boundary, lifted.first_eq, lifted.second_eq,
    lifted.third_eq, lifted.fourth_eq,
    lifted.top_eq, lifted.right_eq, lifted.bottom_eq, RegularFace.boundary,
      Geometry.Grid.ClearGrid.Cell.boundaryWalk_sides,
    SquareRoot.Grid.RootEdgeBank.indexedEdges, SquareRoot.Grid.RootEdgeBank.indexedEdge]
  rw [closed]

open Purelib.Topology.Polygon in
/-- The two retained triangle wedge areas sum to the area of the original lifted face boundary. -/
theorem wedge_eq_boundary (lifted : LiftedFace vertices edges face sheet)
    (primitive : Fin vertices.count → Stokes.PrimitivePoint) :
    Stokes.triangleWedgeArea (primitive lifted.quad.first) (primitive lifted.quad.second) (primitive lifted.quad.third)
      +
      Stokes.triangleWedgeArea (primitive lifted.quad.first) (primitive lifted.quad.third) (primitive
        lifted.quad.fourth) =
      Stokes.edgeListArea primitive (edges.indexedEdges vertices face.boundary sheet) :=
  lifted.quad.wedge_eq_boundary primitive |>.trans (congrArg (Stokes.edgeListArea primitive) lifted.boundary_eq)

end LiftedFace
end BranchCellBank

end Purelib.Riemann.Meshes.GridLiftedFaces
