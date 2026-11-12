module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.Triangles
public import Purelib.Riemann.Meshes.GridLiftedFaceLocations
public import Purelib.Geometry.Triangles.AffineCut
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Refinement

/-! # Common diagonal cuts of the SAME old and fine retained signed cells

The original LocatedFace and actual fine LiftedCell remain separate whole
inputs. Their cached coordinates determine the real old diagonal and both
fine triangles. Each total affine cut is executed once and stored. No
vertex-label projection identifies a new root with an old root, and no
old source triangle, primitive constant or deformation is assumed.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Geometry.Triangles
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {old : RootEdgeBank frames} {faces : PuncturedFaces bank}
variable {oldVertices : VertexBank bank.grid} {position : Fin faces.regulars.length} {oldSheet : Fin 2}
variable {mesh : LiftedMesh oldVertices old faces}

variable {coarse : frames.CellRestriction (faces.regulars[position.val]'position.isLt).cell
  (faces.regulars[position.val]'position.isLt).member} {points : List Canonical}
variable {cuts : CutPartition (faces.regulars[position.val]'position.isLt).cell.box points} (retained : CellRows
  old (faces.regulars[position.val]'position.isLt) coarse cuts)
variable {fineVertices : VertexBank retained.grid} {cell : ClearGrid.Cell curve.polynomial
  (faces.regulars[position.val]'position.isLt).cell.box}
variable {member : cell ∈ retained.grid.cells} {fineSheet : Fin 2}
variable (located : mesh.LocatedFace position oldSheet)
variable (lifted : retained.LiftedCell fineVertices cell member fineSheet)

/-- Preserve both whole signed owners, their actual diagonal/triangle coordinates, and both total cut results.

The first and second fine faces are separate real consumers of the same
retained old diagonal. On-line, boundary-tie and crossing alternatives are
kept by the original cut operation, including collapsed occurrences.
-/
abbrev DiagonalCut :=
  Σ inputs : {value : mesh.LocatedFace position oldSheet ×
      retained.LiftedCell fineVertices cell member fineSheet // value = (located, lifted)},
  Σ diagonal : {value : Canonical × Canonical // value =
    (oldVertices.coordinate inputs.val.1.lifted.quad.first,
      oldVertices.coordinate inputs.val.1.lifted.quad.third)},
  Σ triangles : {value : CoordinateTriangle × CoordinateTriangle // value =
    (⟨fineVertices.coordinate inputs.val.2.quad.first, fineVertices.coordinate inputs.val.2.quad.second,
      fineVertices.coordinate inputs.val.2.quad.third⟩,
      ⟨fineVertices.coordinate inputs.val.2.quad.first, fineVertices.coordinate inputs.val.2.quad.third,
        fineVertices.coordinate inputs.val.2.quad.fourth⟩)},
  Σ _first : {value : AffineCut.Cut diagonal.val.1 diagonal.val.2 triangles.val.1 //
    value = AffineCut.build diagonal.val.1 diagonal.val.2 triangles.val.1},
  {value : AffineCut.Cut diagonal.val.1 diagonal.val.2 triangles.val.2 //
    value = AffineCut.build diagonal.val.1 diagonal.val.2 triangles.val.2}

/-- Materialize the actual common diagonal cuts of both cached fine faces once.

This is new finite geometry work. It reads the supplied signed banks and
stores both whole original owners; it acquires no Point, Query, frame,
root transport, Entry, numerical request or observed join.
-/
def cutDiagonal : retained.DiagonalCut located lifted :=
  let diagonal :=
    (oldVertices.coordinate located.lifted.quad.first, oldVertices.coordinate located.lifted.quad.third)
  let triangles : CoordinateTriangle × CoordinateTriangle :=
    (⟨fineVertices.coordinate lifted.quad.first, fineVertices.coordinate lifted.quad.second,
      fineVertices.coordinate lifted.quad.third⟩,
      ⟨fineVertices.coordinate lifted.quad.first, fineVertices.coordinate lifted.quad.third,
        fineVertices.coordinate lifted.quad.fourth⟩)
  let first := AffineCut.build diagonal.1 diagonal.2 triangles.1
  let last := AffineCut.build diagonal.1 diagonal.2 triangles.2
  ⟨⟨(located, lifted), rfl⟩, ⟨diagonal, rfl⟩, ⟨triangles, rfl⟩, ⟨first, rfl⟩, ⟨last, rfl⟩⟩

namespace DiagonalCut

variable {retained located lifted} (cached : retained.DiagonalCut located lifted)

/-- Read the whole original retained old-face location, with both actual mesh triangle indices. -/
def oldLocation : mesh.LocatedFace position oldSheet := cached.1.val.1

/-- Read the whole original retained fine cell, with all four signed corner occurrences. -/
def fineCell : retained.LiftedCell fineVertices cell member fineSheet := cached.1.val.2

/-- Read the one actual old diagonal coordinate pair used by both fine cuts. -/
def diagonal : Canonical × Canonical := cached.2.1.val

/-- Read the two original fine-face coordinate occurrences. -/
def triangles : CoordinateTriangle × CoordinateTriangle := cached.2.2.1.val

/-- Read the first actual total cut result without replaying its classification or patch work. -/
def first : AffineCut.Cut cached.diagonal.1 cached.diagonal.2 cached.triangles.1 := cached.2.2.2.1.val

/-- Read the second actual total cut result without replaying its classification or patch work. -/
def last : AffineCut.Cut cached.diagonal.1 cached.diagonal.2 cached.triangles.2 := cached.2.2.2.2.val

/-- The exact old location is retained, including original root/frame and face occurrence data. -/
theorem oldLocation_eq : cached.oldLocation = located := congrArg Prod.fst cached.1.property

/-- The exact fine cell is retained, including all signed bounded indices and its original factory. -/
theorem fineCell_eq : cached.fineCell = lifted := congrArg Prod.snd cached.1.property

/-- The shared diagonal is read from the SAME retained old signed quadrilateral. -/
theorem diagonal_eq : cached.diagonal =
    (oldVertices.coordinate cached.oldLocation.lifted.quad.first,
      oldVertices.coordinate cached.oldLocation.lifted.quad.third) := cached.2.1.property

/-- The old coordinate readbacks identify its diagonal with its literal original regular box diagonal. -/
theorem diagonal_box : cached.diagonal =
    ((faces.regulars[position.val]'position.isLt).cell.box.anchor, point
      (faces.regulars[position.val]'position.isLt).cell.box.xUpper
      (faces.regulars[position.val]'position.isLt).cell.box.yUpper) := by
  rw [cached.diagonal_eq, cached.oldLocation.lifted.coordinates.1, cached.oldLocation.lifted.coordinates.2.2.1]

/-- The two retained coordinate faces are exactly those of the SAME actual fine quadrilateral. -/
theorem triangles_eq : cached.triangles =
    (⟨fineVertices.coordinate cached.fineCell.quad.first, fineVertices.coordinate cached.fineCell.quad.second,
      fineVertices.coordinate cached.fineCell.quad.third⟩,
      ⟨fineVertices.coordinate cached.fineCell.quad.first, fineVertices.coordinate cached.fineCell.quad.third,
        fineVertices.coordinate cached.fineCell.quad.fourth⟩) := cached.2.2.1.property

/-- Both actual fine triangles remain in the literal selected old regular box.

This is containment from the original cell factory and actual coordinate
readbacks. It asserts no root/Entry equality or old triangle source map.
-/
theorem triangles_inside :
    ((faces.regulars[position.val]'position.isLt).cell.box.Contains cached.triangles.1.first ∧
      (faces.regulars[position.val]'position.isLt).cell.box.Contains cached.triangles.1.second ∧
      (faces.regulars[position.val]'position.isLt).cell.box.Contains cached.triangles.1.third) ∧
    ((faces.regulars[position.val]'position.isLt).cell.box.Contains cached.triangles.2.first ∧
      (faces.regulars[position.val]'position.isLt).cell.box.Contains cached.triangles.2.second ∧
      (faces.regulars[position.val]'position.isLt).cell.box.Contains cached.triangles.2.third) := by
  rw [cached.triangles_eq, cached.fineCell.coordinates.1, cached.fineCell.coordinates.2.1,
    cached.fineCell.coordinates.2.2.1, cached.fineCell.coordinates.2.2.2]
  have anchor := cell.box_refines.contains cell.box.contains_anchor
  have lowerRight := cell.box_refines.contains
    (show cell.box.Contains (point cell.box.xUpper cell.box.yLower) from
      ⟨cell.box.x_valid, by exact le_rfl, by exact le_rfl, cell.box.y_valid⟩)
  have upperRight := cell.box_refines.contains
    (show cell.box.Contains (point cell.box.xUpper cell.box.yUpper) from
      ⟨cell.box.x_valid, by exact le_rfl, cell.box.y_valid, by exact le_rfl⟩)
  have upperLeft := cell.box_refines.contains
    (show cell.box.Contains (point cell.box.xLower cell.box.yUpper) from
      ⟨by exact le_rfl, cell.box.x_valid, cell.box.y_valid, by exact le_rfl⟩)
  exact ⟨⟨anchor, lowerRight, upperRight⟩, ⟨anchor, upperRight, upperLeft⟩⟩

/-- The first total cut retains its whole original finite constructor. -/
theorem first_eq : cached.first =
    AffineCut.build cached.diagonal.1 cached.diagonal.2 cached.triangles.1 := cached.2.2.2.1.property

/-- The second total cut retains its whole original finite constructor. -/
theorem last_eq : cached.last =
    AffineCut.build cached.diagonal.1 cached.diagonal.2 cached.triangles.2 := cached.2.2.2.2.property

end DiagonalCut

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows

end
