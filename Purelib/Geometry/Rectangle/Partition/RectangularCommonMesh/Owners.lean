module

public import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
import Purelib.Geometry.Rectangle.Partition.RectangularMeshRefinement
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Data.List.Membership

/-! # Actual coarse owners of a once-built single-cell common mesh -/

public section

namespace Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels.CommonMesh

open Purelib
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle OwnedTriangulation)

variable {columns rows : Nat} {geometry : Geometry columns rows}
variable {column : Fin (columns + 1)} {row : Fin (rows + 1)} {points : List Canonical}

/-- Every vertex of the original singleton common-mesh factory retains that SAME selected model cell. -/
theorem build_owner_cell (geometry : Geometry columns rows)
    (column : Fin (columns + 1)) (row : Fin (rows + 1)) (points : List Canonical)
    (vertex : Fin (build geometry [(column, row)] points).surface.mesh.vertices.length) :
    ((build geometry [(column, row)] points).surface.owners vertex).column = column ∧
      ((build geometry [(column, row)] points).surface.owners vertex).row = row := by
  let cells := CutCells.build geometry points [(column, row)]
  change ((OwnedTriangulation.build cells.triangles).owners vertex).column = column ∧
    ((OwnedTriangulation.build cells.triangles).owners vertex).row = row
  refine OwnedTriangulation.build_owner_cell column row cells.triangles ?_ vertex
  intro triangle member
  change triangle ∈ (CutCell.build geometry column row points).triangles ++ [] at member
  rcases Membership.mem_append.mp member with member | absent
  · rewrite [(CutCell.build geometry column row points).triangles_eq] at member
    exact RectangularMeshRefinement.ModelTriangle.fromBoxes_cell geometry column row _ _ member
  · exact (List.not_mem_nil absent).elim

/-- The actual stored whole factory equality transports the original vertex-cell law to its retained mesh.

This uses the producer equation. An independently generated CommonMesh
may choose another containing cell at a boundary, so mere single-cell
triangle selection is not used to identify its surface owners.
-/
theorem owner_cell (mesh : CommonMesh geometry [(column, row)] points)
    (factory : mesh = build geometry [(column, row)] points)
    (vertex : Fin mesh.surface.mesh.vertices.length) :
    (mesh.surface.owners vertex).column = column ∧ (mesh.surface.owners vertex).row = row := by
  cases factory
  exact build_owner_cell geometry column row points vertex

end Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels.CommonMesh

end
