module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.VertexLiftChoices
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PuncturedVertexStars
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Meshes.GridLiftedCornerConnections
public import Purelib.Riemann.Meshes.GridLiftedCornerCoherence
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Polynomial.Geometry.Grid.VertexStar
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PuncturedVertexConnections
import Purelib.Topology.Mesh.CornerWalks

@[expose] public section

/-!
# Connected stars of actual root-labelled triangle vertices

Decode the original triangle and select its retained face lift at the
specified corner. Canonical vertex readback is proved only for actual face
corners: an arbitrary coordinate bank may contain duplicate unused entries.
The resulting routes preserve that exact vertex at every crossed seam.
-/

namespace Purelib.Riemann.Meshes.GridLiftedTriangleStars

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.CornerWalks (VertexConnection)
open Purelib.Topology.Mesh.CornerWalks.OrientedTriangle (ContainsVertex)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Integration.PuncturedVertexConnections (RegularIncident)

end Purelib.Riemann.Meshes.GridLiftedTriangleStars

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)

namespace Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial}
  {ambient : Purelib.Geometry.Rational.Box} {grid : Polynomial.Geometry.Grid.ClearGrid
    polynomial ambient}

open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank
open Purelib.Data
open Purelib.Polynomial
open Purelib.RootIsolation
/-- Equal coordinates give equal canonical vertex indices for the same sheet. -/
private theorem index_congr (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) {first last :
  Gaussian.Basic.Canonical} (equal : first = last)
    (firstOn : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid first) (lastOn :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex grid last) (sheet : Fin 2) :
    vertices.index first firstOn sheet = vertices.index last lastOn sheet := by
  cases equal
  rfl

/-- Re-indexing the coordinate and sheet of a canonical bank index recovers that index. -/
theorem index_readback (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) (point : Gaussian.Basic.Canonical)
  (onGrid : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point) (sheet : Fin 2) :
    vertices.index (vertices.coordinate (vertices.index point onGrid sheet))
      (vertices.coordinate_onGrid _) (vertices.sheet (vertices.index point onGrid sheet)) = vertices.index point onGrid
        sheet :=
  (SquareRoot.Grid.LiftedVertices.VertexBank.index_congr vertices (vertices.coordinate_index point onGrid sheet) _ _
    _).trans
    (congrArg (vertices.index point onGrid) (vertices.sheet_index point onGrid sheet))

end Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank

namespace Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {face : RegularFace bank} {sheet : Fin 2} {vertex : Fin vertices.count}

/-- Every actual corner of the lifted quadrilateral lies in its original regular face box. -/
theorem corner_inside (lifted : LiftedFace vertices edges face sheet)
    (corner : vertex = lifted.quad.first ∨ vertex = lifted.quad.second ∨
      vertex = lifted.quad.third ∨ vertex = lifted.quad.fourth) : face.cell.box.Contains (vertices.coordinate vertex) :=
        by
  rcases corner with same | same | same | same <;> subst vertex
  · rw [lifted.coordinates.1]
    exact face.cell.box.contains_anchor
  · rw [lifted.coordinates.2.1]
    exact ⟨face.cell.box.x_valid, le_rfl, le_rfl, face.cell.box.y_valid⟩
  · rw [lifted.coordinates.2.2.1]
    exact ⟨face.cell.box.x_valid, le_rfl, face.cell.box.y_valid, le_rfl⟩
  · rw [lifted.coordinates.2.2.2]
    exact ⟨le_rfl, face.cell.box.x_valid, face.cell.box.y_valid, le_rfl⟩

open Purelib.RootIsolation in
/-- Readback recovers the exact bank index of an actual lifted-face corner.

The claim uses the retained quadrilateral corner equations; it imposes no injectivity condition on unused
coordinate-bank entries. -/
theorem corner_index (lifted : LiftedFace vertices edges face sheet)
    (corner : vertex = lifted.quad.first ∨ vertex = lifted.quad.second ∨
      vertex = lifted.quad.third ∨ vertex = lifted.quad.fourth) :
    vertices.index (vertices.coordinate vertex) (vertices.coordinate_onGrid vertex) (vertices.sheet vertex) = vertex :=
      by
  rcases corner with same | same | same | same <;> subst vertex
  · simpa only [lifted.first_eq] using
      SquareRoot.Grid.LiftedVertices.VertexBank.index_readback vertices _ _ _
  · simpa only [lifted.second_eq] using
      SquareRoot.Grid.LiftedVertices.VertexBank.index_readback vertices _ _ _
  · simpa only [lifted.third_eq] using
      SquareRoot.Grid.LiftedVertices.VertexBank.index_readback vertices _ _ _
  · simpa only [lifted.fourth_eq] using
      SquareRoot.Grid.LiftedVertices.VertexBank.index_readback vertices _ _ _

/-- The sheet at an actual corner agrees with the lifted side starting there.

Properness of the original face box identifies the side among the four oriented sides, preserving the corner's retained
root label. -/
theorem startSheet_of_corner (lifted : LiftedFace vertices edges face sheet)
    (corner : vertex = lifted.quad.first ∨ vertex = lifted.quad.second ∨
      vertex = lifted.quad.third ∨ vertex = lifted.quad.fourth)
    (side : GridSide) (atPoint : side.start face.cell.box = vertices.coordinate vertex) :
    lifted.sideStartSheet side = vertices.sheet vertex := by
  rcases corner with same | same | same | same <;> subst vertex
  · rw [lifted.coordinates.1] at atPoint
    have same : side = .bottom := GridSide.start_injective face.cell.box_proper atPoint
    exact (congrArg lifted.sideStartSheet same).trans lifted.corner_sheets.1.symm
  · rw [lifted.coordinates.2.1] at atPoint
    have same : side = .right := GridSide.start_injective face.cell.box_proper atPoint
    exact (congrArg lifted.sideStartSheet same).trans lifted.corner_sheets.2.1.symm
  · rw [lifted.coordinates.2.2.1] at atPoint
    have same : side = .top := GridSide.start_injective face.cell.box_proper atPoint
    exact (congrArg lifted.sideStartSheet same).trans lifted.corner_sheets.2.2.1.symm
  · rw [lifted.coordinates.2.2.2] at atPoint
    have same : side = .left := GridSide.start_injective face.cell.box_proper atPoint
    exact (congrArg lifted.sideStartSheet same).trans lifted.corner_sheets.2.2.2.symm

end Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank.LiftedFace

namespace Purelib.Riemann.Meshes.GridLiftedTriangleStars

open Purelib.Topology.Mesh.CornerWalks (VertexConnection)
open Purelib.Topology.Mesh.CornerWalks.OrientedTriangle (ContainsVertex)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Integration.PuncturedVertexConnections (RegularIncident)

namespace FramedPuncturedGrid

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
    VertexBank base.bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

open Purelib.Riemann in
set_option genInjectivity false in
/-- Decode an actual triangle at a retained root-labelled vertex.

The regular incident face, its selected corner lift and triangle half retain the original triangle index and a canonical
readback equation for that exact vertex. -/
structure TriangleAtVertex (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (index : Fin mesh.triangles.length) (vertex : Fin vertices.count) where
  /-- The regular incident face at the original vertex coordinate. -/ regular : RegularIncident base
    (vertices.coordinate vertex)
  /-- The retained corner lift selected by the original vertex sheet. -/ lifted : regular.Lifted mesh (vertices.sheet
    vertex)
  /-- The triangle half within the retained lifted quadrilateral. -/ upper : Bool
  /-- The selected triangle occurrence is the original triangle index. -/ index_eq :
    lifted.value.located.occurrence.triangle upper = index
  /-- Canonical coordinate-and-sheet readback recovers the original vertex index. -/ vertex_eq : vertices.index
    (vertices.coordinate vertex) (vertices.coordinate_onGrid vertex) (vertices.sheet vertex) = vertex

constructive_injectivity TriangleAtVertex

open Purelib.Riemann in
open Purelib.Topology in
/-- Decode the retained face lift and corner of a triangle containing the given vertex.

The selected corner sheet recovers the original face sheet for either triangle half and every corner, retaining exact
triangle and vertex indices. -/
def triangleAtVertex (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (index : Fin mesh.triangles.length) (vertex : Fin vertices.count)
    (contains : Mesh.CornerWalks.OrientedTriangle.ContainsVertex
      (mesh.triangulation.faces index) vertex) : TriangleAtVertex mesh index vertex := by
  let decoded := mesh.locateTriangle index
  have corner := Mesh.CornerWalks.QuadOccurrence.corner_of_contains
    decoded.located.occurrence decoded.upper (decoded.index_eq.symm ▸ contains)
  let regular := RegularIncident.ofPosition base decoded.position (vertices.coordinate vertex)
    (vertices.coordinate_onGrid vertex) (decoded.located.lifted.corner_inside corner)
  let lifted := regular.lift mesh (vertices.sheet vertex)
  have startEq := decoded.located.lifted.startSheet_of_corner corner regular.corner.side regular.corner_start
  have sheetEq : lifted.value.sheet = decoded.sheet :=
    lifted.value.located.lifted.sheet_eq_of_startSheet_eq decoded.located.lifted regular.corner.side
      (lifted.value.start_eq.trans startEq.symm)
  refine ⟨regular, lifted, decoded.upper, ?_, decoded.located.lifted.corner_index corner⟩
  calc
    lifted.value.located.occurrence.triangle decoded.upper =
        (mesh.locateFace regular.located.index lifted.value.sheet).occurrence.triangle decoded.upper :=
          lifted.triangle_eq _
    _ = (mesh.locateFace decoded.position decoded.sheet).occurrence.triangle decoded.upper := by rw [sheetEq]; rfl
    _ = index := decoded.index_eq

open Purelib.Riemann in
open Purelib.Topology in
open Purelib.RootIsolation in
/-- Connect incident triangles through seams containing the same root-labelled vertex.

Decode the original triangles into retained regular corner lifts, connect their incident cells through the constructed
vertex star, and transport the resulting corner route back to the original indices. -/
def vertexConnection (base : FramedPuncturedGrid curve branches higher)
    {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank
      frames}
    (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) : Mesh.CornerWalks.VertexConnection
      mesh.triangulation.faces :=
  fun vertex =>
    let onGrid := vertices.coordinate_onGrid vertex
    let star := Integration.PuncturedVertexStars.VertexStar.build base
      (vertices.coordinate vertex) onGrid
    fun first last firstContains lastContains => by
      let firstCorner := triangleAtVertex mesh first vertex firstContains
      let lastCorner := triangleAtVertex mesh last vertex lastContains
      let connection := RegularIncident.connect star firstCorner.regular lastCorner.regular
      let middleLift := connection.middle.lift mesh (vertices.sheet vertex)
      have firstAt : Mesh.CornerWalks.OrientedTriangle.ContainsVertex
          (mesh.triangulation.faces (firstCorner.lifted.value.located.occurrence.triangle firstCorner.upper))
          (vertices.index (vertices.coordinate vertex) onGrid (vertices.sheet vertex)) := by
        rw [firstCorner.index_eq, firstCorner.vertex_eq]
        exact firstContains
      have lastAt : Mesh.CornerWalks.OrientedTriangle.ContainsVertex
          (mesh.triangulation.faces (lastCorner.lifted.value.located.occurrence.triangle lastCorner.upper))
          (vertices.index (vertices.coordinate vertex) onGrid (vertices.sheet vertex)) := by
        rw [lastCorner.index_eq, lastCorner.vertex_eq]
        exact lastContains
      let route := Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.Connection.cornerRoute
        connection onGrid firstCorner.lifted middleLift lastCorner.lifted
        firstCorner.upper lastCorner.upper firstAt lastAt
      have target := route
      unfold Meshes.GridLiftedCornerConnections.FramedPuncturedGrid.RegularIncident.CornerRoute at target
      rw [firstCorner.index_eq, lastCorner.index_eq, firstCorner.vertex_eq] at target
      exact target

end FramedPuncturedGrid
end Purelib.Riemann.Meshes.GridLiftedTriangleStars
