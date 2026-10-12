module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Branches.Cuts
public import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Polynomial.Dense.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Data.Gaussian.Basic

@[expose] public section

/-!
# A retained two-sheeted mesh of the framed punctured branch grid

The base frame, vertex identities, actual root owners, shared edge maps and
both lifts of every regular face are constructed together.  Generated data
may instead populate these same checked cache fields.  This is the excised
cover mesh, not yet a fundamental polygon with an identified A/B boundary.
-/

namespace Purelib.Riemann.Meshes

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

open Purelib.Riemann.Meshes in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A lift of the original framed punctured grid retaining its vertex bank, root frames, edge bank and triangulated
mesh.

Every stored component is indexed by the same original grid and faces, with the edge bank depending on the exact
retained root frames. -/
structure LiftedPuncturedGrid (base : FramedPuncturedGrid curve branches higher) where
  /-- The retained vertex bank of the original framed punctured grid. -/ vertices :
    SquareRoot.Grid.LiftedVertices.VertexBank base.bank.grid
  /-- The retained root frames on the exact original grid vertices. -/ frames : RootIsolation.SquareRoot.Grid.RootFrames
    base.bank.grid
  /-- The retained root-edge bank using the exact stored frames. -/ edges : SquareRoot.Grid.RootEdgeBank
    frames
  /-- The retained lifted mesh using the original banks and punctured faces. -/ mesh : GridLiftedMesh.LiftedMesh
    vertices edges base.faces

constructive_injectivity LiftedPuncturedGrid

namespace LiftedPuncturedGrid

open Purelib.Riemann.Meshes in
open Purelib.RootIsolation in
/-- Construct the original punctured grid's vertex and root-frame banks, then retain their exact edge bank and lifted
mesh.

The stored banks are passed directly to the mesh builder, preserving their nominal owners and all bounded vertex and
face indices. -/
def build (base : FramedPuncturedGrid curve branches higher) : LiftedPuncturedGrid base :=
  let vertices := SquareRoot.Grid.LiftedVertices.VertexBank.build base.bank.grid
  let frames := RootIsolation.SquareRoot.Grid.RootFrames.build base.bank.grid
  let edges := SquareRoot.Grid.RootEdgeBank.build frames
  { vertices := vertices
    frames := frames
    edges := edges
    mesh := GridLiftedMesh.LiftedMesh.build vertices edges base.faces }

/-- The retained lifted punctured grid has four triangles per original regular face. -/
theorem faceCount {base : FramedPuncturedGrid curve branches higher} (lifted : LiftedPuncturedGrid base) :
    lifted.mesh.triangles.length = 4 * base.faces.regulars.length := lifted.mesh.faceCount

open Purelib.Riemann.Meshes in
/-- Every retained lifted punctured-grid triangle has strictly positive coordinate area. -/
theorem face_positive {base : FramedPuncturedGrid curve branches higher} (lifted : LiftedPuncturedGrid base)
    (index : Fin lifted.mesh.triangles.length) :
    0 < GridLiftedMesh.LiftedFaces.triangleArea lifted.vertices (lifted.mesh.triangulation.faces index) :=
  lifted.mesh.face_positive index

end LiftedPuncturedGrid

end Purelib.Riemann.Meshes
