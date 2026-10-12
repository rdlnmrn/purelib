module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.SourceComparison
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

/-!
# One retained program for the complete cut boundary

The closed word is the actual cut boundary, starting at its retained anchor.
Its source occurrences and length are cached before accuracy is requested.
Generated programs can fill the same structure through semantic equations;
no equality with a default cover or root-preparation computation is required.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms

open Purelib.Curves
open Purelib.Riemann
open Purelib

namespace CutPatch

open Purelib.Topology.Surface.Cut.JumpPaths

/-- Read the literal original cut boundary as a closed projected cycle at its retained anchor. -/
@[expose] def boundaryCycle {vertexCount faceCount : Nat} {faces : Fin faceCount →
  Topology.Polygon.Stokes.OrientedTriangle vertexCount}
    {indices : List (Fin faceCount)} {boundary : List (Topology.Polygon.Stokes.OrientedEdge vertexCount)}
    (patch : Topology.Surface.Cut.Patch.CutPatch faces indices boundary) :
    Topology.Surface.Sewing.CutCycleChains.ClosedCutCycle patch.vertexLabels (patch.boundary.map
      (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels)) :=
  ⟨patch.anchor, patch.anchor, Topology.Surface.Cut.JumpPaths.CutPath.Projected.build patch.vertexLabels patch.boundary
    patch.closed,
    rfl, fun _ member => Or.inl member⟩

end CutPatch

namespace LiftedPuncturedGrid

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}

set_option genInjectivity false in
/-- The original complete cut-boundary program with its exact anchor, source occurrences and length.

Positive orientation and source ownership are retained for the actual cached boundary word. -/
structure BoundaryProgram (lifted : Meshes.LiftedPuncturedGrid base) (source :
  Hyperelliptic.Differentials.Basic.Differential genus) where
  /-- The original cut-cycle integration program. -/ program :
    Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram lifted source
  /-- The program starts at the retained cut anchor. -/ start_eq : program.cycle.start =
    lifted.cutPolygon.patch.cut.anchor
  /-- The program uses exactly the actual original cut boundary. -/ edges_eq : program.cycle.path.cutEdges =
    lifted.cutPolygon.patch.cut.boundary
  /-- Every original routed source occurrence has positive orientation. -/ positive :
    Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.Positive program.routed.spine
  /-- The cached sources of the literal cut boundary. -/ sources :
    Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources lifted.cutPolygon.patch.cut
    lifted.cutPolygon.patch.cut.boundary
  /-- The exact retained sources have positive orientation. -/ sources_positive : sources.Positive
  /-- The retained original boundary length. -/ count : Nat
  /-- The count equals the literal original cut-boundary length. -/ count_eq : count =
    lifted.cutPolygon.patch.cut.boundary.length

constructive_injectivity BoundaryProgram

namespace BoundaryProgram

/-- Prepare the literal original cut boundary once and retain its positive source cache and exact count.

The program, anchor, positive routed sources and count all refer to the same retained cut boundary; the builder stores
those source occurrences for later readback. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base) (source : Hyperelliptic.Differentials.Basic.Differential
  genus) :
    Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.LiftedPuncturedGrid.BoundaryProgram lifted source :=
  let patch := lifted.cutPolygon.patch.cut
  let cycle := Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms.CutPatch.boundaryCycle patch
  let sources := Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources.build patch patch.boundary
    (fun _ member => Or.inl member)
  have sourcesPositive : sources.Positive :=
    Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources.build_positive patch patch.boundary _ (fun
    _ member => member)
  let program := Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms.CutCycleProgram.build lifted cycle source
  have positive : Hyperelliptic.Meshes.PuncturedGrid.TriangleSourceUniqueness.LiftedMesh.RouteSpine.Positive
    program.routed.spine := by
    change ∀ edge ∈ program.routed.spine.values (fun _ route => route.sourceEdge),
      Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive edge lifted.mesh.triangulation.faces
    rw [Hyperelliptic.Meshes.PuncturedGrid.Cut.SourceComparison.build_sourceEdges cycle source sources sourcesPositive]
    exact sourcesPositive
  ⟨program, rfl, rfl, positive, sources, sourcesPositive, patch.boundary.length, rfl⟩

end BoundaryProgram
end LiftedPuncturedGrid

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryPrograms

end
