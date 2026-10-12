module
import Purelib.Data.Fin
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.EdgeOccurrences
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.RootIsolation.SquareRoot.Grid.RootEdges
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Curves

open Purelib.Data

open Purelib.Polynomial

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-!
# Paired triangle occurrences along the original transported grid walk

The two source lists follow each cached edge's actual sheet permutation.
Their projected indices are the original two lifted walks. The finite
permutation identity groups their increments edge by edge without assuming
that a sheet label stays constant along the walk.
-/

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid}
  {edges : SquareRoot.Grid.RootEdgeBank frames} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges
    base.faces}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.EdgeOccurrences

variable {start finish : Gaussian.Basic.Canonical} {edge : Geometry.Grid.Walks.Edge base.bank.grid start finish}

/-- Select the original zero- or one-sheet triangle occurrence for the retained paired edge. -/
@[expose] def source (paired : EdgeOccurrences mesh edge) : Fin 2 →
  Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length
  | ⟨0, _⟩ => paired.zeroSource
  | ⟨1, _⟩ => paired.oneSource
  | ⟨_ + 2, impossible⟩ => (by omega : False).elim

/-- The selected original triangle occurrence projects to the exact transported lifted edge on its supplied sheet. -/
theorem source_project (paired : EdgeOccurrences mesh edge) (sheet :
  Fin 2) :
    (paired.source sheet).project mesh.triangulation.faces = edges.indexedEdge vertices edge sheet := by
  refine Purelib.Data.Fin.cases_induction paired.zero_project (Purelib.Data.Fin.cases_induction paired.one_project (fun
    empty => Fin.elim0 empty)) sheet

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.EdgeOccurrences

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences

set_option genInjectivity false in
/-- Paired original triangle-edge occurrences aligned with every edge of a retained grid walk.

Successive source selection follows each actual edge's sheet permutation. -/
inductive PairedWalk (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    {start finish : Gaussian.Basic.Canonical} → Geometry.Grid.Walks.Walk base.bank.grid start finish → Type
  /-- The paired occurrence bank of the original empty walk at its retained point. -/ | nil (point :
    Gaussian.Basic.Canonical) : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh
    (.nil point)
  /-- Prepend the actual paired edge occurrences to the original retained tail walk. -/ | cons {start middle finish :
    Gaussian.Basic.Canonical} {edge : Geometry.Grid.Walks.Edge base.bank.grid start middle}
      {tail : Geometry.Grid.Walks.Walk base.bank.grid middle finish} (head :
        EdgeOccurrences mesh edge)
      (remaining : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh tail) :
        Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh (.cons edge tail)

constructive_injectivity PairedWalk

namespace PairedWalk

/-- Prepare the original paired triangle occurrences recursively along the retained grid walk. -/
@[expose] def build (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) :
    {start finish : Gaussian.Basic.Canonical} → (walk : Geometry.Grid.Walks.Walk base.bank.grid start finish) →
      Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk
  | _, _, .nil point => .nil point
  | _, _, .cons edge tail => .cons (EdgeOccurrences.build mesh edge)
    (Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk.build mesh tail)

/-- Read the original ordered triangle sources while following each retained edge's actual sheet transport. -/
@[expose] def sources : {start finish : Gaussian.Basic.Canonical} → {walk : Geometry.Grid.Walks.Walk base.bank.grid
  start finish} →
    Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk → Fin 2 → List
      (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge mesh.triangles.length)
  | _, _, _, .nil _, _ => []
  | _, _, _, .cons (edge := edge) head tail, sheet =>
      head.source sheet :: tail.sources ((edges.edge edge).forward.target sheet)

/-- The retained source list projects to the exact original lifted walk on its starting sheet. -/
theorem sources_project : ∀ {start finish : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk base.bank.grid
  start finish}
    (paired : Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk) (sheet : Fin 2),
    (paired.sources sheet).map (fun source => source.project mesh.triangulation.faces) = edges.indexedEdges vertices
      walk sheet
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons head tail, sheet =>
      congrArg₂ List.cons (head.source_project sheet) (tail.sources_project _)

/-- Read the sum of both original sheet increments for every retained edge occurrence. -/
@[expose] def sums (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    {start finish : Gaussian.Basic.Canonical} → {walk : Geometry.Grid.Walks.Walk base.bank.grid start finish} →
      Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk → List Gaussian.Basic.Canonical
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => (head.zeroSource.increment values + head.oneSource.increment values) ::
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk.sums values tail

/-- The retained list of paired increment sums has the original walk's exact edge count. -/
theorem sums_length (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    ∀ {start finish : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk base.bank.grid start finish} (paired :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk),
    (paired.sums values).length = walk.edgeCount
  | _, _, _, .nil _ => rfl
  | _, _, _, .cons _ tail => congrArg Nat.succ (tail.sums_length values)

/-- Actual edge transport may exchange the labels at every step. Its
proved finite bijection is exactly what permits this regrouping. -/
theorem sums_eq (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    ∀ {start finish : Gaussian.Basic.Canonical} {walk : Geometry.Grid.Walks.Walk base.bank.grid start finish} (paired :
      Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences.PairedWalk mesh walk),
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((paired.sources 0).map fun source => source.increment values) +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((paired.sources 1).map fun source => source.increment values) =
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (paired.sums values)
  | _, _, _, .nil _ => by change (0 : Gaussian.Basic.Canonical) + 0 = 0; ring1
  | _, _, _, .cons (edge := edge) head tail => by
      have reindex := Data.Gaussian.Norm.Sum.Basic.sum_two_reindex (edges.edge edge).forward.target
        ((edges.edge edge).bijection (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt
          base.bank.toBranchCellBank _ edge.vertices.1).toLoop
          (Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt base.bank.toBranchCellBank _
            edge.vertices.2).toLoop).forward_injective
        (fun sheet => Data.Gaussian.Norm.Sum.Basic.gaussianSum ((tail.sources sheet).map fun source => source.increment
          values))
      change (head.zeroSource.increment values + Data.Gaussian.Norm.Sum.Basic.gaussianSum ((tail.sources ((edges.edge
        edge).forward.target 0)).map _)) +
        (head.oneSource.increment values + Data.Gaussian.Norm.Sum.Basic.gaussianSum ((tail.sources ((edges.edge
          edge).forward.target 1)).map _)) =
          (head.zeroSource.increment values + head.oneSource.increment values) +
            Data.Gaussian.Norm.Sum.Basic.gaussianSum (tail.sums values)
      rw [← tail.sums_eq values, ← reindex]
      ring1

end PairedWalk
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
