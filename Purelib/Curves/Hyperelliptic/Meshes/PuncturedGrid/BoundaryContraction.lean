module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Data.List.OfFn.Basic
import Purelib.Algebra.NatCast
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Mesh.CornerWalks
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryContraction
import Purelib.Topology.Surface.Cut.BoundaryVertices
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.Vertices
public import Purelib.Topology.Surface.Word.ZeroReduction
public import Purelib.Topology.Surface.Boundary.BoundaryContractionIndices
public import Purelib.Topology.Surface.Cut.ContractedWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordVertices
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.BranchCellBank

open Purelib.Data.List

open Purelib.Riemann

open Purelib.Topology.Chain

open Purelib.Topology.Mesh.CornerWalks

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Boundary

open Purelib.Topology.Surface.Boundary.BoundaryContraction
open _root_.Purelib.Topology.Surface.Boundary renaming BoundaryContraction -> BoundaryContraction

open Purelib.Topology.Surface.Boundary.BoundaryContractionIndices

open Purelib.Topology.Surface.Cut.BoundaryVertices.SewingForest

open Purelib.Topology.Surface.Cut.ContractedWord

open Purelib.Topology.Surface.Cut.ContractedWord.WordVertexRealization

open Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord

public section

/-!
# Contract the actual physical boundary components

The retained root-labelled mesh supplies the active vertices, the disjoint
physical cycles, and their incidence. Contracting these cycles gives an
executable vertex table with the exact count required by the cut-word Euler
balance. No ambient allocation count is substituted for active vertices.
-/

section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryContraction)
open Purelib.Topology.Surface.Word.Vertices (WordVertexRealization WordVertexModel)
open Purelib.Topology.Surface.Word.NormalForm (WordNormalForm)
open Purelib.Topology.Surface.Word.ZeroReduction (WordCancellation)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- Every retained physical-boundary vertex occurs in an actual lifted triangle. -/
theorem physicalBoundaryVertex_active (lifted : Meshes.LiftedPuncturedGrid base) {vertex : Fin lifted.vertices.count}
    (member : vertex ∈ lifted.boundaryComponents.cycles.flatten.map OrientedEdge.start) :
    vertex ∈ (LiftedMesh.activeVertices lifted.mesh).indices := by
  obtain ⟨edge, member, equal⟩ := Map.mem_map.mp member
  have occurrence := ((lifted.boundaryComponents.edge_iff edge).mp member).1
  obtain ⟨triangle, triangleMember, edgeMember⟩ := Flatten.mem_flatMap.mp occurrence
  obtain ⟨index, triangleEq⟩ := Purelib.Data.List.OfFn.Basic.mem_ofFn.mp triangleMember
  apply ((LiftedMesh.activeVertices lifted.mesh).active_iff vertex).mpr
  refine ⟨index, ?_⟩
  rw [triangleEq]
  exact OrientedTriangle.edge_contains edgeMember (.inl equal.symm)

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction

/-- The anchor of a nonempty closed edge path occurs among its starting vertices. -/
private theorem closed_start_mem {count : Nat} {word : List (Stokes.OrientedEdge count)} {anchor : Fin count}
    (closed : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor anchor)
    (nonempty : word ≠ []) : anchor ∈ word.map OrientedEdge.start := by
  cases closed with
  | nil => exact (nonempty rfl).elim
  | cons => exact List.mem_cons_self

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- The retained cut-polygon anchor is an active vertex of the actual lifted mesh. -/
theorem cut_anchor_active (lifted : Meshes.LiftedPuncturedGrid base) :
    lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.anchor ∈ (LiftedMesh.activeVertices
      lifted.mesh).indices := by
  apply ((LiftedMesh.activeVertices lifted.mesh).active_iff _).mpr
  apply (SinglePolygon.boundary_projection_mem_iff lifted.cutPolygon _).mp
  apply Map.mem_map_of_mem
  apply Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.closed_start_mem
    lifted.cutPolygon.patch.cut.closed
  intro empty
  have size := lifted.cutPolygon.boundaryCount
  rw [empty, List.length_nil] at size
  omega

/-- Preparation and root transport are retained. Only the finite boundary contraction is computed, and its table is
cached for every later consumer. -/
@[expose] def boundaryContraction (lifted : Meshes.LiftedPuncturedGrid base) :
    Topology.Surface.Boundary.BoundaryContraction lifted.boundaryComponents (LiftedMesh.activeVertices
      lifted.mesh).indices :=
  BoundaryContraction.build lifted.boundaryComponents (LiftedMesh.activeVertices lifted.mesh).indices
    (lifted.cutPolygon.patch.cut.vertexLabels lifted.cutPolygon.patch.cut.anchor)
    lifted.cut_anchor_active (LiftedMesh.activeVertices lifted.mesh).unique (fun _ member =>
      lifted.physicalBoundaryVertex_active member)

/-- The original paired letters form a closed path in the dense contracted surface vertices. Each omitted physical edge
is proved to become a loop. -/
@[expose] def contractedCutWordWith (lifted : Meshes.LiftedPuncturedGrid base)
    (contraction : Topology.Surface.Boundary.BoundaryContraction lifted.boundaryComponents (LiftedMesh.activeVertices
      lifted.mesh).indices)
    (indexed : (BoundaryContractionIndices.Indexed contraction)) :
    Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      contraction.representatives.length :=
  ProjectedEdgePairing.contractedWord lifted.cutBoundaryPairs indexed.projection
    (fun edge member => indexed.edge_collapsed
      ((lifted.cut_boundary_iff_boundaryComponents (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels edge)).mp
        (Map.mem_map_of_mem member)))
    lifted.cutPolygon.patch.cut.anchor lifted.cutPolygon.patch.cut.closed

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction

set_option genInjectivity false in
/-- Retain the contraction, its dense indexing, and the realized actual paired word together. Subsequent comparisons
consume these exact caches. -/
structure ContractedCutWord (lifted : Meshes.LiftedPuncturedGrid base) where
  /-- The cached contraction of the actual physical boundary cycles on active vertices. -/ contraction :
    Topology.Surface.Boundary.BoundaryContraction lifted.boundaryComponents (LiftedMesh.activeVertices
      lifted.mesh).indices
  /-- The retained dense indexing of this exact contraction. -/ indexed : (BoundaryContractionIndices.Indexed
    contraction)
  /-- The actual paired cut word realized in the contraction's representative vertices. -/ word :
    Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
    contraction.representatives.length
  /-- The cached realization is exactly the construction from this contraction and its indexing. -/ word_eq : word =
    lifted.contractedCutWordWith contraction indexed

constructive_injectivity ContractedCutWord

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- Cache the physical boundary contraction, its dense indexing and the realized paired cut word together. -/
@[expose] def contractedCutWord (lifted : Meshes.LiftedPuncturedGrid base) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord lifted :=
  let contraction := lifted.boundaryContraction
  let indexed := Indexed.build contraction
  { contraction := contraction
    indexed := indexed
    word := lifted.contractedCutWordWith contraction indexed
    word_eq := rfl }

/-- Every contracted vertex really occurs in the paired word, including vertices reached only after a run of deleted
physical-boundary letters. -/
theorem contractedCutWordWith_covered (lifted : Meshes.LiftedPuncturedGrid base)
    (contraction : Topology.Surface.Boundary.BoundaryContraction lifted.boundaryComponents (LiftedMesh.activeVertices
      lifted.mesh).indices)
    (indexed : (BoundaryContractionIndices.Indexed contraction)) (index : Fin contraction.representatives.length) :
    (lifted.contractedCutWordWith contraction indexed).Supported index := by
  have active := ((LiftedMesh.activeVertices lifted.mesh).active_iff _).mp
    (contraction.representative_active (List.getElem_mem index.isLt))
  have source := (SinglePolygon.boundary_projection_mem_iff lifted.cutPolygon _).mpr active
  obtain ⟨vertex, member, equal⟩ := Map.mem_map.mp source
  have support := ProjectedEdgePairing.contractedWord_supported lifted.cutBoundaryPairs indexed.projection
    (fun edge member => indexed.edge_collapsed
      ((lifted.cut_boundary_iff_boundaryComponents (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels edge)).mp
        (Map.mem_map_of_mem member)))
    lifted.cutPolygon.patch.cut.anchor lifted.cutPolygon.patch.cut.closed member
  rw [equal, indexed.readback] at support
  exact support

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord

/-- Every retained contracted vertex is supported by the cached paired word. -/
theorem covered {lifted : Meshes.LiftedPuncturedGrid base} (cache :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord lifted)
    (index : Fin cache.contraction.representatives.length) : cache.word.Supported index := by
  rw [cache.word_eq]
  exact lifted.contractedCutWordWith_covered cache.contraction cache.indexed index

/-- The universal normal-form vertices map onto the actual contracted surface vertices, preserving the anchor and every
labelled cut edge. -/
theorem factor_surjective {lifted : Meshes.LiftedPuncturedGrid base} (cache :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord lifted)
    {size : Nat} (model : Vertices.WordVertexModel (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord) size) :
    Function.Surjective (model.lift cache.word).vertices := Factor.surjective (model.lift cache.word) cache.covered

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction.ContractedCutWord

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

/-- The contracted vertex count is the active count minus physical boundary edges plus boundary components. -/
theorem contracted_vertex_count (lifted : Meshes.LiftedPuncturedGrid base)
    (contraction : Topology.Surface.Boundary.BoundaryContraction lifted.boundaryComponents (LiftedMesh.activeVertices
      lifted.mesh).indices) :
    (contraction.representatives.length : Int) =
      ((LiftedMesh.activeVertices lifted.mesh).indices.length : Int) - lifted.boundaryComponents.cycles.flatten.length +
        lifted.boundaryComponents.cycles.length := by
  have size := congrArg (fun value : Nat => (value : Int)) contraction.count_eq
  simp only [Purelib.Algebra.NatCast.add] at size
  omega

/-- The two independently constructed finite vertex counts now appear in one exact identity. Identifying their vertex
models will imply `g` handles. -/
theorem contracted_cutWord_genus_balance (lifted : Meshes.LiftedPuncturedGrid base)
    (normal : NormalForm.WordNormalForm (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord)
      (IntegralPairing.wordSignature lifted.cutIntegralPairing))
    (terminal : ZeroReduction.WordCancellation normal.trace.terminalWord)
    (contraction : Topology.Surface.Boundary.BoundaryContraction lifted.boundaryComponents (LiftedMesh.activeVertices
      lifted.mesh).indices) :
    2 * (normal.pivots.length : Int) + (terminal.pairs + 1 : Nat) =
      (contraction.representatives.length : Int) + 2 * genus := by
  rw [lifted.contracted_vertex_count contraction]
  exact lifted.cutWord_vertex_euler_balance normal terminal (lifted.cutWordVertexModelWith normal terminal)

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

end
