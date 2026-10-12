module
public import Purelib.Data.List.Filter
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.List.Map
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexGluing
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryContraction
import Purelib.Topology.Surface.Boundary.BoundaryContractionIndices
public import Purelib.Topology.Surface.Cut.AlphabetWitnesses
public import Purelib.Topology.Surface.Cut.BoundaryVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Sewing.SimpleBoundaryCycles
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Topology.Surface.Word.Vertices
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContraction
public import Purelib.Topology.Surface.Cut.VertexReading
import Batteries.Logic
import Init.Core
import Init.Data.List.Basic
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryComponents
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Word.SignedWord
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Descend the paired-word vertex reading to the actual surface

Finite preimage lookup and the proved cut-vertex gluing theorem construct
the values on the retained surface indices. The physical edges are constant,
so the existing boundary contraction supplies the final factor map.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ActiveVertices.BranchCellBank
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut
open Purelib.Data.List
open Purelib.Riemann
open Purelib.Topology.Chain
open Purelib.Topology.Polygon
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Boundary
open Purelib.Topology.Surface.Cut
open Purelib.Topology.Surface.Cut.AlphabetWitnesses
open Purelib.Topology.Surface.Cut.BoundaryVertices.CutPatch
open Purelib.Topology.Surface.Cut.BoundaryVertices.SewingForest
open Purelib.Topology.Surface.Cut.BoundaryWord
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.VertexSewing
open Purelib.Topology.Surface.Word
open Purelib.Topology.Surface.Word.PairedWord

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Topology.Surface.Word.Vertices (WordVertexRealization)
open Purelib.Topology.Surface.Cut.VertexReading (CutVertexReading)
open _root_.Purelib.Topology.Surface.Boundary (BoundaryContraction)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

/-- Find an explicit retained source vertex mapping to the supplied target vertex.

The finite lookup returns its membership and exact label equality; no choice or replacement vertex owner is introduced.
-/
@[expose] def preimage {source target : Nat} (labels : Fin source → Fin target) (vertex : Fin target) :
    (vertices : List (Fin source)) → vertex ∈ vertices.map labels →
      { original : Fin source // original ∈ vertices ∧ labels original = vertex }
  | [], member => (List.not_mem_nil member).elim
  | first :: rest, member =>
      if same : labels first = vertex then ⟨first, List.mem_cons_self, same⟩
      else
        let tail := preimage labels vertex rest
          ((Membership.mem_cons.mp member).resolve_left (Ne.symm same))
        ⟨tail.val, List.mem_cons_of_mem _ tail.property.1, tail.property.2⟩

set_option genInjectivity false in
/-- A cached vertex reading on the actual lifted surface that agrees with the retained cut-boundary reading.

The complete finite value vector uses the original lifted vertex owner. Its
source equation identifies each retained cut-boundary starting vertex. -/
structure SurfaceVertexReading (lifted : Meshes.LiftedPuncturedGrid base) {size : Nat}
    {other : Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord) size}
    (reading : VertexReading.CutVertexReading lifted.cutBoundaryWord other lifted.cutPolygon.patch.cut.anchor) where
  /-- The cached reading at every actual lifted-surface vertex index. -/ values : Data.Vector (Fin size)
    lifted.vertices.count
  /-- Every original cut-boundary starting vertex reads back its exact retained source value. -/ source_eq : ∀ vertex ∈
    lifted.cutPolygon.patch.cut.boundary.map OrientedEdge.start,
    values (lifted.cutPolygon.patch.cut.vertexLabels vertex) = reading.values vertex

constructive_injectivity SurfaceVertexReading

namespace SurfaceVertexReading

variable {lifted : LiftedPuncturedGrid base} {size : Nat}
  {other : WordVertexRealization
    (Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord.pairedLetters lifted.cutBoundaryWord) size}
  {reading : CutVertexReading lifted.cutBoundaryWord other
    lifted.cutPolygon.patch.cut.anchor}

/-- Descend the cut reading by finite preimage lookup and the certified cut-vertex gluing relation. -/
@[expose] def build (lifted : Meshes.LiftedPuncturedGrid base)
    {other : Vertices.WordVertexRealization (CutBoundaryWord.pairedLetters lifted.cutBoundaryWord) size}
    (reading : VertexReading.CutVertexReading lifted.cutBoundaryWord other lifted.cutPolygon.patch.cut.anchor) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent.SurfaceVertexReading lifted reading :=
  let vertices := lifted.cutPolygon.patch.cut.boundary.map OrientedEdge.start
  let labels := lifted.cutPolygon.patch.cut.vertexLabels
  let value := fun vertex : Fin lifted.vertices.count =>
    if member : vertex ∈ vertices.map labels then reading.values
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent.preimage labels vertex vertices member).val
    else reading.values lifted.cutPolygon.patch.cut.anchor
  { values := Data.Vector.Basic.vectorOfFn value
    source_eq := fun vertex member => by
      rw [Data.Vector.Basic.vectorOfFn_apply]
      have projected : labels vertex ∈ vertices.map labels := Map.mem_map_of_mem member
      change (if present : labels vertex ∈ vertices.map labels then
        reading.values (Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent.preimage labels (labels vertex)
          vertices present).val else _) = _
      rw [dif_pos projected]
      let selected := Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent.preimage labels (labels vertex)
        vertices projected
      apply reading.joined_eq
      exact (VertexGluing.cutVertexJoin_iff lifted
        ((Assembly.active_iff_boundary lifted.cutPolygon.patch.assembly selected.val).mpr selected.property.1)
        ((Assembly.active_iff_boundary lifted.cutPolygon.patch.assembly vertex).mpr member)).mpr selected.property.2 }

/-- Both actual endpoints of a retained cut-boundary edge preserve their source readings. -/
theorem edge_endpoints (surface : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent.SurfaceVertexReading
  lifted reading)
    (edge : Stokes.OrientedEdge lifted.cutPolygon.patch.cut.count) (member : edge ∈
      lifted.cutPolygon.patch.cut.boundary) :
    surface.values (lifted.cutPolygon.patch.cut.vertexLabels edge.start) = reading.values edge.start ∧
      surface.values (lifted.cutPolygon.patch.cut.vertexLabels edge.finish) = reading.values edge.finish :=
  ⟨surface.source_eq _ (Map.mem_map_of_mem member),
    surface.source_eq _ (SimpleBoundaryCycles.finish_mem lifted.cutPolygon.patch.cut.closed member)⟩

/-- Every physical-boundary edge has equal values at its actual surface endpoints. -/
theorem physical_constant (surface : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent.SurfaceVertexReading
  lifted reading)
    (edge : Stokes.OrientedEdge lifted.vertices.count) (member : edge ∈ lifted.boundaryComponents.cycles.flatten) :
    surface.values edge.start = surface.values edge.finish := by
  have projected := (lifted.cut_boundary_iff_boundaryComponents edge).mpr member
  obtain ⟨original, originalMember, equal⟩ := Map.mem_map.mp projected
  have endpoints := surface.edge_endpoints original (lifted.cutBoundaryPairs.boundary_subset originalMember)
  rw [← equal]
  exact endpoints.1.trans ((reading.physical_endpoints original originalMember).trans endpoints.2.symm)

/-- The projected label of a retained cut-boundary vertex is active in the actual lifted mesh. -/
private theorem source_active (vertex : Fin lifted.cutPolygon.patch.cut.count)
    (member : vertex ∈ lifted.cutPolygon.patch.cut.boundary.map OrientedEdge.start) :
    lifted.cutPolygon.patch.cut.vertexLabels vertex ∈ (LiftedMesh.activeVertices lifted.mesh).indices :=
  ((LiftedMesh.activeVertices lifted.mesh).active_iff _).mpr ((SinglePolygon.boundary_projection_mem_iff
    lifted.cutPolygon _).mp
    (Map.mem_map_of_mem member))

/-- Factoring through the retained physical-boundary contraction preserves each original cut vertex reading. -/
theorem contracted_source (surface : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent.SurfaceVertexReading
  lifted reading)
    (contraction : Topology.Surface.Boundary.BoundaryContraction lifted.boundaryComponents (LiftedMesh.activeVertices
      lifted.mesh).indices)
    (indexed : (BoundaryContractionIndices.Indexed contraction)) (vertex : Fin lifted.cutPolygon.patch.cut.count)
    (member : vertex ∈ lifted.cutPolygon.patch.cut.boundary.map OrientedEdge.start) :
    indexed.factor surface.values (indexed.projection (lifted.cutPolygon.patch.cut.vertexLabels vertex)) =
      reading.values vertex :=
  (indexed.factor_eq surface.values surface.physical_constant
    (source_active vertex
    member)).trans (surface.source_eq vertex member)

/-- Factor the retained paired-word realization through the actual contracted surface vertices.

The resulting vertex map preserves the anchor and every kept generator edge using the same cached surface reading. -/
@[expose] def factor (surface : Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent.SurfaceVertexReading lifted
  reading)
    (contraction : Topology.Surface.Boundary.BoundaryContraction lifted.boundaryComponents (LiftedMesh.activeVertices
      lifted.mesh).indices)
    (indexed : (BoundaryContractionIndices.Indexed contraction)) : (lifted.contractedCutWordWith contraction
      indexed).Factor other where
  vertices := indexed.factor surface.values
  anchor_eq := by
    change indexed.factor surface.values (indexed.projection (lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.anchor)) = other.anchor
    have startMember : lifted.cutPolygon.patch.cut.anchor ∈ lifted.cutPolygon.patch.cut.boundary.map OrientedEdge.start
      := by
      have path := lifted.cutPolygon.patch.cut.closed
      have nonempty : lifted.cutPolygon.patch.cut.boundary ≠ [] := by
        intro empty
        have size := lifted.cutPolygon.boundaryCount
        rw [empty, List.length_nil] at size
        omega
      have initial {count : Nat} {edges : List (Stokes.OrientedEdge count)} {anchor : Fin count}
          (path : PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish edges anchor anchor)
          (nonempty : edges ≠ []) : anchor ∈ edges.map OrientedEdge.start := by
        cases path with
        | nil => exact (nonempty rfl).elim
        | cons => exact List.mem_cons_self
      exact initial path nonempty
    exact (surface.contracted_source contraction indexed _ startMember).trans reading.anchor_eq
  edge_eq := fun letter member => by
    have side : lifted.cutBoundaryWord.alphabet.oneSided letter.index = false := by
      have kept := (Filter.mem_filter.mp member).2
      cases value : lifted.cutBoundaryWord.alphabet.oneSided letter.index
      · rfl
      · change (!lifted.cutBoundaryWord.alphabet.oneSided letter.index) = true at kept
        rw [value] at kept
        cases kept
    obtain ⟨entry, entryMember, edgeEq, letterEq⟩ := ProjectedEdgePairing.boundaryWord_generator lifted.cutBoundaryPairs
      letter.index
    have edgeMember := Map.mem_map_of_mem (f := CutWordEntry.edge) entryMember
    rw [(ProjectedEdgePairing.boundaryWord lifted.cutBoundaryPairs).alphabet.edges_eq, edgeEq] at edgeMember
    have first := surface.contracted_source contraction indexed _ (Map.mem_map_of_mem edgeMember)
    have last := surface.contracted_source contraction indexed _ (SimpleBoundaryCycles.finish_mem
      lifted.cutPolygon.patch.cut.closed edgeMember)
    have kept := reading.kept entry entryMember (by rw [letterEq]; exact side)
    rw [edgeEq, letterEq] at kept
    change OrientedEdge.map _ ((Data.Vector.Basic.vectorOfFn (fun index => OrientedEdge.map
      (fun vertex => indexed.projection (lifted.cutPolygon.patch.cut.vertexLabels vertex))
      (lifted.cutBoundaryWord.alphabet.generators index))).get letter.index) = _
    rw [Data.Vector.Basic.vectorOfFn_apply]
    change OrientedEdge.mk _ _ = _
    exact (congrArg₂ OrientedEdge.mk first last).trans kept

end SurfaceVertexReading
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.VertexDescent

end
