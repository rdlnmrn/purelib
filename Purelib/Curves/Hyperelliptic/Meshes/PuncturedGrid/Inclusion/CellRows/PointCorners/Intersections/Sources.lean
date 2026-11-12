module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointCorners.Intersections.Resolve
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Topology.Mesh.TriangleCut
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.VertexSewing

/-! # The actual five signed source slots of one retained affine cut patch

The original three corner Owners and both resolved cut Points share the
same old-face Entry sheet. The whole input caches are retained. Internal
seams cancel by exact indexed occurrence identity, never coordinate keys.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Geometry.Triangles
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Mesh.CoordinateTriangulation (CoordinateTriangle)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Owner
open Purelib.Topology.Mesh
open Purelib.Topology.Surface.Sewing

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {old : RootEdgeBank frames} {face : RegularFace bank}
variable {coarse : frames.CellRestriction face.cell face.member} {points : List Canonical}
variable {cuts : CutPartition face.cell.box points} {retained : CellRows old face coarse cuts}
variable {models : FaceModels frames face} {base : Canonical}
variable {stem : Walks.Walk retained.grid face.cell.box.anchor base}
variable {member : FromStates.ContainsVertex retained.grid base}
variable {oldCount : Nat} {oldNeighborhood : ContinuedNeighborhood curve.polynomial oldCount}
variable {oldSample : ContinuedNeighborhood.Point oldNeighborhood base}
variable {classified : retained.PointEntry models stem member oldSample}
variable {located : ClearGrid.CornerLocation retained.grid base} {vertices : VertexBank retained.grid}
variable (lifted : classified.CellLift located vertices)

variable {lineFirst lineLast : Canonical} {triangle : CoordinateTriangle}
variable {apex : AffineCut.Apex lineFirst lineLast triangle}
variable (crossing : AffineCut.CrossingCache lineFirst lineLast triangle apex) (position : Fin 2)
variable (factory : triangle =
  ⟨vertices.coordinate (lifted.cell.quad.faces position).first,
    vertices.coordinate (lifted.cell.quad.faces position).second,
    vertices.coordinate (lifted.cell.quad.faces position).third⟩)

/-- One actual root Owner with its derived Entry on this SAME retained old-face sheet. -/
abbrev SignedVertex (point : Canonical) :=
  Σ owner : Owner (curve.polynomial.eval point),
    {entry : Entry models point owner // entry.sheet = classified.entry.sheet}

/-- Reindex one whole original Entry along its exact coordinate equation. -/
private def castEntry {point next : Canonical} (same : point = next)
    {owner : Owner (curve.polynomial.eval next)} (entry : Entry models next owner) :
    Entry models point (Transport.castOwnerParameter (congrArg curve.polynomial.eval same.symm) owner) := by
  cases same
  exact entry

/-- Exact endpoint reindexing preserves the original Entry's sheet. -/
private theorem castEntry_sheet {point next : Canonical} (same : point = next)
    {owner : Owner (curve.polynomial.eval next)} (entry : Entry models next owner) :
    (castEntry (curve := curve) same entry).sheet = entry.sheet := by
  cases same
  rfl

/-- Exact endpoint reindexing preserves this SAME original Owner's root name. -/
private theorem castName {point next : Canonical} (same : point = next)
    (owner : Owner (curve.polynomial.eval next)) :
    ownerName (Transport.castOwnerParameter (congrArg curve.polynomial.eval same.symm) owner) =
      ownerName owner := by
  cases same
  rfl

/-- Read an original rotated corner Owner and Entry, changing only its exact coordinate index. -/
def originalVertex (corner : Fin 3) : SignedVertex (models := models) (classified := classified)
    (AffineCut.corner crossing.original corner) :=
  let entry := lifted.sourceEntry position (AffineCut.cornerIndex apex.1 corner)
  let same := crossing.original_corner vertices.coordinate (lifted.cell.quad.faces position) factory corner
  ⟨Transport.castOwnerParameter (congrArg curve.polynomial.eval same.symm)
      (vertices.owner retained.localFrames
        (SewnPrimitiveFaces.corner (lifted.cell.quad.faces position) (AffineCut.cornerIndex apex.1 corner))),
    ⟨castEntry (curve := curve) same entry.val, (castEntry_sheet (curve := curve) same entry.val).trans entry.property⟩⟩

/-- The original corner vertex keeps the SAME old bank Owner under its pure coordinate-index transport. -/
theorem originalVertex_owner_heq (corner : Fin 3) :
    HEq (lifted.originalVertex crossing position factory corner).1
      (vertices.owner retained.localFrames
        (SewnPrimitiveFaces.corner (lifted.cell.quad.faces position) (AffineCut.cornerIndex apex.1 corner))) :=
  Transport.castOwnerParameter_heq _ _

namespace Resolved

variable {lifted crossing position factory} {side : Fin 2}
variable {available : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) side).finish)}
variable {count : Nat} (resolved : lifted.Resolved crossing position factory side available count)

/-- Read the actual resolved Point Owner and derive its SAME old-face Entry.

Strict work reads the retained TracedPoint Entry. Endpoint work transports
the actual original corner Entry and consumes the SAME old Point's cached
selection. The endpoint Point and bank Owner remain distinct; their
signed comparison comes from that selection, not coordinate equality.
-/
def vertex : SignedVertex (models := models) (classified := classified) (crossing.point side) :=
  match resolved with
  | .inl strict =>
      let prepared := strict.2.val.prepared
      ⟨prepared.sample.owner, ⟨prepared.entry, prepared.entry_sheet⟩⟩
  | .inr endpoint =>
      let cached := endpoint.2
      let same := lifted.cut_endpoint crossing position factory side endpoint.1.property
      let old := (lifted.cutFinish (apex := apex) position side).val
      let moved := castEntry (curve := curve) same old
      let equivalent := NamedEquivalent.transport
        (castName (curve := curve) same
          (vertices.owner retained.localFrames (apex.edge (lifted.cell.quad.faces position) side).finish)).symm
        rfl cached.2.2.val
      let entry := moved.followEquivalent equivalent
      ⟨cached.2.1.val.owner,
        ⟨entry, (moved.followEquivalent_sheet equivalent).trans
          ((castEntry_sheet (curve := curve) same old).trans (lifted.cutFinish (apex := apex) position side).property)⟩⟩

/-- A strict signed vertex reads the Owner of its SAME retained newly prepared Point. -/
theorem vertex_owner_strict
    (strict : Σ _ : {_value : Unit // crossing.time side < 1},
      {value : lifted.PreparedSide crossing position factory side count //
        value = lifted.prepareSide crossing position factory side count}) :
    (vertex (Sum.inl strict : lifted.Resolved crossing position factory side available count)).1 =
      strict.2.val.prepared.sample.owner := by rfl

/-- A unit signed vertex reads the Owner of its SAME retained endpoint-reindexed Point. -/
theorem vertex_owner_unit
    (endpoint : Σ atEnd : {_value : Unit // crossing.time side = 1},
      lifted.EndpointAt crossing position factory side available atEnd.property) :
    (vertex (Sum.inr endpoint : lifted.Resolved crossing position factory side available count)).1 =
      endpoint.2.2.1.val.owner := by rfl

end Resolved

/-- Materialize the original five ordered source slots from two actual retained signed cut vertices.

Original corners still read the actual source-face/corner Entries. Both
cut vertices are supplied existing caches, without a final relation or a
claim about how their preparation was obtained. Shared and local target
consumers therefore use the same original finite branch operation.
-/
def sourceAt (leading : SignedVertex (models := models) (classified := classified) (crossing.point 0))
    (trailing : SignedVertex (models := models) (classified := classified) (crossing.point 1)) :
    (slot : Fin 5) → SignedVertex (models := models) (classified := classified) (crossing.coordinate slot) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun impossible => nomatch impossible)))))
  · exact Eq.mpr (congrArg (SignedVertex (models := models) (classified := classified))
      (crossing.coordinate_zero.trans (AffineCut.corner_zero crossing.original).symm))
      (lifted.originalVertex crossing position factory 0)
  · exact Eq.mpr (congrArg (SignedVertex (models := models) (classified := classified)) crossing.coordinate_one)
      leading
  · exact Eq.mpr (congrArg (SignedVertex (models := models) (classified := classified))
      (crossing.coordinate_two.trans (AffineCut.corner_one crossing.original).symm))
      (lifted.originalVertex crossing position factory 1)
  · exact Eq.mpr (congrArg (SignedVertex (models := models) (classified := classified))
      (crossing.coordinate_three.trans (AffineCut.corner_two crossing.original).symm))
      (lifted.originalVertex crossing position factory 2)
  · exact Eq.mpr (congrArg (SignedVertex (models := models) (classified := classified)) crossing.coordinate_four)
      trailing

variable (firstAvailable : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) 0).finish))
variable (lastAvailable : Option
  (retained.VertexPoint models vertices (apex.edge (lifted.cell.quad.faces position) 1).finish))
variable (count : Nat)
variable (first : lifted.Resolved crossing position factory 0 firstAvailable count)
variable (last : lifted.Resolved crossing position factory 1 lastAvailable count)

/-- Compute the five exact signed source occurrences from the actual resolved cut caches. -/
def sourceVertex : (slot : Fin 5) →
    SignedVertex (models := models) (classified := classified) (crossing.coordinate slot) :=
  lifted.sourceAt crossing position factory first.vertex last.vertex

/-- The original resolved constructor is the SAME whole source-slot operation on its actual two cached vertices. -/
theorem sourceVertex_eq : sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last =
    lifted.sourceAt crossing position factory first.vertex last.vertex := by rfl

/-- Retain both complete operational cut results and all five actual signed vertices.

The five-slot product retains repeated or collapsed geometric occurrences.
No RootEdgeBank, complete GridLiftedMesh, numerical observation bank or
primitive normalization is manufactured by this data construction.
-/
abbrev SourceBank :=
  {value : classified.CellLift located vertices × AffineCut.CrossingCache lineFirst lineLast triangle apex //
    value = (lifted, crossing)} ×
  {value : lifted.Resolved crossing position factory 0 firstAvailable count ×
      lifted.Resolved crossing position factory 1 lastAvailable count // value = (first, last)} ×
  {value : SignedVertex (models := models) (classified := classified) (crossing.coordinate 0) ×
      SignedVertex (models := models) (classified := classified) (crossing.coordinate 1) ×
      SignedVertex (models := models) (classified := classified) (crossing.coordinate 2) ×
      SignedVertex (models := models) (classified := classified) (crossing.coordinate 3) ×
      SignedVertex (models := models) (classified := classified) (crossing.coordinate 4) //
    value = (sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 0,
      sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 1,
      sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 2,
      sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 3,
      sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 4)}

/-- Materialize the actual signed source bank once after both precise preparation attempts succeed. -/
def sourceBank : lifted.SourceBank crossing position factory firstAvailable lastAvailable count first last :=
  let zero := sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 0
  let one := sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 1
  let two := sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 2
  let three := sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 3
  let four := sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 4
  (⟨(lifted, crossing), rfl⟩, ⟨(first, last), rfl⟩, ⟨(zero, one, two, three, four), rfl⟩)

namespace SourceBank

variable {lifted crossing position factory firstAvailable lastAvailable count first last}
variable (cached : lifted.SourceBank crossing position factory firstAvailable lastAvailable count first last)

/-- Read the SAME original signed quad cache. -/
def original : classified.CellLift located vertices := cached.1.val.1

/-- Read the SAME original cut, including its actual sewn CutPatch. -/
def cut : AffineCut.CrossingCache lineFirst lineLast triangle apex := cached.1.val.2

/-- Read both complete original cut results, including their actual Point/Entry/OwnerJoin caches. -/
def resolved : lifted.Resolved crossing position factory 0 firstAvailable count ×
    lifted.Resolved crossing position factory 1 lastAvailable count := cached.2.1.val

/-- Read one actual stored signed vertex without executing any Point/Entry/connection factory. -/
def vertex : (slot : Fin 5) → SignedVertex (models := models) (classified := classified)
    (crossing.coordinate slot) :=
  Fin.cases cached.2.2.val.1 (Fin.cases cached.2.2.val.2.1
    (Fin.cases cached.2.2.val.2.2.1 (Fin.cases cached.2.2.val.2.2.2.1
      (Fin.cases cached.2.2.val.2.2.2.2 (fun impossible => nomatch impossible)))))

/-- The whole original quad cache is preserved exactly. -/
theorem original_eq : cached.original = lifted := congrArg Prod.fst cached.1.property

/-- The whole original cut cache is preserved exactly. -/
theorem cut_eq : cached.cut = crossing := congrArg Prod.snd cached.1.property

/-- Both complete actual cut results are preserved, without re-executing either preparation. -/
theorem resolved_eq : cached.resolved = (first, last) := cached.2.1.property

/-- The whole five-slot product is the original source-vertex constructor on these SAME resolved caches. -/
theorem vertices_eq : cached.2.2.val =
    (sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 0,
      sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 1,
      sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 2,
      sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 3,
      sourceVertex lifted crossing position factory firstAvailable lastAvailable count first last 4) :=
  cached.2.2.property

/-- Inverse transports cancel for one whole retained dependent value. -/
private theorem mp_mpr {first last : Sort u} (same : first = last) (value : last) :
    Eq.mp same (Eq.mpr same value) = value := by
  cases same
  rfl

/-- The first stored cut slot is the SAME whole original resolved signed vertex after exact coordinate reindexing. -/
theorem first_vertex :
    Eq.mp (congrArg (SignedVertex (models := models) (classified := classified)) crossing.coordinate_one)
      (cached.vertex 1) = first.vertex := by
  have selected := congrArg (fun value => value.2.1) cached.vertices_eq
  exact (congrArg (Eq.mp
    (congrArg (SignedVertex (models := models) (classified := classified)) crossing.coordinate_one)) selected).trans
      (mp_mpr _ first.vertex)

/-- The last stored cut slot is the SAME whole original resolved signed vertex after exact coordinate reindexing. -/
theorem last_vertex :
    Eq.mp (congrArg (SignedVertex (models := models) (classified := classified)) crossing.coordinate_four)
      (cached.vertex 4) = last.vertex := by
  have selected := congrArg (fun value => value.2.2.2.2) cached.vertices_eq
  exact (congrArg (Eq.mp
    (congrArg (SignedVertex (models := models) (classified := classified)) crossing.coordinate_four)) selected).trans
      (mp_mpr _ last.vertex)

/-- The stored a slot is the SAME whole original apex corner after exact coordinate reindexing. -/
theorem first_corner_vertex :
    Eq.mp (congrArg (SignedVertex (models := models) (classified := classified))
      (crossing.coordinate_zero.trans (AffineCut.corner_zero crossing.original).symm))
      (cached.vertex 0) = lifted.originalVertex crossing position factory 0 := by
  have selected := congrArg (fun value => value.1) cached.vertices_eq
  exact (congrArg (Eq.mp (congrArg (SignedVertex (models := models) (classified := classified))
    (crossing.coordinate_zero.trans (AffineCut.corner_zero crossing.original).symm))) selected).trans
      (mp_mpr _ (lifted.originalVertex crossing position factory 0))

/-- The stored b slot is the SAME whole second original corner after its actual coordinate reindexing. -/
theorem second_corner_vertex :
    Eq.mp (congrArg (SignedVertex (models := models) (classified := classified))
      (crossing.coordinate_two.trans (AffineCut.corner_one crossing.original).symm))
      (cached.vertex 2) = lifted.originalVertex crossing position factory 1 := by
  have selected := congrArg (fun value => value.2.2.1) cached.vertices_eq
  exact (congrArg (Eq.mp (congrArg (SignedVertex (models := models) (classified := classified))
    (crossing.coordinate_two.trans (AffineCut.corner_one crossing.original).symm))) selected).trans
      (mp_mpr _ (lifted.originalVertex crossing position factory 1))

/-- The stored c slot is the SAME whole third original corner after its actual coordinate reindexing. -/
theorem third_corner_vertex :
    Eq.mp (congrArg (SignedVertex (models := models) (classified := classified))
      (crossing.coordinate_three.trans (AffineCut.corner_two crossing.original).symm))
      (cached.vertex 3) = lifted.originalVertex crossing position factory 2 := by
  have selected := congrArg (fun value => value.2.2.2.1) cached.vertices_eq
  exact (congrArg (Eq.mp (congrArg (SignedVertex (models := models) (classified := classified))
    (crossing.coordinate_three.trans (AffineCut.corner_two crossing.original).symm))) selected).trans
      (mp_mpr _ (lifted.originalVertex crossing position factory 2))

/-- Every actual source vertex has the derived SAME old-face sheet. -/
theorem vertex_sheet (slot : Fin 5) : (cached.vertex slot).2.val.sheet = classified.entry.sheet :=
  (cached.vertex slot).2.property

/-- The signed source name at an actual bounded refined slot. -/
def name (slot : Fin 5) : Named := ownerName (cached.vertex slot).1

/-- Opposite sewn child occurrences read the SAME exact retained signed endpoint, in opposite order.

The proof uses the original source-face/corner projection and indexed
seam equation. It does not reverse an operational path, identify two
independent selections, cancel observation errors or primitive constants.
-/
theorem seam_names (seam : Fin 2) :
    (cached.name ((TriangleCut.seamSources seam).2.project TriangleCut.faces).start,
      cached.name ((TriangleCut.seamSources seam).2.project TriangleCut.faces).finish) =
    (cached.name ((TriangleCut.seamSources seam).1.project TriangleCut.faces).finish,
      cached.name ((TriangleCut.seamSources seam).1.project TriangleCut.faces).start) := by
  have same := TriangleCut.seamSources_opposite seam
  exact Prod.ext
    (congrArg cached.name ((congrArg OrientedEdge.start same).trans (OrientedEdge.reverse_start _)))
    (congrArg cached.name ((congrArg OrientedEdge.finish same).trans (OrientedEdge.reverse_finish _)))

/-- The two actual child-source seam pairs are the SAME retained patch's ordered seam labels. -/
theorem seam_occurrences :
    [(TriangleCut.seamSources 0).1.project TriangleCut.faces,
      (TriangleCut.seamSources 1).1.project TriangleCut.faces] =
      cached.cut.patch.seams.map (VertexSewing.OrientedEdge.map cached.cut.patch.vertexLabels) := by
  rw [cached.cut.patch_eq]
  exact TriangleCut.seamSources_project

/-- Equal actual bounded occurrences retain the whole SAME signed vertex, including its Owner and Entry. -/
private theorem vertex_heq {first last : Fin 5} (same : first = last) :
    HEq (cached.vertex first) (cached.vertex last) := by
  cases same
  rfl

/-- The two internal sewn occurrences reuse whole signed vertices in opposite order.

Both actual Point/Entry inputs are retained in the bank. This identity
is stronger than equality of coordinate or name labels, and weaker than
an unproved equality of separately prepared opposite operational paths.
-/
theorem seam_vertices (seam : Fin 2) :
    HEq (cached.vertex ((TriangleCut.seamSources seam).2.project TriangleCut.faces).start)
      (cached.vertex ((TriangleCut.seamSources seam).1.project TriangleCut.faces).finish) ∧
    HEq (cached.vertex ((TriangleCut.seamSources seam).2.project TriangleCut.faces).finish)
      (cached.vertex ((TriangleCut.seamSources seam).1.project TriangleCut.faces).start) := by
  have same := TriangleCut.seamSources_opposite seam
  exact ⟨cached.vertex_heq
      ((congrArg OrientedEdge.start same).trans (OrientedEdge.reverse_start _)),
    cached.vertex_heq ((congrArg OrientedEdge.finish same).trans (OrientedEdge.reverse_finish _))⟩

end SourceBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

end
