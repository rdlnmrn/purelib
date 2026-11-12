module

public import Purelib.Riemann.Readings.RectangularPointReadings.Chord
public import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh
public import Purelib.Data.Vector.Dependent
public import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Integration.RectangularSharedPrimitives
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Vector.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Tactic.Ring

/-! # One shared numerical mesh for the literal slots of a retained split

The point list keeps start, corner and finish for each original piece.
Triangle role indices retain corner, start and finish in that order.
One common mesh and one primitive-reading vector are built before
the point lookups and triangle views. Repeated coordinates retain their
original list and dependent-vector occurrences. No root, Entry, geometric
path or canonical-cycle incidence is inferred from these numerical views.
-/

public section

namespace Purelib.Riemann.Readings.RectangularPointReadings

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex ModelTriangle OwnedTriangulation)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Integration.RectangularSharedPrimitives (SharedPrimitiveValues)
open Purelib.Riemann.Integration.PreparedParentSplitting.Geometry (allCells_mem)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentSplit)
open Purelib.Riemann.Paths
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Topology.Mesh.CoordinateTriangulation (VertexLookup)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing

variable {columns rows : Nat} {geometry : Geometry columns rows}
    {polynomial numerator : Polynomial} {models : Bank polynomial geometry}
    {primitives : Primitives models numerator} {anchors : PrimitiveAnchors primitives}
    {offsets : Offsets anchors.edges}

namespace PointReadings

/-- Index an actual shared value cache without evaluating a primitive or replacing its retained cell owners. -/
def ofShared {triangles : List (ModelTriangle geometry)} {surface : OwnedTriangulation triangles}
    (readings : SharedPrimitiveValues anchors offsets surface) {count : Nat}
    (vertices : Fin count → Fin surface.mesh.vertices.length) (points : Fin count → Canonical)
    (equal : ∀ slot, surface.mesh.coordinate (vertices slot) = points slot) :
    PointReadings anchors offsets points where
  owners := vectorOfFn fun slot => surface.owners (vertices slot)
  point_eq := fun slot =>
    (congrArg OwnedVertex.point (vectorOfFn_apply (fun slot => surface.owners (vertices slot)) slot)).trans
      ((surface.point_eq (vertices slot)).trans (equal slot))
  values := vectorOfFn fun slot => readings.values (vertices slot)
  value_eq := fun slot =>
    (vectorOfFn_apply (fun slot => readings.values (vertices slot)) slot).trans
      ((readings.value_eq (vertices slot)).trans
        (congrArg (fun owner : OwnedVertex geometry =>
          anchors.alignedValue offsets owner.column owner.row owner.point)
          (vectorOfFn_apply (fun slot => surface.owners (vertices slot)) slot).symm))

/-- Each indexed view retains the original shared mesh's complete cell owner at that slot. -/
theorem ofShared_owner {triangles : List (ModelTriangle geometry)} {surface : OwnedTriangulation triangles}
    (readings : SharedPrimitiveValues anchors offsets surface) {count : Nat}
    (vertices : Fin count → Fin surface.mesh.vertices.length) (points : Fin count → Canonical)
    (equal : ∀ slot, surface.mesh.coordinate (vertices slot) = points slot) (slot : Fin count) :
    (ofShared readings vertices points equal).owners slot = surface.owners (vertices slot) := by
  change (vectorOfFn fun slot => surface.owners (vertices slot)) slot = _
  exact vectorOfFn_apply _ slot

/-- Each indexed value is the actual cached shared reading, with no numerical evaluation replay. -/
theorem ofShared_value {triangles : List (ModelTriangle geometry)} {surface : OwnedTriangulation triangles}
    (readings : SharedPrimitiveValues anchors offsets surface) {count : Nat}
    (vertices : Fin count → Fin surface.mesh.vertices.length) (points : Fin count → Canonical)
    (equal : ∀ slot, surface.mesh.coordinate (vertices slot) = points slot) (slot : Fin count) :
    (ofShared readings vertices points equal).values slot = readings.values (vertices slot) := by
  change (vectorOfFn fun slot => readings.values (vertices slot)) slot = _
  exact vectorOfFn_apply _ slot

end PointReadings

namespace Chord

variable {cuts : GridCuts geometry} {first last : Canonical} (split : SegmentSplit cuts first last)

/-- Retain each original split occurrence's start, mixed-coordinate corner and finish in point-bank order. -/
def slots : List Canonical :=
  (List.ofFn fun position : Fin split.pieces.length =>
    let piece := split.pieces[position.val]'position.isLt
    [piece.firstPoint, ClearBoxPaths.Chord.corner piece.firstPoint piece.lastPoint, piece.lastPoint]).flatten

/-- Each literal triangle slot occurs in the same ordered point bank, including coincident coordinates. -/
theorem slots_mem (position : Fin split.pieces.length) (slot : Fin 3) :
    ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
      (split.pieces[position.val]'position.isLt).lastPoint slot ∈ slots split := by
  let piece := split.pieces[position.val]'position.isLt
  have outer : [piece.firstPoint, ClearBoxPaths.Chord.corner piece.firstPoint piece.lastPoint, piece.lastPoint] ∈
      List.ofFn (fun position : Fin split.pieces.length =>
        let piece := split.pieces[position.val]'position.isLt
        [piece.firstPoint, ClearBoxPaths.Chord.corner piece.firstPoint piece.lastPoint, piece.lastPoint]) :=
    OfFn.Basic.mem_ofFn.mpr ⟨position, rfl⟩
  apply mem_flatten_of_mem outer
  have coordinates := ClearBoxPaths.Chord.coordinate_values piece.firstPoint piece.lastPoint
  exact Fin.cases
    (coordinates.1.symm ▸ List.mem_cons_of_mem _ List.mem_cons_self)
    (Fin.cases (coordinates.2.1.symm ▸ List.mem_cons_self)
      (Fin.cases (coordinates.2.2.symm ▸ List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self)) (fun index => Fin.elim0 index))) slot

/-- The three original triangle slots lie in the same retained containing cell of that actual split occurrence. -/
theorem slot_inside (position : Fin split.pieces.length) (slot : Fin 3) :
    (geometry.box (split.pieces[position.val]'position.isLt).column
      (split.pieces[position.val]'position.isLt).row).Contains
      (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
        (split.pieces[position.val]'position.isLt).lastPoint slot) :=
  ClearBoxPaths.Chord.coordinate_inside (split.pieces[position.val]'position.isLt).first_inside
    (split.pieces[position.val]'position.isLt).last_inside slot

/-- The exact common mesh over all original cells and the ordered literal split slots. -/
abbrev Mesh := CommonMesh geometry (RectangularExteriorBoundary.Geometry.allCells geometry) (slots split)

/-- The stored lookup family preserves the original piece index and each of its three literal roles. -/
@[expose] def Lookups (mesh : Mesh split) :=
  DependentVector fun position : Fin split.pieces.length =>
    DependentVector fun slot : Fin 3 => VertexLookup mesh.surface.mesh.vertices
      (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
        (split.pieces[position.val]'position.isLt).lastPoint slot)

/-- The exact finite lookup used for one original piece and slot on the given common mesh. -/
def lookup (mesh : Mesh split) (position : Fin split.pieces.length) (slot : Fin 3) :
    VertexLookup mesh.surface.mesh.vertices
      (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
        (split.pieces[position.val]'position.isLt).lastPoint slot) :=
  mesh.lookup _ (slots_mem split position slot) _ _
    (allCells_mem _ _ _) (slot_inside split position slot)

/-- The original checked lookup is the same complete first-occurrence lookup, regardless of its membership proof. -/
theorem lookup_first (mesh : Mesh split) (position : Fin split.pieces.length) (slot : Fin 3)
    (member : ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
      (split.pieces[position.val]'position.isLt).lastPoint slot ∈ mesh.surface.mesh.vertices) :
    lookup split mesh position slot = Topology.Mesh.CoordinateTriangulation.lookupVertex
      (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
        (split.pieces[position.val]'position.isLt).lastPoint slot) mesh.surface.mesh.vertices member := by
  unfold lookup
  rfl

/-- Materialize all original piece and slot lookups once, without discarding repeated occurrences. -/
def lookupBank (mesh : Mesh split) : Lookups split mesh :=
  DependentVector.ofFn fun position => DependentVector.ofFn fun slot => lookup split mesh position slot

/-- Each original split occurrence retains its own triangle view on the unchanged primitive owners. -/
@[expose] def Triangles (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges) :=
  DependentVector fun position : Fin split.pieces.length => PointReadings anchors offsets
    (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
      (split.pieces[position.val]'position.isLt).lastPoint)

/-- Materialize triangle views by indexing only the actual shared numerical cache and stored lookups. -/
def triangleBank (mesh : Mesh split) (readings : SharedPrimitiveValues anchors offsets mesh.surface)
    (lookups : Lookups split mesh) : Triangles split anchors offsets :=
  DependentVector.ofFn fun position =>
    PointReadings.ofShared readings (fun slot => ((lookups.get position).get slot).index)
      (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
        (split.pieces[position.val]'position.isLt).lastPoint)
      (fun slot => ((lookups.get position).get slot).coordinate_eq)

/-- One actual common mesh, shared value cache, materialized lookups and indexed triangle views.

Every component carries its original whole factory equation. The tuple
adds no geometry or primitive owner and does not copy an Entry, domain,
root comparison, source model or physical child preparation.
-/
abbrev MeshReadings (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges) :=
  (mesh : {value : Mesh split // value = CommonMesh.build geometry
    (RectangularExteriorBoundary.Geometry.allCells geometry) (slots split)}) ×
  (shared : {value : SharedPrimitiveValues anchors offsets mesh.val.surface //
    value = SharedPrimitiveValues.build anchors offsets mesh.val.surface}) ×
  (lookups : {value : Lookups split mesh.val // value = lookupBank split mesh.val}) ×
  {value : Triangles split anchors offsets // value = triangleBank split mesh.val shared.val lookups.val}

namespace MeshReadings

variable (anchors : PrimitiveAnchors primitives) (offsets : Offsets anchors.edges)

/-- Build the common mesh and shared primitive values once, then store all lookup and view entries from those caches. -/
def build : MeshReadings split anchors offsets :=
  let mesh := CommonMesh.build geometry (RectangularExteriorBoundary.Geometry.allCells geometry) (slots split)
  let readings := SharedPrimitiveValues.build anchors offsets mesh.surface
  let lookups := lookupBank split mesh
  let triangles := triangleBank split mesh readings lookups
  ⟨⟨mesh, rfl⟩, ⟨readings, rfl⟩, ⟨lookups, rfl⟩, ⟨triangles, rfl⟩⟩

variable {anchors offsets} (cached : MeshReadings split anchors offsets)

/-- Read the same retained common mesh. -/
@[expose] def mesh : Mesh split := cached.1.val

/-- Read the same complete primitive-reading cache on the retained mesh. -/
@[expose] def shared : SharedPrimitiveValues anchors offsets (mesh split cached).surface := cached.2.1.val

/-- Read the materialized original lookup bank. -/
@[expose] def lookups : Lookups split (mesh split cached) := cached.2.2.1.val

/-- Read the materialized original triangle views. -/
@[expose] def triangles : Triangles split anchors offsets := cached.2.2.2.val

/-- The retained mesh has the original whole common-mesh factory, without a new preparation. -/
theorem mesh_eq : mesh split cached = CommonMesh.build geometry
    (RectangularExteriorBoundary.Geometry.allCells geometry) (slots split) := cached.1.property

/-- The shared readings were built on that same retained mesh with the actual primitive, anchor and offset owners. -/
theorem shared_eq : shared split cached =
    SharedPrimitiveValues.build anchors offsets (mesh split cached).surface := cached.2.1.property

/-- Each original lookup is the checked lookup on the same retained common mesh. -/
theorem lookup_eq (position : Fin split.pieces.length) (slot : Fin 3) :
    ((lookups split cached).get position).get slot = lookup split (mesh split cached) position slot := by
  calc
    _ = ((lookupBank split (mesh split cached)).get position).get slot :=
      congrArg (fun bank : Lookups split (mesh split cached) => (bank.get position).get slot)
        cached.2.2.1.property
    _ = _ := by
      change ((DependentVector.ofFn (fun current : Fin split.pieces.length =>
        DependentVector.ofFn (fun child : Fin 3 => lookup split (mesh split cached) current child))).get
          position).get slot = _
      rewrite [DependentVector.ofFn_get]
      exact DependentVector.ofFn_get _ slot

/-- Each actual triangle view is indexed from the retained shared cache and the retained lookup entries. -/
theorem triangle_eq (position : Fin split.pieces.length) :
    (triangles split cached).get position =
      PointReadings.ofShared (shared split cached)
        (fun slot => (((lookups split cached).get position).get slot).index)
        (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
          (split.pieces[position.val]'position.isLt).lastPoint)
        (fun slot => (((lookups split cached).get position).get slot).coordinate_eq) :=
  (congrArg (fun bank : Triangles split anchors offsets => bank.get position) cached.2.2.2.property).trans
    (DependentVector.ofFn_get _ position)

/-- The actual triangle value is the same original shared value at its retained lookup index. -/
theorem triangle_value (position : Fin split.pieces.length) (slot : Fin 3) :
    ((triangles split cached).get position).values slot =
      (shared split cached).values (((lookups split cached).get position).get slot).index :=
  (congrArg (fun reading : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
        (split.pieces[position.val]'position.isLt).lastPoint) => reading.values slot)
    (triangle_eq split cached position)).trans (PointReadings.ofShared_value _ _ _ _ slot)

/-- The actual triangle keeps the same complete original mesh cell owner at each retained slot. -/
theorem triangle_owner (position : Fin split.pieces.length) (slot : Fin 3) :
    ((triangles split cached).get position).owners slot =
      (mesh split cached).surface.owners (((lookups split cached).get position).get slot).index :=
  (congrArg (fun reading : PointReadings anchors offsets
      (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
        (split.pieces[position.val]'position.isLt).lastPoint) => reading.owners slot)
    (triangle_eq split cached position)).trans (PointReadings.ofShared_owner _ _ _ _ slot)

/-- Map both retained axis-leg occurrences through the original three stored vertex lookups. -/
def word (position : Fin split.pieces.length) : List (OrientedEdge (mesh split cached).surface.mesh.vertices.length) :=
  [⟨(((lookups split cached).get position).get 1).index,
      (((lookups split cached).get position).get 0).index⟩,
    ⟨(((lookups split cached).get position).get 0).index,
      (((lookups split cached).get position).get 2).index⟩]

/-- The complete indexed word retains both actual axis-leg occurrences, including stationary legs. -/
theorem word_eq (position : Fin split.pieces.length) : word split cached position =
    [⟨(((lookups split cached).get position).get 1).index,
        (((lookups split cached).get position).get 0).index⟩,
      ⟨(((lookups split cached).get position).get 0).index,
        (((lookups split cached).get position).get 2).index⟩] := by
  unfold word
  rfl

/-- The local chord route reads the actual shared bank on the same two ordered indexed leg occurrences. -/
theorem wordValue_eq (position : Fin split.pieces.length) :
    SewingRetraction.wordValue
      (fun edge : OrientedEdge 3 => ((triangles split cached).get position).values edge.finish -
        ((triangles split cached).get position).values edge.start) ClearBoxPaths.Chord.incidence.path =
      SewingRetraction.wordValue
        (fun edge : OrientedEdge (mesh split cached).surface.mesh.vertices.length =>
          (shared split cached).values edge.finish - (shared split cached).values edge.start)
        (word split cached position) := by
  rewrite [ClearBoxPaths.Chord.incidence_path]
  change (((triangles split cached).get position).values 0 -
      ((triangles split cached).get position).values 1) +
      ((((triangles split cached).get position).values 2 -
        ((triangles split cached).get position).values 0) + 0) = _
  exact congrArg₂ (fun first last : Canonical => first + (last + 0))
    (congrArg₂ (fun last first : Canonical => last - first)
      (triangle_value split cached position 0) (triangle_value split cached position 1))
    (congrArg₂ (fun last first : Canonical => last - first)
      (triangle_value split cached position 2) (triangle_value split cached position 0))

/-- The full retained signed local triangle correction cancels on these same three cached numerical values. -/
theorem correction_zero (position : Fin split.pieces.length) :
    SewingRetraction.faceValue ClearBoxPaths.Chord.faces
      (fun edge : OrientedEdge 3 => ((triangles split cached).get position).values edge.finish -
        ((triangles split cached).get position).values edge.start)
      ClearBoxPaths.Chord.incidence.correction = 0 := by
  rewrite [ClearBoxPaths.Chord.incidence_correction]
  change ((1 : Int) : Canonical) * SewingRetraction.wordValue
    (fun edge : OrientedEdge 3 => ((triangles split cached).get position).values edge.finish -
      ((triangles split cached).get position).values edge.start)
    (ClearBoxPaths.Chord.faces 0).boundary + 0 = 0
  rewrite [ClearBoxPaths.Chord.faces_zero]
  change ((1 : Int) : Canonical) * ((((triangles split cached).get position).values 1 -
      ((triangles split cached).get position).values 0) +
      ((((triangles split cached).get position).values 2 -
        ((triangles split cached).get position).values 1) +
        ((((triangles split cached).get position).values 0 -
          ((triangles split cached).get position).values 2) + 0))) + 0 = 0
  have cancel (first second third : Canonical) :
      ((1 : Int) : Canonical) * ((second - first) + ((third - second) + ((first - third) + 0))) + 0 = 0 := by
    ring1
  exact cancel _ _ _

/-- The shared endpoint increment equals the same indexed route by the actual retained signed correction identity. -/
theorem endpoint_increment_eq (position : Fin split.pieces.length) :
    (shared split cached).values (((lookups split cached).get position).get 2).index -
        (shared split cached).values (((lookups split cached).get position).get 1).index =
      SewingRetraction.wordValue
        (fun edge : OrientedEdge (mesh split cached).surface.mesh.vertices.length =>
          (shared split cached).values edge.finish - (shared split cached).values edge.start)
        (word split cached position) := by
  have actual := ClearBoxPaths.Chord.incidence.value_eq
    (fun edge : OrientedEdge 3 => ((triangles split cached).get position).values edge.finish -
      ((triangles split cached).get position).values edge.start)
    (fun edge =>
      (congrArg₂ (fun last first : Fin 3 =>
        ((triangles split cached).get position).values last -
          ((triangles split cached).get position).values first)
        (OrientedEdge.reverse_finish edge) (OrientedEdge.reverse_start edge)).trans
        (Field.sub_eq_neg_sub
          (((triangles split cached).get position).values edge.start)
          (((triangles split cached).get position).values edge.finish)))
  rewrite [correction_zero split cached position, Basic.add_zero] at actual
  have endpoints := congrArg₂ (fun last first : Canonical => last - first)
    (triangle_value split cached position 2) (triangle_value split cached position 1)
  exact endpoints.symm.trans (actual.trans (wordValue_eq split cached position))

end MeshReadings

end Chord

end Purelib.Riemann.Readings.RectangularPointReadings

end
