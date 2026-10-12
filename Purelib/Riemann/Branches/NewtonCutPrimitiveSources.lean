module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.TriangleComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.List.Permutation
import Purelib.Data.List.Map
public import Purelib.Data.List.Membership
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
import Purelib.Topology.Surface.Sewing.SewnPathAreaRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Vector.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# The retained Newton tour on actual cut-triangle occurrences

Lift each original source occurrence through the cut polygon's complete
face list. The chosen corners, orientation and source identity are retained;
later samples use these same cut vertices and the existing sewn face bank.
The resulting edge list need not be connected in the cut polygon. Its
increment polygon is therefore kept distinct from its raw edge area.
-/

namespace Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces

open Purelib.Data.List

open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (corner)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary (TriangleEdgeOwner)
open Purelib.Topology.Surface.Sewing.SewnPrimitivePaths.SewnPrimitiveFaces (OrientedOwner PathSources)

/-- The original forward cyclic ordering of two corners in a three-corner triangle. -/
@[expose] def cyclicCorners (first last : Fin 3) : Prop :=
  (first = 0 ∧ last = 1) ∨ (first = 1 ∧ last = 2) ∨ (first = 2 ∧ last = 0)

/-- Decide the original finite cyclic-corner relation. -/
instance (first last : Fin 3) : Decidable (cyclicCorners first last) :=
  inferInstanceAs (Decidable ((_ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _)))

/-- Two distinct original triangle corners are cyclically ordered in one of the two orientations. -/
theorem cyclic_or_reverse (first last : Fin 3) (distinct : first ≠ last) :
    cyclicCorners first last ∨ cyclicCorners last first :=
  (by decide : ∀ first last : Fin 3, first ≠ last → cyclicCorners first last ∨ cyclicCorners last first) first last
    distinct

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces in
/-- An original cyclic corner pair determines an edge occurring in the triangle boundary. -/
theorem corner_boundary {count : Nat} (triangle : OrientedTriangle count) {first last : Fin 3}
    (cyclic : cyclicCorners first last) : (⟨corner triangle first, corner triangle last⟩ : OrientedEdge count) ∈
      triangle.boundary := by
  rcases cyclic with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ List.mem_cons_self
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)

/-- Locate an original source index in the retained finite source list with an exact indexed readback equation. -/
@[expose] def sourcePosition {count : Nat} (source : Fin count) :
    (indices : List (Fin count)) → source ∈ indices → {position : Fin indices.length // indices[position.val] = source}
  | [], member => (List.not_mem_nil member).elim
  | head :: tail, member =>
      if equal : head = source then ⟨⟨0, Nat.zero_lt_succ _⟩, equal⟩
      else
        let remaining := sourcePosition source tail ((Membership.mem_cons.mp member).resolve_left (Ne.symm equal))
        ⟨remaining.val.succ, remaining.property⟩

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → OrientedTriangle vertexCount}
  {indices : List (Fin faceCount)} {boundary : List (OrientedEdge vertexCount)}

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces in
open Purelib.Topology.Surface in
/-- Construct a retained cut-edge owner for an original positively oriented source triangle edge.

The original source-list membership locates the exact cut triangle, and its cyclic corner certificate retains the
boundary occurrence and source-edge equation. -/
@[expose] def positiveSourceOwner (patch : Cut.Patch.CutPatch faces indices boundary) (source :
  Sewing.SewnPrimitiveContacts.SourceEdge faceCount)
    (member : source.source ∈ indices) (cyclic : cyclicCorners source.first source.last) :
    {route : Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner patch // route.sourceEdge = source} := by
  let found := sourcePosition source.source indices member
  let position : Fin patch.triangles.length := ⟨found.val.val, by rw [patch.triangles_length]; exact found.val.isLt⟩
  let triangle := patch.triangles[position.val]
  let edge : OrientedEdge patch.count := ⟨corner triangle source.first, corner triangle source.last⟩
  let owner : Sewing.SewnPrimitiveBoundary.TriangleEdgeOwner patch.triangles edge :=
    ⟨position, source.first, source.last, rfl, rfl, corner_boundary triangle cyclic⟩
  refine ⟨⟨edge, owner, false⟩, ?_⟩
  change (⟨indices[found.val.val], source.first, source.last⟩ : Sewing.SewnPrimitiveContacts.SourceEdge faceCount) =
    source
  rw [found.property]

section
open Purelib.Topology.Surface
/-- Reverse the retained orientation flag of the original cut-edge owner. -/
@[expose] def reverseOwner {patch : Cut.Patch.CutPatch faces indices boundary} (route :
  Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner patch) :
  Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner patch :=
  { route with reversed := !route.reversed }

/-- Reversing the original owner swaps exactly its retained source corners. -/
private theorem reverseOwner_source {patch : Cut.Patch.CutPatch faces indices boundary} (route :
  Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner patch) :
    (reverseOwner route).sourceEdge = ⟨route.sourceEdge.source, route.sourceEdge.last, route.sourceEdge.first⟩ := by
  rcases route with ⟨edge, owner, reversed⟩
  cases reversed <;> rfl

/-- Construct an original cut-edge owner for either orientation of a retained source edge with distinct corners.

A finite cyclic-order decision either keeps the original orientation or reverses the exact opposite owner, preserving
the source-edge equation. -/
@[expose] def sourceOwner (patch : Cut.Patch.CutPatch faces indices boundary) (source :
  Sewing.SewnPrimitiveContacts.SourceEdge faceCount)
    (member : source.source ∈ indices) (distinct : source.first ≠ source.last) :
    {route : Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner patch // route.sourceEdge = source} :=
  if cyclic : cyclicCorners source.first source.last then positiveSourceOwner patch source member cyclic
  else
    let opposite : Sewing.SewnPrimitiveContacts.SourceEdge faceCount := ⟨source.source, source.last, source.first⟩
    let route := positiveSourceOwner patch opposite member ((cyclic_or_reverse _ _ distinct).resolve_left cyclic)
    ⟨reverseOwner route.val, by rw [reverseOwner_source, route.property]⟩

end

open Purelib.Topology.Surface in
set_option genInjectivity false in
/-- An ordered cut-edge word with retained original path-source owners and an exact source-list equation.

The original source list remains an index, preserving every directed occurrence and its retained cut ownership. -/
structure CutSourceWord (patch : Cut.Patch.CutPatch faces indices boundary) (original : List
  (Sewing.SewnPrimitiveContacts.SourceEdge faceCount)) where
  /-- The retained ordered cut-edge list with original directed occurrences. -/ edges : List (OrientedEdge patch.count)
  /-- The retained original owner certificates for the exact stored cut-edge word. -/ sources :
    Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.PathSources patch edges
  /-- The retained source readback equals the original source-edge list exactly. -/ sources_eq : sources.sources =
    original

constructive_injectivity CutSourceWord

namespace CutSourceWord

open Purelib.Topology.Surface
/-- Construct original cut owners in the exact retained source-word order. -/
@[expose] def owners (patch : Cut.Patch.CutPatch faces indices boundary) : (original : List
  (Sewing.SewnPrimitiveContacts.SourceEdge faceCount)) →
    (∀ source ∈ original, source.source ∈ indices ∧ source.first ≠ source.last) → List
      (Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner patch)
  | [], _ => []
  | source :: tail, valid =>
      (sourceOwner patch source (valid source List.mem_cons_self).1 (valid source List.mem_cons_self).2).val ::
        owners patch tail (fun source member => valid source (List.mem_cons_of_mem _ member))

/-- The retained constructed owners read back exactly the original source-edge list. -/
theorem owners_sources (patch : Cut.Patch.CutPatch faces indices boundary) : ∀ (original : List
  (Sewing.SewnPrimitiveContacts.SourceEdge faceCount))
    (valid : ∀ source ∈ original, source.source ∈ indices ∧ source.first ≠ source.last),
    (owners patch original valid).map Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner.sourceEdge = original
  | [], _ => rfl
  | source :: tail, valid => congrArg₂ List.cons (sourceOwner patch source _ _).property
      (owners_sources patch tail (fun source member => valid source (List.mem_cons_of_mem _ member)))

/-- Construct a retained cut-source word from original source membership and distinct-corner certificates.

The exact owner list supplies both the stored cut edges and original source readback, preserving order and multiplicity.
-/
@[expose] def build (patch : Cut.Patch.CutPatch faces indices boundary) (original : List
  (Sewing.SewnPrimitiveContacts.SourceEdge faceCount))
    (valid : ∀ source ∈ original, source.source ∈ indices ∧ source.first ≠ source.last) : CutSourceWord patch original
      :=
  let entries := owners patch original valid
  ⟨entries.map Sewing.SewnPrimitivePaths.SewnPrimitiveFaces.OrientedOwner.cutEdge, ⟨entries, rfl, original,
    (owners_sources patch original valid).symm⟩, rfl⟩

/-- The retained cut-edge word has exactly the original source-word length. -/
theorem length_eq {patch : Cut.Patch.CutPatch faces indices boundary} {original : List
  (Sewing.SewnPrimitiveContacts.SourceEdge faceCount)}
    (word : CutSourceWord patch original) : word.edges.length = original.length := by
  have equal := congrArg List.length word.sources.sources_project
  rw [Map.length_map, Map.length_map, word.sources_eq] at equal
  exact equal.symm

/-- The retained cut edges project to the exact original source-edge projections in order. -/
theorem project {patch : Cut.Patch.CutPatch faces indices boundary} {original : List
  (Sewing.SewnPrimitiveContacts.SourceEdge faceCount)}
    (word : CutSourceWord patch original) :
    word.edges.map (Sewing.VertexSewing.OrientedEdge.map patch.vertexLabels) = original.map (fun source =>
      source.project faces) :=
  word.sources.sources_project.symm.trans (congrArg (List.map (fun source => source.project faces)) word.sources_eq)

end CutSourceWord
end Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces

namespace Purelib.Riemann.Branches.NewtonCutPrimitiveSources.BranchCellBank.NewtonGrid.AnnularFaces.Lifted
namespace OuterPreparation

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Branches.NewtonCutPrimitiveSources.SewnPrimitiveFaces (CutSourceWord)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners (firstCorner lastCorner)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.RootIsolation in
open Purelib.Topology.Polygon in
/-- An original retained mesh-edge route has distinct source triangle corners. -/
private theorem sourceCorners_distinct {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
    {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {frames :
      RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
    {vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges : SquareRoot.Grid.RootEdgeBank
      frames}
    {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces}
    {edge : Stokes.OrientedEdge vertices.count} (route : Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge) :
    route.sourceEdge.first ≠ route.sourceEdge.last := by
  cases route with
  | forward location =>
      change Meshes.PuncturedGrid.Face.Corners.FaceCorners.firstCorner location.kind ≠
        Meshes.PuncturedGrid.Face.Corners.FaceCorners.lastCorner location.kind
      cases location.kind <;> decide
  | backward location =>
      change Meshes.PuncturedGrid.Face.Corners.FaceCorners.lastCorner location.kind ≠
        Meshes.PuncturedGrid.Face.Corners.FaceCorners.firstCorner location.kind
      cases location.kind <;> decide

open Purelib in
open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Branches in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Every source edge assigned to the original prepared segment list has distinct corners. -/
private theorem assignedCorners_distinct {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
    {bank : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {frames :
      RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
    {vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges : SquareRoot.Grid.RootEdgeBank
      frames}
    {faces : PuncturedFaces bank} {mesh : LiftedMesh vertices edges faces} {ambient : Box} :
    ∀ {start finish : Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      {prepared : PreparedPath path owner}
      {pieces : CoveredSegments prepared}
      (assigned : Meshes.PuncturedGrid.PreparedFaceSegments.AssignedSegments mesh pieces),
      ∀ source ∈ Meshes.PuncturedGrid.Cut.TriangleComparison.AssignedSegments.sourceEdges assigned, source.first ≠
        source.last
  | _, _, _, _, _, _, .nil _ _, _, member => (List.not_mem_nil member).elim
  | _, _, _, _, _, _, .cons placement tail, source, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · exact sourceCorners_distinct placement.location
      · exact assignedCorners_distinct tail source member

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : NewtonGrid preparation target radius} {index :
    Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index} {lifted :
    LiftedPuncturedGrid grid.punctured} {region :
    Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.List in
/-- Every original annular outer-preparation source belongs to the retained cut source list and has distinct corners. -/
theorem source_valid (prepared : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region) :
    ∀ source ∈ prepared.sources, source.source ∈ lifted.cutPolygon.patch.faceIndices ∧ source.first ≠ source.last := by
  rw [prepared.sources_eq]
  intro source member
  refine ⟨?_, assignedCorners_distinct prepared.assigned source member⟩
  exact (Permutation.mem_iff lifted.cutPolygon.coverage _).mpr (Permutation.ofFn_mem (fun index => index) source.source)

open Purelib.Curves.Hyperelliptic in
/-- Construct the retained cut-source word of the original prepared annular outer boundary. -/
@[expose] def cutSources (prepared : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region) :
  CutSourceWord lifted.cutPolygon.patch.cut prepared.sources :=
  CutSourceWord.build _ prepared.sources (source_valid prepared)

open Purelib.Curves.Hyperelliptic in
open Purelib.Topology.Surface in
/-- The retained cut-source word projects to the exact original annular outer boundary. -/
theorem cutSources_project (prepared : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region) :
    (cutSources prepared).edges.map (Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels) =
      region.outer :=
  (cutSources prepared).project.trans (Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.sources_project
    prepared)

open Purelib.Curves.Hyperelliptic in
/-- The retained cut-source word has exactly the original annular outer-boundary length. -/
theorem cutSources_length (prepared : Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region) :
  (cutSources prepared).edges.length = region.outer.length := by
  rw [(cutSources prepared).length_eq]
  have equal := congrArg List.length (Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation.sources_project
    prepared)
  simpa only [Map.length_map] using equal

end Purelib.Riemann.Branches.NewtonCutPrimitiveSources.BranchCellBank.NewtonGrid.AnnularFaces.Lifted.OuterPreparation

end
