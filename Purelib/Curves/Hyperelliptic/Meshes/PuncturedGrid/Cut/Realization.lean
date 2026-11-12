module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
public import Purelib.Topology.Surface.Word.PairedWord
public import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
public import Purelib.Topology.Surface.Cut.Spanning
public import Purelib.Topology.Surface.Sewing.ChordCycleBank
public import Purelib.Topology.Surface.Sewing.SewingRetraction
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
public import Purelib.Riemann.Meshes.GridLiftedTriangleStars
import Purelib.Topology.Chain.PathBoundary
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.BoundaryPairs
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Cut.JumpPaths

/-! # One retained canonical cut of an original lifted punctured mesh

The original forest, selected polygon, edge pairing and cut word are
computed in dependency order and stored whole. Each cache retains equality
to the existing canonical factory, so clients can reuse its actual data
while keeping the original nominal mesh and cut indices.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Riemann.Meshes
open Purelib.Topology
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.SewingConnected.SewingForest (SinglePolygon)
open Purelib.Topology.Surface.Cut.BoundaryWord (CutBoundaryWord)
open Purelib.Topology.Surface.Cut.BoundaryWord.ProjectedEdgePairing (boundaryWord)
open Purelib.Topology.Surface.Cut.BoundaryPairs.SewingForest.SinglePolygon (edgePairing)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord → IntegralPairing
open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord (pairedLetters)
open Purelib.Topology.Surface.Word.PairedWord.CutBoundaryWord.IntegralPairing (wordSignature wordNormalForm)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh
  (orientedEdges_nonloop)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing (SpanningCoordinates)
open Purelib.Topology.Surface.Cut.Spanning.SewingForest.SinglePolygon (closed_spanning)
open Purelib.LinearAlgebra.Alternating

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}

namespace Cut

/-- An integral cut pairing and the original automatic normal form on that same retained pairing. -/
abbrev IntegralForm {source target : Nat} {labels : Fin source → Fin target}
    {edges : List (OrientedEdge source)} (word : CutBoundaryWord labels edges) :=
  Σ integral : IntegralPairing word,
    Surface.Word.NormalForm.WordNormalForm (pairedLetters word) (wordSignature integral)

/-- The complete original canonical forest with its exact factory identity. -/
@[expose] def Forest (lifted : LiftedPuncturedGrid base) : Type :=
  { retained : SewingForest lifted.mesh.triangulation.faces // retained = lifted.cutForest }

/-- The original selected polygon on that same canonical forest, retaining its whole factory identity. -/
@[expose] def Polygon (lifted : LiftedPuncturedGrid base) : Type :=
  { retained : SinglePolygon lifted.cutForest // retained = lifted.cutPolygon }

/-- The complete canonical occurrence pairing on the original selected cut polygon. -/
@[expose] def Pairing (lifted : LiftedPuncturedGrid base) : Type :=
  { retained : ProjectedEdgePairing lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary // retained = lifted.cutBoundaryPairs }

/-- The original cut word, alphabet and signature retained with their complete factory identity. -/
@[expose] def Word (lifted : LiftedPuncturedGrid base) : Type :=
  { retained : CutBoundaryWord lifted.cutPolygon.patch.cut.vertexLabels
      lifted.cutPolygon.patch.cut.boundary // retained = lifted.cutBoundaryWord }

end Cut

section Constructor

attribute [local irreducible] Cut.Forest Cut.Polygon Cut.Pairing Cut.Word

set_option genInjectivity false in
/-- One retained canonical geometric cut of the exact original lifted mesh.

The stored forest, selected polygon, occurrence-sensitive pairing and cut
word are the original factories' complete values. Their equality fields
preserve the same nominal owners, indices and defining equations while
allowing later cut-coordinate builders to consume the actual caches.
-/
structure Cut (lifted : LiftedPuncturedGrid base) where
  /-- The one original canonical sewing forest. -/ forest : Cut.Forest lifted
  /-- The selected original sewn polygon on that same forest. -/ polygon : Cut.Polygon lifted
  /-- The original complete pairing of the retained polygon's edge occurrences. -/ pairing : Cut.Pairing lifted
  /-- The same cut word, including its cached alphabet and signature. -/ word : Cut.Word lifted

constructive_injectivity Cut

end Constructor

namespace Cut

variable (lifted : LiftedPuncturedGrid base)

/-- Construct the original cut geometry once in its existing dependency order.

The selected polygon consumes the retained forest. Its actual patch supplies
the original edge pairing, which supplies the complete word and alphabet.
Each whole factory equation is checked on those same original values.
-/
@[expose] def build : Cut lifted :=
  let forest := lifted.cutForest
  let polygon := lifted.singlePolygon forest
  let pairing := edgePairing polygon (orientedEdges_nonloop lifted.mesh)
  let word := boundaryWord pairing
  ⟨⟨forest, (rfl)⟩, ⟨polygon, (rfl)⟩, ⟨pairing, (rfl)⟩, ⟨word, (rfl)⟩⟩

variable {lifted} (retained : Cut lifted)

/-- Construct the original canonical retraction from the retained polygon's actual sewn patch. -/
@[expose] def retraction : SewingRetraction.Retraction lifted.mesh.triangulation.faces
    lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary :=
  Eq.mp (congrArg (fun polygon : SinglePolygon lifted.cutForest =>
    SewingRetraction.Retraction lifted.mesh.triangulation.faces polygon.patch.faceIndices polygon.patch.boundary)
    retained.polygon.property) (SewingRetraction.Retraction.ofPatch retained.polygon.val.patch)

/-- Compute the original integral pairing and normal form on this same retained cut word.

Both original algebraic producers consume the cached word and pairing.
Only their dependent result indices are transported to the original
canonical word; no cut geometry or alphabet is recomputed.
-/
@[expose] def integralForm : IntegralForm lifted.cutBoundaryWord :=
  let word := retained.word.val
  let integral := IntegralPairing.build word
  let normal := wordNormalForm (word := word) integral
  Eq.mp (congrArg IntegralForm retained.word.property) ⟨integral, normal⟩

/-- The cut-word carrier of a chosen polygon on the original lifted forest. -/
abbrev PolygonWord (polygon : SinglePolygon lifted.cutForest) :=
  CutBoundaryWord polygon.patch.cut.vertexLabels polygon.patch.cut.boundary

/-- Reindexing an entire cut word along its polygon identity preserves the original complete value. -/
theorem reindexWord_heq {first last : SinglePolygon lifted.cutForest} (same : first = last)
    (word : PolygonWord last) :
    HEq (Eq.mpr (congrArg (PolygonWord (lifted := lifted)) same) word) word := by
  cases same
  rfl

/-- Transport cached cut coordinates through equal original polygons and the same complete cut word.

Only the dependent indices change. The original ordered letters, integral
totals and their certificates are returned together, without recomputation.
-/
@[expose] def reindexCoordinates {first last : SinglePolygon lifted.cutForest} (samePolygon : first = last)
    {firstWord : PolygonWord first} {lastWord : PolygonWord last} (sameWord : HEq firstWord lastWord)
    {path : List (OrientedEdge lifted.vertices.count)}
    (rows : WordCoordinates firstWord.alphabet path) : WordCoordinates lastWord.alphabet path := by
  cases samePolygon
  cases (eq_of_heq sameWord)
  exact rows

/-- Compute original integer coordinates using the actual retained polygon labels and cut alphabet.

The WordCoordinates producer consumes the same cached word, reindexed
only to the stored polygon. The complete result is transported back to the
original nominal cut word; no forest, polygon or alphabet is rebuilt.
-/
@[expose] def coordinates (path : List (OrientedEdge lifted.vertices.count))
    (supported : CutPath.Supported lifted.cutPolygon.patch.boundary path) :
    WordCoordinates lifted.cutBoundaryWord.alphabet path := by
  let polygon := retained.polygon.val
  let word := Eq.mpr (congrArg (PolygonWord (lifted := lifted)) retained.polygon.property) retained.word.val
  let supportAt (polygon : SinglePolygon lifted.cutForest) := CutPath.Supported
    (polygon.patch.cut.boundary.map (VertexSewing.OrientedEdge.map polygon.patch.cut.vertexLabels)) path
  have originalSupport : supportAt lifted.cutPolygon := by
    dsimp only [supportAt]
    rewrite [lifted.cutPolygon.patch.cut.boundary_eq]
    exact supported
  have sameSupport : supportAt polygon :=
    Eq.mpr (congrArg supportAt retained.polygon.property) originalSupport
  let rows := WordCoordinates.build word.alphabet path sameSupport
  have sameWord : HEq word lifted.cutBoundaryWord :=
    (reindexWord_heq retained.polygon.property retained.word.val).trans (heq_of_eq retained.word.property)
  exact reindexCoordinates retained.polygon.property sameWord rows

/-- Reusing the stored geometry gives the whole original coordinate factory result on the same path. -/
theorem coordinates_eq (path : List (OrientedEdge lifted.vertices.count))
    (supported : CutPath.Supported lifted.cutPolygon.patch.boundary path) :
    retained.coordinates path supported =
      WordCoordinates.build lifted.cutBoundaryWord.alphabet path (by
        rewrite [lifted.cutPolygon.patch.cut.boundary_eq]
        exact supported) := by
  cases retained with
  | mk forest polygon pairing word =>
    cases polygon with
    | mk polygon samePolygon =>
      cases word with
      | mk word sameWord =>
        cases samePolygon
        cases sameWord
        rfl

/-- The retained polygon produces exactly the original canonical patch retraction. -/
theorem retraction_eq : retained.retraction = SewingRetraction.Retraction.ofPatch lifted.cutPolygon.patch := by
  cases retained with
  | mk forest polygon pairing word =>
    cases polygon with
    | mk polygon same =>
      cases same
      rfl

/-- The retained word produces the whole original canonical integral pairing and automatic normal form. -/
theorem integralForm_eq : retained.integralForm =
    ⟨lifted.cutIntegralPairing, wordNormalForm (word := lifted.cutBoundaryWord) lifted.cutIntegralPairing⟩ := by
  cases retained with
  | mk forest polygon pairing word =>
    cases word with
    | mk word same =>
      cases same
      rfl

/-- Produce the original integral-spanning certificate using this exact cached cut word.

The supplied integral pairing, normal form and coordinate row remain the
original inputs. The generic spanning producer consumes the stored word;
its geometry and closure arguments supply only the original proof payment.
-/
@[expose] def spanning (path : List (OrientedEdge lifted.vertices.count))
    (rows : WordCoordinates lifted.cutBoundaryWord.alphabet path)
    (integral : IntegralPairing lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : NormalForm integral.paired raw) {anchor : Fin lifted.vertices.count}
    (closed : PathEndpoints OrientedEdge.start OrientedEdge.finish path anchor anchor)
    (supported : CutPath.Supported lifted.cutPolygon.patch.boundary path) :
    SpanningCoordinates integral rows.totals :=
  closed_spanning lifted.cutPolygon lifted.mesh.orientedEdges_unique (orientedEdges_nonloop lifted.mesh)
    (GridLiftedTriangleStars.FramedPuncturedGrid.vertexConnection base lifted.mesh)
    lifted.cutBoundaryPairs integral normal rows closed supported
    (cachedWord := ⟨retained.word.val, retained.word.property⟩)

/-- Reusing the cached cut word preserves the complete original integral-spanning factory result. -/
theorem spanning_eq (path : List (OrientedEdge lifted.vertices.count))
    (rows : WordCoordinates lifted.cutBoundaryWord.alphabet path)
    (integral : IntegralPairing lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)}
    (normal : NormalForm integral.paired raw) {anchor : Fin lifted.vertices.count}
    (closed : PathEndpoints OrientedEdge.start OrientedEdge.finish path anchor anchor)
    (supported : CutPath.Supported lifted.cutPolygon.patch.boundary path) :
    retained.spanning path rows integral normal closed supported =
      closed_spanning lifted.cutPolygon lifted.mesh.orientedEdges_unique (orientedEdges_nonloop lifted.mesh)
        (GridLiftedTriangleStars.FramedPuncturedGrid.vertexConnection base lifted.mesh)
        lifted.cutBoundaryPairs integral normal rows closed supported := by
  cases retained with
  | mk forest polygon pairing word =>
    cases word with
    | mk word same =>
      cases same
      rfl

/-- Transport a retained chord bank through the same polygon and complete cut-word identities. -/
@[expose] def reindexChords {first last : SinglePolygon lifted.cutForest} (samePolygon : first = last)
    {firstWord : PolygonWord first} {lastWord : PolygonWord last} (sameWord : HEq firstWord lastWord)
    (chords : ChordCycleBank firstWord) : ChordCycleBank lastWord := by
  cases samePolygon
  cases (eq_of_heq sameWord)
  exact chords

/-- Construct the original chord bank on the cached word and actual retained polygon anchor.

The original chord producer receives the cached labels, boundary and
ordered word. The complete chord geometry and projected cycles are then
reindexed to the original canonical word without repeating cut preparation.
-/
@[expose] def chords : ChordCycleBank lifted.cutBoundaryWord := by
  let polygon := retained.polygon.val
  let word := Eq.mpr (congrArg (PolygonWord (lifted := lifted)) retained.polygon.property) retained.word.val
  let selected := ChordCycleBank.build word (anchor := polygon.patch.cut.anchor) polygon.patch.cut.closed
  have sameWord : HEq word lifted.cutBoundaryWord :=
    (reindexWord_heq retained.polygon.property retained.word.val).trans (heq_of_eq retained.word.property)
  exact reindexChords retained.polygon.property sameWord selected

/-- The shared cached chord construction preserves the original complete bank and chosen anchor. -/
theorem chords_eq : retained.chords =
    ChordCycleBank.build lifted.cutBoundaryWord lifted.cutPolygon.patch.cut.closed := by
  cases retained with
  | mk forest polygon pairing word =>
    cases polygon with
    | mk polygon samePolygon =>
      cases word with
      | mk word sameWord =>
        cases samePolygon
        cases sameWord
        rfl

end Cut

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

end
