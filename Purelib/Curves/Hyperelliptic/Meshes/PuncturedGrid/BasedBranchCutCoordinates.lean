module
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Realization
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
public import Purelib.Riemann.Meshes.GridLiftedTriangleStars
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
public import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchRelations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Topology.Surface

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.Riemann

open Purelib.Riemann.Meshes.LiftedPuncturedGrid renaming Cut → CutGeometry

public section

/-!
# Common-base branch pairs in the actual retained cut alphabet

One sewing retraction and one integral normal form serve every labelled
reference pair. The materialized words, integer coordinates and spanning
coefficients retain the original sheet transports. The reference-pair
comparison keeps both signed face corrections and the actual physical hole.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates

open Purelib.Topology.Surface.Cut.JumpPaths

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Polygon.Stokes

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
  {first last reference : Data.Index branches} {sheet : Fin 2}

namespace Pair

/-- The original paired indexed walk begins and ends at the exact retained common branch-bank anchor. -/
theorem closed_endpoints (pair :
  BasedBranchBank.Pair bank first last sheet) :
    Topology.Chain.PathBoundary.PathEndpoints OrientedEdge.start
      OrientedEdge.finish pair.closed.indexed
      (BasedBranchBank.anchor lifted sheet)
        (BasedBranchBank.anchor lifted sheet) :=
        by
  rw [pair.closed.indexed_eq]
  have closed := lifted.edges.indexedEdges_closed lifted.vertices pair.closed.walk
    (lifted.vertices.coordinate_onGrid
      (BasedBranchBank.anchor lifted sheet))
      (lifted.vertices.sheet
      (BasedBranchBank.anchor lifted sheet))
    pair.closed.sheet_eq
  simpa only [BasedBranchBank.anchor,
    lifted.vertices.coordinate_index, lifted.vertices.sheet_index] using closed

/-- Every original paired walk edge belongs to the actual retained cut patch. -/
theorem supported (pair : BasedBranchBank.Pair
  bank first last sheet) :
    CutPath.Supported (Sewing.SewingConnected.SewnPatch.originalEdges
      lifted.cutPolygon.patch) pair.closed.indexed := by
  rw [pair.closed.indexed_eq]
  exact CutPath.supported_mono
    (SkeletonFaceAssignments.indexedWalk_supported lifted.mesh pair.closed.walk
      (lifted.vertices.sheet
      (BasedBranchBank.anchor lifted sheet)))
    (fun _ member => Standard.TourRetraction.originalEdge_on_cutPatch lifted member)

set_option genInjectivity false in
/-- The source word is the cached actual pair. Its boundary image, integer
row and integral spanning data are computed once and retained together. -/
structure CutCoordinates (pair :
  BasedBranchBank.Pair bank first last sheet)
    (integral : Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord) where
  /-- The original pair's retained route to the actual cut boundary with its signed face correction. -/ route :
    Sewing.SewingRetraction.WordRoute lifted.mesh.triangulation.faces lifted.cutPolygon.patch.boundary
    pair.closed.indexed
  /-- The integer coordinates of that exact retained boundary route in the original cut alphabet. -/ coordinates :
    WordCoordinates lifted.cutBoundaryWord.alphabet route.path
  /-- The original integral spanning certificate for those exact retained integer totals. -/ span :
    Cut.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates integral coordinates.totals

constructive_injectivity CutCoordinates

namespace CutCoordinates

variable {pair : BasedBranchBank.Pair bank first
  last sheet}
  {integral : Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}

/-- Compute the original pair's boundary route, integer coordinates and spanning certificate using the supplied retained
retraction and normal form. -/
@[expose] def ofRetraction (pair :
  BasedBranchBank.Pair bank first last sheet)
    (geometry : CutGeometry lifted)
    (retraction : Sewing.SewingRetraction.Retraction lifted.mesh.triangulation.faces
      lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary)
    (integral : Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)} (normal :
      NormalForm
      integral.paired raw) :
    CutCoordinates pair integral :=
  let route := retraction.word pair.closed.indexed
    (Pair.supported pair)
  let coordinates := geometry.coordinates route.path route.supported
  ⟨route, coordinates, geometry.spanning route.path coordinates integral normal
    (route.endpoints (Pair.closed_endpoints pair)) route.supported⟩

/-- The original retained closed pair's cut coordinates have zero boundary at each vertex. -/
theorem boundary_zero (cut : CutCoordinates pair
  integral) (vertex : Fin lifted.vertices.count) :
    cut.coordinates.boundaryAt vertex = 0 :=
  cut.coordinates.boundary_zero (cut.route.endpoints
    (Pair.closed_endpoints pair)) vertex

/-- The original pair value equals its retained integer boundary-coordinate combination plus its actual signed face
correction. -/
theorem value_eq (cut : CutCoordinates pair integral)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Sewing.SewingRetraction.wordValue value pair.closed.indexed =
      WordCoordinates.combine cut.coordinates.totals
        (fun index => value (Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators index))) +
      Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value cut.route.correction :=
        by
  rw [cut.route.value_eq value anti, cut.coordinates.value_eq value anti]

/-- The original pair value equals its integral-pairing combination plus retained physical-boundary and signed-face
terms. -/
theorem spanning_value (cut : CutCoordinates pair
  integral)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Sewing.SewingRetraction.wordValue value pair.closed.indexed =
      WordCoordinates.combine cut.span.coefficients (fun index =>
        WordCoordinates.combine (integral.paired index)
        (fun column => value (Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))) +
      WordCoordinates.combine cut.span.physical
        (fun column => value (Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) +
      Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value cut.route.correction :=
        by
  rw [CutCoordinates.value_eq cut value anti,
    Cut.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates.value_eq cut.span]

end CutCoordinates
end Pair

set_option genInjectivity false in
/-- One original labelled branch-reference pair and its retained integer cut-coordinate certificate. -/
structure ReferenceRow (bank : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  lifted) (first reference : Data.Index branches)
    (sheet : Fin 2) (integral : Cut.IntegralPairing.CutBoundaryWord
      lifted.cutBoundaryWord) where
  /-- The actual original common-base pair from the retained branch label to the reference label. -/ pair :
    BasedBranchBank.Pair bank first reference
    sheet
  /-- The retained cut route and integral coordinates of that exact original pair. -/ cut :
    Pair.CutCoordinates pair integral

constructive_injectivity ReferenceRow

set_option genInjectivity false in
/-- Shared expensive finite data is retained once. Every branch row carries
its original label, actual closed pair and proved integral decomposition. -/
structure ReferenceCutBank (bank :
  BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted) (reference :
  Data.Index branches) (sheet : Fin 2) where
  /-- The complete original cut geometry shared by all retained reference rows. -/ geometry : CutGeometry lifted
  /-- The original integral pairing on the actual retained cut-boundary word. -/ integral :
    Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord
  /-- The retained normal form of the exact original paired-letter word and integral signature. -/ normal :
    Word.NormalForm.WordNormalForm (Word.PairedWord.CutBoundaryWord.pairedLetters
    lifted.cutBoundaryWord)
    (Word.PairedWord.CutBoundaryWord.IntegralPairing.wordSignature integral)
  /-- The original shared sewing retraction onto the retained cut patch boundary. -/ retraction :
    Sewing.SewingRetraction.Retraction lifted.mesh.triangulation.faces
    lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary
  /-- The dependent original branch-reference pairs and their retained integral coordinate certificates. -/ rows :
    Vector.DependentVector (fun index : Data.Index branches =>
    ReferenceRow bank index reference sheet integral)

constructive_injectivity ReferenceCutBank

namespace ReferenceCutBank

/-- Prepare the original integral pairing, normal form and sewing retraction once, then retain each actual labelled
branch-reference row. -/
@[expose] def build (bank : BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank
  lifted) (reference : Data.Index branches) (sheet : Fin 2) (geometry : CutGeometry lifted) :
    ReferenceCutBank bank reference sheet :=
  let formed := geometry.integralForm
  let integral := formed.1
  let normal := formed.2
  let retraction := geometry.retraction
  let rows := Vector.DependentVector.ofFn fun index : Data.Index branches =>
    let pair := bank.pair index reference sheet
    (⟨pair, Pair.CutCoordinates.ofRetraction pair geometry
      retraction integral normal.normal⟩ : ReferenceRow
      bank index reference sheet integral)
  ⟨geometry, integral, normal, retraction, rows⟩

/-- The explicit branch-pair comparison now reads the retained integer cut
rows. The physical clockwise hole and both signed face sums survive. -/
theorem reference_hole_value (cut : ReferenceCutBank bank
  reference sheet)
    (hole : Meshes.PuncturedGridFaces.BranchHole base.bank.toBranchCellBank) (pair :
      BasedBranchBank.Pair bank first hole.index
      sheet)
    (value : OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Sewing.SewingRetraction.wordValue value pair.closed.indexed =
      WordCoordinates.combine (cut.rows.get first).cut.coordinates.totals
        (fun index => value (Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators index))) -
      WordCoordinates.combine (cut.rows.get
        hole.index).cut.coordinates.totals
        (fun index => value (Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators index))) +
      Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
        first).cut.route.correction -
      Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value (cut.rows.get
        hole.index).cut.route.correction -
      Sewing.SewingRetraction.wordValue value (hole.liftedBoundary lifted.vertices lifted.edges) := by
  rw [BasedBranchRelations.Pair.reference_hole_value hole pair (cut.rows.get
    first).pair (cut.rows.get hole.index).pair value anti,
    Pair.CutCoordinates.value_eq (cut.rows.get first).cut
      value anti,
    Pair.CutCoordinates.value_eq (cut.rows.get
      hole.index).cut value anti]
  ring1

end ReferenceCutBank
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates
