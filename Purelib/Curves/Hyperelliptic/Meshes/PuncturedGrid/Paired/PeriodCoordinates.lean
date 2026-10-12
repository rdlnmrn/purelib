module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.LinearAlgebra.Alternating.Handle.Basic
import Purelib.LinearAlgebra.Alternating.NormalForm.Basic
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.FramedPuncturedGrid
public import Purelib.Riemann.Meshes.GridLiftedTriangleStars
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
public import Purelib.Topology.Surface.Chord.Spanning
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.ChordCycleBank
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.NormalForm
import Purelib.Topology.Surface.Word.PairedWord
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.WordGenus
public import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.Topology.Surface.Chord.PhysicalBoundary
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.LinearAlgebra.Alternating

open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix

open Purelib.Riemann

public section

/-!
# Cut coordinates of the actual corrected A/B period programs

The retained program words are retracted through one shared finite surface
cache. Their integer rows, physical components and face corrections belong
to those same words. The common normal form has exactly the curve genus
many handles. The computed intersection blocks retain the actual crossing
form; the standard symplectic signs still require a geometric proof.
-/

section

open Purelib.LinearAlgebra.Matrix (matrixOfFn matrixOfFn_apply)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {bank :
    Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted} {sheet : Fin 2}
  {ordered : Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered bank sheet}
    {paired : Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchPairs.Ordered.Paired ordered} {prepared :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

/-- The actual original common-loop word is closed at its retained lifted anchor. -/
private theorem loop_closed (loop : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop
  lifted sheet) :
    Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish loop.indexed
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet) :=
      by
  rw [loop.indexed_eq]
  have closed := lifted.edges.indexedEdges_closed lifted.vertices loop.walk
    (lifted.vertices.coordinate_onGrid
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet))
      (lifted.vertices.sheet
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet))
      loop.sheet_eq
  simpa only [Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor,
    lifted.vertices.coordinate_index, lifted.vertices.sheet_index] using closed

/-- Every edge of the original common-loop word belongs to the retained cut patch. -/
private theorem loop_supported (loop : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea.CommonLoop
  lifted sheet) :
    Topology.Surface.Cut.JumpPaths.CutPath.Supported (Topology.Surface.Sewing.SewingConnected.SewnPatch.originalEdges
      lifted.cutPolygon.patch) loop.indexed := by
  rw [loop.indexed_eq]
  exact Topology.Surface.Cut.JumpPaths.CutPath.supported_mono
    (Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments.indexedWalk_supported lifted.mesh loop.walk
      (lifted.vertices.sheet
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)))
    (fun _ member => Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction.originalEdge_on_cutPatch lifted member)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

/-- The original A program word closes at the retained common lifted anchor. -/
theorem aWord_closed (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (index : Fin genus) :
    Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish (prepared.aWord index)
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet) :=
      by
  rw [prepared.aWord_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates.Pair.closed_endpoints (paired.row index).row.a

/-- The original corrected B program word closes at the retained common lifted anchor. -/
theorem bWord_closed (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (index : Fin genus) :
    Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish (prepared.bWord index)
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet) :=
      by
  rw [prepared.bWord_eq]
  exact Paired.PeriodCoordinates.loop_closed (paired.row index).row.corrected

/-- The original A program word is supported on the retained cut patch. -/
theorem aWord_supported
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (index : Fin genus) :
    Topology.Surface.Cut.JumpPaths.CutPath.Supported (Topology.Surface.Sewing.SewingConnected.SewnPatch.originalEdges
      lifted.cutPolygon.patch) (prepared.aWord index) := by
  rw [prepared.aWord_eq]
  exact Hyperelliptic.Meshes.PuncturedGrid.BasedBranchCutCoordinates.Pair.supported (paired.row index).row.a

/-- The original corrected B program word is supported on the retained cut patch. -/
theorem bWord_supported
  (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (index : Fin genus) :
    Topology.Surface.Cut.JumpPaths.CutPath.Supported (Topology.Surface.Sewing.SewingConnected.SewnPatch.originalEdges
      lifted.cutPolygon.patch) (prepared.bWord index) := by
  rw [prepared.bWord_eq]
  exact Paired.PeriodCoordinates.loop_supported (paired.row index).row.corrected

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

set_option genInjectivity false in
/-- The original closed word's retained retraction, boundary coordinates and integral span. -/
structure ClosedCoordinates (word : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count))
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord) where
  /-- The actual original word retraction with its retained face correction. -/ route :
    Topology.Surface.Sewing.SewingRetraction.WordRoute lifted.mesh.triangulation.faces lifted.cutPolygon.patch.boundary
    word
  /-- The exact boundary coordinates of the retained original route. -/ coordinates :
    Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates lifted.cutBoundaryWord.alphabet route.path
  /-- The integral span of the original coordinate totals. -/ span :
    Topology.Surface.Cut.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates integral coordinates.totals

constructive_injectivity ClosedCoordinates

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

section

variable {word : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)}
  {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates

/-- Retract the actual supported closed word through the supplied shared cache and retain its integral span. -/
@[expose] def build (word : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count))
    (supported : Topology.Surface.Cut.JumpPaths.CutPath.Supported
      (Topology.Surface.Sewing.SewingConnected.SewnPatch.originalEdges lifted.cutPolygon.patch) word)
    (closed : Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish word
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet)
      (Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.anchor lifted sheet))
    (retraction : Topology.Surface.Sewing.SewingRetraction.Retraction lifted.mesh.triangulation.faces
      lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)} (normal :
      LinearAlgebra.Alternating.NormalForm
      integral.paired raw) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates word integral :=
  let route := retraction.word word supported
  let coordinates := Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.build lifted.cutBoundaryWord.alphabet
    route.path (by
    rw [lifted.cutPolygon.patch.cut.boundary_eq]
    exact route.supported)
  ⟨route, coordinates, Topology.Surface.Cut.Spanning.SewingForest.SinglePolygon.closed_spanning lifted.cutPolygon
    lifted.mesh.orientedEdges_unique
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
    lifted.mesh)
    (Meshes.GridLiftedTriangleStars.FramedPuncturedGrid.vertexConnection base lifted.mesh) lifted.cutBoundaryPairs
      integral normal coordinates (route.endpoints closed) route.supported⟩

/-- The original word value is its retained boundary-coordinate combination plus the actual signed-face correction. -/
theorem value_eq (cut : PeriodCoordinates.ClosedCoordinates word integral)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value word =
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine cut.coordinates.totals
      (fun index => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
        lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators index))) +
      Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value cut.route.correction :=
        by
  rw [cut.route.value_eq value anti, cut.coordinates.value_eq value anti]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates

end

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

set_option genInjectivity false in
/-- The exact cut coordinates of one original A and corrected B program word. -/
structure CutRow (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) (integral :
  Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord) (index : Fin genus) where
  /-- The cut coordinates of the actual original A word. -/ a :
    ClosedCoordinates (prepared.aWord index) integral
  /-- The cut coordinates of the actual original corrected B word. -/ b :
    ClosedCoordinates (prepared.bWord index) integral

constructive_injectivity CutRow

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow

/-- Compute both original A/B coordinate rows using the same retained retraction and integral normal form. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired)
    (retraction : Topology.Surface.Sewing.SewingRetraction.Retraction lifted.mesh.triangulation.faces
      lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary)
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    {raw : List (Handle.Basic.PivotIndices lifted.cutBoundaryWord.alphabet.count)} (normal :
      LinearAlgebra.Alternating.NormalForm
      integral.paired raw) (index : Fin genus) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow prepared integral index :=
  let a := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates.build _
    (prepared.aWord_supported index) (prepared.aWord_closed index) retraction integral normal
  let b := Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.ClosedCoordinates.build _
    (prepared.bWord_supported index) (prepared.bWord_closed index) retraction integral normal
  ⟨a, b⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow

section

variable {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {chords : Topology.Surface.Sewing.ChordCycleBank lifted.cutBoundaryWord} {index : Fin genus}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow

set_option genInjectivity false in
/-- The original A/B spans expressed on one retained chord bank with their physical corrections. -/
structure OnChords (row : PeriodCoordinates.CutRow prepared integral index)
  (chords : Topology.Surface.Sewing.ChordCycleBank lifted.cutBoundaryWord) where
  /-- The original A span on the retained chord bank with its actual physical correction. -/ aPhysical :
    Topology.Surface.Chord.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates.OnChords row.a.span chords
  /-- The original corrected B span on the retained chord bank with its actual physical correction. -/ bPhysical :
    Topology.Surface.Chord.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates.OnChords row.b.span chords

constructive_injectivity OnChords

/-- Express both original coordinate spans on the supplied shared chord bank. -/
@[expose] def onChords (row : PeriodCoordinates.CutRow prepared integral
  index) (chords : Topology.Surface.Sewing.ChordCycleBank lifted.cutBoundaryWord) : row.OnChords chords
  :=
  ⟨Topology.Surface.Chord.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates.onChords row.a.span chords,
    Topology.Surface.Chord.Spanning.CutBoundaryWord.IntegralPairing.SpanningCoordinates.onChords row.b.span chords⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow

section

variable {row : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow prepared integral
  index}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow.OnChords

/-- The original A-word value is its retained chord-chain value plus the physical and signed-face corrections. -/
theorem a_value (data : row.OnChords chords)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.aWord index) =
      Topology.Surface.Chord.Spanning.CutCycleChain.edgeValue data.aPhysical.chain value +
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine data.aPhysical.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) +
      Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value row.a.route.correction :=
        by
  rw [row.a.value_eq value anti, data.aPhysical.value_eq value anti]

/-- The original corrected B-word value is its retained chord-chain value plus the physical and signed-face corrections.
-/
theorem b_value (data : row.OnChords chords)
    (value : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      value edge.reverse = -value edge) :
    Topology.Surface.Sewing.SewingRetraction.wordValue value (prepared.bWord index) =
      Topology.Surface.Chord.Spanning.CutCycleChain.edgeValue data.bPhysical.chain value +
      Topology.Surface.Boundary.BoundaryCoordinates.WordCoordinates.combine data.bPhysical.physical
        (fun column => value (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map
          lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column))) +
      Topology.Surface.Sewing.SewingRetraction.faceValue lifted.mesh.triangulation.faces value row.b.route.correction :=
        by
  rw [row.b.value_eq value anti, data.bPhysical.value_eq value anti]

/-- The retained original A physical correction has zero boundary at each actual lifted vertex. -/
theorem a_physical_boundary_zero (data : row.OnChords chords) (vertex : Fin lifted.vertices.count) :
    FiniteSum.Fin.sumFin (fun column => data.aPhysical.physical column *
      Topology.Chain.PathBoundary.edgeBoundaryAt Topology.Polygon.Stokes.OrientedEdge.start
        Topology.Polygon.Stokes.OrientedEdge.finish
        (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column)) vertex) = 0 :=
  Topology.Surface.Chord.PhysicalBoundary.IntegralPairing.SpanningCoordinates.OnChords.physical_boundary_zero
    data.aPhysical lifted.cutPolygon.patch.cut.closed
    (row.a.coordinates.boundary_zero (row.a.route.endpoints (prepared.aWord_closed index))) vertex

/-- The retained original B physical correction has zero boundary at each actual lifted vertex. -/
theorem b_physical_boundary_zero (data : row.OnChords chords) (vertex : Fin lifted.vertices.count) :
    FiniteSum.Fin.sumFin (fun column => data.bPhysical.physical column *
      Topology.Chain.PathBoundary.edgeBoundaryAt Topology.Polygon.Stokes.OrientedEdge.start
        Topology.Polygon.Stokes.OrientedEdge.finish
        (Topology.Surface.Sewing.VertexSewing.OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column)) vertex) = 0 :=
  Topology.Surface.Chord.PhysicalBoundary.IntegralPairing.SpanningCoordinates.OnChords.physical_boundary_zero
    data.bPhysical lifted.cutPolygon.patch.cut.closed
    (row.b.coordinates.boundary_zero (row.b.route.endpoints (prepared.bWord_closed index))) vertex

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow.OnChords

end
end

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

set_option genInjectivity false in
/-- The three actual integer intersection blocks of the retained original program rows. -/
structure IntersectionBlocks
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (rows : Data.Vector.DependentVector (fun index : Fin genus =>
      CutRow prepared integral index)) where
  /-- The cached original A–A integer intersection block. -/ aa : SquareMatrix Int genus
  /-- The cached original A–B integer intersection block. -/ ab : SquareMatrix Int genus
  /-- The cached original B–B integer intersection block. -/ bb : SquareMatrix Int genus
  /-- Every A–A entry is the exact pairing of the retained original spans. -/ aa_eq : ∀ first last, aa first last =
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
    first).a.span (rows.get last).a.span
  /-- Every A–B entry is the exact pairing of the retained original spans. -/ ab_eq : ∀ first last, ab first last =
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
    first).a.span (rows.get last).b.span
  /-- Every B–B entry is the exact pairing of the retained original spans. -/ bb_eq : ∀ first last, bb first last =
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
    first).b.span (rows.get last).b.span

constructive_injectivity IntersectionBlocks

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.IntersectionBlocks

/-- Materialize the exact three integer pairing blocks from the retained original row spans. -/
@[expose] def build
    {integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
    (rows : Data.Vector.DependentVector (fun index : Fin genus =>
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutRow prepared integral index)) :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.IntersectionBlocks rows :=
  ⟨matrixOfFn (fun first last =>
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
    first).a.span (rows.get last).a.span),
    SquareMatrix.matrixOfFn (fun first last =>
      Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
      first).a.span (rows.get last).b.span),
    SquareMatrix.matrixOfFn (fun first last =>
      Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection (rows.get
      first).b.span (rows.get last).b.span),
    SquareMatrix.matrixOfFn_apply _, SquareMatrix.matrixOfFn_apply _, SquareMatrix.matrixOfFn_apply _⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.IntersectionBlocks

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

set_option genInjectivity false in
/-- The already prepared A/B family is retained as the index of this cache.
All rows use one integral pairing and normal form, including its proved
handle count. No table of standard intersection signs is accepted. -/
structure CutBank (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) where
  /-- The original cut word's retained integral pairing. -/ integral :
    Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord
  /-- The actual integral normal form of the retained original paired letters. -/ normal :
    Topology.Surface.Word.NormalForm.WordNormalForm (Topology.Surface.Word.PairedWord.CutBoundaryWord.pairedLetters
    lifted.cutBoundaryWord) (Topology.Surface.Word.PairedWord.CutBoundaryWord.IntegralPairing.wordSignature integral)
  /-- The original normal form's actual handle count equals the curve genus. -/ handles_eq : normal.pivots.length =
    genus
  /-- The one shared original surface retraction. -/ retraction : Topology.Surface.Sewing.SewingRetraction.Retraction
    lifted.mesh.triangulation.faces lifted.cutPolygon.patch.faceIndices lifted.cutPolygon.patch.boundary
  /-- The dependent original A/B coordinate rows. -/ rows : Data.Vector.DependentVector (fun index : Fin genus =>
    CutRow prepared integral index)
  /-- The actual intersection blocks computed from those exact retained rows. -/ intersections :
    IntersectionBlocks rows

constructive_injectivity CutBank

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates

section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

/-- Cache one integral pairing, normal form and retraction for the original prepared family, then compute its actual
intersection blocks. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodPrograms.Prepared paired) :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank prepared :=
  let integral := lifted.cutIntegralPairing
  let normal := Topology.Surface.Word.PairedWord.CutBoundaryWord.IntegralPairing.wordNormalForm integral
  let retraction := Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction.boundaryRetraction lifted
  let rows := Data.Vector.DependentVector.ofFn (PeriodCoordinates.CutRow.build
    prepared retraction integral normal.normal)
  ⟨integral, normal, lifted.cutWord_handle_count normal, retraction, rows,
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.IntersectionBlocks.build rows⟩

/-- The original A–A intersection block is skew-symmetric. -/
theorem aa_skew (cut : PeriodCoordinates.CutBank prepared) (first last : Fin
  genus) :
    cut.intersections.aa first last = -cut.intersections.aa last first := by
  rw [cut.intersections.aa_eq, cut.intersections.aa_eq]
  exact Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_skew
    (cut.rows.get first).a.span (cut.rows.get last).a.span

/-- The original B–B intersection block is skew-symmetric. -/
theorem bb_skew (cut : PeriodCoordinates.CutBank prepared) (first last : Fin
  genus) :
    cut.intersections.bb first last = -cut.intersections.bb last first := by
  rw [cut.intersections.bb_eq, cut.intersections.bb_eq]
  exact Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_skew
    (cut.rows.get first).b.span (cut.rows.get last).b.span

/-- Each original A span has zero self-intersection. -/
theorem aa_diagonal (cut : PeriodCoordinates.CutBank prepared) (index : Fin
  genus) : cut.intersections.aa index index = 0 := by
  rw [cut.intersections.aa_eq]
  exact
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_diagonal
    (cut.rows.get index).a.span

/-- Each original corrected B span has zero self-intersection. -/
theorem bb_diagonal (cut : PeriodCoordinates.CutBank prepared) (index : Fin
  genus) : cut.intersections.bb index index = 0 := by
  rw [cut.intersections.bb_eq]
  exact
    Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates.intersection_diagonal
    (cut.rows.get index).b.span

set_option genInjectivity false in
/-- The same chord bank serves every A/B row. It is acquired after the
cut-coordinate bank and retains those existing coordinate and face caches. -/
structure OnChords (cut : PeriodCoordinates.CutBank prepared) where
  /-- The shared original chord-cycle bank. -/ chords : Topology.Surface.Sewing.ChordCycleBank
    lifted.cutBoundaryWord
  /-- Each retained original coordinate row expressed on this exact chord bank. -/ rows : Data.Vector.DependentVector
    (fun index : Fin genus => (cut.rows.get index).OnChords chords)

constructive_injectivity OnChords

/-- Build one shared chord bank and express every retained original coordinate row on that bank. -/
@[expose] def onChords (cut : PeriodCoordinates.CutBank prepared) :
  cut.OnChords :=
  let chords := Topology.Surface.Sewing.ChordCycleBank.build lifted.cutBoundaryWord
    lifted.cutPolygon.patch.cut.closed
  ⟨chords, Data.Vector.DependentVector.ofFn (fun index => (cut.rows.get index).onChords chords)⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.PeriodCoordinates.CutBank

end
end
