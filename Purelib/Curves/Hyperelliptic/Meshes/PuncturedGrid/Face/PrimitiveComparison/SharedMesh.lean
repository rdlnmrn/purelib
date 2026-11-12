module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.Paths
public import Purelib.Riemann.Readings.RectangularPointReadings.SharedMesh.Paths
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Paths.ClearBoxPaths.Chord
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction

/-! # Both rooted child words on the same retained numerical mesh

The original shared-mesh path producer supplies both literal leg words.
The retained start, corner and finish Points supply their genuine Entry
lineage. Each word uses the shared transport algorithm; the same corner
Point is literally the target of the first leg and source of the second.
The primitive bank, lookups and shared numerical readings are unchanged.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (TracedPoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rectangle (AxisPartition)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization.RectangularInverseModels (Bank)
open Purelib.Riemann.Readings.RectangularPointReadings.Chord (MeshReadings)
open Purelib.Riemann.Readings.RectangularPointReadings.Chord.MeshReadings
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentSplit)
open Purelib.Riemann.Paths
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing

universe u

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
    {models : FaceModels frames face} {domainSheet : Fin 2}
    (domain : PeriodDomain models domainSheet)
    {numerator : Polynomial} {numericalModels : Bank curve.polynomial domain.geometry}
    {primitives : Primitives numericalModels numerator} {anchors : PrimitiveAnchors primitives}
    {offsets : Offsets anchors.edges} {cuts : GridCuts domain.geometry}
    {sourceStart sourceFinish : Canonical}
    (split : SegmentSplit cuts sourceStart sourceFinish) (cached : MeshReadings split anchors offsets)
    (position : Fin split.pieces.length)
    {firstSheet middleSheet lastSheet : Fin 2} {start corner finish : Canonical}
    {firstInside : face.cell.box.Contains start} {middleInside : face.cell.box.Contains corner}
    {lastInside : face.cell.box.Contains finish} {firstCount middleCount lastCount : Nat}
    {firstFrame : OwnerFrame (curve.polynomial.eval start)}
    {middleFrame : OwnerFrame (curve.polynomial.eval corner)}
    {lastFrame : OwnerFrame (curve.polynomial.eval finish)}
    (first : TracedPoint models firstSheet start firstInside firstCount firstFrame)
    (middle : TracedPoint models middleSheet corner middleInside middleCount middleFrame)
    (last : TracedPoint models lastSheet finish lastInside lastCount lastFrame)
    (firstLineage : first.entry.sheet = middle.entry.sheet)
    (lastLineage : middle.entry.sheet = last.entry.sheet)
    (firstPointEq : (split.pieces[position.val]'position.isLt).firstPoint = start)
    (middlePointEq : ClearBoxPaths.Chord.corner (split.pieces[position.val]'position.isLt).firstPoint
      (split.pieces[position.val]'position.isLt).lastPoint = corner)
    (lastPointEq : (split.pieces[position.val]'position.isLt).lastPoint = finish)

/-- Both original axis preparations and rooted word caches on the same start, corner and finish Points.

All geometry, source labels, exact source factories, endpoint chains and
numerical telescope equality are the original shared-mesh producer's
outputs. The two actual transport consumers retain each segment product,
row, Point selector and endpoint joins. No closing or payment is asserted.
-/
@[expose] def PieceConsumer (Result : Type u) :=
  (firstCoordinate : (MeshReadings.mesh split cached).surface.mesh.coordinate
    (((MeshReadings.lookups split cached).get position).get 1).index = start) →
  (middleCoordinate : (MeshReadings.mesh split cached).surface.mesh.coordinate
    (((MeshReadings.lookups split cached).get position).get 0).index = corner) →
  (lastCoordinate : (MeshReadings.mesh split cached).surface.mesh.coordinate
    (((MeshReadings.lookups split cached).get position).get 2).index = finish) →
  (choice : Paths.CellChoice split position) →
  (height : {value : AxisPartition.Endpoint (Paths.partition split cached position choice).y
      (split.pieces[position.val]'position.isLt).firstPoint.im //
    value = (Paths.partition split cached position choice).y.endpoint
      (split.pieces[position.val]'position.isLt).firstPoint.im
      (Paths.endpoint_members split cached position choice).2.1}) →
  (row : Paths.AxisPosition (Paths.partition split cached position choice).y height.val.interval) →
  (width : {value : AxisPartition.Endpoint (Paths.partition split cached position choice).x
      (split.pieces[position.val]'position.isLt).lastPoint.re //
    value = (Paths.partition split cached position choice).x.endpoint
      (split.pieces[position.val]'position.isLt).lastPoint.re
      (Paths.endpoint_members split cached position choice).2.2.1}) →
  (column : Paths.AxisPosition (Paths.partition split cached position choice).x width.val.interval) →
  (horizontal : {value : AxisWalks.Walk (Paths.partition split cached position choice).x.intervals
      (split.pieces[position.val]'position.isLt).firstPoint.re
      (split.pieces[position.val]'position.isLt).lastPoint.re //
    value = (Paths.partition split cached position choice).x.between
      (split.pieces[position.val]'position.isLt).firstPoint.re (split.pieces[position.val]'position.isLt).lastPoint.re
      (Paths.endpoint_members split cached position choice).1
      (Paths.endpoint_members split cached position choice).2.2.1}) →
  (vertical : {value : AxisWalks.Walk (Paths.partition split cached position choice).y.intervals
      (split.pieces[position.val]'position.isLt).firstPoint.im
      (split.pieces[position.val]'position.isLt).lastPoint.im //
    value = (Paths.partition split cached position choice).y.between
      (split.pieces[position.val]'position.isLt).firstPoint.im (split.pieces[position.val]'position.isLt).lastPoint.im
      (Paths.endpoint_members split cached position choice).2.1
      (Paths.endpoint_members split cached position choice).2.2.2}) →
  (horizontalSources : {value : List (SourceEdge
      ((MeshReadings.mesh split cached).triangles.map ModelTriangle.triangle).length) //
    value = (MeshReadings.mesh split cached).horizontalSources
      choice.val.index row.val.index height.val.high horizontal.val}) →
  (verticalSources : {value : List (SourceEdge
      ((MeshReadings.mesh split cached).triangles.map ModelTriangle.triangle).length) //
    value = (MeshReadings.mesh split cached).verticalSources
      choice.val.index column.val.index width.val.high vertical.val}) →
  CutPath.Supported (Topology.Polygon.Stokes.triangleEdgeOccurrences
      (MeshReadings.mesh split cached).surface.mesh.triangulation.faces)
    (horizontalSources.val.map
      (fun source => source.project (MeshReadings.mesh split cached).surface.mesh.triangulation.faces)) →
  PathEndpoints OrientedEdge.start OrientedEdge.finish
    (horizontalSources.val.map
      (fun source => source.project (MeshReadings.mesh split cached).surface.mesh.triangulation.faces))
    (((MeshReadings.lookups split cached).get position).get 1).index
    (((MeshReadings.lookups split cached).get position).get 0).index →
  CutPath.Supported (Topology.Polygon.Stokes.triangleEdgeOccurrences
      (MeshReadings.mesh split cached).surface.mesh.triangulation.faces)
    (verticalSources.val.map
      (fun source => source.project (MeshReadings.mesh split cached).surface.mesh.triangulation.faces)) →
  PathEndpoints OrientedEdge.start OrientedEdge.finish
    (verticalSources.val.map
      (fun source => source.project (MeshReadings.mesh split cached).surface.mesh.triangulation.faces))
    (((MeshReadings.lookups split cached).get position).get 0).index
    (((MeshReadings.lookups split cached).get position).get 2).index →
  (SewingRetraction.wordValue
      (fun edge : OrientedEdge (MeshReadings.mesh split cached).surface.mesh.vertices.length =>
        (MeshReadings.shared split cached).values edge.finish - (MeshReadings.shared split cached).values edge.start)
      (horizontalSources.val.map
      (fun source => source.project (MeshReadings.mesh split cached).surface.mesh.triangulation.faces)) +
    SewingRetraction.wordValue
      (fun edge : OrientedEdge (MeshReadings.mesh split cached).surface.mesh.vertices.length =>
        (MeshReadings.shared split cached).values edge.finish - (MeshReadings.shared split cached).values edge.start)
      (verticalSources.val.map
      (fun source => source.project (MeshReadings.mesh split cached).surface.mesh.triangulation.faces)) =
    SewingRetraction.wordValue
      (fun edge : OrientedEdge (MeshReadings.mesh split cached).surface.mesh.vertices.length =>
        (MeshReadings.shared split cached).values edge.finish - (MeshReadings.shared split cached).values edge.start)
      (MeshReadings.word split cached position)) →
  HorizontalConsumer (domain := domain) (mesh := MeshReadings.mesh split cached)
    (first := first) (last := middle) (cellPosition := choice.val.index)
    (rowIndex := row.val.index) (high := height.val.high) (walk := horizontal.val)
    (sources := horizontalSources.val)
    (firstIndex := (((MeshReadings.lookups split cached).get position).get 1).index)
    (lastIndex := (((MeshReadings.lookups split cached).get position).get 0).index)
    (firstEq := firstCoordinate) (lastEq := middleCoordinate)
    (VerticalConsumer (domain := domain) (mesh := MeshReadings.mesh split cached)
      (first := middle) (last := last) (sources := verticalSources.val)
      (firstIndex := (((MeshReadings.lookups split cached).get position).get 0).index)
      (lastIndex := (((MeshReadings.lookups split cached).get position).get 2).index)
      (firstEq := middleCoordinate) (lastEq := lastCoordinate)
      choice.val.index column.val.index width.val.high vertical.val Result)

/-- Execute both original child leg producers and transport their retained words between the same three actual Points.

The old lookup readbacks derive geometric endpoint incidences internally.
The supplied Entry lineage is genuine same-face evidence from the three
retained acquisitions; coordinate equality is never used as root evidence.
The horizontal row and its joins are constructed before the vertical row.
A stationary leg keeps its original outer slot and empty inner word, with
its distinct Point owners, actual row and both joins still retained.
-/
def withPieceWords {Result : Type u}
    (consume : PieceConsumer (domain := domain) (split := split) (cached := cached) (position := position)
      (first := first) (middle := middle) (last := last) Result) : Result :=
  let piece := split.pieces[position.val]'position.isLt
  have coordinates := ClearBoxPaths.Chord.coordinate_values piece.firstPoint piece.lastPoint
  have firstCoordinate : (MeshReadings.mesh split cached).surface.mesh.coordinate
      (((MeshReadings.lookups split cached).get position).get 1).index = start :=
    (((MeshReadings.lookups split cached).get position).get 1).coordinate_eq.trans
      (coordinates.2.1.trans firstPointEq)
  have middleCoordinate : (MeshReadings.mesh split cached).surface.mesh.coordinate
      (((MeshReadings.lookups split cached).get position).get 0).index = corner :=
    (((MeshReadings.lookups split cached).get position).get 0).coordinate_eq.trans
      (coordinates.1.trans middlePointEq)
  have lastCoordinate : (MeshReadings.mesh split cached).surface.mesh.coordinate
      (((MeshReadings.lookups split cached).get position).get 2).index = finish :=
    (((MeshReadings.lookups split cached).get position).get 2).coordinate_eq.trans
      (coordinates.2.2.trans lastPointEq)
  Paths.withPaths split cached position
    (fun choice height row width column horizontal vertical horizontalSources verticalSources
      horizontalSupported horizontalEnds verticalSupported verticalEnds valuesEq =>
      withHorizontalWord (domain := domain) (mesh := MeshReadings.mesh split cached)
        (first := first) (last := middle) (lineage := firstLineage)
        (cellPosition := choice.val.index) (rowIndex := row.val.index) (high := height.val.high)
        (walk := horizontal.val) (sources := horizontalSources.val) (sources_eq := horizontalSources.property)
        (firstIndex := (((MeshReadings.lookups split cached).get position).get 1).index)
        (lastIndex := (((MeshReadings.lookups split cached).get position).get 0).index)
        (ends := horizontalEnds) (firstEq := firstCoordinate) (lastEq := middleCoordinate)
        (fun hKept hFactory hEnds hSupported hAligned hSegments hSegmentsEq hChain hRaw hRawEq hRawCount
          hPath hPathEq hCount hWithin hContained hEntry hEntryEq hSame hRow hRowEq hTarget hEquivalent
          hEquivalentEq hSourceJoin hSourceJoinEq hTargetJoin hTargetJoinEq hOwnerPath hOwnerPathEq =>
          withVerticalWord (domain := domain) (mesh := MeshReadings.mesh split cached)
            (first := middle) (last := last) (lineage := lastLineage) (sources := verticalSources.val)
            (firstIndex := (((MeshReadings.lookups split cached).get position).get 0).index)
            (lastIndex := (((MeshReadings.lookups split cached).get position).get 2).index)
            (ends := verticalEnds) (firstEq := middleCoordinate) (lastEq := lastCoordinate)
            choice.val.index column.val.index width.val.high vertical.val verticalSources.property
            (consume firstCoordinate middleCoordinate lastCoordinate choice height row width column horizontal vertical
              horizontalSources verticalSources horizontalSupported horizontalEnds verticalSupported verticalEnds
              valuesEq
              hKept hFactory hEnds hSupported hAligned hSegments hSegmentsEq hChain hRaw hRawEq hRawCount
              hPath hPathEq hCount hWithin hContained hEntry hEntryEq hSame hRow hRowEq hTarget hEquivalent
              hEquivalentEq hSourceJoin hSourceJoinEq hTargetJoin hTargetJoinEq hOwnerPath hOwnerPathEq)))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

end
