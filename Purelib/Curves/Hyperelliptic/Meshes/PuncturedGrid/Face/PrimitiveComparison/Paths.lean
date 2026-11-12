module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.TracedPoint
public import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.Paths
public import Purelib.Polynomial.Geometry.ClearPath.Segments
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.SegmentPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Transport
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Topology.Surface.Cut.JumpPaths

/-! # Actual root transport along retained supported mesh words

Each original source occurrence retains one clear segment in its actual
orientation. The same cached segment product builds the clear path; one
real transport row connects the given Point frames. Entry lineage and the
actual target selector derive agreement with the same retained Point.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry (TracedPoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels (CommonMesh)
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Polynomial.Geometry.Grid.AxisWalks (Walk)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.RootContinuation.RootPathTransport (TransportRow)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName OwnerJoin)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Polygon.Stokes (OrientedEdge triangleEdgeOccurrences)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)

universe u

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
    {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
    {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face : RegularFace bank}
    {models : FaceModels frames face} {domainSheet : Fin 2}
    (domain : PeriodDomain models domainSheet)
    {selection : List (Fin (domain.steps + 1) × Fin (domain.steps + 1))} {points : List Canonical}
    (mesh : CommonMesh domain.geometry selection points)

/-- Each stored mesh vertex lies in the original face through its actual retained coarse-cell owner. -/
private theorem vertex_inside (vertex : Fin mesh.surface.mesh.vertices.length) :
    face.cell.box.Contains (mesh.surface.mesh.coordinate vertex) :=
  (domain.patch.cell_refines (mesh.surface.owners vertex).column (mesh.surface.owners vertex).row).contains
    (mesh.surface.owner_inside vertex)

/-- One original contained clear segment at every original source-edge occurrence. -/
abbrev Segments (sources : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)) :=
  ClearPath.Segments (polynomial := curve.polynomial) (ambient := face.cell.box)
    mesh.surface.mesh.coordinate
    (fun source => (source.project mesh.surface.mesh.triangulation.faces).start)
    (fun source => (source.project mesh.surface.mesh.triangulation.faces).finish) sources

/-- Certify one actual horizontal source-edge occurrence from its original endpoints and face clearance. -/
def horizontalSegment (source : SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)
    (height : (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).im =
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).im) :
    {segment : ClearPath.ClearSegment curve.polynomial face.cell.box
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start)
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish) //
      segment.WithinAmbient} :=
  let edge := source.project mesh.surface.mesh.triangulation.faces
  let first := vertex_inside domain mesh edge.start
  let last := vertex_inside domain mesh edge.finish
  ⟨SegmentPreparation.horizontalSegment models _ _ first last height,
    SegmentPreparation.horizontalSegment_within models _ _ first last height⟩

/-- Construct the original horizontal segments once in their supplied source order.

The actual endpoint coordinates and original face clearance determine each
segment. Its source label and orientation remain the exact retained mesh
occurrence; no coordinate search or point preparation is performed.
-/
def horizontalSegments (sources : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length))
    (aligned : ∀ source ∈ sources,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).im =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).im) :
    Segments domain mesh sources :=
  DependentProduct.ofFn sources (fun index => horizontalSegment domain mesh (sources[index.val]'index.isLt)
    (aligned (sources[index.val]'index.isLt) (List.getElem_mem index.isLt)))

/-- Each stored segment is the same complete original source-occurrence factory, read without rebuilding it. -/
theorem horizontalSegments_get
    (sources : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length))
    (aligned : ∀ source ∈ sources,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).im =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).im)
    (index : Fin sources.length) :
    DependentProduct.get sources (horizontalSegments domain mesh sources aligned) index =
      horizontalSegment domain mesh (sources[index.val]'index.isLt)
        (aligned (sources[index.val]'index.isLt) (List.getElem_mem index.isLt)) :=
  DependentProduct.get_ofFn sources _ index

/-- Certify one actual vertical source-edge occurrence from its original endpoints and face clearance. -/
def verticalSegment (source : SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)
    (width : (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).re =
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).re) :
    {segment : ClearPath.ClearSegment curve.polynomial face.cell.box
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start)
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish) //
      segment.WithinAmbient} :=
  let edge := source.project mesh.surface.mesh.triangulation.faces
  let first := vertex_inside domain mesh edge.start
  let last := vertex_inside domain mesh edge.finish
  ⟨SegmentPreparation.verticalSegment models _ _ first last width,
    SegmentPreparation.verticalSegment_within models _ _ first last width⟩

/-- Construct the original vertical segments once in their supplied source order.

The actual endpoint coordinates and original face clearance determine each
segment. Its source label and orientation remain the exact retained mesh
occurrence; no coordinate search or point preparation is performed.
-/
def verticalSegments (sources : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length))
    (aligned : ∀ source ∈ sources,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).re =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).re) :
    Segments domain mesh sources :=
  DependentProduct.ofFn sources (fun index => verticalSegment domain mesh (sources[index.val]'index.isLt)
    (aligned (sources[index.val]'index.isLt) (List.getElem_mem index.isLt)))

/-- Each stored segment is the same complete original source-occurrence factory, read without rebuilding it. -/
theorem verticalSegments_get
    (sources : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length))
    (aligned : ∀ source ∈ sources,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).re =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).re)
    (index : Fin sources.length) :
    DependentProduct.get sources (verticalSegments domain mesh sources aligned) index =
      verticalSegment domain mesh (sources[index.val]'index.isLt)
        (aligned (sources[index.val]'index.isLt) (List.getElem_mem index.isLt)) :=
  DependentProduct.get_ofFn sources _ index

/-- Pull the supplied projected endpoint chain back to the same original source labels. -/
private theorem source_chain :
    (sources : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)) →
    {first last : Fin mesh.surface.mesh.vertices.length} →
    PathEndpoints OrientedEdge.start OrientedEdge.finish
      (sources.map (fun source => source.project mesh.surface.mesh.triangulation.faces)) first last →
    PathEndpoints (fun source => (source.project mesh.surface.mesh.triangulation.faces).start)
      (fun source => (source.project mesh.surface.mesh.triangulation.faces).finish) sources first last
  | [], _, _, ends => by
      have equal := ends.nil_eq
      cases equal
      exact .nil _
  | head :: tail, _, _, ends => by
      have equal := ends.cons_start
      exact (PathEndpoints.cons (edge := head) (source_chain tail ends.cons_tail)).castStart equal.symm

/-- Exact endpoint transport preserves the original path's actual containment. -/
private theorem cast_within {first last start finish : Canonical}
    (path : ClearPath curve.polynomial face.cell.box first last) (within : path.WithinAmbient)
    (firstEq : first = start) (lastEq : last = finish) :
    (ClearPath.castFinish lastEq (ClearPath.castStart firstEq path)).WithinAmbient := by
  cases firstEq
  cases lastEq
  exact within

variable {firstSheet lastSheet : Fin 2} {start finish : Canonical}
    {firstInside : face.cell.box.Contains start} {lastInside : face.cell.box.Contains finish}
    {firstCount lastCount : Nat} {firstFrame : OwnerFrame (curve.polynomial.eval start)}
    {lastFrame : OwnerFrame (curve.polynomial.eval finish)}
    (first : TracedPoint models firstSheet start firstInside firstCount firstFrame)
    (last : TracedPoint models lastSheet finish lastInside lastCount lastFrame)
    (lineage : first.entry.sheet = last.entry.sheet)
    (sources : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length))
    (firstIndex lastIndex : Fin mesh.surface.mesh.vertices.length)
    (ends : PathEndpoints OrientedEdge.start OrientedEdge.finish
      (sources.map (fun source => source.project mesh.surface.mesh.triangulation.faces)) firstIndex lastIndex)
    (firstEq : mesh.surface.mesh.coordinate firstIndex = start)
    (lastEq : mesh.surface.mesh.coordinate lastIndex = finish)

/-- The actual contained word, transport row, target agreement and joins on the same supplied segment cache.

Both retained Point owners remain unchanged. Every geometric segment is
indexed by its original source occurrence; the transport and both joins
retain their complete factories. No primitive or observation is evaluated.
-/
@[expose] def WordConsumer (segments : Segments domain mesh sources) (Result : Type u) :=
  (chain : PathEndpoints (fun source => (source.project mesh.surface.mesh.triangulation.faces).start)
    (fun source => (source.project mesh.surface.mesh.triangulation.faces).finish) sources firstIndex lastIndex) →
  (raw : {path : ClearPath curve.polynomial face.cell.box (mesh.surface.mesh.coordinate firstIndex)
      (mesh.surface.mesh.coordinate lastIndex) // path.WithinAmbient}) →
  raw = ClearPath.ofSegments (polynomial := curve.polynomial) (ambient := face.cell.box)
    mesh.surface.mesh.coordinate
    (fun source => (source.project mesh.surface.mesh.triangulation.faces).start)
    (fun source => (source.project mesh.surface.mesh.triangulation.faces).finish) sources segments chain →
  raw.val.segmentCount = sources.length →
  (path : ClearPath curve.polynomial face.cell.box start finish) →
  path = ClearPath.castFinish lastEq (ClearPath.castStart firstEq raw.val) →
  path.segmentCount = sources.length →
  (within : path.WithinAmbient) →
  (contained : InBox face.cell.box path) →
  (entered : Entry models start (first.frame.owners first.selected.index)) →
  entered = first.entry.followEquivalent first.selected.equivalent →
  (same : entered.sheet = lastSheet) →
  (transport : TransportRow path first.frame last.frame first.selected.index) →
  transport = TransportRow.build path within first.frame last.frame first.selected.index →
  transport.target = last.selected.index →
  (equivalent : NamedEquivalent (ownerName transport.traced.finishOwner) (ownerName last.sample.owner)) →
  equivalent = last.sourceFrameEquivalent entered same contained last.frame last.selected transport →
  (sourceJoin : OwnerJoin first.sample.owner (first.frame.owners first.selected.index)) →
  sourceJoin = OwnerJoin.acquire first.sample.owner (first.frame.owners first.selected.index)
    first.selected.equivalent →
  (targetJoin : OwnerJoin transport.traced.finishOwner last.sample.owner) →
  targetJoin = OwnerJoin.acquire transport.traced.finishOwner last.sample.owner equivalent →
  (ownerPath : OwnerPath curve.polynomial start first.sample.owner finish last.sample.owner) →
  ownerPath = .cons (OwnerLink.stationary curve.polynomial start sourceJoin)
    (transport.traced.trace.get.append
      (.cons (OwnerLink.stationary curve.polynomial finish targetJoin) (.nil finish last.sample.owner))) → Result

/-- Transport one supplied supported word using its actual contained segment cache and original Point frames.

The source support and exact endpoint chain name the same original word.
Endpoint equalities transport geometric indices only. The given Entry
lineage, actual transport row and retained target selector derive the
root agreement; the same algorithm also retains both joins for an empty
word. New joins carry no numerical payment here.
-/
def withWord (segments : Segments domain mesh sources)
    (_supported : CutPath.Supported (triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
      (sources.map (fun source => source.project mesh.surface.mesh.triangulation.faces)))
    {Result : Type u}
    (consume : WordConsumer (domain := domain) (mesh := mesh) (first := first) (last := last)
      (sources := sources) (firstIndex := firstIndex) (lastIndex := lastIndex)
      (firstEq := firstEq) (lastEq := lastEq) segments Result) : Result :=
  let chain := source_chain domain mesh sources ends
  let raw := ClearPath.ofSegments (polynomial := curve.polynomial) (ambient := face.cell.box)
    mesh.surface.mesh.coordinate
    (fun source => (source.project mesh.surface.mesh.triangulation.faces).start)
    (fun source => (source.project mesh.surface.mesh.triangulation.faces).finish) sources segments chain
  let path := ClearPath.castFinish lastEq (ClearPath.castStart firstEq raw.val)
  have rawCount : raw.val.segmentCount = sources.length :=
    ClearPath.ofSegments_count (polynomial := curve.polynomial) (ambient := face.cell.box)
      mesh.surface.mesh.coordinate
      (fun source => (source.project mesh.surface.mesh.triangulation.faces).start)
      (fun source => (source.project mesh.surface.mesh.triangulation.faces).finish) sources segments chain
  have pathCount : path.segmentCount = sources.length :=
    (ClearPath.segmentCount_castFinish lastEq (ClearPath.castStart firstEq raw.val)).trans
      ((ClearPath.segmentCount_castStart firstEq raw.val).trans rawCount)
  have within : path.WithinAmbient := cast_within raw.val raw.property firstEq lastEq
  have contained : InBox face.cell.box path := InBox.ofWithin path within firstInside
  let entered := first.entry.followEquivalent first.selected.equivalent
  have same : entered.sheet = lastSheet :=
    (first.entry.followEquivalent_sheet first.selected.equivalent).trans (lineage.trans last.entry_sheet)
  let transport := TransportRow.build path within first.frame last.frame first.selected.index
  have target := last.sourceFrameTarget_eq entered same contained last.frame last.selected transport
  let equivalent := last.sourceFrameEquivalent entered same contained last.frame last.selected transport
  let sourceJoin := OwnerJoin.acquire first.sample.owner (first.frame.owners first.selected.index)
    first.selected.equivalent
  let targetJoin := OwnerJoin.acquire transport.traced.finishOwner last.sample.owner equivalent
  let ownerPath := OwnerPath.cons (OwnerLink.stationary curve.polynomial start sourceJoin)
    (transport.traced.trace.get.append
      (.cons (OwnerLink.stationary curve.polynomial finish targetJoin) (.nil finish last.sample.owner)))
  consume chain raw rfl rawCount path rfl pathCount within contained entered rfl same transport rfl target
    equivalent rfl sourceJoin rfl targetJoin rfl ownerPath rfl

variable (cellPosition : Fin selection.length)
    (rowIndex : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool)
    {left right : Rational}
    (walk : Walk (mesh.cells.get cellPosition).partition.x.intervals left right)
    (sources_eq : sources = mesh.horizontalSources cellPosition rowIndex high walk)

/-- The complete actual horizontal-word transport cache, with both original Points and every source occurrence kept. -/
@[expose] def HorizontalConsumer (Result : Type u) :=
  (_kept : {value : TracedPoint models firstSheet start firstInside firstCount firstFrame ×
      TracedPoint models lastSheet finish lastInside lastCount lastFrame ×
      Walk (mesh.cells.get cellPosition).partition.x.intervals left right ×
      List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length) //
    value = (first, last, walk, sources)}) →
  sources = mesh.horizontalSources cellPosition rowIndex high walk →
  PathEndpoints OrientedEdge.start OrientedEdge.finish
    (sources.map (fun source => source.project mesh.surface.mesh.triangulation.faces)) firstIndex lastIndex →
  CutPath.Supported (triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
    (sources.map (fun source => source.project mesh.surface.mesh.triangulation.faces)) →
  (aligned : ∀ source ∈ sources,
    (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).im =
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).im) →
  (segments : Segments domain mesh sources) →
  segments = horizontalSegments domain mesh sources aligned →
  WordConsumer (domain := domain) (mesh := mesh) (first := first) (last := last)
    (sources := sources) (firstIndex := firstIndex) (lastIndex := lastIndex)
    (firstEq := firstEq) (lastEq := lastEq) segments Result

/-- Trace the same supported horizontal word between the actual retained Point frames and derive target agreement.

The original endpoint and coordinate certificates transport only geometric
indices. Actual Entry lineage, the new transport's target selection and
the old target Point selector prove their index and root agreement. The
supplied actual Entry sheet equality comes from the retained physical
crop and acquisition lineage. Both new stationary joins are retained separately; this constructor makes no
payment, cross-face identification or closing assertion.
-/
def withHorizontalWord {Result : Type u}
    (consume : HorizontalConsumer (domain := domain) (mesh := mesh) (first := first) (last := last)
      (cellPosition := cellPosition) (rowIndex := rowIndex) (high := high) (walk := walk) (sources := sources)
      (firstIndex := firstIndex) (lastIndex := lastIndex) (firstEq := firstEq) (lastEq := lastEq) Result) : Result :=
  have aligned : ∀ source ∈ sources,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).im =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).im :=
    Eq.mpr (congrArg (fun values => ∀ source ∈ values,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).im =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).im) sources_eq)
      (mesh.horizontalSources_height cellPosition rowIndex high walk)
  have supported : CutPath.Supported (triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
      (sources.map (fun source => source.project mesh.surface.mesh.triangulation.faces)) :=
    Eq.mpr (congrArg (fun values => CutPath.Supported (triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
      (values.map (fun source => source.project mesh.surface.mesh.triangulation.faces))) sources_eq)
      (mesh.horizontalSources_supported cellPosition rowIndex high walk)
  let segments := horizontalSegments domain mesh sources aligned
  withWord (domain := domain) (mesh := mesh) (first := first) (last := last) (lineage := lineage)
    (sources := sources) (firstIndex := firstIndex) (lastIndex := lastIndex) (ends := ends)
    (firstEq := firstEq) (lastEq := lastEq) segments supported
    (consume ⟨(first, last, walk, sources), rfl⟩ sources_eq ends supported aligned segments rfl)

/-- The complete actual vertical-word cache, retaining its original axis walk and every source occurrence. -/
@[expose] def VerticalConsumer
    (cellPosition : Fin selection.length)
    (columnIndex : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool)
    {bottom top : Rational}
    (walk : Walk (mesh.cells.get cellPosition).partition.y.intervals bottom top) (Result : Type u) :=
  (_kept : {value : TracedPoint models firstSheet start firstInside firstCount firstFrame ×
      TracedPoint models lastSheet finish lastInside lastCount lastFrame ×
      Walk (mesh.cells.get cellPosition).partition.y.intervals bottom top ×
      List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length) //
    value = (first, last, walk, sources)}) →
  sources = mesh.verticalSources cellPosition columnIndex high walk →
  PathEndpoints OrientedEdge.start OrientedEdge.finish
    (sources.map (fun source => source.project mesh.surface.mesh.triangulation.faces)) firstIndex lastIndex →
  CutPath.Supported (triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
    (sources.map (fun source => source.project mesh.surface.mesh.triangulation.faces)) →
  (aligned : ∀ source ∈ sources,
    (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).re =
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).re) →
  (segments : Segments domain mesh sources) →
  segments = verticalSegments domain mesh sources aligned →
  WordConsumer (domain := domain) (mesh := mesh) (first := first) (last := last)
    (sources := sources) (firstIndex := firstIndex) (lastIndex := lastIndex)
    (firstEq := firstEq) (lastEq := lastEq) segments Result

/-- Construct the vertical source-segment cache once, then use the shared actual-word transport and join algorithm.

Reversed and stationary walks keep the same original source factories.
Only the axis-specific geometry differs from the horizontal constructor;
all root transport, target agreement and endpoint joins use withWord.
-/
def withVerticalWord
    (cellPosition : Fin selection.length)
    (columnIndex : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool)
    {bottom top : Rational}
    (walk : Walk (mesh.cells.get cellPosition).partition.y.intervals bottom top)
    (sources_eq : sources = mesh.verticalSources cellPosition columnIndex high walk)
    {Result : Type u}
    (consume : VerticalConsumer (domain := domain) (mesh := mesh) (first := first) (last := last)
      (sources := sources) (firstIndex := firstIndex) (lastIndex := lastIndex)
      (firstEq := firstEq) (lastEq := lastEq) cellPosition columnIndex high walk Result) : Result :=
  have aligned : ∀ source ∈ sources,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).re =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).re :=
    Eq.mpr (congrArg (fun values => ∀ source ∈ values,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).re =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).re) sources_eq)
      (mesh.verticalSources_width cellPosition columnIndex high walk)
  have supported : CutPath.Supported (triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
      (sources.map (fun source => source.project mesh.surface.mesh.triangulation.faces)) :=
    Eq.mpr (congrArg (fun values => CutPath.Supported (triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
      (values.map (fun source => source.project mesh.surface.mesh.triangulation.faces))) sources_eq)
      (mesh.verticalSources_supported cellPosition columnIndex high walk)
  let segments := verticalSegments domain mesh sources aligned
  withWord (domain := domain) (mesh := mesh) (first := first) (last := last) (lineage := lineage)
    (sources := sources) (firstIndex := firstIndex) (lastIndex := lastIndex) (ends := ends)
    (firstEq := firstEq) (lastEq := lastEq) segments supported
    (consume ⟨(first, last, walk, sources), rfl⟩ sources_eq ends supported aligned segments rfl)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveComparison.FaceModels

end
