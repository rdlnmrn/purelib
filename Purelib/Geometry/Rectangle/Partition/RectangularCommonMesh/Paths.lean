module

public import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.Indexed
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Polygon.Stokes
public import Purelib.Polynomial.Geometry.Grid.AxisWalks.Steps
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
public import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Chain.PathBoundary
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.List.Reverse
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction

/-! # Exact indexed joins on the retained common-mesh factory

Coordinate realization alone does not identify vertex indices. The actual
common-mesh factory supplies the first-occurrence indexing law for each
retained source corner. This law gives exact joins for geometrically
adjacent source edges without replacing either original source occurrence.
No continued-root or physical Point equality follows from these statements.
-/

public section

namespace Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels.CommonMesh

open Purelib.Topology.Polygon
open Purelib
open Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Topology.Mesh
open Purelib.Topology.Polygon.Stokes (OrientedTriangle)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (corner)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.AxisWalks (IncreasingWalk)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List

variable {columns rows : Nat} {geometry : Geometry columns rows}
    {points : List Data.Gaussian.Basic.Canonical} {selection : List (Fin (columns + 1) × Fin (rows + 1))}
    (mesh : CommonMesh geometry selection points)
    (factory : mesh = CommonMesh.build geometry selection points)

include factory in
/-- Each actual source-face corner uses the original first lookup, by the complete retained mesh factory. -/
theorem corner_lookup (source : Fin (mesh.triangles.map ModelTriangle.triangle).length) (slot : Fin 3)
    (point : Data.Gaussian.Basic.Canonical) (member : point ∈ mesh.surface.mesh.vertices) :
    mesh.surface.mesh.coordinate (corner (mesh.surface.mesh.triangulation.faces source) slot) = point →
      corner (mesh.surface.mesh.triangulation.faces source) slot =
        (CoordinateTriangulation.lookupVertex point mesh.surface.mesh.vertices member).index := by
  let triangle := (mesh.triangles.map ModelTriangle.triangle)[source.val]'source.isLt
  have original := mesh.surface.mesh.face_coordinates source
  have firstMember : triangle.first ∈ mesh.surface.mesh.vertices :=
    Eq.mp (congrArg (fun point => point ∈ mesh.surface.mesh.vertices) original.1) (List.getElem_mem _)
  have secondMember : triangle.second ∈ mesh.surface.mesh.vertices :=
    Eq.mp (congrArg (fun point => point ∈ mesh.surface.mesh.vertices) original.2.1) (List.getElem_mem _)
  have thirdMember : triangle.third ∈ mesh.surface.mesh.vertices :=
    Eq.mp (congrArg (fun point => point ∈ mesh.surface.mesh.vertices) original.2.2) (List.getElem_mem _)
  have actual : mesh.surface.mesh.triangulation.faces source =
      CoordinateTriangulation.indexTriangle mesh.surface.mesh.vertices triangle
        ⟨firstMember, secondMember, thirdMember⟩ :=
    (mesh.surface.mesh.faces_eq source).trans
      (mesh.surface.mesh.faces_eq_indexTriangle (mesh.surface_factory factory) source
        ⟨firstMember, secondMember, thirdMember⟩)
  have firstCase :
      mesh.surface.mesh.coordinate (corner (mesh.surface.mesh.triangulation.faces source) 0) = point →
        corner (mesh.surface.mesh.triangulation.faces source) 0 =
          (CoordinateTriangulation.lookupVertex point mesh.surface.mesh.vertices member).index := by
    intro equal
    change mesh.surface.mesh.coordinate (mesh.surface.mesh.triangulation.faces source).first = point at equal
    change (mesh.surface.mesh.triangulation.faces source).first = _
    exact (congrArg OrientedTriangle.first actual).trans
      (CoordinateTriangulation.lookupVertex_same mesh.surface.mesh.vertices firstMember member
        (original.1.symm.trans equal))
  have secondCase :
      mesh.surface.mesh.coordinate (corner (mesh.surface.mesh.triangulation.faces source) 1) = point →
        corner (mesh.surface.mesh.triangulation.faces source) 1 =
          (CoordinateTriangulation.lookupVertex point mesh.surface.mesh.vertices member).index := by
    intro equal
    change mesh.surface.mesh.coordinate (mesh.surface.mesh.triangulation.faces source).second = point at equal
    change (mesh.surface.mesh.triangulation.faces source).second = _
    exact (congrArg OrientedTriangle.second actual).trans
      (CoordinateTriangulation.lookupVertex_same mesh.surface.mesh.vertices secondMember member
        (original.2.1.symm.trans equal))
  have thirdCase :
      mesh.surface.mesh.coordinate (corner (mesh.surface.mesh.triangulation.faces source) 2) = point →
        corner (mesh.surface.mesh.triangulation.faces source) 2 =
          (CoordinateTriangulation.lookupVertex point mesh.surface.mesh.vertices member).index := by
    intro equal
    change mesh.surface.mesh.coordinate (mesh.surface.mesh.triangulation.faces source).third = point at equal
    change (mesh.surface.mesh.triangulation.faces source).third = _
    exact (congrArg OrientedTriangle.third actual).trans
      (CoordinateTriangulation.lookupVertex_same mesh.surface.mesh.vertices thirdMember member
        (original.2.2.symm.trans equal))
  exact Fin.cases firstCase (Fin.cases secondCase (Fin.cases thirdCase (fun index => Fin.elim0 index))) slot

include factory in
/-- The beginning of an actual retained source edge is the checked first-occurrence lookup of its coordinate. -/
theorem source_start_lookup (source : SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)
    (point : Data.Gaussian.Basic.Canonical) (member : point ∈ mesh.surface.mesh.vertices)
    (equal : mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start = point) :
    (source.project mesh.surface.mesh.triangulation.faces).start =
      (CoordinateTriangulation.lookupVertex point mesh.surface.mesh.vertices member).index :=
  mesh.corner_lookup factory source.source source.first point member equal

include factory in
/-- The finish of an actual retained source edge is the checked first-occurrence lookup of its coordinate. -/
theorem source_finish_lookup (source : SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)
    (point : Data.Gaussian.Basic.Canonical) (member : point ∈ mesh.surface.mesh.vertices)
    (equal : mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish = point) :
    (source.project mesh.surface.mesh.triangulation.faces).finish =
      (CoordinateTriangulation.lookupVertex point mesh.surface.mesh.vertices member).index :=
  mesh.corner_lookup factory source.source source.last point member equal

include factory in
/-- The canonical face factory gives exact vertex adjacency for two geometrically adjacent source occurrences. -/
theorem sources_join (first last : SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)
    (equal : mesh.surface.mesh.coordinate (first.project mesh.surface.mesh.triangulation.faces).finish =
      mesh.surface.mesh.coordinate (last.project mesh.surface.mesh.triangulation.faces).start) :
    (first.project mesh.surface.mesh.triangulation.faces).finish =
      (last.project mesh.surface.mesh.triangulation.faces).start := by
  let point := mesh.surface.mesh.coordinate (first.project mesh.surface.mesh.triangulation.faces).finish
  have member : point ∈ mesh.surface.mesh.vertices := List.getElem_mem _
  exact (mesh.source_finish_lookup factory first point member rfl).trans
    (mesh.source_start_lookup factory last point member equal.symm).symm

/-- Read one original horizontal-step source using the actual adjacent-interval occurrence in its cached axis. -/
def horizontalStep (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool)
    (interval : Interval) (member : interval ∈ (mesh.cells.get cellPosition).partition.x.intervals) :
    SourceEdge (mesh.triangles.map ModelTriangle.triangle).length :=
  let selected := (mesh.cells.get cellPosition).partition.x.intervalPosition interval member
  mesh.horizontalSource cellPosition selected.val.index row high

/-- Read one original vertical-step source using the actual adjacent-interval occurrence in its cached axis. -/
def verticalStep (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool)
    (interval : Interval) (member : interval ∈ (mesh.cells.get cellPosition).partition.y.intervals) :
    SourceEdge (mesh.triangles.map ModelTriangle.triangle).length :=
  let selected := (mesh.cells.get cellPosition).partition.y.intervalPosition interval member
  mesh.verticalSource cellPosition column selected.val.index high

/-- The retained horizontal-step source preserves its original interval endpoints and fixed coordinate. -/
theorem horizontalStep_coordinates (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool)
    (interval : Interval) (member : interval ∈ (mesh.cells.get cellPosition).partition.x.intervals) :
    let vertical := (mesh.cells.get cellPosition).partition.y.intervals[row.val]'row.isLt
    let height := if high then vertical.upper else vertical.lower
    let edge := (mesh.horizontalStep cellPosition row high interval member).project
      mesh.surface.mesh.triangulation.faces
    mesh.surface.mesh.coordinate edge.start = (⟨interval.lower, height⟩ : Canonical) ∧
      mesh.surface.mesh.coordinate edge.finish = (⟨interval.upper, height⟩ : Canonical) := by
  let partition := (mesh.cells.get cellPosition).partition
  let selected := partition.x.intervalPosition interval member
  have same : partition.x.intervals[selected.val.index.val]'selected.val.index.isLt = interval :=
    selected.val.entry_eq.symm.trans (partition.x.intervalOccurrence_entry_eq interval member selected.val)
  let height := if high then (partition.y.intervals[row.val]'row.isLt).upper
    else (partition.y.intervals[row.val]'row.isLt).lower
  have original := mesh.horizontalSource_coordinates cellPosition selected.val.index row high
  exact ⟨original.1.trans (congrArg (fun value : Interval => (⟨value.lower, height⟩ : Canonical)) same),
    original.2.trans (congrArg (fun value : Interval => (⟨value.upper, height⟩ : Canonical)) same)⟩

/-- The retained vertical-step source preserves its original interval endpoints and fixed coordinate. -/
theorem verticalStep_coordinates (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool)
    (interval : Interval) (member : interval ∈ (mesh.cells.get cellPosition).partition.y.intervals) :
    let horizontal := (mesh.cells.get cellPosition).partition.x.intervals[column.val]'column.isLt
    let width := if high then horizontal.upper else horizontal.lower
    let edge := (mesh.verticalStep cellPosition column high interval member).project
      mesh.surface.mesh.triangulation.faces
    mesh.surface.mesh.coordinate edge.start = (⟨width, interval.lower⟩ : Canonical) ∧
      mesh.surface.mesh.coordinate edge.finish = (⟨width, interval.upper⟩ : Canonical) := by
  let partition := (mesh.cells.get cellPosition).partition
  let selected := partition.y.intervalPosition interval member
  have same : partition.y.intervals[selected.val.index.val]'selected.val.index.isLt = interval :=
    selected.val.entry_eq.symm.trans (partition.y.intervalOccurrence_entry_eq interval member selected.val)
  let width := if high then (partition.x.intervals[column.val]'column.isLt).upper
    else (partition.x.intervals[column.val]'column.isLt).lower
  have original := mesh.verticalSource_coordinates cellPosition column selected.val.index high
  exact ⟨original.1.trans (congrArg (fun value : Interval => (⟨width, value.lower⟩ : Canonical)) same),
    original.2.trans (congrArg (fun value : Interval => (⟨width, value.upper⟩ : Canonical)) same)⟩

/-- The horizontal step's support comes from its actual retained rectangle-face occurrence. -/
theorem horizontalStep_supported (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool)
    (interval : Interval) (member : interval ∈ (mesh.cells.get cellPosition).partition.x.intervals) :
    let edge := (mesh.horizontalStep cellPosition row high interval member).project
      mesh.surface.mesh.triangulation.faces
    edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces ∨
      edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces :=
  let selected := (mesh.cells.get cellPosition).partition.x.intervalPosition interval member
  mesh.horizontalSource_supported cellPosition selected.val.index row high

/-- The vertical step's support comes from its actual retained rectangle-face occurrence. -/
theorem verticalStep_supported (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool)
    (interval : Interval) (member : interval ∈ (mesh.cells.get cellPosition).partition.y.intervals) :
    let edge := (mesh.verticalStep cellPosition column high interval member).project
      mesh.surface.mesh.triangulation.faces
    edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces ∨
      edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces :=
  let selected := (mesh.cells.get cellPosition).partition.y.intervalPosition interval member
  mesh.verticalSource_supported cellPosition column selected.val.index high

/-- Construct original source occurrences in the order of a given increasing horizontal axis walk. -/
def horizontalIncreasingSources (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    {start finish : Rational} → IncreasingWalk (mesh.cells.get cellPosition).partition.x.intervals start finish →
    List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)
  | _, _, .nil _ => []
  | _, _, .cons interval member rest =>
      mesh.horizontalStep cellPosition row high interval member ::
        horizontalIncreasingSources cellPosition row high rest

/-- Construct original source occurrences in the order of a given increasing vertical axis walk. -/
def verticalIncreasingSources (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool) :
    {start finish : Rational} → IncreasingWalk (mesh.cells.get cellPosition).partition.y.intervals start finish →
    List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)
  | _, _, .nil _ => []
  | _, _, .cons interval member rest =>
      mesh.verticalStep cellPosition column high interval member ::
        verticalIncreasingSources cellPosition column high rest

/-- Every occurrence of the constructed horizontal word is supported by its same original mesh face. -/
theorem horizontalIncreasingSources_supported (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    {start finish : Rational} →
    (walk : IncreasingWalk (mesh.cells.get cellPosition).partition.x.intervals start finish) →
    CutPath.Supported (Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
      ((mesh.horizontalIncreasingSources cellPosition row high walk).map
        (fun source => source.project mesh.surface.mesh.triangulation.faces))
  | _, _, .nil _ => fun _ absent => (List.not_mem_nil absent).elim
  | _, _, .cons interval member rest => by
      intro edge inWord
      rcases Membership.mem_cons.mp inWord with same | inTail
      · cases same
        exact mesh.horizontalStep_supported cellPosition row high interval member
      · exact horizontalIncreasingSources_supported cellPosition row high rest edge inTail

/-- Every occurrence of the constructed vertical word is supported by its same original mesh face. -/
theorem verticalIncreasingSources_supported (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool) :
    {start finish : Rational} →
    (walk : IncreasingWalk (mesh.cells.get cellPosition).partition.y.intervals start finish) →
    CutPath.Supported (Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
      ((mesh.verticalIncreasingSources cellPosition column high walk).map
        (fun source => source.project mesh.surface.mesh.triangulation.faces))
  | _, _, .nil _ => fun _ absent => (List.not_mem_nil absent).elim
  | _, _, .cons interval member rest => by
      intro edge inWord
      rcases Membership.mem_cons.mp inWord with same | inTail
      · cases same
        exact mesh.verticalStep_supported cellPosition column high interval member
      · exact verticalIncreasingSources_supported cellPosition column high rest edge inTail

include factory in
/-- The actual increasing horizontal source word has exact original canonical mesh endpoints.

The complete retained mesh factory, rather than coordinate agreement alone,
identifies consecutive source-corner indices. The empty walk keeps its
original endpoint role and contributes an empty inner word.
-/
theorem horizontalIncreasingSources_endpoints (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    {start finish : Rational} →
    (walk : IncreasingWalk (mesh.cells.get cellPosition).partition.x.intervals start finish) →
    let interval := (mesh.cells.get cellPosition).partition.y.intervals[row.val]'row.isLt
    let fixed := if high then interval.upper else interval.lower
    (firstMember : (⟨start, fixed⟩ : Canonical) ∈ mesh.surface.mesh.vertices) →
    (lastMember : (⟨finish, fixed⟩ : Canonical) ∈ mesh.surface.mesh.vertices) →
    PathEndpoints Stokes.OrientedEdge.start Stokes.OrientedEdge.finish
      ((mesh.horizontalIncreasingSources cellPosition row high walk).map
        (fun source => source.project mesh.surface.mesh.triangulation.faces))
      (CoordinateTriangulation.lookupVertex (⟨start, fixed⟩ : Canonical) mesh.surface.mesh.vertices firstMember).index
      (CoordinateTriangulation.lookupVertex (⟨finish, fixed⟩ : Canonical) mesh.surface.mesh.vertices lastMember).index
  | _, _, .nil _, firstMember, lastMember =>
      PathEndpoints.castFinish
        (CoordinateTriangulation.lookupVertex_same mesh.surface.mesh.vertices firstMember lastMember rfl)
        (PathEndpoints.nil _)
  | _, _, .cons interval member rest, firstMember, lastMember => by
      let selected := mesh.horizontalStep cellPosition row high interval member
      have coordinates := mesh.horizontalStep_coordinates cellPosition row high interval member
      let fixed := if high then
        ((mesh.cells.get cellPosition).partition.y.intervals[row.val]'row.isLt).upper
        else ((mesh.cells.get cellPosition).partition.y.intervals[row.val]'row.isLt).lower
      have middleMember : (⟨interval.upper, fixed⟩ : Canonical) ∈ mesh.surface.mesh.vertices :=
        Eq.mp (congrArg (fun point => point ∈ mesh.surface.mesh.vertices) coordinates.2) (List.getElem_mem _)
      have following := horizontalIncreasingSources_endpoints cellPosition row high rest middleMember lastMember
      have firstEq := mesh.source_start_lookup factory selected _ firstMember coordinates.1
      have lastEq := mesh.source_finish_lookup factory selected _ middleMember coordinates.2
      exact PathEndpoints.castStart firstEq
        (PathEndpoints.cons (edge := selected.project mesh.surface.mesh.triangulation.faces)
          (PathEndpoints.castStart lastEq.symm following))

include factory in
/-- The actual increasing vertical source word has exact original canonical mesh endpoints.

The complete retained mesh factory, rather than coordinate agreement alone,
identifies consecutive source-corner indices. The empty walk keeps its
original endpoint role and contributes an empty inner word.
-/
theorem verticalIncreasingSources_endpoints (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool) :
    {start finish : Rational} →
    (walk : IncreasingWalk (mesh.cells.get cellPosition).partition.y.intervals start finish) →
    let interval := (mesh.cells.get cellPosition).partition.x.intervals[column.val]'column.isLt
    let fixed := if high then interval.upper else interval.lower
    (firstMember : (⟨fixed, start⟩ : Canonical) ∈ mesh.surface.mesh.vertices) →
    (lastMember : (⟨fixed, finish⟩ : Canonical) ∈ mesh.surface.mesh.vertices) →
    PathEndpoints Stokes.OrientedEdge.start Stokes.OrientedEdge.finish
      ((mesh.verticalIncreasingSources cellPosition column high walk).map
        (fun source => source.project mesh.surface.mesh.triangulation.faces))
      (CoordinateTriangulation.lookupVertex (⟨fixed, start⟩ : Canonical) mesh.surface.mesh.vertices firstMember).index
      (CoordinateTriangulation.lookupVertex (⟨fixed, finish⟩ : Canonical) mesh.surface.mesh.vertices lastMember).index
  | _, _, .nil _, firstMember, lastMember =>
      PathEndpoints.castFinish
        (CoordinateTriangulation.lookupVertex_same mesh.surface.mesh.vertices firstMember lastMember rfl)
        (PathEndpoints.nil _)
  | _, _, .cons interval member rest, firstMember, lastMember => by
      let selected := mesh.verticalStep cellPosition column high interval member
      have coordinates := mesh.verticalStep_coordinates cellPosition column high interval member
      let fixed := if high then
        ((mesh.cells.get cellPosition).partition.x.intervals[column.val]'column.isLt).upper
        else ((mesh.cells.get cellPosition).partition.x.intervals[column.val]'column.isLt).lower
      have middleMember : (⟨fixed, interval.upper⟩ : Canonical) ∈ mesh.surface.mesh.vertices :=
        Eq.mp (congrArg (fun point => point ∈ mesh.surface.mesh.vertices) coordinates.2) (List.getElem_mem _)
      have following := verticalIncreasingSources_endpoints cellPosition column high rest middleMember lastMember
      have firstEq := mesh.source_start_lookup factory selected _ firstMember coordinates.1
      have lastEq := mesh.source_finish_lookup factory selected _ middleMember coordinates.2
      exact PathEndpoints.castStart firstEq
        (PathEndpoints.cons (edge := selected.project mesh.surface.mesh.triangulation.faces)
          (PathEndpoints.castStart lastEq.symm following))

/-- Reverse one retained source occurrence by exchanging its two ordered corners. -/
private def reverseSource (source : SourceEdge (mesh.triangles.map ModelTriangle.triangle).length) :
    SourceEdge (mesh.triangles.map ModelTriangle.triangle).length :=
  ⟨source.source, source.last, source.first⟩

/-- Reverse occurrence order and orientation while retaining every original source-face index. -/
private def reverseSources (sources : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)) :=
  sources.reverse.map (reverseSource mesh)

/-- Projecting the retained reversed sources is exactly the original edge-word reversal. -/
private theorem reverseSources_project
    (sources : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)) :
    (reverseSources mesh sources).map (fun source => source.project mesh.surface.mesh.triangulation.faces) =
      CutPath.reverse (sources.map (fun source => source.project mesh.surface.mesh.triangulation.faces)) := by
  have projected : ∀ values : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length),
      (values.map (reverseSource mesh)).map (fun source => source.project mesh.surface.mesh.triangulation.faces) =
        (values.map (fun source => source.project mesh.surface.mesh.triangulation.faces)).map
          Stokes.OrientedEdge.reverse := by
    intro values
    induction values with
    | nil => rfl
    | cons first rest previous => exact congrArg₂ List.cons rfl previous
  exact (projected sources.reverse).trans
    (congrArg (fun word => word.map Stokes.OrientedEdge.reverse)
      (Reverse.map_reverse (fun source => source.project mesh.surface.mesh.triangulation.faces) sources))

/-- Construct the horizontal source word in its actual axis-walk direction, retaining every source and reversal. -/
def horizontalSources (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool)
    {start finish : Rational}
    (walk : AxisWalks.Walk (mesh.cells.get cellPosition).partition.x.intervals start finish) :
    List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length) :=
  match walk with
  | .forward path => mesh.horizontalIncreasingSources cellPosition row high path
  | .backward path => reverseSources mesh (mesh.horizontalIncreasingSources cellPosition row high path)

/-- The actual oriented horizontal source word is supported by the original retained mesh triangles. -/
theorem horizontalSources_supported (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool)
    {start finish : Rational}
    (walk : AxisWalks.Walk (mesh.cells.get cellPosition).partition.x.intervals start finish) :
    CutPath.Supported (Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
      ((mesh.horizontalSources cellPosition row high walk).map
        (fun source => source.project mesh.surface.mesh.triangulation.faces)) := by
  cases walk with
  | forward path => exact mesh.horizontalIncreasingSources_supported cellPosition row high path
  | backward path =>
      exact Eq.mp (congrArg (fun word => CutPath.Supported
        (Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces) word)
        (reverseSources_project mesh (mesh.horizontalIncreasingSources cellPosition row high path)).symm)
        (CutPath.supported_reverse
          (mesh.horizontalIncreasingSources_supported cellPosition row high path))

/-- Each increasing horizontal source retains one common imaginary coordinate at its two original corners. -/
private theorem horizontalIncreasingSources_height (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    {start finish : Rational} →
    (walk : IncreasingWalk (mesh.cells.get cellPosition).partition.x.intervals start finish) →
    ∀ source ∈ mesh.horizontalIncreasingSources cellPosition row high walk,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).im =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).im
  | _, _, .nil _, _, member => (List.not_mem_nil member).elim
  | _, _, .cons interval included rest, source, member => by
      rcases Membership.mem_cons.mp member with equal | present
      · cases equal
        have coordinates := mesh.horizontalStep_coordinates cellPosition row high interval included
        exact (congrArg (fun point : Canonical => point.im) coordinates.1).trans
          (congrArg (fun point : Canonical => point.im) coordinates.2).symm
      · exact horizontalIncreasingSources_height cellPosition row high rest source present

/-- Every actual oriented horizontal source keeps its horizontal geometry, including reversed occurrences.

The proof uses each original step's coordinate readbacks. Reversal swaps
its two retained corners without changing the source face or selecting a
new edge from coincident coordinates.
-/
theorem horizontalSources_height (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool)
    {start finish : Rational}
    (walk : AxisWalks.Walk (mesh.cells.get cellPosition).partition.x.intervals start finish) :
    ∀ source ∈ mesh.horizontalSources cellPosition row high walk,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).im =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).im := by
  cases walk with
  | forward path => exact horizontalIncreasingSources_height mesh cellPosition row high path
  | backward path =>
      intro source member
      change source ∈ (mesh.horizontalIncreasingSources cellPosition row high path).reverse.map
        (reverseSource mesh) at member
      rcases Map.mem_map.mp member with ⟨original, present, equal⟩
      cases equal
      change (mesh.surface.mesh.coordinate (original.project mesh.surface.mesh.triangulation.faces).finish).im =
        (mesh.surface.mesh.coordinate (original.project mesh.surface.mesh.triangulation.faces).start).im
      exact (horizontalIncreasingSources_height mesh cellPosition row high path original
        ((Reverse.mem_reverse _).mp present)).symm

include factory in
/-- The original canonical mesh factory proves exact endpoints of the oriented horizontal word.

A reversed walk keeps all original source-face indices while reversing the
actual occurrence order and corner signs. A stationary request keeps its
walk occurrence and has a zero-step inner word.
-/
theorem horizontalSources_endpoints (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool)
    {start finish : Rational}
    (walk : AxisWalks.Walk (mesh.cells.get cellPosition).partition.x.intervals start finish) :
    let interval := (mesh.cells.get cellPosition).partition.y.intervals[row.val]'row.isLt
    let fixed := if high then interval.upper else interval.lower
    (firstMember : (⟨start, fixed⟩ : Canonical) ∈ mesh.surface.mesh.vertices) →
    (lastMember : (⟨finish, fixed⟩ : Canonical) ∈ mesh.surface.mesh.vertices) →
    PathEndpoints Stokes.OrientedEdge.start Stokes.OrientedEdge.finish
      ((mesh.horizontalSources cellPosition row high walk).map
        (fun source => source.project mesh.surface.mesh.triangulation.faces))
      (CoordinateTriangulation.lookupVertex (⟨start, fixed⟩ : Canonical) mesh.surface.mesh.vertices firstMember).index
      (CoordinateTriangulation.lookupVertex (⟨finish, fixed⟩ : Canonical)
        mesh.surface.mesh.vertices lastMember).index := by
  intro interval fixed firstMember lastMember
  cases walk with
  | forward path =>
      exact mesh.horizontalIncreasingSources_endpoints factory cellPosition row high path firstMember lastMember
  | backward path =>
      exact Eq.mp (congrArg (fun word => PathEndpoints
        Stokes.OrientedEdge.start Stokes.OrientedEdge.finish word
        (CoordinateTriangulation.lookupVertex _ mesh.surface.mesh.vertices firstMember).index
        (CoordinateTriangulation.lookupVertex _ mesh.surface.mesh.vertices lastMember).index)
        (reverseSources_project mesh (mesh.horizontalIncreasingSources cellPosition row high path)).symm)
        (CutPath.reverse_endpoints
          (mesh.horizontalIncreasingSources_endpoints factory cellPosition row high path lastMember firstMember))

/-- Construct the vertical source word in its actual axis-walk direction, retaining every source and reversal. -/
def verticalSources (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool)
    {start finish : Rational}
    (walk : AxisWalks.Walk (mesh.cells.get cellPosition).partition.y.intervals start finish) :
    List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length) :=
  match walk with
  | .forward path => mesh.verticalIncreasingSources cellPosition column high path
  | .backward path => reverseSources mesh (mesh.verticalIncreasingSources cellPosition column high path)

/-- The actual oriented vertical source word is supported by the original retained mesh triangles. -/
theorem verticalSources_supported (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool)
    {start finish : Rational}
    (walk : AxisWalks.Walk (mesh.cells.get cellPosition).partition.y.intervals start finish) :
    CutPath.Supported (Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces)
      ((mesh.verticalSources cellPosition column high walk).map
        (fun source => source.project mesh.surface.mesh.triangulation.faces)) := by
  cases walk with
  | forward path => exact mesh.verticalIncreasingSources_supported cellPosition column high path
  | backward path =>
      exact Eq.mp (congrArg (fun word => CutPath.Supported
        (Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.surface.mesh.triangulation.faces) word)
        (reverseSources_project mesh (mesh.verticalIncreasingSources cellPosition column high path)).symm)
        (CutPath.supported_reverse
          (mesh.verticalIncreasingSources_supported cellPosition column high path))

/-- Each increasing vertical source retains one common real coordinate at its two original corners. -/
private theorem verticalIncreasingSources_width (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool) :
    {start finish : Rational} →
    (walk : IncreasingWalk (mesh.cells.get cellPosition).partition.y.intervals start finish) →
    ∀ source ∈ mesh.verticalIncreasingSources cellPosition column high walk,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).re =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).re
  | _, _, .nil _, _, member => (List.not_mem_nil member).elim
  | _, _, .cons interval included rest, source, member => by
      rcases Membership.mem_cons.mp member with equal | present
      · cases equal
        have coordinates := mesh.verticalStep_coordinates cellPosition column high interval included
        exact (congrArg (fun point : Canonical => point.re) coordinates.1).trans
          (congrArg (fun point : Canonical => point.re) coordinates.2).symm
      · exact verticalIncreasingSources_width cellPosition column high rest source present

/-- Every actual oriented vertical source keeps its vertical geometry, including reversed occurrences.

The proof uses each original step's coordinate readbacks. Reversal swaps
its two retained corners without changing the source face or selecting a
new edge from coincident coordinates.
-/
theorem verticalSources_width (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool)
    {start finish : Rational}
    (walk : AxisWalks.Walk (mesh.cells.get cellPosition).partition.y.intervals start finish) :
    ∀ source ∈ mesh.verticalSources cellPosition column high walk,
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start).re =
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish).re := by
  cases walk with
  | forward path => exact verticalIncreasingSources_width mesh cellPosition column high path
  | backward path =>
      intro source member
      change source ∈ (mesh.verticalIncreasingSources cellPosition column high path).reverse.map
        (reverseSource mesh) at member
      rcases Map.mem_map.mp member with ⟨original, present, equal⟩
      cases equal
      change (mesh.surface.mesh.coordinate (original.project mesh.surface.mesh.triangulation.faces).finish).re =
        (mesh.surface.mesh.coordinate (original.project mesh.surface.mesh.triangulation.faces).start).re
      exact (verticalIncreasingSources_width mesh cellPosition column high path original
        ((Reverse.mem_reverse _).mp present)).symm

include factory in
/-- The original canonical mesh factory proves exact endpoints of the oriented vertical word.

A reversed walk keeps all original source-face indices while reversing the
actual occurrence order and corner signs. A stationary request keeps its
walk occurrence and has a zero-step inner word.
-/
theorem verticalSources_endpoints (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool)
    {start finish : Rational}
    (walk : AxisWalks.Walk (mesh.cells.get cellPosition).partition.y.intervals start finish) :
    let interval := (mesh.cells.get cellPosition).partition.x.intervals[column.val]'column.isLt
    let fixed := if high then interval.upper else interval.lower
    (firstMember : (⟨fixed, start⟩ : Canonical) ∈ mesh.surface.mesh.vertices) →
    (lastMember : (⟨fixed, finish⟩ : Canonical) ∈ mesh.surface.mesh.vertices) →
    PathEndpoints Stokes.OrientedEdge.start Stokes.OrientedEdge.finish
      ((mesh.verticalSources cellPosition column high walk).map
        (fun source => source.project mesh.surface.mesh.triangulation.faces))
      (CoordinateTriangulation.lookupVertex (⟨fixed, start⟩ : Canonical) mesh.surface.mesh.vertices firstMember).index
      (CoordinateTriangulation.lookupVertex (⟨fixed, finish⟩ : Canonical)
        mesh.surface.mesh.vertices lastMember).index := by
  intro interval fixed firstMember lastMember
  cases walk with
  | forward path =>
      exact mesh.verticalIncreasingSources_endpoints factory cellPosition column high path firstMember lastMember
  | backward path =>
      exact Eq.mp (congrArg (fun word => PathEndpoints
        Stokes.OrientedEdge.start Stokes.OrientedEdge.finish word
        (CoordinateTriangulation.lookupVertex _ mesh.surface.mesh.vertices firstMember).index
        (CoordinateTriangulation.lookupVertex _ mesh.surface.mesh.vertices lastMember).index)
        (reverseSources_project mesh (mesh.verticalIncreasingSources cellPosition column high path)).symm)
        (CutPath.reverse_endpoints
          (mesh.verticalIncreasingSources_endpoints factory cellPosition column high path lastMember firstMember))

/-- Embedding scalar endpoint pairs commutes with their exact ordered reversal. -/
private theorem embed_reverse (values : List (Rational × Rational)) (embed : Rational → Canonical) :
    (values.reverse.map Prod.swap).map (fun pair => (embed pair.1, embed pair.2)) =
      (values.map (fun pair => (embed pair.1, embed pair.2))).reverse.map Prod.swap := by
  have mapped : ∀ values : List (Rational × Rational),
      (values.map Prod.swap).map (fun pair => (embed pair.1, embed pair.2)) =
        (values.map (fun pair => (embed pair.1, embed pair.2))).map Prod.swap := by
    intro values
    induction values with
    | nil => rfl
    | cons head tail previous => exact congrArg₂ List.cons rfl previous
  exact (mapped values.reverse).trans
    (congrArg (fun pairs => pairs.map Prod.swap)
      (Reverse.map_reverse (fun pair => (embed pair.1, embed pair.2)) values))

/-- The original source reversal exchanges the same coordinate endpoints and retains occurrence order. -/
private theorem reverseSources_coordinates
    (sources : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length)) :
    (reverseSources mesh sources).map (fun source =>
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
        mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish)) =
    (sources.map (fun source =>
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
        mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish))).reverse.map
      Prod.swap := by
  have mapped : ∀ values : List (SourceEdge (mesh.triangles.map ModelTriangle.triangle).length),
      (values.map (reverseSource mesh)).map (fun source =>
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
          mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish)) =
      (values.map (fun source =>
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
          mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish))).map
        Prod.swap := by
    intro values
    induction values with
    | nil => rfl
    | cons head tail previous => exact congrArg₂ List.cons rfl previous
  exact (mapped sources.reverse).trans
    (congrArg (fun pairs => pairs.map Prod.swap)
      (Reverse.map_reverse (fun source =>
        (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
          mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish)) sources))

/-- The actual increasing horizontal sources realize every retained interval step, in its exact supplied order. -/
private theorem horizontalIncreasingSources_coordinates (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool) :
    {first last : Rational} →
    (walk : IncreasingWalk (mesh.cells.get cellPosition).partition.x.intervals first last) →
    let interval := (mesh.cells.get cellPosition).partition.y.intervals[row.val]'row.isLt
    let fixed := if high then interval.upper else interval.lower
    (mesh.horizontalIncreasingSources cellPosition row high walk).map (fun source =>
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
        mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish)) =
      walk.steps.map (fun pair => ((⟨pair.1, fixed⟩ : Canonical), (⟨pair.2, fixed⟩ : Canonical)))
  | _, _, .nil _ => rfl
  | _, _, .cons interval member tail => by
      have original := mesh.horizontalStep_coordinates cellPosition row high interval member
      exact congrArg₂ List.cons (congrArg₂ Prod.mk original.1 original.2)
        (horizontalIncreasingSources_coordinates cellPosition row high tail)

/-- The actual increasing vertical sources realize every retained interval step, in its exact supplied order. -/
private theorem verticalIncreasingSources_coordinates (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool) :
    {first last : Rational} →
    (walk : IncreasingWalk (mesh.cells.get cellPosition).partition.y.intervals first last) →
    let interval := (mesh.cells.get cellPosition).partition.x.intervals[column.val]'column.isLt
    let fixed := if high then interval.upper else interval.lower
    (mesh.verticalIncreasingSources cellPosition column high walk).map (fun source =>
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
        mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish)) =
      walk.steps.map (fun pair => ((⟨fixed, pair.1⟩ : Canonical), (⟨fixed, pair.2⟩ : Canonical)))
  | _, _, .nil _ => rfl
  | _, _, .cons interval member tail => by
      have original := mesh.verticalStep_coordinates cellPosition column high interval member
      exact congrArg₂ List.cons (congrArg₂ Prod.mk original.1 original.2)
        (verticalIncreasingSources_coordinates cellPosition column high tail)

/-- The same oriented horizontal source word is exactly the retained ordered axis-step embedding.

Both source-face labels and original corner orientation remain inputs.
Reversal keeps every occurrence and exchanges its endpoints. This is a
geometric subdivision readback; it identifies no root or primitive owner.
-/
theorem horizontalSources_coordinates (cellPosition : Fin selection.length)
    (row : Fin (mesh.cells.get cellPosition).partition.y.intervals.length) (high : Bool)
    {first last : Rational}
    (walk : AxisWalks.Walk (mesh.cells.get cellPosition).partition.x.intervals first last) :
    let interval := (mesh.cells.get cellPosition).partition.y.intervals[row.val]'row.isLt
    let fixed := if high then interval.upper else interval.lower
    (mesh.horizontalSources cellPosition row high walk).map (fun source =>
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
        mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish)) =
      walk.steps.map (fun pair => ((⟨pair.1, fixed⟩ : Canonical), (⟨pair.2, fixed⟩ : Canonical))) := by
  intro interval fixed
  cases walk with
  | forward path => exact horizontalIncreasingSources_coordinates mesh cellPosition row high path
  | backward path =>
      exact (reverseSources_coordinates mesh (mesh.horizontalIncreasingSources cellPosition row high path)).trans
        ((congrArg (fun pairs => pairs.reverse.map Prod.swap)
          (horizontalIncreasingSources_coordinates mesh cellPosition row high path)).trans
          (embed_reverse path.steps (fun value => (⟨value, fixed⟩ : Canonical))).symm)

/-- The same oriented vertical source word is exactly the retained ordered axis-step embedding.

The unchanged interval owners determine direction and coordinate bounds.
No supported self-edge is inserted when the requested interval is empty.
-/
theorem verticalSources_coordinates (cellPosition : Fin selection.length)
    (column : Fin (mesh.cells.get cellPosition).partition.x.intervals.length) (high : Bool)
    {first last : Rational}
    (walk : AxisWalks.Walk (mesh.cells.get cellPosition).partition.y.intervals first last) :
    let interval := (mesh.cells.get cellPosition).partition.x.intervals[column.val]'column.isLt
    let fixed := if high then interval.upper else interval.lower
    (mesh.verticalSources cellPosition column high walk).map (fun source =>
      (mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).start,
        mesh.surface.mesh.coordinate (source.project mesh.surface.mesh.triangulation.faces).finish)) =
      walk.steps.map (fun pair => ((⟨fixed, pair.1⟩ : Canonical), (⟨fixed, pair.2⟩ : Canonical))) := by
  intro interval fixed
  cases walk with
  | forward path => exact verticalIncreasingSources_coordinates mesh cellPosition column high path
  | backward path =>
      exact (reverseSources_coordinates mesh (mesh.verticalIncreasingSources cellPosition column high path)).trans
        ((congrArg (fun pairs => pairs.reverse.map Prod.swap)
          (verticalIncreasingSources_coordinates mesh cellPosition column high path)).trans
          (embed_reverse path.steps (fun value => (⟨fixed, value⟩ : Canonical))).symm)

end Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.RectangularInverseModels.CommonMesh

end
