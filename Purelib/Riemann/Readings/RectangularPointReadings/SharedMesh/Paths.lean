module

public import Purelib.Riemann.Readings.RectangularPointReadings.SharedMesh
public import Purelib.Geometry.Rectangle.Partition.RectangularCommonMesh.Paths
public import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions.Walks
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Readings.RectangularExteriorBoundary
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Topology.Chain.PathBoundary
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Tactic.Ring
import Purelib.Data.List.Search
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Grid.Offsets

/-! # The two original child legs on the same retained shared mesh

The original piece selects its actual retained coarse-cell position. Its
two axis walks and perpendicular endpoint choices use that cell's cached
cut partitions. Each leg retains its own source word, including an empty
inner word at a stationary request. The endpoint proofs name the original
stored corner/start/finish lookups; no physical root owner is replaced.
-/

public section

namespace Purelib.Riemann.Readings.RectangularPointReadings.Chord.MeshReadings.Paths

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List
open Purelib.Geometry.Rectangle (AxisPartition CutPartition)
open Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions (Interval)
open Purelib.Riemann.Integration.PreparedParentSplitting.Geometry (allCells_mem)
open Purelib.Riemann.Integration.RectangularPrimitiveModels (Primitives)
open Purelib.Riemann.Integration.RectangularPrimitiveGluing (PrimitiveAnchors)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry Bank)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentSplit)
open Purelib.Riemann.Paths
open Purelib.LinearAlgebra.Grid (Offsets)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Topology.Mesh
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceEdge)
open Purelib.Topology.Surface.Cut.JumpPaths
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing
open Purelib.Riemann.Integration.RectangularOwnedTriangulation (ModelTriangle)

universe u

variable {columns rows : Nat} {geometry : Geometry columns rows}
    {polynomial numerator : Polynomial} {models : Bank polynomial geometry}
    {primitives : Primitives models numerator} {anchors : PrimitiveAnchors primitives}
    {offsets : Offsets anchors.edges} {cuts : GridCuts geometry} {first last : Canonical}
    (split : SegmentSplit cuts first last) (cached : MeshReadings split anchors offsets)
    (position : Fin split.pieces.length)

/-- The original accepted coarse-cell occurrence and complete first-scan equation for the literal piece owner. -/
abbrev CellChoice :=
  {selected : Search.Occurrence
      (fun pair : Fin (columns + 1) × Fin (rows + 1) =>
        pair = ((split.pieces[position.val]'position.isLt).column,
          (split.pieces[position.val]'position.isLt).row))
      (RectangularExteriorBoundary.Geometry.allCells geometry) //
    Search.firstOccurrence
      (fun pair : Fin (columns + 1) × Fin (rows + 1) =>
        pair = ((split.pieces[position.val]'position.isLt).column,
          (split.pieces[position.val]'position.isLt).row))
      (fun _ => inferInstance) (RectangularExteriorBoundary.Geometry.allCells geometry) = some selected}

/-- Select the piece's actual original coarse-cell occurrence once in the same retained selection. -/
def chooseCell : CellChoice split position :=
  Search.firstAccepted _ (fun _ => inferInstance) _
    ⟨_, allCells_mem geometry _ _, rfl⟩

variable (choice : CellChoice split position)

/-- The selected original cell has exactly the same original column and row as the literal source piece. -/
theorem choice_eq :
    (RectangularExteriorBoundary.Geometry.allCells geometry)[choice.val.index.val]'choice.val.index.isLt =
      ((split.pieces[position.val]'position.isLt).column, (split.pieces[position.val]'position.isLt).row) :=
  choice.val.entry_eq.symm.trans choice.val.accepted

/-- Read the same original cut partition at the retained coarse-cell occurrence. -/
@[expose] def partition : CutPartition
    (geometry.box
      ((RectangularExteriorBoundary.Geometry.allCells geometry)[choice.val.index.val]'choice.val.index.isLt).1
      ((RectangularExteriorBoundary.Geometry.allCells geometry)[choice.val.index.val]'choice.val.index.isLt).2)
    (slots split) :=
  ((mesh split cached).cells.get choice.val.index).partition

/-- A literal requested slot lies in that actual retained partition's parent box. -/
private theorem inside (slot : Fin 3) :
    (geometry.box
      ((RectangularExteriorBoundary.Geometry.allCells geometry)[choice.val.index.val]'choice.val.index.isLt).1
      ((RectangularExteriorBoundary.Geometry.allCells geometry)[choice.val.index.val]'choice.val.index.isLt).2).Contains
      (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
        (split.pieces[position.val]'position.isLt).lastPoint slot) :=
  Eq.mp (congrArg (fun pair : Fin (columns + 1) × Fin (rows + 1) =>
    (geometry.box pair.1 pair.2).Contains
      (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
        (split.pieces[position.val]'position.isLt).lastPoint slot)) (choice_eq split position choice).symm)
    (slot_inside split position slot)

/-- Each actual triangle slot is an original cut coordinate on the retained horizontal axis. -/
private theorem x_member (slot : Fin 3) :
    (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
      (split.pieces[position.val]'position.isLt).lastPoint slot).re ∈
      (partition split cached position choice).x.coordinates :=
  (partition split cached position choice).x.cut_mem
    (Map.mem_map.mpr ⟨_, slots_mem split position slot, rfl⟩)
    ⟨(inside split position choice slot).1, (inside split position choice slot).2.1⟩

/-- Each actual triangle slot is an original cut coordinate on the retained vertical axis. -/
private theorem y_member (slot : Fin 3) :
    (ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
      (split.pieces[position.val]'position.isLt).lastPoint slot).im ∈
      (partition split cached position choice).y.coordinates :=
  (partition split cached position choice).y.cut_mem
    (Map.mem_map.mpr ⟨_, slots_mem split position slot, rfl⟩) (inside split position choice slot).2.2

/-- Both actual piece endpoint coordinates belong to the same retained cut partitions. -/
theorem endpoint_members :
    (split.pieces[position.val]'position.isLt).firstPoint.re ∈ (partition split cached position choice).x.coordinates ∧
      (split.pieces[position.val]'position.isLt).firstPoint.im ∈
        (partition split cached position choice).y.coordinates ∧
      (split.pieces[position.val]'position.isLt).lastPoint.re ∈ (partition split cached position choice).x.coordinates ∧
      (split.pieces[position.val]'position.isLt).lastPoint.im ∈
        (partition split cached position choice).y.coordinates := by
  have coordinates := ClearBoxPaths.Chord.coordinate_values
    (split.pieces[position.val]'position.isLt).firstPoint (split.pieces[position.val]'position.isLt).lastPoint
  exact ⟨Eq.mp (congrArg (fun point : Canonical => point.re ∈
      (partition split cached position choice).x.coordinates) coordinates.2.1)
      (x_member split cached position choice 1),
    Eq.mp (congrArg (fun point : Canonical => point.im ∈
      (partition split cached position choice).y.coordinates) coordinates.2.1)
      (y_member split cached position choice 1),
    Eq.mp (congrArg (fun point : Canonical => point.re ∈
      (partition split cached position choice).x.coordinates) coordinates.2.2)
      (x_member split cached position choice 2),
    Eq.mp (congrArg (fun point : Canonical => point.im ∈
      (partition split cached position choice).y.coordinates) coordinates.2.2)
      (y_member split cached position choice 2)⟩

/-- Retain the original adjacent-interval selection and complete first-scan equation for one perpendicular endpoint. -/
abbrev AxisPosition {lower upper : Rational} {cuts : List Rational} (axis : AxisPartition lower upper cuts)
    (interval : Interval) :=
  {selected : Search.Occurrence (fun entry : Interval => entry.lower = interval.lower) axis.intervals //
    Search.firstOccurrence (fun entry : Interval => entry.lower = interval.lower) (fun _ => inferInstance)
      axis.intervals = some selected}

/-- The actual cached adjacent interval at a retained position is the same complete original endpoint interval. -/
private theorem interval_eq {lower upper : Rational} {cuts : List Rational} (axis : AxisPartition lower upper cuts)
    (interval : Interval) (member : interval ∈ axis.intervals) (selected : AxisPosition axis interval) :
    axis.intervals[selected.val.index.val]'selected.val.index.isLt = interval :=
  selected.val.entry_eq.symm.trans (axis.intervalOccurrence_entry_eq interval member selected.val)

variable {choice}

/-- The original stored lookup has exactly its canonical first-occurrence index, by its complete original factory. -/
private theorem stored_index (slot : Fin 3) (point : Canonical)
    (member : point ∈ (mesh split cached).surface.mesh.vertices)
    (equal : point = ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
      (split.pieces[position.val]'position.isLt).lastPoint slot) :
    (CoordinateTriangulation.lookupVertex point (mesh split cached).surface.mesh.vertices member).index =
      (((lookups split cached).get position).get slot).index := by
  let kept := ((lookups split cached).get position).get slot
  have keptMember : ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
      (split.pieces[position.val]'position.isLt).lastPoint slot ∈ (mesh split cached).surface.mesh.vertices :=
    Eq.mp (congrArg (fun point => point ∈ (mesh split cached).surface.mesh.vertices) kept.coordinate_eq)
      (List.getElem_mem _)
  have actual := (lookup_eq split cached position slot).trans
    (Chord.lookup_first split (mesh split cached) position slot keptMember)
  exact (CoordinateTriangulation.lookupVertex_same (mesh split cached).surface.mesh.vertices
    member keptMember equal).trans (congrArg (fun value => value.index) actual).symm

/-- Both original outer leg slots retain their actual axis preparations, source words and exact stored endpoint names.

The callback receives one original cell choice, each perpendicular Endpoint
and interval lookup, both actual walks, and both source lists with their
literal factories. Support and endpoints refer to those same retained
lists. Stationary legs retain their own slot with an empty inner word.
-/
@[expose] def Consumer (Result : Type u) :=
  (choice : CellChoice split position) →
  (height : {value : AxisPartition.Endpoint (partition split cached position choice).y
      (split.pieces[position.val]'position.isLt).firstPoint.im //
    value = (partition split cached position choice).y.endpoint
      (split.pieces[position.val]'position.isLt).firstPoint.im
      (endpoint_members split cached position choice).2.1}) →
  (row : AxisPosition (partition split cached position choice).y height.val.interval) →
  (width : {value : AxisPartition.Endpoint (partition split cached position choice).x
      (split.pieces[position.val]'position.isLt).lastPoint.re //
    value = (partition split cached position choice).x.endpoint
      (split.pieces[position.val]'position.isLt).lastPoint.re
      (endpoint_members split cached position choice).2.2.1}) →
  (column : AxisPosition (partition split cached position choice).x width.val.interval) →
  (horizontal : {value : AxisWalks.Walk (partition split cached position choice).x.intervals
      (split.pieces[position.val]'position.isLt).firstPoint.re
      (split.pieces[position.val]'position.isLt).lastPoint.re //
    value = (partition split cached position choice).x.between
      (split.pieces[position.val]'position.isLt).firstPoint.re (split.pieces[position.val]'position.isLt).lastPoint.re
      (endpoint_members split cached position choice).1 (endpoint_members split cached position choice).2.2.1}) →
  (vertical : {value : AxisWalks.Walk (partition split cached position choice).y.intervals
      (split.pieces[position.val]'position.isLt).firstPoint.im
      (split.pieces[position.val]'position.isLt).lastPoint.im //
    value = (partition split cached position choice).y.between
      (split.pieces[position.val]'position.isLt).firstPoint.im (split.pieces[position.val]'position.isLt).lastPoint.im
      (endpoint_members split cached position choice).2.1 (endpoint_members split cached position choice).2.2.2}) →
  (horizontalSources : {value : List (SourceEdge
      ((mesh split cached).triangles.map ModelTriangle.triangle).length) //
    value = (mesh split cached).horizontalSources choice.val.index row.val.index height.val.high horizontal.val}) →
  (verticalSources : {value : List (SourceEdge
      ((mesh split cached).triangles.map ModelTriangle.triangle).length) //
    value = (mesh split cached).verticalSources choice.val.index column.val.index width.val.high vertical.val}) →
  CutPath.Supported (Topology.Polygon.Stokes.triangleEdgeOccurrences
      (mesh split cached).surface.mesh.triangulation.faces)
    (horizontalSources.val.map (fun source => source.project (mesh split cached).surface.mesh.triangulation.faces)) →
  PathEndpoints OrientedEdge.start OrientedEdge.finish
    (horizontalSources.val.map (fun source => source.project (mesh split cached).surface.mesh.triangulation.faces))
    (((lookups split cached).get position).get 1).index (((lookups split cached).get position).get 0).index →
  CutPath.Supported (Topology.Polygon.Stokes.triangleEdgeOccurrences
      (mesh split cached).surface.mesh.triangulation.faces)
    (verticalSources.val.map (fun source => source.project (mesh split cached).surface.mesh.triangulation.faces)) →
  PathEndpoints OrientedEdge.start OrientedEdge.finish
    (verticalSources.val.map (fun source => source.project (mesh split cached).surface.mesh.triangulation.faces))
    (((lookups split cached).get position).get 0).index (((lookups split cached).get position).get 2).index →
  (SewingRetraction.wordValue
      (fun edge : OrientedEdge (mesh split cached).surface.mesh.vertices.length =>
        (shared split cached).values edge.finish - (shared split cached).values edge.start)
      (horizontalSources.val.map (fun source => source.project (mesh split cached).surface.mesh.triangulation.faces)) +
    SewingRetraction.wordValue
      (fun edge : OrientedEdge (mesh split cached).surface.mesh.vertices.length =>
        (shared split cached).values edge.finish - (shared split cached).values edge.start)
      (verticalSources.val.map (fun source => source.project (mesh split cached).surface.mesh.triangulation.faces)) =
    SewingRetraction.wordValue
      (fun edge : OrientedEdge (mesh split cached).surface.mesh.vertices.length =>
        (shared split cached).values edge.finish - (shared split cached).values edge.start)
      (word split cached position)) → Result

/-- The same selected cached axis interval retains its original perpendicular endpoint coordinate. -/
theorem endpoint_coordinate {lower upper : Rational} {cuts : List Rational}
    (axis : AxisPartition lower upper cuts) {point : Rational}
    (endpoint : AxisPartition.Endpoint axis point) (selected : AxisPosition axis endpoint.interval) :
    (if endpoint.high then (axis.intervals[selected.val.index.val]'selected.val.index.isLt).upper
      else (axis.intervals[selected.val.index.val]'selected.val.index.isLt).lower) = point :=
  (congrArg (fun interval : Interval => if endpoint.high then interval.upper else interval.lower)
    (interval_eq axis endpoint.interval endpoint.member selected)).trans endpoint.endpoint_eq

/-- A coordinate-equal numerical endpoint has membership from its actual retained original lookup. -/
private theorem member_of_stored (slot : Fin 3) (point : Canonical)
    (equal : point = ClearBoxPaths.Chord.coordinate (split.pieces[position.val]'position.isLt).firstPoint
      (split.pieces[position.val]'position.isLt).lastPoint slot) :
    point ∈ (mesh split cached).surface.mesh.vertices :=
  let kept := ((lookups split cached).get position).get slot
  Eq.mp (congrArg (fun point => point ∈ (mesh split cached).surface.mesh.vertices)
    (kept.coordinate_eq.trans equal.symm)) (List.getElem_mem _)

/-- Actual indexed endpoint differences telescope on the same retained finite value bank. -/
private theorem value_telescope {size : Nat} (values : Fin size → Canonical)
    {edges : List (OrientedEdge size)} {start finish : Fin size}
    (path : PathEndpoints OrientedEdge.start OrientedEdge.finish edges start finish) :
    SewingRetraction.wordValue (fun edge : OrientedEdge size => values edge.finish - values edge.start) edges =
      values finish - values start := by
  induction path with
  | nil index => exact (Basic.sub_self (values index)).symm
  | @cons edge rest finish tail previous =>
      change (values edge.finish - values edge.start) +
        SewingRetraction.wordValue (fun edge : OrientedEdge size => values edge.finish - values edge.start) rest = _
      rewrite [previous]
      have cancel (first middle last : Canonical) : middle - first + (last - middle) = last - first := by
        ring1
      exact cancel _ _ _

/-- Construct both literal child-leg refinements from the same retained cell partition and original stored lookups.

All new finite geometric data are bound once before the callback. The
complete original source and primitive owners remain the existing inputs.
Endpoint equality uses the real mesh and lookup factories; it does not
infer a physical root relation from coordinate agreement.
-/
def withPaths {Result : Type u} (consume : Consumer split cached position Result) : Result := by
  let piece := split.pieces[position.val]'position.isLt
  let choice := chooseCell split position
  let part := partition split cached position choice
  have members := endpoint_members split cached position choice
  let height := part.y.endpoint piece.firstPoint.im members.2.1
  let row := part.y.intervalPosition height.interval height.member
  let width := part.x.endpoint piece.lastPoint.re members.2.2.1
  let column := part.x.intervalPosition width.interval width.member
  let horizontal := part.x.between piece.firstPoint.re piece.lastPoint.re members.1 members.2.2.1
  let vertical := part.y.between piece.firstPoint.im piece.lastPoint.im members.2.1 members.2.2.2
  let horizontalSources := (mesh split cached).horizontalSources
    choice.val.index row.val.index height.high horizontal
  let verticalSources := (mesh split cached).verticalSources
    choice.val.index column.val.index width.high vertical
  let horizontalFixed := if height.high then (part.y.intervals[row.val.index.val]'row.val.index.isLt).upper
    else (part.y.intervals[row.val.index.val]'row.val.index.isLt).lower
  let verticalFixed := if width.high then (part.x.intervals[column.val.index.val]'column.val.index.isLt).upper
    else (part.x.intervals[column.val.index.val]'column.val.index.isLt).lower
  have horizontalEq : horizontalFixed = piece.firstPoint.im := endpoint_coordinate part.y height row
  have verticalEq : verticalFixed = piece.lastPoint.re := endpoint_coordinate part.x width column
  have coordinates := ClearBoxPaths.Chord.coordinate_values piece.firstPoint piece.lastPoint
  have horizontalFirst : (⟨piece.firstPoint.re, horizontalFixed⟩ : Canonical) =
      ClearBoxPaths.Chord.coordinate piece.firstPoint piece.lastPoint 1 :=
    (show (⟨piece.firstPoint.re, horizontalFixed⟩ : Canonical) = piece.firstPoint from
      Basic.ext rfl horizontalEq).trans coordinates.2.1.symm
  have horizontalLast : (⟨piece.lastPoint.re, horizontalFixed⟩ : Canonical) =
      ClearBoxPaths.Chord.coordinate piece.firstPoint piece.lastPoint 0 :=
    (show (⟨piece.lastPoint.re, horizontalFixed⟩ : Canonical) = (⟨piece.lastPoint.re, piece.firstPoint.im⟩ : Canonical)
      from Basic.ext rfl horizontalEq).trans
        ((ClearBoxPaths.Chord.corner_eq piece.firstPoint piece.lastPoint).symm.trans coordinates.1.symm)
  have verticalFirst : (⟨verticalFixed, piece.firstPoint.im⟩ : Canonical) =
      ClearBoxPaths.Chord.coordinate piece.firstPoint piece.lastPoint 0 :=
    (show (⟨verticalFixed, piece.firstPoint.im⟩ : Canonical) = (⟨piece.lastPoint.re, piece.firstPoint.im⟩ : Canonical)
      from Basic.ext verticalEq rfl).trans
        ((ClearBoxPaths.Chord.corner_eq piece.firstPoint piece.lastPoint).symm.trans coordinates.1.symm)
  have verticalLast : (⟨verticalFixed, piece.lastPoint.im⟩ : Canonical) =
      ClearBoxPaths.Chord.coordinate piece.firstPoint piece.lastPoint 2 :=
    (show (⟨verticalFixed, piece.lastPoint.im⟩ : Canonical) = piece.lastPoint from
      Basic.ext verticalEq rfl).trans coordinates.2.2.symm
  have horizontalFirstMember := member_of_stored split cached position 1 _ horizontalFirst
  have horizontalLastMember := member_of_stored split cached position 0 _ horizontalLast
  have verticalFirstMember := member_of_stored split cached position 0 _ verticalFirst
  have verticalLastMember := member_of_stored split cached position 2 _ verticalLast
  have horizontalPath := (mesh split cached).horizontalSources_endpoints (mesh_eq split cached)
    choice.val.index row.val.index height.high horizontal horizontalFirstMember horizontalLastMember
  have verticalPath := (mesh split cached).verticalSources_endpoints (mesh_eq split cached)
    choice.val.index column.val.index width.high vertical verticalFirstMember verticalLastMember
  have actualHorizontal := PathEndpoints.castFinish
    (stored_index split cached position 0 _ horizontalLastMember horizontalLast)
    (PathEndpoints.castStart (stored_index split cached position 1 _ horizontalFirstMember horizontalFirst)
      horizontalPath)
  have actualVertical := PathEndpoints.castFinish
    (stored_index split cached position 2 _ verticalLastMember verticalLast)
    (PathEndpoints.castStart (stored_index split cached position 0 _ verticalFirstMember verticalFirst)
      verticalPath)
  have valuesEq :
      SewingRetraction.wordValue
          (fun edge : OrientedEdge (mesh split cached).surface.mesh.vertices.length =>
            (shared split cached).values edge.finish - (shared split cached).values edge.start)
          (horizontalSources.map (fun source => source.project (mesh split cached).surface.mesh.triangulation.faces)) +
        SewingRetraction.wordValue
          (fun edge : OrientedEdge (mesh split cached).surface.mesh.vertices.length =>
            (shared split cached).values edge.finish - (shared split cached).values edge.start)
          (verticalSources.map (fun source => source.project (mesh split cached).surface.mesh.triangulation.faces)) =
        SewingRetraction.wordValue
          (fun edge : OrientedEdge (mesh split cached).surface.mesh.vertices.length =>
            (shared split cached).values edge.finish - (shared split cached).values edge.start)
          (word split cached position) := by
    have original := congrArg₂ (fun first last : Canonical => first + last)
      (value_telescope (shared split cached).values actualHorizontal)
      (value_telescope (shared split cached).values actualVertical)
    apply original.trans
    rewrite [word_eq split cached position]
    change _ = _ + (_ + 0)
    rewrite [Basic.add_zero]
    rfl
  exact consume choice ⟨height, rfl⟩ row ⟨width, rfl⟩ column ⟨horizontal, rfl⟩ ⟨vertical, rfl⟩
    ⟨horizontalSources, rfl⟩ ⟨verticalSources, rfl⟩
    ((mesh split cached).horizontalSources_supported choice.val.index row.val.index height.high horizontal)
    actualHorizontal
    ((mesh split cached).verticalSources_supported choice.val.index column.val.index width.high vertical)
    actualVertical valuesEq

end Purelib.Riemann.Readings.RectangularPointReadings.Chord.MeshReadings.Paths

end
