module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointCorners.Corners
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.VertexPoints
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Connections
public import Purelib.Geometry.Triangles.AffineCut
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

/-! # Actual preparation of either cut on any retained quad source side

Each source face/corner occurrence reads its original signed Entry.
Strict cuts perform new preparation once; unit cuts reuse a supplied
literal endpoint cache or return its exact missing-preparation request.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Geometry.Rational (Box)
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

/-- Read the Entry at the literal original start of either rotated cut-side occurrence. -/
def cutStart (side : Fin 2) :
    {value : Entry models (vertices.coordinate (apex.edge (lifted.cell.quad.faces position) side).start)
      (vertices.owner retained.localFrames (apex.edge (lifted.cell.quad.faces position) side).start) //
      value.sheet = classified.entry.sheet} :=
  Eq.mp (congrArg (fun index =>
    {value : Entry models (vertices.coordinate index) (vertices.owner retained.localFrames index) //
      value.sheet = classified.entry.sheet})
    (congrArg OrientedEdge.start (apex.source_project lifted.cell.quad.faces position side)))
    (lifted.sourceEntry (apex.source position side).source (apex.source position side).first)

/-- Read the Entry at the literal original finish of either rotated cut-side occurrence. -/
def cutFinish (side : Fin 2) :
    {value : Entry models (vertices.coordinate (apex.edge (lifted.cell.quad.faces position) side).finish)
      (vertices.owner retained.localFrames (apex.edge (lifted.cell.quad.faces position) side).finish) //
      value.sheet = classified.entry.sheet} :=
  Eq.mp (congrArg (fun index =>
    {value : Entry models (vertices.coordinate index) (vertices.owner retained.localFrames index) //
      value.sheet = classified.entry.sheet})
    (congrArg OrientedEdge.finish (apex.source_project lifted.cell.quad.faces position side)))
    (lifted.sourceEntry (apex.source position side).source (apex.source position side).last)

section

include lifted factory

/-- Either actual cut lies in the SAME old clear face by its indexed side endpoints and stored fraction. -/
theorem cut_inside (side : Fin 2) : face.cell.box.Contains (crossing.point side) := by
  have endpoints := crossing.edge_coordinates vertices.coordinate (lifted.cell.quad.faces position) factory side
  have first := Eq.mp (congrArg face.cell.box.Contains (congrArg Prod.fst endpoints))
    (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start).inside
  have last := Eq.mp (congrArg face.cell.box.Contains (congrArg Prod.snd endpoints))
    (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish).inside
  exact Eq.mpr (congrArg face.cell.box.Contains (crossing.point_eq side))
    (Box.contains_line first last
      ⟨(crossing.time_bounds side).1.le, (crossing.time_bounds side).2⟩)

/-- A unit cut is its SAME literal signed endpoint coordinate, including boundary and reversed source occurrences. -/
theorem cut_endpoint (side : Fin 2) (atEnd : crossing.time side = 1) :
    crossing.point side = vertices.coordinate (apex.edge (lifted.cell.quad.faces position) side).finish :=
  (crossing.endpoint side atEnd).trans
    (congrArg Prod.snd (crossing.edge_coordinates vertices.coordinate
      (lifted.cell.quad.faces position) factory side)).symm

end

/-- Retain the old quad/cut, one new Point and both actual source-to-Point connections.

The two connections retain their complete newly acquired OwnerJoins.
Both source Entries come from the SAME original corner product. The
actual side may be boundary, diagonal, reverse or stationary metadata;
no equality of independent Owners is inferred from that classification.
-/
abbrev PreparedSide (side : Fin 2) (count : Nat) :=
  {value : classified.CellLift located vertices × AffineCut.CrossingCache lineFirst lineLast triangle apex //
    value = (lifted, crossing)} ×
  (Σ frame : {value : OwnerFrame (curve.polynomial.eval (crossing.point side)) //
    value = OwnerFrame.build (face.clearance.eval_ne_zero (lifted.cut_inside crossing position factory side))},
  Σ prepared : {value : Entry.TracedPoint models classified.entry.sheet (crossing.point side)
      (lifted.cut_inside crossing position factory side) count frame.val //
    value = Entry.TracedPoint.build models classified.entry.sheet (crossing.point side)
      (lifted.cut_inside crossing position factory side) count frame.val},
  {value : prepared.val.Connection
      (sourceFrame := retained.localFrames.frameAt _
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start))
      (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).start)
      (lifted.cutStart (apex := apex) position side).val (lifted.cutStart (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start).inside //
    value = prepared.val.connect
      (sourceFrame := retained.localFrames.frameAt _
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start))
      (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).start)
      (lifted.cutStart (apex := apex) position side).val (lifted.cutStart (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start).inside} ×
  {value : prepared.val.Connection
      (sourceFrame := retained.localFrames.frameAt _
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish))
      (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).finish)
      (lifted.cutFinish (apex := apex) position side).val (lifted.cutFinish (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish).inside //
    value = prepared.val.connect
      (sourceFrame := retained.localFrames.frameAt _
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish))
      (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).finish)
      (lifted.cutFinish (apex := apex) position side).val (lifted.cutFinish (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish).inside})

/-- Prepare one genuinely new cut Point and both actual signed connections on either side slot.

The old quad, Point, four corner Entries and row bank are inputs, never
replayed. New work is one cut frame, anchor trace/neighborhood/Point,
two source traces/selections and their two stationary OwnerJoins.
-/
def prepareSide (side : Fin 2) (count : Nat) : lifted.PreparedSide crossing position factory side count :=
  let frame := OwnerFrame.build (face.clearance.eval_ne_zero (lifted.cut_inside crossing position factory side))
  let prepared := Entry.TracedPoint.build models classified.entry.sheet (crossing.point side)
    (lifted.cut_inside crossing position factory side) count frame
  let first := prepared.connect
    (sourceFrame := retained.localFrames.frameAt _
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start))
    (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).start)
    (lifted.cutStart (apex := apex) position side).val (lifted.cutStart (apex := apex) position side).property
    (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start).inside
  let last := prepared.connect
    (sourceFrame := retained.localFrames.frameAt _
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish))
    (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).finish)
    (lifted.cutFinish (apex := apex) position side).val (lifted.cutFinish (apex := apex) position side).property
    (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish).inside
  (⟨(lifted, crossing), rfl⟩, ⟨⟨frame, rfl⟩, ⟨prepared, rfl⟩, ⟨first, rfl⟩, ⟨last, rfl⟩⟩)

namespace PreparedSide

variable {lifted crossing position factory} {side : Fin 2} {count : Nat}
variable (cached : lifted.PreparedSide crossing position factory side count)

/-- Read the whole original retained signed quad and Point-corner cache. -/
def original : classified.CellLift located vertices := cached.1.val.1

/-- Read the whole actual affine cut, without reconstructing its type-index factory. -/
def cut : AffineCut.CrossingCache lineFirst lineLast triangle apex := cached.1.val.2

/-- Read the one actual cut-point frame. -/
def frame : OwnerFrame (curve.polynomial.eval (crossing.point side)) := cached.2.1.val

/-- Read the one actual continued Point preparation shared by both endpoint connections. -/
def prepared : Entry.TracedPoint models classified.entry.sheet (crossing.point side)
    (lifted.cut_inside crossing position factory side) count cached.frame := cached.2.2.1.val

/-- The complete old quad cache is preserved. -/
theorem original_eq : cached.original = lifted := congrArg Prod.fst cached.1.property

/-- The complete original affine cut is preserved. -/
theorem cut_eq : cached.cut = crossing := congrArg Prod.snd cached.1.property

/-- The new frame retains its complete original isolation factory. -/
theorem frame_eq : cached.frame =
    OwnerFrame.build (face.clearance.eval_ne_zero (lifted.cut_inside crossing position factory side)) :=
  cached.2.1.property

/-- The new Point preparation retains its whole original factory on this SAME stored frame. -/
theorem prepared_eq : cached.prepared = Entry.TracedPoint.build models classified.entry.sheet (crossing.point side)
    (lifted.cut_inside crossing position factory side) count cached.frame := cached.2.2.1.property

/-- Read the complete start-to-cut connection, including its SAME actual stationary join. -/
def first : cached.prepared.Connection
      (sourceFrame := retained.localFrames.frameAt _
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start))
      (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).start)
      (lifted.cutStart (apex := apex) position side).val (lifted.cutStart (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start).inside :=
  cached.2.2.2.1.val

/-- Read the complete finish-to-cut connection, keeping its actual reverse-side orientation. -/
def last : cached.prepared.Connection
      (sourceFrame := retained.localFrames.frameAt _
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish))
      (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).finish)
      (lifted.cutFinish (apex := apex) position side).val (lifted.cutFinish (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish).inside :=
  cached.2.2.2.2.val

/-- The start connection is its whole once-executed factory on the retained cut Point. -/
theorem first_eq : cached.first = cached.prepared.connect
      (sourceFrame := retained.localFrames.frameAt _
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start))
      (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).start)
      (lifted.cutStart (apex := apex) position side).val (lifted.cutStart (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).start).inside :=
  cached.2.2.2.1.property

/-- The finish connection is its whole once-executed factory on that SAME retained cut Point. -/
theorem last_eq : cached.last = cached.prepared.connect
      (sourceFrame := retained.localFrames.frameAt _
        (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish))
      (index := vertices.sheet (apex.edge (lifted.cell.quad.faces position) side).finish)
      (lifted.cutFinish (apex := apex) position side).val (lifted.cutFinish (apex := apex) position side).property
      (vertices.coordinate_onGrid (apex.edge (lifted.cell.quad.faces position) side).finish).inside :=
  cached.2.2.2.2.property

end PreparedSide

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.PointEntry.CellLift

end
