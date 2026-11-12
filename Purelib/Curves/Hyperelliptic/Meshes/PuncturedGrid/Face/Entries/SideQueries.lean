module

import Purelib.Polynomial.Geometry.ClearPath

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Selection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Comparison
public import Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision.ParameterLocation
public import Purelib.Riemann.Paths.PreparedPathTrace.Single
public import Purelib.Riemann.Integration.PreparedConstantModels.Query
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Boundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic

/-! # Actual nonvertex side query from the same cached full-edge row

The stored grid-edge connection supplies its original row, complete segment,
lineage budget and request-fit proof. A half-open finite lookup reads the
actual accepted child; one new original direct query and one classification
in the SAME Entry frame are retained. Clear-face reachability and original
round-trip index laws derive its operational comparison to the old Owner.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

open Purelib
open Purelib.Polynomial.Geometry
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RegularFaces (EdgePoint)
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint)
open Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision (ParameterLocation locateParameter)
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.PreparedClearPathModels (zeroEndpoint oneEndpoint ownerAtStart CompleteSegment)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.RootPathTransport (TransportRow)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid.RootEdges (RootEdge)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter castOwnerParameter_heq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {vertices : VertexBank bank.grid} {edges : RootEdgeBank frames}
variable {face : RegularFace bank} {models : FaceModels frames face} {point : Canonical}
variable {inside : face.cell.box.Contains point} {sourceOwner : Owner (curve.polynomial.eval point)}

namespace SideQuery

/-- The exact original full-side connection type, with its original two retained endpoint frames. -/
@[expose] def Connection (face : RegularFace bank) (side : GridSide) : Type :=
  RootEdge (ambient := Cuts.Ambient curve)
    (frames.frameAt (side.start face.cell.box) (face.side side).vertices.1)
    (frames.frameAt (side.finish face.cell.box) (face.side side).vertices.2)

variable (acquired : Acquisition models inside sourceOwner) (side : GridSide)
variable (onSide : face.cell.OnSide point side)
variable (lifted : LiftedFace vertices edges face acquired.entry.sheet)

/-- Read the original full-side parameter of the same actual Entry point. -/
@[expose] def position (_acquired : Acquisition models inside sourceOwner) (side : GridSide)
    (onSide : face.cell.OnSide point side) : EdgePoint (face.side side) point :=
  face.boundaryPoint side point inside onSide

/-- A point different from the original full-side finish has a strict half-open parameter bound. -/
theorem parameter_lt_one (notFinish : point ≠ side.finish face.cell.box) :
    (position acquired side onSide).parameter < 1 := by
  refine ⟨(position acquired side onSide).inside.2, ?_⟩
  intro reverse
  have equal := Data.Rat.Fraction.Order.Basic.le_antisymm _ _
    (position acquired side onSide).inside.2 reverse
  have same := (position acquired side onSide).point_eq
  rewrite [equal, (face.side side).segment.pointAt_one] at same
  exact notFinish same.symm

/-- Both original side endpoints are in the SAME regular face, independently of the bank segment representation. -/
private theorem endpoints_inside : face.cell.box.Contains (side.start face.cell.box) ∧
    face.cell.box.Contains (side.finish face.cell.box) := by
  cases side with
  | bottom => exact ⟨⟨le_rfl, face.cell.box.x_valid, le_rfl, face.cell.box.y_valid⟩,
      ⟨face.cell.box.x_valid, le_rfl, le_rfl, face.cell.box.y_valid⟩⟩
  | right => exact ⟨⟨face.cell.box.x_valid, le_rfl, le_rfl, face.cell.box.y_valid⟩,
      ⟨face.cell.box.x_valid, le_rfl, face.cell.box.y_valid, le_rfl⟩⟩
  | top => exact ⟨⟨face.cell.box.x_valid, le_rfl, face.cell.box.y_valid, le_rfl⟩,
      ⟨le_rfl, face.cell.box.x_valid, face.cell.box.y_valid, le_rfl⟩⟩
  | left => exact ⟨⟨le_rfl, face.cell.box.x_valid, face.cell.box.y_valid, le_rfl⟩,
      ⟨le_rfl, face.cell.box.x_valid, le_rfl, face.cell.box.y_valid⟩⟩

/-- The full-side row's actual initial frame Owner is reached from this retained analytic face sheet. -/
private theorem source_reached : Reached face.cell.box (models.frame.owners acquired.entry.sheet)
    ((frames.frameAt (side.start face.cell.box) (face.side side).vertices.1).owners
      (lifted.sideStartSheet side)) := by
  have reached := (lifted.edge_endpoints_reached models side.kind).1
  rewrite [lifted.side_edge_eq] at reached
  have name := vertices.ownerName_index frames (side.start face.cell.box) (face.side side).vertices.1
    (lifted.sideStartSheet side)
  have equivalent := NamedEquivalent.transport rfl name (NamedEquivalent.refl
    (ownerName (vertices.owner frames (vertices.index (side.start face.cell.box) (face.side side).vertices.1
      (lifted.sideStartSheet side)))))
  exact reached.append (Reached.ofEquivalentAt
    (vertices.coordinate_index (side.start face.cell.box) (face.side side).vertices.1
      (lifted.sideStartSheet side)) equivalent)

section Connection

variable (connection : Connection (frames := frames) face side)

/-- Read the SAME original retained forward row at the actual lifted side's source sheet. -/
@[expose] def row : TransportRow (.cons connection.forwardSegment (.nil (side.finish face.cell.box)))
    (frames.frameAt (side.start face.cell.box) (face.side side).vertices.1)
    (frames.frameAt (side.finish face.cell.box) (face.side side).vertices.2) (lifted.sideStartSheet side) :=
  connection.forward.row (lifted.sideStartSheet side)

/-- The actual bank segment and the actual grid edge have the same exact affine point at every parameter.

This reads their identical nominal endpoints and pointAt equations. It
identifies no root Owners and executes no transport or preparation.
-/
theorem segment_point (time : Rational) :
    connection.forwardSegment.pointAt time = (face.side side).segment.pointAt time := by
  rewrite [ClearPath.ClearSegment.pointAt_eq_line connection.forwardSegment time,
    ClearPath.ClearSegment.pointAt_eq_line (face.side side).segment time]
  rfl

/-- Read the exact existing complete single-segment subdivision from the SAME original full-side row. -/
@[expose] def prepared : PSigma (fun within : connection.forwardSegment.WithinAmbient =>
    CompleteSegment connection.forwardSegment within
      ((frames.frameAt (side.start face.cell.box) (face.side side).vertices.1).owners
        (lifted.sideStartSheet side))) :=
  (row acquired side lifted connection).traced.prepared.singleSegment

/-- Read that row's original lineage budget and request-fit certificate without a new budget constructor. -/
@[expose] def budget : {paid : PreparedTraceBudget connection.forwardSegment zeroEndpoint oneEndpoint //
    paid.RequestsFit zeroEndpoint (prepared acquired side lifted connection).2.subdivision.requests} :=
  (row acquired side lifted connection).traced.lineage.singleBudget

/-- Exact query-position type on the SAME retained single-segment subdivision. -/
@[expose] def Location : Type := ParameterLocation (curve := curve)
  (position acquired side onSide).parameter (prepared acquired side lifted connection).2.subdivision

/-- Locate the requested boundary point in the actual stored full-side subdivision, skipping stationary requests. -/
def locate (notFinish : point ≠ side.finish face.cell.box) : Location acquired side onSide lifted connection :=
  locateParameter (curve := curve) (position acquired side onSide).parameter
    (prepared acquired side lifted connection).2.subdivision (position acquired side onSide).inside.1 (by
      rewrite [(prepared acquired side lifted connection).2.endpoint_eq]
      exact parameter_lt_one acquired side onSide notFinish)

variable (differential : Differential genus)
variable (location : Location acquired side onSide lifted connection)

/-- Read the exact original accepted-step edge selected within the same cached full-side row. -/
@[expose] def queryEdge : PreparedConstantModels.PreparedEdge curve differential :=
  location.edge differential acquired.entry.sheet

/-- The selected child's original affine point is the SAME physical old Entry point. -/
theorem point_eq : (queryEdge acquired side onSide lifted connection differential location).point location.fraction =
    point :=
  (location.point_eq differential acquired.entry.sheet).trans
    ((segment_point side connection (position acquired side onSide).parameter).trans
      (position acquired side onSide).point_eq)

/-- The exact original query-cache type at the selected accepted step and its original local fraction. -/
@[expose] def Query : Type := PreparedConstantModels.PreparedEdge.Query
  (queryEdge acquired side onSide lifted connection differential location) location.fraction location.inside

variable (query : Query acquired side onSide lifted connection differential location)

/-- Reindex that SAME retained original query Owner to its proved physical Entry point. -/
@[expose] def queryOwner : Owner (curve.polynomial.eval point) :=
  castOwnerParameter (congrArg curve.polynomial.eval
    (point_eq acquired side onSide lifted connection differential location)) query.owner

/-- Physical-point transport preserves the entire original direct-query Owner heterogeneously. -/
theorem queryOwner_heq : HEq (queryOwner acquired side onSide lifted connection differential location query)
    query.direct :=
  (castOwnerParameter_heq _ query.owner).trans (castOwnerParameter_heq _ query.direct)

/-- The actual direct query is reached from the SAME analytic face sheet through retained subdivision lineage.

The original source-frame incidence, single-row budget and request-fit
proof discharge every geometric premise. Canonical center values occur
only in this erased proof to consume the existing original theorem; they
are not runtime observations or a re-executed numerical parent bank.
-/
private theorem query_reached : Reached face.cell.box (models.frame.owners acquired.entry.sheet)
    (queryOwner acquired side onSide lifted connection differential location query) := by
  let first := (prepared acquired side lifted connection).2
  let paid := budget acquired side lifted connection
  have initial : Reached face.cell.box (models.frame.owners acquired.entry.sheet)
      (ownerAtStart connection.forwardSegment
        ((frames.frameAt (side.start face.cell.box) (face.side side).vertices.1).owners
          (lifted.sideStartSheet side))) :=
    (source_reached acquired side lifted).castFinish connection.forwardSegment.pointAt_zero.symm (by
      unfold ownerAtStart
      exact (castOwnerParameter_heq _ _).symm)
  let centers := PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential acquired.entry.sheet
    first.subdivision
  have roots := (PreparedFaceTracePrefixes.subdivision_reached face.clearance differential connection.forwardSegment
    (prepared acquired side lifted connection).1 (endpoints_inside side).1 (endpoints_inside side).2
    acquired.entry.sheet paid.1 first.subdivision centers paid.2 initial).1
  obtain ⟨parent, member, same⟩ := location.centered_member differential acquired.entry.sheet centers
  have reached := (roots parent member).query_reached location.fraction location.inside
  rewrite [same] at reached
  have physical : (queryEdge acquired side onSide lifted connection differential location).segment.pointAt
      (Riemann.Branches.PreparedSheetContinuation.parameterAt
        (queryEdge acquired side onSide lifted connection differential location).left
        (queryEdge acquired side onSide lifted connection differential location).request location.fraction) = point :=
    (Riemann.Branches.PreparedSheetContinuation.pointAt_parameterAt
      (queryEdge acquired side onSide lifted connection differential location).segment
      (queryEdge acquired side onSide lifted connection differential location).within
      (queryEdge acquired side onSide lifted connection differential location).left
      (queryEdge acquired side onSide lifted connection differential location).request location.fraction).trans
        (point_eq acquired side onSide lifted connection differential location)
  exact reached.castFinish physical ((heq_of_eq query.direct_eq.symm).trans
    (queryOwner_heq acquired side onSide lifted connection differential location query).symm)

/-- Compare the new original full-side query to the distinct old Owner using the SAME Entry frame and two-way banks.

A retained reclassification is an original Acquisition, not another root
relation object. Reachability proves its face sheet; cached round-trip
indices then identify its actual point-frame selection with the old one.
The returned Type-valued comparison composes those actual selections;
no existential Prop witness is extracted as executable data.
-/
def equivalent (selected : Acquisition models inside
      (queryOwner acquired side onSide lifted connection differential location query))
    (selected_eq : selected = acquired.selectOwner
      (queryOwner acquired side onSide lifted connection differential location query)) :
    NamedEquivalent
      (ownerName (queryOwner acquired side onSide lifted connection differential location query))
      (ownerName sourceOwner) := by
  let fromRow : Entry models point (queryOwner acquired side onSide lifted connection differential location query) :=
    ⟨acquired.entry.sheet, query_reached acquired side onSide lifted connection differential location query⟩
  exact acquired.equivalentOfEntry
    (queryOwner acquired side onSide lifted connection differential location query) selected selected_eq fromRow rfl

/-- Retain the old connection, selected branch, one new actual query, same-bank classification and comparison.

All fields use existing original containers. This cache boundary records
the new query/selection work that the original RootEdge does not retain;
it neither copies a paid trace nor replaces either original Owner.
-/
@[expose] def Cache (notFinish : point ≠ side.finish face.cell.box) : Type :=
  Σ connection : {value : Connection (frames := frames) face side // value = edges.edge (face.side side)},
  Σ location : {value : Location acquired side onSide lifted connection.val //
    value = locate acquired side onSide lifted connection.val notFinish},
  Σ query : {value : Query acquired side onSide lifted connection.val differential location.val //
    value = PreparedConstantModels.PreparedEdge.Query.build
      (queryEdge acquired side onSide lifted connection.val differential location.val)
      location.val.fraction location.val.inside},
  Σ selected : {value : Acquisition models inside
      (queryOwner acquired side onSide lifted connection.val differential location.val query.val) //
    value = acquired.selectOwner
      (queryOwner acquired side onSide lifted connection.val differential location.val query.val)},
  {value : NamedEquivalent
      (ownerName (queryOwner acquired side onSide lifted connection.val differential location.val query.val))
      (ownerName sourceOwner) //
    value = equivalent acquired side onSide lifted connection.val differential location.val query.val
      selected.val selected.property}

/-- Execute only one new original direct query and point-frame classification after reading the same stored side row.

The finite lookup precedes the query. Reclassification then reuses every
old Entry route/transport cache, and the final operational comparison
consumes the two actual selected frame occurrences. Original edge/root
preparation and the paid source execution are never rebuilt.
-/
def build (notFinish : point ≠ side.finish face.cell.box) :
    Cache acquired side onSide lifted differential notFinish :=
  let connection := edges.edge (face.side side)
  let location := locate acquired side onSide lifted connection notFinish
  let query := PreparedConstantModels.PreparedEdge.Query.build
    (queryEdge acquired side onSide lifted connection differential location) location.fraction location.inside
  let selected := acquired.selectOwner (queryOwner acquired side onSide lifted connection differential location query)
  let compared := equivalent acquired side onSide lifted connection differential location query selected rfl
  ⟨⟨connection, rfl⟩, ⟨location, rfl⟩, ⟨query, rfl⟩, ⟨selected, rfl⟩, ⟨compared, rfl⟩⟩

end Connection

variable (differential : Differential genus)

namespace Cache

variable {acquired side onSide lifted differential}
variable {notFinish : point ≠ side.finish face.cell.box}
variable (retained : Cache acquired side onSide lifted differential notFinish)

/-- Read the whole original root-edge connection selected from the old bank. -/
@[expose] def connection : Connection (frames := frames) face side := retained.1.val

/-- Read the actual selected accepted-request position, retaining its original cache/Owner indices. -/
@[expose] def location : Location acquired side onSide lifted retained.connection := retained.2.1.val

/-- Read the whole once-built original direct-query cache at that same accepted request. -/
@[expose] def query : Query acquired side onSide lifted retained.connection differential retained.location :=
  retained.2.2.1.val

/-- Read the SAME actual queried Owner, changing only its derived physical-point index. -/
@[expose] def owner : Owner (curve.polynomial.eval point) :=
  queryOwner acquired side onSide lifted retained.connection differential retained.location retained.query

/-- Read the whole same-bank Entry classification of this new query, including both unchanged route banks. -/
@[expose] def selected : Acquisition models inside retained.owner := retained.2.2.2.1.val

/-- Read the actual operational comparison of the new full-side query and the distinct old Entry Owner. -/
@[expose] def equivalent : NamedEquivalent (ownerName retained.owner) (ownerName sourceOwner) := retained.2.2.2.2.val

/-- The connection is exactly the old retained bank lookup, not another edge acquisition. -/
theorem connection_eq : retained.connection = edges.edge (face.side side) := retained.1.property

/-- The selected branch is the whole deterministic lookup on the SAME original prepared subdivision. -/
theorem location_eq : retained.location = locate acquired side onSide lifted retained.connection notFinish :=
  retained.2.1.property

/-- The query is the complete one-time original factory output on its exact selected cache and fraction. -/
theorem query_eq : retained.query = PreparedConstantModels.PreparedEdge.Query.build
    (queryEdge acquired side onSide lifted retained.connection differential retained.location)
    retained.location.fraction retained.location.inside := retained.2.2.1.property

/-- The selected Acquisition is the whole once-built result sharing all old geometry and transport caches. -/
theorem selected_eq : retained.selected = acquired.selectOwner retained.owner := retained.2.2.2.1.property

/-- The comparison is exactly the original-selection composition on these actual retained inputs. -/
theorem equivalent_eq : retained.equivalent =
    SideQuery.equivalent acquired side onSide lifted retained.connection differential retained.location retained.query
      retained.selected retained.selected_eq := retained.2.2.2.2.property

/-- The physical query Owner preserves the complete original direct Owner, not merely its displayed coordinate/name. -/
theorem owner_heq : HEq retained.owner retained.query.direct :=
  queryOwner_heq acquired side onSide lifted retained.connection differential retained.location retained.query

/-- Attach the new full-side query to the SAME actual retained outward row's finish Owner.

The old row comparison is read from the original acquired route/selection
caches. Composing it with the derived new comparison executes no old
transport, query, observation or OwnerJoin factory again.
-/
def forward_equivalent : NamedEquivalent (ownerName retained.owner)
    (ownerName (acquired.forward.row acquired.entry.sheet).traced.finishOwner) :=
  retained.equivalent.trans (Acquisition.equivalent acquired).symm

/-- The new query classification preserves the complete old forward transport bank heterogeneously. -/
theorem forward_reused : HEq retained.selected.forward acquired.forward := by
  have transport : ∀ first last : Acquisition models inside retained.owner,
      first = last → HEq first.forward last.forward := by
    intro first last same
    cases same
    rfl
  exact (transport _ _ retained.selected_eq).trans (acquired.selectOwner_forward retained.owner)

/-- The actual source occurrence in the retained accepted-request list remains directly executable. -/
@[expose] def requestIndex : Fin (prepared acquired side lifted retained.connection).2.subdivision.requests.length :=
  retained.location.index

end Cache

open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)

/-- Select the actual stored mesh face on the old Entry sheet, then construct the genuine nonvertex query attachment.

The original finite mesh location and complete query cache are retained
with their factory identities. The caller supplies actual old models and
Entry acquisition at the literal regular-list index, never a final signed
comparison, root-chain readiness or canonical/homology conclusion.
-/
def atMeshFace {faces : PuncturedFaces bank} (mesh : LiftedMesh vertices edges faces)
    (index : Fin faces.regulars.length) {models : FaceModels frames (faces.regulars[index.val]'index.isLt)}
    {inside : (faces.regulars[index.val]'index.isLt).cell.box.Contains point}
    (acquired : Acquisition models inside sourceOwner) (side : GridSide)
    (onSide : (faces.regulars[index.val]'index.isLt).cell.OnSide point side)
    (differential : Differential genus)
    (notFinish : point ≠ side.finish (faces.regulars[index.val]'index.isLt).cell.box) :
    Σ located : {value : mesh.LocatedFace index acquired.entry.sheet //
      value = mesh.locateFace index acquired.entry.sheet},
    {value : Cache acquired side onSide located.val.lifted differential notFinish //
      value = build acquired side onSide located.val.lifted differential notFinish} :=
  let located := mesh.locateFace index acquired.entry.sheet
  let result := build acquired side onSide located.lifted differential notFinish
  ⟨⟨located, rfl⟩, ⟨result, rfl⟩⟩

end SideQuery
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

end
