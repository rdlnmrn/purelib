module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.SideQueries.Numerical
public import Purelib.Riemann.Readings.UniformPreparedRequests.Face.Query
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Riemann.Integration.RectangularPrimitiveModels
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples

/-! # One original Point acquisition for the same retained numerical side query

The numerical request and direct Query are inputs. Their exact whole-edge
and physical-point laws reindex the already retained side classification,
preserving its complete acquisition. One genuinely new Point is then
cached with its whole original factory equality. Both face-entry and
primitive-piece consumers use this same Point; no query or bank is replayed.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Face.Entries.FaceModels (Entry)
open Face.InverseModels.BranchCellBank (FaceModels)
open Face.Periods (PeriodDomain)
open Face.FragmentReadings (FragmentBounds)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann
open Branches.RectangularSheetGauge
open Integration.PreparedSubdivisionModelCore (CenterStates)
open Integration.UniformPrimitiveNeighborhoods (Bounds)
open Integration.RectangularPrimitiveModels (Primitives)
open Meshes.UniformPrimitiveMesh (Mesh)
open Meshes.PuncturedGridFaces (RegularFace)
open Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Meshes.GridLiftedDualSteps (GridSide)
open Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Paths.RectangularSegmentSplitting (SegmentPiece SegmentSplit)
open Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Owner.Transport (castOwnerParameter_heq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {vertices : VertexBank bank.grid} {edges : RootEdgeBank frames}
variable {face : RegularFace bank} {models : FaceModels frames face} {point : Canonical}
variable {inside : face.cell.box.Contains point} {sourceOwner : Owner (curve.polynomial.eval point)}
variable {acquired : Acquisition models inside sourceOwner} {side : GridSide}
variable {onSide : face.cell.OnSide point side}
variable {lifted : LiftedFace vertices edges face acquired.entry.sheet}
variable {differential : Differential genus} {notFinish : point ≠ side.finish face.cell.box}
variable {queried : SideQuery.Cache acquired side onSide lifted differential notFinish}
variable {centers : CenterStates curve differential acquired.entry.sheet
  (SideQuery.prepared acquired side lifted queried.connection).2.subdivision}
variable {bounds : Bounds queried.connection.forwardSegment} {mesh : Mesh bounds}
variable {covered : ∀ edge ∈ (SideQuery.prepared acquired side lifted queried.connection).2.subdivision.parameterEdges,
  edge ∈ mesh.edges}
variable {count : Nat} {target : Rational} {positive : 0 < target}

namespace SideQuery.Cache.Numerical

variable (numerics : SideQuery.Cache.Numerical queried centers bounds mesh covered count target positive)

/-- The literal selected numerical query point is inside the same old retained face. -/
theorem face_inside : face.cell.box.Contains (numerics.parent.edge.point queried.location.fraction) :=
  Eq.mpr (congrArg face.cell.box.Contains numerics.query_point) inside

/-- Whole query transport preserves the complete Owner of the stored side classification.

This is heterogeneous identity from the two original parameter transports,
not a signed relation inferred from matching physical coordinates.
-/
theorem physical_owner_heq : HEq numerics.query.owner queried.owner := by
  let originalEdge := SideQuery.queryEdge acquired side onSide lifted queried.connection differential queried.location
  have original : HEq queried.query.owner queried.query.direct :=
    castOwnerParameter_heq (originalEdge.directQueryParameter_eq queried.location.fraction) queried.query.direct
  exact numerics.query_owner_heq.trans (original.trans queried.owner_heq.symm)

/-- Reindex the SAME complete stored side acquisition to this literal numerical query Owner. -/
@[expose] def queryAcquisition : Entry.Acquisition models numerics.face_inside numerics.query.owner :=
  Entry.Acquisition.castPoint (lastInside := numerics.face_inside) numerics.query_point.symm
    numerics.physical_owner_heq.symm queried.selected

/-- The reindexed acquisition retains every original cache and factory equality heterogeneously. -/
theorem queryAcquisition_heq : HEq numerics.queryAcquisition queried.selected :=
  Entry.Acquisition.castPoint_heq (lastInside := numerics.face_inside) numerics.query_point.symm
    numerics.physical_owner_heq.symm queried.selected

/-- The reindexed acquisition uses exactly the old retained query-classification sheet. -/
theorem queryAcquisition_sheet : numerics.queryAcquisition.entry.sheet = queried.selected.entry.sheet :=
  Entry.Acquisition.castPoint_sheet (lastInside := numerics.face_inside) numerics.query_point.symm
    numerics.physical_owner_heq.symm queried.selected

/-- One complete new Point and its exact original factory on this SAME numerical request/query.

The side query cache contains no uniform-patch Point. This existing
Subtype container retains that genuinely new computation, while the
original request, query and acquisition remain their nominal inputs.
-/
@[expose] def PointAcquisition :=
  {sample : ContinuedNeighborhood.Point numerics.request.neighborhood
      (numerics.parent.edge.point queried.location.fraction) //
    sample = ContinuedNeighborhood.Point.acquire numerics.request.neighborhood
      (numerics.parent.edge.point queried.location.fraction)
      (numerics.request.point_inside queried.location.inside)}

/-- Execute the original Point factory once after reading the same retained request and query. -/
def acquirePoint : PointAcquisition numerics :=
  let sample := ContinuedNeighborhood.Point.acquire numerics.request.neighborhood
    (numerics.parent.edge.point queried.location.fraction)
    (numerics.request.point_inside queried.location.inside)
  ⟨sample, rfl⟩

namespace PointAcquisition

variable {numerics} (retained : PointAcquisition numerics)

/-- Read the complete once-acquired Point with its own Owner, refinements and parameter norm. -/
@[expose] def sample : ContinuedNeighborhood.Point numerics.request.neighborhood
    (numerics.parent.edge.point queried.location.fraction) := retained.val

/-- The whole retained Point is exactly the original factory on the same request neighborhood and query point. -/
theorem sample_eq : retained.sample = ContinuedNeighborhood.Point.acquire numerics.request.neighborhood
    (numerics.parent.edge.point queried.location.fraction)
    (numerics.request.point_inside queried.location.inside) := retained.property

/-- Derive the actual face Entry for this same cached Point from the original stored query acquisition. -/
@[expose] def entry : Entry models (numerics.parent.edge.point queried.location.fraction) retained.sample.owner :=
  numerics.request.retainedQueryEntry numerics.query retained.sample numerics.queryAcquisition

include retained in
/-- The same once-acquired Point pays the original piece bound on the supplied retained domain and primitives.

The domain retains the old face models and actual query-acquisition sheet.
Its primitive constants, request residual and oriented piece displacement
remain unchanged. No Point or Entry acquisition is executed in this proof.
-/
theorem piece_le {last : Canonical}
    (domain : PeriodDomain models numerics.queryAcquisition.entry.sheet)
    (split : SegmentSplit domain.cuts (numerics.parent.edge.point queried.location.fraction) last)
    (lastInside : numerics.request.neighborhood.box.Contains last)
    (bounds : FragmentBounds domain.patch differential)
    (piece : SegmentPiece domain.geometry (numerics.parent.edge.point queried.location.fraction) last)
    (member : piece ∈ split.pieces) {index : Nat}
    (primitives : Primitives (Transitions.oriented (domain.patch.sheets.refine index).transitions
      (domain.patch.sheets.refine index).gauge)
      (Readings.PreparedPrimitiveSamples.differentialNumerator differential)) :
    normSq ((primitives.value piece.column piece.row piece.lastPoint -
      primitives.value piece.column piece.row piece.firstPoint) -
      (numerics.request.request.model.primitive.value.eval piece.lastPoint -
        numerics.request.request.model.primitive.value.eval piece.firstPoint)) ≤
      numerics.request.facePieceCharge domain bounds piece index :=
  numerics.request.faceQuery_increment_le numerics.query retained.sample numerics.queryAcquisition
    domain split lastInside bounds piece member primitives

end PointAcquisition
end SideQuery.Cache.Numerical
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

end
