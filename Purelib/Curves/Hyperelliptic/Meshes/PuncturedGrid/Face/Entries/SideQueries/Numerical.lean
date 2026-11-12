module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.SideQueries
public import Purelib.Riemann.Readings.UniformPreparedRequests.Subdivision
public import Purelib.Riemann.Integration.PreparedConstantModels.Query.Transport
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Meshes.UniformPrimitiveMesh

/-! # Original numerical requests for the same retained nonvertex side query

The actual full-side preparation and supplied center family are unchanged.
Certified membership in one original uniform mesh prepares the original
covered/request banks once. The existing query is reindexed only by whole
prepared-edge equality to its exact selected numerical parent.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates CenteredEdge centeredEdges)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Meshes.GridLiftedFaces.BranchCellBank (LiftedFace)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents LocalRequest)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {vertices : VertexBank bank.grid} {edges : RootEdgeBank frames}
variable {face : RegularFace bank} {models : FaceModels frames face} {point : Canonical}
variable {inside : face.cell.box.Contains point} {sourceOwner : Owner (curve.polynomial.eval point)}

namespace SideQuery.Cache

variable {acquired : Acquisition models inside sourceOwner} {side : GridSide}
variable {onSide : face.cell.OnSide point side}
variable {lifted : LiftedFace vertices edges face acquired.entry.sheet}
variable {differential : Differential genus} {notFinish : point ≠ side.finish face.cell.box}
variable (retained : SideQuery.Cache acquired side onSide lifted differential notFinish)
variable (centers : CenterStates curve differential acquired.entry.sheet
  (prepared acquired side lifted retained.connection).2.subdivision)
variable (bounds : Bounds retained.connection.forwardSegment) (mesh : Mesh bounds)
variable (covered : ∀ edge ∈ (prepared acquired side lifted retained.connection).2.subdivision.parameterEdges,
  edge ∈ mesh.edges)
variable (count : Nat) (target : Rational) (positive : 0 < target)

/-- The original two-cache request acquisition on this SAME retained full-side subdivision and supplied centers. -/
@[expose] def Numerical := RequestedParents.OnSubdivision bounds mesh acquired.entry.sheet
  (prepared acquired side lifted retained.connection).2.subdivision centers covered count target positive

/-- Construct the original covered patches and request bank once, without re-running the row or retained query. -/
def acquireNumerical : Numerical retained centers bounds mesh covered count target positive :=
  RequestedParents.ofSubdivision bounds mesh acquired.entry.sheet
    (prepared acquired side lifted retained.connection).2.subdivision centers covered count target positive

namespace Numerical

variable {retained centers bounds mesh covered count target positive}
variable (numerics : Numerical retained centers bounds mesh covered count target positive)

/-- Read the same actual covered-parent cache retained by the numerical acquisition. -/
@[expose] def patches : UniformPreparedMesh.CoveredParents count
    (centeredEdges curve differential acquired.entry.sheet
      (prepared acquired side lifted retained.connection).2.subdivision centers) :=
  RequestedParents.OnSubdivision.patches numerics

/-- Read the complete original numerical request bank, including all patches, observations and child blocks. -/
@[expose] def requests : RequestedParents count target
    (centeredEdges curve differential acquired.entry.sheet
      (prepared acquired side lifted retained.connection).2.subdivision centers) :=
  RequestedParents.OnSubdivision.requests numerics

/-- Read the literal selected parent from the original row's supplied centered family. -/
@[expose] def parent : CenteredEdge curve differential :=
  RequestedParents.OnSubdivision.parent numerics retained.location

/-- Read the whole original local primitive request at that identical selected numerical parent. -/
@[expose] def request : LocalRequest numerics.parent count target :=
  RequestedParents.OnSubdivision.request numerics retained.location

/-- The selected parent's complete prepared edge equals the original query edge, including the source and cache. -/
theorem parent_edge : numerics.parent.edge =
    queryEdge acquired side onSide lifted retained.connection differential retained.location :=
  RequestedParents.OnSubdivision.parent_edge numerics retained.location

/-- The selected numerical index is the original raw request occurrence, including rejected stationary prefixes. -/
theorem parent_index :
    (retained.location.centeredIndex differential acquired.entry.sheet centers).val = retained.requestIndex.val :=
  retained.location.centeredIndex_val differential acquired.entry.sheet centers

/-- The selected original request pays its actual child-block primitive-increment bound. -/
theorem request_accurate : Data.Gaussian.Norm.Basic.normSq
    (numerics.request.request.model.primitive.value.eval (numerics.parent.edge.point 1) -
      numerics.request.request.model.primitive.value.eval (numerics.parent.edge.point 0) -
      (Integration.Polynomial.Gaussian.Path.Basic.PathModel.mk
        (numerics.request.request.block.children.map CenteredEdge.model)).integralSample) < target :=
  RequestedParents.OnSubdivision.request_accurate numerics retained.location

/-- Reindex the SAME supplied cached query by actual whole-edge equality to the selected numerical parent. -/
@[expose] def query : PreparedEdge.Query numerics.parent.edge retained.location.fraction retained.location.inside :=
  PreparedEdge.Query.castEdge numerics.parent_edge.symm retained.query

/-- The selected numerical query retains the entire original query cache and its factory certificate. -/
theorem query_heq : HEq numerics.query retained.query :=
  PreparedEdge.Query.castEdge_heq numerics.parent_edge.symm retained.query

/-- The direct Owner of the selected numerical query is the SAME retained direct Owner. -/
theorem query_direct_heq : HEq numerics.query.direct retained.query.direct :=
  PreparedEdge.Query.castEdge_direct_heq numerics.parent_edge.symm retained.query

/-- The physical-index query Owner remains the SAME original retained Owner under the genuine edge transport. -/
theorem query_owner_heq : HEq numerics.query.owner retained.query.owner :=
  PreparedEdge.Query.castEdge_owner_heq numerics.parent_edge.symm retained.query

/-- The selected numerical parent's query point is the original retained Entry point. -/
theorem query_point : numerics.parent.edge.point retained.location.fraction = point :=
  (congrArg (fun edge : PreparedEdge curve differential => edge.point retained.location.fraction)
    numerics.parent_edge).trans
      (SideQuery.point_eq acquired side onSide lifted retained.connection differential retained.location)

end Numerical
end SideQuery.Cache
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.Acquisition

end
