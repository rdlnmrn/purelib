module

public import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision.ParameterLocation.Centered
public import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic

/-! # Original primitive requests on a supplied covered prepared subdivision

The original subdivision and complete center family remain supplied inputs.
A genuine uniform-mesh membership certificate derives strict parameter
widths. The covered-parent and primitive-request producers then run once,
in that order, retaining both complete original results and factory laws.
-/

public section

namespace Purelib.Riemann.Readings.UniformPreparedRequests.RequestedParents

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Subdivision Endpoint)
open Purelib.Riemann.Branches.PreparedSheetContinuation.Subdivision (ParameterLocation)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates CenteredEdge centeredEdges)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

variable {ambient : Box} {start finish : Canonical} {segment : ClearSegment curve.polynomial ambient start finish}
variable {within : segment.WithinAmbient}
variable (bounds : Bounds segment) (mesh : Mesh bounds) (sheet : Fin 2)

/-- Actual membership in the same uniform mesh derives properness of every supplied centered parent. -/
theorem proper_of_mesh : {left : Endpoint} →
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))} →
    (subdivision : Subdivision segment within left owner) →
    (centers : CenterStates curve differential sheet subdivision) →
    (∀ edge ∈ subdivision.parameterEdges, edge ∈ mesh.edges) →
      AllParentsProper (centeredEdges curve differential sheet subdivision centers)
  | _, _, .stop _ _, _, _ => trivial
  | _, _, .next _ _ _ _ _ _ remaining, centers, covered =>
      ⟨UniformPreparedMesh.Mesh.edge_strict mesh (covered _ (List.mem_cons_self ..)),
        proper_of_mesh remaining centers.2
          (fun edge member => covered edge (List.mem_cons_of_mem _ member))⟩

variable {left : Endpoint} {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
variable (subdivision : Subdivision segment within left owner)
variable (centers : CenterStates curve differential sheet subdivision)
variable (covered : ∀ edge ∈ subdivision.parameterEdges, edge ∈ mesh.edges)
variable (count : Nat) (target : Rational) (positive : 0 < target)

/-- Retain the two original once-built covered/request banks on these identical subdivision and center inputs. -/
@[expose] def OnSubdivision :=
  Σ patches : {value : CoveredParents count (centeredEdges curve differential sheet subdivision centers) //
    value = CoveredParents.ofSubdivision bounds mesh sheet count subdivision centers covered},
  {requests : RequestedParents count target (centeredEdges curve differential sheet subdivision centers) //
    requests = RequestedParents.acquire patches.val target positive
      (proper_of_mesh bounds mesh sheet subdivision centers covered)}

/-- Build only the original covered patches and their original primitive requests, once each in that order. -/
def ofSubdivision : OnSubdivision bounds mesh sheet subdivision centers covered count target positive :=
  let patches := CoveredParents.ofSubdivision bounds mesh sheet count subdivision centers covered
  let requests := RequestedParents.acquire patches target positive
    (proper_of_mesh bounds mesh sheet subdivision centers covered)
  ⟨⟨patches, rfl⟩, ⟨requests, rfl⟩⟩

namespace OnSubdivision

variable {bounds mesh sheet subdivision centers covered count target positive}
variable (retained : OnSubdivision bounds mesh sheet subdivision centers covered count target positive)

/-- Read the whole original covered-parent result, with all patches and endpoint containments. -/
@[expose] def patches : CoveredParents count (centeredEdges curve differential sheet subdivision centers) :=
  retained.1.val

/-- Read the whole original once-built primitive-request bank, including every original child block. -/
@[expose] def requests : RequestedParents count target (centeredEdges curve differential sheet subdivision centers) :=
  retained.2.val

/-- The covered-parent cache is the exact original producer on the same supplied subdivision and centers. -/
theorem patches_eq : retained.patches =
    CoveredParents.ofSubdivision bounds mesh sheet count subdivision centers covered := retained.1.property

/-- The request bank is the exact original acquisition on that same whole covered cache and derived properness. -/
theorem requests_eq : retained.requests = RequestedParents.acquire retained.patches target positive
    (proper_of_mesh bounds mesh sheet subdivision centers covered) := retained.2.property

variable {time : Rational}

/-- Read the literal centered parent at the selected raw occurrence; no center or Owner is acquired. -/
@[expose] def parent
    (_bank : OnSubdivision bounds mesh sheet subdivision centers covered count target positive)
    (location : ParameterLocation time subdivision) : CenteredEdge curve differential :=
  (centeredEdges curve differential sheet subdivision centers)[(location.centeredIndex differential sheet centers).val]'
    (location.centeredIndex differential sheet centers).isLt

variable (location : ParameterLocation time subdivision)

/-- Read the complete original local request at that identical selected occurrence. -/
@[expose] def request : LocalRequest (retained.parent location) count target :=
  retained.requests.get (location.centeredIndex differential sheet centers)

/-- The selected local request uses the identical accepted-step edge as the supplied original location query. -/
theorem parent_edge : (retained.parent location).edge = location.edge differential sheet :=
  location.centeredEdge_at differential sheet centers

/-- The actual selected request pays its own original local primitive-increment bound. -/
theorem request_accurate : Norm.Basic.normSq
    ((retained.request location).request.model.primitive.value.eval ((retained.parent location).edge.point 1) -
      (retained.request location).request.model.primitive.value.eval ((retained.parent location).edge.point 0) -
      (Integration.Polynomial.Gaussian.Path.Basic.PathModel.mk
    ((retained.request location).request.block.children.map CenteredEdge.model)).integralSample) < target := by
  rewrite [Norm.Basic.normSq_eq_canonical]
  exact (retained.request location).accurate positive

end OnSubdivision
end Purelib.Riemann.Readings.UniformPreparedRequests.RequestedParents

end
