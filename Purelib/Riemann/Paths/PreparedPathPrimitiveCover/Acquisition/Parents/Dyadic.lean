module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Refinement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.List.Map
import Purelib.Data.List.GetD

/-! # Original acquired centered parents at their exact retained dyadic occurrences

The original centers, traced subdivision and selected Mesh determine the
complete parameter-edge list. Its equality transports only bounded indices;
all parent/root/query caches and their original order remain unchanged.
-/

public section

namespace Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

namespace Acquisition.Segment.Parents

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenterStates CenteredEdge)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus}
variable {ambient : Box} {start finish : Canonical}
variable {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
variable {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
variable (differential : Differential genus) (sheet : Fin 2) (count : Nat)
variable (retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request)

variable (parents : Parents differential sheet count retained)

/-- The actual retained centered parents have the SAME ordered parameter-edge word as their actual acquired Mesh. -/
theorem parameterEdges_eq : parents.covered.parents.map CenteredEdge.parameterEdge = retained.mesh.edges :=
  (congrArg (List.map CenteredEdge.parameterEdge) parents.parents_eq).trans
    ((Riemann.Integration.PreparedSubdivisionModelCore.centeredEdges_parameterEdges
      curve differential sheet retained.traced.prepared.subdivision parents.centers).trans retained.edges_eq)

/-- The SAME original parent list has exactly the actual retained Mesh edge-list length. -/
theorem length_eq_edges : parents.covered.parents.length = retained.mesh.edges.length :=
  (Map.length_map CenteredEdge.parameterEdge parents.covered.parents).symm.trans
    (congrArg List.length (parameterEdges_eq differential sheet count retained parents))

/-- Read an original actual parent occurrence at its exact retained Mesh coordinate.

This is an index transport along the complete original ordered edge-word
readback. It constructs no center, parent, Mesh, source query or Owner.
-/
@[expose] def parentIndex (index : Fin retained.mesh.edges.length) : Fin parents.covered.parents.length :=
  Fin.cast (length_eq_edges differential sheet count retained parents).symm index

/-- The selected original parent's parameter edge is the SAME edge at the retained original Mesh occurrence. -/
theorem parameterEdge_at (index : Fin retained.mesh.edges.length) :
    (parents.covered.parents[(parentIndex differential sheet count retained parents index).val]'
      (parentIndex differential sheet count retained parents index).isLt).parameterEdge =
        retained.mesh.edges[index.val]'index.isLt := by
  let selected := parentIndex differential sheet count retained parents index
  have mappedBound : selected.val < (parents.covered.parents.map CenteredEdge.parameterEdge).length :=
    Eq.mpr (congrArg (fun length => selected.val < length)
      (Map.length_map CenteredEdge.parameterEdge parents.covered.parents)) selected.isLt
  have mapped := Map.getElem_map CenteredEdge.parameterEdge parents.covered.parents selected.val
    selected.isLt mappedBound
  have actual : (parents.covered.parents.map CenteredEdge.parameterEdge)[selected.val]'mappedBound =
      retained.mesh.edges[index.val]'index.isLt :=
    getElem_congr (parameterEdges_eq differential sheet count retained parents) rfl mappedBound
  exact mapped.symm.trans actual

end Acquisition.Segment.Parents

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
