module

public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents
public import Purelib.Polynomial.Geometry.ClearPath.HalfOpen
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Half-open starts of the same retained paid moving parents

The actual paid mesh and its stored centered-edge identity derive strict
parameter progress. Every original child source lies in its same physical
segment's half-open image, including depth zero. These statements preserve
all root owners, centers, requests, acquisitions and stationary trace links.
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
open Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (dyadicEdges dyadicEdges_strict)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (CenteredEdge centeredEdges centeredEdges_parameterEdges centeredEdges_point_zero)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)

variable {genus : Nat} {curve : HyperellipticCurve genus}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment curve.polynomial ambient start finish} {within : segment.WithinAmbient}
    {sourceOwner : Owner (curve.polynomial.eval start)} {request : AccuracyRequest}
    {differential : Differential genus} {sheet : Fin 2} {count : Nat}
    {retained : Segment (segment := segment) (within := within) (owner := sourceOwner) request}
    (parents : Parents differential sheet count retained)

/-- Every retained moving child keeps strict parameter progress from the exact actual paid mesh.

Only original list and mesh equalities are consumed. No subdivision, center
state, source preparation, root continuation or canonical mesh is acquired.
-/
theorem child_parameter_strict (child : CenteredEdge curve differential)
    (member : child ∈ parents.covered.parents) :
    child.parameterEdge.left.parameter < child.parameterEdge.right.parameter := by
  have original : child ∈ centeredEdges curve differential sheet
      retained.traced.prepared.subdivision parents.centers :=
    Eq.mp (congrArg (fun entries => child ∈ entries) parents.parents_eq) member
  have parameterMember : child.parameterEdge ∈ retained.traced.prepared.subdivision.parameterEdges := by
    rewrite [← centeredEdges_parameterEdges curve differential sheet
      retained.traced.prepared.subdivision parents.centers]
    exact Map.mem_map_of_mem original
  have meshMember : child.parameterEdge ∈ retained.mesh.edges :=
    Eq.mp (congrArg (fun edges => child.parameterEdge ∈ edges) retained.edges_eq) parameterMember
  change child.parameterEdge ∈ dyadicEdges retained.mesh.depth firstEndpoint lastEndpoint at meshMember
  exact dyadicEdges_strict retained.mesh.depth firstEndpoint lastEndpoint
    (by decide +kernel : (0 : Data.Rat.Fraction.Rational) < 1) child.parameterEdge meshMember

/-- Every actual moving child starts strictly before the physical segment's terminal parameter one. -/
theorem child_left_lt_one (child : CenteredEdge curve differential)
    (member : child ∈ parents.covered.parents) : child.parameterEdge.left.parameter < 1 :=
  (parents.child_parameter_strict child member).trans_le child.parameterEdge.right.inside.2

/-- The same original child source belongs to its actual physical segment's half-open image.

The witness is the child's retained left endpoint and its original point
readback. Root owners, independent center observations and signed stationary
handoffs remain separate original objects; no half-open surrogate path runs.
-/
theorem child_start_halfOpen (child : CenteredEdge curve differential)
    (member : child ∈ parents.covered.parents) :
    (ClearPath.cons segment (ClearPath.nil finish)).HalfOpen (child.edge.point 0) := by
  have original : child ∈ centeredEdges curve differential sheet
      retained.traced.prepared.subdivision parents.centers :=
    Eq.mp (congrArg (fun entries => child ∈ entries) parents.parents_eq) member
  exact Or.inl ⟨child.parameterEdge.left.parameter, child.parameterEdge.left.inside.1,
    parents.child_left_lt_one child member,
    centeredEdges_point_zero curve differential sheet retained.traced.prepared.subdivision
      parents.centers child original⟩

/-- A nonstationary original segment's same actual child source cannot equal its excluded physical finish. -/
theorem child_start_ne_finish (nonstationary : start ≠ finish) (child : CenteredEdge curve differential)
    (member : child ∈ parents.covered.parents) : child.edge.point 0 ≠ finish := by
  have original : child ∈ centeredEdges curve differential sheet
      retained.traced.prepared.subdivision parents.centers :=
    Eq.mp (congrArg (fun entries => child ∈ entries) parents.parents_eq) member
  rewrite [centeredEdges_point_zero curve differential sheet retained.traced.prepared.subdivision
    parents.centers child original]
  exact segment.pointAt_ne_finish nonstationary (parents.child_left_lt_one child member)

end Acquisition.Segment.Parents

end Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath

end
