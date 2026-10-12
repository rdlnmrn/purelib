module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Integration.UniformPreparedPrimitives
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

/-!
# Covered executable prepared subdivisions

One computed depth pays both primitive coverage and prepared continuation
safety.  The actual dependent subdivision, persisted centers, and ordinary
edge list are cached together with a covered primitive patch for each edge.
Generated subdivisions and centers may enter through the semantic constructor;
the automatic constructor has no successful-check or coverage premise.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh

open Purelib
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic
open Purelib.Data.List
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Geometry.Path.Gaussian
open Purelib.Polynomial
open Purelib.Polynomial.Geometry
open Purelib.Riemann.Branches
open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.Branches.PreparedSheetContinuation
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
open Purelib.Riemann.Meshes
open Purelib.Riemann.Meshes.UniformPrimitiveMesh
open Purelib.Riemann.Topology

/-- Exact rational coordinates and quantitative bounds. -/
private abbrev Coordinate := Fraction.Rational
/-- Exact Gaussian rational coordinates of the prepared segment. -/
private abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- A rational box retaining the segment ambient region. -/
private abbrev Box := Rational.Box
/-- The executable Gaussian polynomial defining the curve. -/
private abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (Mesh)

/-- The retained square-root owner for the polynomial value at an endpoint. -/
abbrev Owner := SquareRootContinuationChain.Owner

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

set_option genInjectivity false in
/-- Retain a covering patch for every displayed parent and both of its endpoints.

The dependent spine keeps each original parent as its index and stores its exact patch together with the same endpoint
containment and tail association. -/
inductive CoveredParents (count : Nat) : List (PreparedSubdivisionModelCore.CenteredEdge curve differential) → Type
  /-- The empty parent list requires no covering patches. -/ | nil :
    Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents count []
  /-- Retain a patch covering the head parent endpoint and the covering certificates for its exact tail. -/ | cons
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} {remaining : List
    (PreparedSubdivisionModelCore.CenteredEdge curve differential)}
      (patch : UniformPrimitiveSheetCompatibility.PreparedPatch parent)
      (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
      (tail : Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents count remaining) :
        Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents count (parent ::
        remaining)

constructive_injectivity CoveredParents

namespace CoveredParents

variable {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish} {within :
    segment.WithinAmbient}

/-- Attach a covering primitive patch to each edge of the retained subdivision.

The dependent spine preserves the exact edge-to-patch association. One retained segment bound cache supplies every
patch, while the original tail and its centers are passed unchanged to the recursion. -/
@[expose] def ofSubdivision (bounds : UniformPrimitiveNeighborhoods.Bounds segment) (mesh : UniformPrimitiveMesh.Mesh
  bounds) (sheet : Fin 2) (count : Nat)
    {left : PreparedSubdivisionModelCore.Endpoint} {owner :
      Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Owner (curve.polynomial.eval (segment.pointAt
      left.parameter))} :
    (subdivision : PreparedSheetContinuation.Subdivision segment within left owner) →
    (centers : PreparedSubdivisionModelCore.CenterStates curve differential sheet subdivision) →
    (covered : ∀ edge ∈ subdivision.parameterEdges, edge ∈ mesh.edges) →
    Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents count
      (PreparedSubdivisionModelCore.centeredEdges curve differential sheet subdivision centers)
  | .stop _ _, _, _ => .nil
  | .next left owner request cached ordered small remaining, centers, covered => by
      let parent : PreparedSubdivisionModelCore.CenteredEdge curve differential :=
        ⟨edgeOfStep curve differential segment within left owner request cached ordered small sheet, centers.1⟩
      let patch := PreparedPatch.ofBounds parent bounds
      have headMember : parent.parameterEdge ∈ mesh.edges := covered _ (List.mem_cons_self ..)
      exact .cons patch (patch.finish_inside_of_mesh count mesh headMember)
        (Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents.ofSubdivision bounds
          mesh sheet count remaining centers.2
          (fun edge member => covered edge (List.mem_cons_of_mem _ member)))
termination_by structural subdivision => subdivision

end CoveredParents

namespace Mesh

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment polynomial ambient start finish}

/-- Combine the primitive covering depth and prepared-safety depth into one retained mesh.

Their natural maximum pays both requirements. Each original depth is computed once, and the returned cache retains its
original power-of-two edge count and covering certificate. -/
@[expose] def prepared (bounds : UniformPrimitiveNeighborhoods.Bounds segment) : UniformPrimitiveMesh.Mesh bounds :=
  let cover := Mesh.build bounds
  let safe := Subdivision.sufficientDyadicDepth segment
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint bounds.rootDiameter
  let depth := max cover.depth safe
  { depth := depth
    edgeCount := 2 ^ depth
    edgeCount_eq := rfl
    small := (quarterRadius_antitone (Data.Gaussian.Basic.Canonical.normSq_nonneg (finish - start))
      (Data.Nat.Order.le_max_left _ _)).trans_lt cover.small }

/-- The computed mesh depth pays the retained prepared-continuation safety requirement.

The direct natural maximum certificate bounds the cached safety depth by the same displayed mesh depth without replaying
either preparation. -/
theorem prepared_depth_sufficient (bounds : UniformPrimitiveNeighborhoods.Bounds segment) :
    Subdivision.sufficientDyadicDepth segment UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint
      bounds.rootDiameter ≤
      (Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Mesh.prepared bounds).depth :=
        Data.Nat.Order.le_max_right _ _

/-- Every dyadic edge of a strictly ordered parameter interval remains strictly ordered.

The original list membership selects a retained half at each subdivision step. Its midpoint inequality preserves the
exact original endpoint order through that same tail. -/
private theorem dyadicEdges_strict (depth : Nat) (left right : PreparedSubdivisionModelCore.Endpoint)
    (ordered : left.parameter < right.parameter)
    {edge : Subdivision.ParameterEdge}
    (member : edge ∈ Subdivision.dyadicEdges depth left right) :
    edge.left.parameter < edge.right.parameter := by
  induction depth generalizing left right with
  | zero =>
      have same := Membership.mem_singleton.mp member
      subst edge
      exact ordered
  | succ depth ih =>
      rcases Membership.mem_append.mp member with member | member
      · exact ih _ _ (ClearSheetContinuation.left_lt_midpoint ordered) member
      · exact ih _ _ (ClearSheetContinuation.midpoint_lt_right ordered) member

/-- Every edge in a uniform primitive mesh has strictly increasing endpoint parameters. -/
theorem edge_strict {bounds : UniformPrimitiveNeighborhoods.Bounds segment} (mesh : UniformPrimitiveMesh.Mesh bounds)
    {edge : Subdivision.ParameterEdge} (member : edge ∈ mesh.edges) :
    edge.left.parameter < edge.right.parameter :=
  Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Mesh.dyadicEdges_strict mesh.depth
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint (by decide) member

end Mesh

set_option genInjectivity false in
/-- A prepared segment with primitive coverage for its persisted centered-edge list.

The mesh, dependent subdivision and center cache remain linked by their exact stored readback equations. Each retained
parent has its own covering patch and endpoint witness. -/
structure CoveredSegment {ambient : Rational.Box} {start finish : Data.Gaussian.Basic.Canonical}
    (segment : ClearPath.ClearSegment curve.polynomial ambient start finish) (within : segment.WithinAmbient)
    (owner : Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Owner (curve.polynomial.eval
      (segment.pointAt UniformPrimitiveMesh.firstEndpoint.parameter)))
    (differential : Differentials.Basic.Differential genus) (sheet : Fin 2) (count : Nat) where
  /-- The retained primitive-neighborhood bounds for the original segment. -/ bounds :
    UniformPrimitiveNeighborhoods.Bounds segment
  /-- The finite mesh certified against those exact retained bounds. -/ mesh : UniformPrimitiveMesh.Mesh bounds
  /-- The actual prepared dependent subdivision beginning at the original square-root owner. -/ subdivision :
    PreparedSheetContinuation.Subdivision segment within UniformPrimitiveMesh.firstEndpoint owner
  /-- The subdivision parameter edges are exactly the retained mesh edges. -/ mesh_eq : subdivision.parameterEdges =
    mesh.edges
  /-- The prepared subdivision finishes at the original terminal parameter. -/ endpoint_eq : subdivision.endpoint =
    UniformPrimitiveMesh.lastEndpoint
  /-- The persisted differential center states indexed by the exact prepared subdivision. -/ centers :
    PreparedSubdivisionModelCore.CenterStates curve differential sheet subdivision
  /-- The cached ordinary list of prepared centered edges. -/ parents : List (PreparedSubdivisionModelCore.CenteredEdge
    curve differential)
  /-- The cached parent list equals extraction from the retained subdivision and center states. -/ parents_eq : parents
    = PreparedSubdivisionModelCore.centeredEdges curve differential sheet subdivision centers
  /-- Each cached parent has its corresponding primitive patch and endpoint coverage. -/ covered :
    Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents count parents

constructive_injectivity CoveredSegment

namespace CoveredSegment

variable {ambient : Purelib.Geometry.Rational.Box} {start finish :
  Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish} {within :
    segment.WithinAmbient}
  {owner : Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Owner (curve.polynomial.eval
    (segment.pointAt Purelib.Riemann.Meshes.UniformPrimitiveMesh.firstEndpoint.parameter))} {sheet : Fin 2}

/-- Retain a covered segment from supplied subdivision and center caches.

The supplied mesh and endpoint equations identify the exact original geometry. The constructor extracts its ordered
parents once and associates each with its covering patch. -/
@[expose] def ofSubdivision (bounds : UniformPrimitiveNeighborhoods.Bounds segment) (mesh : UniformPrimitiveMesh.Mesh
  bounds)
    (subdivision : PreparedSheetContinuation.Subdivision segment within UniformPrimitiveMesh.firstEndpoint owner)
    (meshEq : subdivision.parameterEdges = mesh.edges) (endpointEq : subdivision.endpoint =
      UniformPrimitiveMesh.lastEndpoint)
    (centers : PreparedSubdivisionModelCore.CenterStates curve differential sheet subdivision) (count : Nat) :
    Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment segment within owner differential
      sheet count where
  bounds := bounds
  mesh := mesh
  subdivision := subdivision
  mesh_eq := meshEq
  endpoint_eq := endpointEq
  centers := centers
  parents := PreparedSubdivisionModelCore.centeredEdges curve differential sheet subdivision centers
  parents_eq := rfl
  covered := Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents.ofSubdivision bounds mesh
    sheet count subdivision centers (by
    intro edge member
    rw [meshEq] at member
    exact member)

/-- Execute a sufficiently fine safe mesh with persisted center states.

The cached primitive bounds determine a covering depth and safety depth. The original checked dyadic procedure and
canonical centers then provide the retained subdivision, endpoint and complete parent cover. -/
@[expose] def ofBounds (bounds : UniformPrimitiveNeighborhoods.Bounds segment) (within : segment.WithinAmbient)
    (owner : Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Owner (curve.polynomial.eval
      (segment.pointAt UniformPrimitiveMesh.firstEndpoint.parameter)))
    (differential : Differentials.Basic.Differential genus) (sheet : Fin 2) (count : Nat) :
    Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment segment within owner differential
      sheet count := by
  let mesh := Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Mesh.prepared bounds
  have safe := Subdivision.dyadicMeshSafe_of_sufficientDepth_le segment
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint owner mesh.depth bounds.rootDiameter
      bounds.rootDiameter_positive
    (by decide) (Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Mesh.prepared_depth_sufficient bounds)
  let subdivision := Subdivision.checkedDyadic segment within UniformPrimitiveMesh.firstEndpoint
    UniformPrimitiveMesh.lastEndpoint owner
    mesh.depth bounds.rootDiameter bounds.rootDiameter_positive safe
  have success := Subdivision.tryDyadic_eq_some_checkedDyadic segment within
    UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint owner mesh.depth bounds.rootDiameter
      bounds.rootDiameter_positive safe
  have meshEq : subdivision.parameterEdges = mesh.edges :=
    Subdivision.tryDyadic_parameterEdges segment within UniformPrimitiveMesh.firstEndpoint
      UniformPrimitiveMesh.lastEndpoint owner
      mesh.depth bounds.rootDiameter bounds.rootDiameter_positive success
  have endpointEq := Subdivision.tryDyadic_endpoint segment within UniformPrimitiveMesh.firstEndpoint
    UniformPrimitiveMesh.lastEndpoint owner
    mesh.depth bounds.rootDiameter bounds.rootDiameter_positive success
  let centers := PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet subdivision
  exact Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment.ofSubdivision bounds mesh
    subdivision meshEq endpointEq centers count

/-- Construct a covered prepared segment from its clear geometry and retained starting owner.

Primitive bounds, a sufficient safe mesh and its persisted center states are computed together, and the resulting
ordinary parent list remains tied to that exact dependent subdivision. -/
@[expose] def build (segment : ClearPath.ClearSegment curve.polynomial ambient start finish) (within :
  segment.WithinAmbient)
    (owner : Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Owner (curve.polynomial.eval
      (segment.pointAt UniformPrimitiveMesh.firstEndpoint.parameter)))
    (differential : Differentials.Basic.Differential genus) (sheet : Fin 2) (count : Nat) :
    Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment segment within owner differential
      sheet count :=
  Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment.ofBounds
    (UniformPrimitiveNeighborhoods.Bounds.build segment) within owner differential sheet count

/-- The cached ordinary parent list has exactly the computed mesh size. -/
theorem parents_length (covered : Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment
  segment within owner differential sheet count) :
    covered.parents.length = covered.mesh.edgeCount := by
  have geometry : covered.parents.map CenteredEdge.parameterEdge = covered.mesh.edges := by
    rw [covered.parents_eq, PreparedSubdivisionModelCore.centeredEdges_parameterEdges, covered.mesh_eq]
  have sizes := congrArg List.length geometry
  rw [Map.length_map, covered.mesh.edges_length] at sizes
  exact sizes

/-- Every retained parent in a covered segment has strictly increasing parameter endpoints. -/
theorem parent_proper (covered : Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment segment
  within owner differential sheet count)
    {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential} (member : parent ∈ covered.parents) :
    parent.edge.left.parameter < parent.edge.request.endpoint.parameter := by
  have geometry : covered.parents.map CenteredEdge.parameterEdge = covered.mesh.edges := by
    rw [covered.parents_eq, PreparedSubdivisionModelCore.centeredEdges_parameterEdges, covered.mesh_eq]
  have edgeMember : parent.parameterEdge ∈ covered.mesh.edges := by
    rw [← geometry]
    exact Map.mem_map.mpr ⟨parent, member, rfl⟩
  exact Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Mesh.edge_strict covered.mesh edgeMember

/-- Pointwise strictness of a finite parent list gives its dependent all-parents-proper certificate. -/
private theorem allParentsProper_of_members (parents : List (PreparedSubdivisionModelCore.CenteredEdge curve
  differential))
    (proper : ∀ parent ∈ parents, parent.edge.left.parameter < parent.edge.request.endpoint.parameter) :
    PreparedDyadicRefinements.AllParentsProper parents := by
  induction parents with
  | nil => trivial
  | cons parent remaining ih =>
      exact ⟨proper parent (List.mem_cons_self ..), ih (fun child member => proper child (List.mem_cons_of_mem _
        member))⟩

/-- The complete cached parent list of a covered segment is proper. -/
theorem parents_proper (covered : Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment
  segment within owner differential sheet count) :
    PreparedDyadicRefinements.AllParentsProper covered.parents :=
  Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment.allParentsProper_of_members
    covered.parents (fun _ member => covered.parent_proper member)

/-- The covered samples are an actual connected prepared path with the original lifted endpoints, not merely an
unordered collection of cells. -/
@[expose] def chain (covered : Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment segment
  within owner differential sheet count) :
    PreparedDirectDyadicRefinements.CenteredPathChain covered.parents
      (start := { coordinate := start, sheet := sheet })
      (finish := { coordinate := finish, sheet := sheet }) := by
  rw [covered.parents_eq]
  let original := CenteredPathChain.ofCenteredSubdivision
    curve differential sheet covered.subdivision covered.centers
  have first : segment.pointAt UniformPrimitiveMesh.firstEndpoint.parameter = start := segment.pointAt_zero
  have last : segment.pointAt covered.subdivision.endpoint.parameter = finish := by
    rw [covered.endpoint_eq]
    exact segment.pointAt_one
  exact (original.castStart (congrArg
    (fun coordinate : Data.Gaussian.Basic.Canonical => ({ coordinate := coordinate, sheet := sheet } :
      Lifted.Basic.LiftedPoint 2)) first)).castFinish
    (congrArg (fun coordinate : Data.Gaussian.Basic.Canonical => ({ coordinate := coordinate, sheet := sheet } :
      Lifted.Basic.LiftedPoint 2)) last)

/-- Enter the existing executable refinement pipeline with constructed nondegeneracy and connectivity, while retaining
the separately cached cover. -/
@[expose] def refinementState (covered : Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredSegment
  segment within owner differential sheet count) :
    PreparedDirectDyadicRefinements.DirectRefinementState curve differential :=
  covered.chain.toDirectRefinementState covered.parents_proper

end CoveredSegment

end Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh

end
