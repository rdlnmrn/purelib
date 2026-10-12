module
import Purelib.Data.List.Membership
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore

public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
public import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Tactic.Ring

/-!
# Geometry of cached complete boundary subdivisions

Read boundary locations and exact dyadic movements from the actual retained
subdivision and mesh. No center or root preparation is replayed, and generated
subdivisions enter through the existing semantic covered-segment constructor.
-/

public section

namespace Purelib.Riemann.Paths.UniformPreparedBoundarySegments

open Purelib.Data.Gaussian
open Purelib.Curves.Hyperelliptic.Integration
open Purelib.Riemann.Branches
open Purelib.Polynomial
open Purelib.Data.List
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Riemann.Integration
open Purelib.Riemann.Meshes

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges
  edgeOfStep_point_zero edgeOfStep_point_one centeredEdges_parameterEdges)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint)
open Purelib.Riemann.Meshes.UniformPrimitiveMesh (firstEndpoint lastEndpoint)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredSegment Owner)
/-- The exact rational Gaussian carrier. -/
private abbrev Gaussian := Purelib.Data.Gaussian.Basic.Canonical
/-- The original rational Gaussian box carrier. -/
private abbrev Box := Purelib.Geometry.Rational.Box
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide ParentOnBoundary)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish} {within :
    segment.WithinAmbient}

/-- Every centered subdivision edge has its source segment's retained parameter endpoints.

Membership in the original dependent spine selects the head or unchanged tail. The head's scalar endpoint laws transport
the actual source geometry without changing its parent identity. -/
theorem centeredEdges_source_endpoints (sheet : Fin 2)
    {left : Endpoint} {owner : Observation.UniformPreparedMesh.Owner (curve.polynomial.eval (segment.pointAt
      left.parameter))} :
    (subdivision : PreparedSheetContinuation.Subdivision segment within left owner) →
    (centers : CenterStates curve differential sheet subdivision) →
    ∀ parent ∈ centeredEdges curve differential sheet subdivision centers,
      parent.edge.point 0 = segment.pointAt parent.parameterEdge.left.parameter ∧
      parent.edge.point 1 = segment.pointAt parent.parameterEdge.right.parameter
  | .stop _ _, _, _, member => by cases member
  | .next left owner request cached ordered small remaining, centers, parent, member => by
      rcases Membership.mem_cons.mp member with rfl | member
      · exact ⟨edgeOfStep_point_zero curve differential segment within left owner request cached ordered small sheet,
          edgeOfStep_point_one curve differential segment within left owner request cached ordered small sheet⟩
      · exact centeredEdges_source_endpoints sheet remaining centers.2 parent member
termination_by structural subdivision => subdivision

namespace CoveredSegment

variable {owner : Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Owner (curve.polynomial.eval
  (segment.pointAt firstEndpoint.parameter))} {sheet : Fin 2}

/-- Transport the original subdivision terminal owner to the complete segment's exact finish-point parameter. -/
@[expose] def finishOwner (covered : Observation.UniformPreparedMesh.CoveredSegment segment within owner differential
  sheet count) :
    Observation.UniformPreparedMesh.Owner (curve.polynomial.eval finish) := by
  simpa only [covered.endpoint_eq, lastEndpoint, Geometry.ClearPath.ClearSegment.pointAt_one] using
    covered.subdivision.terminalOwner

/-- The retained finish owner is heterogeneously equal to the original subdivision terminal owner. -/
theorem finishOwner_heq_terminalOwner (covered : Observation.UniformPreparedMesh.CoveredSegment segment within owner
  differential sheet count) :
    HEq (finishOwner covered) covered.subdivision.terminalOwner := by
  unfold finishOwner
  exact cast_heq _ _

/-- Each original covered parent has the exact source-segment points at its retained parameter endpoints. -/
theorem parent_endpoints (covered : Observation.UniformPreparedMesh.CoveredSegment segment within owner differential
  sheet count)
    {parent : CenteredEdge curve differential} (member : parent ∈ covered.parents) :
    parent.edge.point 0 = segment.pointAt parent.parameterEdge.left.parameter ∧
    parent.edge.point 1 = segment.pointAt parent.parameterEdge.right.parameter := by
  rw [covered.parents_eq] at member
  exact centeredEdges_source_endpoints sheet covered.subdivision covered.centers parent member

/-- Every retained covered parent parameter edge belongs to the original uniform mesh. -/
theorem parent_parameterEdge (covered : Observation.UniformPreparedMesh.CoveredSegment segment within owner differential
  sheet count)
    {parent : CenteredEdge curve differential} (member : parent ∈ covered.parents) :
    parent.parameterEdge ∈ covered.mesh.edges := by
  have geometry : covered.parents.map CenteredEdge.parameterEdge = covered.mesh.edges := by
    rw [covered.parents_eq, centeredEdges_parameterEdges, covered.mesh_eq]
  rw [← geometry]
  exact Map.mem_map.mpr ⟨parent, member, rfl⟩

/-- The original covered parent's movement equals the exact quarter-radius of the full segment displacement at its mesh
depth.

The original parameter-edge membership supplies the exact dyadic width, while endpoint equations preserve the source
segment geometry. -/
theorem parent_movement (covered : Observation.UniformPreparedMesh.CoveredSegment segment within owner differential
  sheet count)
    {parent : CenteredEdge curve differential} (member : parent ∈ covered.parents) :
    PreparedDirectDyadicRefinements.geometricMovement parent.edge.segment parent.edge.left.parameter
      parent.edge.request.endpoint.parameter = Geometric.Basic.quarterRadius (normSq (finish - start))
        covered.mesh.depth := by
  have endpoints := parent_endpoints covered member
  have sourceMovement :
      PreparedDirectDyadicRefinements.geometricMovement parent.edge.segment parent.edge.left.parameter
        parent.edge.request.endpoint.parameter =
      normSq (segment.pointAt parent.parameterEdge.right.parameter - segment.pointAt
        parent.parameterEdge.left.parameter) := by
    rw [← endpoints.1, ← endpoints.2, parent.edge.point_zero, parent.edge.point_one]
    exact Norm.Basic.normSq_eq_canonical _
  have movementFormula := segment.normSq_pointAt_sub_pointAt
    parent.parameterEdge.right.parameter parent.parameterEdge.left.parameter
  simp only [Norm.Basic.normSq_eq_canonical] at movementFormula
  rw [sourceMovement, movementFormula,
    UniformPrimitiveMesh.dyadicEdges_width covered.mesh.depth firstEndpoint lastEndpoint _ (parent_parameterEdge covered
      member)]
  change Geometric.Basic.quarterRadius ((1 - 0 : Fraction.Rational) ^ 2) covered.mesh.depth * normSq (finish - start) =
    _
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

/-- An original covered parent lies on the retained ambient boundary when its source segment shares one box side.

Both endpoint containments and their exact source-coordinate equations are retained in the boundary certificate. -/
theorem parent_boundary (covered : Observation.UniformPreparedMesh.CoveredSegment segment within owner differential
  sheet count)
    (side : SameSide ambient start finish)
    {parent : CenteredEdge curve differential} (member : parent ∈ covered.parents) : ParentOnBoundary parent ambient :=
      by
  have endpoints := parent_endpoints covered member
  refine ⟨?_, ?_, ?_⟩
  · rw [endpoints.1]
    exact segment.pointAt_contains within _ parent.parameterEdge.left.inside
  · rw [endpoints.2]
    exact segment.pointAt_contains within _ parent.parameterEdge.right.inside
  · rw [endpoints.1, endpoints.2]
    exact side.pointAt segment _ _

end CoveredSegment

end Purelib.Riemann.Paths.UniformPreparedBoundarySegments

end
