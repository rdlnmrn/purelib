module
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPathDecomposition
public import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Segment
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Paths.PreparedClearPathModels

public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Boundary geometry of the actual retained period-segment parents

Read the original covered segment and cached parent list. The comparison box
may differ from the clearance ambient, so a grid segment can belong to a
smaller Newton-band side without replacing its clearance or root preparation.
-/

namespace Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide ParentOnBoundary)
open Purelib.Riemann.Paths.PreparedClearPathModels (Owner)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
    {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
  {owner : Owner (curve.polynomial.eval start)} {piece : CoveredSegment segment owner} {sheet : Fin 2}

section
open Purelib.Riemann
/-- The retained segment parent cache has exactly two to the original mesh depth entries. -/
theorem segment_parentCount (cache : ParentCache piece.path differential sheet) :
    cache.parents.length = 2 ^ piece.mesh.depth := by
  rw [cache.parents_eq, Paths.PreparedSegmentParentBanks.CoveredSegment.path_parentCount piece differential sheet,
    piece.mesh.edgeCount_eq]

/-- Each cached parent's endpoints are the original segment points at its retained parameter bounds. -/
theorem segment_parent_endpoints (cache : ParentCache piece.path differential sheet)
    {parent : CenteredEdge curve differential} (member : parent ∈ cache.parents) :
    parent.edge.point 0 = segment.pointAt parent.parameterEdge.left.parameter ∧
      parent.edge.point 1 = segment.pointAt parent.parameterEdge.right.parameter := by
  rw [cache.parents_eq, Paths.PreparedSegmentParentBanks.CoveredSegment.path_parents piece differential sheet] at member
  exact Paths.UniformPreparedBoundarySegments.centeredEdges_source_endpoints sheet piece.traced.prepared.subdivision
    (Integration.PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet
      piece.traced.prepared.subdivision) parent member

end

open Purelib.Riemann in
open Purelib.Data in
/-- Every cached parent retains an actual edge of the original segment mesh. -/
theorem segment_parameterEdge (cache : ParentCache piece.path differential sheet)
    {parent : CenteredEdge curve differential} (member : parent ∈ cache.parents) :
    parent.parameterEdge ∈ piece.mesh.edges := by
  have geometry : cache.parents.map CenteredEdge.parameterEdge = piece.mesh.edges := by
    rw [cache.parents_eq, Paths.PreparedSegmentParentBanks.CoveredSegment.path_parents piece differential sheet,
      Paths.PreparedClearPathModels.CompleteSegment.centeredEdges_parameterEdges, piece.mesh_eq]
  rw [← geometry]
  exact List.Map.mem_map.mpr ⟨parent, member, rfl⟩

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Each retained parent has the exact dyadic share of the original segment's squared displacement. -/
theorem segment_parent_movement (cache : ParentCache piece.path differential sheet)
    {parent : CenteredEdge curve differential} (member : parent ∈ cache.parents) :
    movement parent = Rational.Geometric.Basic.quarterRadius (Data.Gaussian.Norm.Basic.normSq (finish - start))
      piece.mesh.depth := by
  have endpoints := segment_parent_endpoints cache member
  have source : movement parent =
      Data.Gaussian.Norm.Basic.normSq (segment.pointAt parent.parameterEdge.right.parameter - segment.pointAt
        parent.parameterEdge.left.parameter) := by
    rw [← endpoints.1, ← endpoints.2, parent.edge.point_zero, parent.edge.point_one]
    rfl
  rw [source, segment.normSq_pointAt_sub_pointAt,
    Meshes.UniformPrimitiveMesh.dyadicEdges_width piece.mesh.depth
      Meshes.UniformPrimitiveMesh.firstEndpoint Meshes.UniformPrimitiveMesh.lastEndpoint _ (segment_parameterEdge cache
        member)]
  change Rational.Geometric.Basic.quarterRadius ((1 - 0 : Rat.Fraction.Rational) ^ 2) piece.mesh.depth *
    Data.Gaussian.Norm.Basic.normSq (finish - start) = _
  rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
  ring1

open Purelib.Riemann in
open Purelib.Geometry in
/-- Original endpoint geometry certifies every retained parent on the same box side.

The comparison box may differ from the clearance ambient, and the parent cache may be sliced from an existing
whole-period preparation. -/
theorem segment_parent_boundary (cache : ParentCache piece.path differential sheet) {box : Rational.Box}
    (first : box.Contains start) (last : box.Contains finish) (side : SameSide box start finish)
    {parent : CenteredEdge curve differential} (member : parent ∈ cache.parents) : ParentOnBoundary parent box := by
  have endpoints := segment_parent_endpoints cache member
  refine ⟨?_, ?_, ?_⟩
  · rw [endpoints.1, Paths.PreparedPathWinding.ClearSegment.pointAt_eq_line segment]
    exact Rational.Box.contains_line first last parent.parameterEdge.left.inside
  · rw [endpoints.2, Paths.PreparedPathWinding.ClearSegment.pointAt_eq_line segment]
    exact Rational.Box.contains_line first last parent.parameterEdge.right.inside
  · rw [endpoints.1, endpoints.2]
    exact side.pointAt segment _ _

end Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
