module
import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.UniformPreparedBoundarySegments

import Purelib.Riemann.Paths.PreparedSegmentBoundaryGeometry
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
public import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels

/-!
# Ambient containment of every cached path parent

The proof follows the original prepared segment spine. It applies to complete
paths, including every corner of a boundary traversal, while downstream code
continues to consume the retained parent list and primitive cover.
-/

namespace Purelib.Riemann.Paths.PreparedPathParentContainment
public section
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)

open Purelib.Riemann in
open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Every parent from the original prepared path has both endpoints in the ambient box.

Follow the prepared segment spine and its actual subdivision parameters; complete-segment provenance identifies each
parent's two source locations. -/
private theorem prepared_parent_endpoints (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (differential :
  Hyperelliptic.Differentials.Basic.Differential genus)
    (sheet : Fin 2) {ambient : Rational.Box} :
    ∀ {first last : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first last}
      {owner : Owner (curve.polynomial.eval first)} (prepared : PreparedPath path owner)
      (parent : CenteredEdge curve differential), parent ∈ (CenteredPathChain.ofPreparedPath curve differential sheet
        prepared).parents →
      ambient.Contains (parent.edge.point 0) ∧ ambient.Contains (parent.edge.point 1)
  | _, _, _, _, .nil _ _, _, member => by cases member
  | _, _, _, _, .cons head tail owner within first rest, parent, member => by
      change parent ∈ (CenteredPathChain.dataOfCompleteSegment curve differential sheet first).parents ++
        (CenteredPathChain.ofPreparedPath curve differential sheet rest).parents at member
      cases Membership.mem_append.mp member with
      | inl member =>
          rw [CenteredPathChain.dataOfCompleteSegment_parents] at member
          have endpoints := Paths.UniformPreparedBoundarySegments.centeredEdges_source_endpoints sheet first.subdivision
            (Integration.PreparedSubdivisionAutomaticModels.canonicalCenterStates curve differential sheet
              first.subdivision) parent member
          rw [endpoints.1, endpoints.2]
          exact ⟨head.pointAt_contains within _ parent.parameterEdge.left.inside,
            head.pointAt_contains within _ parent.parameterEdge.right.inside⟩
      | inr member => exact prepared_parent_endpoints curve differential sheet rest parent member

namespace ParentCache

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Geometry in
/-- Both endpoints of every retained whole-path parent lie in the original ambient box.

The cache's exact parent-list equality transports the prepared-path containment proof without rebuilding its parents or
primitive cover. -/
theorem endpoints_within {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
    {ambient : Rational.Box} {first last : Gaussian.Basic.Canonical} {path :
      Polynomial.Geometry.ClearPath curve.polynomial ambient first last}
    {owner : Owner (curve.polynomial.eval first)} {prepared : CoveredTracedPath path owner} {sheet : Fin 2}
    (cache : ParentCache prepared differential sheet) (parent : CenteredEdge curve differential) (member : parent ∈
      cache.parents) :
    ambient.Contains (parent.edge.point 0) ∧ ambient.Contains (parent.edge.point 1) := by
  rw [cache.parents_eq] at member
  exact prepared_parent_endpoints curve differential sheet prepared.traced.prepared parent member

end ParentCache
end
end Purelib.Riemann.Paths.PreparedPathParentContainment
