module
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedCoveredParentLists
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Riemann.Paths.PreparedPathParentCaches
public import Purelib.Riemann.Paths.PreparedPathDifferentialRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Field
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Approximation.Gaussian.Name.Basic

/-! Change the differential on a retained parent cache without preparing
another path or acquiring another primitive cover. -/
namespace Purelib.Riemann.Integration.PreparedParentCacheRecasting
public section
open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.ParentCache (parents)
variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient :
  Purelib.Geometry.Rational.Box}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
    curve.polynomial ambient start finish}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {prepared : Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath path owner}
    {source : Differential genus} {sheet : Fin 2}

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- Recast the differential of the actual retained parent cache.

The original centered parent list is mapped without changing its geometry or sheet; its exact prepared-path identity and
primitive-cover evidence are transported together. -/
@[expose]
def recast (cache : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared source sheet) (target :
  Differentials.Basic.Differential genus) : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared target
  sheet where
  parents := cache.parents.map (recastCenteredEdge target)
  parents_eq := (congrArg (List.map (recastCenteredEdge target)) cache.parents_eq).trans
    (PreparedPathDifferentialRecasting.ofPreparedPath_recast curve source target sheet prepared.traced.prepared)
  covered := PreparedCoveredParentLists.CoveredParents.recast target cache.covered

open Purelib.Curves.Hyperelliptic
open Purelib.Riemann.Paths
/-- The recast cache contains exactly the original parent list mapped by differential recasting. -/
theorem recast_parents (cache : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared source sheet)
  (target : Differentials.Basic.Differential genus) :
    (recast cache target).parents = cache.parents.map (recastCenteredEdge target) := rfl

/-- Recasting preserves the original endpoint coordinates, sheet and root-owner name of every cached parent.

The two maps apply to the same retained entries in their original order; their composite changes neither the cached list
nor its input owners. -/
theorem recast_geometry (cache : PreparedPathParentCaches.PreparedClearPathModels.ParentCache prepared source sheet)
  (target : Differentials.Basic.Differential genus) :
    (recast cache target).parents.map (fun parent =>
      (parent.edge.point 0, parent.edge.point 1, parent.edge.sheet, OwnerTraceReadings.ownerName parent.edge.owner)) =
    cache.parents.map (fun parent =>
      (parent.edge.point 0, parent.edge.point 1, parent.edge.sheet, OwnerTraceReadings.ownerName parent.edge.owner)) :=
        by
  rw [recast_parents, Map.map_map]
  rfl

end
end Purelib.Riemann.Integration.PreparedParentCacheRecasting
