module
import Purelib.Data.List.Map
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
public import Purelib.Riemann.Paths.PreparedNestedDyadicPaths
public import Purelib.Riemann.Topology.PreparedRecastRootChains
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore

public section

/-! Differential recasting preserves each retained ancestor's dyadic path. -/
namespace Purelib.Riemann.Paths.PreparedRecastDyadicPaths

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Paths.PreparedNestedDyadicPaths (DyadicPaths)
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the original dyadic paths. -/
private abbrev Gaussian := Basic.Canonical

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Integration.Path.Dyadic in
/-- Differential recasting preserves the original ordered geometric dyadic increments. -/
private theorem recast_increments (target : Differentials.Basic.Differential genus) (children : List (CenteredEdge curve
  source))
    (value : Basic.Canonical → Basic.Canonical) (fine : Nat) :
    ((children.map (recastCenteredEdge target)).map (fun child =>
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (child.edge.point parameter)) fine 0 1)).flatten =
    (children.map (fun child => DyadicPrimitivePaths.dyadicIncrements (fun parameter => value (child.edge.point
      parameter)) fine 0 1)).flatten := by
  induction children with
  | nil => rfl
  | cons child children ih => exact congrArg (List.append _) ih

/-- Transport original dyadic path evidence along the exact child-list equality. -/
private theorem paths_mpr {parents first second : List (CenteredEdge curve source)}
    {depth : Nat} (equal : first = second) (refinement : RootSubedgeRefinement parents second)
    (paths : DyadicPaths depth refinement) :
    DyadicPaths depth (Eq.mpr (congrArg (RootSubedgeRefinement parents) equal) refinement) := by
  cases equal
  exact paths

open Purelib.Curves.Hyperelliptic in
open Purelib.Riemann.Topology in
/-- Recast the differential while retaining the original dyadic path identities and depth.

The original parent/child geometry is unchanged; the exact mapped-list concatenation transports each retained
root-subedge block witness. -/
theorem DyadicPaths.recast {parents children : List (CenteredEdge curve source)}
    {refinement : RootSubedgeRefinement parents children} {depth : Nat}
    (paths : DyadicPaths depth refinement) (target : Differentials.Basic.Differential genus) :
    DyadicPaths depth
      (PreparedRecastRootChains.PreparedRefinementRootEndpoints.RootSubedgeRefinement.recast
        target refinement) := by
  induction refinement with
  | nil => trivial
  | @cons parent parents block children chain roots remaining ih =>
      unfold PreparedRecastRootChains.PreparedRefinementRootEndpoints.RootSubedgeRefinement.recast
      apply paths_mpr (Purelib.Data.List.Map.map_append (function := recastCenteredEdge target) (left := block) (right
        := children))
      constructor
      · intro value fine
        rw [recast_increments]
        exact paths.1 value fine
      · exact ih paths.2

end Purelib.Riemann.Paths.PreparedRecastDyadicPaths
