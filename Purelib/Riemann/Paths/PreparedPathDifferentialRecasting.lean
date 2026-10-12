module

import Purelib.Data.List.Map
import Purelib.Riemann.Branches.PreparedSheetContinuation
public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

public section

/-!
# Differential changes on a retained canonical prepared path

The actual subdivision, owners, and chart labels are unchanged. This equality
is specific to the canonical centered extraction of a prepared path: an
arbitrary persisted center must not be identified with its recentering.
-/

namespace Purelib.Riemann.Paths.PreparedPathDifferentialRecasting

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Riemann.Branches
open Purelib.Riemann.Paths
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
  (centeredEdges)
open Purelib.Riemann.Integration.PreparedSubdivisionAutomaticModels
  (canonicalCenterStates)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
  (ofPreparedPath dataOfCompleteSegment_parents)

open Purelib.Curves
open Purelib.Polynomial
open Purelib.Geometry
/-- Changing the differential commutes with canonical centered extraction from one retained subdivision.

The chart sheet, source owner and actual subdivision remain fixed; the statement concerns canonical centers. -/
private theorem canonicalCenteredEdges_recast {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source target :
      Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {left : Endpoint}
    {owner : Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
    (sheet : Fin 2) :
    (subdivision : PreparedSheetContinuation.Subdivision segment within left owner) →
      (centeredEdges curve source sheet subdivision (canonicalCenterStates curve source sheet subdivision)).map
        (recastCenteredEdge target) =
      centeredEdges curve target sheet subdivision (canonicalCenterStates curve target sheet subdivision)
  | .stop _ _ => rfl
  | .next _ _ _ _ _ _ remaining => by
      simp only [centeredEdges, canonicalCenterStates, List.map_cons]
      exact congrArg (List.cons _) (canonicalCenteredEdges_recast curve source target sheet remaining)

/-- Recasting the canonical centers of a complete retained segment equals extraction for the target differential. -/
private theorem completeSegment_centeredEdges_recast {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source target :
      Hyperelliptic.Differentials.Basic.Differential genus)
    {ambient : Rational.Box} {start finish : Gaussian}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish}
    {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)}
    (sheet : Fin 2) (prepared : PreparedClearPathModels.CompleteSegment segment within owner) :
    (prepared.centeredEdges curve source sheet).map (recastCenteredEdge target) =
      prepared.centeredEdges curve target sheet :=
  canonicalCenteredEdges_recast curve source target sheet prepared.subdivision

/-- Every differential uses the same retained prepared path subdivision and parent order.

Recasting the source differential's canonical centered parents equals the target differential's extraction, without
preparing a second path. -/
theorem ofPreparedPath_recast {genus : Nat}
    (curve : Hyperelliptic.Basic.HyperellipticCurve genus) (source target :
      Hyperelliptic.Differentials.Basic.Differential genus) (sheet : Fin 2) :
    ∀ {ambient : Rational.Box} {start finish : Gaussian}
      {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
      {owner : Owner (curve.polynomial.eval start)}
      (prepared : PreparedClearPathModels.PreparedPath path owner),
      (ofPreparedPath curve source sheet prepared).parents.map (recastCenteredEdge target) =
        (ofPreparedPath curve target sheet prepared).parents := by
  intro ambient start finish path owner prepared
  induction prepared with
  | nil point owner => rfl
  | cons head tail owner headWithin preparedHead preparedTail ih =>
      simp only [ofPreparedPath, Map.map_append]
      rw [dataOfCompleteSegment_parents, dataOfCompleteSegment_parents,
        completeSegment_centeredEdges_recast curve source target sheet preparedHead, ih]

end Purelib.Riemann.Paths.PreparedPathDifferentialRecasting
