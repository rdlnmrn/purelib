module
import Purelib.Data.List.Membership
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.RootContinuation.PreparedNestedRootRefinements
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Topology.SquareRootContinuationChain

public import Purelib.Riemann.Paths.PreparedSegmentSources
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements
import Purelib.Riemann.Branches.PreparedSheetContinuation

public section

/-!
# Original segment grouping of prepared paths

Each block retains its actual endpoint chain and ordered locations on one
original segment. The grouping follows cached preparation and survives every
directed root refinement, including differential recasting.
-/

namespace Purelib.Riemann.Paths.PreparedPathSources

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge CenterStates centeredEdges)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain CenteredPathChain)
open Purelib.Riemann.RootContinuation.PreparedDirectedRootRefinements (DirectedRefinement)
open Purelib.Riemann.Paths.PreparedSegmentSources (SegmentSource)
open Purelib.Riemann.Branches.PreparedSheetContinuation (Endpoint Subdivision)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)

variable {genus : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box}

open Purelib.Data in
open Purelib.Polynomial in
/-- An ordered grouping of prepared edges by their original clear-path segments.

Each original segment retains its actual connected lifted block and source-location certificates; the dependent path
index preserves the complete endpoint chain. -/
inductive PathSources (sheet : Fin 2) :
    {start finish : Gaussian.Basic.Canonical} → Polynomial.Geometry.ClearPath curve.polynomial ambient start finish →
      List (CenteredEdge curve source) → Prop
  /-- The empty prepared grouping at one retained endpoint. -/ | nil (point : Gaussian.Basic.Canonical) : PathSources
    sheet (.nil point) []
  /-- A connected source-certified block for the first original segment followed by its retained path tail. -/ | cons
    {start middle finish : Gaussian.Basic.Canonical}
      {segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start middle}
      {tail : Polynomial.Geometry.ClearPath curve.polynomial ambient middle finish}
      {block parents : List (CenteredEdge curve source)}
      (chain : DirectPathChain block (start := { coordinate := start, sheet := sheet })
        (finish := { coordinate := middle, sheet := sheet }))
      (sources : ∀ parent ∈ block, SegmentSource segment parent)
      (remaining : PathSources sheet tail parents) :
      PathSources sheet (.cons segment tail) (block ++ parents)

namespace PathSources

section
open Purelib.Curves.Hyperelliptic.Differentials
open Purelib.Data
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.Riemann.Integration in
/-- Every centered edge in an actual cached subdivision belongs to its original clear segment. -/
private theorem subdivision_sources (source : Basic.Differential genus) {start finish : Gaussian.Basic.Canonical}
    (segment : Geometry.ClearPath.ClearSegment curve.polynomial ambient start finish) (within : segment.WithinAmbient)
    (sheet : Fin 2) :
    ∀ {left : Branches.PreparedSheetContinuation.Endpoint}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval (segment.pointAt left.parameter))}
      (subdivision : Branches.PreparedSheetContinuation.Subdivision segment within left owner)
      (centers : CenterStates curve source sheet subdivision),
      ∀ parent ∈ centeredEdges curve source sheet subdivision centers, SegmentSource segment parent
  | _, _, .stop _ _, _, _, member => (List.not_mem_nil member).elim
  | _, _, .next left owner request cached ordered small remaining, centers, parent, member => by
      rcases List.Membership.mem_cons.mp member with rfl | member
      · exact ⟨left.parameter, request.endpoint.parameter, left.inside.1, ordered,
          request.endpoint.inside.2, PreparedConstantModels.PreparedEdge.point_zero _,
          PreparedConstantModels.PreparedEdge.point_one _⟩
      · exact subdivision_sources source segment within sheet remaining centers.2 parent member

/-- Recover the exact source grouping from a path's retained preparation.

The stored subdivisions provide each segment block and its original endpoint chain. -/
theorem ofPreparedPath (source : Basic.Differential genus) (sheet : Fin 2) :
    ∀ {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
      {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)} (prepared : PreparedPath path
        owner),
      PathSources sheet path (CenteredPathChain.ofPreparedPath curve source sheet prepared).parents
  | _, _, _, _, .nil point _ => .nil point
  | _, _, _, _, .cons head _ _ within first rest => by
      apply PathSources.cons (CenteredPathChain.dataOfCompleteSegment curve source sheet first).chain.toDirectPathChain
        _ (ofPreparedPath source sheet rest)
      rw [CenteredPathChain.dataOfCompleteSegment_parents]
      exact subdivision_sources source head within sheet first.subdivision _

/-- Every retained dyadic path-bank construction preserves the original segment grouping. -/
theorem ofDyadicBank (source : Basic.Differential genus) (sheet : Fin 2)
    {depth : Nat} {diameter : Rat.Fraction.Rational} {positive : 0 < diameter}
    {start finish : Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
    {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
    (bank : PreparedPath.DyadicBank depth diameter positive path owner) :
    PathSources sheet path (CenteredPathChain.ofDyadicBank curve source sheet bank).parents := by
  cases bank with
  | safe checked => exact ofPreparedPath source sheet checked.prepared
  | executed within prepared success => exact ofPreparedPath source sheet prepared
  | executedCertified checked =>
      rw [CenteredPathChain.ofDyadicBank, CenteredPathChain.ofExecutedCheckedDyadic_parents_eq_ofPreparedPath]
      exact ofPreparedPath source sheet checked.prepared
  | certified certificate => exact ofPreparedPath source sheet certificate.prepared

end

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.Riemann in
open Purelib.Riemann.Paths.PreparedSegmentSources in
/-- Directed refinement preserves grouping by the original clear-path segments.

Splitting the actual refinement at each retained block boundary transports its source certificates and connected root
chain. -/
theorem refine {sheet : Fin 2} {start finish : Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish}
    {parents children : List (CenteredEdge curve source)}
    (sources : PathSources sheet path parents) (refinement : DirectedRefinement parents children) :
    PathSources sheet path children := by
  induction sources generalizing children with
  | nil point => cases refinement; exact .nil point
  | @cons start middle finish segment tail block parents chain sources remaining ih =>
      obtain ⟨left, right, equal, firstPart, secondPart⟩ := refinement.split block
      obtain ⟨rootParts⟩ := firstPart.roots
      rw [equal]
      exact .cons (RootContinuation.PreparedNestedRootRefinements.refinedChain rootParts chain)
        (DirectedRefinement.segment_sources firstPart sources)
        (ih secondPart)

open Purelib.Curves.Hyperelliptic.Differentials in
open Purelib.Data in
open Purelib.Polynomial in
/-- Changing the differential preserves each original segment block and its ordered source positions. -/
theorem recast {sheet : Fin 2} {start finish : Gaussian.Basic.Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start finish} {parents : List (CenteredEdge curve
      source)}
    (sources : PathSources sheet path parents) (target : Basic.Differential genus) :
    PathSources sheet path (parents.map (recastCenteredEdge target)) := by
  induction sources with
  | nil point => exact .nil point
  | cons chain sources remaining ih =>
      rw [List.Map.map_append]
      refine .cons (chain.recast target) ?_ ih
      intro child member
      obtain ⟨parent, present, rfl⟩ := List.Map.mem_map.mp member
      exact (sources parent present).recast target

end PathSources
end Purelib.Riemann.Paths.PreparedPathSources

end
