module

public import Purelib.Riemann.Integration.PreparedParentSplitting
public import Purelib.Approximation.Gaussian.Budget.Aggregate
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Topology.Chain.PathBoundary
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Tactic.Ring

/-! # Common primitive comparisons on the original ordered split bank

Each original parent occurrence may carry a different retained primitive.
The same geometric split telescopes it without identifying constants or
repeated equal parents. Finite Cauchy charges the literal total piece count.
-/

public section

namespace Purelib.Riemann.Integration.PreparedParentSplitting.ParentSplits

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum gaussianSum_append gaussianSum_map_sub)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Normalization.RectangularInverseModels (Geometry)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (GridCuts SegmentSplit SegmentPiece)

variable {genus columns rows : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}
    {geometry : Geometry columns rows} {cuts : GridCuts geometry}

/-- Read the actual retained split at its original bounded parent occurrence, without rebuilding a split. -/
@[expose] def get : {parents : List (CenteredEdge curve differential)} → (splits : ParentSplits cuts parents) →
    (position : Fin parents.length) → SegmentSplit cuts
      ((parents[position.val]'position.isLt).edge.point 0)
      ((parents[position.val]'position.isLt).edge.point 1)
  | [], .nil, position => Fin.elim0 position
  | _ :: _, .cons split tail, position => Fin.cases split (fun index => tail.get index) position

/-- The exact retained bounded split is an occurrence of the original splitting bank. -/
theorem get_member : {parents : List (CenteredEdge curve differential)} → (splits : ParentSplits cuts parents) →
    (position : Fin parents.length) → ParentSplits.Member (splits.get position) splits
  | [], .nil, position => Fin.elim0 position
  | _ :: _, .cons split tail, position => by
      refine Fin.cases (ParentSplits.Member.here tail) ?_ position
      intro index
      exact .there split (tail.get_member index)

/-- Evaluate each supplied occurrence's primitive at its own original endpoints, preserving the parent order. -/
@[expose] def primitiveIncrements : {parents : List (CenteredEdge curve differential)} →
    (splits : ParentSplits cuts parents) → (Fin parents.length → Canonical → Canonical) → List Canonical
  | [], .nil, _ => []
  | parent :: _, .cons _ tail, primitives =>
      (primitives 0 (parent.edge.point 1) - primitives 0 (parent.edge.point 0)) ::
        tail.primitiveIncrements (fun position => primitives position.succ)

/-- Pointwise scalar readbacks of the supplied occurrence primitives preserve their same ordered increments. -/
theorem primitiveIncrements_congr : {parents : List (CenteredEdge curve differential)} →
    (splits : ParentSplits cuts parents) → (first last : Fin parents.length → Canonical → Canonical) →
    (∀ position point, first position point = last position point) →
    splits.primitiveIncrements first = splits.primitiveIncrements last
  | [], .nil, _, _, _ => rfl
  | parent :: _, .cons _ tail, first, last, same =>
      congrArg₂ List.cons (congrArg₂ (fun finish start : Canonical => finish - start)
        (same 0 (parent.edge.point 1)) (same 0 (parent.edge.point 0)))
        (primitiveIncrements_congr tail (fun position => first position.succ) (fun position => last position.succ)
          (fun position point => same position.succ point))

/-- One shared endpoint reading telescopes over the original full centered chain, including stationary occurrences. -/
theorem primitiveIncrements_shared {parents : List (CenteredEdge curve differential)}
    (splits : ParentSplits cuts parents) (reading : Canonical → Canonical)
    {first last : LiftedPoint 2}
    (chain : CenteredPathChain parents (start := first) (finish := last)) :
    gaussianSum (splits.primitiveIncrements (fun _ => reading)) =
      reading last.coordinate - reading first.coordinate := by
  induction chain with
  | nil =>
      cases splits
      change (0 : Canonical) = _ - _
      ring1
  | cons parent chain ih =>
      cases splits with
      | cons split tail =>
          change (reading (parent.edge.point 1) - reading (parent.edge.point 0)) +
            gaussianSum (tail.primitiveIncrements (fun _ => reading)) = _
          rewrite [ih tail, parent.edge.point_zero, parent.edge.point_one]
          ring1

/-- The actual per-piece errors retain the given primitive separately at every original parent occurrence. -/
private def errors : {parents : List (CenteredEdge curve differential)} → (splits : ParentSplits cuts parents) →
    (Canonical → Canonical) → (Fin parents.length → Canonical → Canonical) → List Canonical
  | [], .nil, _, _ => []
  | _ :: _, .cons split tail, reading, primitives =>
      split.pieces.map (fun piece =>
        (reading piece.lastPoint - reading piece.firstPoint) -
          (primitives 0 piece.lastPoint - primitives 0 piece.firstPoint)) ++
      errors tail reading (fun position => primitives position.succ)

/-- The error list retains exactly the original splitting bank's full piece count. -/
private theorem errors_length : {parents : List (CenteredEdge curve differential)} →
    (splits : ParentSplits cuts parents) → (reading : Canonical → Canonical) →
    (primitives : Fin parents.length → Canonical → Canonical) →
    (errors splits reading primitives).length = splits.pieceCount
  | [], .nil, _, _ => rfl
  | _ :: _, .cons split tail, reading, primitives => by
      change (split.pieces.map _ ++ errors tail reading (fun position => primitives position.succ)).length = _
      rewrite [Append.length_append, Map.length_map, errors_length tail reading
        (fun position => primitives position.succ), ← split.count_eq]
      rfl

/-- Summing the retained piece errors gives the difference of the two original full endpoint-increment sums. -/
private theorem errors_sum : {parents : List (CenteredEdge curve differential)} →
    (splits : ParentSplits cuts parents) → (reading : Canonical → Canonical) →
    (primitives : Fin parents.length → Canonical → Canonical) →
    gaussianSum (errors splits reading primitives) =
      gaussianSum (splits.primitiveIncrements (fun _ => reading)) -
        gaussianSum (splits.primitiveIncrements primitives)
  | [], .nil, _, _ => by change (0 : Canonical) = 0 - 0; ring1
  | _ :: _, .cons split tail, reading, primitives => by
      change gaussianSum (split.pieces.map _ ++ errors tail reading (fun position => primitives position.succ)) = _
      rewrite [gaussianSum_append, gaussianSum_map_sub, split.telescope reading,
        split.telescope (primitives 0), errors_sum tail reading (fun position => primitives position.succ)]
      change (_ - (_ - _)) + (_ - _) = (_ + _) - (_ + _)
      ring1

/-- A bound on each literal retained piece bounds every entry of the same actual error list. -/
private theorem errors_bounded {bound : Rational} : {parents : List (CenteredEdge curve differential)} →
    (splits : ParentSplits cuts parents) → (reading : Canonical → Canonical) →
    (primitives : Fin parents.length → Canonical → Canonical) →
    (∀ position, ∀ piece ∈ (splits.get position).pieces,
      normSq ((reading piece.lastPoint - reading piece.firstPoint) -
        (primitives position piece.lastPoint - primitives position piece.firstPoint)) ≤ bound) →
    ∀ value ∈ errors splits reading primitives, normSq value ≤ bound
  | [], .nil, _, _, _, value, impossible => nomatch impossible
  | _ :: _, .cons split tail, reading, primitives, bounded, value, member => by
      change value ∈ split.pieces.map _ ++ errors tail reading (fun position => primitives position.succ) at member
      rcases Membership.mem_append.mp member with head | rest
      · obtain ⟨piece, pieceMember, same⟩ := Map.mem_map.mp head
        exact Eq.mp (congrArg (fun actual : Canonical => normSq actual ≤ bound) same)
          (bounded 0 piece pieceMember)
      · exact errors_bounded tail reading (fun position => primitives position.succ)
          (fun position piece member => bounded position.succ piece member) value rest

/-- Original per-piece estimates at the genuine count-adjusted allowance pay the full unchanged primitive sum.

The primitive function is indexed by the original bounded occurrence, so two
equal parents may retain different polynomials and constants. Every local
bound concerns its exact original split and numerical reading.
-/
theorem primitive_difference_lt {parents : List (CenteredEdge curve differential)}
    (splits : ParentSplits cuts parents) (reading : Canonical → Canonical)
    (primitives : Fin parents.length → Canonical → Canonical) {target : Rational}
    (positive : 0 < target)
    (bounded : ∀ position, ∀ piece ∈ (splits.get position).pieces,
      normSq ((reading piece.lastPoint - reading piece.firstPoint) -
        (primitives position piece.lastPoint - primitives position piece.firstPoint)) ≤
          Approximation.Rational.Budget.Aggregate.perTerm target splits.pieceCount) :
    normSq (gaussianSum (splits.primitiveIncrements (fun _ => reading)) -
      gaussianSum (splits.primitiveIncrements primitives)) < target := by
  have actual := Approximation.Gaussian.Budget.Aggregate.normSq_sum_lt
    (errors splits reading primitives) positive (fun value member => by
      rewrite [errors_length splits reading primitives]
      exact errors_bounded splits reading primitives bounded value member)
  exact Eq.mp (congrArg (fun value : Canonical => normSq value < target)
    (errors_sum splits reading primitives)) actual

end Purelib.Riemann.Integration.PreparedParentSplitting.ParentSplits
