module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Int.Order
import Purelib.Data.List.Map

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Topology.Polygon.WitnessReadbacks

public import Purelib.Topology.Surface.Sewing.AreaChainTests
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Topology.Surface.Sewing.VertexSewing

public section

/-!
# Complete occurrence pairing from a proved projected area identity

The existing finite scan is reused once. A zero projected chain has no
unmatched residual occurrence, even when the input repeats edges. Actual
cut primitives retain every paired jump and defect instead of descending
through the surface labels.
-/

namespace Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
open Purelib

open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing (PrimitiveSample)

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea edgeArea_reverse edgeListArea
  edgeListArea_append edgeListArea_reordering)

/-- Opposite projected edge pairs contribute zero total area for any target primitive values.

Each stored opposite-edge certificate identifies a reversed target edge. Its signed area cancels the first occurrence
while the retained tail pairs contribute zero. -/
private theorem projected_pairs_area {source target : Nat} {labels : Fin source → Fin target}
    (primitive : Fin target → PrimitivePoint) (pairs : List
      (ProjectedEdgePair labels)) :
    edgeListArea (fun vertex => primitive (labels vertex))
      (ProjectedEdgePair.occurrences pairs) = 0 := by
  induction pairs with
  | nil => rfl
  | cons pair tail ih =>
      have opposite := congrArg (fun edge : OrientedEdge target =>
        edgeArea (primitive edge.start) (primitive edge.finish)) pair.opposite
      change edgeArea (primitive (labels pair.second.start)) (primitive (labels
        pair.second.finish)) =
        edgeArea (primitive (labels pair.first.finish))
          (primitive (labels pair.first.start)) at opposite
      change edgeArea (primitive (labels pair.first.start)) (primitive (labels
        pair.first.finish)) +
        (edgeArea (primitive (labels pair.second.start)) (primitive (labels pair.second.finish))
          + _) = 0
      rw [ih, opposite, edgeArea_reverse]
      ring1

/-- An edge-chain coefficient is nonnegative when no occurrence has its reverse orientation.

The retained reverse-exclusion condition follows each source tail. The current edge contributes either zero or one to
the displayed integer coefficient. -/
private theorem coefficient_nonnegative {count : Nat} (selected : OrientedEdge count) :
    ∀ (word : List (OrientedEdge count)), (∀ edge ∈ word, edge.reverse ≠ selected) →
      0 ≤ Sewing.AreaChainTests.coefficient selected word
  | [], _ => Data.Int.Order.le_refl 0
  | edge :: tail, absent => by
      have rest := ProjectedAreaCancellation.coefficient_nonnegative selected tail
        (fun next member => absent next (List.mem_cons_of_mem _ member))
      rw [Sewing.AreaChainTests.coefficient, Sewing.AreaChainTests.edgeCoefficient,
        if_neg (absent edge List.mem_cons_self)]
      split <;> omega

namespace ProjectedEdgePairing

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (OrientedEdge
  source)}

/-- Projected area is unchanged when the retained opposite pairs are removed from the original word.

The retained incidence decomposition consists of the actual opposite pairs and residual boundary. Their projected signed
areas differ only by the zero contribution of those pairs. -/
theorem projected_boundary_area (pairing : ProjectedEdgePairing labels edges)
  (primitive : Fin target → PrimitivePoint) :
    edgeListArea primitive (edges.map (OrientedEdge.map
      labels)) =
      edgeListArea primitive (pairing.boundary.map
        (OrientedEdge.map labels)) := by
  rw [Polygon.WitnessReadbacks.mapped_incidence_area labels primitive pairing.incidence,
    ← Polygon.WitnessReadbacks.mapped_area, edgeListArea_append,
      projected_pairs_area, add_zero,
    Polygon.WitnessReadbacks.mapped_area]

/-- The scan's actual residual is empty. Repeated occurrences require no simplicity hypothesis: a surviving orientation
has a positive coefficient.

Any residual head would contribute one to its own projected coefficient while the remaining reverse-free tail
contributes nonnegatively. The supplied area identity forces that same coefficient to zero. -/
theorem boundary_empty_of_projected_area_zero (pairing : ProjectedEdgePairing
  labels edges)
    (zero : ∀ primitive : Fin target → PrimitivePoint, edgeListArea
      primitive (edges.map (OrientedEdge.map labels)) = 0) :
    pairing.boundary = [] := by
  have coefficientZero (selected : OrientedEdge target) :
      Sewing.AreaChainTests.coefficient selected (pairing.boundary.map
        (OrientedEdge.map labels)) = 0 :=
    Sewing.AreaChainTests.coefficient_eq (last := [])
      (fun primitive =>
        (projected_boundary_area pairing
        primitive).symm.trans (zero primitive)) selected
  cases equation : pairing.boundary with
  | nil => rfl
  | cons first rest =>
      have noReverse := pairing.noReverse
      rw [equation] at noReverse
      have absent : ∀ edge ∈ (first :: rest).map (OrientedEdge.map labels),
        edge.reverse ≠ OrientedEdge.map labels first := by
        intro edge member equal
        obtain ⟨other, member, projected⟩ := Data.List.Map.mem_map.mp member
        apply noReverse first List.mem_cons_self other member
        exact (OrientedEdge.reverse_reverse
          (OrientedEdge.map labels other)).symm.trans
          (congrArg OrientedEdge.reverse ((congrArg OrientedEdge.reverse
            projected).trans equal))
      have positive := coefficient_nonnegative
        (OrientedEdge.map labels first) (rest.map
        (OrientedEdge.map labels))
        (fun edge member => absent edge (List.mem_cons_of_mem _ member))
      have total := coefficientZero (OrientedEdge.map labels first)
      rw [equation, List.map_cons, Sewing.AreaChainTests.coefficient,
        Sewing.AreaChainTests.edgeCoefficient,
        if_pos rfl, if_neg (absent (OrientedEdge.map labels first)
          List.mem_cons_self)] at total
      omega

set_option genInjectivity false in
/-- The pairing and its completeness proof belong to the same scan.

The certificate retains the actual projected pairing, including repeated source occurrences, and the proof that its own
residual boundary is empty. -/
structure Complete (labels : Fin source → Fin target) (edges : List (OrientedEdge source)) where
  /-- The actual finite scan and its retained paired edge occurrences. -/ pairing :
    ProjectedEdgePairing labels edges
  /-- This same scan has no unmatched residual occurrence. -/ boundary_empty : pairing.boundary = []

constructive_injectivity Complete

namespace Complete

/-- Run the finite pairing scan and certify its residual boundary is empty.

The supplied projected area identity and nonloop condition prove completeness of this exact scan, including repeated
edge occurrences. -/
@[expose] def build (labels : Fin source → Fin target) (edges : List (OrientedEdge source))
    (nonloop : ∀ edge ∈ edges, labels edge.start ≠ labels edge.finish)
    (zero : ∀ primitive : Fin target → PrimitivePoint, edgeListArea
      primitive (edges.map (OrientedEdge.map labels)) = 0) :
    Complete labels edges :=
  let pairing := ProjectedEdgePairing.build labels edges nonloop
  ⟨pairing,
    boundary_empty_of_projected_area_zero
    pairing zero⟩

/-- A complete projected pairing expresses original cut area as its retained jump and defect sums.

The supplied primitive sample belongs to the retained pairing. Its boundary decomposition reduces to the same cached
jump and defect sums when the residual is empty. -/
theorem area_eq_jumps_defects (complete :
  Complete labels edges) (primitive : Fin
  source → PrimitivePoint)
    (sample : PrimitiveSample complete.pairing primitive) :
      edgeListArea primitive edges = sample.jumpSum + sample.defectSum := by
  rw [sample.boundary_decomposition, sample.boundaryArea_eq, complete.boundary_empty]
  exact congrArg (· + sample.defectSum) (zero_add sample.jumpSum)

end Complete
end ProjectedEdgePairing
end Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
