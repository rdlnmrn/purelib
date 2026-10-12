module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Word.ProjectedEdgePairs
import Purelib.Data.List.Map
import Purelib.Tactic.Ring

public section

/-!
# Exact primitive-jump contributions on paired cut edges

Opposite projected edges do not cancel for independent cut-vertex values.
Their contribution is a jump paired with the edge increment, plus an exact
defect term if the jumps at the two endpoints differ. The defect is retained
until analytic compatibility or a quantitative error bound pays for it.
-/

namespace Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Data.List

open Purelib.Data

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Word

open Purelib.Topology.Surface.Word.ProjectedEdgePairs

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea edgeListArea edgeListArea_append
  edgeListArea_reordering)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePair ProjectedEdgePairing)

namespace ProjectedEdgePair

variable {source target : Nat} {labels : Fin source → Fin target}

open Purelib.Topology.Polygon.Stokes in
set_option genInjectivity false in
/-- Cached calculations for one actual pair.

The retained pair supplies both cut occurrences. Every jump, increment, defect and area contribution is cached with an
equality to those same endpoint readings. -/
structure Sample (primitive : Fin source → Stokes.PrimitivePoint) where
  /-- Original projected edge pair used by every cached quantity. -/ pair : ProjectedEdgePairs.ProjectedEdgePair labels
  /-- Primitive difference from the first edge's start to the second edge's finish. -/ startJump : Stokes.PrimitivePoint
  /-- The retained start jump is the specified aligned endpoint difference. -/ startJump_eq : startJump =
    PrimitivePoint.sub (primitive pair.second.finish) (primitive pair.first.start)
  /-- Primitive difference from the first edge's finish to the second edge's start. -/ finishJump :
    Stokes.PrimitivePoint
  /-- The retained finish jump is the specified aligned endpoint difference. -/ finishJump_eq : finishJump =
    PrimitivePoint.sub (primitive pair.second.start) (primitive pair.first.finish)
  /-- Cached primitive increment along the first edge. -/ increment : Stokes.PrimitivePoint
  /-- The increment is the first edge's primitive endpoint difference. -/ increment_eq : increment = PrimitivePoint.sub
    (primitive pair.first.finish) (primitive pair.first.start)
  /-- Cached difference between the two aligned endpoint jumps. -/ defect : Stokes.PrimitivePoint
  /-- The defect is the finish jump minus the start jump. -/ defect_eq : defect = PrimitivePoint.sub finishJump
    startJump
  /-- Cached sum of the two original oriented edge areas. -/ contribution : Gaussian.Basic.Canonical
  /-- The contribution uses the primitive values at both original edge endpoints. -/ contribution_eq : contribution =
    Stokes.edgeArea (primitive pair.first.start) (primitive pair.first.finish) +
    Stokes.edgeArea (primitive pair.second.start) (primitive pair.second.finish)
  /-- Cached area interaction of the start jump with the first-edge increment. -/ jumpTerm : Gaussian.Basic.Canonical
  /-- The jump contribution is the negative area pairing of start jump and increment. -/ jumpTerm_eq : jumpTerm =
    -Stokes.edgeArea startJump increment
  /-- Cached area interaction of the jump defect with the second edge's finish value. -/ defectTerm :
    Gaussian.Basic.Canonical
  /-- The defect contribution uses the retained defect and the original second finish value. -/ defectTerm_eq :
    defectTerm = Stokes.edgeArea defect (primitive pair.second.finish)

constructive_injectivity Sample

namespace Sample

variable {primitive : Fin source → Stokes.PrimitivePoint}

section
open Purelib.Topology.Polygon.Stokes
open Purelib.Topology.Surface.Cut.PrimitiveJumps
/-- Cache both aligned endpoint jumps, their defect and the complete area decomposition for one cut pair.

The supplied primitive values and retained pair determine every displayed cache field. The builder keeps those computed
values with their exact specification equalities. -/
@[expose] def build (primitive : Fin source → Stokes.PrimitivePoint) (pair : ProjectedEdgePairs.ProjectedEdgePair
  labels) : ProjectedEdgePair.Sample (labels := labels) primitive :=
  let startJump := PrimitivePoint.sub (primitive pair.second.finish) (primitive pair.first.start)
  let finishJump := PrimitivePoint.sub (primitive pair.second.start) (primitive pair.first.finish)
  let increment := PrimitivePoint.sub (primitive pair.first.finish) (primitive pair.first.start)
  let defect := PrimitivePoint.sub finishJump startJump
  { pair := pair
    startJump := startJump
    startJump_eq := rfl
    finishJump := finishJump
    finishJump_eq := rfl
    increment := increment
    increment_eq := rfl
    defect := defect
    defect_eq := rfl
    contribution := Stokes.edgeArea (primitive pair.first.start) (primitive pair.first.finish) +
      Stokes.edgeArea (primitive pair.second.start) (primitive pair.second.finish)
    contribution_eq := rfl
    jumpTerm := -Stokes.edgeArea startJump increment
    jumpTerm_eq := rfl
    defectTerm := Stokes.edgeArea defect (primitive pair.second.finish)
    defectTerm_eq := rfl }

/-- Exact identity, including the nonconstant-jump error.

The retained cache equations reduce the claim to scalar Gaussian algebra. The start-jump term and finish-jump defect
together account for both oriented cut-edge areas. -/
theorem contribution_decomposition (sample : ProjectedEdgePair.Sample (labels := labels) primitive) :
    sample.contribution = sample.jumpTerm + sample.defectTerm := by
  rw [sample.contribution_eq, sample.jumpTerm_eq, sample.defectTerm_eq, sample.defect_eq,
    sample.startJump_eq, sample.finishJump_eq, sample.increment_eq]
  simp only [PrimitivePoint.sub, Stokes.edgeArea]
  ring1

/-- Equal aligned endpoint jumps make the retained defect contribution vanish.

The equality identifies the finish and start jump cache fields. Their retained difference is zero, so its area
interaction with the second edge finish is zero. -/
theorem defectTerm_zero (sample : ProjectedEdgePair.Sample (labels := labels) primitive)
    (constantJump : sample.finishJump = sample.startJump) : sample.defectTerm = 0 := by
  rw [sample.defectTerm_eq, sample.defect_eq, constantJump]
  simp only [PrimitivePoint.sub, Stokes.edgeArea]
  ring1

end

section
open Purelib.Topology.Surface.Cut.PrimitiveJumps
/-- Equal aligned endpoint jumps leave only the retained jump contribution.

The complete contribution decomposition and the supplied cache equality make the defect term vanish while retaining the
original pair's jump term. -/
theorem contribution_of_constantJump (sample : ProjectedEdgePair.Sample (labels := labels) primitive)
    (constantJump : sample.finishJump = sample.startJump) : sample.contribution = sample.jumpTerm := by
  rw [sample.contribution_decomposition, sample.defectTerm_zero constantJump, add_zero]

/-- Sum a selected Gaussian reading over the ordered retained pair samples.

The empty sample list has reading zero. Each retained sample contributes its selected value before the unchanged tail in
its supplied order. -/
@[expose] def sum (value : ProjectedEdgePair.Sample (labels := labels) primitive → Gaussian.Basic.Canonical) : List
  (ProjectedEdgePair.Sample (labels := labels) primitive) → Gaussian.Basic.Canonical
  | [] => 0
  | sample :: samples => value sample + Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.sum value
    samples

end

open Purelib.Topology.Surface.Cut.PrimitiveJumps
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair
/-- Summing pair contributions gives the area of the complete paired-edge occurrence list.

Each retained sample contributes both original cut-edge areas. Structural recursion preserves the pair order and the
first-then-second occurrence order within each pair. -/
theorem sum_contributions : (samples : List (ProjectedEdgePair.Sample (labels := labels) primitive)) →
    Sample.sum Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.contribution samples =
      Stokes.edgeListArea primitive (ProjectedEdgePair.occurrences (samples.map
      Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.pair))
  | [] => rfl
  | sample :: samples => by
      rw [Sample.sum, sample.contribution_eq,
        Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.sum_contributions samples]
      simp only [List.map_cons, ProjectedEdgePair.occurrences, Stokes.edgeListArea]
      ring1

/-- The total paired contribution is the sum of retained jump terms and retained defect terms.

The decomposition is specialized to each original sample. Structural recursion groups the same ordered jump and defect
readings into their two finite sums. -/
theorem sum_decomposition : (samples : List (ProjectedEdgePair.Sample (labels := labels) primitive)) →
    Sample.sum Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.contribution samples = Sample.sum
      Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.jumpTerm samples + Sample.sum
      Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.defectTerm samples
  | [] => by change (0 : Gaussian.Basic.Canonical) = 0 + 0; ring1
  | sample :: samples => by
      rw [Sample.sum, Sample.sum, Sample.sum, sample.contribution_decomposition,
        Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.sum_decomposition samples]
      ring1

end Sample
end ProjectedEdgePair

namespace ProjectedEdgePairing

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List (Stokes.OrientedEdge source)}

open Purelib.Topology.Surface.Cut.PrimitiveJumps in
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair in
set_option genInjectivity false in
/-- All executable pair calculations and aggregate sums are cached.

The retained sample list reads back the pairing's exact original pairs. Boundary, jump and defect totals are tied to
those same caches by specification equalities. -/
structure PrimitiveSample (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges) (primitive : Fin source →
  Stokes.PrimitivePoint) where
  /-- Ordered retained primitive samples for the original projected edge pairs. -/ samples : List
    (ProjectedEdgePair.Sample (labels := labels) primitive)
  /-- Reading sample pairs recovers the original pair list exactly. -/ pairs_eq : samples.map
    Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.pair = pairing.pairs
  /-- Cached area of the residual physical boundary. -/ boundaryArea : Gaussian.Basic.Canonical
  /-- The residual area is computed from the pairing's original boundary list. -/ boundaryArea_eq : boundaryArea =
    Stokes.edgeListArea primitive pairing.boundary
  /-- Cached sum of the retained pair jump contributions. -/ jumpSum : Gaussian.Basic.Canonical
  /-- The jump total is the sum over the retained original samples. -/ jumpSum_eq : jumpSum = Sample.sum
    Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.jumpTerm samples
  /-- Cached sum of the retained pair defect contributions. -/ defectSum : Gaussian.Basic.Canonical
  /-- The defect total is the sum over the retained original samples. -/ defectSum_eq : defectSum = Sample.sum
    Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.defectTerm samples

constructive_injectivity PrimitiveSample

namespace PrimitiveSample

variable {pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges} {primitive : Fin source →
  Stokes.PrimitivePoint}

open Purelib.Topology.Surface.Cut.PrimitiveJumps
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair
/-- Cache every original pair sample and the residual boundary, jump and defect area totals.

The retained pair list is preserved exactly, and each aggregate is tied to those same samples. -/
@[expose] def build (pairing : ProjectedEdgePairs.ProjectedEdgePairing labels edges) (primitive : Fin source →
  Stokes.PrimitivePoint) :
    ProjectedEdgePairing.PrimitiveSample pairing primitive :=
  let samples := pairing.pairs.map (Sample.build primitive)
  { samples := samples
    pairs_eq := by
      rw [Map.map_map]
      change pairing.pairs.map (fun pair => pair) = pairing.pairs
      induction pairing.pairs with
      | nil => rfl
      | cons pair rest ih => exact congrArg (List.cons pair) ih
    boundaryArea := Stokes.edgeListArea primitive pairing.boundary
    boundaryArea_eq := rfl
    jumpSum := Sample.sum Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.jumpTerm samples
    jumpSum_eq := rfl
    defectSum := Sample.sum Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair.Sample.defectTerm samples
    defectSum_eq := rfl }

/-- The full cut boundary is its genuine one-sided contribution plus the retained period-jump and compatibility-defect
terms.

The retained incidence reordering preserves all original edge occurrences. The exact cached pair decomposition separates
their boundary, jump and defect contributions without discarding any reading. -/
theorem boundary_decomposition (sample : ProjectedEdgePairing.PrimitiveSample pairing primitive) :
    Stokes.edgeListArea primitive edges = sample.boundaryArea + sample.jumpSum + sample.defectSum := by
  rw [Stokes.edgeListArea_reordering primitive pairing.incidence, Stokes.edgeListArea_append,
    ← sample.pairs_eq, ← Sample.sum_contributions,
    Sample.sum_decomposition,
    sample.boundaryArea_eq, sample.jumpSum_eq, sample.defectSum_eq]
  ring1

end PrimitiveSample
end ProjectedEdgePairing

end Purelib.Topology.Surface.Cut.PrimitiveJumps
