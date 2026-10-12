module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Aggregate
public import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.CCL.Calculus.WeightedAggregateBudget
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Riemann.Readings.PrimitiveAreaBounds.ProjectedEdgePair

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePair

@[expose] public section

/-!
# Paying the complete weighted cut-pair defect sum

The bound applies to the actual cached defect terms in the boundary
decomposition. Both primitive components are allowed to differ. A fixed
magnitude pays the endpoint weights before both finite pair-count factors.
-/

namespace Purelib.Approximation.Budget.WeightedDefectBudget

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Topology.Surface.Word.ProjectedEdgePairs (ProjectedEdgePairing)
open Purelib.Topology.Surface.Cut.PrimitiveJumps.ProjectedEdgePairing (PrimitiveSample)
open Purelib.Riemann.Readings.PrimitiveAreaBounds (AreaCoordinate)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

/-- The recursive sum over retained pair samples equals the Gaussian sum of their mapped values. -/
private theorem pairSum_eq {source target : Nat} {labels : Fin source → Fin target} {primitive : Fin source →
  Stokes.PrimitivePoint}
    (value : ProjectedEdgePair.Sample (labels := labels) primitive → Data.Gaussian.Basic.Canonical)
    (samples : List (ProjectedEdgePair.Sample (labels := labels) primitive)) :
    Sample.sum value samples = Data.Gaussian.Norm.Sum.Basic.gaussianSum (samples.map value) := by
  induction samples with
  | nil => rfl
  | cons sample samples ih => exact congrArg (value sample + ·) ih

namespace ProjectedEdgePairing.PrimitiveSample

variable {source target : Nat} {labels : Fin source → Fin target} {edges : List
  (Purelib.Topology.Polygon.Stokes.OrientedEdge source)}
  {pairing : Purelib.Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing labels edges} {primitive : Fin source
    → Purelib.Topology.Polygon.Stokes.PrimitivePoint}

/-- The complete retained weighted defect sum meets the positive squared-error target.

Each component defect receives its count-adjusted allowance, and the displayed endpoint magnitude pays the actual
weights before both finite count factors. -/
theorem defectSum_accurate (sample : ProjectedEdgePairing.PrimitiveSample pairing primitive) {target magnitude :
  PrimitiveAreaBounds.AreaCoordinate}
    (positive : 0 < target) (nonnegative : 0 ≤ magnitude) (count : Nat) (countEq : sample.samples.length = count)
    (defects : ∀ entry ∈ sample.samples, (PrimitivePoint.Bounded entry.defect)
      (Aggregate.perTerm (Weighted.allowance target (4 * magnitude)) count))
    (endpoints : ∀ entry ∈ sample.samples, (PrimitivePoint.Bounded (primitive entry.pair.second.finish)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq sample.defectSum < target := by
  rw [sample.defectSum_eq, Approximation.Budget.WeightedDefectBudget.pairSum_eq]
  apply Gaussian.Budget.Aggregate.normSq_sum_lt _ positive
  intro value member
  obtain ⟨entry, member, equal⟩ := Map.mem_map.mp member
  rw [← equal, Map.length_map, countEq]
  have bound := Sample.defectTerm_bound entry (defects entry member) (endpoints entry member)
  have paid := WeightedAggregateBudget.weighted_perTerm_le positive
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : PrimitiveAreaBounds.AreaCoordinate) ≤ 4) nonnegative)
      count
  apply (show Data.Gaussian.Norm.Basic.normSq entry.defectTerm = entry.defectTerm.normSq from
    Data.Gaussian.Norm.Basic.normSq_eq_canonical _).trans_le
  exact bound.trans ((show 4 * Aggregate.perTerm
      (Weighted.allowance target (4 * magnitude)) count * magnitude =
        (4 * magnitude) * Aggregate.perTerm
          (Weighted.allowance target (4 * magnitude)) count by ring1).trans_le paid)

end ProjectedEdgePairing.PrimitiveSample
end Purelib.Approximation.Budget.WeightedDefectBudget
