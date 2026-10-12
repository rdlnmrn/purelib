module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Norm.Weighted

import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Area bounds using the total finite length weight, rather than the number
of trace vertices. They retain every edge, including owner junctions. -/
namespace Purelib.Integration.Path.WeightedPathArea
open Purelib.Riemann.Readings
open Purelib.Riemann.Periods
open Purelib.Integration.Path
open Purelib.Data.Gaussian
open Purelib.Algebra
open Purelib.Topology.Polygon

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample Coordinate)

variable {count : Nat}

/-- The directed edge area equals the area against its exact original endpoint displacement. -/
private theorem edge_increment (first last : Stokes.PrimitivePoint) :
    Stokes.edgeArea first last = Stokes.edgeArea first ((Stokes.PrimitivePoint.sub last) first) := by
  simp only [Stokes.edgeArea, Stokes.PrimitivePoint.sub]
  ring1

/-- Nonnegative edge weights control path area through a common vertex magnitude and weighted increment density.

Both primitive coordinates retain their original bounds, and the final estimate uses the square of the exact finite
weight sum. -/
theorem weighted_area_bound (values : Fin (count + 1) → Stokes.PrimitivePoint)
    (weights : Fin count → CenteredBilinearPath.Coordinate) {magnitude density : CenteredBilinearPath.Coordinate}
    (nonnegative : ∀ edge, 0 ≤ weights edge)
    (bounded : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded (values vertex)) magnitude)
    (increments : ∀ edge : Fin count,
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (values edge.succ)) (values
        edge.castSucc))) (density * (weights edge)^2)) :
    Data.Gaussian.Norm.Basic.normSq (CenteredBilinearPath.area values) ≤ 4 * magnitude * density * (FiniteSum.Fin.sumFin
      weights)^2 := by
  apply Norm.Weighted.normSq_sumFin_weighted _ weights nonnegative
  intro edge
  rw [WeightedPathArea.edge_increment]
  have scalarBound := PrimitiveAreaBounds.PrimitivePoint.area_bound (bounded edge.castSucc) (increments edge)
  rw [← Norm.Basic.normSq_eq_canonical] at scalarBound
  exact scalarBound.trans_eq (by ring1)

namespace Sample
variable {values : Fin (count + 1) → Purelib.Topology.Polygon.Stokes.PrimitivePoint}

/-- The retained centered sample has exactly the original primitive increments between any two vertices. -/
theorem centered_increment (sample : CenteredBilinearPath.Sample values) (first last : Fin (count + 1)) :
    (Stokes.PrimitivePoint.sub (sample.centered last)) (sample.centered first) = (Stokes.PrimitivePoint.sub (values
      last)) (values first) := by
  rw [sample.centered_eq, sample.centered_eq]
  apply congrArg₂ Stokes.PrimitivePoint.mk <;> dsimp only [Stokes.PrimitivePoint.sub] <;> ring1

/-- The retained centered area obeys the weighted bound using original increments and centered vertex magnitudes.

The original nonnegative weights and sample owner remain fixed; centering changes neither the increments nor their
density certificates. -/
theorem centered_weighted_bound (sample : CenteredBilinearPath.Sample values)
    (weights : Fin count → CenteredBilinearPath.Coordinate) {magnitude density : CenteredBilinearPath.Coordinate}
    (nonnegative : ∀ edge, 0 ≤ weights edge)
    (bounded : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded (sample.centered vertex)) magnitude)
    (increments : ∀ edge : Fin count,
      (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (values edge.succ)) (values
        edge.castSucc))) (density * (weights edge)^2)) :
    Data.Gaussian.Norm.Basic.normSq sample.centeredArea ≤ 4 * magnitude * density * (FiniteSum.Fin.sumFin weights)^2 :=
      by
  rw [sample.centeredArea_eq]
  apply WeightedPathArea.weighted_area_bound _ weights nonnegative bounded
  intro edge
  rw [WeightedPathArea.Sample.centered_increment]
  exact increments edge

end Sample
end Purelib.Integration.Path.WeightedPathArea

end
