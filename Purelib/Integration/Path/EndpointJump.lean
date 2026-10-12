module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Surface.Cut.PrimitiveJumps

public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Tactic.Ring

@[expose] public section

/-! Endpoint differences split into an initial primitive jump and an increment error. -/
namespace Purelib.Riemann.Periods.CenteredBilinearPath.Sample

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)

open Purelib.Riemann.Periods.CenteredBilinearPath (Sample Coordinate)
variable {leftCount rightCount : Nat}
  {leftValues : Fin (leftCount + 1) → PrimitivePoint}
  {rightValues : Fin (rightCount + 1) → PrimitivePoint}

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- The skew endpoint term formed from the original origin discrepancy and the left sample's terminal centered value.

Both sample owners index the operation; the formula retains the original left-centered endpoint and original origin
readings. -/
def endpointJump (left : Sample leftValues) (_right : Sample
  rightValues) : Basic.Canonical :=
  edgeArea ((Stokes.PrimitivePoint.sub (leftValues 0)) (rightValues 0)) (left.centered (Fin.last leftCount))

open Purelib.Riemann.Periods.CenteredBilinearPath.Sample (endpointJump)

open Purelib.Data.Gaussian in
open Purelib.Topology.Polygon in
/-- The skew area of the original right origin with the difference of the two terminal centered values. -/
def endpointIncrementError (left : Sample leftValues) (right
  : Sample rightValues) : Basic.Canonical :=
  edgeArea (rightValues 0)
    ((Stokes.PrimitivePoint.sub (left.centered (Fin.last leftCount))) (right.centered (Fin.last rightCount)))

open Purelib.Riemann.Periods.CenteredBilinearPath.Sample (endpointIncrementError)

open Purelib.Topology.Polygon in
/-- The two retained endpoint corrections differ by endpoint jump plus endpoint increment error. -/
theorem endpoint_difference (left : Sample leftValues) (right
  : Sample rightValues) :
    left.endpoint - right.endpoint = endpointJump left right + endpointIncrementError left right := by
  rw [left.endpoint_eq, right.endpoint_eq]
  simp only [endpointJump, endpointIncrementError, left.centered_eq, right.centered_eq,
    edgeArea, Stokes.PrimitivePoint.sub]
  ring1

open Purelib.Data.Gaussian in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Bounds on the original right origin and terminal increment discrepancy give a four-times-product bound on the
endpoint increment error. -/
theorem endpointIncrementError_bound (left : Sample
  leftValues) (right : Sample rightValues)
    {magnitude error : Coordinate} (origin : (PrimitiveAreaBounds.PrimitivePoint.Bounded (rightValues 0)) magnitude)
    (increment : (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (left.centered (Fin.last
      leftCount)))
      (right.centered (Fin.last rightCount)))) error) :
    Data.Gaussian.Norm.Basic.normSq (endpointIncrementError left right) ≤ 4 * magnitude * error := by
  simpa only [Norm.Basic.normSq_eq_canonical, endpointIncrementError] using
    PrimitiveAreaBounds.PrimitivePoint.area_bound origin increment

end Purelib.Riemann.Periods.CenteredBilinearPath.Sample
