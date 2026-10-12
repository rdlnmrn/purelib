module
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.CCL.Calculus.WeightedAggregateBudget
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
public import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
public import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.SewnConjugateErrors
import Purelib.Data.Vector.Basic
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Approximation.Rational.Budget

open Purelib.CCL.Calculus

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Rat

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear

open Purelib.Data

public section

/-! The original computed sewing budget also pays conjugate/value areas.
Both scalar contact requests and their cached amplification are reused. -/
namespace Purelib.Topology.Surface.Sewing.SewnConjugateRequests

open Purelib

open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Topology.Surface.Sewing.Bilinear.Errors (traceAt)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy)

open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint triangleWedgeArea)

open _root_.Purelib.Data.Gaussian.Basic (conj)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {patch : SewingTree.SewnPatch faces} {magnitude target : SewnPrimitiveFaces.Coordinate}

/-- The original shared sewing request pays the complete conjugate/value boundary-area error.

Both scalar contact certificates and the full face count are retained in the weighted error allocation. -/
theorem accurate {leftLocal rightLocal : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
    {left : SewnPrimitiveSamples.CachedSample patch leftLocal} {right : SewnPrimitiveSamples.CachedSample patch
      rightLocal}
    (request : Requests.AreaRequest patch magnitude target) (sample : SewnConjugateSamples.ConjugatePair left right)
    (leftAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance left.sewn.readings)
    (rightAccurate : SewnPrimitiveRequests.LocalAccuracy request.tolerance right.sewn.readings)
    (bounded : ∀ position (index : Fin 3),
      (PrimitivePoint.Bounded (⟨conj (leftLocal (Errors.traceAt left position).source index) -
        Data.Gaussian.Basic.conj (leftLocal (Errors.traceAt left position).source 0),
        rightLocal (Errors.traceAt left position).source index - rightLocal (Errors.traceAt left position).source 0⟩ :
          Topology.Polygon.Stokes.PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (sample.boundaryArea - FiniteSum.Fin.sumFin (fun position =>
      Stokes.triangleWedgeArea
      ⟨conj (leftLocal (Errors.traceAt left position).source 0), rightLocal (Errors.traceAt left position).source 0⟩
      ⟨conj (leftLocal (Errors.traceAt left position).source 1), rightLocal (Errors.traceAt left position).source 1⟩
      ⟨conj (leftLocal (Errors.traceAt left position).source 2), rightLocal (Errors.traceAt left position).source 2⟩)) <
        target := by
  have small : request.error ≤ 1 := by rw [request.error_eq]; exact Fraction.Order.Basic.min_le_left _ _
  have estimate := SewnConjugateErrors.boundary_area_error sample (fun _ => request.error) request.nonnegative
    (fun _ => request.error_positive.le) (fun _ => small)
    (request.trace_bound left leftAccurate) (request.trace_bound right rightAccurate) bounded
  rw [Algebra.FiniteSum.Fin.Rational.sum_constant, ← request.weight_eq] at estimate
  have weighted : request.weight * request.error ≤
      Aggregate.perTerm target patch.cut.triangles.length := by
    have errorLe : request.error ≤ Aggregate.perTerm
        (Weighted.allowance target request.weight) patch.cut.triangles.length := by
      rw [request.error_eq]
      exact Fraction.Order.Basic.min_le_right _ _
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe
      request.weight_nonnegative).trans
      (WeightedAggregateBudget.weighted_perTerm_le request.positive request.weight_nonnegative _)
  have countNonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le patch.cut.triangles.length)
  exact estimate.trans_lt ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct weighted countNonnegative)
    countNonnegative).trans_lt (Aggregate.count_mul_perTerm_lt request.positive _))

end Purelib.Topology.Surface.Sewing.SewnConjugateRequests
