module
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Algebra.FiniteSum.Fin.Rational
import Purelib.Data.Gaussian.Basic
import Purelib.CCL.Calculus.WeightedAggregateBudget
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Topology.Surface.Sewing.Bilinear.Errors
public import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnConjugateErrors
public import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Sewing.SewnConjugateRequests
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The existing full-surface contact budget pays any retained selection
of triangle positions, with the original count and both sheet occurrences. -/

namespace Purelib.Riemann.Readings.SelectedConjugateRequests

open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (Coordinate)
open Purelib.Topology.Surface.Sewing.SewnConjugateSamples (ConjugatePair)
open Purelib.Topology.Surface.Sewing.Bilinear.Errors (traceAt)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests (LocalAccuracy)
open Purelib.Topology.Surface.Sewing.Bilinear.Requests (AreaRequest)

open Purelib.Topology.Polygon.Stokes (OrientedTriangle PrimitivePoint triangleWedgeArea)

open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Basic (conj)

open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {vertexCount faceCount : Nat} {faces : Fin faceCount → OrientedTriangle vertexCount}
  {patch : SewnPatch faces} {magnitude target :
    Coordinate}
  {leftLocal rightLocal : Fin faceCount → PrimitiveValues 3}
  {left : CachedSample patch leftLocal} {right :
    CachedSample patch rightLocal}

open Purelib.Algebra in
open Purelib.Topology in
open Purelib.Approximation in
open Purelib.Data in
open Purelib.CCL.Calculus in
/-- A conjugate area request pays the error of any retained triangle-position selection.

Both sewn readings meet the request's local accuracy, and the centered conjugate primitive pairs meet its magnitude
bound. The budget uses the original full triangle count, with omitted positions contributing zero. -/
theorem selected_conjugate_accurate (request : Surface.Sewing.Bilinear.Requests.AreaRequest patch magnitude target)
  (sample : Surface.Sewing.SewnConjugateSamples.ConjugatePair left right)
    (keep : Fin patch.cut.triangles.length → Bool)
    (leftAccurate : Surface.Sewing.SewnPrimitiveRequests.LocalAccuracy request.tolerance left.sewn.readings)
    (rightAccurate : Surface.Sewing.SewnPrimitiveRequests.LocalAccuracy request.tolerance right.sewn.readings)
    (bounded : ∀ position (index : Fin 3),
      (Bounded (⟨conj (leftLocal (Surface.Sewing.Bilinear.Errors.traceAt left position).source index) -
        Data.Gaussian.Basic.conj (leftLocal (Surface.Sewing.Bilinear.Errors.traceAt left position).source 0),
        rightLocal (Surface.Sewing.Bilinear.Errors.traceAt left position).source index - rightLocal
          (Surface.Sewing.Bilinear.Errors.traceAt left position).source 0⟩ :
          PrimitivePoint)) magnitude) :
    Data.Gaussian.Norm.Basic.normSq (FiniteSum.Fin.sumFin (fun position => if keep position then
      triangleWedgeArea (sample.values patch.cut.triangles[position.val].first)
        (sample.values patch.cut.triangles[position.val].second)
        (sample.values patch.cut.triangles[position.val].third) -
      triangleWedgeArea
        ⟨conj (leftLocal (Surface.Sewing.Bilinear.Errors.traceAt left position).source 0), rightLocal
          (Surface.Sewing.Bilinear.Errors.traceAt left position).source 0⟩
        ⟨conj (leftLocal (Surface.Sewing.Bilinear.Errors.traceAt left position).source 1), rightLocal
          (Surface.Sewing.Bilinear.Errors.traceAt left position).source 1⟩
        ⟨conj (leftLocal (Surface.Sewing.Bilinear.Errors.traceAt left position).source 2), rightLocal
          (Surface.Sewing.Bilinear.Errors.traceAt left position).source 2⟩
      else 0)) < target := by
  have small : request.error ≤ 1 := by
    rw [request.error_eq]; exact Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _
      _
  have estimate := Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
    (fun position => if keep position then
      triangleWedgeArea (sample.values patch.cut.triangles[position.val].first)
        (sample.values patch.cut.triangles[position.val].second)
        (sample.values patch.cut.triangles[position.val].third) -
      triangleWedgeArea
        ⟨conj (leftLocal (Surface.Sewing.Bilinear.Errors.traceAt left position).source 0), rightLocal
          (Surface.Sewing.Bilinear.Errors.traceAt left position).source 0⟩
        ⟨conj (leftLocal (Surface.Sewing.Bilinear.Errors.traceAt left position).source 1), rightLocal
          (Surface.Sewing.Bilinear.Errors.traceAt left position).source 1⟩
        ⟨conj (leftLocal (Surface.Sewing.Bilinear.Errors.traceAt left position).source 2), rightLocal
          (Surface.Sewing.Bilinear.Errors.traceAt left position).source 2⟩ else 0)
    (fun _ => 32 * (magnitude + 1) * request.error) (by
      intro position
      split
      · exact Surface.Sewing.SewnConjugateErrors.triangle_area_error_at sample position request.nonnegative
          request.error_positive.le small
          (request.trace_bound left leftAccurate position) (request.trace_bound right rightAccurate position) (bounded
            position)
      · rw [Gaussian.Norm.Basic.normSq_zero]
        exact Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by
          decide +kernel) (add_nonneg request.nonnegative (by decide))) request.error_positive.le)
  rw [Purelib.Algebra.FiniteSum.Fin.Rational.sum_constant, ← request.weight_eq] at estimate
  have weighted : request.weight * request.error ≤
      Rational.Budget.Aggregate.perTerm target patch.cut.triangles.length := by
    have errorLe : request.error ≤ Rational.Budget.Aggregate.perTerm
        (Rational.Budget.Weighted.allowance target request.weight) patch.cut.triangles.length := by
      rw [request.error_eq]
      exact Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _
    exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe request.weight_nonnegative).trans
      (WeightedAggregateBudget.weighted_perTerm_le request.positive request.weight_nonnegative _)
  have nonnegative := Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le patch.cut.triangles.length)
  exact estimate.trans_lt ((Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct weighted nonnegative) nonnegative).trans_lt
      (Rational.Budget.Aggregate.count_mul_perTerm_lt request.positive _))

end Purelib.Riemann.Readings.SelectedConjugateRequests
