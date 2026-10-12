module
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Affine

import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Normalization.InverseModelEdgeTransition
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
public import Purelib.Riemann.Integration.PrimitiveEdgeControl
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Data.Int.Cast.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Data.Nat.Init
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Mathlib.Algebra.Group.Defs
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Gaussian.Norm.Basic

open Purelib.Geometry.Rational

open Purelib.Riemann.Comparison

open Purelib.Riemann.Comparison.PrimitiveEdgeComparison

open Purelib.Riemann.Integration

open Purelib.Riemann.Normalization

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Cut

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.PrimitiveSewing

@[expose] public section

/-!
# Analytic local-model estimates for actual sewn seam charges

The selected boundary owners retain their original local increments. Once
those two readbacks identify the local polynomial models on their common
oriented segment, the model residuals bound the new seam charge. Earlier
sewing errors are retained explicitly. The sheet sign and reversal of the
second boundary occurrence are part of the readback equations, not inferred
from projected endpoint coincidence.
-/

namespace Purelib.Topology.Surface.Sewing.SewnPrimitiveAnalyticControl

open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
open Purelib.Riemann.Integration.PrimitiveEdgeControl

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian Polynomial Box half correction
  residualStep correction_residual residualStep_contracts Model)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces (FaceBank)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (RegionClearance PrimitiveOverlapBounds DensePrimitive
  PrimitiveEdgeAnchor)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Surface.Cut.Patch (CutPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary (TriangleEdgeOwner)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing.EndpointGluing (PrimitiveSew)

variable {polynomial numerator leftCoefficient rightCoefficient : InverseRootPolynomial.Polynomial}
  {leftBox rightBox : InverseRootPolynomial.Box} {clearance : PrimitiveEdgeComparison.RegionClearance polynomial
    leftBox}
  {bounds : PrimitiveEdgeComparison.PrimitiveOverlapBounds clearance numerator}
  {leftModel : InverseRootPolynomial.Model polynomial leftBox} {rightModel : InverseRootPolynomial.Model polynomial
    rightBox}
  {start finish : InverseRootPolynomial.Gaussian} {edge : InverseModelEdgeTransition.EdgeTransition leftModel rightModel
    start finish}
  {leftPrimitive : PrimitiveEdgeComparison.DensePrimitive leftCoefficient leftBox} {rightPrimitive :
    PrimitiveEdgeComparison.DensePrimitive rightCoefficient rightBox}
  {anchor : PrimitiveEdgeComparison.PrimitiveEdgeAnchor edge leftPrimitive.value rightPrimitive.value}
  {vertexCount faceCount : Nat} {faces : Fin faceCount → Stokes.OrientedTriangle vertexCount}
  {localValues : Fin faceCount → PrimitiveSewing.PrimitiveValues 3}
  {firstIndices secondIndices : List (Fin faceCount)}
  {firstBoundary secondBoundary : List (Stokes.OrientedEdge vertexCount)}
  {first : Patch.CutPatch faces firstIndices firstBoundary} {second : Patch.CutPatch faces secondIndices secondBoundary}
  {leftValues : PrimitiveSewing.PrimitiveValues first.count} {rightValues : PrimitiveSewing.PrimitiveValues
    second.count}
  {leftBank : SewnPrimitiveFaces.FaceBank first localValues leftValues} {rightBank : SewnPrimitiveFaces.FaceBank second
    localValues rightValues}
  {firstEdge : Stokes.OrientedEdge first.count} {secondEdge : Stokes.OrientedEdge second.count}
  {firstOwner : SewnPrimitiveBoundary.TriangleEdgeOwner first.triangles firstEdge} {secondOwner :
    SewnPrimitiveBoundary.TriangleEdgeOwner second.triangles secondEdge}

/-- Any two rational cuts are permitted, including reversed and degenerate segments. Only the genuinely local polynomial
readbacks are required; the actual sewn increments may already carry nonzero errors. -/
theorem sewn_charge_le (control : Riemann.Integration.PrimitiveEdgeControl bounds edge leftPrimitive rightPrimitive
  anchor)
    (joined : EndpointGluing.PrimitiveSew leftValues rightValues firstEdge secondEdge)
    (left : FaceBank.EdgeReading leftBank firstOwner) (right : FaceBank.EdgeReading rightBank secondOwner)
    {firstParameter lastParameter : InverseRootPolynomial.Coordinate}
    (firstInside : 0 ≤ firstParameter ∧ firstParameter ≤ 1) (lastInside : 0 ≤ lastParameter ∧ lastParameter ≤ 1)
    (left_eq : left.localIncrement =
      leftPrimitive.value.eval (Affine.line start (finish - start) lastParameter) -
        leftPrimitive.value.eval (Affine.line start (finish - start) firstParameter))
    (right_eq : right.localIncrement = edge.sign *
      (rightPrimitive.value.eval (Affine.line start (finish - start) firstParameter) -
        rightPrimitive.value.eval (Affine.line start (finish - start) lastParameter))) :
    joined.charge ≤ 16 * (left.trace.allowance + right.trace.allowance) +
      2 * control.drift * (lastParameter - firstParameter) ^ 2 := by
  have mismatch := EdgeTransition.primitive_increment_le edge bounds leftPrimitive rightPrimitive
    control.leftCoefficient_eq control.rightCoefficient_eq lastInside firstInside
  rw [← control.drift_eq] at mismatch
  have same : left.localIncrement + right.localIncrement =
      (leftPrimitive.value.eval (Affine.line start (finish - start) lastParameter) -
        leftPrimitive.value.eval (Affine.line start (finish - start) firstParameter)) -
      edge.sign * (rightPrimitive.value.eval (Affine.line start (finish - start) lastParameter) -
        rightPrimitive.value.eval (Affine.line start (finish - start) firstParameter)) := by
    rw [left_eq, right_eq]
    ring1
  rw [← same] at mismatch
  have mismatchDirect : Data.Gaussian.Norm.Basic.normSq (left.localIncrement + right.localIncrement) ≤ control.drift *
    (lastParameter -
    firstParameter) ^ 2 := by
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact mismatch
  exact (SewnPrimitiveBoundary.seam_charge_le joined left right (control.drift * (lastParameter - firstParameter) ^ 2)
    mismatchDirect).trans_eq (by ring1)

end Purelib.Topology.Surface.Sewing.SewnPrimitiveAnalyticControl
