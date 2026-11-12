module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings

open Purelib.Data.Rat

open Purelib.Riemann.Branches

open Purelib.Riemann.Integration

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Even-degree chart edges retain the shared sheet reading. The comparison
with the unweighted polynomial edge pays both its square residual and its
variation along the edge; root closure alone does not remove either error. -/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Normalization
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Point Join)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings (PairedChartRequest)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings.PairedChartRequest (Evaluation)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeArea)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_mul normSq_nonneg)
open Purelib.Data.Rat.Fraction.Compatibility

/-- Scaling the two original paired vertices multiplies their bilinear edge area by the product of the scalars. -/
private theorem scaled_edge (s t : Gaussian) (a b : PrimitivePoint) :
    edgeArea ⟨s * a.left, s * a.right⟩ ⟨t * b.left, t * b.right⟩ = s * t *
      edgeArea a b := by
  unfold edgeArea
  ring1

/-- The sheet-product defect is controlled without identifying finite readings with exact signs or assuming that
adjacent signs agree. -/
theorem regular_edge_error (s t : Gaussian) (a b : PrimitivePoint)
    {squareError : Coordinate} (square : normSq (s * s - 1) ≤
      squareError) :
    normSq (edgeArea ⟨s * a.left, s * a.right⟩ ⟨t * b.left, t * b.right⟩ -
      edgeArea a b) ≤
      (2 * (normSq s * normSq (t - s) +
        squareError)) * normSq (edgeArea a b) := by
  have product : s * t - 1 = s * (t - s) + (s * s - 1) := by ring1
  have bound := (Data.Gaussian.Norm.Bounds.normSq_add_le_two (s * (t - s)) (s * s - 1)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct (le_refl _)
      square) (by decide))
  rw [normSq_mul, ← product] at bound
  rw [scaled_edge, show s * t * edgeArea a b -
    edgeArea a b = (s * t - 1) * edgeArea a b by ring1,
    normSq_mul]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct bound (normSq_nonneg _)

variable {genus count otherCount index : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {otherParent : PreparedSubdivisionModelCore.CenteredEdge curve other}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch otherParent}
  {data : UniformReciprocalModels.Data patch count} {otherData :
    UniformReciprocalModels.Data otherPatch otherCount}
  {edge otherEdge : ParameterEdge}
  {cell : Cell data edge} {otherCell :
    Cell otherData otherEdge}
  {model : RootModel cell} {otherModel :
    RootModel otherCell}
  {box otherBox : Geometry.Rational.Box}
  {sample : Primitives.Sample cap differential index box}
  {otherSample : Primitives.Sample cap other index otherBox}
  {parameter otherParameter target : Coordinate} {floor stage : Nat}
  {leftPoint : Point cap model parameter} {rightPoint :
    Point cap otherModel otherParameter}
  {joined : Join leftPoint rightPoint} {request :
    PairedChartRequest joined sample otherSample
    target floor}

/-- Both components use the already cached first sheet reading. -/
theorem Evaluation.regular_chartPoint (readings : Evaluation request stage)
    (regular : HyperellipticReciprocal.originOrder curve = 0) :
    readings.chartPoint =
      ⟨readings.first.coordinate * sample.primitive.value.eval (parent.edge.point parameter)⁻¹,
       readings.first.coordinate * otherSample.primitive.value.eval (parent.edge.point parameter)⁻¹⟩ := by
  apply congrArg₂ PrimitivePoint.mk
  · exact readings.firstChart.value_eq.trans (if_pos regular)
  · exact (readings.otherChart.value_eq.trans (if_pos regular)).trans
      (congrArg (fun coordinate => coordinate * otherSample.primitive.value.eval (parent.edge.point parameter)⁻¹)
        readings.coordinate_eq.symm)

/-- The actual request, not an exact-sign assumption, supplies this budget. -/
theorem Evaluation.regular_square (readings : Evaluation request stage)
    (regular : HyperellipticReciprocal.originOrder curve = 0) :
    normSq (readings.first.coordinate * readings.first.coordinate - 1) < target := by
  have bound := readings.firstChart.square_accurate
  simpa only [regular, pow_zero] using bound

/-- Apply the defect estimate to two retained readings of one common-cover interval. The remaining sign-step error is
explicit, not a supplied equality between their independently read coordinates. -/
theorem Evaluation.regular_edge_bound (readings : Evaluation request stage)
    {nextParameter nextOtherParameter nextTarget : Coordinate} {nextFloor nextStage : Nat}
    {nextLeft : Point cap model nextParameter} {nextRight : Point cap otherModel nextOtherParameter}
    {nextJoin : Join nextLeft nextRight}
    {nextRequest : PairedChartRequest nextJoin sample otherSample nextTarget nextFloor}
    (next : Evaluation nextRequest nextStage)
    (regular : HyperellipticReciprocal.originOrder curve = 0) :
    let firstPolynomial : PrimitivePoint :=
      ⟨sample.primitive.value.eval (parent.edge.point parameter)⁻¹,
       otherSample.primitive.value.eval (parent.edge.point parameter)⁻¹⟩
    let lastPolynomial : PrimitivePoint :=
      ⟨sample.primitive.value.eval (parent.edge.point nextParameter)⁻¹,
       otherSample.primitive.value.eval (parent.edge.point nextParameter)⁻¹⟩
    normSq (edgeArea readings.chartPoint next.chartPoint - edgeArea
      firstPolynomial lastPolynomial) ≤
      (2 * (normSq readings.first.coordinate *
        normSq (next.first.coordinate - readings.first.coordinate) + target)) *
        normSq (edgeArea firstPolynomial lastPolynomial) := by
  intro firstPolynomial lastPolynomial
  rw [Evaluation.regular_chartPoint readings regular,
    Evaluation.regular_chartPoint next regular]
  exact regular_edge_error _ _ firstPolynomial
    lastPolynomial (Evaluation.regular_square
    readings regular).le

/-- At an owned common endpoint the two regular-chart pairs are collinear, even if their cached sheet readings differ.
Thus the joining edge has exactly zero bilinear area. This is not equality of the readings or their increments. -/
theorem Evaluation.regular_join_area (readings : Evaluation request stage)
    {nextCount nextOtherCount : Nat}
    {nextParent : PreparedSubdivisionModelCore.CenteredEdge curve differential}
    {nextOtherParent : PreparedSubdivisionModelCore.CenteredEdge curve other}
    {nextPatch : PreparedPatch nextParent}
    {nextOtherPatch : PreparedPatch nextOtherParent}
    {nextData : UniformReciprocalModels.Data nextPatch nextCount}
    {nextOtherData : UniformReciprocalModels.Data nextOtherPatch nextOtherCount}
    {nextEdge nextOtherEdge : ParameterEdge}
    {nextCell : Cell nextData nextEdge} {nextOtherCell : Cell
      nextOtherData nextOtherEdge}
    {nextModel : RootModel nextCell} {nextOtherModel :
      RootModel nextOtherCell}
    {nextParameter nextOtherParameter nextTarget : Coordinate} {nextFloor nextStage : Nat}
    {nextLeft : Point cap nextModel nextParameter} {nextRight : Point cap nextOtherModel
      nextOtherParameter}
    {nextJoin : Join nextLeft nextRight}
    {nextSample : Primitives.Sample cap differential index box}
    {nextOtherSample : Primitives.Sample cap other index otherBox}
    {nextRequest : PairedChartRequest nextJoin nextSample nextOtherSample nextTarget nextFloor}
    (next : Evaluation nextRequest nextStage) (owners : Join leftPoint nextLeft)
    (firstSample : nextSample = sample) (secondSample : nextOtherSample = otherSample)
    (regular : HyperellipticReciprocal.originOrder curve = 0) :
    edgeArea readings.chartPoint next.chartPoint = 0 := by
  rw [Evaluation.regular_chartPoint readings regular,
    Evaluation.regular_chartPoint next regular]
  have scalar (s t a b c d : Gaussian) (first : a = c) (second : b = d) :
      edgeArea ⟨s * a, s * b⟩ ⟨t * c, t * d⟩ = 0 := by
    rw [first, second]
    unfold edgeArea
    ring1
  exact scalar _ _ _ _ _ _
    ((congrArg (fun point => sample.primitive.value.eval point⁻¹) owners.point_eq).trans
      (congrArg (fun retained : Primitives.Sample cap differential index box =>
        retained.primitive.value.eval (nextParent.edge.point nextParameter)⁻¹) firstSample.symm))
    ((congrArg (fun point => otherSample.primitive.value.eval point⁻¹) owners.point_eq).trans
      (congrArg (fun retained : Primitives.Sample cap other index otherBox =>
        retained.primitive.value.eval (nextParent.edge.point nextParameter)⁻¹) secondSample.symm))

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges
