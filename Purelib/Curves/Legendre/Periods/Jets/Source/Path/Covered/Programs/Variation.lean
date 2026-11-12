module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
public import Purelib.Data.Gaussian.Norm.Components.Maximum
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Finite source comparisons paid by maximum-coordinate variation

The original ordered parent displacements give nonnegative rational
weights. Weighted quadrance bounds retain every actual sample and allow
zero displacements. No parent count multiplies the quantitative bound.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint finishPoint)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

/-- Sum the maximum absolute coordinate of each original ordered physical parent displacement. -/
@[expose] def variation {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) : Rational :=
  sumFin (fun index : Fin parents.length => Norm.Components.maximum
    ((finishPoint (parents[index.val]'index.isLt)).coordinate -
      (startPoint (parents[index.val]'index.isLt)).coordinate))

/-- The actual finite maximum-coordinate variation is nonnegative, including constant or empty spines. -/
theorem variation_nonnegative {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) : 0 ≤ variation parents :=
  Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _
    (fun _index => Norm.Components.maximum_nonnegative _)

/-- Compute a source comparison scale from the square of the actual retained rational variation. -/
def variationErrorScale {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) : Rational :=
  64 * variation parents ^ 2

/-- The variation scale is nonnegative without a positive displacement or parent-count assumption. -/
theorem variationErrorScale_nonnegative
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    (parents : List (CenteredEdge (Fibre.frameCurve frame) basis)) : 0 ≤ variationErrorScale parents :=
  Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Order.Arithmetic.sq_nonneg_direct _)

/-- The same actual source samples have a comparison bound independent of the parent count.

Original per-parent query comparisons supply each local error. Twice the
squared maximum coordinate bounds each displacement quadrance; weighted
finite summation uses their exact total variation, including zero weights.
-/
theorem integral_difference_variation_le
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    (covered : CoveredParents count parents) {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets original firstStage} {lastTargets : CellEndpoints.Targets original lastStage}
    (first : PreparedParents covered floor firstTargets) (last : PreparedParents covered floor lastTargets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish))
    (channel : Fin 6) :
    Norm.Basic.normSq ((PathModel.mk ((sources covered first chain).cells channel)).integralSample -
      (PathModel.mk ((sources covered last chain).cells channel)).integralSample) ≤
        32 * (firstTargets.localBound + lastTargets.localBound) * variation parents ^ 2 := by
  let weights := fun index : Fin parents.length => Norm.Components.maximum
    ((finishPoint (parents[index.val]'index.isLt)).coordinate -
      (startPoint (parents[index.val]'index.isLt)).coordinate)
  let values := fun index : Fin parents.length =>
    ((first.entry index).preparation.cell.models.cell channel).integralSample -
      ((last.entry index).preparation.cell.models.cell channel).integralSample
  have coefficient : 0 ≤ 16 * (firstTargets.localBound + lastTargets.localBound) :=
    Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Order.Arithmetic.add_pos_of_pos_of_nonneg_direct firstTargets.localBound_positive
        lastTargets.localBound_positive.le).le
  have bounded (index : Fin parents.length) : Norm.Basic.normSq (values index) ≤
      (32 * (firstTargets.localBound + lastTargets.localBound)) * (weights index) ^ 2 := by
    have original := (first.entry index).integral_difference_le (last.entry index) channel
    have cost := Norm.Components.normSq_le_twice_maximum_sq
      ((finishPoint (parents[index.val]'index.isLt)).coordinate -
        (startPoint (parents[index.val]'index.isLt)).coordinate)
    exact original.trans ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct cost coefficient).trans_eq
      (by ring1))
  have paid := Norm.Weighted.normSq_sumFin_weighted values weights
    (fun _index => Norm.Components.maximum_nonnegative _) bounded
  have same := (congrArg₂ (fun first last : Canonical => first - last)
    (integralSample_eq_sumFin covered first chain channel)
    (integralSample_eq_sumFin covered last chain channel)).trans (sumFin_sub _ _).symm
  exact (congrArg Norm.Basic.normSq same).trans_le paid

/-- Two genuinely paid source allocations give the computed variation scale on the same actual sample difference.

The displayed accuracy bounds concern the actual original Targets. No
sample, cache or allowance is changed, and a zero variation remains valid.
-/
theorem integral_difference_variation_accuracy_le
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish}
    (covered : CoveredParents count parents) {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets original firstStage} {lastTargets : CellEndpoints.Targets original lastStage}
    (first : PreparedParents covered floor firstTargets) (last : PreparedParents covered floor lastTargets)
    {start finish : LiftedPoint 2} (chain : CenteredPathChain parents (start := start) (finish := finish))
    (channel : Fin 6) (accuracy : Rational)
    (firstPaid : firstTargets.localBound ≤ accuracy) (lastPaid : lastTargets.localBound ≤ accuracy) :
    Norm.Basic.normSq ((PathModel.mk ((sources covered first chain).cells channel)).integralSample -
      (PathModel.mk ((sources covered last chain).cells channel)).integralSample) ≤
        variationErrorScale parents * accuracy := by
  have allowance := Order.Arithmetic.add_le_add_direct firstPaid lastPaid
  have bound := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct allowance
    (Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 32)
      (Order.Arithmetic.sq_nonneg_direct (variation parents)))
  have paid := integral_difference_variation_le covered first last chain channel
  exact paid.trans ((show 32 * (firstTargets.localBound + lastTargets.localBound) * variation parents ^ 2 =
    (32 * variation parents ^ 2) * (firstTargets.localBound + lastTargets.localBound) by ring1).trans_le
      (bound.trans_eq (by unfold variationErrorScale; ring1)))

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents

end
