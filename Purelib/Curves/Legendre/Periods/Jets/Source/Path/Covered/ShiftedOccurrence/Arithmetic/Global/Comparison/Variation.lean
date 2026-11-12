module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Comparison
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs.Variation
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Gaussian.Norm.Components.Maximum
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Variation-weighted comparison of the same two actual target geometries

The retained CommonRestrictions product and both independent preparations
remain the original inputs. The existing per-parent signed comparison pays
each difference. Maximum-coordinate parent weights then remove all parent
and child count factors from the same literal source-list sample bound.
-/

namespace
  Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.ValueBlocks.CommonRestrictions

open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Meshes
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint finishPoint)

/-- The same two acquired target words obey a variation bound through their original stored common restrictions.

Every actual source/target index and cache remains an input. Nonnegative
original physical variation weights, including zero weights, replace the
loose count-times-cost summation without constructing any new restriction
or comparing coordinate labels instead of the retained signed queries.
-/
public theorem integral_difference_variation_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {firstWidths lastWidths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : Riemann.Topology.PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {firstSpatial lastSpatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {firstSourceCurrent firstSourceFloor firstSourceRootStage firstTargetCurrent : Nat}
    {firstTargetFloor firstTargetRootStage : Nat}
    {lastSourceCurrent lastSourceFloor lastSourceRootStage lastTargetCurrent lastTargetFloor lastTargetRootStage : Nat}
    {firstSource : StageAttempt.Requested covered chain firstSourceCurrent firstSourceFloor firstSourceRootStage
      (firstSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {lastSource : StageAttempt.Requested covered chain lastSourceCurrent lastSourceFloor lastSourceRootStage
      (lastSpatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {firstNext : StageAttempt.Requested.Shifted (target := target) firstSource ranges allocation admitted
      firstWidths roots
      firstTargetCurrent firstTargetFloor firstTargetRootStage}
    {lastNext : StageAttempt.Requested.Shifted (target := target) lastSource ranges allocation admitted lastWidths roots
      lastTargetCurrent lastTargetFloor lastTargetRootStage}
    (firstRetained : ValueBlocks (next := firstNext)) (lastRetained : ValueBlocks (next := lastNext))
    {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets firstNext.requested.request.chain.path firstStage}
    {lastTargets : CellEndpoints.Targets lastNext.requested.request.chain.path lastStage}
    (firstPrepared : PreparedParents firstNext.requested.request.covered firstTargetFloor firstTargets)
    (lastPrepared : PreparedParents lastNext.requested.request.covered lastTargetFloor lastTargets)
    (cached : CommonRestrictions firstRetained lastRetained firstPrepared lastPrepared)
    (channel : Fin 6) :
    Norm.Basic.normSq
      ((PathModel.mk ((PreparedParents.sources firstNext.requested.request.covered firstPrepared
          firstNext.requested.request.chain).cells channel)).integralSample -
        (PathModel.mk ((PreparedParents.sources lastNext.requested.request.covered lastPrepared
          lastNext.requested.request.chain).cells channel)).integralSample) ≤
      32 * (firstTargets.localBound + lastTargets.localBound) * variation (parent :: parents) ^ 2 := by
  let firstValues := fun outer => (PathModel.mk (firstRetained.groupedCells firstPrepared channel outer)).integralSample
  let lastValues := fun outer => (PathModel.mk (lastRetained.groupedCells lastPrepared channel outer)).integralSample
  let values := fun outer => firstValues outer - lastValues outer
  let weights := fun outer : Fin (parent :: parents).length => Norm.Components.maximum
    ((finishPoint ((parent :: parents)[outer.val]'outer.isLt)).coordinate -
      (startPoint ((parent :: parents)[outer.val]'outer.isLt)).coordinate)
  have coefficient : 0 ≤ 16 * (firstTargets.localBound + lastTargets.localBound) :=
    Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Order.Arithmetic.add_pos_of_pos_of_nonneg_direct firstTargets.localBound_positive
        lastTargets.localBound_positive.le).le
  have bounded (outer : Fin (parent :: parents).length) : Norm.Basic.normSq (values outer) ≤
      (32 * (firstTargets.localBound + lastTargets.localBound)) * (weights outer) ^ 2 := by
    have original := parent_difference_le (firstNext := firstNext) (lastNext := lastNext)
      firstRetained lastRetained firstPrepared lastPrepared cached channel outer
    have cost := Norm.Components.normSq_le_twice_maximum_sq
      ((finishPoint ((parent :: parents)[outer.val]'outer.isLt)).coordinate -
        (startPoint ((parent :: parents)[outer.val]'outer.isLt)).coordinate)
    exact original.trans ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct cost coefficient).trans_eq
      (by ring1))
  have finite := Norm.Weighted.normSq_sumFin_weighted values weights
    (fun outer => Norm.Components.maximum_nonnegative _) bounded
  have samples := (congrArg₂ (fun first last : Canonical => first - last)
    (firstRetained.sample_eq_groups (next := firstNext) firstPrepared channel)
    (lastRetained.sample_eq_groups (next := lastNext) lastPrepared channel)).trans (sumFin_sub _ _).symm
  exact (congrArg Norm.Basic.normSq samples).trans_le finite

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.ValueBlocks.CommonRestrictions
