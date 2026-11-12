module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Block
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Cells
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Certificates
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Integration.Path.Primitive.Cells.Targets.Weighted
import Purelib.Integration.Path.Lifted.Model
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.List.Flatten.Table
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Actual target programmes with original-parent weighted error scales

The shifted geometry, covered patches, centered chain and local-to-global
occurrence positions stay fixed. Only the actual source allocations change
with programme stage. The selected original Request contributes its whole
stored preparation rather than another execution of that request.

Nonnegative original child widths sum to one inside each original source
parent. Weighted finite Cauchy therefore removes the adaptive child count
from sample comparisons. The remaining scale depends only on the original
source parents and their displacement costs. Algebraic certification uses
the same target query factories and literal six cell lists.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib.Riemann.Topology
open Purelib.Algebra.FiniteSum.Rational

open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Path.Jets (UniformPathCertificates)
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
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}

namespace ValueBlocks

variable (retained : ValueBlocks (next := next))

/-- The original target parent spine is the exact ordered flattening of the retained local children. -/
private theorem targetParents_eq :
    next.requested.request.shape.val.1 :: next.requested.request.shape.val.2 =
      (List.ofFn (fun outer => ValueBlock.children (next := next) outer)).flatten :=
  next.requested.request.shape.property.symm.trans
    ((congrArg (fun result => result.parents) next.geometry_eq).trans
      (build_parents source.prepared ranges allocation admitted widths next.blocks chain roots))

/-- The same actual global child cost is its squared original width times its original parent cost. -/
theorem child_cost (outer : Fin (parent :: parents).length)
    (inner : Fin (ValueBlock.children (next := next) outer).length) :
    PreparedParent.cost
      ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2)[
        ((retained.block outer).position inner).sourceIndex.val]'
          ((retained.block outer).position inner).sourceIndex.isLt) =
      (((retained.block outer).interval inner).finish - ((retained.block outer).interval inner).start) ^ 2 *
        PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt) := by
  let channel := Specification.Table.baseIndex (0 : Fin 2) (0 : Fin 2)
  have targetCost := (next.requested.prepared.entry
    ((retained.block outer).position inner).sourceIndex).cell_cost channel
  have sourceCost := (source.prepared.entry outer).cell_cost channel
  have actual := (retained.block outer).displacement_normSq inner 0 0
  exact targetCost.symm.trans (actual.trans
    (congrArg (fun cost : Rational =>
      (((retained.block outer).interval inner).finish - ((retained.block outer).interval inner).start) ^ 2 * cost)
      sourceCost))

/-- Squared original child widths have total at most one, including zero-width occurrences. -/
theorem width_squares_le_one (outer : Fin (parent :: parents).length) :
    sumFin (fun inner => (((retained.block outer).interval inner).finish -
      ((retained.block outer).interval inner).start) ^ 2) ≤ 1 := by
  let weights := fun inner => ((retained.block outer).interval inner).finish -
    ((retained.block outer).interval inner).start
  have bounded : ∀ inner, weights inner ≤ 1 := fun inner =>
    (FiniteSum.Rational.Order.weight_le_sum weights (retained.block outer).width_nonnegative inner).trans_eq
      (retained.block outer).sum_widths
  have squared (inner) : weights inner ^ 2 ≤ weights inner := by
    calc
      _ = weights inner * weights inner := by ring1
      _ ≤ weights inner * 1 := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounded inner)
        ((retained.block outer).width_nonnegative inner)
      _ = _ := Field.mul_one_direct _
  have squares := FiniteSum.Rational.Order.IndexedBudget.sumFin_le squared
  exact squares.trans_eq (retained.block outer).sum_widths

/-- The shifted child displacement-cost total is bounded by the SAME original source-parent cost total.

Exact ordered parent flattening and original occurrence positions transport
the costs. Each block contributes its original cost times a sum of squared
nonnegative widths at most one; no adaptive count is introduced.
-/
theorem target_cost_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) :
    displacementCost (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2) ≤
      displacementCost (parent :: parents) := by
  let words := fun outer : Fin (parent :: parents).length => ValueBlock.children (next := next) outer
  have grouped :
      displacementCost (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2) =
        sumFin (fun outer => Squares.coordinateSum
          ((words outer).map PreparedParent.cost)) := by
    calc
      _ = Squares.coordinateSum
          ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).map
            PreparedParent.cost) :=
        (Squares.coordinateSum_map_eq_sumFin _ PreparedParent.cost).symm
      _ = Squares.coordinateSum ((List.ofFn words).flatten.map PreparedParent.cost) :=
        congrArg (fun entries => Squares.coordinateSum (entries.map PreparedParent.cost))
          (targetParents_eq (next := next))
      _ = _ := Squares.coordinateSum_map_flatten_ofFn words PreparedParent.cost
  have blocks (outer : Fin (parent :: parents).length) :
      Squares.coordinateSum ((words outer).map PreparedParent.cost) ≤
        PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt) := by
    have costs (inner : Fin (words outer).length) :
        PreparedParent.cost ((words outer)[inner.val]'inner.isLt) =
          (((retained.block outer).interval inner).finish - ((retained.block outer).interval inner).start) ^ 2 *
            PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt) :=
      (congrArg PreparedParent.cost ((retained.block outer).position inner).property.1).symm.trans
        (retained.child_cost outer inner)
    calc
      _ = sumFin (fun inner : Fin (words outer).length =>
          PreparedParent.cost ((words outer)[inner.val]'inner.isLt)) :=
        Squares.coordinateSum_map_eq_sumFin _ PreparedParent.cost
      _ = sumFin (fun inner =>
          (((retained.block outer).interval inner).finish - ((retained.block outer).interval inner).start) ^ 2 *
            PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt)) :=
        FiniteSum.Fin.sumFin_congr costs
      _ = sumFin (fun inner =>
          (((retained.block outer).interval inner).finish - ((retained.block outer).interval inner).start) ^ 2) *
            PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt) := FiniteSum.Fin.sumFin_mul_right _ _
      _ ≤ 1 * PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt) :=
        Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (retained.width_squares_le_one outer)
          (PreparedParent.cost_nonnegative _)
      _ = _ := by ring1
  exact grouped.trans_le (FiniteSum.Rational.Order.IndexedBudget.sumFin_le blocks)

section Preparations

variable {preparationFloor firstStage : Nat}
    {firstTargets : CellEndpoints.Targets next.requested.request.chain.path firstStage}
    (first : PreparedParents next.requested.request.covered preparationFloor firstTargets)

/-- Read actual target preparation cells by their SAME retained original block/local occurrences. -/
@[expose] def groupedCells (channel : Fin 6) (outer : Fin (parent :: parents).length) : List CellModel :=
  List.ofFn (fun inner =>
    (first.entry ((retained.block outer).position inner).sourceIndex).preparation.cell.models.cell channel)

/-- The exact global target list is the ordered flattening of its SAME retained block occurrence views. -/
theorem cells_eq_groups
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) {preparationFloor firstStage : Nat}
    {firstTargets : CellEndpoints.Targets next.requested.request.chain.path firstStage}
    (first : PreparedParents next.requested.request.covered preparationFloor firstTargets) (channel : Fin 6) :
    (sources next.requested.request.covered first next.requested.request.chain).cells channel =
      (List.ofFn (fun outer => retained.groupedCells first channel outer)).flatten := by
  let words := fun outer : Fin (parent :: parents).length => ValueBlock.children (next := next) outer
  let values := fun index : Fin
      (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length =>
    (first.entry index).preparation.cell.models.cell channel
  let positions := fun outer : Fin (parent :: parents).length =>
    fun inner : Fin (words outer).length => ((retained.block outer).position inner).sourceIndex
  have offset (outer : Fin (parent :: parents).length) (inner : Fin (words outer).length) :
      (positions outer inner).val = ((List.ofFn words).take outer.val).flatten.length + inner.val :=
    ((retained.block outer).position inner).property.2
  exact (cells_eq_ofFn next.requested.request.covered first next.requested.request.chain channel).trans
    (Data.List.Flatten.ofFn_grouped words (congrArg List.length (targetParents_eq (next := next)))
      values positions offset)

/-- The actual global target sample is the finite sum of its SAME ordered original-parent group samples. -/
theorem sample_eq_groups
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) {preparationFloor firstStage : Nat}
    {firstTargets : CellEndpoints.Targets next.requested.request.chain.path firstStage}
    (first : PreparedParents next.requested.request.covered preparationFloor firstTargets) (channel : Fin 6) :
    (PathModel.mk ((sources next.requested.request.covered first next.requested.request.chain).cells
      channel)).integralSample =
      sumFin (fun outer => (PathModel.mk (retained.groupedCells first channel outer)).integralSample) := by
  rewrite [retained.cells_eq_groups first channel]
  exact PathModel.integralSample_flatten_ofFn _

section Comparisons

variable {lastStage : Nat}
    {lastTargets : CellEndpoints.Targets next.requested.request.chain.path lastStage}
    (last : PreparedParents next.requested.request.covered targetFloor lastTargets)

/-- Independent model floors obey the same retained-width comparison on each original parent block.

Both actual preparation products keep their own floors. The original
positions, child costs and nonnegative widths pay the same finite weighted
sum, including repeated and zero-width occurrences.
-/
theorem independent_block_difference_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) {firstFloor firstStage : Nat}
    {firstTargets : CellEndpoints.Targets next.requested.request.chain.path firstStage}
    (first : PreparedParents next.requested.request.covered firstFloor firstTargets) {lastFloor lastStage : Nat}
    {lastTargets : CellEndpoints.Targets next.requested.request.chain.path lastStage}
    (last : PreparedParents next.requested.request.covered lastFloor lastTargets)
    (channel : Fin 6) (outer : Fin (parent :: parents).length) :
    Norm.Basic.normSq
      ((PathModel.mk (retained.groupedCells first channel outer)).integralSample -
        (PathModel.mk (retained.groupedCells last channel outer)).integralSample) ≤
      16 * (firstTargets.localBound + lastTargets.localBound) *
        PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt) := by
  let coefficient : Rational := 16 * (firstTargets.localBound + lastTargets.localBound)
  let originalCost : Rational := PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt)
  let childWidth : Fin (ValueBlock.children (next := next) outer).length → Rational := fun inner =>
    ((retained.block outer).interval inner).finish - ((retained.block outer).interval inner).start
  let values : Fin (ValueBlock.children (next := next) outer).length → CellModel := fun inner =>
    (first.entry ((retained.block outer).position inner).sourceIndex).preparation.cell.models.cell channel
  let others : Fin (ValueBlock.children (next := next) outer).length → CellModel := fun inner =>
    (last.entry ((retained.block outer).position inner).sourceIndex).preparation.cell.models.cell channel
  have pointwise (inner : Fin (ValueBlock.children (next := next) outer).length) :
      Norm.Basic.normSq ((values inner).integralSample - (others inner).integralSample) ≤
        (coefficient * originalCost) * (childWidth inner) ^ 2 := by
    have original := PreparedParent.integral_difference_le
      (parameter := parameter + increment) (frame := target)
      (first.entry ((retained.block outer).position inner).sourceIndex)
      (last.entry ((retained.block outer).position inner).sourceIndex) channel
    have childCost := retained.child_cost outer inner
    exact original.trans_eq
      ((congrArg (fun cost : Rational => coefficient * cost) childCost).trans
        ((congrArg (fun product : Rational => coefficient * product)
          (Field.mul_comm ((childWidth inner) ^ 2) originalCost)).trans
            (Field.mul_assoc coefficient originalCost ((childWidth inner) ^ 2)).symm))
  have bound := Norm.Weighted.normSq_sumFin_weighted
    (fun inner => (values inner).integralSample - (others inner).integralSample)
    childWidth (retained.block outer).width_nonnegative pointwise
  have sumDifference :
      sumFin (fun inner => (values inner).integralSample - (others inner).integralSample) =
        sumFin (fun inner => (values inner).integralSample) -
          sumFin (fun inner => (others inner).integralSample) := FiniteSum.Fin.sumFin_sub _ _
  have unitPower : (1 : Rational) ^ 2 = 1 := by decide +kernel
  have densityEq : (coefficient * originalCost) * (sumFin childWidth) ^ 2 = coefficient * originalCost :=
    (congrArg (fun width : Rational => (coefficient * originalCost) * width ^ 2)
      (retained.block outer).sum_widths).trans
        ((congrArg (fun power : Rational => (coefficient * originalCost) * power) unitPower).trans
          (Field.mul_one_direct (coefficient * originalCost)))
  have actual : Norm.Basic.normSq
      ((PathModel.mk (retained.groupedCells first channel outer)).integralSample -
        (PathModel.mk (retained.groupedCells last channel outer)).integralSample) =
      Norm.Basic.normSq (sumFin (fun inner => (values inner).integralSample) -
        sumFin (fun inner => (others inner).integralSample)) :=
    congrArg Norm.Basic.normSq (congrArg₂ (fun left right : Canonical => left - right)
      (PathModel.integralSample_ofFn_eq_sumFin values) (PathModel.integralSample_ofFn_eq_sumFin others))
  exact actual.trans_le
    (((congrArg Norm.Basic.normSq sumDifference).symm.trans_le bound).trans_eq densityEq)

/-- Independent same-patch target preparations have an original-parent weighted local integral comparison.

Each child consumes the two actual independent query factories on the
identical retained target patch. Weighted finite Cauchy uses its original
nonnegative width and exact width sum one, retaining zero-width children.
-/
theorem block_difference_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) {firstStage : Nat}
    {firstTargets : CellEndpoints.Targets next.requested.request.chain.path firstStage}
    (first : PreparedParents next.requested.request.covered targetFloor firstTargets) {lastStage : Nat}
    {lastTargets : CellEndpoints.Targets next.requested.request.chain.path lastStage}
    (last : PreparedParents next.requested.request.covered targetFloor lastTargets)
    (channel : Fin 6) (outer : Fin (parent :: parents).length) :
    Norm.Basic.normSq
      ((PathModel.mk (retained.groupedCells first channel outer)).integralSample -
        (PathModel.mk (retained.groupedCells last channel outer)).integralSample) ≤
      16 * (firstTargets.localBound + lastTargets.localBound) *
        PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt) :=
  retained.independent_block_difference_le first last channel outer

/-- Independently paid target floors have the same original-parent weighted whole-sample comparison.

The actual ordered grouping uses the same retained local-to-global
positions. Only the preparation floors vary; the target cover, physical
sheets, individual query owners and original parent scale are unchanged.
-/
theorem independent_target_difference_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) {firstFloor firstStage : Nat}
    {firstTargets : CellEndpoints.Targets next.requested.request.chain.path firstStage}
    (first : PreparedParents next.requested.request.covered firstFloor firstTargets) {lastFloor lastStage : Nat}
    {lastTargets : CellEndpoints.Targets next.requested.request.chain.path lastStage}
    (last : PreparedParents next.requested.request.covered lastFloor lastTargets) (channel : Fin 6) :
    Norm.Basic.normSq
      ((PathModel.mk ((sources next.requested.request.covered first next.requested.request.chain).cells
        channel)).integralSample -
        (PathModel.mk ((sources next.requested.request.covered last next.requested.request.chain).cells
          channel)).integralSample) ≤
      16 * (firstTargets.localBound + lastTargets.localBound) *
        ((parent :: parents).length : Rational) * displacementCost (parent :: parents) := by
  have actual := Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin
    (fun outer => (PathModel.mk (retained.groupedCells first channel outer)).integralSample)
    (fun outer => (PathModel.mk (retained.groupedCells last channel outer)).integralSample)
    (fun outer => 16 * (firstTargets.localBound + lastTargets.localBound) *
      PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt))
    (retained.independent_block_difference_le first last channel)
  have sample_eq :
      Norm.Basic.normSq
        ((PathModel.mk ((sources next.requested.request.covered first next.requested.request.chain).cells
          channel)).integralSample -
          (PathModel.mk ((sources next.requested.request.covered last next.requested.request.chain).cells
            channel)).integralSample) =
        Norm.Basic.normSq
          (sumFin (fun outer => (PathModel.mk (retained.groupedCells first channel outer)).integralSample) -
            sumFin (fun outer => (PathModel.mk (retained.groupedCells last channel outer)).integralSample)) :=
    congrArg Norm.Basic.normSq (congrArg₂ (fun left right : Canonical => left - right)
      (retained.sample_eq_groups first channel) (retained.sample_eq_groups last channel))
  have costs_eq :
      sumFin (fun outer : Fin (parent :: parents).length =>
        PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt)) =
      displacementCost (parent :: parents) := by rfl
  have extracted :
      sumFin (fun outer : Fin (parent :: parents).length =>
        16 * (firstTargets.localBound + lastTargets.localBound) *
          PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt)) =
      (16 * (firstTargets.localBound + lastTargets.localBound)) * displacementCost (parent :: parents) :=
    (FiniteSum.Fin.sumFin_mul_left (16 * (firstTargets.localBound + lastTargets.localBound))
      (fun outer : Fin (parent :: parents).length =>
        PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt))).trans
      (congrArg (fun total : Rational => (16 * (firstTargets.localBound + lastTargets.localBound)) * total)
        costs_eq)
  have factor_eq :
      ((parent :: parents).length : Rational) *
        sumFin (fun outer : Fin (parent :: parents).length =>
          16 * (firstTargets.localBound + lastTargets.localBound) *
            PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt)) =
      16 * (firstTargets.localBound + lastTargets.localBound) *
        ((parent :: parents).length : Rational) * displacementCost (parent :: parents) :=
    (congrArg (fun total : Rational => ((parent :: parents).length : Rational) * total) extracted).trans
      ((Field.mul_assoc ((parent :: parents).length : Rational)
        (16 * (firstTargets.localBound + lastTargets.localBound)) (displacementCost (parent :: parents))).symm.trans
          (congrArg (fun coefficient : Rational => coefficient * displacementCost (parent :: parents))
            (Field.mul_comm ((parent :: parents).length : Rational)
              (16 * (firstTargets.localBound + lastTargets.localBound)))))
  exact sample_eq.trans_le (actual.trans_eq factor_eq)

/-- The two actual target samples have a fixed ORIGINAL-parent count bound, without a target-child-count factor. -/
theorem target_difference_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) {firstStage : Nat}
    {firstTargets : CellEndpoints.Targets next.requested.request.chain.path firstStage}
    (first : PreparedParents next.requested.request.covered targetFloor firstTargets) {lastStage : Nat}
    {lastTargets : CellEndpoints.Targets next.requested.request.chain.path lastStage}
    (last : PreparedParents next.requested.request.covered targetFloor lastTargets) (channel : Fin 6) :
    Norm.Basic.normSq
      ((PathModel.mk ((sources next.requested.request.covered first next.requested.request.chain).cells
        channel)).integralSample -
        (PathModel.mk ((sources next.requested.request.covered last next.requested.request.chain).cells
          channel)).integralSample) ≤
      16 * (firstTargets.localBound + lastTargets.localBound) *
        ((parent :: parents).length : Rational) * displacementCost (parent :: parents) :=
  retained.independent_target_difference_le first last channel

end Comparisons

/-- The allocation's retained geometric count is exactly the SAME literal target-parent list length. -/
private theorem targets_count
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {firstStage : Nat}
    {firstTargets : CellEndpoints.Targets next.requested.request.chain.path firstStage}
    (first : PreparedParents next.requested.request.covered targetFloor firstTargets) : firstTargets.count =
    (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length := by
  let actual := sources next.requested.request.covered first next.requested.request.chain
  have pathCount := LiftedPath.followedBy_length actual.valueZero_follows
  have listCount := cells_length next.requested.request.covered first next.requested.request.chain (0 : Fin 6)
  change actual.valueZero.length = _ at listCount
  exact firstTargets.count_eq.trans (pathCount.symm.trans listCount)

/-- Original-parent displacement cost lies below the SAME fixed original-parent progressive scale. -/
private theorem original_cost_le_scale :
    displacementCost (parent :: parents) ≤ errorScale (parent :: parents) := by
  have countLower : (1 : Rational) ≤ ((parent :: parents).length : Rational) :=
    Cast.Order.natCast_le_direct (m := 1) (n := (parent :: parents).length)
      (Nat.succ_le_succ (Nat.zero_le parents.length))
  have multiplied := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct countLower
    (by decide +kernel : (0 : Rational) ≤ 32)
  have scaleLower : (1 : Rational) ≤ 32 * ((parent :: parents).length : Rational) :=
    (by decide +kernel : (1 : Rational) ≤ 32).trans
      ((Field.mul_one_direct (32 : Rational)).symm.trans_le multiplied)
  have bounded := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct scaleLower
    (displacementCost_nonnegative (parent :: parents))
  have identity : displacementCost (parent :: parents) = 1 * displacementCost (parent :: parents) := by ring1
  exact identity.trans_le bounded

/-- The actual target aggregate allowance follows the original-parent scale and actual selected-stage allocation. -/
theorem target_allowance_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) {firstStage : Nat}
    {firstTargets : CellEndpoints.Targets next.requested.request.chain.path firstStage}
    (first : PreparedParents next.requested.request.covered targetFloor firstTargets) (channel : Fin 6) :
    (PathModel.mk
      ((sources next.requested.request.covered first next.requested.request.chain).cells channel)).aggregateAllowance ≤
      Geometric.Basic.quarterRadius (errorScale (parent :: parents)) firstStage := by
  have originalCountPayment := firstTargets.count_mul_localBound_le_quarterRadius
  have countPaid :
      ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length : Rational) *
          firstTargets.localBound ≤ Geometric.Basic.quarterRadius 1 firstStage :=
    (congrArg (fun count : Nat => (count : Rational) * firstTargets.localBound)
      (targets_count (next := next) first)).symm.trans_le originalCountPayment
  have countNonnegative : (0 : Rational) ≤
      ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length : Rational) :=
    Cast.Order.natCast_le_direct (m := 0)
      (n := (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length) (Nat.zero_le _)
  have localNonnegative := firstTargets.localBound_positive.le
  calc
    _ = ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length : Rational) *
          firstTargets.localBound *
            displacementCost (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2) :=
      aggregateAllowance_eq next.requested.request.covered first next.requested.request.chain channel
    _ ≤ ((next.requested.request.shape.val.1 :: next.requested.request.shape.val.2).length : Rational) *
          firstTargets.localBound * displacementCost (parent :: parents) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_left_direct retained.target_cost_le
        (Order.Arithmetic.mul_nonneg_direct countNonnegative localNonnegative)
    _ ≤ Geometric.Basic.quarterRadius 1 firstStage * displacementCost (parent :: parents) :=
      Order.Arithmetic.mul_le_mul_of_nonneg_right_direct countPaid
        (displacementCost_nonnegative (parent :: parents))
    _ = Geometric.Basic.quarterRadius (displacementCost (parent :: parents)) firstStage :=
      (congrArg (fun radius : Rational => radius * displacementCost (parent :: parents))
        ((Geometric.Basic.quarterRadius_eq_mul_pow 1 firstStage).trans (Field.one_mul _))).trans
          ((Field.mul_comm _ _).trans
            (Geometric.Basic.quarterRadius_eq_mul_pow (displacementCost (parent :: parents)) firstStage).symm)
    _ ≤ _ := Geometric.Basic.quarterRadius_scale_mono
      (original_cost_le_scale (parent := parent) (parents := parents)) firstStage

end Preparations

/-- The actual programme model reads the literal original six source lists of its selected preparation. -/
@[expose] def targetModel (channel : Fin 6) (stage : Nat) : PathModel :=
  model next.requested.request.covered next.requested.request.chain
    next.requested.request.attempt.preparationFamily channel stage

/-- Target samples on the SAME fixed shifted geometry follow a scale computed only from the original parents. -/
theorem target_later_close
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) (channel : Fin 6) {earlier later : Nat} (ordered : earlier ≤ later) :
    Norm.Basic.normSq ((targetModel (next := next) channel later).integralSample -
      (targetModel (next := next) channel earlier).integralSample) ≤
        Geometric.Basic.quarterRadius (errorScale (parent :: parents)) earlier := by
  let firstTargets := CellEndpoints.Targets.build next.requested.request.chain.path earlier
  let lastTargets := CellEndpoints.Targets.build next.requested.request.chain.path later
  have localOrder := firstTargets.localBound_antitone lastTargets ordered
  have localSum : lastTargets.localBound + firstTargets.localBound ≤ 2 * firstTargets.localBound :=
    (Order.Arithmetic.add_le_add_direct localOrder (Order.Basic.le_refl _)).trans_eq (by ring1)
  have geometryNonnegative : (0 : Rational) ≤
      ((parent :: parents).length : Rational) * displacementCost (parent :: parents) :=
    Order.Arithmetic.mul_nonneg_direct
      (Cast.Order.natCast_le_direct (m := 0) (n := (parent :: parents).length) (Nat.zero_le _))
      (displacementCost_nonnegative (parent :: parents))
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct localSum (by decide +kernel : (0 : Rational) ≤ 16))
    geometryNonnegative
  have actual := retained.target_difference_le
    (next.requested.request.attempt.preparationFamily later)
    (next.requested.request.attempt.preparationFamily earlier) channel
  calc
    _ ≤ 16 * (lastTargets.localBound + firstTargets.localBound) *
        ((parent :: parents).length : Rational) * displacementCost (parent :: parents) := actual
    _ = (16 * (lastTargets.localBound + firstTargets.localBound)) *
        (((parent :: parents).length : Rational) * displacementCost (parent :: parents)) := by ring1
    _ ≤ (16 * (2 * firstTargets.localBound)) *
        (((parent :: parents).length : Rational) * displacementCost (parent :: parents)) := scaled
    _ = errorScale (parent :: parents) * firstTargets.localBound := by unfold errorScale; ring1
    _ ≤ _ := firstTargets.mul_localBound_le_quarterRadius (errorScale (parent :: parents))
      (errorScale_nonnegative (parent :: parents))

/-- The actual target stage-zero sample and fixed original-parent scale determine its common center bound. -/
@[expose] def targetCenter (channel : Fin 6) : Rational :=
  2 * (Norm.Basic.normSq (targetModel (next := next) channel 0).integralSample + errorScale (parent :: parents))

/-- The actual target center bound is nonnegative. -/
theorem targetCenter_nonnegative (channel : Fin 6) : 0 ≤ targetCenter (next := next) channel := by
  have terms := Order.Arithmetic.add_le_add_direct
    (Norm.Basic.normSq_nonneg (targetModel (next := next) channel 0).integralSample)
    (errorScale_nonnegative (parent :: parents))
  rewrite [Field.zero_add] at terms
  exact Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Rational) ≤ 2) terms

/-- Every actual target programme sample is bounded by its original stage-zero sample and uniform scale. -/
theorem target_sample_bounded
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) (channel : Fin 6) (stage : Nat) :
    Norm.Basic.normSq (targetModel (next := next) channel stage).integralSample ≤
      targetCenter (next := next) channel := by
  have movement := (retained.target_later_close channel (Nat.zero_le stage)).trans
    (Geometric.Basic.quarterRadius_le_scale (errorScale_nonnegative (parent :: parents)) 0)
  have decomposition : (targetModel (next := next) channel stage).integralSample =
      ((targetModel (next := next) channel stage).integralSample -
        (targetModel (next := next) channel 0).integralSample) +
          (targetModel (next := next) channel 0).integralSample := by ring1
  have triangle := Norm.Bounds.normSq_add_le_two
    ((targetModel (next := next) channel stage).integralSample -
      (targetModel (next := next) channel 0).integralSample)
    (targetModel (next := next) channel 0).integralSample
  have shifted := (congrArg Norm.Basic.normSq decomposition).trans_le triangle
  exact (shifted.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct movement (Order.Basic.le_refl _))
    (by decide +kernel : (0 : Rational) ≤ 2))).trans_eq
      (congrArg (fun total : Rational => 2 * total)
        (Field.add_comm (errorScale (parent :: parents))
          (Norm.Basic.normSq (targetModel (next := next) channel 0).integralSample)))

/-- Construct an actual six-channel target programme with original-parent uniform schedule and retained request.

The model is the original target source list at every stage. Comparisons
consume independently prepared original queries on that SAME fixed target
cover. The selected request's whole preparation is reused, without another
StageAttempt, source, acquisition or endpoint-bank execution.
-/
def targetProgram (channel : Fin 6) : RefinementProgram where
  model := targetModel (next := next) channel
  errorScale := errorScale (parent :: parents)
  errorScale_nonneg := errorScale_nonnegative (parent :: parents)
  modelAllowance_le := fun stage => retained.target_allowance_le
    (next.requested.request.attempt.preparationFamily stage) channel
  later_close := by
    intro earlier later ordered
    exact (Norm.Basic.normSq_eq_canonical
      ((targetModel (next := next) channel later).integralSample -
        (targetModel (next := next) channel earlier).integralSample)).symm.trans_le
          (retained.target_later_close channel ordered)
  centerBound := targetCenter (next := next) channel
  centerBound_nonneg := targetCenter_nonnegative (next := next) channel
  sample_bounded := by
    intro stage
    exact (Norm.Basic.normSq_eq_canonical
      (targetModel (next := next) channel stage).integralSample).symm.trans_le
        (retained.target_sample_bounded channel stage)

/-- The target programme keeps the exact original fixed-geometry model at every stage. -/
theorem targetProgram_model
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) (channel : Fin 6) (stage : Nat) :
    (retained.targetProgram channel).model stage = targetModel (next := next) channel stage := by rfl

/-- The actual programme sample is the literal original requested source-list integral at the SAME retained stage. -/
theorem targetProgram_sample
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) (channel : Fin 6) (stage : Nat) :
    ((retained.targetProgram channel).model stage).integralSample =
      (PathModel.mk ((sources next.requested.request.covered
        (next.requested.request.attempt.preparationFamily stage) next.requested.request.chain).cells
          channel)).integralSample :=
  congrArg (fun original : PathModel => original.integralSample)
    (retained.targetProgram_model channel stage)

/-- The target error scale uses only the original source parents, independently of increment and child counts. -/
theorem targetProgram_errorScale
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) (channel : Fin 6) :
    (retained.targetProgram channel).errorScale = errorScale (parent :: parents) := by rfl

/-- Certify the original target algebraic form on that SAME actual fixed shifted cycle at every stage. -/
def targetCertified (channel : Fin 6) : CertifiedPeriodProgram (Fibre.frameCurve target)
    (Specification.Table.forms (parameter + increment) channel)
      (constantCycle next.requested.request.chain) where
  integral := retained.targetProgram channel
  certificates := by
    intro stage
    exact Eq.mpr
      (congrArg (fun original : PathModel =>
        UniformPathCertificates (Fibre.frameCurve target)
          (Specification.Table.forms (parameter + increment) channel)
          original.cells next.requested.request.chain.path)
        (retained.targetProgram_model channel stage))
      ((certify target next.requested.request.covered
        (next.requested.request.attempt.preparationFamily stage) next.requested.request.chain).channel channel)

/-- The retained certified target programme contains the SAME whole original progressive integral owner. -/
theorem targetCertified_integral
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) (channel : Fin 6) :
    (retained.targetCertified channel).integral = retained.targetProgram channel := by rfl

/-- The actual certified programme stage reads its SAME original target source list. -/
theorem targetCertified_cells
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) (channel : Fin 6) (stage : Nat) :
    ((retained.targetCertified channel).integral.model stage).cells =
      (sources next.requested.request.covered (next.requested.request.attempt.preparationFamily stage)
        next.requested.request.chain).cells channel := by rfl

/-- At the retained selected stage the certified programme uses the whole SAME actual Request cell list. -/
theorem targetCertified_cells_at
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) (channel : Fin 6) :
    ((retained.targetCertified channel).integral.model next.requested.selected.stage).cells =
      (sources next.requested.request.covered next.requested.prepared next.requested.request.chain).cells channel :=
  (retained.targetCertified_cells channel next.requested.selected.stage).trans
    (congrArg (fun source => source.cells channel)
      next.requested.request.attempt.preparationFamily_sources)

/-- Every later actual target programme sample pays the common joint accuracy against the SAME stored target word.

The selected-stage sample is the retained Request sample itself. Its
original sufficient-stage search and the original-parent progressive scale
pay the later comparison; no old observation is relabelled or re-observed.
-/
theorem targetProgramme_difference_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) (channel : Fin 6) (stage : Nat)
    (after : next.requested.selected.stage ≤ stage) :
    Norm.Basic.normSq
      (((retained.targetCertified channel).integral.model stage).integralSample -
        (PathModel.mk ((sources next.requested.request.covered next.requested.prepared
          next.requested.request.chain).cells channel)).integralSample) ≤
      errorScale (parent :: parents) *
        (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance := by
  have payment := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (next.requested.selected.later_accurate (Nat.le_refl _)).le
    (errorScale_nonnegative (parent :: parents))
  have scheduled : Geometric.Basic.quarterRadius (errorScale (parent :: parents))
      next.requested.selected.stage ≤ errorScale (parent :: parents) *
        (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)).tolerance := by
    have coefficient : Geometric.Basic.quarterRadius (errorScale (parent :: parents))
        next.requested.selected.stage = errorScale (parent :: parents) *
          Geometric.Basic.quarterRadius 1 next.requested.selected.stage :=
      (Geometric.Basic.quarterRadius_eq_mul_pow (errorScale (parent :: parents))
        next.requested.selected.stage).trans
          (congrArg (fun radius : Rational => errorScale (parent :: parents) * radius)
            ((Geometric.Basic.quarterRadius_eq_mul_pow 1 next.requested.selected.stage).trans
              (Field.one_mul _)).symm)
    exact coefficient.trans_le payment
  have actualSample := congrArg (fun cells => (PathModel.mk cells).integralSample)
    (retained.targetCertified_cells_at channel)
  have newSample : ((retained.targetCertified channel).integral.model stage).integralSample =
      (targetModel (next := next) channel stage).integralSample := by rfl
  have selectedSample : ((retained.targetCertified channel).integral.model
      next.requested.selected.stage).integralSample =
      (targetModel (next := next) channel next.requested.selected.stage).integralSample := by rfl
  have difference := congrArg₂ (fun left right : Canonical => left - right)
    newSample (actualSample.symm.trans selectedSample)
  exact (congrArg Norm.Basic.normSq difference).trans_le
    ((retained.target_later_close channel after).trans scheduled)

/-- The actual selected target programme sample is the unchanged actual target sample of the retained global word. -/
theorem targetCertified_sample_at
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next)) (order coordinate : Fin 2) :
    ((retained.targetCertified (Specification.Table.baseIndex order coordinate)).integral.model
      next.requested.selected.stage).integralSample =
      (PathModel.mk (targetCells (next := next) order coordinate)).integralSample :=
  (congrArg (fun cells => (PathModel.mk cells).integralSample)
    (retained.targetCertified_cells_at (Specification.Table.baseIndex order coordinate))).trans
      (congrArg (fun cells => (PathModel.mk cells).integralSample)
        (targetCells_eq_sources (next := next) order coordinate).symm)

/-- The SAME actual global Taylor output is the actual selected sample of its certified target programme. -/
theorem Integral.output_targetProgramme
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)} (actual : Integral retained) (order coordinate : Fin 2) :
    (actual.certificate order coordinate).output =
      ((retained.targetCertified (Specification.Table.baseIndex order coordinate)).integral.model
        next.requested.selected.stage).integralSample :=
  (actual.output order coordinate).trans
    (retained.targetCertified_sample_at order coordinate).symm

/-- The actual target programme sample and original source-word samples obey the SAME retained finite Taylor bound.

Only the exact selected-stage target sample readback is transported.
The certificate, independent derivative readings, original fixed-geometry
factor and parameter-fourth payment are those already stored in actual.
This theorem identifies no canonical period or independently acquired cycle.
-/
theorem Integral.targetProgramme_remainder_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : PreparedRefinementRootChains.RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {retained : ValueBlocks (next := next)} (actual : Integral retained) (order coordinate : Fin 2) :
    Canonical.normSq
      (((retained.targetCertified (Specification.Table.baseIndex order coordinate)).integral.model
          next.requested.selected.stage).integralSample -
        (PathModel.mk (oldCells (source := source) (Specification.Table.baseIndex order coordinate))).integralSample -
        increment * (PathModel.mk
          (oldCells (source := source) (Specification.Table.slopeIndex order coordinate))).integralSample) ≤
      factor (covered := covered) order coordinate * Canonical.normSq increment ^ 2 := by
  have exactSample := retained.targetCertified_sample_at order coordinate
  exact Eq.mpr (congrArg (fun sample : Canonical =>
    Canonical.normSq
      (sample - (PathModel.mk
          (oldCells (source := source) (Specification.Table.baseIndex order coordinate))).integralSample -
        increment * (PathModel.mk
          (oldCells (source := source) (Specification.Table.slopeIndex order coordinate))).integralSample) ≤
      factor (covered := covered) order coordinate * Canonical.normSq increment ^ 2) exactSample)
    (actual.remainder_le order coordinate)

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
