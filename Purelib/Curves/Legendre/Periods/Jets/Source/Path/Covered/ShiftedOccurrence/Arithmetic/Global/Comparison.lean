module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Uniform.Sum
public import Purelib.Data.List.DependentProduct
public import Purelib.Data.Vector.Dependent
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Actual global target integral comparison across retained shifted geometries

Both ValueBlocks keep the same original fixed covered-parent spine and
independent old/new Requests, models, Alignments and global allocations.
Their existing full-prefix positions identify the actual two target lists.
One original cache product stores common-dyadic restrictions outside all
callbacks. Width-weighted per-parent bounds and finite Cauchy over ORIGINAL
parents give a constant independent of increment and adaptive child counts.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Algebra
open Purelib.Algebra.FiniteSum.Fin (sumFin)
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
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
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

namespace ValueBlocks

variable {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets firstNext.requested.request.chain.path firstStage}
    {lastTargets : CellEndpoints.Targets lastNext.requested.request.chain.path lastStage}
    (firstPrepared : PreparedParents firstNext.requested.request.covered firstTargetFloor firstTargets)
    (lastPrepared : PreparedParents lastNext.requested.request.covered lastTargetFloor lastTargets)

/-- The original common-fine occurrence vector and six-channel restriction banks for one actual pair of parent blocks.

Only existing dependent vectors, dependent products and original restriction
caches are grouped. Both original globally allocated preparation products,
local/global positions and actual acquired depths remain nominal inputs;
there is no replacement source, root, period or context record.
-/
@[expose] def CommonEntry (outer : Fin (parent :: parents).length) :=
  let firstBlock := DependentProduct.get (parent :: parents) firstNext.blocks outer
  let lastBlock := DependentProduct.get (parent :: parents) lastNext.blocks outer
  let firstPositions := fun index => ((firstRetained.block outer).position index).sourceIndex
  let lastPositions := fun index => ((lastRetained.block outer).position index).sourceIndex
  PreparedParent.ShiftedAcquisition.CommonCaches
    (first := firstSource.prepared.entry outer) (last := lastSource.prepared.entry outer)
    (firstLinked := firstBlock) (lastLinked := lastBlock)
    (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
    (firstPositions := firstPositions) (lastPositions := lastPositions)

/-- Delegate the same three auxiliary cache factories once to their original minimal acquisition context. -/
def commonEntry (outer : Fin (parent :: parents).length) :
    CommonEntry firstRetained lastRetained firstPrepared lastPrepared outer :=
  let firstBlock := DependentProduct.get (parent :: parents) firstNext.blocks outer
  let lastBlock := DependentProduct.get (parent :: parents) lastNext.blocks outer
  let firstPositions := fun index => ((firstRetained.block outer).position index).sourceIndex
  let lastPositions := fun index => ((lastRetained.block outer).position index).sourceIndex
  PreparedParent.ShiftedAcquisition.commonCaches
    (first := firstSource.prepared.entry outer) (last := lastSource.prepared.entry outer)
    (firstLinked := firstBlock) (lastLinked := lastBlock)
    (firstPrepared := firstPrepared) (lastPrepared := lastPrepared)
    (firstPositions := firstPositions) (lastPositions := lastPositions)

/-- Retain the original pair of common-refinement cache banks at every SAME original parent occurrence. -/
@[expose] def CommonRestrictions := DependentProduct (parent :: parents)
  (fun outer => CommonEntry firstRetained lastRetained firstPrepared lastPrepared outer)

namespace CommonRestrictions

/-- Materialize each parent's new cache once while retaining both complete original geometry/source families. -/
def build : CommonRestrictions firstRetained lastRetained firstPrepared lastPrepared :=
  DependentProduct.ofFn (parent :: parents)
    (fun outer => commonEntry firstRetained lastRetained firstPrepared lastPrepared outer)

variable (cached : CommonRestrictions firstRetained lastRetained firstPrepared lastPrepared)

/-- Read the SAME stored original parent occurrence's complete common-refinement cache product. -/
@[expose] def entry (outer : Fin (parent :: parents).length) :
    CommonEntry firstRetained lastRetained firstPrepared lastPrepared outer :=
  DependentProduct.get (parent :: parents) cached outer

/-- The stored whole parent cache retains its exact original three-factory construction, without replay. -/
theorem build_entry (outer : Fin (parent :: parents).length) :
    entry firstRetained lastRetained firstPrepared lastPrepared
      (build firstRetained lastRetained firstPrepared lastPrepared) outer =
        commonEntry firstRetained lastRetained firstPrepared lastPrepared outer := by
  unfold build entry
  exact DependentProduct.get_ofFn _ _ outer

include firstRetained lastRetained cached

omit firstRetained lastRetained cached in
/-- Actual global target-child samples in one original parent obey the internally derived width-weighted bound. -/
theorem parent_difference_le
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
    (channel : Fin 6) (outer : Fin (parent :: parents).length) :
    Norm.Basic.normSq
      ((PathModel.mk (firstRetained.groupedCells firstPrepared channel outer)).integralSample -
        (PathModel.mk (lastRetained.groupedCells lastPrepared channel outer)).integralSample) ≤
      16 * (firstTargets.localBound + lastTargets.localBound) *
        PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt) := by
  let firstBlock := DependentProduct.get (parent :: parents) firstNext.blocks outer
  let lastBlock := DependentProduct.get (parent :: parents) lastNext.blocks outer
  let firstPositions := fun index => ((firstRetained.block outer).position index).sourceIndex
  let lastPositions := fun index => ((lastRetained.block outer).position index).sourceIndex
  let retained := entry firstRetained lastRetained firstPrepared lastPrepared cached outer
  have actual := PreparedParent.ShiftedAcquisition.commonIntegral_difference_le
    (firstSource.prepared.entry outer) (lastSource.prepared.entry outer) firstBlock lastBlock
    (firstRetained.block outer).aligned (lastRetained.block outer).aligned firstPrepared lastPrepared
    firstPositions lastPositions
    (fun index => ((firstRetained.block outer).position index).property.1)
    (fun index => ((lastRetained.block outer).position index).property.1)
    channel retained.1 (retained.2.1.get channel) (retained.2.2.get channel)
  have firstSum := PathModel.integralSample_ofFn_eq_sumFin (fun index =>
    (firstPrepared.entry (firstPositions index)).preparation.cell.models.cell channel)
  have lastSum := PathModel.integralSample_ofFn_eq_sumFin (fun index =>
    (lastPrepared.entry (lastPositions index)).preparation.cell.models.cell channel)
  exact (congrArg Norm.Basic.normSq
    (congrArg₂ (fun first last : Canonical => first - last) firstSum lastSum)).trans_le actual

omit firstRetained lastRetained cached in
/-- The SAME literal global target cell lists have a comparison constant from ORIGINAL geometry alone.

All six channels use the actual retained model/Query owners. Both source
stages, both target allocations and the two independently acquired child
spines remain inputs. Only the ORIGINAL parent count multiplies its fixed
displacement-cost sum; no adaptive child count enters this bound.
-/
theorem integral_difference_le
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
      16 * (firstTargets.localBound + lastTargets.localBound) *
        ((parent :: parents).length : Rational) * displacementCost (parent :: parents) := by
  let firstValues := fun outer => (PathModel.mk (firstRetained.groupedCells firstPrepared channel outer)).integralSample
  let lastValues := fun outer => (PathModel.mk (lastRetained.groupedCells lastPrepared channel outer)).integralSample
  let bounds := fun outer : Fin (parent :: parents).length =>
    16 * (firstTargets.localBound + lastTargets.localBound) *
        PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt)
  have finite := Norm.Sum.Indexed.normSq_sumFin_sub_le_count_mul_sumFin firstValues lastValues bounds
    (fun outer => parent_difference_le firstRetained lastRetained firstPrepared lastPrepared cached channel outer)
  have samples := congrArg₂ (fun first last : Canonical => first - last)
    (firstRetained.sample_eq_groups firstPrepared channel) (lastRetained.sample_eq_groups lastPrepared channel)
  have costs_eq :
      sumFin (fun outer : Fin (parent :: parents).length =>
        PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt)) =
      displacementCost (parent :: parents) := by rfl
  have extracted : sumFin bounds =
      (16 * (firstTargets.localBound + lastTargets.localBound)) * displacementCost (parent :: parents) :=
    (FiniteSum.Fin.sumFin_mul_left (16 * (firstTargets.localBound + lastTargets.localBound))
      (fun outer : Fin (parent :: parents).length =>
        PreparedParent.cost ((parent :: parents)[outer.val]'outer.isLt))).trans
      (congrArg (fun total : Rational => (16 * (firstTargets.localBound + lastTargets.localBound)) * total)
        costs_eq)
  have factor : ((parent :: parents).length : Rational) * sumFin bounds =
      16 * (firstTargets.localBound + lastTargets.localBound) *
        ((parent :: parents).length : Rational) * displacementCost (parent :: parents) :=
    (congrArg (fun total : Rational => ((parent :: parents).length : Rational) * total) extracted).trans
      ((Field.mul_assoc ((parent :: parents).length : Rational)
        (16 * (firstTargets.localBound + lastTargets.localBound)) (displacementCost (parent :: parents))).symm.trans
          (congrArg (fun coefficient : Rational => coefficient * displacementCost (parent :: parents))
            (Field.mul_comm ((parent :: parents).length : Rational)
              (16 * (firstTargets.localBound + lastTargets.localBound)))))
  exact (congrArg Norm.Basic.normSq samples).trans_le (finite.trans_eq factor)

end CommonRestrictions

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
