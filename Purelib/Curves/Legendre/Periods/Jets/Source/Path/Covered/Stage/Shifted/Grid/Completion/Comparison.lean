module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Source
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Retained
public import Purelib.LinearAlgebra.Gaussian.Norm
public import Purelib.Algebra.Recurrence.Affine
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained.Transport
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # A later retained source carries the previous programme and computed error

The original sufficient-source factory selects a new member on the same
physical covered spine. Whole member and source-family readbacks identify
its actual sample with the supplied previous target programme at that NEW
stage. Original later-close bounds compare it to the old selected sample.
The incoming computed vector remains separate and its actual discrepancy
feeds the same affine recurrence, without a desired error bound input.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted
namespace PositiveGridNode.CompletionData

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Algebra.FiniteSum.Fin
open Purelib.Algebra.FiniteSum.Rational.Order.IndexedBudget (sumFin_le)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (zipWith)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply vector_ext zipWith_apply)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.LinearAlgebra.Gaussian
open Purelib.Algebra.Recurrence

/-- The closed unit weight used in the original vector quadrance bound is positive. -/
private theorem onePositive : (0 : Rational) < 1 := by decide +kernel

/-- The closed doubling multiplier in the retained affine recurrence is nonnegative. -/
private theorem twoNonnegative : (0 : Rational) ≤ 2 := by decide +kernel

/-- Quantified programme readback of the newly sufficient retained source sample. -/
abbrev RequestedSampleReadback : Prop :=
  ∀
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {aligned : DependentProduct (parent :: parents) (fun outer => Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (retained : CompletionData node aligned alignedEq old)
    (programmes : ShiftedGeometry.ValueBlocks (next := node.next))
    (nextCurrent : Nat) (nextAccuracy : AccuracyRequest) (channel : Fin 6),
    let paid := retained.requestedSource nextCurrent nextAccuracy
    sourceSample paid.1 paid.2 channel =
      ((programmes.targetProgram (next := node.next) channel).model paid.1.selected.stage).integralSample

/-- The newly sufficient completed source is the same previous programme at its NEW selected stage.

The original requested_member law retains the whole selected completed-family
member. Its original preparation-family source law supplies all six actual
cells. The new numerical stage is not identified with the old selected
sample. The comparison consumes the original factory/source laws rather
than replacing or re-executing either actual preparation cache.
-/
theorem requestedSample_programme : RequestedSampleReadback := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained programmes nextCurrent
    nextAccuracy channel
  dsimp only
  let incoming := retained.sourceMember
  let canonical := retained.sourceMember_factory
  let paid := Completed.requested (frame := node.target) (basis := basis) (count := count)
      (index := node.next.requested.selected.stage) (floor := targetFloor) (rootStage := targetRootStage)
    node.next.requested.request.covered node.next.requested.request.chain
    incoming.val canonical nextCurrent nextAccuracy
  let Claim : RequestedSource node nextCurrent nextAccuracy → Prop := fun value =>
    sourceSample value.1 value.2 channel =
      ((programmes.targetProgram (next := node.next) channel).model value.1.selected.stage).integralSample
  have original : Claim paid := by
    let stage := paid.1.selected.stage
    let members := Completed.family (frame := node.target) (basis := basis) (count := count)
        (index := node.next.requested.selected.stage) (floor := targetFloor) (rootStage := targetRootStage)
      node.next.requested.request.covered node.next.requested.request.chain
      incoming.val canonical
    have cached : paid.2.val = (members stage).val :=
      Completed.requested_member (frame := node.target) (basis := basis) (count := count)
        (index := node.next.requested.selected.stage) (floor := targetFloor) (rootStage := targetRootStage)
      node.next.requested.request.covered node.next.requested.request.chain
        incoming.val canonical nextCurrent nextAccuracy
    have stageSources := incoming.val.1.completedFamily_sources stage (members stage).val (members stage).property
    have retainedSources := congrArg
      (fun value : Completed node.next.requested.request.covered node.next.requested.request.chain
        stage targetFloor targetRootStage => value.2.2.val.sources) cached
    have originalSources := congrArg
      (fun attempt : StageAttempt node.next.requested.request.covered node.next.requested.request.chain
        node.next.requested.selected.stage targetFloor targetRootStage =>
        sources node.next.requested.request.covered (attempt.preparationFamily stage)
          node.next.requested.request.chain) retained.sourceMember_attempt
    have scalar := congrArg (fun original => (PathModel.mk (original.cells channel)).integralSample)
      (retainedSources.trans (stageSources.trans originalSources))
    change (PathModel.mk (paid.2.val.2.2.val.sources.cells channel)).integralSample = _
    exact scalar.trans (programmes.targetProgram_sample (next := node.next) channel stage).symm

  exact Eq.mp (congrArg Claim (retained.requestedSource_eq nextCurrent nextAccuracy).symm) original

/-- Quantified discrepancy bound between the actual later source and its retained programme sample. -/
abbrev RequestedSampleDifferenceBound : Prop :=
  ∀
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {aligned : DependentProduct (parent :: parents) (fun outer => Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (retained : CompletionData node aligned alignedEq old)
    (programmes : ShiftedGeometry.ValueBlocks (next := node.next))
    (nextCurrent : Nat) (nextAccuracy : AccuracyRequest) (channel : Fin 6),
    let paid := retained.requestedSource nextCurrent nextAccuracy
    Norm.Basic.normSq
      (sourceSample paid.1 paid.2 channel -
        ((programmes.targetProgram (next := node.next) channel).model
          node.next.requested.selected.stage).integralSample) ≤
      Geometric.Basic.quarterRadius (errorScale (parent :: parents)) node.next.requested.selected.stage

/-- Original programme decay bounds the changed numerical source against its old retained-stage programme sample.

The sufficient source stage is strictly after the actual incoming stage.
Both readings stay attached to that same original target programme, whose
fixed old-parent scale pays the new-versus-old quadrance comparison.
-/
theorem requestedSample_difference_le : RequestedSampleDifferenceBound := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained programmes nextCurrent
    nextAccuracy channel
  dsimp only
  let incoming := retained.sourceMember
  let canonical := retained.sourceMember_factory
  let paid := retained.requestedSource nextCurrent nextAccuracy
  have original := Completed.requested_stage_lt
    (frame := node.target) (basis := basis) (count := count)
    (index := node.next.requested.selected.stage) (floor := targetFloor) (rootStage := targetRootStage)
    node.next.requested.request.covered node.next.requested.request.chain
    incoming.val canonical nextCurrent nextAccuracy
  have sameStage := congrArg
    (fun value : RequestedSource node nextCurrent nextAccuracy => value.1.selected.stage)
    (retained.requestedSource_eq nextCurrent nextAccuracy)
  have later : node.next.requested.selected.stage ≤ paid.1.selected.stage :=
    original.le.trans (Nat.le_of_eq sameStage.symm)
  have exactSample := retained.requestedSample_programme programmes nextCurrent nextAccuracy channel
  dsimp only at exactSample
  have movement := (Norm.Basic.normSq_eq_canonical _).trans_le
    ((programmes.targetProgram (next := node.next) channel).later_close later)
  have scale := congrArg (fun value : Rational =>
    Geometric.Basic.quarterRadius value node.next.requested.selected.stage)
      (programmes.targetProgram_errorScale (next := node.next) channel)
  exact (congrArg (fun sample : Canonical => Norm.Basic.normSq
    (sample - ((programmes.targetProgram (next := node.next) channel).model
      node.next.requested.selected.stage).integralSample)) exactSample).trans_le
        (movement.trans_eq scale)

/-- Quantified initial vector discrepancy on the same retained source and computed vector. -/
abbrev RequestedInitialBound : Prop :=
  ∀
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {aligned : DependentProduct (parent :: parents) (fun outer => Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (retained : CompletionData node aligned alignedEq old)
    (programmes : ShiftedGeometry.ValueBlocks (next := node.next))
    (nextCurrent : Nat) (nextAccuracy : AccuracyRequest) (computed : Vec Canonical 2),
    let paid := retained.requestedSource nextCurrent nextAccuracy
    Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate => sourceSample paid.1 paid.2
      (Specification.Table.valueIndex coordinate))) computed) ≤
    2 * (2 * Geometric.Basic.quarterRadius (errorScale (parent :: parents)) node.next.requested.selected.stage +
      Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate =>
      ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
        node.next.requested.selected.stage).integralSample)) computed))

/-- The same incoming computed vector keeps its actual old endpoint discrepancy at the later source stage.

Both true vectors use their actual retained programme/source samples. The
original weighted vector inequality adds the derived programme discrepancy
to the original computed-vector discrepancy; no error bound is an input.
-/
theorem requested_initial_le : RequestedInitialBound := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained programmes nextCurrent
    nextAccuracy computed
  dsimp only
  let paid := retained.requestedSource nextCurrent nextAccuracy
  let previous := vectorOfFn (fun coordinate =>
      ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
        node.next.requested.selected.stage).integralSample)
  let current := vectorOfFn (fun coordinate => sourceSample paid.1 paid.2
      (Specification.Table.valueIndex coordinate))
  let changes := zipWith (fun first last => first - last) current previous
  let errors := zipWith (fun sample approximate => sample - approximate) previous computed
  let radius := Geometric.Basic.quarterRadius (errorScale (parent :: parents)) node.next.requested.selected.stage
  have rows (coordinate : Fin 2) : Norm.Basic.normSq (changes coordinate) ≤ radius := by
    have reading := (zipWith_apply (fun first last : Canonical => first - last) current previous coordinate).trans
      (congrArg₂ (fun first last : Canonical => first - last)
        (vectorOfFn_apply (fun coordinate => sourceSample paid.1 paid.2
          (Specification.Table.valueIndex coordinate)) coordinate)
        (vectorOfFn_apply (fun coordinate =>
          ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
            node.next.requested.selected.stage).integralSample) coordinate))
    have actual := retained.requestedSample_difference_le programmes nextCurrent nextAccuracy
      (Specification.Table.valueIndex coordinate)
    dsimp only at actual
    exact (congrArg Norm.Basic.normSq reading).trans_le actual
  have changesBound : Norm.vector changes ≤ 2 * radius :=
    (sumFin_le rows).trans_eq (by
      rewrite [sumFin_succ, sumFin_succ]
      change radius + (radius + 0) = 2 * radius
      ring1)
  have same : zipWith (fun sample approximate => sample - approximate) current computed =
      zipWith (fun change error => change + error) changes errors := by
    apply vector_ext
    intro coordinate
    rewrite [zipWith_apply, zipWith_apply, zipWith_apply, zipWith_apply]
    ring1
  have combined := Norm.vector_add_le_parameter 1 onePositive changes errors
  change Norm.vector (zipWith (fun change error => change + error) changes errors) ≤
    2 * Norm.vector changes + 2 * Norm.vector errors at combined
  have scaled := mul_le_mul_of_nonneg_left_direct
    (add_le_add_right_direct changesBound (Norm.vector errors)) twoNonnegative
  exact ((congrArg Norm.vector same).trans_le combined).trans
    ((show 2 * Norm.vector changes + 2 * Norm.vector errors =
      2 * (Norm.vector changes + Norm.vector errors) by ring1).trans_le scaled)

/-- Quantified affine propagation of the same retained initial vector discrepancy. -/
abbrev RequestedInitialIterateBound : Prop :=
  ∀
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {index : Fin intervals}
    {node : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    {aligned : DependentProduct (parent :: parents) (fun outer => Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (retained : CompletionData node aligned alignedEq old)
    (programmes : ShiftedGeometry.ValueBlocks (next := node.next))
    (nextCurrent : Nat) (nextAccuracy : AccuracyRequest) (computed : Vec Canonical 2)
    (forcing : Rational) (blocks : Nat),
    let paid := retained.requestedSource nextCurrent nextAccuracy
    Affine.iterate (fun _ => (2 : Rational)) (fun _ => forcing)
      (Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate => sourceSample paid.1 paid.2
      (Specification.Table.valueIndex coordinate))) computed)) blocks ≤
    Affine.iterate (fun _ => (2 : Rational)) (fun _ => forcing)
      (2 * (2 * Geometric.Basic.quarterRadius (errorScale (parent :: parents)) node.next.requested.selected.stage +
      Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate =>
      ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
        node.next.requested.selected.stage).integralSample)) computed))) blocks

/-- The original doubling recurrence propagates the derived incoming discrepancy through every coarse block.

The forcing and block count remain the actual scalar inputs. The same
Affine.iterate is compared from its two initial quantities; no final
Euler/sample bound or requested-path existence is assumed.
-/
theorem requested_initial_iterate_le : RequestedInitialIterateBound := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage index node aligned alignedEq old retained programmes nextCurrent
    nextAccuracy computed forcing blocks
  dsimp only
  let paid := retained.requestedSource nextCurrent nextAccuracy
  let initial := Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate => sourceSample paid.1 paid.2
      (Specification.Table.valueIndex coordinate))) computed)
  let charge := 2 * (2 * Geometric.Basic.quarterRadius (errorScale (parent :: parents))
    node.next.requested.selected.stage +
      Norm.vector (zipWith (fun sample approximate => sample - approximate)
      (vectorOfFn (fun coordinate =>
      ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
        node.next.requested.selected.stage).integralSample)) computed))
  have bound := retained.requested_initial_le programmes nextCurrent nextAccuracy computed
  dsimp only at bound
  exact Affine.comparison (fun _ => (2 : Rational)) (fun _ => forcing)
    (Affine.iterate (fun _ => (2 : Rational)) (fun _ => forcing) initial) charge blocks
    bound (fun _ _ => twoNonnegative) (fun _ _ => Data.Rat.Fraction.Order.Basic.le_refl _)

end PositiveGridNode.CompletionData
end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
