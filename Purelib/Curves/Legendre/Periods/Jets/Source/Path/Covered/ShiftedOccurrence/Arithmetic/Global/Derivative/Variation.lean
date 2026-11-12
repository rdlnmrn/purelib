module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Derivative
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Completion
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Comparison.Variation
import Purelib.Calculus.Jet.Quadratic.Perturbation.Quadrance
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs.Variation
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Variation
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Stronger all-later estimates on the same actual derivative programmes

One genuine completion retains the canonical source family. Both actual
independent target preparations and their original CommonRestrictions are
inputs. Their three independent numerical payments and the stronger bound
on the same Global remainder give a variation estimate without replacing
any original certificate, factor, programme, query or retained source owner.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.ValueBlocks.Integral

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

open Purelib.Calculus.Jet

/-- The actual completed source sample pays its original requested word by finite variation at every later stage. -/
private theorem source_difference_variation_le
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0} {current floor rootStage : Nat}
    (source : StageAttempt.Requested covered chain current floor rootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero)))
    (completed : (index : Nat) → StageAttempt.Completed covered chain index floor rootStage)
    (index : Nat) (after : source.selected.stage ≤ index) (channel : Fin 6) :
    Norm.Basic.normSq
      (((StageAttempt.staged (frame := frame) covered chain completed channel).integral.model index).integralSample -
        (PathModel.mk ((PreparedParents.sources covered source.prepared chain).cells channel)).integralSample) ≤
      (64 * variation (parent :: parents) ^ 2) * Norm.Basic.normSq increment ^ 2 := by
  let prepared := (completed index).1.preparations
  let targets := CellEndpoints.Targets.build chain.path index
  have cells := (StageAttempt.staged_cells (frame := frame) covered chain completed channel index).trans
    (congrArg (fun sources => sources.cells channel)
      (StageAttempt.Completion.stage_sources (completed index).1 (completed index).2))
  have samples := congrArg (fun cells => (PathModel.mk cells).integralSample) cells
  have compared := PreparedParents.integral_difference_variation_le covered prepared source.prepared chain channel
  have selectedPaid : source.targets.localBound ≤ Norm.Basic.normSq increment ^ 2 :=
    source.localBound_lt.le.trans (spatial.minimum_le_right (Variation.Sampling.incrementRequest increment nonzero))
  have laterPaid : targets.localBound ≤ Norm.Basic.normSq increment ^ 2 :=
    (source.targets.localBound_antitone targets after).trans selectedPaid
  have scalar := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct laterPaid selectedPaid)
      (by decide +kernel : (0 : Rational) ≤ 32)) (Order.Arithmetic.sq_nonneg_direct (variation (parent :: parents)))
  have factor : 32 * (targets.localBound + source.targets.localBound) * variation (parent :: parents) ^ 2 ≤
      (64 * variation (parent :: parents) ^ 2) * Norm.Basic.normSq increment ^ 2 :=
    scalar.trans_eq (by ring1)
  exact (congrArg Norm.Basic.normSq
    (congrArg (fun value : Canonical => value -
      (PathModel.mk ((PreparedParents.sources covered source.prepared chain).cells channel)).integralSample)
      samples)).trans_le (compared.trans factor)

/-- Both actual target preparations pay the independent programme reading through their original common cache. -/
private theorem target_difference_variation_le
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
    (actual : Integral (next := firstNext) firstRetained) (targetIndex : Nat)
    (after : lastNext.requested.selected.stage ≤ targetIndex)
    (cached : CommonRestrictions firstRetained lastRetained firstNext.requested.prepared
      (lastNext.requested.request.attempt.preparationFamily targetIndex)) (channelOrder coordinate : Fin 2) :
    Norm.Basic.normSq
      (((lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex channelOrder coordinate)).model
          targetIndex).integralSample - (actual.certificate channelOrder coordinate).output) ≤
      (64 * variation (parent :: parents) ^ 2) * Norm.Basic.normSq increment ^ 2 := by
  let firstPrepared := firstNext.requested.prepared
  let lastPrepared := lastNext.requested.request.attempt.preparationFamily targetIndex
  let lastTargets := CellEndpoints.Targets.build lastNext.requested.request.chain.path targetIndex
  have compared := CommonRestrictions.integral_difference_variation_le
    (firstNext := firstNext) (lastNext := lastNext) firstRetained lastRetained
    firstPrepared lastPrepared cached (Specification.Table.baseIndex channelOrder coordinate)
  have firstSample := (actual.output (next := firstNext) (retained := firstRetained) channelOrder coordinate).trans
    (congrArg (fun cells => (PathModel.mk cells).integralSample)
      (ValueBlocks.targetCells_eq_sources (next := firstNext) channelOrder coordinate))
  have lastSample := lastRetained.targetProgram_sample
    (next := lastNext) (Specification.Table.baseIndex channelOrder coordinate) targetIndex
  have firstPaid : firstNext.requested.targets.localBound ≤ Norm.Basic.normSq increment ^ 2 :=
    firstNext.requested.localBound_lt.le.trans
      (firstSpatial.minimum_le_right (Variation.Sampling.incrementRequest increment nonzero))
  have lastPaid : lastTargets.localBound ≤ Norm.Basic.normSq increment ^ 2 :=
    (lastNext.requested.targets.localBound_antitone lastTargets after).trans
      (lastNext.requested.localBound_lt.le.trans
        (lastSpatial.minimum_le_right (Variation.Sampling.incrementRequest increment nonzero)))
  have scalar := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Order.Arithmetic.add_le_add_direct firstPaid lastPaid)
      (by decide +kernel : (0 : Rational) ≤ 32)) (Order.Arithmetic.sq_nonneg_direct (variation (parent :: parents)))
  have factor : 32 * (firstNext.requested.targets.localBound + lastTargets.localBound) *
      variation (parent :: parents) ^ 2 ≤
      (64 * variation (parent :: parents) ^ 2) * Norm.Basic.normSq increment ^ 2 :=
    scalar.trans_eq (by ring1)
  have samples := congrArg₂ (fun last first : Canonical => last - first) lastSample firstSample
  exact (congrArg Norm.Basic.normSq samples).trans_le
    ((Norm.Bounds.normSq_sub_symm _ _).trans_le (compared.trans factor))

/-- The three original numerical payments strengthen the same independent-programme remainder at all later indices.

One genuine source Completion is extended by its original canonical family
operation. The exact same original atIndependentPrograms value retains its
old factor field. Its actual base/output/slope and the stronger bound on
the original Global remainder supply the new scalar theorem. The retained
CommonRestrictions belongs to both actual target preparations displayed in
its type; no comparison factory, source query or certificate is rebuilt.
-/
public theorem independentProgramme_remainder_variation_le
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
    (actual : Integral (next := firstNext) firstRetained)
    (sourceCompleted : StageAttempt.Completion firstSource.attempt)
    (sourceIndex targetIndex : Nat) (sourceAfter : firstSource.selected.stage ≤ sourceIndex)
    (targetAfter : lastNext.requested.selected.stage ≤ targetIndex)
    (cached : CommonRestrictions firstRetained lastRetained firstNext.requested.prepared
      (lastNext.requested.request.attempt.preparationFamily targetIndex))
    (order coordinate : Fin 2) (ceiling : Rational)
    (ceiling_le : ∀ index : Fin (parent :: parents).length,
      Variation.Point.Step.Joint.rowCeiling ((covered.entry index).val.neighborhood count) 0 order coordinate ≤
        ceiling) :
    let completed := fun stage => (firstSource.completedFamily sourceCompleted stage).val
    Norm.Basic.normSq
      (atIndependentPrograms (firstNext := firstNext) (lastNext := lastNext)
      firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
        order coordinate).remainder ≤
      (4 * (16 * (ceiling + 21 / 2) + 3 * 64) * variation (parent :: parents) ^ 2) *
        Norm.Basic.normSq increment ^ 2 := by
  let completed := fun stage => (firstSource.completedFamily sourceCompleted stage).val
  change Norm.Basic.normSq
    (atIndependentPrograms (firstNext := firstNext) (lastNext := lastNext)
      firstRetained lastRetained actual completed sourceIndex targetIndex sourceAfter targetAfter
      order coordinate).remainder ≤ _
  let programmes := StageAttempt.staged (frame := frame) covered chain completed
  let base := ((programmes (Specification.Table.baseIndex order coordinate)).integral.model sourceIndex).integralSample
  let output := ((lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex order coordinate)).model
    targetIndex).integralSample
  let slope := ((programmes (Specification.Table.slopeIndex order coordinate)).integral.model
    sourceIndex).integralSample
  let original := actual.certificate order coordinate
  have baseSample := (actual.base (next := firstNext) (retained := firstRetained) order coordinate).trans
    (congrArg (fun cells => (PathModel.mk cells).integralSample)
      (oldCells_eq_sources (source := firstSource) (Specification.Table.baseIndex order coordinate)))
  have slopeSample := (actual.slope (next := firstNext) (retained := firstRetained) order coordinate).trans
    (congrArg (fun cells => (PathModel.mk cells).integralSample)
      (oldCells_eq_sources (source := firstSource) (Specification.Table.slopeIndex order coordinate)))
  have basePaid := (congrArg Norm.Basic.normSq
    (congrArg (fun value : Canonical => base - value) baseSample)).trans_le
      (source_difference_variation_le firstSource completed sourceIndex sourceAfter
        (Specification.Table.baseIndex order coordinate))
  have slopePaid := (congrArg Norm.Basic.normSq
    (congrArg (fun value : Canonical => slope - value) slopeSample)).trans_le
      (source_difference_variation_le firstSource completed sourceIndex sourceAfter
        (Specification.Table.slopeIndex order coordinate))
  have outputPaid := target_difference_variation_le (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual targetIndex targetAfter cached order coordinate
  have originalPaid := actual.remainder_variation_le (next := firstNext) (retained := firstRetained)
    order coordinate ceiling ceiling_le
  have unit : Norm.Basic.normSq increment ≤ 1 :=
    ((admitted.trans allocation.bound_le_bound).trans (ranges.bound_le_entry 0)).trans
      (by
        unfold Variation.Point.Range.bound
        exact Order.Basic.min_le_left _ _)
  have bounded := original.perturbation_bound_of_remainder_le base output slope
    (16 * (ceiling + 21 / 2) * variation (parent :: parents) ^ 2)
    (64 * variation (parent :: parents) ^ 2) (64 * variation (parent :: parents) ^ 2)
    (64 * variation (parent :: parents) ^ 2) unit originalPaid basePaid outputPaid slopePaid
  let retained := atIndependentPrograms (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual completed sourceIndex targetIndex
    sourceAfter targetAfter order coordinate
  have samples := congrArg₂ (fun difference slope : Canonical => difference - increment * slope)
    (congrArg₂ (fun output base : Canonical => output - base)
      (atIndependentPrograms_output (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completed sourceIndex targetIndex
        sourceAfter targetAfter order coordinate)
      (atIndependentPrograms_base (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completed sourceIndex targetIndex
        sourceAfter targetAfter order coordinate))
    (atIndependentPrograms_slope (firstNext := firstNext) (lastNext := lastNext)
      firstRetained lastRetained actual completed sourceIndex targetIndex
      sourceAfter targetAfter order coordinate)
  have same := retained.expansion.symm.trans samples
  have coefficient :
      4 * (16 * (ceiling + 21 / 2) * variation (parent :: parents) ^ 2 +
        64 * variation (parent :: parents) ^ 2 + 64 * variation (parent :: parents) ^ 2 +
          64 * variation (parent :: parents) ^ 2) =
        4 * (16 * (ceiling + 21 / 2) + 3 * 64) * variation (parent :: parents) ^ 2 := by ring1
  exact (congrArg Norm.Basic.normSq same).trans_le (bounded.trans_eq
    (congrArg (fun factor : Rational => factor * Norm.Basic.normSq increment ^ 2) coefficient))

/-- Every later pair of SAME source and independent target samples has the stronger variation divided-difference bound.

The original all-stage source cache is derived from one genuine Completion.
The actual target sample and both original completed source readings keep
their independent owners and stages. The unchanged retained certificate's
expansion cancels the actual nonzero increment; its old factor is not used
or compared with the new scalar estimate.
-/
public theorem differenceQuotient_variation_le
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
    (actual : Integral (next := firstNext) firstRetained)
    (sourceCompleted : StageAttempt.Completion firstSource.attempt)
    (sourceIndex targetIndex : Nat) (sourceAfter : firstSource.selected.stage ≤ sourceIndex)
    (targetAfter : lastNext.requested.selected.stage ≤ targetIndex)
    (cached : CommonRestrictions firstRetained lastRetained firstNext.requested.prepared
      (lastNext.requested.request.attempt.preparationFamily targetIndex))
    (order coordinate : Fin 2) (ceiling : Rational)
    (ceiling_le : ∀ index : Fin (parent :: parents).length,
      Variation.Point.Step.Joint.rowCeiling ((covered.entry index).val.neighborhood count) 0 order coordinate ≤
        ceiling) :
    let completed := fun stage => (firstSource.completedFamily sourceCompleted stage).val
    Norm.Basic.normSq
      ((((lastRetained.targetProgram (next := lastNext) (Specification.Table.baseIndex order coordinate)).model
          targetIndex).integralSample -
        ((StageAttempt.staged (frame := frame) covered chain completed
          (Specification.Table.baseIndex order coordinate)).integral.model sourceIndex).integralSample) / increment -
        ((StageAttempt.staged (frame := frame) covered chain completed
          (Specification.Table.slopeIndex order coordinate)).integral.model sourceIndex).integralSample) ≤
      (4 * (16 * (ceiling + 21 / 2) + 3 * 64) * variation (parent :: parents) ^ 2) *
        Norm.Basic.normSq increment := by
  let completed := fun stage => (firstSource.completedFamily sourceCompleted stage).val
  let retained := atIndependentPrograms (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual completed sourceIndex targetIndex
    sourceAfter targetAfter order coordinate
  have bounded := independentProgramme_remainder_variation_le (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual sourceCompleted sourceIndex targetIndex sourceAfter targetAfter cached
    order coordinate ceiling ceiling_le
  have quotient := retained.differenceQuotient_le_of_remainder_le nonzero
    (4 * (16 * (ceiling + 21 / 2) + 3 * 64) * variation (parent :: parents) ^ 2) bounded
  have samples := congrArg₂ (fun difference slope : Canonical => difference / increment - slope)
    (congrArg₂ (fun output base : Canonical => output - base)
      (atIndependentPrograms_output (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completed sourceIndex targetIndex
        sourceAfter targetAfter order coordinate)
      (atIndependentPrograms_base (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completed sourceIndex targetIndex
        sourceAfter targetAfter order coordinate))
    (atIndependentPrograms_slope (firstNext := firstNext) (lastNext := lastNext)
      firstRetained lastRetained actual completed sourceIndex targetIndex
      sourceAfter targetAfter order coordinate)
  exact (congrArg Norm.Basic.normSq samples).symm.trans_le quotient

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.ValueBlocks.Integral
