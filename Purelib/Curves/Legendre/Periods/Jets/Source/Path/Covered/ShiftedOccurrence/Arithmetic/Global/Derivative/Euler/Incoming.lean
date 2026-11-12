module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Derivative.Euler
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedRequest.Completion
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Source
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.PicardFuchs.Clearance
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Calculus.Linear.Euler
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.LinearAlgebra.Gaussian.Norm
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedBankRootChains

/-! # Incoming target programmes as the next actual Euler source

One genuine completion of the incoming retained Request supplies its
original completed stage family. Exact literal-source readbacks identify
that family's staged samples with the same six incoming target programmes.
An independently acquired outgoing Taylor bank then pays a local Euler
defect on those actual incoming and outgoing programme readings.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Rational.Geometric
open Purelib.Calculus.Jet
open Purelib.Calculus.Linear
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Scale (scale)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector (map)
open Purelib.Data.Vector.Basic (map_apply vectorOfFn vectorOfFn_apply vector_ext)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.LinearAlgebra.Gaussian
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology

namespace ValueBlocks

/-- The incoming canonical completion family and the same original target programme have identical stage samples.

Only the original staged-cell, completed-family source and target-programme
sample laws are composed. Both programme owners remain present; this is a
literal model readback, not an operational comparison or another query.
-/
private theorem incoming_sample
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
    {incomingNext : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (incoming : ValueBlocks (next := incomingNext))
    (completed : incomingNext.requested.request.attempt.CompletedFamily) (channel : Fin 6) (stage : Nat) :
    ((StageAttempt.staged (parameter := parameter + increment) (frame := target)
      incomingNext.requested.request.covered incomingNext.requested.request.chain
      (fun index => (completed index).val) channel).integral.model stage).integralSample =
      ((incoming.targetProgram (next := incomingNext) channel).model stage).integralSample := by
  have cells := StageAttempt.staged_cells (parameter := parameter + increment) (frame := target)
    incomingNext.requested.request.covered incomingNext.requested.request.chain
    (fun index => (completed index).val) channel stage
  have sources := incomingNext.requested.request.attempt.completedFamily_sources stage
    (completed stage).val (completed stage).property
  have sameCells := cells.trans (congrArg (fun original => original.cells channel) sources)
  exact (congrArg (fun cells => (PathModel.mk cells).integralSample) sameCells).trans
    (incoming.targetProgram_sample (next := incomingNext) channel stage).symm

/-- Constant-parameter connection transport retains the same incoming target programme samples.

One genuine completion constructs the original canonical family and source
attachment on the unchanged incoming target frame and cycle. The original
zero-direction trace starts on that attached jet. Whole-integral readbacks
identify its result with the same two retained target programmes at the same
stage; the other four certified programmes remain in the identical jet.
No zero-offset acquisition, frame replacement, endpoint period comparison
or canonical-cycle attachment is performed.
-/
public theorem constantTrace_fromIncoming
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
    {incomingNext : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (incoming : ValueBlocks (next := incomingNext))
    (completed : StageAttempt.Completion incomingNext.requested.request.attempt)
    (index : Nat) (timeWidths : Nat → Rational) (steps : Nat) :
    let family := incomingNext.requested.request.completedFamily completed
    let actual := incoming.sourceJet (next := incomingNext) family
    Euler.trace (fun _ => Connection.alongMatrix (parameter + increment) 0) timeWidths
        (vectorOfFn (fun coordinate => ((actual.value coordinate).integral.model index).integralSample)) steps =
      vectorOfFn (fun coordinate =>
        ((incoming.targetProgram (next := incomingNext) (Specification.Table.valueIndex coordinate)).model
          index).integralSample) := by
  let family := incomingNext.requested.request.completedFamily completed
  let actual := incoming.sourceJet (next := incomingNext) family
  have readings :
      vectorOfFn (fun coordinate => ((actual.value coordinate).integral.model index).integralSample) =
        vectorOfFn (fun coordinate =>
          ((incoming.targetProgram (next := incomingNext) (Specification.Table.valueIndex coordinate)).model
            index).integralSample) := by
    apply vector_ext
    intro coordinate
    have original := incoming.sourceJet_value_integral (next := incomingNext) family coordinate
    have reading := congrArg (fun programme : RefinementProgram => (programme.model index).integralSample)
      original
    exact (vectorOfFn_apply (fun coordinate : Fin 2 =>
      ((actual.value coordinate).integral.model index).integralSample) coordinate).trans
        (reading.trans (vectorOfFn_apply (fun coordinate : Fin 2 =>
          ((incoming.targetProgram (next := incomingNext) (Specification.Table.valueIndex coordinate)).model
            index).integralSample) coordinate).symm)
  exact (Connection.constant_period_trace actual index timeWidths steps).trans readings

namespace Integral

/-- One actual incoming completion pays the next local Euler defect on the same incoming and outgoing programmes.

The source spine is the incoming Request's literal cover and based chain.
Its signed root chain is the incoming geometry's original root chain cast
only through the stored head-list equality. One supplied genuine Completion
extends to source stages internally. The outgoing entry vector is retained
with its whole original factory equation, keeping both actual Taylor
certificates and independently allocated outgoing programme samples.
No final sample equality, all-stage completion, Ready or Distinct input is
required. This is one moving leg, not automatic completion of its new target
bank or a common-window certificate for an entire parameter path.
-/
public theorem eulerDefect_fromIncoming_le
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
    {incomingNext : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (incoming : ValueBlocks (next := incomingNext))
    (completed : StageAttempt.Completion incomingNext.requested.request.attempt)
    {movement : Canonical} {laterTarget : Paths.Frame ((parameter + increment) + movement)}
    {nextRanges : ParameterRange incomingNext.requested.request.covered}
    {nextAllocation : ParameterRange.StripAllocation nextRanges}
    {nextAdmitted : Norm.Basic.normSq movement ≤ nextAllocation.bound}
    {firstWidths lastWidths :
      Fin (incomingNext.requested.request.shape.val.1 :: incomingNext.requested.request.shape.val.2).length →
        AccuracyRequest}
    {firstSpatial lastSpatial : AccuracyRequest} {moving : movement ≠ 0}
    {firstSourceCurrent firstTargetCurrent firstTargetFloor firstTargetRootStage : Nat}
    {lastSourceCurrent lastSourceFloor lastSourceRootStage : Nat}
    {lastTargetCurrent lastTargetFloor lastTargetRootStage : Nat}
    {firstSource : StageAttempt.Requested (parameter := parameter + increment) (frame := target)
      incomingNext.requested.request.covered incomingNext.requested.request.chain
      firstSourceCurrent targetFloor targetRootStage
      (firstSpatial.minimum (Variation.Sampling.incrementRequest movement moving))}
    {lastSource : StageAttempt.Requested (parameter := parameter + increment) (frame := target)
      incomingNext.requested.request.covered incomingNext.requested.request.chain
      lastSourceCurrent lastSourceFloor lastSourceRootStage
      (lastSpatial.minimum (Variation.Sampling.incrementRequest movement moving))}
    {firstNext : StageAttempt.Requested.Shifted (parameter := parameter + increment) (increment := movement)
      (frame := target) (target := laterTarget)
      firstSource nextRanges nextAllocation nextAdmitted firstWidths
      (PreparedBankRootChains.RootChain.castChildren incomingNext.requested.request.shape.property
        incomingNext.geometry.roots)
      firstTargetCurrent firstTargetFloor firstTargetRootStage}
    {lastNext : StageAttempt.Requested.Shifted (parameter := parameter + increment) (increment := movement)
      (frame := target) (target := laterTarget)
      lastSource nextRanges nextAllocation nextAdmitted lastWidths
      (PreparedBankRootChains.RootChain.castChildren incomingNext.requested.request.shape.property
        incomingNext.geometry.roots)
      lastTargetCurrent lastTargetFloor lastTargetRootStage}
    (firstRetained : ValueBlocks (next := firstNext)) (lastRetained : ValueBlocks (next := lastNext))
    (actual : Integral (next := firstNext) firstRetained) (sourceIndex targetIndex : Nat)
    (sourceAfter : firstSource.selected.stage ≤ sourceIndex)
    (targetAfter : lastNext.requested.selected.stage ≤ targetIndex)
    (entries : Vec (Quadratic.Basic.Certificate movement) 2)
    (entries_eq : entries = eulerEntries (parameter := parameter + increment) (frame := target)
      (increment := movement) (target := laterTarget) (basis := basis) (count := count)
      (parent := incomingNext.requested.request.shape.val.1)
      (parents := incomingNext.requested.request.shape.val.2)
      (covered := incomingNext.requested.request.covered) (chain := incomingNext.requested.request.chain)
      (firstNext := firstNext) (lastNext := lastNext)
      firstRetained lastRetained actual
      (fun index => (incomingNext.requested.request.completedFamily completed index).val)
      sourceIndex targetIndex sourceAfter targetAfter)
    (width : Rational) (direction : Canonical) (scaled : movement = scale width direction) (start : Nat)
    (selection : Search.Selection 1 start
      (width ^ 2 * (ParameterClearance.ofFrame target).connectionLowerSq))
    (after : selection.stage ≤ sourceIndex) :
    Norm.vector (Euler.defect (Connection.alongMatrix (parameter + increment) direction) width
      (vectorOfFn (fun coordinate =>
        ((incoming.targetProgram (next := incomingNext) (Specification.Table.valueIndex coordinate)).model
          sourceIndex).integralSample))
      (vectorOfFn (fun coordinate =>
        ((lastRetained.targetProgram (next := lastNext) (Specification.Table.valueIndex coordinate)).model
          targetIndex).integralSample))) ≤
      (2 * ((ValueBlocks.derivativeFactor (parameter := parameter + increment) (frame := target)
          (basis := basis) (count := count) (parent := incomingNext.requested.request.shape.val.1)
          (parents := incomingNext.requested.request.shape.val.2)
          (covered := incomingNext.requested.request.covered) 0 0 +
        ValueBlocks.derivativeFactor (parameter := parameter + increment) (frame := target)
          (basis := basis) (count := count) (parent := incomingNext.requested.request.shape.val.1)
          (parents := incomingNext.requested.request.shape.val.2)
          (covered := incomingNext.requested.request.covered) 0 1) *
          Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)) * width ^ 4 := by
  let family := incomingNext.requested.request.completedFamily completed
  let completedStages := fun index => (family index).val
  have bases (coordinate : Fin 2) : (entries coordinate).base =
      ((incoming.targetProgram (next := incomingNext) (Specification.Table.valueIndex coordinate)).model
        sourceIndex).integralSample := by
    have retainedBase := (congrArg
      (fun original : Vec (Quadratic.Basic.Certificate movement) 2 => (original coordinate).base) entries_eq).trans
      (eulerEntries_base (parameter := parameter + increment) (frame := target)
        (increment := movement) (target := laterTarget) (basis := basis) (count := count)
        (parent := incomingNext.requested.request.shape.val.1)
        (parents := incomingNext.requested.request.shape.val.2)
        (covered := incomingNext.requested.request.covered) (chain := incomingNext.requested.request.chain)
        (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completedStages sourceIndex targetIndex sourceAfter targetAfter coordinate)
    have original := StageAttempt.jet_value_integral (parameter := parameter + increment) (frame := target)
      incomingNext.requested.request.covered incomingNext.requested.request.chain completedStages coordinate
    exact retainedBase.trans ((congrArg
      (fun programme : RefinementProgram => (programme.model sourceIndex).integralSample) original).trans
        (incoming_sample (incomingNext := incomingNext) incoming family
        (Specification.Table.valueIndex coordinate) sourceIndex))
  have outputs (coordinate : Fin 2) : (entries coordinate).output =
      ((lastRetained.targetProgram (next := lastNext) (Specification.Table.valueIndex coordinate)).model
        targetIndex).integralSample :=
    (congrArg (fun original : Vec (Quadratic.Basic.Certificate movement) 2 => (original coordinate).output)
      entries_eq).trans
      (eulerEntries_output (parameter := parameter + increment) (frame := target)
        (increment := movement) (target := laterTarget) (basis := basis) (count := count)
        (parent := incomingNext.requested.request.shape.val.1)
        (parents := incomingNext.requested.request.shape.val.2)
        (covered := incomingNext.requested.request.covered) (chain := incomingNext.requested.request.chain)
        (firstNext := firstNext) (lastNext := lastNext)
        firstRetained lastRetained actual completedStages sourceIndex targetIndex sourceAfter targetAfter coordinate)
  have baseVector : map Quadratic.Basic.Certificate.base entries =
      vectorOfFn (fun coordinate =>
        ((incoming.targetProgram (next := incomingNext) (Specification.Table.valueIndex coordinate)).model
          sourceIndex).integralSample) := by
    apply vector_ext
    intro coordinate
    exact ((map_apply Quadratic.Basic.Certificate.base entries coordinate).trans (bases coordinate)).trans
      (vectorOfFn_apply (fun coordinate : Fin 2 =>
        ((incoming.targetProgram (next := incomingNext) (Specification.Table.valueIndex coordinate)).model
          sourceIndex).integralSample) coordinate).symm
  have outputVector : map Quadratic.Basic.Certificate.output entries =
      vectorOfFn (fun coordinate =>
        ((lastRetained.targetProgram (next := lastNext) (Specification.Table.valueIndex coordinate)).model
          targetIndex).integralSample) := by
    apply vector_ext
    intro coordinate
    exact ((map_apply Quadratic.Basic.Certificate.output entries coordinate).trans (outputs coordinate)).trans
      (vectorOfFn_apply (fun coordinate : Fin 2 =>
        ((lastRetained.targetProgram (next := lastNext) (Specification.Table.valueIndex coordinate)).model
          targetIndex).integralSample) coordinate).symm
  have paid := eulerDefect_le (parameter := parameter + increment) (frame := target)
    (increment := movement) (target := laterTarget) (basis := basis) (count := count)
    (parent := incomingNext.requested.request.shape.val.1)
    (parents := incomingNext.requested.request.shape.val.2)
    (covered := incomingNext.requested.request.covered) (chain := incomingNext.requested.request.chain)
    (firstNext := firstNext) (lastNext := lastNext)
    firstRetained lastRetained actual completedStages sourceIndex targetIndex sourceAfter targetAfter
    entries entries_eq width direction scaled start selection after
  have sameDefect := congrArg₂ (fun before finish : Vec Canonical 2 =>
    Norm.vector (Euler.defect (Connection.alongMatrix (parameter + increment) direction) width before finish))
    baseVector outputVector
  exact sameDefect.symm.trans_le paid

end Integral

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry
