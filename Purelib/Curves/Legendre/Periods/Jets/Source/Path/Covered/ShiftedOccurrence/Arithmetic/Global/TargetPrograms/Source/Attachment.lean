module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip.Increment
import Purelib.Curves.Legendre.Periods.Jets.Source.Attachment
import Purelib.Curves.Legendre.Periods.Jets.Basic
import Purelib.Curves.Legendre.Periods.Jets.Connection
import Purelib.Curves.Legendre.Periods.Jets.PicardFuchs
import Purelib.Curves.Legendre.Periods.Jets.Specification
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Fin.Two

/-! # Source attachment for the same retained shifted target programmes

The original target programme preparations determine an actual attempt
family on the identical covered spine. A genuine original Completed value for each of
those exact attempts retains its original endpoint acquisitions and Stage.
The six already certified target programmes then consume those literal
source lists directly. No alternative programme or period name is built.

All-stage Completion remains geometric input: preparation alone proves
neither readiness nor coherent first-match roots at repeated signed visits.
A different physical spine additionally needs its own signed refinement
comparison; no such identification is inferred here.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Period.Jets (CertifiedPeriodProgram)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Curves.Legendre.Periods.Jets.Source (Attachment)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

namespace ValueBlocks

/-- The original two target value programmes retain their existing parameter, differential and lifted-cycle owners. -/
@[expose] def sourceValue
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve target)
    (Specification.valueSpecification (parameter + increment) coordinate)
      (constantCycle next.requested.request.chain) :=
  Fin.cases (retained.targetCertified (next := next) 0)
    (Fin.cases (retained.targetCertified (next := next) 1) (fun index => Fin.elim0 index))

/-- The original target first-derivative programmes retain the same six-channel target preparation family. -/
@[expose] def sourceFirst
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve target)
    (Specification.firstDerivativeSpecification (parameter + increment) coordinate)
      (constantCycle next.requested.request.chain) :=
  Fin.cases (retained.targetCertified (next := next) 2)
    (Fin.cases (retained.targetCertified (next := next) 3) (fun index => Fin.elim0 index))

/-- The original target second-derivative programmes retain that identical target cycle and source family. -/
@[expose] def sourceSecond
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    : (coordinate : Fin 2) → CertifiedPeriodProgram (Fibre.frameCurve target)
    (Specification.secondDerivativeSpecification (parameter + increment) coordinate)
      (constantCycle next.requested.request.chain) :=
  Fin.cases (retained.targetCertified (next := next) 4)
    (Fin.cases (retained.targetCertified (next := next) 5) (fun index => Fin.elim0 index))

/-- The next source value row is the whole same original incoming target integral programme. -/
theorem sourceValue_integral
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (coordinate : Fin 2) :
    ((retained.sourceValue (next := next) coordinate).integral) =
      retained.targetProgram (next := next) (Specification.Table.valueIndex coordinate) := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    exact retained.targetCertified_integral (next := next) 0
  · subst coordinate
    exact retained.targetCertified_integral (next := next) 1

/-- The next source first row is the whole same original incoming first target integral programme. -/
theorem sourceFirst_integral
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (coordinate : Fin 2) :
    ((retained.sourceFirst (next := next) coordinate).integral) =
      retained.targetProgram (next := next) (Specification.Table.firstIndex coordinate) := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    exact retained.targetCertified_integral (next := next) 2
  · subst coordinate
    exact retained.targetCertified_integral (next := next) 3

/-- The next source second row is the whole same original incoming second target integral programme. -/
theorem sourceSecond_integral
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (coordinate : Fin 2) :
    ((retained.sourceSecond (next := next) coordinate).integral) =
      retained.targetProgram (next := next) (Specification.Table.secondIndex coordinate) := by
  rcases Data.Fin.Two.finTwo_cases coordinate with equal | equal
  · subst coordinate
    exact retained.targetCertified_integral (next := next) 4
  · subst coordinate
    exact retained.targetCertified_integral (next := next) 5

/-- Each original target channel uses the literal cells of its retained completed source stage. -/
private theorem source_cells_eq
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (completed : next.requested.request.attempt.CompletedFamily) (channel : Fin 6) (stage : Nat) :
    ((retained.targetCertified (next := next) channel).integral.model stage).cells =
      (completed stage).val.2.2.val.sources.cells channel :=
  (retained.targetCertified_cells (next := next) channel stage).trans
    (congrArg (fun source => source.cells channel)
      (next.requested.request.attempt.completedFamily_sources stage
        (completed stage).val (completed stage).property)).symm

/-- Attach the same six original target programmes to their actual completed source stages.

Every supplied original Completed value retains its actual attempt and
Completion, with the whole exact attempt-family factory equation: its
selected member is the entire retained incoming Request, while each other
member has its own genuine bank and checks. Original whole-source and
literal-cell readbacks derive all six attachment equations; no period or
endpoint agreement is requested as an input.
-/
def sourceAttachment
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (completed : next.requested.request.attempt.CompletedFamily) :
    Attachment target (constantCycle next.requested.request.chain)
      (retained.sourceValue (next := next)) (retained.sourceFirst (next := next))
      (retained.sourceSecond (next := next)) where
  stages := fun stage =>
    (completed stage).val.2.2.val
  valueZero_eq := by
    intro stage
    change ((retained.targetCertified (next := next) 0).integral.model stage).cells = _
    exact retained.source_cells_eq (next := next) completed 0 stage
  valueOne_eq := by
    intro stage
    change ((retained.targetCertified (next := next) 1).integral.model stage).cells = _
    exact retained.source_cells_eq (next := next) completed 1 stage
  firstZero_eq := by
    intro stage
    change ((retained.targetCertified (next := next) 2).integral.model stage).cells = _
    exact retained.source_cells_eq (next := next) completed 2 stage
  firstOne_eq := by
    intro stage
    change ((retained.targetCertified (next := next) 3).integral.model stage).cells = _
    exact retained.source_cells_eq (next := next) completed 3 stage
  secondZero_eq := by
    intro stage
    change ((retained.targetCertified (next := next) 4).integral.model stage).cells = _
    exact retained.source_cells_eq (next := next) completed 4 stage
  secondOne_eq := by
    intro stage
    change ((retained.targetCertified (next := next) 5).integral.model stage).cells = _
    exact retained.source_cells_eq (next := next) completed 5 stage

/-- The attached source stage is the same original Stage from that exact retained Completion. -/
theorem sourceAttachment_stage
    {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {target : Paths.Frame (parameter + increment)} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq increment ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {spatial : AccuracyRequest} {nonzero : increment ≠ 0}
    {sourceCurrent sourceFloor sourceRootStage targetCurrent targetFloor targetRootStage : Nat}
    {source : StageAttempt.Requested covered chain sourceCurrent sourceFloor sourceRootStage
      (spatial.minimum (Variation.Sampling.incrementRequest increment nonzero))}
    {next : StageAttempt.Requested.Shifted (target := target) source ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    (retained : ValueBlocks (next := next))
    (completed : next.requested.request.attempt.CompletedFamily) (stage : Nat) :
    (retained.sourceAttachment (next := next) completed).stages stage = (completed stage).val.2.2.val := by rfl

end ValueBlocks

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry

end
