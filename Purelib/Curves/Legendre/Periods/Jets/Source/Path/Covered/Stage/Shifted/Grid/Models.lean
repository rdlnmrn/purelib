module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid
public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained

/-! # Same positive-node Request and literal original target programme samples

The retained common-source factory equation transports the original target
Request, preparation and selected stage. Its original finite model agrees
at every stage with the node's own target model. Existing targetProgram_model
then attaches the literal original programme without any sample comparison,
new preparation or programme construction.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

namespace PositiveGridNode

/-- The stored node views have the SAME actual selected target stage. -/
theorem common_stage
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    {intervals : Nat} {positive : 0 < intervals} {index : Fin intervals}
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
    (retained : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    : retained.common.requested.selected.stage = retained.next.requested.selected.stage :=
  (congrArg (fun common : Shifted
      (increment := Sampling.gridOffset intervals index.succ direction) (target := retained.target)
      source ranges allocation ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      widths roots targetCurrent targetFloor targetRootStage => common.requested.selected.stage)
    retained.common_eq).trans
      (ofSourceAccuracy_stage
        (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source retained.paid.1
        retained.source_eq retained.next)

/-- The stored common view keeps the SAME whole actual target Request at its original shape/attempt owners. -/
theorem common_request
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    {intervals : Nat} {positive : 0 < intervals} {index : Fin intervals}
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
    (retained : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    : HEq retained.common.requested.request retained.next.requested.request := by
  have project (first last : Shifted
      (increment := Sampling.gridOffset intervals index.succ direction) (target := retained.target)
      source ranges allocation ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      widths roots targetCurrent targetFloor targetRootStage) (equal : first = last) :
      HEq first.requested.request last.requested.request := by
    cases equal
    rfl
  exact (project _ _ retained.common_eq).trans
    (ofSourceAccuracy_request
      (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source retained.paid.1
      retained.source_eq retained.next)

/-- Both node displays retain the SAME complete target preparation, models, observations and global allocation. -/
theorem common_prepared
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    {intervals : Nat} {positive : 0 < intervals} {index : Fin intervals}
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
    (retained : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    : HEq retained.common.requested.prepared retained.next.requested.prepared := by
  have project (first last : Shifted
      (increment := Sampling.gridOffset intervals index.succ direction) (target := retained.target)
      source ranges allocation ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      widths roots targetCurrent targetFloor targetRootStage) (equal : first = last) :
      HEq first.requested.prepared last.requested.prepared := by
    cases equal
    rfl
  exact (project _ _ retained.common_eq).trans
    (ofSourceAccuracy_prepared
      (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source retained.paid.1
      retained.source_eq retained.next)

/-- The SAME original target model is read by the common and next views at EVERY original stage. -/
theorem common_model
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    {intervals : Nat} {positive : 0 < intervals} {index : Fin intervals}
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
    (retained : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (channel : Fin 6) (stage : Nat) :
    model retained.common.requested.request.covered retained.common.requested.request.chain
      retained.common.requested.request.attempt.preparationFamily channel stage =
    model retained.next.requested.request.covered retained.next.requested.request.chain
      retained.next.requested.request.attempt.preparationFamily channel stage :=
  (congrArg (fun common : Shifted
      (increment := Sampling.gridOffset intervals index.succ direction) (target := retained.target)
      source ranges allocation ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
      widths roots targetCurrent targetFloor targetRootStage =>
    model common.requested.request.covered common.requested.request.chain
      common.requested.request.attempt.preparationFamily channel stage) retained.common_eq).trans
        (ofSourceAccuracy_model
          (Sampling.gridRequest_minimum intervals positive index direction moving spatial).symm source retained.paid.1
          retained.source_eq retained.next channel stage)

/-- The common view reads the literal original targetProgram model of this SAME actual node at every stage.

The programme owner is the supplied original ValueBlocks on retained.next.
Only the original targetProgram_model law and whole-cache transport are
composed. No programme, geometry, source, target or comparison is rebuilt.
-/
theorem common_model_eq_program
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    {intervals : Nat} {positive : 0 < intervals} {index : Fin intervals}
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
    (retained : PositiveGridNode intervals positive index direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)
    (programmes : ShiftedGeometry.ValueBlocks
      (source := retained.paid.1) (next := retained.next)
      (spatial := spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))
      (nonzero := Sampling.gridOffset_nonzero intervals positive index direction moving))
    (channel : Fin 6) (stage : Nat) :
    model retained.common.requested.request.covered retained.common.requested.request.chain
      retained.common.requested.request.attempt.preparationFamily channel stage =
    ((programmes.targetProgram (next := retained.next) channel).model stage) :=
  (retained.common_model channel stage).trans
    (programmes.targetProgram_model (next := retained.next) channel stage).symm

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
