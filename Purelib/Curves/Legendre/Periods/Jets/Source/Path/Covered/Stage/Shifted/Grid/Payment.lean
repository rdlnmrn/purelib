module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion
public import Purelib.Curves.Legendre.Periods.Jets.Connection.Euler.Request
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Source
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Connection
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Integration.Program.Gaussian.Basic

/-! # Internally paid connection readings on the same original positive-grid programmes

One tighter spatial request precedes the original common source and node
factories. Their actual selections then pay the same fixed original-strip
connection floor. The original node Completion family attaches its six
programmes, deriving slope-to-connection comparison at its literal stage.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

namespace PositiveGridNode

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.LinearAlgebra.Matrix.Multiplication (matrixVector)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry (ValueBlocks)

/-- Tighten the original spatial request once by the fixed source-frame residual payment at the grid width. -/
def connectionRequest {parameter : Canonical} (frame : Paths.Frame parameter)
    (intervals : Nat) (positive : 0 < intervals) (spatial : AccuracyRequest) : AccuracyRequest :=
  spatial.minimum (Connection.residualRequest (ParameterClearance.ofFrame frame)
    (1 / (intervals : Rational)) (Sampling.gridWidth_positive intervals positive))

/-- The actual combined request continues to pay the original independent spatial accuracy. -/
theorem connectionRequest_le_spatial {parameter : Canonical} (frame : Paths.Frame parameter)
    (intervals : Nat) (positive : 0 < intervals) (spatial : AccuracyRequest) :
    (connectionRequest frame intervals positive spatial).tolerance ≤ spatial.tolerance :=
  spatial.minimum_le_left _

/-- The same whole combined request also pays its original-strip connection-residual accuracy. -/
theorem connectionRequest_le_residual {parameter : Canonical} (frame : Paths.Frame parameter)
    (intervals : Nat) (positive : 0 < intervals) (spatial : AccuracyRequest) :
    (connectionRequest frame intervals positive spatial).tolerance ≤
      (Connection.residualRequest (ParameterClearance.ofFrame frame) (1 / (intervals : Rational))
        (Sampling.gridWidth_positive intervals positive)).tolerance :=
  spatial.minimum_le_right _

section Source

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    (source : Requested covered chain current floor rootStage
      ((connectionRequest frame intervals positive spatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
          (Sampling.gridIncrement_nonzero intervals positive direction moving))))

/-- Build the original source-stage connection Selection and retain both its whole factory and same-stage payment.

The source is an actual new request at the combined accuracy. Its own
selected allowance derives the residual payment; no final connection
sample inequality or separately supplied stage floor is required.
-/
def sourceSelection :
    { selection : Search.Selection 1 source.selected.stage
        ((1 / (intervals : Rational)) ^ 2 * (ParameterClearance.ofFrame frame).connectionLowerSq) //
      selection = Connection.connectionSelection frame (1 / (intervals : Rational))
        (Sampling.gridWidth_positive intervals positive) source.selected.stage ∧
      selection.stage = source.selected.stage } := by
  let selection := Connection.connectionSelection frame (1 / (intervals : Rational))
    (Sampling.gridWidth_positive intervals positive) source.selected.stage
  have paid := (source.selected.later_accurate (Nat.le_refl source.selected.stage)).trans_le
    ((connectionRequest frame intervals positive spatial).minimum_le_left
      (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving)))
  have accurate := (paid.trans_le (connectionRequest_le_residual frame intervals positive spatial)).trans_le
    (Connection.residualRequest_le_source frame (1 / (intervals : Rational))
      (Sampling.gridWidth_positive intervals positive))
  exact ⟨selection, rfl, Connection.connectionSelection_stage_eq_of_accurate frame
    (1 / (intervals : Rational)) (Sampling.gridWidth_positive intervals positive) source.selected.stage accurate⟩

end Source

section Node

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals} {index : Fin intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      ((connectionRequest frame intervals positive spatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
          (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    (node : PositiveGridNode intervals positive index direction moving
      (connectionRequest frame intervals positive spatial) source member ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage)

/-- Build the same actual node-frame connection Selection at its already paid original target stage.

The common and next displays retain exactly the same selected stage. The
original whole-direction strip payment derives the fixed denominator floor
at this actual frame. Only the original numerical Selection is newly
constructed; source, target, query and Completion caches remain unchanged.
-/
def nodeSelection :
    { selection : Search.Selection 1 node.next.requested.selected.stage
        ((1 / (intervals : Rational)) ^ 2 * (ParameterClearance.ofFrame node.target).connectionLowerSq) //
      selection = Connection.connectionSelection node.target (1 / (intervals : Rational))
        (Sampling.gridWidth_positive intervals positive) node.next.requested.selected.stage ∧
      selection.stage = node.next.requested.selected.stage } := by
  let selection := Connection.connectionSelection node.target (1 / (intervals : Rational))
    (Sampling.gridWidth_positive intervals positive) node.next.requested.selected.stage
  have paid := ((congrArg (fun stage => Geometric.Basic.quarterRadius 1 stage) node.common_stage).symm.trans_lt
    (node.common.requested.selected.later_accurate (Nat.le_refl _))).trans_le
      ((connectionRequest frame intervals positive spatial).minimum_le_left
        (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
          (Sampling.gridIncrement_nonzero intervals positive direction moving)))
  have targetAdmitted := allocation.parameter_admitted (Sampling.gridOffset intervals index.succ direction)
    ((Sampling.gridOffset_normSq_le intervals positive index.succ direction).trans admitted)
  have accurate := (paid.trans_le (connectionRequest_le_residual frame intervals positive spatial)).trans_le
    (Connection.residualRequest_le_frame (ParameterClearance.ofFrame frame) (1 / (intervals : Rational))
      (Sampling.gridWidth_positive intervals positive) (Sampling.gridOffset intervals index.succ direction)
      targetAdmitted node.target)
  exact ⟨selection, rfl, Connection.connectionSelection_stage_eq_of_accurate node.target
    (1 / (intervals : Rational)) (Sampling.gridWidth_positive intervals positive)
    node.next.requested.selected.stage accurate⟩

end Node

-- Preserve the original named completion witness, which the law uses only in its proof.
set_option linter.unusedVariables false in
/-- Quantified connection-row payment on the same retained node, programmes and completion. -/
abbrev NodeSlopeBound : Prop :=
  ∀
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    {intervals : Nat} {positive : 0 < intervals} {index : Fin intervals}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      ((connectionRequest frame intervals positive spatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
          (Sampling.gridIncrement_nonzero intervals positive direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {node : PositiveGridNode intervals positive index direction moving
      (connectionRequest frame intervals positive spatial) source member ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage}
    {aligned : DependentProduct (parent :: parents) (fun outer => Acquisition.Segment.RootComparisons.Alignment
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.paths
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.firstReference)}
    {alignedEq : aligned = DependentProduct.ofFn (parent :: parents) (fun outer =>
      (DependentProduct.get (parent :: parents) node.common.blocks outer).comparison.align)}
    {old : QueryAgreement source.prepared}
    (programmes : ValueBlocks (source := node.paid.1) (next := node.next)
      (spatial := (connectionRequest frame intervals positive spatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
          (Sampling.gridIncrement_nonzero intervals positive direction moving)))
      (nonzero := Sampling.gridOffset_nonzero intervals positive index direction moving))
    (completed : CompletionData node aligned alignedEq old) (row : Fin 2),
    Norm.Basic.normSq
      (((programmes.targetProgram (next := node.next) (Specification.Table.firstIndex row)).model
          node.next.requested.selected.stage).integralSample -
        matrixVector (Connection.matrix (parameter + Sampling.gridOffset intervals index.succ direction))
          (vectorOfFn (fun coordinate =>
            ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
              node.next.requested.selected.stage).integralSample)) row) ≤
      (1 / (intervals : Rational)) ^ 2

/-- The actual node programmes satisfy the internally paid original connection-slope comparison.

The retained CompletionData supplies its same whole canonical family.
SourceJet keeps the six original targetCertified programmes. Their public
whole-integral laws derive both actual value and first-row readings at
this node's own selected stage; original sourceSlope_le then pays the
comparison without a supplied slope relation or final sample inequality.
-/
theorem nodeSlope_le : NodeSlopeBound := by
  intro parameter frame basis count parent parents covered chain current floor rootStage intervals positive
    index direction moving spatial source member ranges allocation admitted widths root roots targetCurrent
    targetFloor targetRootStage node aligned alignedEq old programmes completed row
  let actual := programmes.sourceJet (next := node.next) completed.family
  let selection := nodeSelection node
  have values (coordinate : Fin 2) :
      (vectorOfFn (fun coordinate =>
        ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
          node.next.requested.selected.stage).integralSample)) coordinate =
        ((actual.value coordinate).integral.model node.next.requested.selected.stage).integralSample :=
    (vectorOfFn_apply (fun coordinate : Fin 2 =>
      ((programmes.targetProgram (next := node.next) (Specification.Table.valueIndex coordinate)).model
        node.next.requested.selected.stage).integralSample) coordinate).trans
      (congrArg (fun programme : RefinementProgram =>
        (programme.model node.next.requested.selected.stage).integralSample)
          (programmes.sourceJet_value_integral (next := node.next) completed.family coordinate)).symm
  have slope : ((programmes.targetProgram (next := node.next) (Specification.Table.firstIndex row)).model
        node.next.requested.selected.stage).integralSample =
      ((actual.first row).integral.model node.next.requested.selected.stage).integralSample :=
    (congrArg (fun programme : RefinementProgram =>
      (programme.model node.next.requested.selected.stage).integralSample)
        (programmes.sourceJet_first_integral (next := node.next) completed.family row)).symm
  exact Connection.sourceSlope_le actual (1 / (intervals : Rational)) node.next.requested.selected.stage
    node.next.requested.selected.stage selection.val (Nat.le_of_eq selection.property.2) _ _ row values slope

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
