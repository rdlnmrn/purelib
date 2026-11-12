module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Table
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Sampling.Grid.Trace
public import Purelib.Calculus.Jet.Quadratic.Transport
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy.Transport
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs

/-! # The initial grid edge on the same original retained programme blocks

The first positive node already stores the original four-row ValueBlocks.
Only their integral aggregation is materialized here. Exact source accuracy
transport attaches its base and slope to the incoming completed source;
its output is the same first node's actual selected programme sample.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

namespace PositiveGridNode

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry
  (ValueBlocks BetweenRows Position)
open Purelib.Calculus.Jet
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

section OriginalSource

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (source : Requested covered chain current floor rootStage accuracy)
    (member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt })

/-- Read one literal channel sample of the same actual completed source Stage. -/
@[expose] def sourceSample (channel : Fin 6) : Canonical :=
  (PathModel.mk (member.val.2.2.val.sources.cells channel)).integralSample

/-- The completed source's literal sample is the same original requested preparation's cell-word sample.

The proof consumes the retained member's whole attempt identity and the
original completion source readback. It does not construct a preparation,
all-stage family, programme, completion or new source observation.
-/
theorem sourceSample_eq (channel : Fin 6) : sourceSample source member channel =
    (PathModel.mk ((sources covered source.prepared chain).cells channel)).integralSample := by
  have completed := (Completion.stage_sources member.val.1 member.val.2).trans
    member.val.1.preparations_sources
  have requested := congrArg
    (fun attempt : StageAttempt covered chain source.selected.stage floor rootStage =>
      sources covered attempt.2.1 chain) member.property
  exact congrArg (fun word => (PathModel.mk (word.cells channel)).integralSample)
    (completed.trans requested)

/-- The common source's original selected-stage model reads the same literal completed-source sample.

The original preparationFamily selected branch consumes the actual cache.
This is a model/sample readback, with no new programme or all-stage family.
-/
theorem sourceSample_model (channel : Fin 6) :
    (model covered chain source.attempt.preparationFamily channel source.selected.stage).integralSample =
      sourceSample source member channel :=
  (congrArg (fun word => (PathModel.mk (word.cells channel)).integralSample)
    source.attempt.preparationFamily_sources).trans (sourceSample_eq source member channel).symm

end OriginalSource

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat}
    (intervals : Nat) (positive : 0 < intervals) (direction : Canonical) (moving : direction ≠ 0)
    (spatial : AccuracyRequest)
    (source : Requested covered chain current floor rootStage
      (spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving))))
    (member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt })
    (ranges : ParameterRange covered) (allocation : ParameterRange.StripAllocation ranges)
    (admitted : Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (parent :: parents).length → AccuracyRequest)
    {root : Named} (roots : RootChain (parent :: parents) root root)
    (targetCurrent targetFloor targetRootStage : Nat)

variable {intervals positive direction moving spatial source member ranges allocation admitted widths roots
    targetCurrent targetFloor targetRootStage}
    (table : Table intervals positive direction moving spatial source member
      ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage)

namespace Table

/-- The same stored first positive node, without another node factory. -/
@[expose] def firstNode : PositiveGridNode intervals positive (Sampling.gridFirstIndex intervals positive)
    direction moving spatial source member ranges allocation admitted widths roots
      targetCurrent targetFloor targetRootStage :=
  table.nodes.node (Sampling.gridFirstIndex intervals positive)

/-- The original integral cache type on the same stored first node's programme blocks. -/
@[expose] def FirstIntegral :=
  ValueBlocks.Integral (next := table.firstNode.next)
    (table.programmes.entry (Sampling.gridFirstIndex intervals positive))

/-- A literal sample of the same positive node's original programme at its own selected target stage. -/
@[expose] def positiveSample (index : Fin intervals) (channel : Fin 6) : Canonical :=
  (((table.programmes.entry index).targetProgram (next := (table.nodes.node index).next) channel).model
    (table.nodes.node index).next.requested.selected.stage).integralSample

/-- The original first node's paid-source cell word is the same common source word at its equal accuracy. -/
private theorem first_oldCells (channel : Fin 6) :
    ValueBlocks.oldCells (source := table.firstNode.paid.1) channel =
      (sources covered source.prepared chain).cells channel := by
  have paid := congrArg
    (fun request : Requested covered chain current floor rootStage
      ((spatial.minimum (Sampling.incrementRequest (Sampling.gridIncrement intervals direction)
        (Sampling.gridIncrement_nonzero intervals positive direction moving))).minimum
          (Sampling.incrementRequest
            (Sampling.gridOffset intervals (Sampling.gridFirstIndex intervals positive).succ direction)
            (Sampling.gridOffset_nonzero intervals positive (Sampling.gridFirstIndex intervals positive)
              direction moving))) =>
        (sources covered request.prepared chain).cells channel)
    table.firstNode.source_eq
  exact (ValueBlocks.oldCells_eq_sources (source := table.firstNode.paid.1) channel).trans
    (paid.trans (source.castAccuracy_cells
      (Sampling.gridRequest_minimum intervals positive (Sampling.gridFirstIndex intervals positive)
        direction moving spatial).symm channel))

variable (actual : table.FirstIntegral)

/-- The first original certificate reads the actual incoming completed-source base channel. -/
theorem first_base (order coordinate : Fin 2) :
    (actual.certificate order coordinate).base =
      sourceSample source member (Specification.Table.baseIndex order coordinate) :=
  (actual.base order coordinate).trans
    ((congrArg (fun cells => (PathModel.mk cells).integralSample)
      (table.first_oldCells (Specification.Table.baseIndex order coordinate))).trans
        (sourceSample_eq source member (Specification.Table.baseIndex order coordinate)).symm)

/-- The first original certificate reads the actual incoming completed-source derivative channel. -/
theorem first_slope (order coordinate : Fin 2) :
    (actual.certificate order coordinate).slope =
      sourceSample source member (Specification.Table.slopeIndex order coordinate) :=
  (actual.slope order coordinate).trans
    ((congrArg (fun cells => (PathModel.mk cells).integralSample)
      (table.first_oldCells (Specification.Table.slopeIndex order coordinate))).trans
        (sourceSample_eq source member (Specification.Table.slopeIndex order coordinate)).symm)

/-- The first original certificate reads the same first positive node's literal target programme sample. -/
theorem first_output (order coordinate : Fin 2) :
    (actual.certificate order coordinate).output =
      table.positiveSample (Sampling.gridFirstIndex intervals positive)
        (Specification.Table.baseIndex order coordinate) := by
  have cells := (ValueBlocks.targetCells_eq_sources (next := table.firstNode.next) order coordinate).trans
    (congrArg (fun original => original.cells (Specification.Table.baseIndex order coordinate))
      table.firstNode.next.requested.request.attempt.preparationFamily_sources).symm
  exact (actual.output order coordinate).trans
    ((congrArg (fun cells => (PathModel.mk cells).integralSample) cells).trans
      ((table.programmes.entry (Sampling.gridFirstIndex intervals positive)).targetProgram_sample
        (next := table.firstNode.next) (Specification.Table.baseIndex order coordinate)
        table.firstNode.next.requested.selected.stage).symm)

/-- The original first-node row is reindexed only by the exact first-offset equality.

The complete base, slope, output, remainder, factor and original certificate
remain retained. No second ValueBlocks, node, programme, shifted acquisition
or zero-offset request is executed.
-/
@[expose] def firstCertificate (order coordinate : Fin 2) :
    Quadratic.Basic.Certificate (Sampling.gridIncrement intervals direction) :=
  (actual.certificate order coordinate).castIncrement (Sampling.gridOffset_first intervals positive direction)

/-- The complete first-edge certificate retains the same first-node aggregate heterogeneously. -/
theorem firstCertificate_heq (order coordinate : Fin 2) :
    HEq (table.firstCertificate actual order coordinate) (actual.certificate order coordinate) :=
  (actual.certificate order coordinate).castIncrement_heq (Sampling.gridOffset_first intervals positive direction)

end Table

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
