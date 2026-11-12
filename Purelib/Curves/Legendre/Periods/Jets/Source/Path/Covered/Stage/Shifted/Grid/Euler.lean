module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Payment
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Trace
public import Purelib.Calculus.Linear.Euler.Blocks
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Jet
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Connection
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Retained.Transport
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Source
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Fin
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

/-! # The original positive-grid certificates drive the same finite Euler trace

Every local defect consumes two already-stored order-zero row certificates.
The source or preceding positive node supplies its same retained Completion
family and paid numerical Selection. Consecutive coarse blocks retain the
original fine sample order and apply the computed interval growth budget.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

namespace PositiveGridNode

open Purelib
open Purelib.Algebra.Recurrence
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.PicardFuchs.Clearance (ParameterClearance)
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Vector (map zipWith)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply vector_ext map_apply)
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Gaussian
open Purelib.Calculus.Linear
open Purelib.Calculus.Jet.Quadratic.Basic (Certificate)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain Named)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry (ValueBlocks)

/-- The original selected source member is the literal selected-stage model of its original completed family. -/
private theorem source_staged_sample
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {accuracy : AccuracyRequest}
    (source : Requested covered chain current floor rootStage accuracy)
    (member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt })
    (channel : Fin 6) :
    ((StageAttempt.staged covered chain
      (fun stage => (Completed.family covered chain member.val
        (member.property.trans source.attempt_eq) stage).val) channel).integral.model
          source.selected.stage).integralSample = sourceSample source member channel := by
  have cells := (StageAttempt.staged_cells covered chain
    (fun stage => (Completed.family covered chain member.val
      (member.property.trans source.attempt_eq) stage).val) channel source.selected.stage).trans
        (congrArg (fun retained : Completed covered chain source.selected.stage floor rootStage =>
          retained.2.2.val.sources.cells channel)
            (Completed.family_at covered chain member.val (member.property.trans source.attempt_eq)))
  exact congrArg (fun cells => (PathModel.mk cells).integralSample) cells

/-- The fixed original-strip ceiling for the actual direction-scaled connection matrix. -/
@[expose] def coefficientCeiling {parameter : Canonical} (frame : Paths.Frame parameter)
    (direction : Canonical) : Rational :=
  Norm.Basic.normSq direction * Connection.matrixCeiling (ParameterClearance.ofFrame frame)

/-- The original directional coefficient ceiling is nonnegative, including constant directions. -/
theorem coefficientCeiling_nonnegative {parameter : Canonical} (frame : Paths.Frame parameter)
    (direction : Canonical) : 0 ≤ coefficientCeiling frame direction :=
  Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg direction)
    (Connection.matrixCeiling_nonnegative (ParameterClearance.ofFrame frame))

/-- Compute the number of coarse Euler intervals from the same original frame and literal direction. -/
@[expose] def coarseIntervals {parameter : Canonical} (frame : Paths.Frame parameter)
    (direction : Canonical) : Nat :=
  Euler.intervalCount 2 (coefficientCeiling frame direction) (coefficientCeiling_nonnegative frame direction)

/-- The original computed coarse interval count is positive for every direction. -/
theorem coarseIntervals_positive {parameter : Canonical} (frame : Paths.Frame parameter)
    (direction : Canonical) : 0 < coarseIntervals frame direction :=
  Euler.intervalCount_positive 2 (coefficientCeiling frame direction) (coefficientCeiling_nonnegative frame direction)

/-- A positive further refinement gives the literal original uniform fine-grid count. -/
theorem fineIntervals_positive {parameter : Canonical} (frame : Paths.Frame parameter)
    (direction : Canonical) (refinement : Nat) (positive : 0 < refinement) :
    0 < coarseIntervals frame direction * refinement := Nat.mul_pos (coarseIntervals_positive frame direction) positive

namespace Table.Trace

/-- Read the two literal value-channel samples from the same stored six-channel grid node. -/
@[expose] def eulerValues
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
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
    {table : Table intervals positive direction moving (connectionRequest frame intervals positive spatial)
      source member ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    (trace : Table.Trace table) (index : Fin (intervals + 1)) : Vec Canonical 2 :=
  vectorOfFn (fun coordinate => trace.sample index (Specification.Table.valueIndex coordinate))

/-- Read both already-stored order-zero row certificates in their original coordinate order. -/
@[expose] def eulerEntries
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
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
    {table : Table intervals positive direction moving (connectionRequest frame intervals positive spatial)
      source member ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    (trace : Table.Trace table) (index : Fin intervals) :
    Vec (Certificate (Sampling.gridIncrement intervals direction)) 2 :=
  vectorOfFn (fun coordinate => trace.certificate index 0 coordinate)

/-- The original two entry factors give one fixed directional Euler factor on every edge. -/
theorem eulerFactor_eq
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
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
    {table : Table intervals positive direction moving (connectionRequest frame intervals positive spatial)
      source member ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    (trace : Table.Trace table) (index : Fin intervals) :
    Connection.eulerFactor (trace.eulerEntries index) direction =
      2 * ((ValueBlocks.factor (covered := covered) 0 0 + ValueBlocks.factor (covered := covered) 0 1) *
        Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction) := by
  have first := (congrArg (fun entry : Certificate (Sampling.gridIncrement intervals direction) => entry.factor)
    (vectorOfFn_apply (fun coordinate => trace.certificate index 0 coordinate) 0)).trans
      (trace.factor_eq index 0 0)
  have last := (congrArg (fun entry : Certificate (Sampling.gridIncrement intervals direction) => entry.factor)
    (vectorOfFn_apply (fun coordinate => trace.certificate index 0 coordinate) 1)).trans
      (trace.factor_eq index 0 1)
  exact congrArg₂ (fun left right : Rational =>
    2 * ((left + right) * Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)) first last

/-- Every retained grid edge has an internally derived defect against its actual directional connection matrix.

The source case uses the supplied genuine selected member. A later edge
uses the preceding node's same stored CompletionData and six programmes.
The numerical selection is paid by the original combined request. All
base, output, slope and factor transports consume original readback laws;
no endpoint, connection, residual or local-defect comparison is an input.
-/
theorem eulerDefect_le
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
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
    {table : Table intervals positive direction moving (connectionRequest frame intervals positive spatial)
      source member ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    (trace : Table.Trace table) (old : QueryAgreement source.prepared)
    (completed : Table.Completions table old) (index : Fin intervals) :
    Norm.vector (Euler.defect
      (Connection.alongMatrix (parameter + Sampling.gridOffset intervals index.castSucc direction) direction)
      (1 / (intervals : Rational)) (trace.eulerValues index.castSucc) (trace.eulerValues index.succ)) ≤
      (2 * ((ValueBlocks.factor (covered := covered) 0 0 + ValueBlocks.factor (covered := covered) 0 1) *
        Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)) *
          (1 / (intervals : Rational)) ^ 4 := by
  let entries := trace.eulerEntries index
  have bases : map Certificate.base entries = trace.eulerValues index.castSucc := by
    apply vector_ext
    intro coordinate
    exact (map_apply Certificate.base entries coordinate).trans
      (((congrArg (fun entry : Certificate (Sampling.gridIncrement intervals direction) => entry.base)
        (vectorOfFn_apply (fun coordinate => trace.certificate index 0 coordinate) coordinate)).trans
          (trace.base index 0 coordinate)).trans
            (vectorOfFn_apply (fun coordinate => trace.sample index.castSucc
              (Specification.Table.valueIndex coordinate)) coordinate).symm)
  have outputs : map Certificate.output entries = trace.eulerValues index.succ := by
    apply vector_ext
    intro coordinate
    exact (map_apply Certificate.output entries coordinate).trans
      (((congrArg (fun entry : Certificate (Sampling.gridIncrement intervals direction) => entry.output)
        (vectorOfFn_apply (fun coordinate => trace.certificate index 0 coordinate) coordinate)).trans
          (trace.output index 0 coordinate)).trans
            (vectorOfFn_apply (fun coordinate => trace.sample index.succ
              (Specification.Table.valueIndex coordinate)) coordinate).symm)
  have entryBase (coordinate : Fin 2) : (entries coordinate).base =
      trace.sample index.castSucc (Specification.Table.valueIndex coordinate) :=
    (congrArg (fun entry : Certificate (Sampling.gridIncrement intervals direction) => entry.base)
      (vectorOfFn_apply (fun coordinate => trace.certificate index 0 coordinate) coordinate)).trans
        (trace.base index 0 coordinate)
  have entrySlope (coordinate : Fin 2) : (entries coordinate).slope =
      trace.sample index.castSucc (Specification.Table.firstIndex coordinate) :=
    (congrArg (fun entry : Certificate (Sampling.gridIncrement intervals direction) => entry.slope)
      (vectorOfFn_apply (fun coordinate => trace.certificate index 0 coordinate) coordinate)).trans
        (trace.slope index 0 coordinate)
  have actual : Norm.vector (Euler.defect
      (Connection.alongMatrix (parameter + Sampling.gridOffset intervals index.castSucc direction) direction)
      (1 / (intervals : Rational)) (map Certificate.base entries) (map Certificate.output entries)) ≤
      Connection.eulerFactor entries direction * (1 / (intervals : Rational)) ^ 4 := by
    by_cases zero : index.val = 0
    · let family := Completed.family covered chain member.val (member.property.trans source.attempt_eq)
      let retained := fun stage => (family stage).val
      let jet := StageAttempt.jet covered chain retained
      let selection := sourceSelection (intervals := intervals) (positive := positive)
        (direction := direction) (moving := moving) (spatial := spatial) source
      have atSource (channel : Fin 6) : trace.sample index.castSucc channel = sourceSample source member channel :=
        (trace.sample_eq index.castSucc channel).trans
          ((congrArg (fun node => table.sampleAt node channel)
            (Sampling.gridIndex_zero intervals index zero)).trans (table.sampleAt_zero channel))
      have base_eq (coordinate : Fin 2) : (entries coordinate).base =
          ((jet.value coordinate).integral.model source.selected.stage).integralSample :=
        ((entryBase coordinate).trans (atSource (Specification.Table.valueIndex coordinate))).trans
          ((source_staged_sample source member (Specification.Table.valueIndex coordinate)).symm.trans
            (congrArg (fun programme : RefinementProgram =>
              (programme.model source.selected.stage).integralSample)
                (StageAttempt.jet_value_integral covered chain retained coordinate)).symm)
      have slope_eq (coordinate : Fin 2) : (entries coordinate).slope =
          ((jet.first coordinate).integral.model source.selected.stage).integralSample :=
        ((entrySlope coordinate).trans (atSource (Specification.Table.firstIndex coordinate))).trans
          ((source_staged_sample source member (Specification.Table.firstIndex coordinate)).symm.trans
            (congrArg (fun programme : RefinementProgram =>
              (programme.model source.selected.stage).integralSample)
                (StageAttempt.jet_first_integral covered chain retained coordinate)).symm)
      have original := Connection.eulerDefect_le jet (1 / (intervals : Rational)) direction rfl
        source.selected.stage source.selected.stage selection.val (Nat.le_of_eq selection.property.2)
        entries base_eq slope_eq
      have parameter_eq : parameter + Sampling.gridOffset intervals index.castSucc direction = parameter := by
        have nodeZero := Grid.Unit.node_zero index.castSucc zero
        have scaledZero : Scale.scale (0 : Rational) direction = 0 := by
          apply Data.Gaussian.Basic.ext <;> change (0 : Rational) * _ = 0 <;> ring1
        exact (congrArg (fun width : Rational => parameter + Scale.scale width direction) nodeZero).trans
          ((congrArg (fun value : Canonical => parameter + value) scaledZero).trans (by ring1))
      exact (congrArg (fun value : Canonical => Norm.vector (Euler.defect
        (Connection.alongMatrix value direction) (1 / (intervals : Rational))
        (map Certificate.base entries) (map Certificate.output entries))) parameter_eq).trans_le original
    · let previous := Sampling.gridPairIndex intervals (Sampling.gridInnerEdge intervals index zero)
      let node := table.nodes.node previous
      let cache := completed.entry previous
      let programmes := table.programmes.entry previous
      let jet := programmes.sourceJet (next := node.next) cache.family
      let selection := nodeSelection node
      have position : previous.succ = index.castSucc := Sampling.gridInnerEdge_first intervals index zero
      have atNode (channel : Fin 6) : trace.sample index.castSucc channel = table.positiveSample previous channel :=
        (trace.sample_eq index.castSucc channel).trans
          ((congrArg (fun boundedIndex => table.sampleAt boundedIndex channel) position.symm).trans
            (table.sampleAt_succ previous channel))
      have base_eq (coordinate : Fin 2) : (entries coordinate).base =
          ((jet.value coordinate).integral.model node.next.requested.selected.stage).integralSample :=
        ((entryBase coordinate).trans (atNode (Specification.Table.valueIndex coordinate))).trans
          (congrArg (fun programme : RefinementProgram =>
            (programme.model node.next.requested.selected.stage).integralSample)
              (programmes.sourceJet_value_integral (next := node.next) cache.family coordinate)).symm
      have slope_eq (coordinate : Fin 2) : (entries coordinate).slope =
          ((jet.first coordinate).integral.model node.next.requested.selected.stage).integralSample :=
        ((entrySlope coordinate).trans (atNode (Specification.Table.firstIndex coordinate))).trans
          (congrArg (fun programme : RefinementProgram =>
            (programme.model node.next.requested.selected.stage).integralSample)
              (programmes.sourceJet_first_integral (next := node.next) cache.family coordinate)).symm
      have original := Connection.eulerDefect_le jet (1 / (intervals : Rational)) direction rfl
        node.next.requested.selected.stage node.next.requested.selected.stage selection.val
        (Nat.le_of_eq selection.property.2) entries base_eq slope_eq
      exact (congrArg (fun value : Fin (intervals + 1) => Norm.vector (Euler.defect
        (Connection.alongMatrix (parameter + Sampling.gridOffset intervals value direction) direction)
        (1 / (intervals : Rational)) (map Certificate.base entries) (map Certificate.output entries)))
          position).symm.trans_le original
  have same := congrArg₂ (fun first last : Vec Canonical 2 => Norm.vector (Euler.defect
    (Connection.alongMatrix (parameter + Sampling.gridOffset intervals index.castSucc direction) direction)
    (1 / (intervals : Rational)) first last)) bases outputs
  exact same.symm.trans_le (actual.trans_eq
    (congrArg (fun factor : Rational => factor * (1 / (intervals : Rational)) ^ 4)
      (trace.eulerFactor_eq index)))

/-- The literal retained node-zero values are the same original selected completed-source readings. -/
theorem eulerValues_zero
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {intervals : Nat} {positive : 0 < intervals}
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
    {table : Table intervals positive direction moving (connectionRequest frame intervals positive spatial)
      source member ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    (trace : Table.Trace table) :
    trace.eulerValues 0 = vectorOfFn (fun coordinate =>
      sourceSample source member (Specification.Table.valueIndex coordinate)) := by
  apply vector_ext
  intro coordinate
  exact (vectorOfFn_apply (fun coordinate => trace.sample 0
    (Specification.Table.valueIndex coordinate)) coordinate).trans
      (((trace.sample_eq 0 (Specification.Table.valueIndex coordinate)).trans
        (table.sampleAt_zero (Specification.Table.valueIndex coordinate))).trans
          (vectorOfFn_apply (fun coordinate => sourceSample source member
            (Specification.Table.valueIndex coordinate)) coordinate).symm)

/-- The retained grid bounds the original Euler trace from any supplied initial vector.

The actual source sample and incoming computed vector remain separate.
Original local defects and the computed coarse growth budget propagate
their quadrance discrepancy through the same affine recurrence, without
a supplied error bound. All node, programme, Completion and row caches
are consumed unchanged; no source acquisition or factory is repeated.
-/
theorem eulerBlocks_from_le
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {refinement : Nat} {positiveRefinement : 0 < refinement}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      ((connectionRequest frame (coarseIntervals frame direction * refinement)
        (fineIntervals_positive frame direction refinement positiveRefinement) spatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement (coarseIntervals frame direction * refinement) direction)
          (Sampling.gridIncrement_nonzero (coarseIntervals frame direction * refinement)
            (fineIntervals_positive frame direction refinement positiveRefinement) direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {table : Table (coarseIntervals frame direction * refinement)
      (fineIntervals_positive frame direction refinement positiveRefinement) direction moving
      (connectionRequest frame (coarseIntervals frame direction * refinement)
        (fineIntervals_positive frame direction refinement positiveRefinement) spatial)
      source member ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    (trace : Table.Trace table) (old : QueryAgreement source.prepared)
    (completed : Table.Completions table old) (initial : Vec Canonical 2) :
    let fineCount := coarseIntervals frame direction * refinement
    let boundedIndex := fun index : Nat => (⟨min index fineCount,
      Nat.lt_succ_of_le (Nat.min_le_right index fineCount)⟩ : Fin (fineCount + 1))
    let coefficients := fun index => Connection.alongMatrix
      (parameter + Sampling.gridOffset fineCount (boundedIndex index) direction) direction
    let fineWidth : Rational := 1 / (fineCount : Rational)
    let factor := 2 * ((ValueBlocks.factor (covered := covered) 0 0 + ValueBlocks.factor (covered := covered) 0 1) *
      Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)
    Norm.vector (zipWith (fun first last => first - last)
      (trace.eulerValues ⟨fineCount, Nat.lt_succ_self fineCount⟩)
      (Euler.trace coefficients (fun _ => fineWidth) initial fineCount)) ≤
      Affine.iterate (fun _ => 2)
        (fun _ => 2 * ((refinement : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3)))
        (Norm.vector (zipWith (fun first last => first - last) (trace.eulerValues 0) initial))
        (coarseIntervals frame direction) := by
  dsimp only
  let fineCount := coarseIntervals frame direction * refinement
  let boundedIndex := fun index : Nat => (⟨min index fineCount,
    Nat.lt_succ_of_le (Nat.min_le_right index fineCount)⟩ : Fin (fineCount + 1))
  let coefficients := fun index => Connection.alongMatrix
    (parameter + Sampling.gridOffset fineCount (boundedIndex index) direction) direction
  let samples := fun index => trace.eulerValues (boundedIndex index)
  let fineWidth : Rational := 1 / (fineCount : Rational)
  let factor := 2 * ((ValueBlocks.factor (covered := covered) 0 0 + ValueBlocks.factor (covered := covered) 0 1) *
    Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)
  have positiveCount : 0 < fineCount := fineIntervals_positive frame direction refinement positiveRefinement
  have factorNonnegative : 0 ≤ factor :=
    (Connection.eulerFactor_nonnegative (trace.eulerEntries ⟨0, positiveCount⟩) direction).trans_eq
      (trace.eulerFactor_eq ⟨0, positiveCount⟩)
  have bounded (index : Nat) (_before : index < fineCount) :
      Norm.matrix (coefficients index) ≤ coefficientCeiling frame direction :=
    Connection.alongMatrix_le (ParameterClearance.ofFrame frame)
      (Sampling.gridOffset fineCount (boundedIndex index) direction) direction
      (allocation.parameter_admitted _
        ((Sampling.gridOffset_normSq_le fineCount positiveCount (boundedIndex index) direction).trans admitted))
  have remainders (index : Nat) (before : index < fineCount) :
      Norm.vector (Euler.defect (coefficients index) fineWidth (samples index) (samples (index + 1))) ≤
        factor * fineWidth ^ 4 := by
    let edge : Fin fineCount := ⟨index, before⟩
    have start : boundedIndex index = edge.castSucc := Fin.ext (Nat.min_eq_left (Nat.le_of_lt before))
    have finish : boundedIndex (index + 1) = edge.succ := Fin.ext (Nat.min_eq_left (Nat.succ_le_of_lt before))
    have sameMatrix := congrArg (fun position => Connection.alongMatrix
      (parameter + Sampling.gridOffset fineCount position direction) direction) start
    have sameStart := congrArg trace.eulerValues start
    have sameFinish := congrArg trace.eulerValues finish
    have first := congrArg₂ (fun matrix current => Norm.vector (Euler.defect matrix fineWidth current
      (samples (index + 1)))) sameMatrix sameStart
    have last := congrArg (fun value => Norm.vector (Euler.defect
      (Connection.alongMatrix (parameter + Sampling.gridOffset fineCount edge.castSucc direction) direction)
      fineWidth (trace.eulerValues edge.castSucc) value)) sameFinish
    exact (first.trans last).trans_le (trace.eulerDefect_le old completed edge)
  have actual := Euler.stability_blocks coefficients samples initial
    (coefficientCeiling frame direction) (coefficientCeiling_nonnegative frame direction)
    refinement positiveRefinement factor factorNonnegative bounded remainders
  have start : boundedIndex 0 = (0 : Fin (fineCount + 1)) := Fin.ext (Nat.min_eq_left (Nat.zero_le fineCount))
  have finish : boundedIndex fineCount = (⟨fineCount, Nat.lt_succ_self fineCount⟩ : Fin (fineCount + 1)) :=
    Fin.ext (Nat.min_eq_left (Nat.le_refl fineCount))
  have initialError : Norm.vector (zipWith (fun first last => first - last) (samples 0) initial) =
      Norm.vector (zipWith (fun first last => first - last) (trace.eulerValues 0) initial) :=
    congrArg (fun values : Vec Canonical 2 => Norm.vector
      (zipWith (fun first last => first - last) values initial))
        (congrArg trace.eulerValues start)
  have left := congrArg (fun values : Vec Canonical 2 => Norm.vector
    (zipWith (fun first last => first - last) values
      (Euler.trace coefficients (fun _ => fineWidth) initial fineCount)))
        (congrArg trace.eulerValues finish)
  have right := congrArg (fun value : Rational =>
    Affine.iterate (fun _ => 2)
      (fun _ => 2 * ((refinement : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3)))
      value (coarseIntervals frame direction)) initialError
  exact left.symm.trans_le (actual.trans_eq right)

/-- The original grid trace, paid completions and computed coarse budget bound the whole finite Euler execution.

The table has the literal count `coarseIntervals frame direction * refinement`.
Its node, programme, Completion and four-row caches are supplied unchanged.
The natural-indexed executor reads exactly those finite samples and matrices
below that count; its harmless terminal extension is never used for an edge.
Every local defect is derived internally by eulerDefect_le, each consecutive
block pays its original width and growth budget, and Affine.comparison
accumulates the actual block errors. The scalar bound depends on fixed
coarse count and original parent factors, rather than an exponential in the
fine-edge count. No source/target/final sample inequality is supplied.
-/
theorem eulerBlocks_le
    {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {refinement : Nat} {positiveRefinement : 0 < refinement}
    {direction : Canonical} {moving : direction ≠ 0} {spatial : AccuracyRequest}
    {source : Requested covered chain current floor rootStage
      ((connectionRequest frame (coarseIntervals frame direction * refinement)
        (fineIntervals_positive frame direction refinement positiveRefinement) spatial).minimum
        (Sampling.incrementRequest (Sampling.gridIncrement (coarseIntervals frame direction * refinement) direction)
          (Sampling.gridIncrement_nonzero (coarseIntervals frame direction * refinement)
            (fineIntervals_positive frame direction refinement positiveRefinement) direction moving)))}
    {member : { value : Completed covered chain source.selected.stage floor rootStage // value.1 = source.attempt }}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {admitted : Norm.Basic.normSq direction ≤ allocation.bound}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {targetCurrent targetFloor targetRootStage : Nat}
    {table : Table (coarseIntervals frame direction * refinement)
      (fineIntervals_positive frame direction refinement positiveRefinement) direction moving
      (connectionRequest frame (coarseIntervals frame direction * refinement)
        (fineIntervals_positive frame direction refinement positiveRefinement) spatial)
      source member ranges allocation admitted widths roots targetCurrent targetFloor targetRootStage}
    (trace : Table.Trace table) (old : QueryAgreement source.prepared)
    (completed : Table.Completions table old) :
    let fineCount := coarseIntervals frame direction * refinement
    let boundedIndex := fun index : Nat => (⟨min index fineCount,
      Nat.lt_succ_of_le (Nat.min_le_right index fineCount)⟩ : Fin (fineCount + 1))
    let coefficients := fun index => Connection.alongMatrix
      (parameter + Sampling.gridOffset fineCount (boundedIndex index) direction) direction
    let fineWidth : Rational := 1 / (fineCount : Rational)
    let factor := 2 * ((ValueBlocks.factor (covered := covered) 0 0 + ValueBlocks.factor (covered := covered) 0 1) *
      Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)
    Norm.vector (zipWith (fun first last => first - last)
      (trace.eulerValues ⟨fineCount, Nat.lt_succ_self fineCount⟩)
      (Euler.trace coefficients (fun _ => fineWidth) (trace.eulerValues 0) fineCount)) ≤
      Affine.iterate (fun _ => 2)
        (fun _ => 2 * ((refinement : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3)))
        0 (coarseIntervals frame direction) := by
  dsimp only
  let fineCount := coarseIntervals frame direction * refinement
  let fineWidth : Rational := 1 / (fineCount : Rational)
  let factor := 2 * ((ValueBlocks.factor (covered := covered) 0 0 + ValueBlocks.factor (covered := covered) 0 1) *
    Norm.Basic.normSq direction ^ 2 + 2 * Norm.Basic.normSq direction)
  have actual := trace.eulerBlocks_from_le (positiveRefinement := positiveRefinement)
    old completed (trace.eulerValues 0)
  dsimp only at actual
  have initialError : Norm.vector (zipWith (fun first last => first - last)
      (trace.eulerValues 0) (trace.eulerValues 0)) = 0 := by
    have coordinates (row : Fin 2) : Norm.Basic.normSq
        (zipWith (fun first last => first - last) (trace.eulerValues 0) (trace.eulerValues 0) row) = 0 :=
      (congrArg Norm.Basic.normSq ((Data.Vector.Basic.zipWith_apply _ _ _ row).trans
        (show trace.eulerValues 0 row - trace.eulerValues 0 row = 0 by ring1))).trans Norm.Basic.normSq_zero
    exact (Algebra.FiniteSum.Fin.sumFin_congr coordinates).trans Algebra.FiniteSum.Fin.sumFin_zero
  exact actual.trans_eq (congrArg (fun value : Rational =>
    Affine.iterate (fun _ => 2)
      (fun _ => 2 * ((refinement : Rational) * (factor * (fineWidth + 1) * fineWidth ^ 3)))
      value (coarseIntervals frame direction)) initialError)

end Table.Trace

end PositiveGridNode

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted

end
