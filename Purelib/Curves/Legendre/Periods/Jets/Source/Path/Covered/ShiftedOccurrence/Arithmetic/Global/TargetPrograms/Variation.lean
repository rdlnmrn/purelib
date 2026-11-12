module

public import
  Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs.Cells
import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction.Variation
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.Variation
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
import Purelib.Data.Gaussian.Norm.Components.Maximum
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Variation

/-! # Variation of literal acquired target programmes

The actual global word and retained local Position prefixes give the exact
ordered flattening. Its same six cached restrictions and nonnegative full
interval widths preserve total variation on every target preparation and
all six original target programme models, without selecting new cells.
-/

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.ValueBlocks

open Purelib.Riemann.Topology

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint finishPoint)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

/-- The same original block's actual target cell views retain its original physical maximum-coordinate variation. -/
private theorem group_variation_eq
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
    (retained : ValueBlocks (next := next))
    {stage : Nat} {targets : CellEndpoints.Targets next.requested.request.chain.path stage}
    (prepared : PreparedParents next.requested.request.covered targetFloor targets)
    (channel : Fin 6) (outer : Fin (parent :: parents).length) :
    (PathModel.mk (retained.groupedCells prepared channel outer)).variation =
      Norm.Components.maximum ((source.prepared.entry outer).preparation.cell.models.cell channel).displacement := by
  let block := retained.block outer
  let original := (source.prepared.entry outer).preparation.cell.models.cell channel
  let cells := fun inner : Fin (ValueBlock.children (next := next) outer).length =>
    (prepared.entry (block.position inner).sourceIndex).preparation.cell.models.cell channel
  have same (inner : Fin (ValueBlock.children (next := next) outer).length) :
      (cells inner).displacement = ((block.cell inner).restriction.model channel).displacement :=
    (((prepared.entry (block.position inner).sourceIndex).cell_displacement channel).trans
      ((next.requested.prepared.entry (block.position inner).sourceIndex).cell_displacement channel).symm).trans
        (block.displacement_eq inner channel)
  have pointwise := sumFin_congr (fun inner => congrArg Norm.Components.maximum (same inner))
  have cached := Restriction.sum_maximum_displacement original
    (fun inner => (block.interval inner).start) (fun inner => (block.interval inner).finish)
    (fun inner => (block.cell inner).restriction.cache channel) block.width_nonnegative block.sum_widths
  exact (PathModel.variation_ofFn cells).trans (pointwise.trans cached)

/-- Every literal target source word has the SAME original-parent variation, at its actual preparation owner.

The existing ordered flattening retains all repeated child occurrences.
Each group's equality consumes its original stored restrictions and full
width sum. No source model or polynomial restriction is constructed here.
-/
public theorem target_variation_eq
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
    (retained : ValueBlocks (next := next))
    {stage : Nat} {targets : CellEndpoints.Targets next.requested.request.chain.path stage}
    (prepared : PreparedParents next.requested.request.covered targetFloor targets)
    (channel : Fin 6) :
    (PathModel.mk ((sources next.requested.request.covered prepared
      next.requested.request.chain).cells channel)).variation = variation (parent :: parents) := by
  have flat := congrArg (fun cells => (PathModel.mk cells).variation)
    (retained.cells_eq_groups (next := next) prepared channel)
  have groups := PathModel.variation_flatten_ofFn
    (fun outer => retained.groupedCells prepared channel outer)
  have originals := sumFin_congr (fun outer =>
    (group_variation_eq (next := next) retained prepared channel outer).trans
      (congrArg Norm.Components.maximum ((source.prepared.entry outer).cell_displacement channel)))
  exact flat.trans (groups.trans originals)

/-- The actual acquired target parent spine has the SAME rational variation as the original source spine. -/
public theorem target_parents_variation
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
    (retained : ValueBlocks (next := next))
    {stage : Nat} {targets : CellEndpoints.Targets next.requested.request.chain.path stage}
    (prepared : PreparedParents next.requested.request.covered targetFloor targets)
    : variation (next.requested.request.shape.val.1 :: next.requested.request.shape.val.2) =
      variation (parent :: parents) :=
  (variation_sources (parameter := parameter + increment) (frame := target)
    next.requested.request.covered prepared next.requested.request.chain 0).symm.trans
      (retained.target_variation_eq (next := next) prepared 0)

/-- Each of the SAME six target programme models retains that identical original physical variation at every stage. -/
public theorem targetProgram_variation
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
    (retained : ValueBlocks (next := next))
    (channel : Fin 6) (stage : Nat) :
    ((retained.targetProgram (next := next) channel).model stage).variation = variation (parent :: parents) :=
  (congrArg PathModel.variation (retained.targetProgram_model (next := next) channel stage)).trans
    (retained.target_variation_eq (next := next) (next.requested.request.attempt.preparationFamily stage) channel)

/-- The SAME selected global target cell word has the original variation through its whole block-flatten equation. -/
public theorem targetCells_variation
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
    (retained : ValueBlocks (next := next))
    (order coordinate : Fin 2) :
    (PathModel.mk (targetCells (next := next) order coordinate)).variation = variation (parent :: parents) := by
  exact (congrArg (fun cells => (PathModel.mk cells).variation)
    (targetCells_eq_sources (next := next) order coordinate)).trans
      (retained.target_variation_eq (next := next) next.requested.prepared
        (Specification.Table.baseIndex order coordinate))

/-- Two actual target preparation words have a numerical error paid by original variation instead of their child count.

Both actual globally allocated preparations and all their models remain
inputs. The same-patch comparison theorem supplies their original query
comparisons; the exact variation readback removes adaptive cardinality.
-/
public theorem target_difference_variation_le
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
    (retained : ValueBlocks (next := next))
    {firstStage lastStage : Nat}
    {firstTargets : CellEndpoints.Targets next.requested.request.chain.path firstStage}
    {lastTargets : CellEndpoints.Targets next.requested.request.chain.path lastStage}
    (first : PreparedParents next.requested.request.covered targetFloor firstTargets)
    (last : PreparedParents next.requested.request.covered targetFloor lastTargets) (channel : Fin 6) :
    Norm.Basic.normSq
      ((PathModel.mk ((sources next.requested.request.covered first next.requested.request.chain).cells
        channel)).integralSample -
        (PathModel.mk ((sources next.requested.request.covered last next.requested.request.chain).cells
          channel)).integralSample) ≤
      32 * (firstTargets.localBound + lastTargets.localBound) * variation (parent :: parents) ^ 2 :=
  (integral_difference_variation_le (parameter := parameter + increment) (frame := target)
    next.requested.request.covered first last next.requested.request.chain channel).trans_eq
      (congrArg (fun length : Rational =>
        32 * (firstTargets.localBound + lastTargets.localBound) * length ^ 2)
        (retained.target_parents_variation (next := next) first))

namespace Integral

/-- The same selected target programme and original source-word samples obey the stronger variation Taylor bound.

The original certificate's output/base/slope readbacks and exact expansion
identify all three samples. Its same-entry stronger remainder theorem is
consumed directly; the old factor field and all original programme owners
are unchanged. The original-patch ceiling remains an explicit local input.
-/
public theorem targetProgramme_remainder_variation_le
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
    {retained : ValueBlocks (next := next)}
    (actual : Integral (next := next) retained) (order coordinate : Fin 2) (ceiling : Rational)
    (ceiling_le : ∀ index : Fin (parent :: parents).length,
      Variation.Point.Step.Joint.rowCeiling ((covered.entry index).val.neighborhood count) 0 order coordinate ≤
        ceiling) :
    Norm.Basic.normSq
      (((retained.targetCertified (next := next) (Specification.Table.baseIndex order coordinate)).integral.model
          next.requested.selected.stage).integralSample -
        (PathModel.mk (oldCells (source := source) (Specification.Table.baseIndex order coordinate))).integralSample -
        increment * (PathModel.mk
          (oldCells (source := source) (Specification.Table.slopeIndex order coordinate))).integralSample) ≤
      (16 * (ceiling + 21 / 2) * variation (parent :: parents) ^ 2) * Norm.Basic.normSq increment ^ 2 := by
  have output := actual.output_targetProgramme (next := next) (retained := retained) order coordinate
  have base := actual.base (next := next) (retained := retained) order coordinate
  have slope := actual.slope (next := next) (retained := retained) order coordinate
  have same := congrArg₂ (fun difference slope : Canonical => difference - increment * slope)
    (congrArg₂ (fun output base : Canonical => output - base) output base) slope
  have remainder := same.symm.trans (actual.certificate order coordinate).expansion
  exact (congrArg Norm.Basic.normSq remainder).trans_le
    (actual.remainder_variation_le (next := next) (retained := retained) order coordinate ceiling ceiling_le)

/-- The SAME selected actual target programme gives a first-difference row error with variation in place of count.

The source readings are the original globally allocated old cell words.
The nonzero increment cancels their literal Taylor residual against its
positive quadrance; neither a replacement certificate nor an independent
sample/derivative agreement is introduced. A source-jet attachment still
requires the genuine original completion on that exact source attempt.
-/
public theorem targetProgramme_differenceQuotient_variation_le
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
    {retained : ValueBlocks (next := next)}
    (actual : Integral (next := next) retained) (order coordinate : Fin 2) (ceiling : Rational)
    (ceiling_le : ∀ index : Fin (parent :: parents).length,
      Variation.Point.Step.Joint.rowCeiling ((covered.entry index).val.neighborhood count) 0 order coordinate ≤
        ceiling) :
    Norm.Basic.normSq
      ((((retained.targetCertified (next := next) (Specification.Table.baseIndex order coordinate)).integral.model
            next.requested.selected.stage).integralSample -
          (PathModel.mk (oldCells (source := source)
            (Specification.Table.baseIndex order coordinate))).integralSample) / increment -
        (PathModel.mk (oldCells (source := source)
          (Specification.Table.slopeIndex order coordinate))).integralSample) ≤
      (16 * (ceiling + 21 / 2) * variation (parent :: parents) ^ 2) * Norm.Basic.normSq increment := by
  let output := ((retained.targetCertified (next := next)
    (Specification.Table.baseIndex order coordinate)).integral.model next.requested.selected.stage).integralSample
  let base := (PathModel.mk (oldCells (source := source)
    (Specification.Table.baseIndex order coordinate))).integralSample
  let slope := (PathModel.mk (oldCells (source := source)
    (Specification.Table.slopeIndex order coordinate))).integralSample
  have numerator : increment * ((output - base) / increment - slope) =
      output - base - increment * slope := by
    change increment * ((output - base) * increment⁻¹ - slope) = _
    calc
      _ = (increment * increment⁻¹) * (output - base) - increment * slope := by ring1
      _ = _ := by
        rewrite [Canonical.mul_inv_cancel increment nonzero, Canonical.one_mul]
        rfl
  have original := actual.targetProgramme_remainder_variation_le (next := next) (retained := retained)
    order coordinate ceiling ceiling_le
  have scaled := (congrArg Norm.Basic.normSq numerator).trans_le original
  rewrite [Norm.Basic.normSq_mul] at scaled
  have multiplied :
      Norm.Basic.normSq ((output - base) / increment - slope) * Norm.Basic.normSq increment ≤
        ((16 * (ceiling + 21 / 2) * variation (parent :: parents) ^ 2) * Norm.Basic.normSq increment) *
          Norm.Basic.normSq increment :=
    (Field.mul_comm _ _).trans_le (scaled.trans_eq (by ring1))
  exact Order.Arithmetic.le_of_mul_le_mul_right_direct multiplied (Norm.Basic.normSq_pos nonzero)

end Integral

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.ShiftedGeometry.ValueBlocks
