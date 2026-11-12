module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests.Totals
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.OwnerTrace
import Purelib.Curves.Legendre.Periods.Jets.Source
import Purelib.Curves.Legendre.Periods.Jets.Source.Cells
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Integration.Program.Gaussian.Approximation
import Purelib.Integration.Program.Gaussian.Name
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Program
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Partition
import Purelib.Data.List.DependentProduct
import Purelib.Data.Nat.List.Maximum
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer
import Purelib.Polynomial.Dense.Power
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Piece
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Approximation.Rational.Geometric.Search

import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests

import Purelib.Riemann.Readings.UniformPreparedRequests

import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Riemann.Integration.ContinuedPrimitiveOverlap

import Purelib.Riemann.Readings.PreparedPrimitiveSamples

/-! # Shared original coefficient requests along retained parallel moves

One materialized bank determines common model and scalar stages before a
single original source/model/root acquisition. Every original form consumes
that same retained Point, observation and comparison with its own indexed
coefficient and internally derived payment. These are coefficient requests;
whole supplied-Blocks or six-programme integral agreement remains separate.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Data
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds renaming Data → WaistBounds
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Polynomial.Dense.Basic (DensePolynomial)

open Purelib.Data.Rat.Fraction.Order

namespace OwnerTrace

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Approximation
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Vector (DependentVector)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece Layer)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels.CoveredTracedPath (Blocks)
open Purelib.Integration.Path.Dyadic
open OwnerMove.PrimitiveTarget
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport

variable {site : Fin 2} {parameter : Canonical} {quarter : Geometry.Gaussian.UnitCircle.Quarter.UnitCircuitQuarter}
variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
variable {clearance : OwnerBudget.SourceClearance leg}
variable {originalSource : Spatial.Source leg.source leg.sourcePrepared}
variable (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
variable {count : Nat} {frame : Curves.Legendre.Paths.Frame parameter} {basis : Differential 1} {sheet : Fin 2}
variable (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
variable {initialAccuracy : AccuracyRequest} {initial : Piece (forms.get 0) leg.actual initialAccuracy}

section NumericalTotals

open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm
open Purelib.Algebra

variable {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
variable {bank : OwnerMoves.Entries trace.moves} {retained : OwnerMoves.Entries.Primitives bounds bank count}
variable {scalar : Layer initial trace.budget.fine.selection.stage} {factory : bank = OwnerMoves.entries trace.moves}
variable {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
variable {modelFloor scalarFloor pairCurrent : Nat} {target : Fraction.Rational} {positive : 0 < target}
variable {sourceAccuracy : AccuracyRequest} {requestStage : Nat}
variable (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage)
variable (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
variable (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)

/-- The actual retained global Source model and original whole scalar programme meet the computed finite target.

The source parent list, global Targets and source floor remain unchanged.
The scalar sample belongs to its original whole programme at the coarse
stage plus the retained global Taylor maximum, for each actual form.
-/
@[expose] def NumericalSources.ProgrammeAccuracy (channel : Fin 6) : Prop :=
  normSq ((PathModel.mk (values.2.2.2.val.2.2.2.1.val.cells channel)).integralSample -
    ((initial.reweight (forms.get channel)).program.model
      (trace.budget.fine.selection.stage + values.2.2.1.val.2)).integralSample) < target

/-- Each actual whole Source sample meets the original scalar programme through the same retained row caches. -/
theorem NumericalSources.programme_accurate
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan)) (channel : Fin 6) :
    NumericalSources.ProgrammeAccuracy bounds forms values channel := by
  have bounded := NumericalSources.integral_accurate bounds forms values scalarFactory unitSpan layers channel
  have same := congrArg (fun sample => normSq
    ((PathModel.mk (values.2.2.2.val.2.2.2.1.val.cells channel)).integralSample - sample))
    (NumericalSources.scalar_factory bounds forms values scalarFactory unitSpan layers channel)
  exact same.symm.trans_lt bounded

open Purelib.Integration.Path.Primitive.PrimitiveEdge

/-- The same retained whole source model obeys the original later-sample law at an independent model floor. -/
private theorem NumericalSources.source_tail
    {laterFloor laterStage : Nat}
    (last : PreparedParents (count := 1) caches.covered laterFloor
      (CellEndpoints.Targets.build caches.centeredChain.path laterStage))
    (channel : Fin 6) (order : requestStage ≤ laterStage) :
    normSq ((PathModel.mk ((PreparedParents.sources caches.covered last caches.centeredChain).cells
        channel)).integralSample -
      (PathModel.mk (values.2.2.2.val.2.2.2.1.val.cells channel)).integralSample) ≤
        Geometric.Basic.quarterRadius (PreparedParents.errorScale caches.parents) requestStage := by
  have cached (kept : PreparedParents.BlockSources caches values.2.2.1.val.1 requestStage) :
      normSq ((PathModel.mk ((PreparedParents.sources caches.covered last caches.centeredChain).cells
          channel)).integralSample -
        (PathModel.mk (kept.2.2.2.1.val.cells channel)).integralSample) ≤
          Geometric.Basic.quarterRadius (PreparedParents.errorScale caches.parents) requestStage := by
    rcases kept with ⟨⟨chain, chainEq⟩, ⟨targets, targetsEq⟩, prepared, whole, rows⟩
    cases chainEq
    cases targetsEq
    have bounded := PreparedParents.later_close caches.covered caches.centeredChain prepared.val last channel order
    have sample := congrArg (fun path : Source.Path parameter caches.centeredChain.path =>
      (PathModel.mk (path.cells channel)).integralSample) whole.property
    have same := congrArg (fun sample => normSq
      ((PathModel.mk ((PreparedParents.sources caches.covered last caches.centeredChain).cells
        channel)).integralSample - sample)) sample
    exact same.trans_le bounded
  exact cached values.2.2.2.val

/-- The actual global Source geometry and six original scalar allowances give one computed comparison scale. -/
def NumericalSources.comparisonScale
    (cached : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks) :
    Fraction.Rational :=
  PreparedParents.errorScale cached.parents + FiniteSum.Fin.sumFin (fun channel : Fin 6 =>
    16 * (initial.reweight (forms.get channel)).span.width ^ 2 *
      (initial.reweight (forms.get channel)).cell.allowance)

/-- The one computed comparison scale is nonnegative and pays both original programme-owner scales on all six forms. -/
theorem NumericalSources.comparisonScale_bounds
    (cached : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks) :
    0 ≤ comparisonScale (initial := initial) bounds forms cached ∧
      PreparedParents.errorScale cached.parents ≤ comparisonScale (initial := initial) bounds forms cached ∧
      ∀ channel : Fin 6, (initial.reweight (forms.get channel)).program.errorScale ≤
        comparisonScale (initial := initial) bounds forms cached := by
  let scalarScales := fun channel : Fin 6 => 16 * (initial.reweight (forms.get channel)).span.width ^ 2 *
    (initial.reweight (forms.get channel)).cell.allowance
  have scalarNonnegative (channel : Fin 6) : 0 ≤ scalarScales channel :=
    Eq.mp (congrArg (fun scale : Fraction.Rational => 0 ≤ scale)
      ((initial.reweight (forms.get channel)).errorScale_eq))
      (initial.reweight (forms.get channel)).program.errorScale_nonneg
  have totalNonnegative := FiniteSum.Rational.Order.weight_sum_nonnegative scalarScales scalarNonnegative
  have sourceNonnegative := PreparedParents.errorScale_nonnegative cached.parents
  have sourceBound : PreparedParents.errorScale cached.parents ≤
      comparisonScale (initial := initial) bounds forms cached := by
    have added := Arithmetic.add_le_add_direct
      (Fraction.Order.Basic.le_refl (PreparedParents.errorScale cached.parents)) totalNonnegative
    have zero := (Fraction.Field.add_comm (PreparedParents.errorScale cached.parents) 0).trans
      (Fraction.Field.zero_add _)
    exact zero.symm.le.trans added
  refine ⟨?_, sourceBound, ?_⟩
  · have added := Arithmetic.add_le_add_direct sourceNonnegative totalNonnegative
    exact (Fraction.Field.zero_add (0 : Fraction.Rational)).symm.le.trans added
  · intro channel
    have entry := FiniteSum.Rational.Order.entry_le_sumFin scalarScales scalarNonnegative channel
    have combined := Arithmetic.add_le_add_direct sourceNonnegative
      (Fraction.Order.Basic.le_refl (FiniteSum.Fin.sumFin scalarScales))
    exact ((initial.reweight (forms.get channel)).errorScale_eq.trans_le entry).trans
      ((Fraction.Field.zero_add _).symm.le.trans combined)

/-- Both once-computed global floors retain the original caller's model and scalar lower bounds. -/
theorem NumericalSources.minimum_le :
    modelFloor ≤ values.2.2.1.val.1 ∧ scalarFloor ≤ values.2.2.1.val.2 := by
  have original := numericalFloors_minimum bounds forms values.2.1.val
  exact ⟨original.1.trans_eq (congrArg (fun floors : Nat × Nat => floors.1) values.2.2.1.property).symm,
    original.2.trans_eq (congrArg (fun floors : Nat × Nat => floors.2) values.2.2.1.property).symm⟩

/-- Actual independent later programme samples meet the target through one retained global source/scalar acquisition. -/
private theorem NumericalSources.tails_accurate
    (sourceFloor leftStart rightStart : Nat) (scale : Fraction.Rational)
    (selected : Geometric.Search.Selection scale (max leftStart rightStart) ((target / 4) / 4))
    (sourceScale : PreparedParents.errorScale caches.parents ≤ scale)
    (scalarScale : ∀ channel : Fin 6, (initial.reweight (forms.get channel)).program.errorScale ≤ scale)
    (prepared : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor
      (max scalarFloor selected.stage) pairCurrent ((target / 4) / 4)
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) (by decide +kernel))
      sourceAccuracy selected.stage)
    (layers : NumericalLayerRows bounds forms prepared.2.1.val prepared.2.2.1.val.2
      (prepared.inputSpans bounds forms scalarFactory unitSpan))
    (channel : Fin 6) {leftLater rightLater : Nat} (leftOrder : selected.stage ≤ leftLater)
    (rightOrder : trace.budget.fine.selection.stage + prepared.2.2.1.val.2 ≤ rightLater) :
    let original := fun index => Source.Cell.prepareCovered caches.covered sourceFloor
      (CellEndpoints.Targets.build caches.centeredChain.path index)
    normSq
      (((PreparedParents.program caches.covered caches.centeredChain original channel).model leftLater).integralSample -
        ((initial.reweight (forms.get channel)).program.model rightLater).integralSample) < target := by
  let original := fun index => Source.Cell.prepareCovered caches.covered sourceFloor
    (CellEndpoints.Targets.build caches.centeredChain.path index)
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  have selectedPaid : Geometric.Basic.quarterRadius scale selected.stage < (target / 4) / 4 :=
    selected.allowance_eq.symm.trans_lt selected.accurate
  have sourceTail := NumericalSources.source_tail bounds forms prepared (original leftLater) channel leftOrder
  have sourcePaid := sourceTail.trans_lt
    ((Geometric.Basic.quarterRadius_scale_mono sourceScale selected.stage).trans_lt selectedPaid)
  have middlePaid := NumericalSources.programme_accurate bounds forms prepared scalarFactory unitSpan layers channel
  have firstTwo := Norm.Bounds.normSq_sub_lt_of_quarter_bounds
    (target := target / 4) sourcePaid middlePaid
  let actual := initial.reweight (forms.get channel)
  let depth := trace.budget.fine.selection.stage + prepared.2.2.1.val.2
  have tail := actual.program.later_close rightOrder
  have tailBasic := (Norm.Basic.normSq_eq_canonical _).trans_le tail
  have swapped := (Norm.Bounds.normSq_sub_symm
    (actual.program.model depth).integralSample (actual.program.model rightLater).integralSample).trans_le tailBasic
  have stagePaid : selected.stage ≤ depth :=
    ((Nat.Order.le_max_right scalarFloor selected.stage).trans
      (NumericalSources.minimum_le bounds forms prepared).2).trans (Nat.le_add_left _ _)
  have scalarTail := swapped.trans
    (Geometric.Basic.quarterRadius_antitone actual.program.errorScale_nonneg stagePaid)
  have scalarSmall := scalarTail.trans_lt
    ((Geometric.Basic.quarterRadius_scale_mono (scalarScale channel) selected.stage).trans_lt selectedPaid)
  have small_le : (target / 4) / 4 ≤ target / 4 := (Bounds.Quarter.quarter_lt_self quarterPositive).le
  have final := Norm.Bounds.normSq_sub_lt_of_quarter_bounds
    (target := target) firstTwo (scalarSmall.trans_le small_le)
  have readback := congrArg PathModel.integralSample
    (PreparedParents.program_model caches.covered caches.centeredChain original channel leftLater)
  exact (congrArg normSq (congrArg
    (fun sample => sample - (actual.program.model rightLater).integralSample) readback)).trans_lt final

/-- One actual global acquisition retains its selected stage, original Source/Layer banks, samples and six comparisons.

The exact Sigma uses the original comparison vector and cache owners.
Selection and both global floors precede the one Source acquisition; all
scalar Points and shared root/readModel/comparison triples are acquired
once before the final per-form comparison records are materialized.
-/
@[expose] def NumericalSources.ProgrammeRequest
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (sourceFloor leftStart rightStart : Nat) : Type 2 :=
  let scale := NumericalSources.comparisonScale (initial := initial) bounds forms caches
  let smallPositive := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) (by decide +kernel)
  let original := fun index => Source.Cell.prepareCovered caches.covered sourceFloor
    (CellEndpoints.Targets.build caches.centeredChain.path index)
  let left := fun channel =>
    (PreparedParents.program caches.covered caches.centeredChain original channel).approximation
  let right := fun channel => (initial.reweight (forms.get channel)).program.approximation
  Σ selected : Geometric.Search.Selection scale (max leftStart rightStart) ((target / 4) / 4),
  Σ prepared : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor
      (max scalarFloor selected.stage) pairCurrent ((target / 4) / 4) smallPositive sourceAccuracy selected.stage,
  Σ layers : NumericalLayerRows bounds forms prepared.2.1.val prepared.2.2.1.val.2
      (prepared.inputSpans bounds forms scalarFactory unitSpan),
  Σ _samples : {actual : List (DependentVector (fun _ : Fin 6 => Canonical)) //
      actual = NumericalLayerRows.samples bounds forms prepared scalarFactory unitSpan layers},
    {comparisons : CoefficientRequests.LayerBank.ParentSources.ProgramComparisons
        left right leftStart rightStart target //
      ∀ channel : Fin 6, (comparisons.get channel).leftIndex = selected.stage ∧
        (comparisons.get channel).rightIndex = trace.budget.fine.selection.stage + prepared.2.2.1.val.2}

/-- Compare all six actual whole geometric/scalar programmes at independent starts and arbitrary requested accuracy.

The original global Source preparation and same-depth scalar acquisition
are retained once. Both inputs keep their original parents, observations
and sample procedures. Actual finite row/factory bounds and original
independent-floor tail laws supply the final comparison internally.
-/
def NumericalSources.compareProgrammes
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (sourceFloor leftStart rightStart : Nat) :
    NumericalSources.ProgrammeRequest (originalSource := originalSource) (initial := initial)
      (count := count) (frame := frame) (basis := basis) (sheet := sheet)
      bounds forms trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy scalarFactory unitSpan sourceFloor leftStart rightStart := by
  let scale := NumericalSources.comparisonScale (initial := initial) bounds forms caches
  have scales := NumericalSources.comparisonScale_bounds (initial := initial) bounds forms caches
  have smallPositive : 0 < (target / 4) / 4 := Fraction.Order.Field.div_pos_direct
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) (by decide +kernel)
  let selected := Geometric.Search.Selection.build scale scales.1 (max leftStart rightStart)
    ((target / 4) / 4) smallPositive
  let prepared := prepareSources bounds forms trace bank retained scalar factory caches modelFloor
    (max scalarFloor selected.stage) pairCurrent ((target / 4) / 4) smallPositive sourceAccuracy selected.stage
  let lastIndex := trace.budget.fine.selection.stage + prepared.2.2.1.val.2
  let layers := prepared.acquireLayers bounds forms scalarFactory unitSpan
  let samples := NumericalLayerRows.samples bounds forms prepared scalarFactory unitSpan layers
  let original := fun index => Source.Cell.prepareCovered caches.covered sourceFloor
    (CellEndpoints.Targets.build caches.centeredChain.path index)
  have firstPaid : leftStart ≤ selected.stage := (Nat.Order.le_max_left leftStart rightStart).trans selected.lower
  have stagePaid : selected.stage ≤ lastIndex :=
    ((Nat.Order.le_max_right scalarFloor selected.stage).trans
      (NumericalSources.minimum_le bounds forms prepared).2).trans (Nat.le_add_left _ _)
  have lastPaid : rightStart ≤ lastIndex :=
    ((Nat.Order.le_max_right leftStart rightStart).trans selected.lower).trans stagePaid
  let entry (channel : Fin 6) : Gaussian.Equivalence.Comparison
      (PreparedParents.program caches.covered caches.centeredChain original channel).approximation
      (initial.reweight (forms.get channel)).program.approximation leftStart rightStart target :=
    { leftIndex := selected.stage
      rightIndex := lastIndex
      left_ge := firstPaid
      right_ge := lastPaid
      close := by
        intro leftLater rightLater leftOrder rightOrder
        exact NumericalSources.tails_accurate (trace := trace) (bank := bank) (retained := retained)
          (scalar := scalar) (factory := factory) (caches := caches)
          (modelFloor := modelFloor) (scalarFloor := scalarFloor) (pairCurrent := pairCurrent)
          (target := target) (positive := positive) (sourceAccuracy := sourceAccuracy)
          bounds forms scalarFactory unitSpan sourceFloor leftStart rightStart
          scale selected scales.2.1 scales.2.2 prepared layers channel leftOrder rightOrder }
  let comparisons := DependentVector.ofFn entry
  have indices (channel : Fin 6) : (comparisons.get channel).leftIndex = selected.stage ∧
      (comparisons.get channel).rightIndex = trace.budget.fine.selection.stage + prepared.2.2.1.val.2 := by
    have same := DependentVector.ofFn_get entry channel
    exact ⟨congrArg (fun actual => actual.leftIndex) same, congrArg (fun actual => actual.rightIndex) same⟩
  exact ⟨selected, prepared, layers, ⟨samples, rfl⟩, ⟨comparisons, indices⟩⟩

/-- The same actual global request and original six sampler-receipt/comparison payloads at independent named starts.

The exact Sigma retains one whole raw acquisition. The existing original
sampler composition consumes its saved comparison vector and preserves
both actual sampler receipts per channel; no identity between raw and
emitted sampler indices is assumed.
-/
@[expose] def NumericalSources.NamedProgrammeRequest
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (sourceFloor rawLeftStart rawRightStart leftStart rightStart : Nat) : Type 2 :=
  let original := fun index => Source.Cell.prepareCovered caches.covered sourceFloor
    (CellEndpoints.Targets.build caches.centeredChain.path index)
  let left := fun channel =>
    (PreparedParents.program caches.covered caches.centeredChain original channel).approximation
  let right := fun channel => (initial.reweight (forms.get channel)).program.approximation
  Σ _raw : NumericalSources.ProgrammeRequest bounds forms trace bank retained scalar factory caches
      modelFloor scalarFloor pairCurrent ((target / 4) / 4)
      (Bounds.Quarter.quarter_pos (Bounds.Quarter.quarter_pos positive)) sourceAccuracy scalarFactory unitSpan
      sourceFloor rawLeftStart rawRightStart,
    DependentVector (fun channel : Fin 6 =>
      (Gaussian.Equivalence.Comparison (Gaussian.Name.Sampling.approximation (left channel).toNamed) (left channel)
          leftStart rawLeftStart ((target / 4) / 4) ×
        Gaussian.Equivalence.Comparison (Gaussian.Name.Sampling.approximation (right channel).toNamed) (right channel)
          rightStart rawRightStart (target / 4)) ×
      Gaussian.Equivalence.Comparison (Gaussian.Name.Sampling.approximation (left channel).toNamed)
        (Gaussian.Name.Sampling.approximation (right channel).toNamed) leftStart rightStart target)

/-- Pay actual named-sampler comparisons from one retained all-six raw global request without another raw acquisition.

The original generic sampler operation retains its full valid composition
route. Sampling may request additional genuine programme stages; those
payments remain explicit in the returned receipts, rather than being
identified with the raw cached model indices.
-/
def NumericalSources.compareNamedProgrammes
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (sourceFloor rawLeftStart rawRightStart leftStart rightStart : Nat) :
    NumericalSources.NamedProgrammeRequest (originalSource := originalSource) (initial := initial)
      (count := count) (frame := frame) (basis := basis) (sheet := sheet)
      bounds forms trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
      target positive sourceAccuracy scalarFactory unitSpan sourceFloor rawLeftStart rawRightStart
      leftStart rightStart := by
  let raw := NumericalSources.compareProgrammes bounds forms trace bank retained scalar factory caches
    modelFloor scalarFloor pairCurrent ((target / 4) / 4)
    (Bounds.Quarter.quarter_pos (Bounds.Quarter.quarter_pos positive)) sourceAccuracy scalarFactory unitSpan
    sourceFloor rawLeftStart rawRightStart
  let original := fun index => Source.Cell.prepareCovered caches.covered sourceFloor
    (CellEndpoints.Targets.build caches.centeredChain.path index)
  let left := fun channel =>
    (PreparedParents.program caches.covered caches.centeredChain original channel).approximation
  let right := fun channel => (initial.reweight (forms.get channel)).program.approximation
  let comparisons := CoefficientRequests.LayerBank.namedRows left right rawLeftStart rawRightStart
    leftStart rightStart target positive raw.2.2.2.2.val
  exact ⟨raw, comparisons⟩

/-- The six original whole Source/scalar programme outputs are operationally equivalent on their retained owners.

Every named comparison request constructs the internally paid global bank
and consumes its saved raw comparisons. Independent sampler stages remain
separate from raw stages. The detailed request operation exposes the full
retained banks and sampler receipts; this original Equivalent view returns
only the requested operational comparison.
-/
def NumericalSources.equivalent
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves) (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (scalar : Layer initial trace.budget.fine.selection.stage) (factory : bank = OwnerMoves.entries trace.moves)
    (caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks)
    (modelFloor scalarFloor pairCurrent : Nat) (sourceAccuracy : AccuracyRequest)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1) (sourceFloor : Nat) (channel : Fin 6) :
    let original := fun index => Source.Cell.prepareCovered caches.covered sourceFloor
      (CellEndpoints.Targets.build caches.centeredChain.path index)
    Gaussian.Equivalence.NamedEquivalent
      (PreparedParents.program caches.covered caches.centeredChain original channel).output.name
      (initial.reweight (forms.get channel)).program.output.name := by
  let original := fun index => Source.Cell.prepareCovered caches.covered sourceFloor
    (CellEndpoints.Targets.build caches.centeredChain.path index)
  change Gaussian.Equivalence.NamedEquivalent
    (PreparedParents.program caches.covered caches.centeredChain original channel).approximation.toNamed
    (initial.reweight (forms.get channel)).program.approximation.toNamed
  refine ⟨?_⟩
  intro leftStart rightStart requestedTarget requestedPositive
  let requested := NumericalSources.compareNamedProgrammes bounds forms trace bank retained scalar factory caches
    modelFloor scalarFloor pairCurrent requestedTarget requestedPositive sourceAccuracy scalarFactory unitSpan
    sourceFloor 0 0 leftStart rightStart
  exact (requested.2.get channel).2

end NumericalTotals

end OwnerTrace

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
