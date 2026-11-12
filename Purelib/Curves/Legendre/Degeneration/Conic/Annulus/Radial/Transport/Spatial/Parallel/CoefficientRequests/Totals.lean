module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests.Sources
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
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
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

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
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

/-- The actual global source split has exactly the original moving occurrence count, excluding stationary handoffs.

The complete original inputs and retained certificates are quantified in
this proposition, including their ownership indices and finite bounds.
-/
@[expose] def NumericalSources.RowCountLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {quarter : UnitCircuitQuarter}
    {leg : Leg site parameter quarter}
    {coarse : Leg.TraceBudget leg}
    {clearance : OwnerBudget.SourceClearance leg}
    {originalSource : Spatial.Source leg.source leg.sourcePrepared}
    (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
    {count : Nat}
    {frame : Curves.Legendre.Paths.Frame parameter}
    {basis : Differential 1}
    {sheet : Fin 2}
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest}
    {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor : Nat}
    {scalarFloor : Nat}
    {pairCurrent : Nat}
    {target : Fraction.Rational}
    {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    {requestStage : Nat}
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage),
    values.2.2.2.val.2.2.2.2.val.length =
      (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length

/-- The actual global source split has exactly the original moving occurrence count, excluding stationary handoffs. -/
theorem NumericalSources.row_count : NumericalSources.RowCountLaw := by
  unfold NumericalSources.RowCountLaw
  intro site parameter quarter leg coarse clearance originalSource bounds count frame basis sheet forms
    initialAccuracy initial trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage values
  let sources := values.2.2.2.val
  have original := OwnerMoves.sourceRows (moves := trace.moves) (original := sources.1.val.path)
    (stage := requestStage) (floor := values.2.2.1.val.1) (targets := sources.2.1.val)
    ⟨bank, factory⟩ frame basis sheet caches sources.2.2.1.val
  have factory := PreparedParents.blockRows_eq_mapBanks caches sources.2.2.1.val
  exact (congrArg List.length sources.2.2.2.2.property.1).trans
    ((congrArg List.length factory).trans original.1)

/-- Materialize the six actual integral readings of every supplied scalar Layer row in its original order.

Structural mapping consumes the retained complete row head and literal
tail once. The six stored Layer payloads supply their numerical models;
no Point, request, Selection or preparation producer is executed.
-/
def NumericalLayerRows.samples
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan)) :
    List (DependentVector (fun _ : Fin 6 => Canonical)) :=
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  DependentProduct.mapToList times layers (fun _ acquired => DependentVector.ofFn (fun channel : Fin 6 =>
    (CoefficientRequests.LayerBank.layer bounds acquired.1.val channel).model.integralSample))

/-- The materialized actual scalar readings preserve the complete original moving occurrence count.

The complete original inputs and retained certificates are quantified in
this proposition, including their ownership indices and finite bounds.
-/
@[expose] def NumericalLayerRows.SamplesLengthLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {quarter : UnitCircuitQuarter}
    {leg : Leg site parameter quarter}
    {coarse : Leg.TraceBudget leg}
    {clearance : OwnerBudget.SourceClearance leg}
    {originalSource : Spatial.Source leg.source leg.sourcePrepared}
    (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
    {count : Nat}
    {frame : Curves.Legendre.Paths.Frame parameter}
    {basis : Differential 1}
    {sheet : Fin 2}
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest}
    {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor : Nat}
    {scalarFloor : Nat}
    {pairCurrent : Nat}
    {target : Fraction.Rational}
    {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    {requestStage : Nat}
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan)),
    (samples bounds forms values scalarFactory unitSpan layers).length =
      (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length

/-- The materialized actual scalar readings preserve the complete original moving occurrence count. -/
theorem NumericalLayerRows.samples_length : NumericalLayerRows.SamplesLengthLaw := by
  unfold NumericalLayerRows.SamplesLengthLaw
  intro site parameter quarter leg coarse clearance originalSource bounds count frame basis sheet forms
    initialAccuracy initial trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage values scalarFactory unitSpan layers
  exact DependentProduct.length_mapToList _ layers _

/-- An actual cached scalar sample reads the same retained Layer and form at its original bounded occurrence.

The complete original inputs and retained certificates are quantified in
this proposition, including their ownership indices and finite bounds.
-/
@[expose] def NumericalLayerRows.SamplesReadbackLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {quarter : UnitCircuitQuarter}
    {leg : Leg site parameter quarter}
    {coarse : Leg.TraceBudget leg}
    {clearance : OwnerBudget.SourceClearance leg}
    {originalSource : Spatial.Source leg.source leg.sourcePrepared}
    (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
    {count : Nat}
    {frame : Curves.Legendre.Paths.Frame parameter}
    {basis : Differential 1}
    {sheet : Fin 2}
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest}
    {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor : Nat}
    {scalarFloor : Nat}
    {pairCurrent : Nat}
    {target : Fraction.Rational}
    {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    {requestStage : Nat}
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan))
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length)
    (channel : Fin 6),
    let saved := samples bounds forms values scalarFactory unitSpan layers
    (saved[edge.val]'((samples_length bounds forms values scalarFactory unitSpan layers).symm ▸ edge.isLt)).get
        channel =
      (CoefficientRequests.LayerBank.layer bounds (DependentProduct.get _ layers edge).1.val
        channel).model.integralSample

/-- An actual cached scalar sample reads the same retained Layer and form at its original bounded occurrence. -/
theorem NumericalLayerRows.samples_get : NumericalLayerRows.SamplesReadbackLaw := by
  unfold NumericalLayerRows.SamplesReadbackLaw
  intro site parameter quarter leg coarse clearance originalSource bounds count frame basis sheet forms
    initialAccuracy initial trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage values scalarFactory unitSpan layers edge channel
  have row := DependentProduct.get_mapToList _ layers (fun _ acquired => DependentVector.ofFn
    (fun channel : Fin 6 =>
      (CoefficientRequests.LayerBank.layer bounds acquired.1.val channel).model.integralSample)) edge
  exact (congrArg (fun value => value.get channel) row).trans (DependentVector.ofFn_get _ channel)

/-- The actual eager scalar sample list has the original finite sum of those same retained Layer samples.

The complete original inputs and retained certificates are quantified in
this proposition, including their ownership indices and finite bounds.
-/
@[expose] def NumericalLayerRows.SampleSumLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {quarter : UnitCircuitQuarter}
    {leg : Leg site parameter quarter}
    {coarse : Leg.TraceBudget leg}
    {clearance : OwnerBudget.SourceClearance leg}
    {originalSource : Spatial.Source leg.source leg.sourcePrepared}
    (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
    {count : Nat}
    {frame : Curves.Legendre.Paths.Frame parameter}
    {basis : Differential 1}
    {sheet : Fin 2}
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest}
    {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor : Nat}
    {scalarFloor : Nat}
    {pairCurrent : Nat}
    {target : Fraction.Rational}
    {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    {requestStage : Nat}
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan))
    (channel : Fin 6),
    FiniteSum.Fin.sumFin (fun edge : Fin
      (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length =>
      (CoefficientRequests.LayerBank.layer bounds (DependentProduct.get _ layers edge).1.val
        channel).model.integralSample) =
      Sum.Basic.gaussianSum ((samples bounds forms values scalarFactory unitSpan layers).map
        (fun row => row.get channel))

/-- The actual eager scalar sample list has the original finite sum of those same retained Layer samples. -/
theorem NumericalLayerRows.sum_samples : NumericalLayerRows.SampleSumLaw := by
  unfold NumericalLayerRows.SampleSumLaw
  intro site parameter quarter leg coarse clearance originalSource bounds count frame basis sheet forms
    initialAccuracy initial trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage values scalarFactory unitSpan layers channel
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let sampled := samples bounds forms values scalarFactory unitSpan layers
  let scalarValues : Fin times.length → Canonical := fun edge =>
    (CoefficientRequests.LayerBank.layer bounds (DependentProduct.get times layers edge).1.val
      channel).model.integralSample
  have sampleCount : sampled.length = times.length :=
    samples_length bounds forms values scalarFactory unitSpan layers
  apply (FiniteSum.Fin.sumFin_congr_size sampleCount.symm scalarValues
    (fun index : Fin sampled.length => (sampled[index.val]'index.isLt).get channel) ?_).trans
    (Sum.Indexed.sumFin_map sampled (fun row => row.get channel))
  intro left right same
  have original := samples_get bounds forms values scalarFactory unitSpan layers left channel
  have lookup := congrArg (fun row => row.get channel)
    (getElem_congr (Eq.refl sampled) same (sampleCount.symm ▸ left.isLt))
  exact original.symm.trans lookup

/-- The actual six-channel source total and materialized scalar-row samples satisfy the original global target.

The exact proposition retains the original Source product and returned
Layer/request banks. Its two sums use those actual ordered values, while
the per-row request pays both factors of the same moving occurrence count.
-/
@[expose] def NumericalSources.TotalsAccuracy
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan)) (channel : Fin 6) : Prop :=
  normSq
    (Sum.Basic.gaussianSum (values.2.2.2.val.2.2.2.2.val.map (fun row =>
        (PathModel.mk (row.get channel)).integralSample)) -
      Sum.Basic.gaussianSum
        ((NumericalLayerRows.samples bounds forms values scalarFactory unitSpan layers).map
          (fun row => row.get channel))) < target

/-- The actual six-channel source total and materialized scalar-row samples satisfy the original global target.

The exact proposition retains the original Source product and returned
Layer/request banks. Its two sums use those actual ordered values, while
the per-row request pays both factors of the same moving occurrence count.
-/
@[expose] def NumericalSources.TotalsAccuracyLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {quarter : UnitCircuitQuarter}
    {leg : Leg site parameter quarter}
    {coarse : Leg.TraceBudget leg}
    {clearance : OwnerBudget.SourceClearance leg}
    {originalSource : Spatial.Source leg.source leg.sourcePrepared}
    (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
    {count : Nat}
    {frame : Curves.Legendre.Paths.Frame parameter}
    {basis : Differential 1}
    {sheet : Fin 2}
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest}
    {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor : Nat}
    {scalarFloor : Nat}
    {pairCurrent : Nat}
    {target : Fraction.Rational}
    {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    {requestStage : Nat}
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan))
    (channel : Fin 6),
    NumericalSources.TotalsAccuracy bounds forms values scalarFactory unitSpan layers channel

/-- The internally paid row bounds imply the actual all-six global source/scalar sum inequality.

Only original finite-sum transport and squared-norm bounds are used. The
same actual source rows and eager scalar sample list retain their original
count and ordinal readings; no final sum estimate is supplied by a caller.
-/
theorem NumericalSources.totals_accurate : NumericalSources.TotalsAccuracyLaw := by
  unfold NumericalSources.TotalsAccuracyLaw
  intro site parameter quarter leg coarse clearance originalSource bounds count frame basis sheet forms
    initialAccuracy initial trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage values scalarFactory unitSpan layers channel
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let rows := values.2.2.2.val.2.2.2.2.val
  let sampled := NumericalLayerRows.samples bounds forms values scalarFactory unitSpan layers
  have rowCount : rows.length = times.length := NumericalSources.row_count bounds forms values
  have sampleCount : sampled.length = times.length :=
    NumericalLayerRows.samples_length bounds forms values scalarFactory unitSpan layers
  let sourceValues : Fin times.length → Canonical := fun edge =>
    (PathModel.mk
      ((rows[edge.val]'(rowCount.symm ▸ edge.isLt)).get channel)).integralSample
  let scalarValues : Fin times.length → Canonical := fun edge =>
    (CoefficientRequests.LayerBank.layer bounds (DependentProduct.get times layers edge).1.val
      channel).model.integralSample
  have bounded (edge : Fin times.length) :
      normSq (sourceValues edge - scalarValues edge) ≤
        Budget.Aggregate.perTerm target times.length := by
    have row := NumericalSources.rows_accurate bounds forms trace bank retained scalar factory caches
      modelFloor scalarFloor pairCurrent target positive sourceAccuracy requestStage values scalarFactory unitSpan
      layers edge channel
    rcases row with ⟨inside, paid⟩
    exact paid.le
  have estimate := Sum.Indexed.normSq_sumFin_le
    (fun edge => sourceValues edge - scalarValues edge)
    (Budget.Aggregate.perTerm target times.length) bounded
  have sourceSum : FiniteSum.Fin.sumFin sourceValues =
      Sum.Basic.gaussianSum (rows.map (fun row =>
        (PathModel.mk (row.get channel)).integralSample)) := by
    apply (FiniteSum.Fin.sumFin_congr_size rowCount.symm sourceValues
      (fun index : Fin rows.length =>
        (PathModel.mk
          ((rows[index.val]'index.isLt).get channel)).integralSample) ?_).trans
      (Sum.Indexed.sumFin_map rows (fun row =>
        (PathModel.mk (row.get channel)).integralSample))
    intro left right same
    cases left with
    | mk first firstBound =>
      cases right with
      | mk last lastBound =>
        cases same
        rfl
  have scalarSum := NumericalLayerRows.sum_samples bounds forms values scalarFactory unitSpan layers channel
  have sumDifference := (FiniteSum.Fin.sumFin_sub sourceValues scalarValues).trans
    (congrArg₂ (fun left right : Canonical => left - right) sourceSum scalarSum)
  have normDifference := congrArg normSq sumDifference
  have countEq : (times.length : Fraction.Rational) ^ 2 *
      Budget.Aggregate.perTerm target times.length =
      (times.length : Fraction.Rational) * ((times.length : Fraction.Rational) *
        Budget.Aggregate.perTerm target times.length) := by
    rewrite [pow_two, Fraction.Field.mul_assoc]
    rfl
  exact (normDifference.symm.trans_le estimate).trans_lt
    (countEq.trans_lt (Budget.Aggregate.count_mul_perTerm_lt positive times.length))

/-- The same retained whole Source integral is the original ordered sum of its actual split row samples.

The complete original inputs and retained certificates are quantified in
this proposition, including their ownership indices and finite bounds.
-/
@[expose] def NumericalSources.SourceSampleLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {quarter : UnitCircuitQuarter}
    {leg : Leg site parameter quarter}
    {coarse : Leg.TraceBudget leg}
    {clearance : OwnerBudget.SourceClearance leg}
    {originalSource : Spatial.Source leg.source leg.sourcePrepared}
    (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
    {count : Nat}
    {frame : Curves.Legendre.Paths.Frame parameter}
    {basis : Differential 1}
    {sheet : Fin 2}
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest}
    {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor : Nat}
    {scalarFloor : Nat}
    {pairCurrent : Nat}
    {target : Fraction.Rational}
    {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    {requestStage : Nat}
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage)
    (channel : Fin 6),
    (PathModel.mk (values.2.2.2.val.2.2.2.1.val.cells channel)).integralSample =
      Sum.Basic.gaussianSum (values.2.2.2.val.2.2.2.2.val.map (fun row =>
        (PathModel.mk (row.get channel)).integralSample))

/-- The same retained whole Source integral is the original ordered sum of its actual split row samples.

The stored flatten certificate and original indexed PathModel law retain
all six cells, global Targets and parent occurrence order. This exact
readback executes neither a source preparation nor another splitter.
-/
theorem NumericalSources.source_sample : NumericalSources.SourceSampleLaw := by
  unfold NumericalSources.SourceSampleLaw
  intro site parameter quarter leg coarse clearance originalSource bounds count frame basis sheet forms
    initialAccuracy initial trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage values channel
  let source := values.2.2.2.val
  let rows := source.2.2.2.2.val
  let groups := rows.map (fun row => row.get channel)
  let blocks := fun index : Fin groups.length => groups[index.val]'index.isLt
  have enumeration := Data.List.OfFn.Basic.ofFn_getElem groups
  have whole := congrArg (fun cells => (PathModel.mk cells).integralSample)
    (source.2.2.2.2.property.2 channel)
  have materialized := congrArg (fun groups => (PathModel.mk groups.flatten).integralSample) enumeration
  have indexed := PathModel.integralSample_flatten_ofFn blocks
  have summed := Sum.Indexed.sumFin_map groups (fun cells => (PathModel.mk cells).integralSample)
  have mapped := Data.List.Map.map_map (fun cells => (PathModel.mk cells).integralSample)
    (fun row => row.get channel) rows
  exact whole.trans (materialized.symm.trans
    (indexed.trans (summed.trans (congrArg Sum.Basic.gaussianSum mapped))))

/-- The actual retained whole Source model and eager scalar-row sample sum meet the requested global target.

Both numerical inputs are the original supplied caches. The complete
predicate preserves their original global source floor and common Taylor
depth, without identifying the geometric programmes or canonical cycles.
-/
@[expose] def NumericalSources.IntegralAccuracy
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan)) (channel : Fin 6) : Prop :=
  normSq ((PathModel.mk (values.2.2.2.val.2.2.2.1.val.cells channel)).integralSample -
    Sum.Basic.gaussianSum ((NumericalLayerRows.samples bounds forms values scalarFactory unitSpan layers).map
      (fun row => row.get channel))) < target

/-- The actual retained whole Source model and eager scalar-row sample sum meet the requested global target.

Both numerical inputs are the original supplied caches. The complete
predicate preserves their original global source floor and common Taylor
depth, without identifying the geometric programmes or canonical cycles.
-/
@[expose] def NumericalSources.IntegralAccuracyLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {quarter : UnitCircuitQuarter}
    {leg : Leg site parameter quarter}
    {coarse : Leg.TraceBudget leg}
    {clearance : OwnerBudget.SourceClearance leg}
    {originalSource : Spatial.Source leg.source leg.sourcePrepared}
    (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
    {count : Nat}
    {frame : Curves.Legendre.Paths.Frame parameter}
    {basis : Differential 1}
    {sheet : Fin 2}
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest}
    {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor : Nat}
    {scalarFloor : Nat}
    {pairCurrent : Nat}
    {target : Fraction.Rational}
    {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    {requestStage : Nat}
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan))
    (channel : Fin 6),
    NumericalSources.IntegralAccuracy bounds forms values scalarFactory unitSpan layers channel

/-- All six whole retained Source integrals satisfy the computed comparison with their actual scalar-row samples. -/
theorem NumericalSources.integral_accurate : NumericalSources.IntegralAccuracyLaw := by
  unfold NumericalSources.IntegralAccuracyLaw
  intro site parameter quarter leg coarse clearance originalSource bounds count frame basis sheet forms
    initialAccuracy initial trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage values scalarFactory unitSpan layers channel
  have bounded := NumericalSources.totals_accurate bounds forms values scalarFactory unitSpan layers channel
  have same := congrArg (fun sample => normSq (sample -
    Sum.Basic.gaussianSum ((NumericalLayerRows.samples bounds forms values scalarFactory unitSpan layers).map
      (fun row => row.get channel)))) (NumericalSources.source_sample bounds forms values channel)
  exact same.trans_lt bounded

/-- The materialized numerical input retains the whole original scalar Piece at the same bounded occurrence.

The complete original inputs and retained certificates are quantified in
this proposition, including their ownership indices and finite bounds.
-/
@[expose] def NumericalSources.InputPieceLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {quarter : UnitCircuitQuarter}
    {leg : Leg site parameter quarter}
    {coarse : Leg.TraceBudget leg}
    {clearance : OwnerBudget.SourceClearance leg}
    {originalSource : Spatial.Source leg.source leg.sourcePrepared}
    (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
    {count : Nat}
    {frame : Curves.Legendre.Paths.Frame parameter}
    {basis : Differential 1}
    {sheet : Fin 2}
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest}
    {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor : Nat}
    {scalarFloor : Nat}
    {pairCurrent : Nat}
    {target : Fraction.Rational}
    {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    {requestStage : Nat}
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage)
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length),
    let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
    (DependentProduct.get times values.1.val edge).1.2 =
      scalar.pieces[edge.val]'((scalar.count.trans
        (DyadicSteps.tail_length trace.budget.fine.selection.stage 0 1).symm).symm ▸ edge.isLt)

/-- The materialized numerical input retains the whole original scalar Piece at the same bounded occurrence. -/
theorem NumericalSources.input_piece : NumericalSources.InputPieceLaw := by
  unfold NumericalSources.InputPieceLaw
  intro site parameter quarter leg coarse clearance originalSource bounds count frame basis sheet forms
    initialAccuracy initial trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage values edge
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  have stored := congrArg (fun inputs : DependentProduct times (fun edge =>
    NumericalInput (count := count) (frame := frame) (basis := basis) (sheet := sheet)
      bounds forms trace bank scalar edge) => (DependentProduct.get times inputs edge).1.2) values.1.property
  have original := numericalInputs_piece bounds forms trace bank retained scalar factory caches edge
  exact stored.trans original

/-- Each actual acquired scalar sample reads its original same-parent factory at the paid global Taylor depth.

The complete original inputs and retained certificates are quantified in
this proposition, including their ownership indices and finite bounds.
-/
@[expose] def NumericalSources.LayerSampleLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {quarter : UnitCircuitQuarter}
    {leg : Leg site parameter quarter}
    {coarse : Leg.TraceBudget leg}
    {clearance : OwnerBudget.SourceClearance leg}
    {originalSource : Spatial.Source leg.source leg.sourcePrepared}
    (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
    {count : Nat}
    {frame : Curves.Legendre.Paths.Frame parameter}
    {basis : Differential 1}
    {sheet : Fin 2}
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest}
    {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor : Nat}
    {scalarFloor : Nat}
    {pairCurrent : Nat}
    {target : Fraction.Rational}
    {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    {requestStage : Nat}
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan))
    (edge : Fin (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1).length)
    (channel : Fin 6),
    let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
    (CoefficientRequests.LayerBank.layer bounds (DependentProduct.get times layers edge).1.val
      channel).model.integralSample =
      (((scalar.pieces[edge.val]'((scalar.count.trans
        (DyadicSteps.tail_length trace.budget.fine.selection.stage 0 1).symm).symm ▸ edge.isLt)).reweight
          (forms.get channel)).layerAt values.2.2.1.val.2).model.integralSample

/-- Each actual acquired scalar sample reads its original same-parent factory at the paid global Taylor depth. -/
theorem NumericalSources.layer_sample : NumericalSources.LayerSampleLaw := by
  unfold NumericalSources.LayerSampleLaw
  intro site parameter quarter leg coarse clearance originalSource bounds count frame basis sheet forms
    initialAccuracy initial trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage values scalarFactory unitSpan layers edge channel
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let input := DependentProduct.get times values.1.val edge
  let acquired := DependentProduct.get times layers edge
  have original := CoefficientRequests.LayerBank.layer_factory bounds acquired.1.val channel
  have sample := congrArg (fun layer : Layer (input.1.2.reweight (forms.get channel))
      (CoefficientRequests.Precisions.depth bounds acquired.1.val.2.1.val values.2.2.1.val.2) =>
    layer.model.integralSample) original
  have depth := NumericalSources.layers_depth bounds forms trace bank retained scalar factory caches
    modelFloor scalarFloor pairCurrent target positive sourceAccuracy requestStage values scalarFactory unitSpan
    layers edge
  have stageSample := congrArg (fun depth =>
    ((input.1.2.reweight (forms.get channel)).layerAt depth).model.integralSample) depth
  have pieceSample := congrArg (fun piece : Piece (forms.get 0) leg.actual scalar.accuracy =>
    ((piece.reweight (forms.get channel)).layerAt values.2.2.1.val.2).model.integralSample)
    (NumericalSources.input_piece bounds forms values edge)
  exact sample.trans (stageSample.trans pieceSample)

/-- The actual scalar-row total is the original whole scalar programme sample at the retained common later stage.

Only complete original Layer factory and partition readbacks occur in the
proof. No fine Layer, Point, root or coefficient request is acquired at
runtime to establish this equality of the supplied numerical payloads.
-/
@[expose] def NumericalSources.ScalarFactory
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan)) (channel : Fin 6) : Prop :=
  Sum.Basic.gaussianSum ((NumericalLayerRows.samples bounds forms values scalarFactory unitSpan layers).map
    (fun row => row.get channel)) =
      ((initial.reweight (forms.get channel)).program.model
        (trace.budget.fine.selection.stage + values.2.2.1.val.2)).integralSample

/-- The actual scalar-row total is the original whole scalar programme sample at the retained common later stage.

Only complete original Layer factory and partition readbacks occur in the
proof. No fine Layer, Point, root or coefficient request is acquired at
runtime to establish this equality of the supplied numerical payloads.
-/
@[expose] def NumericalSources.ScalarFactoryLaw : Prop :=
  ∀
    {site : Fin 2}
    {parameter : Canonical}
    {quarter : UnitCircuitQuarter}
    {leg : Leg site parameter quarter}
    {coarse : Leg.TraceBudget leg}
    {clearance : OwnerBudget.SourceClearance leg}
    {originalSource : Spatial.Source leg.source leg.sourcePrepared}
    (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
    {count : Nat}
    {frame : Curves.Legendre.Paths.Frame parameter}
    {basis : Differential 1}
    {sheet : Fin 2}
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest}
    {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    {trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest)}
    {bank : OwnerMoves.Entries trace.moves}
    {retained : OwnerMoves.Entries.Primitives bounds bank count}
    {scalar : Layer initial trace.budget.fine.selection.stage}
    {factory : bank = OwnerMoves.entries trace.moves}
    {caches : Blocks.ParentCaches (curve := Fibre.frameCurve frame) basis sheet trace.moves.spatialBlocks}
    {modelFloor : Nat}
    {scalarFloor : Nat}
    {pairCurrent : Nat}
    {target : Fraction.Rational}
    {positive : 0 < target}
    {sourceAccuracy : AccuracyRequest}
    {requestStage : Nat}
    (values : NumericalSources bounds forms trace bank retained scalar factory caches modelFloor scalarFloor
  pairCurrent target positive sourceAccuracy requestStage)
    (scalarFactory : scalar = initial.layerAt trace.budget.fine.selection.stage)
    (unitSpan : initial.span.lower = 0 ∧ initial.span.upper = 1)
    (layers : NumericalLayerRows bounds forms values.2.1.val values.2.2.1.val.2
      (values.inputSpans bounds forms scalarFactory unitSpan))
    (channel : Fin 6),
    NumericalSources.ScalarFactory bounds forms values scalarFactory unitSpan layers channel

/-- The original whole scalar partition has the supplied acquired row samples on all six forms. -/
theorem NumericalSources.scalar_factory : NumericalSources.ScalarFactoryLaw := by
  unfold NumericalSources.ScalarFactoryLaw
  intro site parameter quarter leg coarse clearance originalSource bounds count frame basis sheet forms
    initialAccuracy initial trace bank retained scalar factory caches modelFloor scalarFloor pairCurrent
    target positive sourceAccuracy requestStage values scalarFactory unitSpan layers channel
  let coarse := trace.budget.fine.selection.stage
  let depth := values.2.2.1.val.2
  let times := DyadicTrace.tail coarse (0 : Fraction.Rational) 1
  let parents := scalar.reweight (forms.get channel)
  have parentsFactory : parents = (initial.reweight (forms.get channel)).layerAt coarse :=
    (congrArg (fun layer : Layer initial coarse => layer.reweight (forms.get channel)) scalarFactory).trans
      (initial.layerAt_reweight (forms.get channel) coarse)
  let fine := (initial.reweight (forms.get channel)).layerAt (coarse + depth)
  let divided := Layer.partition parents parentsFactory fine rfl
  have whole := Layer.Partition.integralSample_eq_sum divided
  let scalarValues : Fin times.length → Canonical := fun edge =>
    (CoefficientRequests.LayerBank.layer bounds (DependentProduct.get times layers edge).1.val
      channel).model.integralSample
  have count : times.length = parents.pieces.length :=
    (DyadicSteps.tail_length coarse 0 1).trans parents.count.symm
  have grouped : FiniteSum.Fin.sumFin scalarValues = FiniteSum.Fin.sumFin
      (fun index : Fin parents.pieces.length => (PathModel.mk (divided.get index).2.val).integralSample) := by
    apply FiniteSum.Fin.sumFin_congr_size count scalarValues
      (fun index : Fin parents.pieces.length => (PathModel.mk (divided.get index).2.val).integralSample)
    intro left right same
    have rowSample := NumericalSources.layer_sample bounds forms values scalarFactory unitSpan layers left channel
    have originalCount : scalar.pieces.length = times.length :=
      scalar.count.trans (DyadicSteps.tail_length coarse 0 1).symm
    let oldIndex : Fin scalar.pieces.length := ⟨left.val, originalCount.symm ▸ left.isLt⟩
    have reweighted := scalar.reweight_get (forms.get channel) oldIndex
    have rowSame := getElem_congr (Eq.refl parents.pieces) same.symm right.isLt
    have pieceSame := rowSame.trans reweighted
    have localFactory := Layer.Partition.layer_factory parents parentsFactory fine rfl right
      ⟨parents.pieces[right.val]'right.isLt, rfl⟩
    have factorySample := congrArg
      (fun layer : Layer (parents.pieces[right.val]'right.isLt) depth => layer.model.integralSample) localFactory
    have actualCells := congrArg (fun cells => (PathModel.mk cells).integralSample)
      (divided.layer_cells right)
    have sameParent := congrArg (fun piece => (piece.layerAt depth).model.integralSample) pieceSame
    exact rowSample.trans ((actualCells.symm.trans factorySample).trans sameParent).symm
  have programme := congrArg (fun model : PathModel => model.integralSample)
    ((initial.reweight (forms.get channel)).model_eq (coarse + depth))
  exact (NumericalLayerRows.sum_samples bounds forms values scalarFactory unitSpan layers channel).symm.trans
    (grouped.trans (whole.symm.trans programme.symm))

end NumericalTotals

end OwnerTrace

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
