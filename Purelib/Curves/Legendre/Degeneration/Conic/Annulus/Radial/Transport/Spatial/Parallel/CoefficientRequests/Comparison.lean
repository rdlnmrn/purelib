module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests.Layer
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

namespace OwnerMove.PrimitiveTarget

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece Layer)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Approximation
open Purelib.Approximation.Rational.Geometric
open Purelib.Polynomial
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells (Model)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
variable {clearance : OwnerBudget.SourceClearance leg}
variable (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
variable {budget : OwnerBudget leg coarse (some bounds.timeRequest)}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {reading : Reading leg.actual first firstInside} {targetReading : Reading leg.actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Rational.Geometric.Basic.quarterRadius 1 7}
variable {geometry : Geometry reading targetReading leg.regular payment}
variable {oldFirst oldLast : Canonical}
variable {data : SquareRootTrace.EdgeData (Paths.polynomial parameter) oldFirst oldLast
  (coordinate site parameter 2 quarter
    (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1)) first)
  (coordinate site parameter 2 quarter
    (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1)) last)}
variable {paid : (first - last) ^ 2 < (leg.source.residualTimeRequest
  (OwnerBudget.accuracy leg budget.floor (some bounds.timeRequest)).val
  (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)).tolerance}
variable {dataPaid : data.movementBound ≤ Radial.Clearance.rootFloor site parameter ^ 2 / 1024}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter
    (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1)) first))}
variable {sourceAgreement : Gaussian.Equivalence.NamedEquivalent
  (source.certificate source.parameterNonzero).value.name reading.lift.value.name}

variable {original : OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}

section CoefficientRequests

open Purelib.Data.Vector (DependentVector)
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)

variable {span : Interval.Bounds} {scalarInside : FixedRootBoxPath.Inside span.lower}
variable {scalarReading : Reading leg.actual span.lower scalarInside}

namespace CoefficientRequests

open Purelib.Algebra.Quadratic (Pair)

namespace LayerBank

variable {retained : Anchored bounds original count}
variable {preparedSource : CurveSource bounds retained.target} {cache : Source.Cache retained.target.patch}
variable {forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel))}
variable {initialAccuracy : AccuracyRequest} {initial : Piece (forms.get 0) leg.actual initialAccuracy}
variable {modelFloor scalarFloor : Nat} {target : Fraction.Rational} {positive : 0 < target}
variable {sourceAccuracy : AccuracyRequest}
variable {depthFloor : Nat}

section ParentIntegralComparison

open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)

/-- The exact count-paid source and scalar Layer comparison on their retained original caches.

The complete quantified proposition retains the actual scalar LayerBank,
independently floored source row, original pair selections and both stage
payments. The same common Source Request and typed scalar request bank
supply the proof; no source preparation or final comparison is an input.
-/
@[expose] def ParentSources.ScalarAccuracy : Prop :=
  ∀ (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (_points : ParentPoints bounds retained.target retained.sourcePoint frame covered spatialCache)
    {pairCurrent : Nat}
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets path stage)
    (paidPairs : PreparedParents.PairSelections retained.target.patch
      spatialCache.covered pairCurrent
      (Budget.Aggregate.perTerm (target / 4) spatialCache.parents.length))
    (scalar : LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) sourceAccuracy depthFloor)
    {sourceFloor : Nat}
    (spatial : PreparedParents spatialCache.covered sourceFloor targets)
    (_paidStages : ∀ (channel : Fin 6) (index : Fin spatialCache.parents.length),
      (paidPairs.entry channel index).2.stage ≤ scalar.1.2.1.val.selection.stage ∧
        (paidPairs.entry channel index).2.stage ≤
          (spatial.entry index).preparation.attached.source.selection.stage)
    (paid : LayerBank.Requests bounds scalar)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last)
    (channel : Fin 6),
    Norm.Basic.normSq
      ((PathModel.mk
          ((PreparedParents.sources
              spatialCache.covered spatial spatialCache.centeredChain).cells channel)).integralSample -
        (LayerBank.layer bounds scalar channel).model.integralSample) < target

/-- Computed count-paid source cells and the actual retained scalar Layers meet the full requested target.

The same parent/six bank pays the per-parent allowance of a target quarter,
while its original scalar Precision bank pays the other quarter. Both
actual numerical inputs are retained; their common primitive is exactly
the original Source Request cache. No final sample inequality is supplied.
-/
theorem ParentSources.scalar_accurate :
    ParentSources.ScalarAccuracy (depthFloor := depthFloor) (original := original) (count := count) bounds := by
  intro retained preparedSource cache forms initialAccuracy initial modelFloor scalarFloor target positive
    sourceAccuracy frame differential sheet covered spatialCache points pairCurrent baseStart baseFinish path stage
    targets paidPairs scalar sourceFloor spatial paidStages paid span_eq channel
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  have sourceBound := LayerBank.ParentSources.integral_accurate bounds retained cache covered spatialCache points
    scalar.1.2.1.val (Budget.Aggregate.perTerm (target / 4) spatialCache.parents.length)
    paidPairs targets spatial paidStages channel
  have countPaid := Budget.Aggregate.count_mul_perTerm_lt quarterPositive spatialCache.parents.length
  have countEq : (spatialCache.parents.length : Fraction.Rational) ^ 2 *
      Budget.Aggregate.perTerm (target / 4) spatialCache.parents.length =
        (spatialCache.parents.length : Fraction.Rational) * ((spatialCache.parents.length : Fraction.Rational) *
          Budget.Aggregate.perTerm (target / 4) spatialCache.parents.length) := by
    rewrite [pow_two, Fraction.Field.mul_assoc]
    rfl
  have sourcePaid := sourceBound.trans_lt (countEq.trans_lt countPaid)
  have scalarPaid := LayerBank.accurate bounds scalar paid span_eq channel
  have primitiveEq := LayerBank.primitive_value bounds scalar channel
  have scalarSame := congrArg (fun polynomial : Pair.Polynomial.Coefficients =>
    Norm.Basic.normSq (polynomial.eval
      (coordinate site parameter 2 quarter (by decide +kernel) last) - polynomial.eval
      (coordinate site parameter 2 quarter (by decide +kernel) first) -
      (LayerBank.layer bounds scalar channel).model.integralSample)) primitiveEq
  have scalarBound := scalarSame.symm.trans_lt scalarPaid
  exact Norm.Bounds.normSq_sub_lt_of_quarter_bounds sourcePaid scalarBound

/-- The common scalar stage lies after the original requested scalar floor. -/
private theorem scalarFloor_le (bank : LayerBank bounds retained preparedSource cache forms initial
    modelFloor scalarFloor target positive sourceAccuracy) :
    scalarFloor ≤ bank.2.1.val.maximum (fun _ entry => entry.2.taylor.stage) := by
  let actual := bank.2.1.val.get 0
  exact (actual.2.coefficients.2.lower.trans actual.2.taylor.lower).trans
    (bank.2.1.val.get_le_maximum (fun _ entry => entry.2.taylor.stage) 0)

/-- Both actual future samples inherit the paid finite parent/scalar comparison on the same retained caches.

The supplied original search certificate pays the source and six scalar
programme scales before acquisition. The actual parent and Taylor stages
are the comparison indices; original Cauchy laws consume the same supplied
parent bank and original scalar Layers at every later index.
-/
private theorem ParentSources.tails_accurate
    (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (points : ParentPoints bounds retained.target retained.sourcePoint frame covered spatialCache)
    {pairCurrent : Nat} (sourceFloor : Nat)
    (prepared : (index : Nat) → PreparedParents spatialCache.covered sourceFloor
      (CellEndpoints.Targets.build spatialCache.centeredChain.path index))
    (scale : Fraction.Rational)
    (selected : Search.Selection scale (max leftStart rightStart) ((target / 4) / 4))
    (sourceScale : PreparedParents.errorScale spatialCache.parents ≤ scale)
    (scalarScale : ∀ channel : Fin 6, (initial.reweight (forms.get channel)).program.errorScale ≤ scale)
    (result : LayerBank.ParentSources (pairCurrent := pairCurrent) bounds retained preparedSource cache forms initial
      modelFloor (max scalarFloor selected.stage) (((target / 4) / 4) / 4)
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct
          (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) (by decide +kernel))
        (by decide +kernel)) sourceAccuracy spatialCache.covered
      (Budget.Aggregate.perTerm (((target / 4) / 4) / 4) spatialCache.parents.length)
      (CellEndpoints.Targets.build spatialCache.centeredChain.path selected.stage))
    (paid : LayerBank.Requests bounds result.2.1)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last)
    (channel : Fin 6) {leftLater rightLater : Nat} (leftOrder : selected.stage ≤ leftLater)
    (rightOrder : result.2.1.2.1.val.maximum (fun _ entry => entry.2.taylor.stage) ≤ rightLater) :
    Norm.Basic.normSq
      (((PreparedParents.program spatialCache.covered spatialCache.centeredChain
          prepared channel).model leftLater).integralSample -
        ((initial.reweight (forms.get channel)).program.model rightLater).integralSample) < target := by
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  have smallPositive : 0 < (target / 4) / 4 :=
    Fraction.Order.Field.div_pos_direct quarterPositive (by decide +kernel)
  have selectedPaid : Geometric.Basic.quarterRadius scale selected.stage < (target / 4) / 4 :=
    selected.allowance_eq.symm.trans_lt selected.accurate
  have sourceTail := PreparedParents.later_close spatialCache.covered spatialCache.centeredChain
    result.2.2.val (prepared leftLater) channel leftOrder
  have sourcePaid := sourceTail.trans_lt
    ((Geometric.Basic.quarterRadius_scale_mono sourceScale selected.stage).trans_lt selectedPaid)
  have middlePaid := LayerBank.ParentSources.scalar_accurate bounds retained preparedSource cache forms initial
    (max modelFloor result.1.modelFloor) (max scalarFloor selected.stage) ((target / 4) / 4) smallPositive
    sourceAccuracy
    covered spatialCache points (CellEndpoints.Targets.build spatialCache.centeredChain.path selected.stage)
    result.1 result.2.1 result.2.2.val result.2.2.property.2 paid span_eq channel
  have firstTwo := Norm.Bounds.normSq_sub_lt_of_quarter_bounds
    (target := target / 4) sourcePaid middlePaid
  let actual := initial.reweight (forms.get channel)
  let depth := result.2.1.2.1.val.maximum (fun _ entry => entry.2.taylor.stage)
  have layerEq : (LayerBank.layer bounds result.2.1 channel).model.integralSample =
      (actual.program.model depth).integralSample :=
    (congrArg (fun layer => layer.model.integralSample) (LayerBank.layer_factory bounds result.2.1 channel)).trans
      (congrArg (fun model => model.integralSample) (actual.model_eq depth)).symm
  have tail := actual.program.later_close rightOrder
  have tailBasic := (Norm.Basic.normSq_eq_canonical _).trans_le tail
  have swapped := (Norm.Bounds.normSq_sub_symm
    (actual.program.model depth).integralSample (actual.program.model rightLater).integralSample).trans_le tailBasic
  have scalarTail := (congrArg Norm.Basic.normSq
    (congrArg (fun value => value - (actual.program.model rightLater).integralSample) layerEq)).trans_le swapped
  have stagePaid : selected.stage ≤ depth :=
    (Nat.Order.le_max_right scalarFloor selected.stage).trans (scalarFloor_le bounds result.2.1)
  have scalarQuarter := scalarTail.trans
    (Geometric.Basic.quarterRadius_antitone actual.program.errorScale_nonneg stagePaid)
  have scalarSmall := scalarQuarter.trans_lt
    ((Geometric.Basic.quarterRadius_scale_mono (scalarScale channel) selected.stage).trans_lt selectedPaid)
  have small_le : (target / 4) / 4 ≤ target / 4 := by
    apply (Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : Fraction.Rational) < 4)).mpr
    have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct
      (by decide +kernel : (1 : Fraction.Rational) ≤ 4) quarterPositive.le
    exact (Fraction.Field.mul_one_direct _).symm.le.trans scaled
  have final := Norm.Bounds.normSq_sub_lt_of_quarter_bounds
    (target := target) firstTwo (scalarSmall.trans_le small_le)
  have sourceReadback := congrArg PathModel.integralSample
    (PreparedParents.program_model spatialCache.covered spatialCache.centeredChain
      prepared channel leftLater)
  exact (congrArg Norm.Basic.normSq
    (congrArg (fun value => value - (actual.program.model rightLater).integralSample) sourceReadback)).trans_lt final

/-- The exact original vector of six comparisons on its two actual programme-owner families.

This ordinary field-type alias preserves the existing DependentVector,
original Comparison records, requested starts and squared tolerance. It
compacts the inferred type of a stored vector without changing its payload,
its original programmes or any acquisition procedure.
-/
@[expose] def ParentSources.ProgramComparisons
    (left right : Fin 6 → Gaussian.Sequence.ApproximationData)
    (leftStart rightStart : Nat) (target : Fraction.Rational) : Type 1 :=
  DependentVector (fun channel : Fin 6 =>
    Gaussian.Equivalence.Comparison (left channel) (right channel) leftStart rightStart target)

/-- The exact original paid-request and comparison suffix at one retained source stage and scalar bank.

This ordinary dependent field-type alias retains the whole original request
vector, comparison vector and paid-index equations. Naming the suffix keeps
projection inference from expanding the preceding parent/scalar bank; no
runtime tuple, proof, cache or owner is replaced.
-/
@[expose] def ParentSources.ProgramRequest.Tail (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent sourceFloor : Nat)
    (prepared : (index : Nat) → PreparedParents spatialCache.covered sourceFloor
      (CellEndpoints.Targets.build spatialCache.centeredChain.path index))
    (sourceStage : Nat)
    (result : LayerBank.ParentSources (pairCurrent := pairCurrent) bounds retained preparedSource cache forms initial
      modelFloor (max scalarFloor sourceStage) (((target / 4) / 4) / 4)
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct
          (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) (by decide +kernel))
        (by decide +kernel)) sourceAccuracy spatialCache.covered
      (Budget.Aggregate.perTerm (((target / 4) / 4) / 4) spatialCache.parents.length)
      (CellEndpoints.Targets.build spatialCache.centeredChain.path sourceStage)) : Type 2 :=
  LayerBank.Requests bounds result.2.1 ×
      {actual : ParentSources.ProgramComparisons
          (fun channel => (PreparedParents.program spatialCache.covered spatialCache.centeredChain
            prepared channel).approximation)
          (fun channel => (initial.reweight (forms.get channel)).program.approximation)
          leftStart rightStart target //
        ∀ channel : Fin 6, (actual.get channel).leftIndex = sourceStage ∧
          (actual.get channel).rightIndex =
            result.2.1.2.1.val.maximum (fun _ entry => entry.2.taylor.stage)}

/-- One actual six-programme comparison request with its original paid source and scalar banks.

This is the exact existing Sigma/product/vector composition. It retains
one original finite search, Point bank, parent/scalar bank, typed request
vector and six original Comparison records. Both original programme
owners remain in the comparison indices; no replacement programme owner
or new certificate record is introduced.
-/
@[expose] def ParentSources.ProgramRequest (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent sourceFloor : Nat)
    (prepared : (index : Nat) → PreparedParents spatialCache.covered sourceFloor
      (CellEndpoints.Targets.build spatialCache.centeredChain.path index)) : Type 2 :=
  let scale := PreparedParents.errorScale spatialCache.parents +
    Algebra.FiniteSum.Fin.sumFin (fun channel : Fin 6 =>
      (initial.reweight (forms.get channel)).program.errorScale)
  Σ selected : Search.Selection scale (max leftStart rightStart) ((target / 4) / 4),
  Σ _points : ParentPoints bounds retained.target retained.sourcePoint frame covered spatialCache,
  Σ result : LayerBank.ParentSources (pairCurrent := pairCurrent) bounds retained preparedSource cache forms initial
      modelFloor (max scalarFloor selected.stage) (((target / 4) / 4) / 4)
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct
          (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) (by decide +kernel))
        (by decide +kernel)) sourceAccuracy spatialCache.covered
      (Budget.Aggregate.perTerm (((target / 4) / 4) / 4) spatialCache.parents.length)
      (CellEndpoints.Targets.build spatialCache.centeredChain.path selected.stage),
    ParentSources.ProgramRequest.Tail bounds retained preparedSource cache forms initial modelFloor scalarFloor
      leftStart rightStart target positive sourceAccuracy covered spatialCache pairCurrent sourceFloor prepared
      selected.stage result

/-- Compute all six original operational programme comparisons on one actual retained acquisition bank.

The original finite search pays the source scale and all six actual scalar
scales before the shared preparation. Its stage and the same cached Taylor
maximum are retained comparison indices. One structural source preparation,
Point bank and chronological scalar acquisition feed all six records; no
channel callback selects, samples, refines or reacquires those caches.
Every future-sample bound follows from original programme tail laws and
the internally paid finite integral comparison.
-/
def ParentSources.compareProgrammes (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent sourceFloor : Nat)
    (prepared : (index : Nat) → PreparedParents spatialCache.covered sourceFloor
      (CellEndpoints.Targets.build spatialCache.centeredChain.path index))
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last) :
    ParentSources.ProgramRequest bounds retained preparedSource cache forms initial modelFloor scalarFloor
      leftStart rightStart target positive sourceAccuracy covered spatialCache pairCurrent sourceFloor prepared := by
  let scalarScales := fun channel : Fin 6 => (initial.reweight (forms.get channel)).program.errorScale
  have scalarNonnegative (channel : Fin 6) : 0 ≤ scalarScales channel :=
    (initial.reweight (forms.get channel)).program.errorScale_nonneg
  let scalarTotal := Algebra.FiniteSum.Fin.sumFin scalarScales
  have totalNonnegative : 0 ≤ scalarTotal :=
    Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative scalarScales scalarNonnegative
  let originalScale := PreparedParents.errorScale spatialCache.parents
  have originalNonnegative : 0 ≤ originalScale :=
    PreparedParents.errorScale_nonnegative spatialCache.parents
  let scale := originalScale + scalarTotal
  have scaleNonnegative : 0 ≤ scale := by
    have added : (0 : Fraction.Rational) + 0 ≤ scale :=
      Arithmetic.add_le_add_direct
        (first := 0) (second := originalScale) (third := 0) (fourth := scalarTotal)
        originalNonnegative totalNonnegative
    exact (Fraction.Field.zero_add (0 : Fraction.Rational)).symm.le.trans added
  have sourceScale : originalScale ≤ scale := by
    calc
      originalScale = originalScale + 0 := by ring0
      _ ≤ _ := Arithmetic.add_le_add_direct
        (Fraction.Order.Basic.le_refl _) totalNonnegative
  have scalarScale (channel : Fin 6) : scalarScales channel ≤ scale := by
    apply (Algebra.FiniteSum.Rational.Order.entry_le_sumFin scalarScales scalarNonnegative channel).trans
    calc
      scalarTotal = 0 + scalarTotal := (Fraction.Field.zero_add _).symm
      _ ≤ _ := Arithmetic.add_le_add_direct originalNonnegative (Fraction.Order.Basic.le_refl _)
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  have smallPositive : 0 < (target / 4) / 4 :=
    Fraction.Order.Field.div_pos_direct quarterPositive (by decide +kernel)
  have scalarPositive : 0 < ((target / 4) / 4) / 4 :=
    Fraction.Order.Field.div_pos_direct smallPositive (by decide +kernel)
  let selected := Search.Selection.build scale scaleNonnegative (max leftStart rightStart)
    ((target / 4) / 4) smallPositive
  let actualFloor := max scalarFloor selected.stage
  let targets := CellEndpoints.Targets.build spatialCache.centeredChain.path selected.stage
  let pairTarget := Budget.Aggregate.perTerm (((target / 4) / 4) / 4) spatialCache.parents.length
  have pairPositive : 0 < pairTarget :=
    Budget.Aggregate.perTerm_positive scalarPositive spatialCache.parents.length
  let result := layerBankWithParents (pairCurrent := pairCurrent) bounds retained preparedSource cache forms initial
    span_eq proper modelFloor actualFloor (((target / 4) / 4) / 4) scalarPositive sourceAccuracy
    spatialCache.covered pairTarget pairPositive targets
  let points := parentPoints bounds retained.target retained.sourcePoint frame covered spatialCache
    ⟨retained.reference, retained.reference_eq⟩
  let paid := LayerBank.requests bounds result.2.1
  let depth := result.2.1.2.1.val.maximum (fun _ entry => entry.2.taylor.stage)
  have stagePaid : selected.stage ≤ depth :=
    (Nat.Order.le_max_right scalarFloor selected.stage).trans (scalarFloor_le bounds result.2.1)
  have firstPaid : leftStart ≤ selected.stage := (Nat.Order.le_max_left leftStart rightStart).trans selected.lower
  have lastPaid : rightStart ≤ depth :=
    ((Nat.Order.le_max_right leftStart rightStart).trans selected.lower).trans stagePaid
  let entry (channel : Fin 6) : Gaussian.Equivalence.Comparison
      (PreparedParents.program spatialCache.covered spatialCache.centeredChain
        prepared channel).approximation
      (initial.reweight (forms.get channel)).program.approximation leftStart rightStart target :=
      { leftIndex := selected.stage
        rightIndex := depth
        left_ge := firstPaid
        right_ge := lastPaid
        close := by
          intro leftLater rightLater leftOrder rightOrder
          exact ParentSources.tails_accurate bounds retained preparedSource cache forms initial
            modelFloor scalarFloor leftStart rightStart target positive sourceAccuracy covered spatialCache points
            sourceFloor prepared scale selected sourceScale scalarScale result paid span_eq channel
            leftOrder rightOrder }
  let comparisons := DependentVector.ofFn entry
  have indices (channel : Fin 6) : (comparisons.get channel).leftIndex = selected.stage ∧
      (comparisons.get channel).rightIndex = depth := by
    have same : comparisons.get channel = entry channel := DependentVector.ofFn_get entry channel
    exact ⟨congrArg (fun actual => actual.leftIndex) same, congrArg (fun actual => actual.rightIndex) same⟩
  exact ⟨selected, points, result, paid, ⟨comparisons, indices⟩⟩

section NamedProgrammes

open Gaussian.Equivalence (Comparison Equivalent)
open Gaussian.Name
open Gaussian.Sequence (ApproximationData)

/-- Compose one saved raw comparison with its two actual canonical sampler comparisons.

The original Comparison composition preserves both outer paid starts and
uses the same retained raw comparison. The returned tuple retains both
actual sampler receipts; no raw relation is requested again.
-/
private def namedRow (left right : ApproximationData)
    (rawLeftStart rawRightStart leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (raw : Comparison left right rawLeftStart rawRightStart ((target / 4) / 4)) :
    (Comparison (Sampling.approximation left.toNamed) left
        leftStart rawLeftStart ((target / 4) / 4) ×
      Comparison (Sampling.approximation right.toNamed) right
        rightStart rawRightStart (target / 4)) ×
    Comparison (Sampling.approximation left.toNamed)
      (Sampling.approximation right.toNamed) leftStart rightStart target := by
  have quarterPositive : 0 < target / 4 := Data.Rat.Bounds.Quarter.quarter_pos positive
  have smallPositive : 0 < (target / 4) / 4 := Data.Rat.Bounds.Quarter.quarter_pos quarterPositive
  let leftSampler := (Equivalent.toNamed_sampling left).compare
    leftStart rawLeftStart ((target / 4) / 4) smallPositive
  let rightSampler := (Equivalent.toNamed_sampling right).compare
    rightStart rawRightStart (target / 4) quarterPositive
  have firstTarget : 2 * ((target / 4) / 4 + (target / 4) / 4) = target / 4 := by
    rewrite [Data.Rat.Bounds.Quarter.two_quarters, Fraction.Field.mul_comm]
    exact Data.Rat.Bounds.Quarter.half_mul_two (target / 4)
  have finalTarget : 2 * (2 * ((target / 4) / 4 + (target / 4) / 4) + target / 4) = target := by
    rewrite [firstTarget, Data.Rat.Bounds.Quarter.two_quarters, Fraction.Field.mul_comm]
    exact Data.Rat.Bounds.Quarter.half_mul_two target
  let compared := ((leftSampler.trans raw).trans rightSampler.symm).weaken target finalTarget.le
  exact ⟨⟨leftSampler, rightSampler⟩, compared⟩

/-- Assemble the six original sampler rows on supplied original approximation and comparison vectors.

This bounded constructor forwards each whole supplied raw comparison to the
same generic sampler composition. Its callback does not build any source,
Point, preparation, Layer or raw comparison request.
-/
def namedRows (left right : Fin 6 → ApproximationData)
    (rawLeftStart rawRightStart leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (raw : DependentVector (fun channel : Fin 6 => Comparison (left channel) (right channel)
      rawLeftStart rawRightStart ((target / 4) / 4))) :
    DependentVector (fun channel : Fin 6 =>
      (Comparison (Sampling.approximation (left channel).toNamed) (left channel)
          leftStart rawLeftStart ((target / 4) / 4) ×
        Comparison (Sampling.approximation (right channel).toNamed) (right channel)
          rightStart rawRightStart (target / 4)) ×
      Comparison (Sampling.approximation (left channel).toNamed) (Sampling.approximation (right channel).toNamed)
        leftStart rightStart target) :=
  DependentVector.ofFn (fun channel => namedRow (left channel) (right channel)
    rawLeftStart rawRightStart leftStart rightStart target positive (raw.get channel))

/-- Read the entire saved original comparison vector through its exact original tuple projection.

The selected stage, Point bank, parent/scalar bank and paid requests remain
in the unchanged supplied tuple. The returned vector is the same stored
value; no selection or preparation procedure is executed.
-/
private def ParentSources.ProgramRequest.comparisons (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent sourceFloor : Nat)
    (prepared : (index : Nat) → PreparedParents spatialCache.covered sourceFloor
      (CellEndpoints.Targets.build spatialCache.centeredChain.path index))
    (request : ParentSources.ProgramRequest bounds retained preparedSource cache forms initial
      modelFloor scalarFloor leftStart rightStart target positive sourceAccuracy
      covered spatialCache pairCurrent sourceFloor prepared) :
    ParentSources.ProgramComparisons
      (fun channel => (PreparedParents.program spatialCache.covered spatialCache.centeredChain
        prepared channel).approximation)
      (fun channel => (initial.reweight (forms.get channel)).program.approximation)
      leftStart rightStart target :=
  request.2.2.2.2.val

/-- One all-six named comparison request retains its single raw bank and both sampler receipts per channel.

This exact Sigma/vector view keeps the actual original programmes, source
and scalar banks, ordered Point/request caches and canonical sampler
comparisons. Raw and named starts are separate retained indices. No new
comparison family or replacement programme owner is introduced.
-/
@[expose] def ParentSources.NamedProgramRequest (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor rawLeftStart rawRightStart leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent sourceFloor : Nat)
    (prepared : (index : Nat) → PreparedParents spatialCache.covered sourceFloor
      (CellEndpoints.Targets.build spatialCache.centeredChain.path index)) : Type 2 :=
  Σ _raw : ParentSources.ProgramRequest bounds retained preparedSource cache forms initial
      modelFloor scalarFloor rawLeftStart rawRightStart ((target / 4) / 4)
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) (by decide +kernel)) sourceAccuracy
      covered spatialCache pairCurrent sourceFloor prepared,
    DependentVector (fun channel : Fin 6 =>
      (Comparison
          (Sampling.approximation
            (PreparedParents.program spatialCache.covered spatialCache.centeredChain
          prepared channel).approximation.toNamed)
          (PreparedParents.program spatialCache.covered spatialCache.centeredChain
          prepared channel).approximation
          leftStart rawLeftStart ((target / 4) / 4) ×
        Comparison
          (Sampling.approximation (initial.reweight (forms.get channel)).program.approximation.toNamed)
          (initial.reweight (forms.get channel)).program.approximation
          rightStart rawRightStart (target / 4)) ×
      Comparison
        (Sampling.approximation
            (PreparedParents.program spatialCache.covered spatialCache.centeredChain
          prepared channel).approximation.toNamed)
        (Sampling.approximation (initial.reweight (forms.get channel)).program.approximation.toNamed)
        leftStart rightStart target)

/-- Pay all six original named programme comparisons from one retained raw acquisition bank.

The common raw request is computed once before the eager ordered sampler
rows. Each row consumes its saved original comparison and retains both
actual canonical sampler receipts. Original composition pays the same
requested tolerance at both independent named starts without assuming
emitted-index coverage or asking for another raw comparison.
-/
def ParentSources.compareNamedProgrammes (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor rawLeftStart rawRightStart leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent sourceFloor : Nat)
    (prepared : (index : Nat) → PreparedParents spatialCache.covered sourceFloor
      (CellEndpoints.Targets.build spatialCache.centeredChain.path index))
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last) :
    ParentSources.NamedProgramRequest bounds retained preparedSource cache forms initial modelFloor scalarFloor
    rawLeftStart rawRightStart leftStart rightStart target positive sourceAccuracy
    covered spatialCache pairCurrent sourceFloor prepared := by
  have quarterPositive : 0 < target / 4 := Data.Rat.Bounds.Quarter.quarter_pos positive
  have smallPositive : 0 < (target / 4) / 4 := Data.Rat.Bounds.Quarter.quarter_pos quarterPositive
  let sourceProgram : Fin 6 → ApproximationData := fun channel =>
    (PreparedParents.program spatialCache.covered spatialCache.centeredChain
      prepared channel).approximation
  let scalarProgram : Fin 6 → ApproximationData := fun channel =>
    (initial.reweight (forms.get channel)).program.approximation
  let raw : ParentSources.ProgramRequest bounds retained preparedSource cache forms initial
      modelFloor scalarFloor rawLeftStart rawRightStart ((target / 4) / 4) smallPositive sourceAccuracy
      covered spatialCache pairCurrent sourceFloor prepared :=
    ParentSources.compareProgrammes bounds retained preparedSource cache forms initial
      modelFloor scalarFloor rawLeftStart rawRightStart ((target / 4) / 4) smallPositive sourceAccuracy
      covered spatialCache pairCurrent sourceFloor prepared span_eq proper
  let comparisons : DependentVector (fun channel : Fin 6 => Comparison (sourceProgram channel) (scalarProgram channel)
      rawLeftStart rawRightStart ((target / 4) / 4)) :=
    ParentSources.ProgramRequest.comparisons bounds retained preparedSource cache forms initial
      modelFloor scalarFloor rawLeftStart rawRightStart ((target / 4) / 4) smallPositive sourceAccuracy
      covered spatialCache pairCurrent sourceFloor prepared raw
  let rows := namedRows sourceProgram scalarProgram rawLeftStart rawRightStart leftStart rightStart
    target positive comparisons
  exact ⟨raw, rows⟩

/-- The original emitted source and scalar programme names are operationally equivalent on each actual form.

Every positive-accuracy request delegates one shared six-channel named
request, retains its original raw/model bank and canonical sampler receipts,
and reads the chosen stored comparison. Both original programme output
names remain the indices. Independently invoking another request does new
request work; bounded lookup within a retained NamedProgramRequest does not.
-/
def ParentSources.outputEquivalent (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor rawLeftStart rawRightStart : Nat)
    (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent sourceFloor : Nat)
    (prepared : (index : Nat) → PreparedParents spatialCache.covered sourceFloor
      (CellEndpoints.Targets.build spatialCache.centeredChain.path index))
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (channel : Fin 6) : Gaussian.Equivalence.NamedEquivalent
      (PreparedParents.program spatialCache.covered spatialCache.centeredChain
        prepared channel).output.name
      (initial.reweight (forms.get channel)).program.output.name where
  compare leftStart rightStart target positive :=
    let request := ParentSources.compareNamedProgrammes bounds retained preparedSource cache forms initial
      modelFloor scalarFloor rawLeftStart rawRightStart leftStart rightStart target positive sourceAccuracy
      covered spatialCache pairCurrent sourceFloor prepared span_eq proper
    (request.2.get channel).2

end NamedProgrammes

end ParentIntegralComparison

end LayerBank

end CoefficientRequests

end CoefficientRequests

end OwnerMove.PrimitiveTarget

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
