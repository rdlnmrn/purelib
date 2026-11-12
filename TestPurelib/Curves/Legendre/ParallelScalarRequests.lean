module

import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests
import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests.Preparation
import all Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests.Layer
import Purelib.Curves.Legendre.Periods.Jets.Source
import Purelib.Curves.Legendre.Periods.Jets.Specification.Table
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds
import Purelib.Data.Vector.Dependent
import Purelib.Data.List.DependentProduct
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.OwnerTrace
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer
import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Power
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Integration.Program.Gaussian.Name

/-! # Paid scalar layers from original scaled odd-power primitives

These clients retain the original primitive, finite precision and cell
request bank for arbitrary scaled numerators and denominator pairs. The
whole former zero-pair factories and supplied-cache branches are checked
separately from the actual paid layer bound. No supplied-Blocks programme
or all-six integral equivalence is claimed.

The import-all Preparation and Layer owners supply the original unexposed
producers reduced by the whole former-factory comparisons.
-/

namespace TestPurelib.Curves.Legendre.ParallelScalarRequests

open Purelib.Data.Rat.Bounds.Quarter (quarter_pos)

open Purelib.Data
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds renaming Data → WaistBounds
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell (PreparedParents)

open Purelib
open Purelib.Curves.Legendre
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus
open Radial
open Radial.Transport
open Radial.Transport.Spatial
open Purelib.Data.Gaussian
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Polynomial.Dense.Basic
open Purelib.Polynomial.Dense.Gaussian.Bounds
open Purelib.Curves.Legendre.Periods.Jets
open Purelib.Data.Vector (DependentVector)
open Purelib.Data.List
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
open OwnerMove.PrimitiveTarget
open OwnerMove (PrimitiveTarget)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Approximation
open Purelib.Approximation.Rational
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

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Algebra.Quadratic (Pair)

variable {index : Nat} {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
variable {cellRadicand : Pair.Polynomial.Coefficients}
variable {cellDifferential : OddPowerDifferential cellRadicand}
variable {cellData : WaistBounds site parameter cellDifferential}
variable {initialAccuracy : AccuracyRequest}

/-- The complete omitted-cache zero-pair construction is the original inverse/power/ofModel result. -/
example (cached : PrimitiveTarget bounds original count) (index : Nat) (numerator : Pair.Polynomial.Coefficients) :
    scalarModels bounds cached index numerator =
      (let inverse := cached.patch.base.refine index
       let powers := OddPowers.build inverse.value
       let common := PrimitiveModel.ofModel cached.patch index numerator inverse rfl
       ⟨⟨inverse, rfl⟩, ⟨powers, rfl⟩, ⟨common, rfl⟩⟩) :=
  scalarModels_default bounds cached index numerator

/-- The full original zero-pair precision factory, including all five retained caches, remains unchanged. -/
example (cached : PrimitiveTarget bounds original count)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    ScalarModels.precision bounds cached initial modelFloor scalarFloor target positive =
      (let error := ScalarModels.coefficientTarget initial target
       let errorPositive := Budget.Weighted.allowance_positive
         (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
         (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
           (Fraction.Order.Arithmetic.sq_nonneg_direct initial.span.width))
       let selected := coefficientSelections bounds cached cellData initialAccuracy
         modelFloor scalarFloor error errorPositive
       let models := scalarModels bounds cached selected.1.stage cellDifferential.numerator
       let horner := Box.denseHornerNormBounds models.common.coefficient cached.patch.box
       let scale := ScalarModels.taylorScale bounds models initial horner
       let taylor := Search.Selection.build scale
         (ScalarModels.taylorScale_nonnegative bounds models initial horner rfl)
         selected.2.stage (target / 2) (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
       ⟨⟨selected, rfl⟩, models, ⟨horner, rfl⟩, ⟨scale, rfl⟩, taylor⟩) :=
  ScalarModels.precision_default bounds cached initial modelFloor scalarFloor target positive

/-- Supplying the complete original factors and primitive retains their whole original values for any odd index. -/
example (cached : PrimitiveTarget bounds original count)
    (factors : ScalarModels.Factors bounds cached index)
    (common : PrimitiveModel cached.patch index numerator pairCount) :
    let actual := scalarModels bounds cached index numerator pairCount (some common) (some factors)
    actual.inverse = factors.1.val ∧ HEq actual.powers factors.2.val ∧ actual.common = common := by
  rewrite [scalarModels_ofFactors]
  exact ⟨rfl, HEq.rfl, rfl⟩

/-- Acquire the original ordered scalar requests and their internally paid primitive-boundary estimate.

The scale equation is the actual displayed numerator's evaluation, and the
pair identity is the original form's denominator index. Both endpoint and
interior branches derive their domains and signed links from the retained
original parent. No residual or final integral inequality is a premise.
-/
def paidScalarLayer (retained : Anchored bounds original count)
    (prepared : CurveSource bounds retained.target)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (supplied : Option (ScalarModels.Precision.Retained bounds retained.target initial modelFloor scalarFloor
      target positive numerator pairCount))
    (precision : ScalarModels.Precision bounds retained.target initial modelFloor scalarFloor target positive
      numerator pairCount supplied)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (layer : Layer initial precision.taylor.stage)
    (spans : layer.pieces.map (fun piece => piece.span) = Interval.Bisection.parts precision.taylor.stage initial.span)
    (pairs : cellDifferential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = cellDifferential.scale * cellDifferential.numerator.eval location) :
    {_actual : ScalarModels.LayerRequests bounds retained prepared precision.models layer
        (ScalarModels.coefficientTarget initial target) //
      Norm.Basic.normSq (precision.models.common.primitive.value.eval
          (coordinate site parameter 2 quarter (by decide +kernel) last) -
        precision.models.common.primitive.value.eval
          (coordinate site parameter 2 quarter (by decide +kernel) first) -
        layer.model.integralSample) < target} := by
  let actual := precision.requests bounds retained prepared ⟨precision.taylor.stage, Nat.le_refl _⟩
    span_eq proper layer spans pairs scale
  exact ⟨actual, precision.accurate bounds retained ⟨precision.taylor.stage, Nat.le_refl _⟩
    span_eq layer spans actual⟩

/-- Use a real retained six-bank channel to select precision and pay the same original scalar layer.

The actual Source Request supplies its final stage, inverse, powers and
primitive, and the stored channel supplies its completed Selections. The
actual scaled numerator and denominator pair proofs come from the selected
original Table form. This compares one actual scalar layer to its common
primitive boundary; it makes no supplied-Blocks programme claim.
-/
def paidChannelLayer (retained : Anchored bounds original count)
    (prepared : CurveSource bounds retained.target)
    {span : Interval.Bounds} {scalarInside : FixedRootBoxPath.Inside span.lower}
    (pointReading : Reading leg.actual span.lower scalarInside)
    (sample : ContinuedNeighborhood.Point retained.target.patch
      (coordinate site parameter 2 quarter
        (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1)) span.lower))
    (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (channel : Fin 6) (initial : Piece (forms.get channel) leg.actual initialAccuracy)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (bank : CoefficientRequests bounds retained.target pointReading sample cache forms initialAccuracy modelFloor
      scalarFloor (ScalarModels.coefficientTarget initial target)
        (ScalarModels.coefficientTarget_positive initial positive) sourceAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last) :
    let selected := CoefficientRequests.precision bounds retained.target cache forms
      initialAccuracy modelFloor scalarFloor channel initial target positive sourceAccuracy
      (CoefficientRequests.preparation bounds retained.target pointReading sample cache forms initialAccuracy
        modelFloor scalarFloor (ScalarModels.coefficientTarget initial target)
          (ScalarModels.coefficientTarget_positive initial positive) sourceAccuracy bank)
    (layer : Layer initial selected.2.taylor.stage) →
    (layer.pieces.map (fun piece => piece.span) = Interval.Bisection.parts selected.2.taylor.stage initial.span) →
    {_actual : ScalarModels.LayerRequests bounds retained prepared selected.2.models layer
        (ScalarModels.coefficientTarget initial target) //
      Norm.Basic.normSq (selected.2.models.common.primitive.value.eval
          (coordinate site parameter 2 quarter (by decide +kernel) last) -
        selected.2.models.common.primitive.value.eval
          (coordinate site parameter 2 quarter (by decide +kernel) first) -
        layer.model.integralSample) < target} := by
  intro selected layer spans
  exact paidScalarLayer bounds retained prepared initial modelFloor scalarFloor target positive
    (some selected.1) selected.2 span_eq proper layer spans rfl (fun location => by
      rewrite [DensePolynomial.eval_scale]
      rfl)

/-- Select one common depth from all six retained original Taylor requests before any scalar Point acquisition.

The returned cache retains the actual six Precision objects and the exact
once-computed maximum. Each bound reads its same original bounded entry;
no selection, inverse model or primitive is rebuilt by a stage lookup.
-/
def commonScalarDepth (cached : PrimitiveTarget bounds original count)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : CoefficientRequests.Preparation bounds cached cache forms initialAccuracy modelFloor scalarFloor
      (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
      sourceAccuracy) :
    let expected := CoefficientRequests.precisions bounds cached cache forms initial modelFloor scalarFloor
      target positive sourceAccuracy prepared
    Σ entries : {actual : _ // actual = expected},
      {depth : Nat // depth = entries.val.maximum (fun _ entry => entry.2.taylor.stage) ∧
        ∀ channel, (entries.val.get channel).2.taylor.stage ≤ depth} := by
  let entries := CoefficientRequests.precisions bounds cached cache forms initial modelFloor scalarFloor
    target positive sourceAccuracy prepared
  let depth := entries.maximum (fun _ entry => entry.2.taylor.stage)
  exact ⟨⟨entries, rfl⟩, ⟨depth, rfl, fun channel =>
    entries.get_le_maximum (fun _ entry => entry.2.taylor.stage) channel⟩⟩

/-- Acquire and retain the actual six scalar numerical samples from one common-stage chronological coefficient bank.

The complete original bank is returned with these samples. Each channel
reads only its retained Layer.model; no numerical preparation, Point or
root request is placed inside the six sample-producing callbacks.
-/
def sixLayerSamples (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    CoefficientRequests.LayerBank bounds retained preparedSource cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy ×
      DependentVector (fun _channel : Fin 6 => Canonical) :=
  let bank := CoefficientRequests.layerBank bounds retained preparedSource cache forms initial span_eq proper
    modelFloor scalarFloor target positive sourceAccuracy
  let layers := bank.2.2.2.2.val
  let firstSample := (layers.get 0).model.integralSample
  let samples := DependentVector.ofFn (Fin.cases firstSample
    (fun channel => (layers.get channel.succ).model.integralSample))
  ⟨bank, samples⟩

/-- Every retained bounded row and channel has its actual paid coefficient residual at the requested common target.

The payment is read from the actual constructed request on the same stored
Point, Model, primitive and source ordinal; it is not a premise or an
inequality concerning a separately sampled coefficient.
-/
example (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (bank : CoefficientRequests.LayerBank bounds retained preparedSource cache forms initial
      modelFloor scalarFloor target positive sourceAccuracy)
    (ordinal : Fin bank.2.2.1.val.pieces.length) (channel : Fin 6) :
    let row := DependentProduct.get bank.2.2.1.val.pieces bank.2.2.2.1 ordinal
    (row.2.2.2.get channel).1.val.primitiveResidual (bank.1.2.2.val.get channel).coefficient <
      ScalarModels.coefficientTarget initial target := by
  exact ((DependentProduct.get bank.2.2.1.val.pieces bank.2.2.2.1 ordinal).2.2.2.get channel).2.property.1

/-- All six actual requests forward the same complete root, shared reading and whole numerical Comparison.

This is a whole-cache check on arbitrary retained scalar occurrences.
It preserves the original Point and typed coefficient request, rather than
replacing cache reuse with equality of approximate scalar samples.
-/
example (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (bank : CoefficientRequests.LayerBank bounds retained preparedSource cache forms initial
      modelFloor scalarFloor target positive sourceAccuracy)
    (ordinal : Fin bank.2.2.1.val.pieces.length) (channel : Fin 6) :
    let row := DependentProduct.get bank.2.2.1.val.pieces bank.2.2.2.1 ordinal
    let request := (row.2.2.2.get channel).2.val
    request.1 = row.2.2.1.1 ∧ HEq request.2.1 row.2.2.1.2.1 ∧
      HEq request.2.2.val row.2.2.1.2.2.val := by
  exact ((DependentProduct.get bank.2.2.1.val.pieces bank.2.2.2.1 ordinal).2.2.2.get channel).2.property.2

/-- The actual retained initial Piece has the same complete cache when viewed at its identical original budget.

This whole equality supplies the zero-channel initial-index transport.
It retains its original source, observation and scalar coefficient values;
no canonical Model.build or replacement source is used.
-/
example (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy) :
    initial.reweight (forms.get 0) = initial := initial.reweight_self

/-- Construct all six actual typed request banks and their own paid primitive-boundary estimates.

One retained common-stage bank supplies every actual Point, root request,
Model and whole Comparison. All six original request banks are materialized
once before any channel getter, and the original Precision estimates use
those exact banks and returned Layers. No desired residual, domain-success
or integral bound is supplied by the caller.
-/
def cachedSixRequests (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) :
    Σ bank : CoefficientRequests.LayerBank bounds retained preparedSource cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy,
      {_paid : CoefficientRequests.LayerBank.Requests bounds bank //
        ∀ channel : Fin 6,
          Norm.Basic.normSq ((bank.2.1.val.get channel).2.models.common.primitive.value.eval
              (coordinate site parameter 2 quarter (by decide +kernel) last) -
            (bank.2.1.val.get channel).2.models.common.primitive.value.eval
              (coordinate site parameter 2 quarter (by decide +kernel) first) -
            (CoefficientRequests.LayerBank.layer bounds bank channel).model.integralSample) < target} := by
  let bank := CoefficientRequests.layerBank bounds retained preparedSource cache forms initial span_eq proper
    modelFloor scalarFloor target positive sourceAccuracy
  let paid := CoefficientRequests.LayerBank.requests bounds bank
  exact ⟨bank, ⟨paid, fun channel => CoefficientRequests.LayerBank.accurate bounds bank paid span_eq channel⟩⟩

section TracePrimitivePieces

open Purelib.Integration.Path.Dyadic

/-- Materialize actual per-occurrence six-form Selections from the supplied scalar and primitive caches.

One ordinal view retains the whole original Piece and primitive at each
trace edge. The structural map computes each original six-entry selection
bank once, using its supplied whole primitive and the actual common scalar
accuracy. No source/model/root acquisition depends on this selection bank.
Interval correspondence and whole-Blocks programme comparison are separate.
-/
def traceSelections
    {originalSource : Source leg.source leg.sourcePrepared}
    (trace : OwnerTrace leg coarse originalSource (some bounds.timeRequest))
    (bank : OwnerMoves.Entries trace.moves)
    (retained : OwnerMoves.Entries.Primitives bounds bank count)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (scalar : Layer initial trace.budget.fine.selection.stage)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    Σ paired : OwnerTrace.PrimitivePieces bounds trace bank retained scalar,
      DependentProduct (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1)
        (fun edge =>
          let actual := DependentProduct.get
            (DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1) paired.val edge
          {selected : CoefficientSelections bounds actual.1.target forms scalar.accuracy
              modelFloor scalarFloor target //
            selected = DependentVector.ofFn (fun channel => coefficientSelections bounds actual.1.target
              (forms.get channel) scalar.accuracy modelFloor scalarFloor target positive
              (Specification.Table.forms parameter channel).denominatorPairs)}) := by
  let paired := trace.primitivePieces bounds bank retained scalar
  let times := DyadicTrace.tail trace.budget.fine.selection.stage (0 : Fraction.Rational) 1
  let selected := DependentProduct.map times paired.val
    (fun _ actual => {selected : CoefficientSelections bounds actual.1.target forms scalar.accuracy
        modelFloor scalarFloor target //
      selected = DependentVector.ofFn (fun channel => coefficientSelections bounds actual.1.target
        (forms.get channel) scalar.accuracy modelFloor scalarFloor target positive
        (Specification.Table.forms parameter channel).denominatorPairs)})
    (fun _ actual => ⟨DependentVector.ofFn (fun channel => coefficientSelections bounds actual.1.target
      (forms.get channel) scalar.accuracy modelFloor scalarFloor target positive
      (Specification.Table.forms parameter channel).denominatorPairs), rfl⟩)
  exact ⟨paired, selected⟩

end TracePrimitivePieces

section LaterTaylor

open Purelib.Curves.Legendre.Periods

/-- One actual later-floor acquisition forwards both complete supplied caches and pays all six returned Layers.

The original preparation and Precision vector are arguments, so no model,
selection or Taylor factory is rerun here. The computed depth pays the
requested floor and every stored Taylor stage before the one original
chronological Point/root/Comparison traversal.
-/
def cachedLaterLayers (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Jets.Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : CoefficientRequests.Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor (ScalarModels.coefficientTarget initial target)
      (ScalarModels.coefficientTarget_positive initial positive) sourceAccuracy)
    (selected : {actual : CoefficientRequests.Precisions bounds retained.target forms initial
        modelFloor scalarFloor target positive //
      actual = CoefficientRequests.precisions bounds retained.target cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy prepared})
    (depthFloor : Nat) :
    Σ bank : CoefficientRequests.LayerBank bounds retained preparedSource cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy depthFloor,
    {_requests : CoefficientRequests.LayerBank.Requests bounds bank //
      bank.1 = prepared ∧ HEq bank.2.1 selected ∧
        depthFloor ≤ CoefficientRequests.Precisions.depth bounds bank.2.1.val depthFloor ∧
        ∀ channel : Fin 6,
          Norm.Basic.normSq ((bank.2.1.val.get channel).2.models.common.primitive.value.eval
              (coordinate site parameter 2 quarter (by decide +kernel) last) -
            (bank.2.1.val.get channel).2.models.common.primitive.value.eval
              (coordinate site parameter 2 quarter (by decide +kernel) first) -
            (CoefficientRequests.LayerBank.layer bounds bank channel).model.integralSample) < target} := by
  let bank := CoefficientRequests.layerBank bounds retained preparedSource cache forms initial span_eq proper
    modelFloor scalarFloor target positive sourceAccuracy prepared selected depthFloor
  let requests := CoefficientRequests.LayerBank.requests bounds bank
  exact ⟨bank, requests,
    CoefficientRequests.layerBank_preparation bounds retained preparedSource cache forms initial span_eq proper
      modelFloor scalarFloor target positive sourceAccuracy prepared selected depthFloor,
    CoefficientRequests.layerBank_precisions bounds retained preparedSource cache forms initial span_eq proper
      modelFloor scalarFloor target positive sourceAccuracy prepared selected depthFloor,
    CoefficientRequests.Precisions.floor_le_depth bounds bank.2.1.val depthFloor,
    fun channel => CoefficientRequests.LayerBank.accurate bounds bank requests span_eq channel⟩

/-- The zero supplied depth preserves the complete former constructor on every original supplied preparation.

The actual Precision vector and its original factory certificate remain
inputs. Whole agreement uses the original default law, including every
Layer, row request, model and cached comparison value.
-/
example (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Jets.Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : CoefficientRequests.Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor (ScalarModels.coefficientTarget initial target)
      (ScalarModels.coefficientTarget_positive initial positive) sourceAccuracy)
    (selected : {actual : CoefficientRequests.Precisions bounds retained.target forms initial
        modelFloor scalarFloor target positive //
      actual = CoefficientRequests.precisions bounds retained.target cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy prepared}) :
    CoefficientRequests.layerBank bounds retained preparedSource cache forms initial span_eq proper
      modelFloor scalarFloor target positive sourceAccuracy prepared selected 0 =
    CoefficientRequests.layerBank bounds retained preparedSource cache forms initial span_eq proper
      modelFloor scalarFloor target positive sourceAccuracy prepared := by
  rcases selected with ⟨value, same⟩
  cases same
  rfl

end LaterTaylor

end TestPurelib.Curves.Legendre.ParallelScalarRequests
