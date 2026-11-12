module

import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests.Sources
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

/-! # Parent-source and scalar requests from the same retained primitive bank

These clients keep the original Point bank, six-channel parent sources and
paid scalar layers together. The import-all Preparation and Layer owners
supply the original unexposed producers used by the whole-factory identity.
-/

namespace TestPurelib.Curves.Legendre.ParallelParentSources

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

section ParentPrimitives

open Purelib.Integration.CertifiedProgram (CachedModel)
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

open Purelib.Curves.Legendre.Periods
open OwnerMove.PrimitiveTarget.CoefficientRequests
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge

/-- The exact named return view preserves the entire former parent/scalar factory on all actual input covers.

This regression alone imports the original unexposed construction body.
Every stored selection, preparation, model, request and dependent transport
is the original complete factory result; production body visibility is
unchanged.
-/
example (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Jets.Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {parentCount pairCurrent : Nat}
    (pairCover : CoveredParents parentCount parents) (pairTarget : Fraction.Rational)
    (pairPositive : 0 < pairTarget)
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets path stage) :
    CoefficientRequests.layerBankWithParents (pairCurrent := pairCurrent) bounds retained preparedSource cache forms
      initial span_eq proper modelFloor scalarFloor target positive sourceAccuracy pairCover pairTarget
      pairPositive targets =
    (by
      let paidPairs := PreparedParents.pairSelections retained.target.patch
        pairCover pairCurrent pairTarget pairPositive
      let minimum := max modelFloor paidPairs.modelFloor
      let error := ScalarModels.coefficientTarget initial target
      have errorPositive : 0 < error := ScalarModels.coefficientTarget_positive initial positive
      let prepared := prepare bounds retained.target cache forms initialAccuracy minimum scalarFloor
        error errorPositive sourceAccuracy
      let scalar := layerBank bounds retained preparedSource cache forms initial span_eq proper minimum scalarFloor
        target positive sourceAccuracy prepared
      let spatial := Jets.Source.Cell.prepareCovered pairCover prepared.2.1.val.selection.stage targets
      have same : scalar.1 = prepared := layerBank_preparation bounds retained preparedSource cache forms initial
        span_eq proper minimum scalarFloor target positive sourceAccuracy prepared
      have sameStage : prepared.2.1.val.selection.stage = scalar.1.2.1.val.selection.stage :=
        congrArg (fun value => value.2.1.val.selection.stage) same.symm
      let actualSpatial := Eq.mp (congrArg
        (fun selectedStage => PreparedParents pairCover selectedStage targets) sameStage) spatial
      have minimumPaid : minimum ≤ prepared.2.1.val.selection.stage :=
        (Preparation.modelFloor_le bounds retained.target cache forms initialAccuracy minimum scalarFloor
          error errorPositive sourceAccuracy prepared).trans prepared.2.1.val.selection.lower
      have originalPaid : modelFloor ≤ scalar.1.2.1.val.selection.stage :=
        ((Nat.Order.le_max_left modelFloor paidPairs.modelFloor).trans minimumPaid).trans_eq sameStage
      have pairPaid (channel : Fin 6) (index : Fin parents.length) :
          (paidPairs.entry channel index).2.stage ≤ scalar.1.2.1.val.selection.stage :=
        (((paidPairs.stage_le channel index).trans (Nat.Order.le_max_right modelFloor paidPairs.modelFloor)).trans
          minimumPaid).trans_eq sameStage
      exact ⟨paidPairs, scalar, actualSpatial, originalPaid, by
        intro channel index
        have localPaid := (actualSpatial.entry index).floor_le_model_stage
        exact ⟨pairPaid channel index, (pairPaid channel index).trans localPaid⟩⟩
    ) := (rfl)

/-- The original retained Point bank, six-channel source bank, readings and their paid comparisons. -/
private def CachedParentSix (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Jets.Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Parallel.Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent : Nat)
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets path stage) : Type 2 :=
    ParentPoints bounds retained.target retained.sourcePoint frame covered spatialCache ×
      (Σ result : LayerBank.ParentSources (pairCurrent := pairCurrent) bounds retained
          preparedSource cache forms initial modelFloor scalarFloor (target / 4)
          (quarter_pos positive) sourceAccuracy spatialCache.covered
          (Budget.Aggregate.perTerm (target / 4) spatialCache.parents.length) targets,
        Σ spatial : {actual : Jets.Source.Path parameter spatialCache.centeredChain.path //
            actual = PreparedParents.sources
              spatialCache.covered result.2.2.val spatialCache.centeredChain},
        Σ readings : {actual : DependentVector (fun _ : Fin 6 =>
              CachedModel Cached.Basic.modelOperations × CachedModel Cached.Basic.modelOperations) //
            ∀ channel : Fin 6,
              (actual.get channel).1.model = PathModel.mk (spatial.val.cells channel) ∧
                (actual.get channel).2.model = (CoefficientRequests.LayerBank.layer bounds result.2.1 channel).model},
        {_paid : CoefficientRequests.LayerBank.Requests bounds result.2.1 //
          (∀ (channel : Fin 6) (index : Fin spatialCache.parents.length),
            Norm.Basic.normSq
              (((result.2.2.val.entry index).preparation.cell.models.cell channel).integralSample -
                ((result.2.1.1.2.1.val.primitive channel).primitive.value.eval
                    (Jets.Source.Cell.PreparedParent.finishPoint
                      (spatialCache.parents[index.val]'index.isLt)).coordinate -
                  (result.2.1.1.2.1.val.primitive channel).primitive.value.eval
                    (Jets.Source.Cell.PreparedParent.startPoint
                      (spatialCache.parents[index.val]'index.isLt)).coordinate)) <
                Budget.Aggregate.perTerm (target / 4) spatialCache.parents.length) ∧
          (∀ channel : Fin 6,
            Norm.Basic.normSq ((result.2.1.2.1.val.get channel).2.models.common.primitive.value.eval
                (coordinate site parameter 2 quarter (by decide +kernel) last) -
              (result.2.1.2.1.val.get channel).2.models.common.primitive.value.eval
                (coordinate site parameter 2 quarter (by decide +kernel) first) -
              (CoefficientRequests.LayerBank.layer bounds result.2.1 channel).model.integralSample) < target / 4) ∧
          ∀ channel : Fin 6,
            Norm.Basic.normSq
              ((readings.val.get channel).1.sample - (readings.val.get channel).2.sample) < target})

/-- Retain the actual Point and parent-source banks, then certify their original six cached readings. -/
private def retainParentSix (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Jets.Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Parallel.Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent : Nat)
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets path stage)
    (points : ParentPoints bounds retained.target retained.sourcePoint frame covered spatialCache)
    (result : LayerBank.ParentSources (pairCurrent := pairCurrent) bounds retained
          preparedSource cache forms initial modelFloor scalarFloor (target / 4)
          (quarter_pos positive) sourceAccuracy spatialCache.covered
          (Budget.Aggregate.perTerm (target / 4) spatialCache.parents.length) targets) :
    CachedParentSix (bounds := bounds) retained preparedSource cache forms initial
      modelFloor scalarFloor target positive sourceAccuracy covered spatialCache pairCurrent targets := by
  let pairTarget := Budget.Aggregate.perTerm (target / 4) spatialCache.parents.length
  let sourcePath := PreparedParents.sources
    spatialCache.covered result.2.2.val spatialCache.centeredChain
  let readings : DependentVector (fun _ : Fin 6 =>
      CachedModel Cached.Basic.modelOperations × CachedModel Cached.Basic.modelOperations) :=
    DependentVector.ofFn (fun channel =>
      (CachedModel.canonical (operations := Cached.Basic.modelOperations) (PathModel.mk (sourcePath.cells channel)),
        CachedModel.canonical (operations := Cached.Basic.modelOperations)
          (CoefficientRequests.LayerBank.layer bounds result.2.1 channel).model))
  have readingModels (channel : Fin 6) :
      (readings.get channel).1.model = PathModel.mk (sourcePath.cells channel) ∧
        (readings.get channel).2.model = (CoefficientRequests.LayerBank.layer bounds result.2.1 channel).model := by
    have same : readings.get channel =
        (CachedModel.canonical (operations := Cached.Basic.modelOperations)
            (PathModel.mk (sourcePath.cells channel)),
          CachedModel.canonical (operations := Cached.Basic.modelOperations)
            (CoefficientRequests.LayerBank.layer bounds result.2.1 channel).model) :=
      DependentVector.ofFn_get _ channel
    exact ⟨congrArg (fun actual => actual.1.model) same, congrArg (fun actual => actual.2.model) same⟩
  let paid := CoefficientRequests.LayerBank.requests bounds result.2.1
  refine ⟨points, result, ⟨sourcePath, rfl⟩, ⟨readings, readingModels⟩, paid,
    (fun channel index => LayerBank.ParentSources.increment_accurate bounds retained cache
      covered spatialCache points result.2.1.1.2.1.val pairTarget result.1 targets result.2.2.val
      result.2.2.property.2 channel index),
    (fun channel => CoefficientRequests.LayerBank.accurate bounds result.2.1 paid span_eq channel),
    ?_⟩
  intro channel
  have sourceSample := (readings.get channel).1.sample_eq.trans
    (congrArg PathModel.integralSample (readingModels channel).1)
  have scalarSample := (readings.get channel).2.sample_eq.trans
    (congrArg PathModel.integralSample (readingModels channel).2)
  have differenceEq := congrArg₂ (fun left right : Canonical => left - right) sourceSample scalarSample
  exact (congrArg Norm.Basic.normSq differenceEq).trans_lt
    (LayerBank.ParentSources.scalar_accurate bounds retained preparedSource
      cache forms initial (max modelFloor result.1.modelFloor) scalarFloor target positive sourceAccuracy
      covered spatialCache points targets result.1 result.2.1 result.2.2.val result.2.2.property.2 paid span_eq channel)

section

attribute [local irreducible] CachedParentSix

/-- Construct the actual scalar and parent-source banks once and retain every channel's intrinsic primitive payment.

The original parent Point bank consumes the same actual source Point and
Reference. The supplied covered parent cache fixes the original geometric
occurrences. Both numerical banks and the actual typed scalar requests are
returned, together with one original ordered source Path and six pairs of
original CachedModel records containing their actual sums and allowances.
Original count-paid quarter allowances are computed from the
requested target and the retained parent count; all six actual whole-list
integral bounds follow internally. This is a quantified executable client,
not a closed mesh execution.
-/
def cachedParentSix (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Jets.Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Parallel.Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent : Nat)
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets path stage) :
    CachedParentSix (bounds := bounds) retained preparedSource cache forms initial
      modelFloor scalarFloor target positive sourceAccuracy covered spatialCache pairCurrent targets := by
  have quarterPositive : 0 < target / 4 := quarter_pos positive
  let pairTarget := Budget.Aggregate.perTerm (target / 4) spatialCache.parents.length
  have pairPositive : 0 < pairTarget := Budget.Aggregate.perTerm_positive quarterPositive spatialCache.parents.length
  let result := CoefficientRequests.layerBankWithParents (pairCurrent := pairCurrent) bounds retained preparedSource
    cache forms initial span_eq proper modelFloor scalarFloor (target / 4) quarterPositive sourceAccuracy
    spatialCache.covered pairTarget pairPositive targets
  let points := parentPoints bounds retained.target retained.sourcePoint frame covered spatialCache
    ⟨retained.reference, retained.reference_eq⟩
  exact retainParentSix (bounds := bounds) retained preparedSource cache forms initial span_eq
    modelFloor scalarFloor target positive sourceAccuracy covered spatialCache pairCurrent targets points result

end

/-- The actual emitted source and scalar names have the computed all-six comparison at independent starts.

The returned original request retains its single raw bank and both sampler
receipts per form. Its stored final comparisons bound the actual canonical
samples of the original programme output names at every pair of later
indices. The client neither creates new programme owners nor assumes a
successful sample comparison.
-/
def namedParentSix (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Jets.Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor rawLeftStart rawRightStart leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Parallel.Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent : Nat)
    (sourceFloor : Nat)
    (prepared : (index : Nat) → PreparedParents spatialCache.covered sourceFloor
      (CellEndpoints.Targets.build spatialCache.centeredChain.path index)) :
    {request : LayerBank.ParentSources.NamedProgramRequest bounds retained preparedSource cache
        forms initial modelFloor scalarFloor rawLeftStart rawRightStart leftStart rightStart target positive
        sourceAccuracy covered spatialCache pairCurrent sourceFloor prepared //
      ∀ (channel : Fin 6) (leftLater rightLater : Nat),
        (request.2.get channel).2.leftIndex ≤ leftLater →
        (request.2.get channel).2.rightIndex ≤ rightLater →
        Norm.Basic.normSq
          ((Gaussian.Name.Sampling.approximation
              (PreparedParents.program spatialCache.covered spatialCache.centeredChain
                prepared channel).output.name).sample leftLater -
            (Gaussian.Name.Sampling.approximation
              (initial.reweight (forms.get channel)).program.output.name).sample rightLater) < target} := by
  let request := LayerBank.ParentSources.compareNamedProgrammes bounds retained preparedSource
    cache forms initial modelFloor scalarFloor rawLeftStart rawRightStart leftStart rightStart target positive
    sourceAccuracy covered spatialCache pairCurrent sourceFloor prepared span_eq proper
  refine ⟨request, ?_⟩
  intro channel leftLater rightLater leftPaid rightPaid
  exact (request.2.get channel).2.close leftPaid rightPaid

/-- The compact comparison suffix preserves the complete former raw request type on every original input.

This kernel identity includes the original search, Point bank, parent and
scalar caches, typed request vector, whole comparison vector and index
certificates. The producer's complete former computational body is kept
literal and is separately checked in emitted C.
-/
example (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Jets.Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor leftStart rightStart : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Parallel.Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent : Nat)
    (sourceFloor : Nat)
    (prepared : (index : Nat) → PreparedParents spatialCache.covered sourceFloor
      (CellEndpoints.Targets.build spatialCache.centeredChain.path index)) :
    LayerBank.ParentSources.ProgramRequest bounds retained preparedSource cache forms initial
      modelFloor scalarFloor leftStart rightStart target positive sourceAccuracy
      covered spatialCache pairCurrent sourceFloor prepared = (
  let scale := PreparedParents.errorScale spatialCache.parents +
    Algebra.FiniteSum.Fin.sumFin (fun channel : Fin 6 =>
      (initial.reweight (forms.get channel)).program.errorScale)
  Σ selected : Search.Selection scale (max leftStart rightStart) ((target / 4) / 4),
  Σ _points : ParentPoints bounds retained.target retained.sourcePoint frame covered spatialCache,
  Σ result : LayerBank.ParentSources (pairCurrent := pairCurrent) bounds retained preparedSource
      cache forms initial
      modelFloor (max scalarFloor selected.stage) (((target / 4) / 4) / 4)
      (Fraction.Order.Field.div_pos_direct
        (Fraction.Order.Field.div_pos_direct
          (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) (by decide +kernel))
        (by decide +kernel)) sourceAccuracy spatialCache.covered
      (Rational.Budget.Aggregate.perTerm (((target / 4) / 4) / 4) spatialCache.parents.length)
      (CellEndpoints.Targets.build spatialCache.centeredChain.path selected.stage),
    CoefficientRequests.LayerBank.Requests bounds result.2.1 ×
      {actual : DependentVector (fun channel : Fin 6 => Gaussian.Equivalence.Comparison
          (PreparedParents.program spatialCache.covered spatialCache.centeredChain
            prepared channel).approximation
          (initial.reweight (forms.get channel)).program.approximation leftStart rightStart target) //
        ∀ channel : Fin 6, (actual.get channel).leftIndex = selected.stage ∧
          (actual.get channel).rightIndex =
            result.2.1.2.1.val.maximum (fun _ entry => entry.2.taylor.stage)}) := (rfl)

/-- A strictly later original source preparation meets the same actual six retained scalar Layer bounds.

The source floor is computed above both the same common Source Selection
and the stored pair-selection maximum. Exactly one original prepareCovered
call builds the source row; the supplied scalar bank, Point bank and typed
requests are forwarded unchanged. Every channel's integral estimate follows
from those actual payments, without a successful comparison premise.
-/
def laterParentSix (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Jets.Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Parallel.Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (pairCurrent : Nat)
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets path stage)
    (points : ParentPoints bounds retained.target retained.sourcePoint frame covered spatialCache)
    (paidPairs : PreparedParents.PairSelections retained.target.patch spatialCache.covered pairCurrent
      (Budget.Aggregate.perTerm (target / 4) spatialCache.parents.length))
    (scalar : CoefficientRequests.LayerBank bounds retained preparedSource cache forms initial
      (max modelFloor paidPairs.modelFloor) scalarFloor (target / 4)
      (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) sourceAccuracy)
    (paid : CoefficientRequests.LayerBank.Requests bounds scalar)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) :
    Σ sourceFloor : {floor : Nat // scalar.1.2.1.val.selection.stage < floor ∧ paidPairs.modelFloor ≤ floor},
      {spatial : PreparedParents spatialCache.covered sourceFloor.val targets //
        ∀ channel : Fin 6,
          Norm.Basic.normSq
            ((PathModel.mk ((PreparedParents.sources spatialCache.covered spatial
                spatialCache.centeredChain).cells channel)).integralSample -
              (CoefficientRequests.LayerBank.layer bounds scalar channel).model.integralSample) < target} := by
  have quarterPositive : 0 < target / 4 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let sourceFloor := max scalar.1.2.1.val.selection.stage paidPairs.modelFloor + 1
  have strictlyLater : scalar.1.2.1.val.selection.stage < sourceFloor :=
    Nat.lt_succ_of_le (Nat.Order.le_max_left _ _)
  have pairsLater : paidPairs.modelFloor ≤ sourceFloor :=
    (Nat.Order.le_max_right _ _).trans (Nat.le_succ _)
  let spatial := Jets.Source.Cell.prepareCovered spatialCache.covered sourceFloor targets
  have commonPaid : paidPairs.modelFloor ≤ scalar.1.2.1.val.selection.stage :=
    ((Nat.Order.le_max_right modelFloor paidPairs.modelFloor).trans
      (CoefficientRequests.Preparation.modelFloor_le bounds retained.target cache forms initialAccuracy
        (max modelFloor paidPairs.modelFloor) scalarFloor (ScalarModels.coefficientTarget initial (target / 4))
        (ScalarModels.coefficientTarget_positive initial quarterPositive) sourceAccuracy scalar.1)).trans
          scalar.1.2.1.val.selection.lower
  have stages (channel : Fin 6) (index : Fin spatialCache.parents.length) :
      (paidPairs.entry channel index).2.stage ≤ scalar.1.2.1.val.selection.stage ∧
        (paidPairs.entry channel index).2.stage ≤
          (spatial.entry index).preparation.attached.source.selection.stage :=
    ⟨(paidPairs.stage_le channel index).trans commonPaid,
      ((paidPairs.stage_le channel index).trans pairsLater).trans (spatial.entry index).floor_le_model_stage⟩
  exact ⟨⟨sourceFloor, strictlyLater, pairsLater⟩, spatial, fun channel =>
    LayerBank.ParentSources.scalar_accurate bounds retained preparedSource cache forms initial
      (max modelFloor paidPairs.modelFloor) scalarFloor target positive sourceAccuracy covered spatialCache points
      targets paidPairs scalar spatial stages paid span_eq channel⟩

end ParentPrimitives

end TestPurelib.Curves.Legendre.ParallelParentSources
