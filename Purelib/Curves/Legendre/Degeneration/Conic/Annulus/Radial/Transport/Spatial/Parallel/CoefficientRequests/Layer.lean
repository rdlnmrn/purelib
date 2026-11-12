module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.CoefficientRequests.Preparation
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

section ParentPayments

open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)

/-- Every actual supplied preparation's common minimum covers its original model floor. -/
theorem Preparation.modelFloor_le (cached : PrimitiveTarget bounds original count)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds cached cache forms initialAccuracy modelFloor scalarFloor
      target positive sourceAccuracy) :
    modelFloor ≤ prepared.1.val.maximum (fun _ selected => selected.1.stage) :=
  ((prepared.1.val.get (0 : Fin 6)).1.lower).trans
    (prepared.1.val.get_le_maximum (fun _ selected => selected.1.stage) (0 : Fin 6))

/-- The exact original paid parent and scalar banks, retaining both owners and their actual stage certificates.

This is an exact Sigma view of the supplied scalar LayerBank, original
covered-parent preparations and existing pair-selection bank. Its numerical
payload and field order are unchanged; the named definition compacts
construction and integral-comparison signatures without another record.
-/
@[expose] def LayerBank.ParentSources (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)} {parentCount pairCurrent : Nat}
    (pairCover : CoveredParents parentCount parents) (pairTarget : Fraction.Rational)
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets path stage) : Type 2 :=
    Σ paidPairs : PreparedParents.PairSelections retained.target.patch
        pairCover pairCurrent pairTarget,
    Σ scalar : LayerBank bounds retained preparedSource cache forms initial
        (max modelFloor paidPairs.modelFloor) scalarFloor target positive sourceAccuracy,
    {spatial : PreparedParents pairCover scalar.1.2.1.val.selection.stage targets //
      modelFloor ≤ scalar.1.2.1.val.selection.stage ∧
        ∀ (channel : Fin 6) (index : Fin parents.length),
          (paidPairs.entry channel index).2.stage ≤ scalar.1.2.1.val.selection.stage ∧
            (paidPairs.entry channel index).2.stage ≤
              (spatial.entry index).preparation.attached.source.selection.stage}

/-- Compute one global parent/six payment bank and share the same common preparation with both actual outputs.

All pair budgets and selections precede preparation. The caller's model
floor and the pair bank's floor remain visible through their maximum.
The original scalar constructor consumes that complete preparation once;
the original covered-parent builder uses its actual final cached Source
Selection stage. No successful integral comparison, model/domain bound,
Point or alternate request owner is supplied as a premise.
-/
def layerBankWithParents (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
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
    LayerBank.ParentSources (pairCurrent := pairCurrent) bounds retained preparedSource cache forms initial
      modelFloor scalarFloor
      target positive sourceAccuracy pairCover pairTarget targets := by
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

/-- The exact source-cell discrepancy bound on the retained original parent and six-channel caches.

The complete quantified proposition keeps the actual Source Request,
independently floored spatial preparation, ordered pair selections and
both actual stage payments. Its named type compacts dependent metadata;
the scalar acquisition factory is not an input or recomputed payload.
-/
@[expose] def LayerBank.ParentSources.IncrementAccuracy : Prop :=
  ∀ (retained : Anchored bounds original count) (cache : Source.Cache retained.target.patch)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (_points : ParentPoints bounds retained.target retained.sourcePoint frame covered spatialCache)
    {commonFloor : Nat} {commonTarget : Fraction.Rational}
    (requested : Source.Request cache commonFloor commonTarget)
    {pairCurrent : Nat} (pairTarget : Fraction.Rational)
    (paidPairs : PreparedParents.PairSelections retained.target.patch
      spatialCache.covered pairCurrent pairTarget)
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets path stage) {sourceFloor : Nat}
    (spatial : PreparedParents spatialCache.covered sourceFloor targets)
    (_paid : ∀ (channel : Fin 6) (index : Fin spatialCache.parents.length),
      (paidPairs.entry channel index).2.stage ≤ requested.selection.stage ∧
        (paidPairs.entry channel index).2.stage ≤
          (spatial.entry index).preparation.attached.source.selection.stage)
    (channel : Fin 6) (index : Fin spatialCache.parents.length),
    Norm.Basic.normSq
      (((spatial.entry index).preparation.cell.models.cell channel).integralSample -
        ((requested.primitive channel).primitive.value.eval
            (PreparedParent.finishPoint
              (spatialCache.parents[index.val]'index.isLt)).coordinate -
          (requested.primitive channel).primitive.value.eval
            (PreparedParent.startPoint
              (spatialCache.parents[index.val]'index.isLt)).coordinate)) < pairTarget

/-- Each actual retained source cell meets its common primitive payment on the same original spatial parent.

The matching ParentCache fixes the nominal parent occurrence and supplied
cover. Its retained Point bank derives the unflipped original model edge
and both endpoint domains internally. The same stored budget, Selection
and actual source/common model stages pay every odd-power channel. The
spatial floor is independent of the common Request floor. No
successful comparison or desired cell-integral inequality is a premise.
-/
theorem LayerBank.ParentSources.increment_accurate :
    LayerBank.ParentSources.IncrementAccuracy (original := original) (count := count) bounds := by
  intro retained cache frame differential sheet covered spatialCache points commonFloor commonTarget requested
    pairCurrent pairTarget paidPairs baseStart baseFinish path stage targets sourceFloor spatial paidStages
    channel index
  let originalParent := spatial.entry index
  let selected := paidPairs.entry channel index
  let comparisonCells := Jets.Source.CellModels.build requested
    (PreparedParent.startPoint (spatialCache.parents[index.val]'index.isLt)).coordinate
    (PreparedParent.finishPoint (spatialCache.parents[index.val]'index.isLt)).coordinate
    0 (Fraction.Order.Basic.le_refl _)
  let edge := ParentPoints.sourceEdge bounds points index originalParent requested
  have paid := paidStages channel index
  have near := originalParent.preparation.models.pair_integral_difference_lt comparisonCells channel
    selected.1 selected.2 edge.val edge.property paid.2 paid.1
  have boundary := comparisonCells.cell_integralSample_primitive channel
  have sourceEq := congrArg (fun cell => (cell.models.cell channel).integralSample)
    originalParent.preparation.cell_eq
  have commonEq := congrArg (fun value =>
    (originalParent.preparation.models.cell channel).integralSample - value) boundary
  have paidBoundary := (congrArg Norm.Basic.normSq commonEq).symm.trans_lt near
  exact (congrArg Norm.Basic.normSq
    (congrArg (fun value => value -
      ((requested.primitive channel).primitive.value.eval
          (PreparedParent.finishPoint
            (spatialCache.parents[index.val]'index.isLt)).coordinate -
        (requested.primitive channel).primitive.value.eval
          (PreparedParent.startPoint
            (spatialCache.parents[index.val]'index.isLt)).coordinate)) sourceEq)).trans_lt paidBoundary

/-- The exact ordered source-integral bound on the retained original parent and six-channel caches.

The complete quantified proposition keeps the actual Source Request,
independently floored spatial preparation, ordered pair selections and
both actual stage payments. Its named type compacts dependent metadata;
the scalar acquisition factory is not an input or recomputed payload.
-/
@[expose] def LayerBank.ParentSources.IntegralAccuracy : Prop :=
  ∀ (retained : Anchored bounds original count) (cache : Source.Cache retained.target.patch)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (_points : ParentPoints bounds retained.target retained.sourcePoint frame covered spatialCache)
    {commonFloor : Nat} {commonTarget : Fraction.Rational}
    (requested : Source.Request cache commonFloor commonTarget)
    {pairCurrent : Nat} (pairTarget : Fraction.Rational)
    (paidPairs : PreparedParents.PairSelections retained.target.patch
      spatialCache.covered pairCurrent pairTarget)
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets path stage) {sourceFloor : Nat}
    (spatial : PreparedParents spatialCache.covered sourceFloor targets)
    (_paid : ∀ (channel : Fin 6) (index : Fin spatialCache.parents.length),
      (paidPairs.entry channel index).2.stage ≤ requested.selection.stage ∧
        (paidPairs.entry channel index).2.stage ≤
          (spatial.entry index).preparation.attached.source.selection.stage)
    (channel : Fin 6),
    Norm.Basic.normSq
      ((PathModel.mk
          ((PreparedParents.sources
              spatialCache.covered spatial spatialCache.centeredChain).cells channel)).integralSample -
        ((requested.primitive channel).primitive.value.eval
            (coordinate site parameter 2 quarter (by decide +kernel) last) -
          (requested.primitive channel).primitive.value.eval
            (coordinate site parameter 2 quarter (by decide +kernel) first))) ≤
      (spatialCache.parents.length : Fraction.Rational) ^ 2 * pairTarget

/-- The actual ordered six-channel source integral meets its common primitive boundary allowance.

Each original bounded occurrence uses its retained Point and paid model
stages. The same ParentCache supplies the actual centered chain, and the
original finite-sum and primitive telescope laws cancel precisely those
endpoints. The count-squared allowance includes an empty parent spine.
-/
theorem LayerBank.ParentSources.integral_accurate :
    LayerBank.ParentSources.IntegralAccuracy (original := original) (count := count) bounds := by
  intro retained cache frame differential sheet covered spatialCache points commonFloor commonTarget requested
    pairCurrent pairTarget paidPairs baseStart baseFinish path stage targets sourceFloor spatial paidStages channel
  let primitive : Canonical → Canonical := (requested.primitive channel).primitive.value.eval
  let samples : Fin spatialCache.parents.length → Canonical := fun index =>
    ((spatial.entry index).preparation.cell.models.cell channel).integralSample
  let increments : Fin spatialCache.parents.length → Canonical := fun index =>
    primitive ((spatialCache.parents[index.val]'index.isLt).edge.point 1) -
      primitive ((spatialCache.parents[index.val]'index.isLt).edge.point 0)
  have bounded (index : Fin spatialCache.parents.length) :
      Norm.Basic.normSq (samples index - increments index) ≤ pairTarget := by
    have paid := LayerBank.ParentSources.increment_accurate bounds retained cache covered spatialCache points
      requested pairTarget paidPairs targets spatial paidStages channel index
    have startEq : (spatialCache.parents[index.val]'index.isLt).edge.point 0 =
        (PreparedParent.startPoint (spatialCache.parents[index.val]'index.isLt)).coordinate :=
      Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.model_start
        (spatialCache.parents[index.val]'index.isLt)
    have finishEq : (spatialCache.parents[index.val]'index.isLt).edge.point 1 =
        (PreparedParent.finishPoint (spatialCache.parents[index.val]'index.isLt)).coordinate :=
      Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.model_finish
        (spatialCache.parents[index.val]'index.isLt)
    have boundaryEq := congrArg₂ (fun left right : Canonical => left - right)
      (congrArg primitive finishEq) (congrArg primitive startEq)
    have residueEq := congrArg (fun value => samples index - value) boundaryEq
    exact ((congrArg Norm.Basic.normSq residueEq).trans_lt paid).le
  have estimate := Data.Gaussian.Norm.Sum.Indexed.normSq_sumFin_le
    (fun index => samples index - increments index) pairTarget bounded
  have sampleEq := PreparedParents.integralSample_eq_sumFin
    (parameter := parameter) (frame := frame) (basis := differential) (count := 1)
    (floor := sourceFloor) (original := path) (stage := stage) (targets := targets)
    spatialCache.covered spatial spatialCache.centeredChain channel
  have commonEq := (Data.Gaussian.Norm.Sum.Indexed.sumFin_map spatialCache.parents (fun parent =>
    primitive (parent.edge.point 1) - primitive (parent.edge.point 0))).trans
      ((Riemann.Paths.PreparedPrimitivePaths.mapped_increment_sum primitive spatialCache.parents).trans
        (Riemann.Paths.PreparedPrimitivePaths.incrementSum_eq primitive spatialCache.centeredChain.toDirectPathChain))
  have differenceEq := (Algebra.FiniteSum.Fin.sumFin_sub samples increments).trans
    (congrArg₂ (fun left right : Canonical => left - right) sampleEq.symm commonEq)
  have scalarEq := (congrArg Norm.Basic.normSq differenceEq).symm
  exact scalarEq.trans_le estimate

open Purelib.Data.Gaussian.Basic.Canonical (normSq)
open Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests (ControlledSumRequest)
open Purelib.Riemann.Integration.ContinuedPrimitiveOverlap (PrimitivePairBudget PrimitivePairGeometry)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)

/-- The first scaled value-form numerator is the same normalized unit table as the genus-one basis numerator. -/
private theorem valueZero_numerator (differential : Differential 1) :
    (Specification.Table.forms parameter (0 : Fin 6)).numerator.scale
        (Specification.Table.forms parameter (0 : Fin 6)).scale = differentialNumerator differential := by
  have exponent : differential.exponent = 0 :=
    Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ differential.index.isLt)
  change DensePolynomial.scale (1 : Canonical) (DensePolynomial.constant 1) =
    DensePolynomial.shift differential.exponent (DensePolynomial.constant 1)
  rewrite [exponent, DensePolynomial.scale_one_left, DensePolynomial.shift_zero_exponent]
  rfl

/-- The actual source integral and original controlled primitive sum satisfy the same retained cover payment.

The controlled request is supplied with its whole original acquisition
identity at the already selected six-bank floor. Each actual request and
Point is read from its stored bank. The source and controlled computations
remain different outputs on the same original parent occurrences; this
bound does not identify that parent list with a canonical period cycle.
-/
theorem LayerBank.ParentSources.controlled_accurate
    (retained : Anchored bounds original count) (cache : Source.Cache retained.target.patch)
    {frame : Paths.Frame parameter} {differential : Differential 1} {sheet : Fin 2}
    (covered : Covered geometry source)
    (spatialCache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (points : ParentPoints bounds retained.target retained.sourcePoint frame covered spatialCache)
    {commonFloor : Nat} {commonTarget : Fraction.Rational}
    (requested : Source.Request cache commonFloor commonTarget)
    (storedPrimitive : {actual : PrimitiveModel retained.target.patch requested.selection.stage
      ((Specification.Table.forms parameter (0 : Fin 6)).numerator.scale
        (Specification.Table.forms parameter (0 : Fin 6)).scale)
      (Specification.Table.forms parameter (0 : Fin 6)).denominatorPairs // actual = requested.primitive 0})
    {pairCurrent : Nat} (pairTarget : Fraction.Rational)
    (paidPairs : PreparedParents.PairSelections retained.target.patch
      spatialCache.covered pairCurrent pairTarget)
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    (targets : CellEndpoints.Targets path stage) {sourceFloor : Nat}
    (spatial : PreparedParents spatialCache.covered sourceFloor targets)
    (paid : ∀ (channel : Fin 6) (index : Fin spatialCache.parents.length),
      (paidPairs.entry channel index).2.stage ≤ requested.selection.stage ∧
        (paidPairs.entry channel index).2.stage ≤
          (spatial.entry index).preparation.attached.source.selection.stage)
    (requestTarget : Fraction.Rational) (positive : 0 < requestTarget)
    (controlled : {actual : ControlledSumRequest spatialCache.parents 1 requestTarget //
      actual = ControlledSumRequest.acquire spatialCache.covered spatialCache.proper requestTarget positive
        paidPairs.modelFloor}) :
    Norm.Basic.normSq
      ((PathModel.mk
          ((PreparedParents.sources spatialCache.covered spatial
            spatialCache.centeredChain).cells 0)).integralSample - controlled.val.primitiveSum) ≤
        4 * (spatialCache.parents.length : Fraction.Rational) ^ 2 * pairTarget := by
  let numerator := (Specification.Table.forms parameter (0 : Fin 6)).numerator.scale
    (Specification.Table.forms parameter (0 : Fin 6)).scale
  have numeratorEq : numerator = differentialNumerator differential := valueZero_numerator differential
  let model : PrimitiveModel retained.target.patch requested.selection.stage (differentialNumerator differential) :=
    Eq.mp (congrArg (fun value => PrimitiveModel retained.target.patch requested.selection.stage value) numeratorEq)
      storedPrimitive.val
  have primitiveEq : model.primitive.value = storedPrimitive.val.primitive.value := by
    have readback (first last : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
        (same : first = last)
        (actual : PrimitiveModel retained.target.patch requested.selection.stage first) :
        (Eq.mp (congrArg (fun value => PrimitiveModel retained.target.patch requested.selection.stage value)
          same) actual).primitive.value = actual.primitive.value := by
      cases same
      rfl
    exact readback numerator (differentialNumerator differential) numeratorEq storedPrimitive.val
  let requests := controlled.val.requestsAtTarget
  have bounded (index : Fin spatialCache.parents.length) :
      normSq ((requests.get index).request.model.primitive.value.eval
          ((spatialCache.parents[index.val]'index.isLt).edge.point 1) -
        (requests.get index).request.model.primitive.value.eval
          ((spatialCache.parents[index.val]'index.isLt).edge.point 0) -
        (model.primitive.value.eval ((spatialCache.parents[index.val]'index.isLt).edge.point 1) -
          model.primitive.value.eval ((spatialCache.parents[index.val]'index.isLt).edge.point 0))) ≤ pairTarget := by
    let parent := spatialCache.parents[index.val]'index.isLt
    let localRequest := requests.get index
    let selected := paidPairs.entry (0 : Fin 6) index
    let point := DependentProduct.get spatialCache.parents (ParentPoints.points bounds points) index
    have fields : localRequest.neighborhood = (spatialCache.covered.entry index).1.neighborhood 1 ∧
        paidPairs.modelFloor ≤ localRequest.request.index := by
      have original := ControlledSumRequest.acquire_local spatialCache.covered spatialCache.proper
        requestTarget positive paidPairs.modelFloor index
      exact Eq.mpr (congrArg (fun actual : ControlledSumRequest spatialCache.parents 1 requestTarget =>
        (actual.requestsAtTarget.get index).neighborhood =
            (spatialCache.covered.entry index).1.neighborhood 1 ∧
          paidPairs.modelFloor ≤ (actual.requestsAtTarget.get index).request.index) controlled.property) original
    let Parameters := (ContinuedNeighborhood (Paths.polynomial parameter) 1) ×
      (Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial × Canonical)
    let family (parameters : Parameters) :=
      Σ budget : PrimitivePairBudget parameters.1 retained.target.patch parameters.2.1
        (PreparedParent.startPoint parent).coordinate parameters.2.2,
        Search.Selection budget.scale pairCurrent pairTarget
    let originalParameters : Parameters :=
      ⟨(spatialCache.covered.entry index).1.neighborhood 1,
        ⟨numerator, (PreparedParent.finishPoint parent).coordinate⟩⟩
    let actualParameters : Parameters :=
      ⟨localRequest.neighborhood, ⟨differentialNumerator differential, parent.edge.point 1⟩⟩
    have finishEq : parent.edge.point 1 = (PreparedParent.finishPoint parent).coordinate :=
      parent.edge.point_one
    have parametersEq : originalParameters = actualParameters :=
      (congrArg (fun patch => (patch, (numerator,
        (PreparedParent.finishPoint parent).coordinate))) fields.1.symm).trans
        ((congrArg (fun value => (localRequest.neighborhood,
          (value, (PreparedParent.finishPoint parent).coordinate))) numeratorEq).trans
          (congrArg (fun finish => (localRequest.neighborhood,
            (differentialNumerator differential, finish))) finishEq.symm))
    let originalPair : family originalParameters := selected
    let actualPair : family actualParameters := Eq.mp (congrArg family parametersEq) originalPair
    have stageEq : actualPair.2.stage = selected.2.stage := by
      have readback (first last : Parameters) (same : first = last) (entry : family first) :
          (Eq.mp (congrArg family same) entry).2.stage = entry.2.stage := by
        cases same
        rfl
      exact readback originalParameters actualParameters parametersEq originalPair
    have inside := parent_endpoints_inside bounds retained.target frame covered spatialCache parent
      (_root_.List.getElem_mem index.isLt)
    have startInside : retained.target.patch.box.Contains
        (parent.edge.segment.pointAt parent.edge.left.parameter) := by
      have original := inside.1
      rewrite [parent.edge.point_zero] at original
      exact original
    let geometry : PrimitivePairGeometry localRequest.neighborhood retained.target.patch
        (differentialNumerator differential) (parent.edge.segment.pointAt parent.edge.left.parameter)
        (parent.edge.point 1) :=
      { leftStart := localRequest.source_inside
        leftFinish := localRequest.finishInside
        rightStart := startInside
        rightFinish := inside.2
        budget := actualPair.1 }
    have localLater : actualPair.2.stage ≤ localRequest.request.index :=
      stageEq.le.trans ((paidPairs.stage_le 0 index).trans fields.2)
    have commonLater : actualPair.2.stage ≤ requested.selection.stage :=
      stageEq.le.trans (paid 0 index).1
    have estimate := localRequest.increment_mismatch_le geometry point.1 point.2.2 model
      actualPair.2.stage localLater commonLater
    have attained := estimate.trans_lt
      (actualPair.2.allowance_eq.symm.trans_lt actualPair.2.accurate)
    rewrite [parent.edge.point_zero]
    have same (a b c d : Canonical) : a - b - (c - d) = a - b + (d - c) := by ring0
    rewrite [same]
    exact attained.le
  have boundaryBound := requests.boundary_mismatch_le model.primitive.value.eval
    spatialCache.centeredChain.toDirectPathChain pairTarget bounded
  have sumEq : Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments = controlled.val.primitiveSum :=
    (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum
      controlled.val.requestsAtTarget_readbacks.2).trans controlled.val.primitiveSum_eq.symm
  rewrite [sumEq, primitiveEq] at boundaryBound
  rewrite [← Norm.Basic.normSq_eq_canonical] at boundaryBound
  have sourceBound := LayerBank.ParentSources.integral_accurate bounds retained cache covered spatialCache points
    requested pairTarget paidPairs targets spatial paid (0 : Fin 6)
  have commonEq := congrArg (fun actual => actual.primitive.value) storedPrimitive.property
  rewrite [← commonEq] at sourceBound
  let boundary := storedPrimitive.val.primitive.value.eval
      (coordinate site parameter 2 quarter (by decide +kernel) last) -
    storedPrimitive.val.primitive.value.eval
      (coordinate site parameter 2 quarter (by decide +kernel) first)
  let actualSource := (PathModel.mk
    ((PreparedParents.sources spatialCache.covered spatial
      spatialCache.centeredChain).cells 0)).integralSample
  have reversed : Norm.Basic.normSq (boundary - controlled.val.primitiveSum) ≤
      (spatialCache.parents.length : Fraction.Rational) ^ 2 * pairTarget :=
    (Norm.Bounds.normSq_sub_symm boundary controlled.val.primitiveSum).trans_le boundaryBound
  have triangle := Norm.Bounds.normSq_sub_le_via actualSource boundary controlled.val.primitiveSum
  have combined := triangle.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct sourceBound reversed) (by decide +kernel))
  exact combined.trans_eq (by ring0)

end ParentPayments

/-- Read the original base-form ordered request bank from completed actual chronological acquisition rows.

Each output entry forwards the same stored source/interior Point and whole
root request. Exact original Piece equality changes only the bounded index;
residual payment comes from the actual stored head coefficient outcome.
No Point, request, model or comparison producer is executed.
-/
def requests_zero (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy)
    {depth : Nat} (layer : Layer initial depth)
    (rows : Rows bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
      sourceAccuracy prepared layer.accuracy layer.pieces) :
    ScalarModels.LayerRequests bounds retained preparedSource
      (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy prepared 0) layer target := by
  let viewed := models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor target positive
    sourceAccuracy prepared 0
  exact DependentProduct.map layer.pieces rows
    (fun ordinal _row => ScalarModels.CellRequest bounds retained preparedSource viewed
      (layer.pieces[ordinal.val]'ordinal.isLt).cell target)
    (fun _ row => by
      let head := row.2.2.2.get 0
      have paid : row.1.val.cell.primitiveResidual (prepared.2.2.val.get 0).coefficient < target := by
        have actual := head.2.property.1
        rewrite [head.1.property] at actual
        exact actual
      let request : ScalarModels.CellRequest bounds retained preparedSource viewed row.1.val.cell target :=
        ⟨row.2.1, ⟨row.2.2.1, paid⟩⟩
      exact Eq.mp (congrArg
        (fun piece : Piece (forms.get 0) leg.actual layer.accuracy =>
          ScalarModels.CellRequest bounds retained preparedSource viewed piece.cell target)
        row.1.property) request)

/-- The exact original request family on a supplied ordered list of same-channel Pieces. -/
private def PieceRequests (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy)
    (channel : Fin 6) (scalarAccuracy : AccuracyRequest)
    (pieces : List (Piece (forms.get channel) leg.actual scalarAccuracy)) : Type 1 :=
  DependentProduct pieces (fun ordinal => ScalarModels.CellRequest bounds retained preparedSource
    (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor target positive
      sourceAccuracy prepared channel) (pieces[ordinal.val]'ordinal.isLt).cell target)

/-- Attach an actual completed coefficient outcome and original Point to its same supplied Piece.

Only the original CellRequest pair is assembled. The supplied full Piece
equality changes its indices; the actual Point, whole coefficient request
and residual payment come directly from the retained acquisition.
-/
private def cellRequest (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy)
    (scalarAccuracy : AccuracyRequest) (channel : Fin 6)
    (original : Piece (forms.get 0) leg.actual scalarAccuracy)
    (linked : {actual : ScalarPoint bounds retained.target retained.sourcePoint original.source //
      ∀ within : first ≤ original.span.lower ∧ original.span.lower < last,
        actual = scalarPoint bounds retained.target retained.sourcePoint preparedSource original.source within})
    (acquired : Acquired bounds retained original.source linked.val cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy prepared scalarAccuracy original.cell)
    (child : Piece (forms.get channel) leg.actual scalarAccuracy)
    (same : child = Piece.ofCell original.within (acquired.2.get channel).1.val) :
    ScalarModels.CellRequest bounds retained preparedSource
      (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy prepared channel) child.cell target := by
  let viewed := models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor target positive
    sourceAccuracy prepared channel
  let outcome := acquired.2.get channel
  let supplied : ScalarModels.CellRequest bounds retained preparedSource viewed
      (Piece.ofCell original.within outcome.1.val).cell target :=
    ⟨linked, ⟨outcome.2.val, outcome.2.property.1⟩⟩
  exact Eq.mpr (congrArg
    (fun piece : Piece (forms.get channel) leg.actual scalarAccuracy =>
      ScalarModels.CellRequest bounds retained preparedSource viewed piece.cell target) same) supplied

/-- Read one supplied successor request from the same original chronological row.

The complete stored Point and coefficient request are forwarded. The retained
row equation transports their Piece index without another acquisition.
-/
private def rowRequest (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy)
    (scalarAccuracy : AccuracyRequest) (channel : Fin 5)
    (original : Piece (forms.get 0) leg.actual scalarAccuracy)
    (remaining : List (Piece (forms.get 0) leg.actual scalarAccuracy))
    (row : Rows.Entry bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
      sourceAccuracy prepared scalarAccuracy (original :: remaining) ⟨0, Nat.zero_lt_succ _⟩)
    (child : Piece (forms.get channel.succ) leg.actual scalarAccuracy)
    (same : child = original.reweight (forms.get channel.succ)) :
    ScalarModels.CellRequest bounds retained preparedSource
      (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy prepared channel.succ) child.cell target := by
  let outcome := row.2.2.2.get channel.succ
  have constructorEq : Piece.ofCell row.1.val.within outcome.1.val =
      original.reweight (forms.get channel.succ) :=
    (congrArg (fun model => Piece.ofCell row.1.val.within model) outcome.1.property).trans
      (congrArg (fun piece : Piece (forms.get 0) leg.actual scalarAccuracy =>
        piece.reweight (forms.get channel.succ)) row.1.property)
  have alignedHead : child = Piece.ofCell row.1.val.within outcome.1.val :=
    same.trans constructorEq.symm
  exact cellRequest bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
    sourceAccuracy prepared scalarAccuracy channel.succ row.1.val row.2.1 row.2.2 child alignedHead

/-- Project actual successor requests by consuming the retained source and child heads and their literal tails.

The child list is actual supplied data. Its exact row-constructor equation
aligns its nominal sources and coefficient Models. The recursion forwards
stored Points and whole requests without another acquisition or list-prefix
lookup; equality transport changes only the original dependent indices.
-/
private def requestsOnRows (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy)
    (scalarAccuracy : AccuracyRequest) (channel : Fin 5)
    (parents : List (Piece (forms.get 0) leg.actual scalarAccuracy))
    (rows : Rows bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
      sourceAccuracy prepared scalarAccuracy parents)
    (children : List (Piece (forms.get channel.succ) leg.actual scalarAccuracy))
    (aligned : children = parents.map (fun piece => piece.reweight (forms.get channel.succ))) :
    PieceRequests bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
      sourceAccuracy prepared channel.succ scalarAccuracy children := by
  let rec collect (parents : List (Piece (forms.get 0) leg.actual scalarAccuracy))
      (rows : Rows bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy prepared scalarAccuracy parents)
      (children : List (Piece (forms.get channel.succ) leg.actual scalarAccuracy))
      (aligned : children = parents.map (fun piece => piece.reweight (forms.get channel.succ))) :
      PieceRequests bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy prepared channel.succ scalarAccuracy children := by
    cases parents with
    | nil =>
        cases children with
        | nil => exact PUnit.unit
        | cons child remaining =>
            have impossible : False := by cases aligned
            exact impossible.elim
    | cons original remaining =>
        cases children with
        | nil =>
            have impossible : False := by cases aligned
            exact impossible.elim
        | cons child tail =>
            have childDefault : child = original.reweight (forms.get channel.succ) := (List.cons.inj aligned).1
            have alignedTail : tail = remaining.map (fun piece => piece.reweight (forms.get channel.succ)) :=
              (List.cons.inj aligned).2
            let actual := rowRequest bounds retained preparedSource cache forms initialAccuracy
              modelFloor scalarFloor target positive sourceAccuracy prepared scalarAccuracy channel
              original remaining rows.1 child childDefault
            exact ⟨actual, collect remaining rows.2 tail alignedTail⟩
  exact collect parents rows children aligned

/-- Project one actual successor Layer's original request bank from the same retained chronological rows.

The supplied whole Layer equation is the completed cache factory equation.
It derives the original child-list and accuracy transports. Both actual
source and child lists drive the structural projection; all root, Point,
shared-reading and whole Comparison caches remain the stored originals.
-/
def requests_succ (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} {initial : Piece (forms.get 0) leg.actual initialAccuracy}
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy)
    {depth : Nat} (layer : Layer initial depth)
    (rows : Rows bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
      sourceAccuracy prepared layer.accuracy layer.pieces) (channel : Fin 5)
    (output : Layer (initial.reweight (forms.get channel.succ)) depth)
    (same : output = layer.reweight (forms.get channel.succ)
      (some (layer.reweightedPieces (forms.get channel.succ)
        (reweightedCells bounds retained preparedSource cache forms modelFloor scalarFloor target positive
          sourceAccuracy prepared layer rows channel)))) :
    ScalarModels.LayerRequests bounds retained preparedSource
      (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy prepared channel.succ) output target := by
  have accuracyEq : output.accuracy = layer.accuracy := congrArg (fun actual => actual.accuracy) same
  let children : List (Piece (forms.get channel.succ) leg.actual layer.accuracy) :=
    Eq.mp (congrArg (fun accuracy => List (Piece (forms.get channel.succ) leg.actual accuracy)) accuracyEq)
      output.pieces
  have childEq : children = (layer.reweightedPieces (forms.get channel.succ)
      (reweightedCells bounds retained preparedSource cache forms modelFloor scalarFloor target positive
        sourceAccuracy prepared layer rows channel)).val := by
    cases same
    rfl
  have aligned : children = layer.pieces.map (fun piece => piece.reweight (forms.get channel.succ)) :=
    childEq.trans (layer.reweightedPieces (forms.get channel.succ)
      (reweightedCells bounds retained preparedSource cache forms modelFloor scalarFloor target positive
        sourceAccuracy prepared layer rows channel)).property
  let requests := requestsOnRows bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor
    target positive sourceAccuracy prepared layer.accuracy channel layer.pieces rows children aligned
  let original : Σ pieces : List (Piece (forms.get channel.succ) leg.actual layer.accuracy),
      PieceRequests bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy prepared channel.succ layer.accuracy pieces := ⟨children, requests⟩
  let restored : Σ pieces : List (Piece (forms.get channel.succ) leg.actual output.accuracy),
      PieceRequests bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy prepared channel.succ output.accuracy pieces :=
    Eq.mpr (congrArg (fun accuracy =>
      Σ pieces : List (Piece (forms.get channel.succ) leg.actual accuracy),
        PieceRequests bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
          sourceAccuracy prepared channel.succ accuracy pieces) accuracyEq) original
  have roundTrip (left right : AccuracyRequest) (equal : left = right)
      (pieces : List (Piece (forms.get channel.succ) leg.actual left))
      (supplied : PieceRequests bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor
        target positive sourceAccuracy prepared channel.succ right
          (Eq.mp (congrArg (fun accuracy => List (Piece (forms.get channel.succ) leg.actual accuracy)) equal)
            pieces)) :
      (Eq.mpr (congrArg (fun accuracy =>
        Σ pieces : List (Piece (forms.get channel.succ) leg.actual accuracy),
          PieceRequests bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor
            target positive sourceAccuracy prepared channel.succ accuracy pieces) equal)
        ⟨Eq.mp (congrArg (fun accuracy => List (Piece (forms.get channel.succ) leg.actual accuracy)) equal)
          pieces, supplied⟩).1 = pieces := by
    cases equal
    rfl
  have restoredEq : restored.1 = output.pieces := roundTrip output.accuracy layer.accuracy accuracyEq
    output.pieces requests
  exact Eq.mp (congrArg
    (fun pieces : List (Piece (forms.get channel.succ) leg.actual output.accuracy) =>
      PieceRequests bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy prepared channel.succ output.accuracy pieces) restoredEq) restored.2

open Purelib.Algebra.Quadratic (Pair)

/-- Reindex an actual request bank along the exact whole original initial-Piece identity. -/
private def castInitialRequests (retained : Anchored bounds original count)
    (prepared : CurveSource bounds retained.target)
    {numerator : Pair.Polynomial.Coefficients} {pairCount index : Nat}
    {common : Option (PrimitiveModel retained.target.patch index numerator pairCount)}
    (models : ScalarModels bounds retained.target index numerator pairCount common)
    {cellRadicand : Pair.Polynomial.Coefficients} {cellDifferential : OddPowerDifferential cellRadicand}
    {cellData : WaistBounds site parameter cellDifferential}
    {initialAccuracy : AccuracyRequest} {left right : Piece cellData leg.actual initialAccuracy}
    {depth : Nat} (equal : left = right) (layer : Layer right depth)
    {target : Fraction.Rational} (requests : ScalarModels.LayerRequests bounds retained prepared models layer target) :
    ScalarModels.LayerRequests bounds retained prepared models
      (Eq.mpr (congrArg (fun initial => Layer initial depth) equal) layer) target := by
  cases equal
  exact requests

/-- Forward a whole original request bank across exact retained model, index and primitive-input identities. -/
private def castModelRequests (retained : Anchored bounds original count)
    (prepared : CurveSource bounds retained.target)
    {numerator : Pair.Polynomial.Coefficients} {pairCount leftIndex rightIndex : Nat}
    {leftCommon : Option (PrimitiveModel retained.target.patch leftIndex numerator pairCount)}
    {rightCommon : Option (PrimitiveModel retained.target.patch rightIndex numerator pairCount)}
    (left : ScalarModels bounds retained.target leftIndex numerator pairCount leftCommon)
    (right : ScalarModels bounds retained.target rightIndex numerator pairCount rightCommon)
    (indexEq : leftIndex = rightIndex) (commonEq : HEq leftCommon rightCommon) (modelsEq : HEq left right)
    {cellRadicand : Pair.Polynomial.Coefficients} {cellDifferential : OddPowerDifferential cellRadicand}
    {cellData : WaistBounds site parameter cellDifferential}
    {initialAccuracy : AccuracyRequest} {initial : Piece cellData leg.actual initialAccuracy} {depth : Nat}
    {layer : Layer initial depth} {target : Fraction.Rational}
    (requests : ScalarModels.LayerRequests bounds retained prepared left layer target) :
    ScalarModels.LayerRequests bounds retained prepared right layer target := by
  cases indexEq
  cases eq_of_heq commonEq
  cases eq_of_heq modelsEq
  exact requests

/-- Transport the original whole Layer factory equation through an equal initial Piece. -/
private theorem castLayerFactory
    {cellRadicand : Pair.Polynomial.Coefficients} {cellDifferential : OddPowerDifferential cellRadicand}
    {cellData : WaistBounds site parameter cellDifferential}
    {initialAccuracy : AccuracyRequest} {left right : Piece cellData leg.actual initialAccuracy} {depth : Nat}
    (equal : left = right) (layer : Layer right depth) (same : layer = right.layerAt depth) :
    Eq.mpr (congrArg (fun initial => Layer initial depth) equal) layer = left.layerAt depth := by
  cases equal
  exact same

namespace LayerBank

variable {retained : Anchored bounds original count}
variable {preparedSource : CurveSource bounds retained.target} {cache : Source.Cache retained.target.patch}
variable {forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel))}
variable {initialAccuracy : AccuracyRequest} {initial : Piece (forms.get 0) leg.actual initialAccuracy}
variable {modelFloor scalarFloor : Nat} {target : Fraction.Rational} {positive : 0 < target}
variable {sourceAccuracy : AccuracyRequest}
variable {depthFloor : Nat}

/-- Read an actual returned Layer at its original form, reindexing only the identical head Piece.

All six values come from the stored output vector. The head's whole
self-reweight identity changes its dependent index, while every actual
Layer field and numerical sample remains the original cached payload.
-/
def layer (bank : LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor
    target positive sourceAccuracy depthFloor) (channel : Fin 6) :
    Layer (initial.reweight (forms.get channel))
      (Precisions.depth bounds bank.2.1.val depthFloor) := by
  let depth : Nat := Precisions.depth bounds bank.2.1.val depthFloor
  cases channel with
  | mk ordinal bound =>
      cases ordinal with
      | zero =>
          change Layer (initial.reweight (forms.get 0)) depth
          exact Eq.mpr (congrArg
            (fun actual : Piece (forms.get 0) leg.actual initialAccuracy => Layer actual depth) initial.reweight_self)
            (bank.2.2.2.2.val.get 0)
      | succ ordinal =>
          let channel : Fin 5 := ⟨ordinal, Nat.lt_of_succ_lt_succ bound⟩
          exact bank.2.2.2.2.val.get channel.succ

/-- Project all six original typed request banks from the same retained chronological rows.

The exact output-vector equation aligns the supplied Layer at each form.
Both source and strict-interior branches forward their complete original
Point, root request, shared reading and Comparison; no acquisition,
selection, primitive, scalar cell or numerical observation is repeated.
-/
private def modelRequests (bank : LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor
    target positive sourceAccuracy depthFloor) (channel : Fin 6) :
    ScalarModels.LayerRequests bounds retained preparedSource
      (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
        (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
        sourceAccuracy bank.1 channel) (layer bounds bank channel) (ScalarModels.coefficientTarget initial target) := by
  cases channel with
  | mk ordinal bound =>
      cases ordinal with
      | zero =>
          let raw := requests_zero bounds retained preparedSource cache forms modelFloor scalarFloor
            (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
            sourceAccuracy bank.1 bank.2.2.1.val bank.2.2.2.1
          have same : bank.2.2.2.2.val.get 0 = bank.2.2.1.val :=
            (congrArg (fun actual : Layers forms initial _ => actual.get 0) bank.2.2.2.2.property).trans
              (layers_zero bounds retained preparedSource cache forms modelFloor scalarFloor
                (ScalarModels.coefficientTarget initial target)
                (ScalarModels.coefficientTarget_positive initial positive)
                sourceAccuracy bank.1 bank.2.2.1.val bank.2.2.2.1)
          let actual := Eq.mpr (congrArg (fun actual => ScalarModels.LayerRequests bounds retained preparedSource
            (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
              (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
              sourceAccuracy bank.1 0) actual (ScalarModels.coefficientTarget initial target)) same) raw
          exact castInitialRequests bounds retained preparedSource _ initial.reweight_self _ actual
      | succ ordinal =>
          let channel : Fin 5 := ⟨ordinal, Nat.lt_of_succ_lt_succ bound⟩
          have same : bank.2.2.2.2.val.get channel.succ =
              bank.2.2.1.val.reweight (forms.get channel.succ)
                (some (bank.2.2.1.val.reweightedPieces (forms.get channel.succ)
                  (reweightedCells bounds retained preparedSource cache forms modelFloor scalarFloor
                    (ScalarModels.coefficientTarget initial target)
                    (ScalarModels.coefficientTarget_positive initial positive)
                    sourceAccuracy bank.1 bank.2.2.1.val bank.2.2.2.1 channel))) :=
            (congrArg (fun actual : Layers forms initial _ => actual.get channel.succ)
              bank.2.2.2.2.property).trans (DependentVector.ofFn_get _ channel.succ)
          exact requests_succ bounds retained preparedSource cache forms modelFloor scalarFloor
            (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
            sourceAccuracy bank.1 bank.2.2.1.val bank.2.2.2.1 channel (bank.2.2.2.2.val.get channel.succ) same

/-- Each returned complete Layer is the original factory result on that same form at the retained common stage. -/
theorem layer_factory (bank : LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor
    target positive sourceAccuracy depthFloor) (channel : Fin 6) :
    layer bounds bank channel = (initial.reweight (forms.get channel)).layerAt
      (Precisions.depth bounds bank.2.1.val depthFloor) := by
  refine Fin.cases ?_ (fun channel => ?_) channel
  · have same : bank.2.2.2.2.val.get 0 = initial.layerAt _ :=
      ((congrArg (fun actual : Layers forms initial _ => actual.get 0) bank.2.2.2.2.property).trans
        (layers_zero bounds retained preparedSource cache forms modelFloor scalarFloor
          (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
          sourceAccuracy bank.1 bank.2.2.1.val bank.2.2.2.1)).trans bank.2.2.1.property
    exact castLayerFactory initial.reweight_self _ same
  · have same :=
      (congrArg (fun actual : Layers forms initial _ => actual.get channel.succ) bank.2.2.2.2.property).trans
        (layers_succ bounds retained preparedSource cache forms modelFloor scalarFloor
          (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
          sourceAccuracy bank.1 bank.2.2.1.val bank.2.2.2.1 channel)
    exact same.trans ((congrArg (fun actual : Layer initial _ => actual.reweight (forms.get channel.succ))
      bank.2.2.1.property).trans (initial.layerAt_reweight (forms.get channel.succ) _))

/-- The stored Precision consumes the same retained stage, optional primitive and complete original model view. -/
private theorem selected_inputs (bank : LayerBank bounds retained preparedSource cache forms initial
    modelFloor scalarFloor target positive sourceAccuracy depthFloor) (channel : Fin 6) :
    let actual := bank.2.1.val.get channel
    actual.1.val.1 = bank.1.2.1.val.selection.stage ∧
      HEq actual.1.val.2.1 (some (bank.1.2.2.val.get channel)) ∧
      HEq actual.2.models (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
        (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
        sourceAccuracy bank.1 channel) := by
  have factory : bank.2.1.val.get channel = precision bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor channel (initial.reweight (forms.get channel)) target positive sourceAccuracy bank.1 :=
    (congrArg (fun actual : Precisions bounds retained.target forms initial modelFloor scalarFloor target positive =>
      actual.get channel) bank.2.1.property).trans (DependentVector.ofFn_get _ channel)
  have inputs := precision_inputs bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
    channel (initial.reweight (forms.get channel)) target positive sourceAccuracy bank.1
  have same := congrArg (fun actual =>
    actual.1.val.1 = bank.1.2.1.val.selection.stage ∧
      HEq actual.1.val.2.1 (some (bank.1.2.2.val.get channel)) ∧
      HEq actual.2.models (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
        (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
        sourceAccuracy bank.1 channel)) factory
  exact Eq.mpr same ⟨inputs.1, inputs.2.1, inputs.2.2.2⟩

/-- Read all six original request banks on their actual stored Precision models and actual returned Layers.

Whole retained model identities align their original stage and optional
primitive indices. This transport forwards every complete actual request
and Point; the same root, shared reading and Comparison payloads remain
unchanged, with no new selection, sampling or construction.
-/
private def requestAt (bank : LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor
    target positive sourceAccuracy depthFloor) (channel : Fin 6) :
    ScalarModels.LayerRequests bounds retained preparedSource (bank.2.1.val.get channel).2.models
      (layer bounds bank channel) (ScalarModels.coefficientTarget (initial.reweight (forms.get channel)) target) := by
  let actual := bank.2.1.val.get channel
  have inputs := selected_inputs bounds bank channel
  exact castModelRequests bounds retained preparedSource
    (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
      (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
      sourceAccuracy bank.1 channel) actual.2.models inputs.1.symm inputs.2.1.symm inputs.2.2.symm
    (modelRequests bounds bank channel)

/-- The six original typed request banks on this same retained Layer bank and its stored Precision models.

This is exactly the existing eager dependent vector, with each complete
original LayerRequests value indexed by its actual returned Layer. It
introduces no new nominal request or comparison owner.
-/
@[expose] def Requests (bank : LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor
    target positive sourceAccuracy depthFloor) : Type 2 :=
  DependentVector (fun channel : Fin 6 =>
    ScalarModels.LayerRequests bounds retained preparedSource (bank.2.1.val.get channel).2.models
      (layer bounds bank channel) (ScalarModels.coefficientTarget (initial.reweight (forms.get channel)) target))

/-- Materialize all six original request projections once before any bounded request-bank lookup.

Only the previously stored chronological row payloads are consumed. The
vector retains the resulting original typed banks eagerly, so a subsequent
getter returns a complete stored bank without rerunning its structural
projection, any acquisition or any numerical operation.
-/
def requests (bank : LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor
    target positive sourceAccuracy depthFloor) : Requests bounds bank :=
  DependentVector.ofFn (requestAt bounds bank)

/-- Every actual retained channel Layer approximates its own retained primitive boundary at the requested target.

The same materialized Taylor vector pays the common maximum before any
Point acquisition. The original Precision estimate consumes the exact
returned Layer, its original factory spans and projected stored requests;
no residual, domain-success or final sample inequality is a caller premise.
-/
theorem accurate (bank : LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor
    target positive sourceAccuracy depthFloor) (paid : Requests bounds bank)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (channel : Fin 6) :
    Norm.Basic.normSq ((bank.2.1.val.get channel).2.models.common.primitive.value.eval
        (coordinate site parameter 2 quarter (by decide +kernel) last) -
      (bank.2.1.val.get channel).2.models.common.primitive.value.eval
        (coordinate site parameter 2 quarter (by decide +kernel) first) -
      (layer bounds bank channel).model.integralSample) < target := by
  let actual := bank.2.1.val.get channel
  let depth := Precisions.depth bounds bank.2.1.val depthFloor
  have after : actual.2.taylor.stage ≤ depth :=
    (bank.2.1.val.get_le_maximum (fun _ entry => entry.2.taylor.stage) channel).trans
      (Precisions.maximum_le_depth bounds bank.2.1.val depthFloor)
  have spans : (layer bounds bank channel).pieces.map (fun piece => piece.span) =
      Interval.Bisection.parts depth (initial.reweight (forms.get channel)).span := by
    rewrite [layer_factory]
    exact (initial.reweight (forms.get channel)).layerAt_spans depth
  exact ScalarModels.Precision.accurate bounds retained actual.2 ⟨depth, after⟩ span_eq
    (layer bounds bank channel) spans (paid.get channel)

/-- Equality of whole retained indexed models preserves their actual primitive polynomial payload. -/
private theorem model_primitive_value
    {numerator : Pair.Polynomial.Coefficients} {pairs leftIndex rightIndex : Nat}
    {leftCommon : Option (PrimitiveModel retained.target.patch leftIndex numerator pairs)}
    {rightCommon : Option (PrimitiveModel retained.target.patch rightIndex numerator pairs)}
    (left : ScalarModels bounds retained.target leftIndex numerator pairs leftCommon)
    (right : ScalarModels bounds retained.target rightIndex numerator pairs rightCommon)
    (indexEq : leftIndex = rightIndex) (commonEq : HEq leftCommon rightCommon) (modelsEq : HEq left right) :
    left.common.primitive.value = right.common.primitive.value := by
  cases indexEq
  cases eq_of_heq commonEq
  cases eq_of_heq modelsEq
  rfl

/-- Each actual stored Precision primitive is the same polynomial as its original retained Source Request primitive.

Whole original model-cache identities transport the actual model index and
optional primitive input. The retained primitive vector's factory equation
then identifies its original Request constructor. No equality of unrelated
semantic values or polynomial normalization is used.
-/
theorem primitive_value (bank : LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor
    target positive sourceAccuracy depthFloor) (channel : Fin 6) :
    (bank.2.1.val.get channel).2.models.common.primitive.value =
      (bank.1.2.1.val.primitive channel).primitive.value := by
  have inputs := selected_inputs bounds bank channel
  have first := model_primitive_value bounds (bank.2.1.val.get channel).2.models
    (models bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
      (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
      sourceAccuracy bank.1 channel) inputs.1 inputs.2.1 inputs.2.2
  have cached := (models_values bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
    (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
    sourceAccuracy bank.1 channel).2.2
  have source := (primitive bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
    (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
    sourceAccuracy bank.1 channel).property
  exact first.trans ((congrArg (fun common => common.primitive.value) cached).trans
    (congrArg (fun common => common.primitive.value) source))

/-- Actual same-Request spatial cells and retained scalar Layers agree to the computed original integral target.

Both supplied numerical owners remain inputs: the original spatial
CellModels and the complete original scalar bank with its actual requests.
The spatial integral is exactly its same cached primitive boundary, and
original Precision.accurate pays the scalar discrepancy at the retained
Taylor maximum. No desired sample, domain or programme inequality is an
input. This statement does not identify different original patches.
-/
theorem spatial_accurate (bank : LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor
    target positive sourceAccuracy depthFloor) (paid : Requests bounds bank)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last)
    {allowance : Fraction.Rational}
    (spatial : Source.CellModels bank.1.2.1.val
      (coordinate site parameter 2 quarter (by decide +kernel) first)
      (coordinate site parameter 2 quarter (by decide +kernel) last) allowance) (channel : Fin 6) :
    Norm.Basic.normSq ((spatial.cell channel).integralSample -
      (layer bounds bank channel).model.integralSample) < target := by
  have scalar := accurate bounds bank paid span_eq channel
  rewrite [primitive_value] at scalar
  have spatialEq := spatial.cell_integralSample_primitive channel
  exact (congrArg Norm.Basic.normSq
    (congrArg (fun value => value - (layer bounds bank channel).model.integralSample) spatialEq)).trans_lt scalar

end LayerBank

end CoefficientRequests

end CoefficientRequests

end OwnerMove.PrimitiveTarget

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
