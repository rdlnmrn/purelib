module

import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.OwnerTrace
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

public import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests

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

/-- The original six computed coefficient-stage pairs in one materialized bounded container.

Every entry retains its actual scaled form and both original finite
Selections. Lookup returns the stored entry; no stage selection is run by
an entry reader.
-/
@[expose] def CoefficientSelections (cached : PrimitiveTarget bounds original count)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat) (target : Fraction.Rational) : Type 1 :=
  DependentVector (fun channel : Fin 6 =>
    Search.Selection (modelErrorScale bounds cached (forms.get channel)
      (Specification.Table.forms parameter channel).denominatorPairs) modelFloor (target / 2) ×
    Search.Selection (samplingErrorScale bounds cached (forms.get channel) initialAccuracy
      (Specification.Table.forms parameter channel).denominatorPairs) scalarFloor (target / 2))

/-- The original six coefficient primitives materialized from one actual retained common Source Request. -/
@[expose] def CoefficientPrimitives (cached : PrimitiveTarget bounds original count)
    {cache : Source.Cache cached.patch} {floor : Nat} {target : Fraction.Rational}
    (request : Source.Request cache floor target) : Type 1 :=
  DependentVector (fun channel : Fin 6 => PrimitiveModel cached.patch request.selection.stage
    ((Specification.Table.forms parameter channel).numerator.scale
      (Specification.Table.forms parameter channel).scale)
    (Specification.Table.forms parameter channel).denominatorPairs)

namespace CoefficientRequests

/-- The retained coefficient Selections, common Source Request and six actual primitive caches before Point acquisition.

This exact Sigma is the original request bank's numerical preparation
prefix. Its bounded entries and complete factory equalities retain the
original model, power cache, scaled forms and finite search payments.
-/
@[expose] def Preparation (cached : PrimitiveTarget bounds original count)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest) : Type 1 :=
  Σ selections : {actual : CoefficientSelections bounds cached forms initialAccuracy modelFloor scalarFloor target //
      actual = DependentVector.ofFn (fun channel => coefficientSelections bounds cached (forms.get channel)
        initialAccuracy modelFloor scalarFloor target positive
        (Specification.Table.forms parameter channel).denominatorPairs)},
  let commonFloor := selections.val.maximum (fun _ selected => selected.1.stage)
  Σ requested : {actual : Source.Request cache commonFloor sourceAccuracy.tolerance //
      actual = cache.request commonFloor sourceAccuracy.tolerance sourceAccuracy.positive},
  {actual : CoefficientPrimitives bounds cached requested.val //
      actual = DependentVector.ofFn (fun channel => requested.val.primitive channel)}

/-- Compute and retain the original coefficient preparation once before acquiring any scalar Point or root triple. -/
def prepare (cached : PrimitiveTarget bounds original count) (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest) :
    Preparation bounds cached cache forms initialAccuracy modelFloor scalarFloor target positive sourceAccuracy :=
  let selections := DependentVector.ofFn (fun channel => coefficientSelections bounds cached (forms.get channel)
    initialAccuracy modelFloor scalarFloor target positive
      (Specification.Table.forms parameter channel).denominatorPairs)
  let commonFloor := selections.maximum (fun _ selected => selected.1.stage)
  let requested := cache.request commonFloor sourceAccuracy.tolerance sourceAccuracy.positive
  let primitives : CoefficientPrimitives bounds cached requested :=
    DependentVector.ofFn (fun channel => requested.primitive channel)
  ⟨⟨selections, rfl⟩, ⟨requested, rfl⟩, ⟨primitives, rfl⟩⟩

/-- Six actual reweighted cells and their original paid coefficient requests on one retained scalar observation.

The existing dependent vector and Sigma retain each complete Model and
CoefficientRequest. The actual Source Request and primitive bank are the
supplied preparation; no cell-factory equality replaces a supplied cache.
-/
@[expose] def Cell (cached : PrimitiveTarget bounds original count)
    (pointReading : Reading leg.actual span.lower scalarInside)
    (sample : ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter (by decide +kernel) span.lower))
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds cached cache forms initialAccuracy modelFloor scalarFloor
      target positive sourceAccuracy) (scalarAccuracy : AccuracyRequest)
    (base : Model (forms.get 0) pointReading scalarAccuracy)
    (rootRequest : Model.CoefficientRequest (site := site) (parameter := parameter) (quarter := quarter)
      (positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1))
      (actual := leg.actual) (span := span) (inside := scalarInside)
      (radicand := Paths.polynomial parameter) (differential := Specification.Table.forms parameter 0)
      (polynomial := Paths.polynomial parameter) (count := count) (patch := cached.patch)
      (sample := sample) (powers := prepared.2.1.val.models.powers)
      base prepared.2.1.val.model_eq (prepared.2.2.val.get 0)) (channel : Fin 6) : Type 1 :=
  Σ cell : {actual : Model (forms.get channel) pointReading scalarAccuracy //
      actual = Fin.cases
        (motive := fun channel : Fin 6 => Model (forms.get channel) pointReading scalarAccuracy)
        base (fun channel => base.reweight (forms.get channel.succ)) channel},
    {_actual : Model.CoefficientRequest (site := site) (parameter := parameter) (quarter := quarter)
      (positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1))
      (actual := leg.actual) (span := span) (inside := scalarInside)
      (radicand := Paths.polynomial parameter) (differential := Specification.Table.forms parameter channel)
      (polynomial := Paths.polynomial parameter) (count := count) (patch := cached.patch)
      (sample := sample) (powers := prepared.2.1.val.models.powers)
      cell.val prepared.2.1.val.model_eq (prepared.2.2.val.get channel) //
      cell.val.primitiveResidual (prepared.2.2.val.get channel).coefficient < target ∧
        _actual.1 = rootRequest.1 ∧ HEq _actual.2.1 rootRequest.2.1 ∧
          HEq _actual.2.2.val rootRequest.2.2.val}

/-- The six stored typed outcomes of one supplied original scalar coefficient acquisition. -/
@[expose] def Cells (cached : PrimitiveTarget bounds original count)
    (pointReading : Reading leg.actual span.lower scalarInside)
    (sample : ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter (by decide +kernel) span.lower))
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds cached cache forms initialAccuracy modelFloor scalarFloor
      target positive sourceAccuracy) (scalarAccuracy : AccuracyRequest)
    (base : Model (forms.get 0) pointReading scalarAccuracy)
    (rootRequest : Model.CoefficientRequest (site := site) (parameter := parameter) (quarter := quarter)
      (positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1))
      (actual := leg.actual) (span := span) (inside := scalarInside)
      (radicand := Paths.polynomial parameter) (differential := Specification.Table.forms parameter 0)
      (polynomial := Paths.polynomial parameter) (count := count) (patch := cached.patch)
      (sample := sample) (powers := prepared.2.1.val.models.powers)
      base prepared.2.1.val.model_eq (prepared.2.2.val.get 0)) : Type 2 :=
  DependentVector (fun channel : Fin 6 => Cell bounds cached pointReading sample cache forms
    initialAccuracy modelFloor scalarFloor target positive sourceAccuracy prepared scalarAccuracy
      base rootRequest channel)

/-- Assemble six paid requests from one actual supplied cell, root request and retained preparation.

The zero channel forwards the complete actual cell and request. Successor
channels use the original reweights, preserving the same observation,
Point, root, shared reading and whole comparison. Only scalar coefficient
and primitive-polynomial data differ; no numerical acquisition is repeated.
-/
def ofCell (cached : PrimitiveTarget bounds original count)
    (pointReading : Reading leg.actual span.lower scalarInside)
    (sample : ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter (by decide +kernel) span.lower))
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds cached cache forms initialAccuracy modelFloor scalarFloor
      target positive sourceAccuracy) (depth : Nat) (scalarAccuracy : AccuracyRequest)
    (accuracy_eq : scalarAccuracy.tolerance = Geometric.Basic.quarterRadius initialAccuracy.tolerance depth)
    (scalarPaid : prepared.1.val.maximum (fun _ selected => selected.2.stage) ≤ depth)
    (base : Model (forms.get 0) pointReading scalarAccuracy)
    (rootRequest : Model.CoefficientRequest (site := site) (parameter := parameter) (quarter := quarter)
      (positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1))
      (actual := leg.actual) (span := span) (inside := scalarInside)
      (radicand := Paths.polynomial parameter) (differential := Specification.Table.forms parameter 0)
      (polynomial := Paths.polynomial parameter) (count := count) (patch := cached.patch)
      (sample := sample) (powers := prepared.2.1.val.models.powers)
      base prepared.2.1.val.model_eq (prepared.2.2.val.get 0))
    (contained : cached.patch.box.Contains (coordinate site parameter 2 quarter (by decide +kernel) span.lower)) :
    Cells bounds cached pointReading sample cache forms initialAccuracy modelFloor scalarFloor
      target positive sourceAccuracy prepared scalarAccuracy base rootRequest := by
  let requested := prepared.2.1.val
  let primitives := prepared.2.2.val
  have selection_eq (channel : Fin 6) : prepared.1.val.get channel =
      coefficientSelections bounds cached (forms.get channel) initialAccuracy modelFloor scalarFloor target positive
        (Specification.Table.forms parameter channel).denominatorPairs :=
    (congrArg (fun entries : CoefficientSelections bounds cached forms initialAccuracy modelFloor scalarFloor target =>
      entries.get channel) prepared.1.property).trans (DependentVector.ofFn_get _ channel)
  have modelAfter (channel : Fin 6) :
      (coefficientSelections bounds cached (forms.get channel) initialAccuracy modelFloor scalarFloor target positive
        (Specification.Table.forms parameter channel).denominatorPairs).1.stage ≤ requested.selection.stage := by
    have attained := prepared.1.val.get_le_maximum (fun _ selected => selected.1.stage) channel
    rewrite [selection_eq channel] at attained
    exact attained.trans requested.selection.lower
  have scalarAfter (channel : Fin 6) :
      (coefficientSelections bounds cached (forms.get channel) initialAccuracy modelFloor scalarFloor target positive
        (Specification.Table.forms parameter channel).denominatorPairs).2.stage ≤ depth := by
    have attained := prepared.1.val.get_le_maximum (fun _ selected => selected.2.stage) channel
    rewrite [selection_eq channel] at attained
    exact attained.trans scalarPaid
  have payment (channel : Fin 6) (cell : Model (forms.get channel) pointReading scalarAccuracy)
      (request : Model.CoefficientRequest (site := site) (parameter := parameter) (quarter := quarter)
        (positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1))
        (actual := leg.actual) (span := span) (inside := scalarInside)
        (radicand := Paths.polynomial parameter) (differential := Specification.Table.forms parameter channel)
        (polynomial := Paths.polynomial parameter) (count := count) (patch := cached.patch)
        (sample := sample) (powers := requested.models.powers)
        cell requested.model_eq (primitives.get channel)) :
      cell.primitiveResidual (primitives.get channel).coefficient < target :=
    coefficient_error_lt bounds cached cell requested.model_eq (primitives.get channel) request
      initialAccuracy depth modelFloor scalarFloor target positive accuracy_eq
      (modelAfter channel) (scalarAfter channel)
  let Row : Fin 6 → Type 1 := fun channel => Cell bounds cached pointReading sample cache forms
    initialAccuracy modelFloor scalarFloor target positive sourceAccuracy prepared scalarAccuracy
      base rootRequest channel
  let head : Row 0 := ⟨⟨base, rfl⟩, ⟨rootRequest, payment 0 base rootRequest, rfl, HEq.rfl, HEq.rfl⟩⟩
  exact DependentVector.ofFn (Fin.cases head (fun channel => by
    let cell : Model (forms.get channel.succ) pointReading scalarAccuracy := base.reweight (forms.get channel.succ)
    let request := Model.CoefficientRequest.reweight base requested.model_eq (primitives.get 0)
      rootRequest (forms.get channel.succ) rfl
      (fun point => by rewrite [DensePolynomial.eval_scale]; rfl)
      (primitives.get channel.succ) contained
    have comparisonSame : HEq request.2.2.val rootRequest.2.2.val :=
      cast_heq (congrArg (fun retained => Gaussian.Equivalence.Observation.Comparison
        retained rootRequest.2.1.val.rootReading scalarAccuracy.tolerance)
          (base.rootReading_reweight (forms.get channel.succ))).symm rootRequest.2.2.val
    exact ⟨⟨cell, rfl⟩, ⟨request, payment channel.succ cell request, rfl, HEq.rfl, comparisonSame⟩⟩))

/-- The complete original scalar acquisition and its six typed outcomes on the same retained Point.

This exact dependent pair names the existing result without changing its
root, shared reading, complete Comparison or any original owner indices.
It is a compact supplied-data view, not another nominal request family.
-/
@[expose] def Acquired (retained : Anchored bounds original count)
    (pointReading : Reading leg.actual span.lower scalarInside)
    (point : ScalarPoint bounds retained.target retained.sourcePoint pointReading)
    (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : CoefficientRequests.Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy)
    (scalarAccuracy : AccuracyRequest)
    (base : Model (forms.get 0) pointReading scalarAccuracy) : Type 2 :=
  Σ rootRequest : Model.CoefficientRequest (site := site) (parameter := parameter) (quarter := quarter)
        (positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1))
        (actual := leg.actual) (span := span) (inside := scalarInside)
        (radicand := Paths.polynomial parameter) (differential := Specification.Table.forms parameter 0)
        (polynomial := Paths.polynomial parameter) (count := count) (patch := retained.target.patch)
        (sample := point.sample) (powers := prepared.2.1.val.models.powers)
        base prepared.2.1.val.model_eq (prepared.2.2.val.get 0),
      CoefficientRequests.Cells bounds retained.target pointReading point.sample cache forms initialAccuracy
        modelFloor scalarFloor target positive sourceAccuracy prepared scalarAccuracy base rootRequest

end CoefficientRequests

/-- Six paid original coefficient requests retain one common stage, scalar sample, primitive bank and root triple.

The exact Sigma stores the actual finite selection bank, common Source
Request, scalar base model, six original primitives and original base
CoefficientRequest. The final existing dependent vector stores each actual
reweighted Model and its paid original CoefficientRequest. No parallel
request record or nominal parent is introduced.
-/
@[expose] def CoefficientRequests (cached : PrimitiveTarget bounds original count)
    (pointReading : Reading leg.actual span.lower scalarInside)
    (sample : ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter
    (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1)) span.lower))
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest) : Type 2 :=
  Σ selections : {actual : CoefficientSelections bounds cached forms initialAccuracy modelFloor scalarFloor target //
      actual = DependentVector.ofFn (fun channel => coefficientSelections bounds cached (forms.get channel)
        initialAccuracy modelFloor scalarFloor target positive
        (Specification.Table.forms parameter channel).denominatorPairs)},
  let commonFloor := selections.val.maximum (fun _ selected => selected.1.stage)
  let commonDepth := selections.val.maximum (fun _ selected => selected.2.stage)
  Σ requested : {actual : Source.Request cache commonFloor sourceAccuracy.tolerance //
      actual = cache.request commonFloor sourceAccuracy.tolerance sourceAccuracy.positive},
  let scalarAccuracy : AccuracyRequest :=
    ⟨Geometric.Basic.quarterRadius initialAccuracy.tolerance commonDepth,
      Geometric.Basic.quarterRadius_pos initialAccuracy.positive commonDepth⟩
  Σ base : {actual : Model (forms.get 0) pointReading scalarAccuracy //
      actual = Model.build (forms.get 0) pointReading leg.regular scalarAccuracy},
  Σ primitives : {actual : CoefficientPrimitives bounds cached requested.val //
      actual = DependentVector.ofFn (fun channel => requested.val.primitive channel)},
  Σ _rootRequest : Model.CoefficientRequest (site := site) (parameter := parameter) (quarter := quarter)
      (positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1))
      (actual := leg.actual) (span := span) (inside := scalarInside)
      (radicand := Paths.polynomial parameter) (differential := Specification.Table.forms parameter 0)
      (polynomial := Paths.polynomial parameter) (count := count) (patch := cached.patch)
      (sample := sample) (powers := requested.val.models.powers)
      base.val requested.val.model_eq (primitives.val.get 0),
  DependentVector (fun channel : Fin 6 =>
    Σ cell : {actual : Model (forms.get channel) pointReading scalarAccuracy //
        actual = Model.build (forms.get channel) pointReading leg.regular scalarAccuracy},
      {_actual : Model.CoefficientRequest (site := site) (parameter := parameter) (quarter := quarter)
      (positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1))
      (actual := leg.actual) (span := span) (inside := scalarInside)
      (radicand := Paths.polynomial parameter) (differential := Specification.Table.forms parameter channel)
      (polynomial := Paths.polynomial parameter) (count := count) (patch := cached.patch)
        (sample := sample) (powers := requested.val.models.powers)
          cell.val requested.val.model_eq (primitives.val.get channel) //
        cell.val.primitiveResidual (primitives.val.get channel).coefficient < target})

/-- Construct all six original paid coefficient requests from one actual Point and its retained signed link.

Both geometric entry points below derive the supplied link and domain from
their original retained owners. Stages are computed from the actual stored
selection pairs before the common source/model/root acquisition. Each
reweighted request consumes the identical retained root, shared reading and
whole comparison; no entry lookup invokes a producer.
-/
private def coefficientRequestsAt (cached : PrimitiveTarget bounds original count)
    (pointReading : Reading leg.actual span.lower scalarInside)
    (sample : ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter
    (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1)) span.lower))
    (related : Gaussian.Equivalence.NamedEquivalent pointReading.lift.value.name sample.certificate.value.name)
    (contained : cached.patch.box.Contains
      (coordinate site parameter 2 quarter
    (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1)) span.lower))
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest) :
    CoefficientRequests bounds cached pointReading sample cache forms initialAccuracy modelFloor scalarFloor
      target positive sourceAccuracy := by
  let prepared := CoefficientRequests.prepare bounds cached cache forms initialAccuracy modelFloor scalarFloor
    target positive sourceAccuracy
  let selections := prepared.1.val
  let commonDepth := selections.maximum (fun _ selected => selected.2.stage)
  let requested := prepared.2.1.val
  let scalarAccuracy : AccuracyRequest :=
    ⟨Geometric.Basic.quarterRadius initialAccuracy.tolerance commonDepth,
      Geometric.Basic.quarterRadius_pos initialAccuracy.positive commonDepth⟩
  let base : Model (forms.get 0) pointReading scalarAccuracy :=
    Model.build (forms.get 0) pointReading leg.regular scalarAccuracy
  let primitives : CoefficientPrimitives bounds cached requested := prepared.2.2.val
  let rootRequest := Model.coefficientRequest
    (site := site) (parameter := parameter) (quarter := quarter)
    (positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1))
    (actual := leg.actual) (span := span) (inside := scalarInside)
    (polynomial := Paths.polynomial parameter) (count := count) (patch := cached.patch) (sample := sample)
    (stage := requested.selection.stage) (inverse := requested.model) (powers := requested.models.powers)
    (radicand := Paths.polynomial parameter) (differential := Specification.Table.forms parameter 0)
    (data := forms.get 0) (source := pointReading) (accuracy := scalarAccuracy)
    base related rfl (fun point => by rewrite [DensePolynomial.eval_scale]; rfl)
    requested.model_eq (primitives.get 0) contained
  let actual := CoefficientRequests.ofCell bounds cached pointReading sample cache forms
    initialAccuracy modelFloor scalarFloor target positive sourceAccuracy prepared commonDepth scalarAccuracy
    rfl (Nat.le_refl _) base rootRequest contained
  have canonical (channel : Fin 6) :
      Fin.cases (motive := fun channel : Fin 6 => Model (forms.get channel) pointReading scalarAccuracy)
        base (fun channel => base.reweight (forms.get channel.succ)) channel =
      Model.build (forms.get channel) pointReading leg.regular scalarAccuracy := by
    refine Fin.cases (Eq.refl _) ?_ channel
    intro channel
    exact Model.reweight_build (forms.get 0) pointReading leg.regular scalarAccuracy (forms.get channel.succ)
  let Row : Fin 6 → Type 1 := fun channel =>
    Σ cell : {actual : Model (forms.get channel) pointReading scalarAccuracy //
        actual = Model.build (forms.get channel) pointReading leg.regular scalarAccuracy},
      {_actual : Model.CoefficientRequest (site := site) (parameter := parameter) (quarter := quarter)
      (positive := Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1))
      (actual := leg.actual) (span := span) (inside := scalarInside)
      (radicand := Paths.polynomial parameter) (differential := Specification.Table.forms parameter channel)
      (polynomial := Paths.polynomial parameter) (count := count) (patch := cached.patch)
        (sample := sample) (powers := requested.models.powers)
          cell.val requested.model_eq (primitives.get channel) //
        cell.val.primitiveResidual (primitives.get channel).coefficient < target}
  let entries : DependentVector Row := DependentVector.ofFn (fun channel => by
    let entry := actual.get channel
    exact ⟨⟨entry.1.val, entry.1.property.trans (canonical channel)⟩,
      ⟨entry.2.val, entry.2.property.1⟩⟩)
  exact ⟨prepared.1, prepared.2.1, ⟨base, rfl⟩, prepared.2.2, rootRequest, entries⟩

/-- Pay all six original forms on the retained source Point with one actual scalar and root acquisition.

The source relation and common-model containment are those of the same
retained source Point and original move. The scalar span has that actual
source as its lower endpoint; no success inequality is an input.
-/
def sourceCoefficientRequests (cached : PrimitiveTarget bounds original count)
    (sourcePoint : SourcePoint bounds cached) (finish : Fraction.Rational) (ordered : first ≤ finish)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest) :
    CoefficientRequests (span := ⟨first, finish, ordered⟩) bounds cached reading sourcePoint.1 cache forms
      initialAccuracy modelFloor scalarFloor target positive sourceAccuracy :=
  coefficientRequestsAt (span := ⟨first, finish, ordered⟩) bounds cached reading sourcePoint.1 sourcePoint.2
    (source_inside bounds cached) cache forms initialAccuracy modelFloor scalarFloor target positive sourceAccuracy

/-- Pay all six original forms on one retained interior Point and its same original scalar Reading.

The CurvePoint supplies its actual Point and signed link; the original move
supplies containment from strict chronological bounds. The complete shared
source/model/root caches are retained, with no new Point acquisition.
-/
def CurvePoint.coefficientRequests (cached : PrimitiveTarget bounds original count)
    {interior : first < span.lower ∧ span.lower < last}
    (point : CurvePoint bounds cached span.lower scalarReading interior)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest) :
    CoefficientRequests bounds cached scalarReading point.sample cache forms initialAccuracy modelFloor scalarFloor
      target positive sourceAccuracy :=
  coefficientRequestsAt bounds cached scalarReading point.sample point.readingEquivalent
    (curve_inside bounds cached span.lower ⟨interior.1.le, interior.2.le⟩)
    cache forms initialAccuracy modelFloor scalarFloor target positive sourceAccuracy

/-- Pay all six actual coefficients through one retained original scalar source or strict-interior Point.

The supplied preparation, scalar cell and Point are completed caches. One
original branch-aware coefficient request acquires the root, model reading
and numerical comparison. The shared assembly forwards that entire triple
to all six typed outcomes without a per-channel acquisition.
-/
def ScalarPoint.coefficientRequests (retained : Anchored bounds original count)
    (pointReading : Reading leg.actual span.lower scalarInside)
    (point : ScalarPoint bounds retained.target retained.sourcePoint pointReading)
    (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : CoefficientRequests.Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy)
    (depth : Nat) (scalarAccuracy : AccuracyRequest)
    (accuracy_eq : scalarAccuracy.tolerance = Geometric.Basic.quarterRadius initialAccuracy.tolerance depth)
    (scalarPaid : prepared.1.val.maximum (fun _ selected => selected.2.stage) ≤ depth)
    (base : Model (forms.get 0) pointReading scalarAccuracy) :
    CoefficientRequests.Acquired bounds retained pointReading point cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy prepared scalarAccuracy base := by
  let requested := prepared.2.1.val
  let primitives := prepared.2.2.val
  let rootRequest := point.coefficientRequest bounds base
    (stage := requested.selection.stage) (inverse := requested.model)
    (numerator := (Specification.Table.forms parameter 0).numerator.scale
      (Specification.Table.forms parameter 0).scale)
    (pairCount := (Specification.Table.forms parameter 0).denominatorPairs)
    rfl (fun location => by rewrite [DensePolynomial.eval_scale]; rfl)
    requested.models.powers requested.model_eq (primitives.get 0)
  have contained : retained.target.patch.box.Contains
      (coordinate site parameter 2 quarter (by decide +kernel) span.lower) := by
    cases point with
    | inl original =>
        rewrite [original.fst]
        exact source_inside bounds retained.target
    | inr original =>
        exact curve_inside bounds retained.target span.lower ⟨original.fst.1.le, original.fst.2.le⟩
  exact ⟨rootRequest, CoefficientRequests.ofCell bounds retained.target pointReading point.sample cache forms
    initialAccuracy modelFloor scalarFloor target positive sourceAccuracy prepared depth scalarAccuracy
    accuracy_eq scalarPaid base rootRequest contained⟩

namespace CoefficientRequests

/-- The original bounded row retains its whole Piece, linked Point and complete six-coefficient acquisition. -/
@[expose] def Rows.Entry (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy) (scalarAccuracy : AccuracyRequest)
    (pieces : List (Piece (forms.get 0) leg.actual scalarAccuracy))
    (ordinal : Fin pieces.length) : Type 2 :=
    Σ original : {piece : Piece (forms.get 0) leg.actual scalarAccuracy //
        piece = pieces[ordinal.val]'ordinal.isLt},
    Σ linked : {actual : ScalarPoint bounds retained.target retained.sourcePoint original.val.source //
        ∀ within : first ≤ original.val.span.lower ∧ original.val.span.lower < last,
          actual = scalarPoint bounds retained.target retained.sourcePoint preparedSource original.val.source within},
      Acquired bounds retained original.val.source linked.val cache forms initialAccuracy modelFloor scalarFloor
        target positive sourceAccuracy prepared scalarAccuracy original.val.cell

/-- Actual ordered scalar occurrences with one retained Point and complete six-coefficient acquisition each.

Each existing dependent-product entry retains its whole original Piece,
original bounded ordinal, source/interior Point and exact branch factory
identity. The completed acquisition contains the same whole root request,
shared reading and Comparison for every typed coefficient outcome.
-/
@[expose] def Rows (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy) (scalarAccuracy : AccuracyRequest)
    (pieces : List (Piece (forms.get 0) leg.actual scalarAccuracy)) : Type 2 :=
  DependentProduct pieces (Rows.Entry bounds retained preparedSource cache forms initialAccuracy
    modelFloor scalarFloor target positive sourceAccuracy prepared scalarAccuracy pieces)

/-- Acquire one original row before its unchanged chronological tail.

The helper retains the original Piece and bounded occurrence. Its Point and
whole coefficient acquisition consume the supplied preparation exactly once.
-/
private def acquireRow (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy)
    (depth : Nat) (scalarAccuracy : AccuracyRequest)
    (accuracy_eq : scalarAccuracy.tolerance = Geometric.Basic.quarterRadius initialAccuracy.tolerance depth)
    (scalarPaid : prepared.1.val.maximum (fun _ selected => selected.2.stage) ≤ depth)
    (piece : Piece (forms.get 0) leg.actual scalarAccuracy)
    (remaining : List (Piece (forms.get 0) leg.actual scalarAccuracy))
    (within : first ≤ piece.span.lower ∧ piece.span.lower < last) :
    Rows.Entry bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
      sourceAccuracy prepared scalarAccuracy (piece :: remaining) ⟨0, Nat.zero_lt_succ _⟩ :=
  let linked := scalarPoint bounds retained.target retained.sourcePoint preparedSource piece.source within
  let acquired := linked.coefficientRequests bounds retained piece.source cache forms initialAccuracy
    modelFloor scalarFloor target positive sourceAccuracy prepared depth scalarAccuracy accuracy_eq scalarPaid
      piece.cell
  ⟨⟨piece, rfl⟩, ⟨linked, fun _ => rfl⟩, acquired⟩

/-- Acquire one actual six-coefficient row per original retained scalar occurrence in chronological order.

The supplied layer provides the actual cells and exact finite dyadic mesh.
Every source/interior domain is derived internally from that mesh. One
structural recursion consumes each complete original Piece and literal
tail; the shared numerical preparation stays outside all row acquisitions.
-/
def ofLayer (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy
      modelFloor scalarFloor target positive sourceAccuracy)
    {depth : Nat} (layer : Layer initial depth)
    (spans : layer.pieces.map (fun piece => piece.span) = Interval.Bisection.parts depth initial.span)
    (scalarPaid : prepared.1.val.maximum (fun _ selected => selected.2.stage) ≤ depth) :
    Rows bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy
      prepared layer.accuracy layer.pieces := by
  have initialProper : initial.span.lower < initial.span.upper := by
    rewrite [span_eq.1, span_eq.2]
    exact proper
  have within : ∀ piece ∈ layer.pieces, first ≤ piece.span.lower ∧ piece.span.lower < last := by
    intro piece member
    have original := layer.lower_within spans initialProper piece member
    rewrite [span_eq.1, span_eq.2] at original
    exact original
  let rec collect (pieces : List (Piece (forms.get 0) leg.actual layer.accuracy))
      (within : ∀ piece ∈ pieces, first ≤ piece.span.lower ∧ piece.span.lower < last) :
      Rows bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor target positive
        sourceAccuracy
        prepared layer.accuracy pieces :=
    match pieces with
    | [] => PUnit.unit
    | piece :: tail =>
        let head := acquireRow bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor
          target positive sourceAccuracy prepared depth layer.accuracy layer.accuracy_eq scalarPaid piece tail
          (within piece (List.Mem.head tail))
        let rest := collect tail (fun original member => within original (List.Mem.tail piece member))
        ⟨head, rest⟩
  exact collect layer.pieces within

/-- Read actual successor-channel Models and original Piece parents from an already completed ordered row bank.

One structural dependent map forwards each complete supplied Model and
parent. The root request, shared reading and Comparison stay retained in
the original row bank; no entry lookup or acquisition is executed here.
-/
def reweightedCells (retained : Anchored bounds original count)
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
      sourceAccuracy prepared layer.accuracy layer.pieces) (channel : Fin 5) :
    Layer.ReweightedCells layer (forms.get channel.succ) :=
  DependentProduct.map layer.pieces rows
    (fun ordinal _row =>
      Σ original : {piece : Piece (forms.get 0) leg.actual layer.accuracy //
          piece = layer.pieces[ordinal.val]'ordinal.isLt},
        {model : Model (forms.get channel.succ) original.val.source layer.accuracy //
          model = original.val.cell.reweight (forms.get channel.succ)})
    (fun _ row => ⟨row.1, (row.2.2.2.get channel.succ).1⟩)

/-- The six original typed Layers associated with a base-form layer and its five differential reweights.

The head is the same complete supplied Layer. Each successor is the
original reweighted Layer at the same scalar depth and its own original
form, retaining the genuine base Piece rather than replacing its owner.
-/
@[expose] def Layers
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (depth : Nat) : Type 2 :=
  DependentVector (Fin.cases (Layer initial depth)
    (fun channel => Layer (initial.reweight (forms.get channel.succ)) depth))

/-- Assemble six actual original Layers from the single completed chronological acquisition bank.

The head is the identical supplied base Layer. Successor layers forward
the actual Model and whole original Piece stored at each row occurrence.
The original requests, roots, source links and comparisons are not rerun;
only the required typed Piece/list/Layer containers are constructed.
-/
@[expose] def layers (retained : Anchored bounds original count)
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
      sourceAccuracy prepared layer.accuracy layer.pieces) : Layers forms initial depth :=
  DependentVector.ofFn (Fin.cases layer (fun channel =>
    let models := reweightedCells bounds retained preparedSource cache forms modelFloor scalarFloor
      target positive sourceAccuracy prepared layer rows channel
    layer.reweight (forms.get channel.succ) (some (layer.reweightedPieces (forms.get channel.succ) models))))

/-- The head of the six-channel result is the same complete original Layer with its actual numerical model cache. -/
theorem layers_zero (retained : Anchored bounds original count)
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
    (layers bounds retained preparedSource cache forms modelFloor scalarFloor target positive sourceAccuracy
      prepared layer rows).get 0 = layer :=
  DependentVector.ofFn_get _ 0

/-- Each successor Layer consumes its actual retained row Models and equals the whole original default result. -/
theorem layers_succ (retained : Anchored bounds original count)
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
      sourceAccuracy prepared layer.accuracy layer.pieces) (channel : Fin 5) :
    (layers bounds retained preparedSource cache forms modelFloor scalarFloor target positive sourceAccuracy
      prepared layer rows).get channel.succ = layer.reweight (forms.get channel.succ) := by
  exact (DependentVector.ofFn_get _ channel.succ).trans (layer.reweight_supplied (forms.get channel.succ) _)

end CoefficientRequests

section ScalarModels

open Purelib.Riemann.Normalization
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece)

namespace ScalarModels

/-- Retain one original Source Request's actual model, shared powers and supplied whole primitive as scalar models.

The supplied primitive is the actual retained Source primitive at this
channel, not a rebuilt polynomial presentation. The original power-cache
field equations establish its complete factory equality; the numerical
inverse, powers and primitive objects are forwarded literally.
-/
@[expose] def ofSourceRequest (cached : PrimitiveTarget bounds original count)
    {sourceCache : Source.Cache cached.patch} {floor : Nat} {sourceTarget : Fraction.Rational}
    (request : Source.Request sourceCache floor sourceTarget) (channel : Fin 6)
    (primitive : {actual : PrimitiveModel cached.patch request.selection.stage
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs // actual = request.primitive channel}) :
    ScalarModels bounds cached request.selection.stage
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs (some primitive.val) :=
  ofCached bounds cached request.selection.stage
    ((Specification.Table.forms parameter channel).numerator.scale
      (Specification.Table.forms parameter channel).scale)
    ⟨⟨request.model, request.model_eq⟩, ⟨request.models.powers, request.models.powers.eq_build⟩⟩
    (Specification.Table.forms parameter channel).denominatorPairs (some primitive.val) ⟨primitive.val, rfl⟩

/-- The Source-derived scalar view retains all three complete original objects at the same actual stage. -/
theorem ofSourceRequest_values (cached : PrimitiveTarget bounds original count)
    {sourceCache : Source.Cache cached.patch} {floor : Nat} {sourceTarget : Fraction.Rational}
    (request : Source.Request sourceCache floor sourceTarget) (channel : Fin 6)
    (primitive : {actual : PrimitiveModel cached.patch request.selection.stage
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs // actual = request.primitive channel}) :
    let retained := ofSourceRequest bounds cached request channel primitive
    retained.inverse = request.model ∧ HEq retained.powers request.models.powers ∧
      retained.common = primitive.val := by
  exact ⟨rfl, HEq.rfl, rfl⟩

end ScalarModels

namespace CoefficientRequests

/-- Read the exact retained preparation prefix of an already completed original coefficient bank.

Only the original selection vector, Source Request and primitive vector
are forwarded. This finite Sigma view performs no selection, preparation,
root request or coefficient computation.
-/
@[expose] def preparation (cached : PrimitiveTarget bounds original count)
    (pointReading : Reading leg.actual span.lower scalarInside)
    (sample : ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter
        (Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ 1)) span.lower))
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (retained : CoefficientRequests bounds cached pointReading sample cache forms initialAccuracy modelFloor
      scalarFloor target positive sourceAccuracy) :
    Preparation bounds cached cache forms initialAccuracy modelFloor scalarFloor target positive sourceAccuracy :=
  ⟨retained.1, retained.2.1, retained.2.2.2.1⟩

/-- Read one complete retained primitive with its original whole Source factory equation.

The bounded getter consumes the actual materialized primitive bank. Its
certificate comes from that same bank's stored construction equality; no
primitive coefficient or integral is computed by this operation.
-/
@[expose] def primitive (cached : PrimitiveTarget bounds original count)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (retained : Preparation bounds cached cache forms initialAccuracy modelFloor
      scalarFloor target positive sourceAccuracy) (channel : Fin 6) :
    {actual : PrimitiveModel cached.patch retained.2.1.val.selection.stage
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs //
      actual = retained.2.1.val.primitive channel} := by
  let request := retained.2.1.val
  let actual := retained.2.2.val.get channel
  have primitive_eq : actual = request.primitive channel := by
    have whole := congrArg (fun entries : CoefficientPrimitives bounds cached request => entries.get channel)
      retained.2.2.property
    exact whole.trans (DependentVector.ofFn_get _ channel)
  exact ⟨actual, primitive_eq⟩

/-- Consume a retained six-bank occurrence as the original scalar inverse, power and primitive cache view.

Only the actual stored Request and its actual primitive entry are read.
The whole primitive factory equation follows from the existing bank and
bounded getter laws; no Source request, power or primitive is run again.
-/
@[expose] def models (cached : PrimitiveTarget bounds original count)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (retained : Preparation bounds cached cache forms initialAccuracy modelFloor
      scalarFloor target positive sourceAccuracy) (channel : Fin 6) :
    ScalarModels bounds cached retained.2.1.val.selection.stage
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs (some (retained.2.2.val.get channel)) :=
  ScalarModels.ofSourceRequest bounds cached retained.2.1.val channel
    (primitive bounds cached cache forms initialAccuracy modelFloor scalarFloor
      target positive sourceAccuracy retained channel)

/-- The scalar view of each stored channel retains the whole actual Source model, power cache and primitive. -/
theorem models_values (cached : PrimitiveTarget bounds original count)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (sourceAccuracy : AccuracyRequest)
    (retained : Preparation bounds cached cache forms initialAccuracy modelFloor
      scalarFloor target positive sourceAccuracy) (channel : Fin 6) :
    let actual := models bounds cached cache forms initialAccuracy modelFloor scalarFloor
      target positive sourceAccuracy retained channel
    actual.inverse = retained.2.1.val.model ∧ HEq actual.powers retained.2.1.val.models.powers ∧
      actual.common = retained.2.2.val.get channel := by
  unfold models
  exact ScalarModels.ofSourceRequest_values bounds cached _ _ _

/-- Choose the original finite Taylor request from the actual retained six-channel selections and model caches.

The supplied bank was paid at this exact weighted coefficient allowance.
Its common stage dominates this channel's stored model Selection, and its
whole model, powers and primitive are retained in the existing Precision
input. Only the original Horner fold and subsequent Taylor Selection are
computed here; coefficient stages and inverse primitives are not rebuilt.
-/
def precision (cached : PrimitiveTarget bounds original count)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (channel : Fin 6) (initial : Piece (forms.get channel) leg.actual initialAccuracy)
    (integralTarget : Fraction.Rational) (integralPositive : 0 < integralTarget)
    (sourceAccuracy : AccuracyRequest)
    (retained : Preparation bounds cached cache forms initialAccuracy modelFloor
      scalarFloor (ScalarModels.coefficientTarget initial integralTarget)
        (ScalarModels.coefficientTarget_positive initial integralPositive) sourceAccuracy) :
    Σ supplied : ScalarModels.Precision.Retained bounds cached initial modelFloor scalarFloor
        integralTarget integralPositive
        ((Specification.Table.forms parameter channel).numerator.scale
          (Specification.Table.forms parameter channel).scale)
        (Specification.Table.forms parameter channel).denominatorPairs,
      ScalarModels.Precision bounds cached initial modelFloor scalarFloor integralTarget integralPositive
        ((Specification.Table.forms parameter channel).numerator.scale
          (Specification.Table.forms parameter channel).scale)
        (Specification.Table.forms parameter channel).denominatorPairs (some supplied) := by
  let request := retained.2.1.val
  let common := primitive bounds cached cache forms initialAccuracy modelFloor scalarFloor
    (ScalarModels.coefficientTarget initial integralTarget)
    (ScalarModels.coefficientTarget_positive initial integralPositive) sourceAccuracy retained channel
  let selected := retained.1.val.get channel
  have selected_eq : selected = coefficientSelections bounds cached (forms.get channel) initialAccuracy
      modelFloor scalarFloor (ScalarModels.coefficientTarget initial integralTarget)
        (ScalarModels.coefficientTarget_positive initial integralPositive)
        (Specification.Table.forms parameter channel).denominatorPairs := by
    have whole := congrArg (fun actual : CoefficientSelections bounds cached forms initialAccuracy
        modelFloor scalarFloor (ScalarModels.coefficientTarget initial integralTarget) => actual.get channel)
      retained.1.property
    exact whole.trans (DependentVector.ofFn_get _ channel)
  have modelPaid : (coefficientSelections bounds cached (forms.get channel) initialAccuracy
      modelFloor scalarFloor (ScalarModels.coefficientTarget initial integralTarget)
        (ScalarModels.coefficientTarget_positive initial integralPositive)
        (Specification.Table.forms parameter channel).denominatorPairs).1.stage ≤ request.selection.stage := by
    rewrite [← selected_eq]
    exact (retained.1.val.get_le_maximum (fun _ entry => entry.1.stage) channel).trans request.selection.lower
  let supplied : ScalarModels.Precision.Retained bounds cached initial modelFloor scalarFloor
      integralTarget integralPositive
      ((Specification.Table.forms parameter channel).numerator.scale
        (Specification.Table.forms parameter channel).scale)
      (Specification.Table.forms parameter channel).denominatorPairs :=
    ⟨⟨request.selection.stage, some common.val,
      ScalarModels.ofSourceRequest bounds cached request channel common⟩, modelPaid⟩
  exact ⟨supplied, ScalarModels.Precision.ofModels bounds cached initial modelFloor scalarFloor integralTarget
    integralPositive _ _ (some supplied) ⟨selected, selected_eq⟩ supplied.val.2.2⟩

/-- The selected precision retains its actual source stage, primitive and supplied and completed whole model views.

The completed Precision consumes the same cached models as its retained
input. The original ofModels cache theorem certifies that link without
exposing its implementation or reconstructing a model from scalar values.
-/
theorem precision_inputs (cached : PrimitiveTarget bounds original count)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    (initialAccuracy : AccuracyRequest) (modelFloor scalarFloor : Nat)
    (channel : Fin 6) (initial : Piece (forms.get channel) leg.actual initialAccuracy)
    (integralTarget : Fraction.Rational) (integralPositive : 0 < integralTarget)
    (sourceAccuracy : AccuracyRequest)
    (retained : Preparation bounds cached cache forms initialAccuracy modelFloor
      scalarFloor (ScalarModels.coefficientTarget initial integralTarget)
        (ScalarModels.coefficientTarget_positive initial integralPositive) sourceAccuracy) :
    let actual := precision bounds cached cache forms initialAccuracy modelFloor scalarFloor
      channel initial integralTarget integralPositive sourceAccuracy retained
    actual.1.val.1 = retained.2.1.val.selection.stage ∧
      HEq actual.1.val.2.1 (some (retained.2.2.val.get channel)) ∧
      HEq actual.1.val.2.2
        (models bounds cached cache forms initialAccuracy modelFloor scalarFloor
          (ScalarModels.coefficientTarget initial integralTarget)
          (ScalarModels.coefficientTarget_positive initial integralPositive) sourceAccuracy retained channel) ∧
      HEq actual.2.models
        (models bounds cached cache forms initialAccuracy modelFloor scalarFloor
          (ScalarModels.coefficientTarget initial integralTarget)
          (ScalarModels.coefficientTarget_positive initial integralPositive) sourceAccuracy retained channel) := by
  unfold precision
  exact ⟨rfl, HEq.rfl, HEq.rfl,
    (ScalarModels.Precision.ofModels_caches bounds cached initial modelFloor scalarFloor
      integralTarget integralPositive _ _ _ _ _).2⟩

open Purelib.Algebra.Quadratic (Pair)

/-- The six actual original Precision results retained before the common scalar stage is selected.

This exact vector family keeps each supplied source-model view and all
original Horner, Taylor and coefficient Selection caches. It names the
existing complete result without changing any underlying constructor.
-/
@[expose] def Precisions (cached : PrimitiveTarget bounds original count)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialRadicand : Pair.Polynomial.Coefficients}
    {initialDifferential : OddPowerDifferential initialRadicand}
    {initialData : WaistBounds site parameter initialDifferential}
    {initialAccuracy : AccuracyRequest} (initial : Piece initialData leg.actual initialAccuracy)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target) : Type 1 :=
    DependentVector (fun channel : Fin 6 =>
      let channelInitial := initial.reweight (forms.get channel)
      Σ supplied : ScalarModels.Precision.Retained bounds cached channelInitial modelFloor scalarFloor
          target positive
          ((Specification.Table.forms parameter channel).numerator.scale
            (Specification.Table.forms parameter channel).scale)
          (Specification.Table.forms parameter channel).denominatorPairs,
        ScalarModels.Precision bounds cached channelInitial modelFloor scalarFloor target positive
          ((Specification.Table.forms parameter channel).numerator.scale
            (Specification.Table.forms parameter channel).scale)
          (Specification.Table.forms parameter channel).denominatorPairs (some supplied))

/-- Materialize all six original scalar precisions from the same retained preparation before Point acquisition.

Each original Precision keeps its supplied Source model, shared powers,
actual primitive and completed coefficient Selections. Its own finite
Horner fold and Taylor Selection are computed once and stored in the
existing dependent vector. A subsequent maximum reads those stored stages;
no channel lookup selects, refines or prepares a model again.
-/
@[expose] def precisions (cached : PrimitiveTarget bounds original count)
    (cache : Source.Cache cached.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialRadicand : Pair.Polynomial.Coefficients}
    {initialDifferential : OddPowerDifferential initialRadicand}
    {initialData : WaistBounds site parameter initialDifferential}
    {initialAccuracy : AccuracyRequest} (initial : Piece initialData leg.actual initialAccuracy)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds cached cache forms initialAccuracy modelFloor scalarFloor
      (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
      sourceAccuracy) :
    Precisions bounds cached forms initial modelFloor scalarFloor target positive :=
  DependentVector.ofFn (fun channel => precision bounds cached cache forms initialAccuracy
    modelFloor scalarFloor channel (initial.reweight (forms.get channel)) target positive sourceAccuracy prepared)

end CoefficientRequests

end ScalarModels

namespace CoefficientRequests

namespace Precisions

variable {cached : PrimitiveTarget bounds original count}
variable {forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
  (Specification.Table.forms parameter channel))}
variable {initialAccuracy : AccuracyRequest} {initial : Piece (forms.get 0) leg.actual initialAccuracy}
variable {modelFloor scalarFloor : Nat} {target : Fraction.Rational} {positive : 0 < target}

/-- The same retained six Taylor selections pay an explicitly later common depth.

The zero floor is literally the former maximum. A positive floor changes
only the numerical refinement depth; all original selections remain the
same cached values and no search is repeated.
-/
@[expose] def depth (selected : Precisions bounds cached forms initial modelFloor scalarFloor target positive) :
    Nat → Nat
  | 0 => selected.maximum (fun _ entry => entry.2.taylor.stage)
  | floor + 1 => max (selected.maximum (fun _ entry => entry.2.taylor.stage)) (floor + 1)

/-- The complete retained Taylor maximum is paid at the chosen later depth. -/
theorem maximum_le_depth
    (selected : Precisions bounds cached forms initial modelFloor scalarFloor target positive) (floor : Nat) :
    selected.maximum (fun _ entry => entry.2.taylor.stage) ≤ depth bounds selected floor := by
  cases floor with
  | zero => exact Nat.le_refl _
  | succ floor => exact Nat.Order.le_max_left _ _

/-- The requested explicit depth floor is retained by the same paid common depth. -/
theorem floor_le_depth
    (selected : Precisions bounds cached forms initial modelFloor scalarFloor target positive) (floor : Nat) :
    floor ≤ depth bounds selected floor := by
  cases floor with
  | zero => exact Nat.zero_le _
  | succ floor => exact Nat.Order.le_max_right _ _

/-- A floor already paying every retained Taylor selection is exactly the returned depth. -/
theorem depth_eq_of_le
    (selected : Precisions bounds cached forms initial modelFloor scalarFloor target positive) (floor : Nat)
    (paid : selected.maximum (fun _ entry => entry.2.taylor.stage) ≤ floor) :
    depth bounds selected floor = floor := by
  cases floor with
  | zero => exact Nat.le_antisymm paid (Nat.zero_le _)
  | succ floor => exact Nat.max_eq_right paid

end Precisions

/-- The complete retained preparation, scalar stage and actual ordered six-Layer acquisition on one original parent.

The exact Sigma stores completed original selections, source request,
primitives, six Precisions, one factory Layer, its chronological acquisition
rows and their six actual output Layers. Every expensive object is data;
its factory equations certify the same cached values rather than rebuilds.
-/
@[expose] def LayerBank (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest) (depthFloor : Nat := 0) : Type 2 :=
  let error := ScalarModels.coefficientTarget initial target
  let errorPositive := ScalarModels.coefficientTarget_positive initial positive
  Σ prepared : Preparation bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
      error errorPositive sourceAccuracy,
  Σ selected : {actual : Precisions bounds retained.target forms initial
        modelFloor scalarFloor target positive //
      actual = precisions bounds retained.target cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy prepared},
  let depth := Precisions.depth bounds selected.val depthFloor
  Σ layer : {actual : Layer initial depth // actual = initial.layerAt depth},
  Σ rows : Rows bounds retained preparedSource cache forms initialAccuracy modelFloor scalarFloor
      error errorPositive sourceAccuracy prepared layer.val.accuracy layer.val.pieces,
    {actual : Layers forms initial depth //
      actual = layers bounds retained preparedSource cache forms modelFloor scalarFloor error errorPositive
        sourceAccuracy prepared layer.val rows}

/-- Construct the actual six-channel scalar Layer bank with all common stages retained before Point acquisition.

One numerical preparation and one six-Precision vector pay a common Taylor
maximum. The original scalar factory Layer is built once at that stage.
A chronological structural traversal acquires one actual Point/root/shared
Comparison per occurrence, then six original Layers consume those same
stored row Models. No successful domain, residual or sample bound is a
caller premise, and no source preparation is repeated.
-/
def layerBank (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
      (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
      sourceAccuracy := prepare bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
        (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
        sourceAccuracy)
    (selected : {actual : Precisions bounds retained.target forms initial modelFloor scalarFloor target positive //
      actual = precisions bounds retained.target cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy prepared} :=
          ⟨precisions bounds retained.target cache forms initial
            modelFloor scalarFloor target positive sourceAccuracy prepared, rfl⟩)
    (depthFloor : Nat := 0) :
    LayerBank bounds retained preparedSource cache forms initial modelFloor scalarFloor target positive
      sourceAccuracy depthFloor := by
  let error := ScalarModels.coefficientTarget initial target
  have errorPositive : 0 < error := ScalarModels.coefficientTarget_positive initial positive
  let depth := Precisions.depth bounds selected.val depthFloor
  have scalarPaid : prepared.1.val.maximum (fun _ entry => entry.2.stage) ≤ depth := by
    apply DependentVector.maximum_le
    intro channel
    have same : (selected.val.get channel).2.coefficients = prepared.1.val.get channel := by
      have factory := congrArg
        (fun entries : CoefficientSelections bounds retained.target forms initialAccuracy
          modelFloor scalarFloor error => entries.get channel) prepared.1.property
      exact (selected.val.get channel).2.coefficients_eq.trans
        (factory.trans (DependentVector.ofFn_get _ channel)).symm
    have after : (prepared.1.val.get channel).2.stage ≤ (selected.val.get channel).2.taylor.stage := by
      rewrite [← same]
      exact (selected.val.get channel).2.taylor.lower
    exact (after.trans (selected.val.get_le_maximum (fun _ entry => entry.2.taylor.stage) channel)).trans
      (Precisions.maximum_le_depth bounds selected.val depthFloor)
  let layer := initial.layerAt depth
  let rows := ofLayer bounds retained preparedSource cache forms initial span_eq proper modelFloor scalarFloor
    error errorPositive sourceAccuracy prepared layer (initial.layerAt_spans depth) scalarPaid
  let actual := layers bounds retained preparedSource cache forms modelFloor scalarFloor error errorPositive
    sourceAccuracy prepared layer rows
  exact ⟨prepared, selected, ⟨layer, rfl⟩, rows, ⟨actual, rfl⟩⟩

/-- The omitted preparation retains the complete former six-Layer construction and all actual cached results. -/
private theorem layerBank_default_eq (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
      (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
      sourceAccuracy := prepare bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
        (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
        sourceAccuracy)
    (selected : {actual : Precisions bounds retained.target forms initial modelFloor scalarFloor target positive //
      actual = precisions bounds retained.target cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy prepared} :=
          ⟨precisions bounds retained.target cache forms initial
            modelFloor scalarFloor target positive sourceAccuracy prepared, rfl⟩) :
    layerBank bounds retained preparedSource cache forms initial span_eq proper modelFloor scalarFloor
      target positive sourceAccuracy prepared selected 0 = (by
    let error := ScalarModels.coefficientTarget initial target
    have errorPositive : 0 < error := ScalarModels.coefficientTarget_positive initial positive
    let prepared := prepared
    let selected := precisions bounds retained.target cache forms initial
      modelFloor scalarFloor target positive sourceAccuracy prepared
    let depth := selected.maximum (fun _ entry => entry.2.taylor.stage)
    have scalarPaid : prepared.1.val.maximum (fun _ entry => entry.2.stage) ≤ depth := by
      apply DependentVector.maximum_le
      intro channel
      have same : (selected.get channel).2.coefficients = prepared.1.val.get channel := by
        have factory := congrArg
          (fun entries : CoefficientSelections bounds retained.target forms initialAccuracy
            modelFloor scalarFloor error => entries.get channel) prepared.1.property
        exact (selected.get channel).2.coefficients_eq.trans
          (factory.trans (DependentVector.ofFn_get _ channel)).symm
      have after : (prepared.1.val.get channel).2.stage ≤ (selected.get channel).2.taylor.stage := by
        rewrite [← same]
        exact (selected.get channel).2.taylor.lower
      exact after.trans (selected.get_le_maximum (fun _ entry => entry.2.taylor.stage) channel)
    let layer := initial.layerAt depth
    let rows := ofLayer bounds retained preparedSource cache forms initial span_eq proper modelFloor scalarFloor
      error errorPositive sourceAccuracy prepared layer (initial.layerAt_spans depth) scalarPaid
    let actual := layers bounds retained preparedSource cache forms modelFloor scalarFloor error errorPositive
      sourceAccuracy prepared layer rows
    exact ⟨prepared, ⟨selected, rfl⟩, ⟨layer, rfl⟩, rows, ⟨actual, rfl⟩⟩
) := by
  rcases selected with ⟨value, same⟩
  cases same
  rfl

/-- A supplied common preparation is the complete prefix retained by the actual original Layer bank. -/
theorem layerBank_preparation (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
      (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
      sourceAccuracy)
    (selected : {actual : Precisions bounds retained.target forms initial modelFloor scalarFloor target positive //
      actual = precisions bounds retained.target cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy prepared} :=
          ⟨precisions bounds retained.target cache forms initial
            modelFloor scalarFloor target positive sourceAccuracy prepared, rfl⟩)
    (depthFloor : Nat := 0) :
    (layerBank bounds retained preparedSource cache forms initial span_eq proper modelFloor scalarFloor
      target positive sourceAccuracy prepared selected depthFloor).1 = prepared := (rfl)

/-- The actual supplied six-Precision cache is forwarded whole by the original Layer-bank constructor.

The original vector and its exact factory equation are both retained.
Reading the returned cache does not run any of its selections, models,
Horner or Taylor producers again.
-/
theorem layerBank_precisions (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
      (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
      sourceAccuracy)
    (selected : {actual : Precisions bounds retained.target forms initial modelFloor scalarFloor target positive //
      actual = precisions bounds retained.target cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy prepared} :=
          ⟨precisions bounds retained.target cache forms initial
            modelFloor scalarFloor target positive sourceAccuracy prepared, rfl⟩)
    (depthFloor : Nat := 0) :
    HEq (layerBank bounds retained preparedSource cache forms initial span_eq proper modelFloor scalarFloor
      target positive sourceAccuracy prepared selected depthFloor).2.1 selected := (HEq.refl _)

/-- The selected Precision values are the exact original supplied vector.

The factory equality attached to that vector may have a transported preparation
index. This projection reads the same retained values independently of that proof.
-/
theorem layerBank_precisions_values (retained : Anchored bounds original count)
    (preparedSource : CurveSource bounds retained.target) (cache : Source.Cache retained.target.patch)
    (forms : DependentVector (fun channel : Fin 6 => WaistBounds site parameter
      (Specification.Table.forms parameter channel)))
    {initialAccuracy : AccuracyRequest} (initial : Piece (forms.get 0) leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (sourceAccuracy : AccuracyRequest)
    (prepared : Preparation bounds retained.target cache forms initialAccuracy modelFloor scalarFloor
      (ScalarModels.coefficientTarget initial target) (ScalarModels.coefficientTarget_positive initial positive)
      sourceAccuracy)
    (selected : {actual : Precisions bounds retained.target forms initial modelFloor scalarFloor target positive //
      actual = precisions bounds retained.target cache forms initial
        modelFloor scalarFloor target positive sourceAccuracy prepared} :=
          ⟨precisions bounds retained.target cache forms initial
            modelFloor scalarFloor target positive sourceAccuracy prepared, rfl⟩)
    (depthFloor : Nat := 0) :
    (layerBank bounds retained preparedSource cache forms initial span_eq proper modelFloor scalarFloor
      target positive sourceAccuracy prepared selected depthFloor).2.1.val = selected.val := (rfl)

end CoefficientRequests

end CoefficientRequests

end OwnerMove.PrimitiveTarget

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
