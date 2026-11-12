module

public import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.Polynomial
public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.Query
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation

/-! # Actual rooted queries of the original retained polynomial row models

The original request/model occurrence remains indexed by its work product,
floor and stage. One supplied Point and one supplied direct Query feed one
new polynomial observation. Its actual root attachment uses their original
patch bridge, without executing either query or any model factory again.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents.PolynomialWork.Models

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
open Purelib.Curves.Hyperelliptic.Integration.Algebraic.Uniform.Jets (UniformObservation)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)

variable {genus count floor stage : Nat} {curve : HyperellipticCurve genus} {basis : Differential genus}
    {differential : OddPowerDifferential curve.polynomial} {parents : List (CenteredEdge curve basis)}
    {covered : CoveredParents count parents} {work : PolynomialWork covered floor differential}
    (retained : work.Models stage) (ordinary : differential.denominatorPairs = 0)
    (index : Fin parents.length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)

/-- The original spatial coordinate gives the SAME actual parent fraction. -/
theorem coordinate_point : (work.entry index).1.val.point input = (parents[index.val]'index.isLt).edge.point input := by
  unfold Spatial.Coordinate.point
  rewrite [(work.entry index).1.val.displacement_eq]
  rfl

/-- One actual Point, direct Query and polynomial observation on the same retained model occurrence.

The Point and observation keep their complete original factory equations.
The direct Query already retains its own whole Owner factory. The final
comparison relates these actual roots; its numerator and selected model
stage remain those of the original PolynomialWork entry.
-/
@[expose] def RootedQuery :=
  Σ sample : {value : ContinuedNeighborhood.Point ((covered.entry index).val.neighborhood count)
      ((work.entry index).1.val.point input) //
    value = points (covered.entry index).val (covered.entry index).property (work.entry index).1.val
      input inside.1 inside.2},
  Σ direct : PreparedEdge.Query (parents[index.val]'index.isLt).edge input inside,
  Σ observed : {value : UniformObservation curve differential
      (ClearSegment.liftOnSheet (parents[index.val]'index.isLt).edge.sheet
        (parents[index.val]'index.isLt).edge.localSegment) (retained.entry index).2.val.pullback.model input //
    value = (retained.entry index).2.val.observe ordinary
      (ClearSegment.liftOnSheet (parents[index.val]'index.isLt).edge.sheet
        (parents[index.val]'index.isLt).edge.localSegment) input sample.val
      ((work.entry index).1.val.point_inside (polynomialStart_inside (covered.entry index).val count)
        (polynomialFinish_inside (covered.entry index).val count (covered.entry index).property)
        inside.1 inside.2)},
  NamedEquivalent (ownerName direct.owner) observed.val.algebraic.sheetValue.value.name

namespace RootedQuery

/-- Consume the supplied original Point and direct Query once, then observe their SAME retained polynomial model.

The original selected request precedes this observation. The shared patch
comparison consumes the given query caches; the numerical observation
uses the given Point and original inverse/power/primitive/pullback bank.
-/
def ofQueries
    (sample : ContinuedNeighborhood.Point ((covered.entry index).val.neighborhood count)
      ((work.entry index).1.val.point input))
    (sampleFactory : sample = points (covered.entry index).val (covered.entry index).property
      (work.entry index).1.val input inside.1 inside.2)
    (direct : PreparedEdge.Query (parents[index.val]'index.isLt).edge input inside) :
    RootedQuery retained ordinary index input inside :=
  let admission := (work.entry index).1.val.point_inside (polynomialStart_inside (covered.entry index).val count)
    (polynomialFinish_inside (covered.entry index).val count (covered.entry index).property) inside.1 inside.2
  let observed := (retained.entry index).2.val.observe ordinary
    (ClearSegment.liftOnSheet (parents[index.val]'index.isLt).edge.sheet
      (parents[index.val]'index.isLt).edge.localSegment) input sample admission
  let common := (covered.entry index).val.retainedQueryEquivalent count input inside direct
    (coordinate_point (work := work) index input).symm admission sample
  let name := (retained.entry index).2.val.observe_root_name ordinary
    (ClearSegment.liftOnSheet (parents[index.val]'index.isLt).edge.sheet
      (parents[index.val]'index.isLt).edge.localSegment) input sample admission
  let roots := NamedEquivalent.transport direct.name_eq name.symm common
  ⟨⟨sample, sampleFactory⟩, direct, ⟨observed, rfl⟩, roots⟩

/-- Execute both original Point/Query factories once, sharing the same rooted-observation constructor. -/
def build : RootedQuery retained ordinary index input inside :=
  let sample := points (covered.entry index).val (covered.entry index).property (work.entry index).1.val
    input inside.1 inside.2
  let direct := PreparedEdge.Query.build (parents[index.val]'index.isLt).edge input inside
  ofQueries retained ordinary index input inside sample rfl direct

variable {retained ordinary index input inside}
    (queried : RootedQuery retained ordinary index input inside)

/-- Read the SAME actual supplied numerical Point without a new acquisition. -/
@[expose] def sample : ContinuedNeighborhood.Point ((covered.entry index).val.neighborhood count)
    ((work.entry index).1.val.point input) := queried.1.val

/-- Read the SAME actual direct Query, including its complete original Owner factory. -/
@[expose] def direct : PreparedEdge.Query (parents[index.val]'index.isLt).edge input inside := queried.2.1

/-- Read the SAME original polynomial observation with its literal model, numerator and request owners. -/
@[expose] def observed : UniformObservation curve differential
    (ClearSegment.liftOnSheet (parents[index.val]'index.isLt).edge.sheet
      (parents[index.val]'index.isLt).edge.localSegment) (retained.entry index).2.val.pullback.model input :=
  queried.2.2.1.val

/-- Read the actual retained root attachment of these same supplied direct and numerical queries. -/
@[expose] def roots : NamedEquivalent (ownerName queried.direct.owner)
    queried.observed.algebraic.sheetValue.value.name := queried.2.2.2

/-- The complete supplied Point is the original model's Point-query factory on this SAME occurrence. -/
theorem sample_eq : queried.sample = points (covered.entry index).val (covered.entry index).property
    (work.entry index).1.val input inside.1 inside.2 := queried.1.property

/-- The observation is the original model's observer on this SAME retained Point, without a second execution. -/
theorem observed_eq : queried.observed = (retained.entry index).2.val.observe ordinary
    (ClearSegment.liftOnSheet (parents[index.val]'index.isLt).edge.sheet
      (parents[index.val]'index.isLt).edge.localSegment) input queried.sample
    ((work.entry index).1.val.point_inside (polynomialStart_inside (covered.entry index).val count)
      (polynomialFinish_inside (covered.entry index).val count (covered.entry index).property) inside.1 inside.2) :=
  queried.2.2.1.property

/-- The observation keeps the exact certified generator of the SAME retained numerical Point. -/
theorem root_name : queried.observed.algebraic.sheetValue.value.name = queried.sample.certificate.value.name :=
  (congrArg (fun observed : UniformObservation curve differential
      (ClearSegment.liftOnSheet (parents[index.val]'index.isLt).edge.sheet
        (parents[index.val]'index.isLt).edge.localSegment) (retained.entry index).2.val.pullback.model input =>
    observed.algebraic.sheetValue.value.name) queried.observed_eq).trans
    ((retained.entry index).2.val.observe_root_name ordinary
      (ClearSegment.liftOnSheet (parents[index.val]'index.isLt).edge.sheet
        (parents[index.val]'index.isLt).edge.localSegment) input queried.sample
      ((work.entry index).1.val.point_inside (polynomialStart_inside (covered.entry index).val count)
        (polynomialFinish_inside (covered.entry index).val count (covered.entry index).property) inside.1 inside.2))

/-- The exact observation point belongs to its SAME original numerical coordinate at this parameter. -/
theorem point_eq : queried.observed.algebraic.point = (work.entry index).1.val.point input :=
  queried.observed.algebraic.point_eq.trans
    (((retained.entry index).2.val.pullback.observationPoint_eq queried.observed.observation).trans
      (congrArg (work.entry index).1.val.point queried.observed.parameter_eq))

end RootedQuery

end Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh.CoveredParents.PolynomialWork.Models

end
