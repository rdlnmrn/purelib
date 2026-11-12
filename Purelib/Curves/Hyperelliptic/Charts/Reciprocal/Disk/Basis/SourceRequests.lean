module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.SourceEndpointTransport
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Geometry

open Purelib.Riemann

public section

/-! A common request for the actual source endpoint of every basis row.
The source polynomial threshold is selected before sampling; root-owner
transport selects a later reading threshold on the same polynomial bank. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests

open Purelib.Riemann.Normalization

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {genus count : Nat} {curve : Basic.HyperellipticCurve genus} {differential :
  Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    UniformReciprocalCover.Cell data edge}
  {model : UniformReciprocalRootChannels.RootModel cell} {parameter :
    InverseRootPolynomial.Coordinate} {anchor : ArcOwners.Point cap
    model parameter}
  {regular : RegularBounds.Data cap}

set_option genInjectivity false in
/-- A row keeps its own source preparation, cell and root model, with a
certified join to the anchor geometry used by the homogeneous energy fan. -/
structure BasisSourceOwner (regular : RegularBounds.Data cap)
    (anchor : ArcOwners.Point cap model parameter) (row : Fin genus) where
  /-- The original standard differential's retained boundary parent. -/ parent :
    Integration.PreparedSubdivisionModelCore.CenteredEdge curve (Periods.PeriodMatrix.standardDifferential row)
  /-- The retained original source patch. -/ patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent
  /-- The original source model count. -/ count : Nat
  /-- The source data on that same original parent. -/ data :
    UniformReciprocalModels.Data patch count
  /-- The actual retained source edge. -/ edge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge
  /-- The retained edge cell. -/ cell : UniformReciprocalCover.Cell data edge
  /-- The retained source model on that cell. -/ model :
    UniformReciprocalRootChannels.RootModel cell
  /-- The actual source parameter. -/ parameter : InverseRootPolynomial.Coordinate
  /-- The original source point at that parameter. -/ point : ArcOwners.Point cap
    model parameter
  /-- The retained joining from this source point to the chart anchor. -/ joined :
    ArcOwners.Join anchor point
  /-- The cached endpoint comparison on that same joining. -/ comparison :
    ArcSamples.Data regular cell
  /-- The original source comparison bounds. -/ bounds : EndpointComparison.Data
    regular point

constructive_injectivity BasisSourceOwner

/-- Retain the supplied original source point and cache its endpoint comparison with the same model and bounds. -/
@[expose] def BasisSourceOwner.ofPoint {row : Fin genus}
    {sourceParent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve
      (Periods.PeriodMatrix.standardDifferential row)}
    {sourcePatch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch sourceParent} {sourceCount : Nat}
    {sourceData : UniformReciprocalModels.Data sourcePatch sourceCount}
    {sourceEdge : Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {sourceCell :
      UniformReciprocalCover.Cell sourceData sourceEdge}
    {sourceModel : UniformReciprocalRootChannels.RootModel sourceCell} {sourceParameter
      : InverseRootPolynomial.Coordinate}
    (point : ArcOwners.Point cap sourceModel sourceParameter) (joined :
      ArcOwners.Join anchor point)
    (comparison : ArcSamples.Data regular sourceCell) :
      BasisSourceOwner regular anchor row :=
  ⟨sourceParent, sourcePatch, sourceCount, sourceData, sourceEdge, sourceCell, sourceModel, sourceParameter,
    point, joined, comparison, EndpointComparison.Data.build regular point⟩

/-- One retained source owner for each original standard differential in the basis. -/
@[expose] def BasisSourceOwners (regular : RegularBounds.Data cap) (anchor :
  ArcOwners.Point cap model parameter) :=
  Data.Vector.DependentVector (BasisSourceOwner regular
    anchor)

variable {owners : BasisSourceOwners regular
  anchor} {target : InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The dependent vector of source comparison requests on their exact original per-row owners. -/
@[expose] def BasisSourceEntries (owners : BasisSourceOwners
  regular anchor) (tolerance : InverseRootPolynomial.Coordinate) (floor : Nat) :=
  Data.Vector.DependentVector (fun row => EndpointComparison.Request (owners.get
    row).bounds tolerance floor)

set_option genInjectivity false in
/-- A genus-paid source comparison request retaining every basis row's own source owner and a common sufficient stage.
-/
structure BasisSourceRequest (owners : BasisSourceOwners
  regular anchor) (target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The whole-basis source target is positive. -/ positive : 0 < target
  /-- The retained local basis-row tolerance. -/ tolerance : InverseRootPolynomial.Coordinate
  /-- The local tolerance is the original genus-based target allocation. -/ tolerance_eq : tolerance =
    Rational.Budget.Aggregate.perTerm target genus
  /-- The actual source comparison requests on the retained per-row owners. -/ entries :
    BasisSourceEntries owners tolerance floor
  /-- The cached sufficient stage for all source requests. -/ index : Nat
  /-- The common stage is the maximum of the original floor and retained row indices. -/ index_eq : index = max floor
    (entries.maximum fun _ request => request.index)

constructive_injectivity BasisSourceRequest

namespace BasisSourceRequest

/-- Allocate the original basis target and cache every source request with one sufficient shared stage. -/
@[expose] def build (owners : BasisSourceOwners regular
  anchor) (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    BasisSourceRequest owners target floor :=
  let tolerance := Rational.Budget.Aggregate.perTerm target genus
  let entries : BasisSourceEntries owners tolerance floor :=
    Data.Vector.DependentVector.ofFn fun row =>
    EndpointComparison.Request.build (owners.get row).bounds tolerance
      (Rational.Budget.Aggregate.perTerm_positive positive genus) floor
  ⟨positive, tolerance, rfl, entries, max floor (entries.maximum fun _ request => request.index), rfl⟩

variable {index : Nat} {box : Rational.Box} {polynomials :
  Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

/-- Actual source samples indexed by their retained row owners and the corresponding polynomial models. -/
@[expose] def Samples (owners : BasisSourceOwners regular
  anchor) (polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index
  box) :=
  Data.Vector.DependentVector (fun row => ArcSamples.Sample (owners.get
    row).comparison (polynomials.get row))

/-- The exact per-row transports from retained source entries to the chart requests on their original joinings. -/
@[expose] def Transports (request : BasisSourceRequest owners
  target floor)
    {minimum : Nat} (charts : ChartReadings.BasisChartRequest
      anchor.coordinates polynomials target minimum) :=
  Data.Vector.DependentVector (fun row =>
    SourceEndpointTransport (owners.get row).joined
    (request.entries.get row) (charts.entries.get row).endpoint)

set_option genInjectivity false in
/-- The actual basis chart requests and their source transports with one shared sufficient stage. -/
structure ChartRequest (request : BasisSourceRequest owners
  target floor)
    (polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (minimum : Nat) where
  /-- The retained basis chart request. -/ charts :
    ChartReadings.BasisChartRequest anchor.coordinates polynomials target
    minimum
  /-- The actual source-to-chart transports for its original rows. -/ transports :
    Transports request charts
  /-- The cached sufficient stage for charts and transports. -/ stage : Nat
  /-- The common stage is the original maximum of the retained chart and source indices. -/ stage_eq : stage = max
    charts.stage (transports.maximum fun _ transport => transport.stage)

constructive_injectivity ChartRequest

namespace ChartRequest

variable {request : BasisSourceRequest owners
  target floor} {minimum : Nat}

/-- Prepare the basis charts once and retain each original source transport with its sufficient shared stage. -/
@[expose] def build (request : BasisSourceRequest owners
  target floor)
    (polynomials : Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box)
      (minimum : Nat) : ChartRequest
      request polynomials minimum :=
  let charts := ChartReadings.BasisChartRequest.build anchor.coordinates
    polynomials target request.positive minimum
  let transports : Transports request
    charts := Data.Vector.DependentVector.ofFn fun row =>
    SourceEndpointTransport.build (owners.get row).joined
      (request.entries.get row) (charts.entries.get row).endpoint
  ⟨charts, transports, max charts.stage (transports.maximum fun _ transport => transport.stage), rfl⟩

set_option genInjectivity false in
/-- The actual chart evaluation and cached original source values with their rowwise transport bounds. -/
structure Evaluation (charts : ChartRequest
  request polynomials minimum)
    (samples : Samples owners polynomials)
      (coordinate : InverseRootPolynomial.Gaussian) (stage : Nat) where
  /-- The actual retained basis chart evaluation. -/ chart : charts.charts.Evaluation coordinate stage
  /-- The cached vector of original source pullback values. -/ sources : Data.Vector
    InverseRootPolynomial.Gaussian genus
  /-- Each cached source is exactly its retained original source sample value. -/ sources_eq : ∀ row, sources row =
    (samples.get row).pullback.value.eval
    ((owners.get row).parent.edge.point (owners.get row).parameter)⁻¹
  /-- Each original source value differs from its retained chart entry within the fourfold local allowance. -/
    source_close : ∀ row, Gaussian.Norm.Basic.normSq (sources row - chart.direct row) ≤ 4 *
    charts.charts.tolerance

constructive_injectivity Evaluation

/-- Read the retained source samples once; all basis chart evaluations use
exactly the already supplied anchor root, including its sampling stage. -/
@[expose] def evaluate (charts :
  ChartRequest request polynomials minimum)
  (samples : Samples owners polynomials)
    {sample : Cap.Primitives.Sample cap differential index box}
    {endpoint : Coordinates.Overlap.Endpoint anchor.coordinates sample} {stage :
      Nat} (reading : ChartReadings.Endpoint.Reading endpoint stage)
    (branch : HyperellipticReciprocal.originOrder curve = 1)
    (modelLater : request.index ≤ index) (later : charts.stage ≤ stage) :
    Evaluation charts samples
      reading.coordinate stage := by
  let chart := charts.charts.evaluate reading branch ((Data.Nat.Order.le_max_left _ _).trans
    (charts.stage_eq.symm.trans_le later))
  let sources := Data.Vector.Basic.vectorOfFn fun row => (samples.get row).pullback.value.eval
    ((owners.get row).parent.edge.point (owners.get row).parameter)⁻¹
  have close (row : Fin genus) : Gaussian.Norm.Basic.normSq (sources row - chart.direct row) ≤ 4 *
    charts.charts.tolerance := by
    rw [Data.Vector.Basic.vectorOfFn_apply]
    have afterModel := (request.entries.get_le_maximum (fun _ request => request.index) row).trans
      ((Data.Nat.Order.le_max_right _ _).trans (request.index_eq.symm.trans_le modelLater))
    have afterRoot := (charts.transports.get_le_maximum (fun _ transport => transport.stage) row).trans
      ((Data.Nat.Order.le_max_right _ _).trans (charts.stage_eq.symm.trans_le later))
    have bound := SourceEndpointTransport.basis_source_accurate (owners.get
      row).joined (charts.transports.get row)
      (samples.get row) chart afterModel afterRoot
    rw [request.tolerance_eq, ← charts.charts.tolerance_eq] at bound
    exact bound.le
  exact ⟨chart, sources, Data.Vector.Basic.vectorOfFn_apply _, close⟩

/-- The actual retained source vector compares homogeneously with the
polynomial primitive at the root coordinate used by the fan energy. -/
theorem Evaluation.accurate {charts :
  ChartRequest request polynomials minimum}
    {samples : Samples owners polynomials}
      {coordinate : InverseRootPolynomial.Gaussian} {stage : Nat}
    (evaluated : Evaluation
      charts samples coordinate stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Gaussian.Norm.Basic.normSq (sumFin (fun row => coefficients row * evaluated.sources row) -
      polynomials.value coefficients coordinate) ≤
      10 * target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
  evaluated.chart.source_accurate evaluated.sources evaluated.source_close coefficients

namespace Evaluation

variable {charts :
  ChartRequest request
  polynomials minimum} {samples :
  Samples owners
  polynomials}
  {coordinate : InverseRootPolynomial.Gaussian} {stage : Nat}

set_option genInjectivity false in
/-- Cache the two endpoint combinations used by restoration. Both readbacks
remain tied to the original per-row source samples and shared root readings. -/
structure Combination (evaluated :
  Evaluation charts samples
  coordinate stage)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) where
  /-- The cached finite coefficient combination of actual original source values. -/ sourceValue :
    InverseRootPolynomial.Gaussian
  /-- The cached source combination equals its exact retained finite sum. -/ source_eq : sourceValue =
    sumFin (fun row => coefficients row * evaluated.sources row)
  /-- The cached finite coefficient combination of direct chart values. -/ directValue :
    InverseRootPolynomial.Gaussian
  /-- The cached direct value equals its exact retained finite sum. -/ direct_eq : directValue = sumFin
    (fun row => coefficients row * evaluated.chart.direct row)
  /-- The cached source combination meets the fourfold homogeneous transport bound. -/ source_close :
    Gaussian.Norm.Basic.normSq (sourceValue - directValue) ≤ 4 * target *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  /-- The cached source combination meets the tenfold homogeneous chart-primitive bound. -/ chart_close :
    Gaussian.Norm.Basic.normSq (sourceValue - polynomials.value coefficients coordinate) ≤ 10 * target *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
  /-- The cached direct combination meets the original homogeneous chart target. -/ direct_close :
    Gaussian.Norm.Basic.normSq (directValue - polynomials.value coefficients coordinate) ≤ target *
    Readings.PreparedObservationCoercivity.coefficientNormSq coefficients

constructive_injectivity Combination

/-- Cache the supplied finite coefficient combination of original source and direct values, retaining their exact
readbacks and paid comparison bounds. -/
@[expose] def combine (evaluated :
  Evaluation charts samples
  coordinate stage) (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) :
    Combination
      evaluated coefficients :=
  ⟨sumFin (fun row => coefficients row * evaluated.sources row), rfl,
    sumFin (fun row => coefficients row * evaluated.chart.direct row), rfl,
    evaluated.chart.source_direct_accurate evaluated.sources evaluated.source_close coefficients,
    evaluated.accurate coefficients, evaluated.chart.accurate coefficients⟩

end Evaluation
end ChartRequest
end BasisSourceRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceRequests
