module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PolynomialPullback
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ComparisonBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Reciprocal.Bounds
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
open Purelib.Data.Rat
open Purelib.Riemann.Normalization
open Purelib.Riemann.RootContinuation

/-!
# Shared polynomial and chart requests at retained arc vertices

The source-stage request is prepared before choosing the cap polynomial.
The chart request subsequently selects a root-reading stage. Each evaluation
reads that root once and retains the actual pullback and global chart values.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap (Endpoint)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings (ChartRequest)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell data edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {model :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels.RootModel cell}
  {parameter target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

set_option genInjectivity false in
/-- An original reciprocal arc vertex with its retained owner, endpoint bounds and pre-polynomial comparison request. -/
structure Prepared (regular : RegularBounds.Data cap) (model : UniformReciprocalRootChannels.RootModel cell)
    (parameter target : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The original query parameter lies in its retained covered cell interval. -/ inside : edge.left.parameter ≤
    parameter ∧ parameter ≤ edge.right.parameter
  /-- The retained original reciprocal root occurrence and cap coordinate overlap. -/ point : ArcOwners.Point cap model
    parameter
  /-- The cached comparison ceilings for this exact original vertex owner. -/ bounds : EndpointComparison.Data regular
    point
  /-- The original polynomial or chart comparison request at the retained target and floor. -/ request :
    EndpointComparison.Request bounds target floor

constructive_injectivity Prepared

namespace Prepared

/-- Request a comparison on the supplied original vertex owner and cached bounds without reacquiring its root. -/
@[expose] def ofPoint (point : ArcOwners.Point cap model parameter)
    (bounds : EndpointComparison.Data regular point)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared regular model parameter target floor :=
  ⟨point.root.between, point, bounds, EndpointComparison.Request.build bounds target positive floor⟩

/-- Acquire the original reciprocal arc vertex once, cache its bounds and retain its paid polynomial comparison request.
-/
@[expose] def build (regular : RegularBounds.Data cap) (model : UniformReciprocalRootChannels.RootModel cell)
    (parameter : InverseRootPolynomial.Coordinate) (inside : edge.left.parameter ≤ parameter ∧ parameter ≤
      edge.right.parameter)
    (target : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared regular model parameter target floor :=
  let point := ArcOwners.Point.build cap model parameter inside
  let bounds := EndpointComparison.Data.build regular point
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared.ofPoint point bounds target positive floor

end Prepared

variable {index : Nat} {box : Purelib.Geometry.Rational.Box}
  {capSample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}

set_option genInjectivity false in
/-- A retained chart evaluation request on one supplied cap polynomial.

The independent reading stage pays both the original coordinate comparison and the root-square tolerance. -/
structure Chart (prepared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared regular model parameter
  target floor)
    (capSample : Primitives.Sample cap differential index box) (minimum : Nat) where
  /-- The cached original endpoint evaluation on the supplied cap polynomial. -/ endpoint : Coordinates.Overlap.Endpoint
    prepared.point.coordinates capSample
  /-- The positive retained chart tolerance also protecting root-coordinate nonvanishing. -/ tolerance :
    InverseRootPolynomial.Coordinate
  /-- The tolerance is the smaller of the original target and actual root-parameter squared norm. -/ tolerance_eq :
    tolerance = min target (Data.Gaussian.Norm.Basic.normSq ((parent.edge.point parameter)⁻¹ ^
    HyperellipticReciprocal.originOrder curve))
  /-- The original polynomial or chart comparison request at the retained target and floor. -/ request :
    ChartReadings.ChartRequest endpoint tolerance minimum
  /-- The retained common coordinate and chart reading stage. -/ stage : Nat
  /-- The stage is the maximum of the original coordinate comparison floor and chart request stage. -/ stage_eq : stage
    = max prepared.request.coordinate.rightIndex request.stage

constructive_injectivity Chart

namespace Chart

variable {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared regular model parameter
  target floor} {minimum : Nat}

/-- Retain the original endpoint on the supplied cap sample and request its positive chart tolerance at the independent
reading floor. -/
@[expose] def build (prepared : Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared regular model
  parameter target floor)
    (capSample : Primitives.Sample cap differential index box) (minimum : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Chart prepared capSample minimum :=
  let endpoint := Coordinates.Overlap.Endpoint.build prepared.point.coordinates capSample
  let tolerance := min target (Data.Gaussian.Norm.Basic.normSq ((parent.edge.point parameter)⁻¹ ^
    HyperellipticReciprocal.originOrder curve))
  have parameterPositive := Data.Gaussian.Norm.Basic.normSq_pos (SquareRootChannelOwnership.parameter_nonzero
    prepared.point.coordinates.coordinate.certificate)
  let request := ChartRequest.build endpoint tolerance (Fraction.Order.Basic.lt_min prepared.request.positive
    parameterPositive) minimum
  ⟨endpoint, tolerance, rfl, request, max prepared.request.coordinate.rightIndex request.stage, rfl⟩

end Chart

set_option genInjectivity false in
/-- The coordinate, both primitive values, and all original requests remain available to the finite polygon and its
later orientation proof. -/
structure Reading (regular : RegularBounds.Data cap) (model : UniformReciprocalRootChannels.RootModel cell)
    {comparison : ArcSamples.Data regular cell}
    (sample : ArcSamples.Sample comparison capSample) (parameter target : InverseRootPolynomial.Coordinate) (floor stage
      : Nat) where
  /-- The retained original vertex preparation and its pre-polynomial request. -/ prepared :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared regular model parameter target floor
  /-- The original independent chart-reading floor. -/ minimum : Nat
  /-- The retained chart request using this exact original vertex preparation and cap polynomial. -/ chart :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Chart prepared capSample minimum
  /-- The actual cached original endpoint root-coordinate reading. -/ root : ChartReadings.Endpoint.Reading
    chart.endpoint stage
  /-- The cached intrinsic reciprocal coordinate polynomial evaluation. -/ coordinateValue :
    InverseRootPolynomial.Gaussian
  /-- The intrinsic coordinate uses the original radicand and the retained local and shared inverse polynomial values.
  -/
  coordinate_eq : coordinateValue = (HyperellipticReciprocal.polynomial curve).eval (parent.edge.point parameter)⁻¹
    *
    sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹ * capSample.inverse.value.eval (parent.edge.point
      parameter)⁻¹
  /-- The cached coordinate polynomial approximates the actual retained root reading within the original target. -/
    coordinate_accurate : Data.Gaussian.Norm.Basic.normSq (coordinateValue - root.coordinate) < target
  /-- The cached original pullback polynomial value at the actual inverse source point. -/ sourceValue :
    InverseRootPolynomial.Gaussian
  /-- The source value is exactly the supplied retained pullback's endpoint evaluation. -/ source_eq : sourceValue =
    sample.pullback.value.eval (parent.edge.point parameter)⁻¹
  /-- The cached original regular or ramified cap primitive reading. -/ chartValue : InverseRootPolynomial.Gaussian
  /-- The chart value is the original parity-dependent cap primitive evaluated on the retained coordinate. -/ chart_eq :
    chartValue = if HyperellipticReciprocal.originOrder curve = 0 then
    root.coordinate * capSample.primitive.value.eval (parent.edge.point parameter)⁻¹
    else capSample.primitive.value.eval root.coordinate
  /-- The retained endpoint and chart primitive readings differ by less than the original target. -/ chart_accurate :
    Data.Gaussian.Norm.Basic.normSq (root.value - chartValue) < target
  /-- The original source pullback and retained chart value differ by less than four targets. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq (sourceValue - chartValue) < 4 * target
  /-- The cached original root coordinate satisfies its requested square relation. -/ square :
    Data.Gaussian.Norm.Basic.normSq (root.coordinate * root.coordinate -
    (parent.edge.point parameter)⁻¹ ^ HyperellipticReciprocal.originOrder curve) < target
  /-- The retained original root-coordinate reading is nonzero. -/ nonzero : root.coordinate ≠ 0

constructive_injectivity Reading

namespace Chart

variable {prepared : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Prepared regular model parameter
  target floor} {minimum stage : Nat}

/-- Read the original vertex root once and retain its intrinsic coordinate, source pullback, chart value and all paid
comparisons. -/
@[expose] def evaluate (chart : Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Chart prepared capSample
  minimum)
    (sample : ArcSamples.Sample comparison capSample)
    (modelLater : prepared.request.index ≤ index) (stage : Nat) (later : chart.stage ≤ stage) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Reading regular model sample parameter target floor stage
      := by
  have indices := chart.stage_eq ▸ later
  let root := ChartReadings.Endpoint.Reading.build chart.endpoint stage
  let value := chart.request.evaluate root ((Data.Nat.Order.le_max_right _ _).trans indices)
  let coordinateValue := prepared.bounds.radicand * sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹ *
    capSample.inverse.value.eval (parent.edge.point parameter)⁻¹
  have coordinateEq : coordinateValue = (HyperellipticReciprocal.polynomial curve).eval (parent.edge.point parameter)⁻¹
    *
      sample.retained.inverse.value.eval (parent.edge.point parameter)⁻¹ * capSample.inverse.value.eval
        (parent.edge.point parameter)⁻¹ := by
    dsimp only [coordinateValue]
    rw [prepared.bounds.radicand_eq]
  have coordinateAccurate : Data.Gaussian.Norm.Basic.normSq (coordinateValue - root.coordinate) < target :=
    prepared.request.coordinate_accurate sample modelLater ((Data.Nat.Order.le_max_left _ _).trans indices)
  let sourceValue := sample.pullback.value.eval (parent.edge.point parameter)⁻¹
  have sourceClose : Data.Gaussian.Norm.Basic.normSq (sourceValue - root.value) < target := by
    rw [root.sample_eq]
    exact prepared.request.accurate sample chart.endpoint modelLater ((Data.Nat.Order.le_max_left _ _).trans indices)
  have toleranceLe : chart.tolerance ≤ target := by rw [chart.tolerance_eq]; exact Fraction.Order.Basic.min_le_left _ _
  have accurate : Data.Gaussian.Norm.Basic.normSq (sourceValue - value.value) < 4 * target :=
    (Data.Gaussian.Norm.Bounds.normSq_sub_le_via sourceValue root.value value.value).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct sourceClose (value.accurate.trans_le toleranceLe))).trans_eq (by
        ring1))
  have nonzero : root.coordinate ≠ 0 := by
    intro zero
    have bound := value.square_accurate
    rw [zero, Data.Gaussian.Basic.mul_zero, Data.Gaussian.Basic.zero_sub, Data.Gaussian.Norm.Basic.normSq_neg] at bound
    have small : chart.tolerance ≤ Data.Gaussian.Norm.Basic.normSq ((parent.edge.point parameter)⁻¹ ^
      HyperellipticReciprocal.originOrder curve) := by
      rw [chart.tolerance_eq]; exact Fraction.Order.Basic.min_le_right _ _
    exact lt_irrefl _ (bound.trans_le small)
  exact ⟨prepared, minimum, chart, root, coordinateValue, coordinateEq, coordinateAccurate, sourceValue, rfl,
    value.value, value.value_eq, value.accurate.trans_le toleranceLe, accurate,
    value.square_accurate.trans_le toleranceLe, nonzero⟩

end Chart

namespace Reading

variable {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample} {stage :
  Nat}

/-- For an odd-degree original curve, the retained chart reading is the cap primitive at its actual root coordinate. -/
theorem odd_value (reading : Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests.Reading regular model sample
  parameter target floor stage)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    reading.chartValue = capSample.primitive.value.eval reading.root.coordinate := by
  have balance := HyperellipticReciprocal.degree_balance curve
  rw [degree] at balance
  have branch : HyperellipticReciprocal.originOrder curve = 1 := by omega
  have retained := reading.chart_eq
  rewrite [branch, if_neg (by decide : ¬ (1 : Nat) = 0)] at retained
  exact retained

end Reading
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.VertexRequests
