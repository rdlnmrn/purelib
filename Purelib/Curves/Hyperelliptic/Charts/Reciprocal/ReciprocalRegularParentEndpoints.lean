module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAdjacency
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartAreas
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartSources
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartPaths
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedBoundaryEndpoints

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedChartTrace

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularChartEdges

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

public section

/-! Requested endpoint increments for the regular parent chart bank.
The same cap samples and retained endpoint owners determine the budget. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg normSq_mul normSq_neg)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest (Request)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts (ChartBankRequest ChartParent)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentTrace (EndpointJoin)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}
  {parents : List (Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
  {target requested : Coordinate} {minimum depth : Nat}
  {original : Request regular other parents
    target minimum}
  {request : ChartBankRequest original depth
    requested}

/-- The original named coordinate approximation at the retained last endpoint of a parent chart. -/
@[expose] def lastCoordinateApproximation (request : PairedParentCharts.ChartBankRequest original depth requested)
    (i : Fin original.plans.length) := Sampling.approximation
  (ChartRequest.lastPoint (request.plans.get i)).coordinates.coordinate.prepared.denominator.name

/-- The original named coordinate approximation at the retained first endpoint of a parent chart. -/
@[expose] def firstCoordinateApproximation (request : PairedParentCharts.ChartBankRequest original depth requested)
    (j : Fin original.plans.length) := Sampling.approximation
  (ChartRequest.firstPoint (request.plans.get j)).coordinates.coordinate.prepared.denominator.name

/-- The actual acquired last endpoint reading from the original retained parent chart bank. -/
@[expose] def Evaluation.lastReading (evaluated : request.Evaluation) (i : Fin original.plans.length) :=
  ((evaluated.entries.get i).entries.get (PairedParentCharts.ChartParent original
    i).common.lastIndex).evaluated.chart.retained.area.evaluated.readings.get
    (Fin.last ((request.plans.get i).plans.get (PairedParentCharts.ChartParent original
      i).common.lastIndex).geometry.tail.length)

/-- The actual acquired first endpoint reading from the original retained parent chart bank. -/
@[expose] def Evaluation.firstReading (evaluated : request.Evaluation) (j : Fin original.plans.length) :=
  ((evaluated.entries.get j).entries.get (PairedParentCharts.ChartParent original
    j).common.firstIndex).evaluated.chart.retained.area.evaluated.readings.get 0

/-- The actual numerical stage of the retained last endpoint chart reading. -/
@[expose] def Evaluation.lastStage (evaluated : request.Evaluation) (i : Fin original.plans.length) :=
  ((evaluated.entries.get i).entries.get (PairedParentCharts.ChartParent original
    i).common.lastIndex).evaluated.chart.retained.area.refined.stage

/-- The actual numerical stage of the retained first endpoint chart reading. -/
@[expose] def Evaluation.firstStage (evaluated : request.Evaluation) (j : Fin original.plans.length) :=
  ((evaluated.entries.get j).entries.get (PairedParentCharts.ChartParent original
    j).common.firstIndex).evaluated.chart.retained.area.refined.stage

/-- The actual coordinate value in the retained original last endpoint reading. -/
@[expose] def Evaluation.lastCoordinate (evaluated : request.Evaluation) (i : Fin original.plans.length) : Gaussian :=
  (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastReading evaluated
    i).first.coordinate

/-- The actual coordinate value in the retained original first endpoint reading. -/
@[expose] def Evaluation.firstCoordinate (evaluated : request.Evaluation) (j : Fin original.plans.length) : Gaussian :=
  (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstReading evaluated
    j).first.coordinate

/-- The actual last endpoint coordinate is the original named approximation sampled at its retained stage. -/
theorem Evaluation.lastCoordinate_eq (evaluated : request.Evaluation) (i : Fin original.plans.length) :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastCoordinate evaluated i =
      (lastCoordinateApproximation request
      i).sample (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastStage evaluated
      i) :=
  (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastReading evaluated
    i).first.coordinate_eq

/-- The actual first endpoint coordinate is the original named approximation sampled at its retained stage. -/
theorem Evaluation.firstCoordinate_eq (evaluated : request.Evaluation) (j : Fin original.plans.length) :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstCoordinate evaluated j =
      (firstCoordinateApproximation request
      j).sample (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstStage evaluated
      j) :=
  (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstReading evaluated
    j).first.coordinate_eq

/-- At an unramified reciprocal origin, the actual last chart point is the retained endpoint coordinate multiplied by
the two shared cap primitive values. -/
theorem Evaluation.last_regular_point (evaluated : request.Evaluation) (i : Fin original.plans.length)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    (Evaluation.chartTrace (evaluated.entries.get i)).last =
      (⟨Evaluation.lastCoordinate evaluated i * evaluated.firstCap.primitive.value.eval
        ((PairedParentCharts.ChartParent original i).parent.edge.point (ChartRequest.lastParameter (request.plans.get
          i)))⁻¹,
        Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastCoordinate evaluated i *
          evaluated.otherCap.primitive.value.eval
        ((PairedParentCharts.ChartParent original i).parent.edge.point (ChartRequest.lastParameter (request.plans.get
          i)))⁻¹⟩ : Stokes.PrimitivePoint) := by
  have first := congrArg (fun sample : Primitives.Sample cap differential request.index collar.box =>
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastCoordinate evaluated i *
      sample.primitive.value.eval
      ((PairedParentCharts.ChartParent original i).parent.edge.point (ChartRequest.lastParameter (request.plans.get
        i)))⁻¹) (evaluated.shared i).1
  have second := congrArg (fun sample : Primitives.Sample cap other request.index collar.box =>
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastCoordinate evaluated i *
      sample.primitive.value.eval
      ((PairedParentCharts.ChartParent original i).parent.edge.point (ChartRequest.lastParameter (request.plans.get
        i)))⁻¹) (evaluated.shared i).2
  exact (Evaluation.chartTrace_last (evaluated.entries.get i)).trans
    ((Evaluation.regular_chartPoint
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastReading evaluated i)
      unramified).trans
      (congrArg₂ PrimitivePoint.mk first second))

/-- At an unramified reciprocal origin, the actual first chart point is the retained endpoint coordinate multiplied by
the two shared cap primitive values. -/
theorem Evaluation.first_regular_point (evaluated : request.Evaluation) (j : Fin original.plans.length)
    (unramified : HyperellipticReciprocal.originOrder curve = 0) :
    (Evaluation.chartTrace (evaluated.entries.get j)).first =
      (⟨Evaluation.firstCoordinate evaluated j * evaluated.firstCap.primitive.value.eval
        ((PairedParentCharts.ChartParent original j).parent.edge.point (ChartRequest.firstParameter (request.plans.get
          j)))⁻¹,
        Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstCoordinate evaluated j *
          evaluated.otherCap.primitive.value.eval
        ((PairedParentCharts.ChartParent original j).parent.edge.point (ChartRequest.firstParameter (request.plans.get
          j)))⁻¹⟩ : Stokes.PrimitivePoint) := by
  have first := congrArg (fun sample : Primitives.Sample cap differential request.index collar.box =>
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstCoordinate evaluated j *
      sample.primitive.value.eval
      ((PairedParentCharts.ChartParent original j).parent.edge.point (ChartRequest.firstParameter (request.plans.get
        j)))⁻¹) (evaluated.shared j).1
  have second := congrArg (fun sample : Primitives.Sample cap other request.index collar.box =>
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstCoordinate evaluated j *
      sample.primitive.value.eval
      ((PairedParentCharts.ChartParent original j).parent.edge.point (ChartRequest.firstParameter (request.plans.get
        j)))⁻¹) (evaluated.shared j).2
  exact (Evaluation.chartTrace_first (evaluated.entries.get j)).trans
    ((Evaluation.regular_chartPoint
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstReading evaluated j)
      unramified).trans
      (congrArg₂ PrimitivePoint.mk first second))

set_option genInjectivity false in
/-- The cap polynomial values are cached once at the retained last endpoint. -/
structure RegularEndpointRequest (evaluated : request.Evaluation)
    (i j : Fin original.plans.length) (joined : ReciprocalRegularParentTrace.EndpointJoin request i j)
    (error : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached first differential cap primitive value at the original last physical endpoint. -/ firstValue :
    InverseRootPolynomial.Gaussian
  /-- The first cached value reads the original shared first cap at that exact retained endpoint. -/ firstValue_eq :
    firstValue = evaluated.firstCap.primitive.value.eval
    ((PairedParentCharts.ChartParent original i).parent.edge.point (ChartRequest.lastParameter (request.plans.get i)))⁻¹
  /-- The cached second differential cap primitive value at the same original endpoint. -/ secondValue :
    InverseRootPolynomial.Gaussian
  /-- The second cached value reads the original shared second cap at that exact retained endpoint. -/ secondValue_eq :
    secondValue = evaluated.otherCap.primitive.value.eval
    ((PairedParentCharts.ChartParent original i).parent.edge.point (ChartRequest.lastParameter (request.plans.get i)))⁻¹
  /-- The retained sum of the squared norms of the two original cap values. -/ weight : InverseRootPolynomial.Coordinate
  /-- The cached weight reads those exact original first and second cap values. -/ weight_eq : weight =
    Data.Gaussian.Norm.Basic.normSq firstValue + Data.Gaussian.Norm.Basic.normSq secondValue
  /-- The retained coordinate tolerance selected from the original endpoint target and cached weight. -/ tolerance :
    InverseRootPolynomial.Coordinate
  /-- The coordinate tolerance is exactly the weighted allowance for the retained error and cap weight. -/ tolerance_eq
    : tolerance = Weighted.allowance error weight
  /-- The cached cap weight times the selected tolerance is paid by the original error target. -/ paid : weight *
    tolerance ≤ error
  /-- The actual named coordinate comparison between the two original joined endpoints, above both requested floors. -/
    comparison : Gaussian.Equivalence.Comparison
    (lastCoordinateApproximation request i)
      (firstCoordinateApproximation request j)
      floor floor tolerance
  /-- The cached common stage paying both sides of the retained endpoint comparison. -/ index : Nat
  /-- The retained stage is exactly the maximum of the two original comparison indices. -/ index_eq : index = max
    comparison.leftIndex comparison.rightIndex

constructive_injectivity RegularEndpointRequest

namespace RegularEndpointRequest

/-- Cache the shared cap values at the original endpoint and prepare a paid coordinate comparison using the retained
owner join. -/
@[expose] def build (evaluated : request.Evaluation) (i j : Fin original.plans.length)
    (joined : ReciprocalRegularParentTrace.EndpointJoin request i j) (error : InverseRootPolynomial.Coordinate)
      (positive : 0 < error) (floor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.RegularEndpointRequest evaluated i j joined
      error floor := by
  let firstValue := evaluated.firstCap.primitive.value.eval
    ((PairedParentCharts.ChartParent original i).parent.edge.point (ChartRequest.lastParameter (request.plans.get i)))⁻¹
  let secondValue := evaluated.otherCap.primitive.value.eval
    ((PairedParentCharts.ChartParent original i).parent.edge.point (ChartRequest.lastParameter (request.plans.get i)))⁻¹
  let weight := Data.Gaussian.Norm.Basic.normSq firstValue + Data.Gaussian.Norm.Basic.normSq
    secondValue
  have nonnegative : 0 ≤ weight := add_nonneg (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    (Data.Gaussian.Norm.Basic.normSq_nonneg _)
  let tolerance := Weighted.allowance error weight
  have tolerancePositive := Weighted.allowance_positive positive nonnegative
  let comparison := joined.coordinate.compare floor floor tolerance tolerancePositive
  exact ⟨firstValue, rfl, secondValue, rfl, weight, rfl, tolerance, rfl,
    Weighted.mul_allowance_le positive.le nonnegative,
    comparison, max comparison.leftIndex comparison.rightIndex, rfl⟩

/-- At the two paid original reading stages, the actual retained endpoint coordinates differ within the selected
tolerance. -/
theorem coordinate_accurate {evaluated : request.Evaluation} {i j : Fin original.plans.length}
    {joined : ReciprocalRegularParentTrace.EndpointJoin request i j} {error : InverseRootPolynomial.Coordinate} {floor :
      Nat}
    (planned : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.RegularEndpointRequest evaluated
      i j joined error floor)
    (leftLater : planned.index ≤
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastStage evaluated i)
      (rightLater : planned.index ≤
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstStage evaluated j) :
    Data.Gaussian.Norm.Basic.normSq
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstCoordinate evaluated j -
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastCoordinate evaluated i) ≤
      planned.tolerance := by
  have reverse (a b : InverseRootPolynomial.Gaussian) : Data.Gaussian.Norm.Basic.normSq (b - a) =
    Data.Gaussian.Norm.Basic.normSq (a - b) := by
    rw [show b - a = -(a - b) by ring1, Data.Gaussian.Norm.Basic.normSq_neg]
  have equal := congrArg₂ (fun a b : InverseRootPolynomial.Gaussian => Data.Gaussian.Norm.Basic.normSq (a - b))
    (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstCoordinate_eq evaluated j)
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastCoordinate_eq evaluated i)
  exact equal.trans_le ((reverse _ _).trans_le (planned.comparison.close
    ((Purelib.Data.Nat.Order.le_max_left _ _).trans (planned.index_eq.ge.trans leftLater))
    ((Purelib.Data.Nat.Order.le_max_right _ _).trans (planned.index_eq.ge.trans rightLater))).le)

/-- Apply the preselected comparison to the literal cached chart endpoints. -/
theorem accurate {evaluated : request.Evaluation} {i j : Fin original.plans.length}
    {joined : ReciprocalRegularParentTrace.EndpointJoin request i j} {error : InverseRootPolynomial.Coordinate} {floor :
      Nat}
    (planned : Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.RegularEndpointRequest evaluated
      i j joined error floor)
    (unramified : HyperellipticReciprocal.originOrder curve = 0)
    (leftLater : planned.index ≤
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastStage evaluated i)
      (rightLater : planned.index ≤
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstStage evaluated j) :
    PrimitivePoint.Bounded
      ((Evaluation.chartTrace (evaluated.entries.get j)).first.sub
        (Evaluation.chartTrace (evaluated.entries.get i)).last) error := by
  have close := planned.coordinate_accurate leftLater rightLater
  have firstLe : Data.Gaussian.Norm.Basic.normSq planned.firstValue ≤ planned.weight :=
    (le_add_of_nonneg_right (Data.Gaussian.Norm.Basic.normSq_nonneg planned.secondValue)).trans_eq
      planned.weight_eq.symm
  have secondLe : Data.Gaussian.Norm.Basic.normSq planned.secondValue ≤ planned.weight :=
    (le_add_of_nonneg_left (Data.Gaussian.Norm.Basic.normSq_nonneg planned.firstValue)).trans_eq planned.weight_eq.symm
  have scalar (value : InverseRootPolynomial.Gaussian) (bounded : Data.Gaussian.Norm.Basic.normSq value ≤
    planned.weight) :
      Data.Gaussian.Norm.Basic.normSq
        (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstCoordinate evaluated j
        * value - Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastCoordinate
        evaluated i * value) ≤ error := by
    rw [show Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstCoordinate
      evaluated j * value -
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastCoordinate evaluated i *
      value =
      (Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstCoordinate evaluated j -
        Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastCoordinate evaluated i) *
        value by ring1, Data.Gaussian.Norm.Basic.normSq_mul]
    exact ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded (Data.Gaussian.Norm.Basic.normSq_nonneg
      _)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct close
        ((Data.Gaussian.Norm.Basic.normSq_nonneg planned.firstValue).trans firstLe))).trans
      ((show planned.tolerance * planned.weight = planned.weight * planned.tolerance by ring1).trans_le planned.paid)
  have firstSame : evaluated.firstCap.primitive.value.eval
      ((PairedParentCharts.ChartParent original j).parent.edge.point (ChartRequest.firstParameter (request.plans.get
        j)))⁻¹ = planned.firstValue :=
    (congrArg (fun point : InverseRootPolynomial.Gaussian => evaluated.firstCap.primitive.value.eval point⁻¹)
      joined.point_eq.symm).trans
      planned.firstValue_eq.symm
  have secondSame : evaluated.otherCap.primitive.value.eval
      ((PairedParentCharts.ChartParent original j).parent.edge.point (ChartRequest.firstParameter (request.plans.get
        j)))⁻¹ = planned.secondValue :=
    (congrArg (fun point : InverseRootPolynomial.Gaussian => evaluated.otherCap.primitive.value.eval point⁻¹)
      joined.point_eq.symm).trans
      planned.secondValue_eq.symm
  have firstRead :=
    Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.first_regular_point evaluated j
    unramified
  have lastRead := Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.last_regular_point
    evaluated i unramified
  rw [firstSame, secondSame] at firstRead
  rw [← planned.firstValue_eq, ← planned.secondValue_eq] at lastRead
  have same := congrArg₂ PrimitivePoint.sub firstRead lastRead
  have firstBound := scalar planned.firstValue firstLe
  have secondBound := scalar planned.secondValue secondLe
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at firstBound secondBound
  exact same.symm ▸ (show PrimitivePoint.Bounded
    (PrimitivePoint.sub
    ⟨Evaluation.firstCoordinate evaluated j * planned.firstValue,
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.firstCoordinate evaluated j *
      planned.secondValue⟩
    ⟨Evaluation.lastCoordinate evaluated i * planned.firstValue,
      Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints.Evaluation.lastCoordinate evaluated i *
      planned.secondValue⟩) error from
      ⟨firstBound, secondBound⟩)

end RegularEndpointRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentEndpoints
