module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.SquareRootChannelOwnership
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

public section

/-!
# Actual cap endpoint pairs in the global polynomial chart

Select the common root-reading stage before evaluating the original pair.
The original arc sample, endpoint factors and root coordinates are reused.
The new polynomial values and square residuals are certified on those exact
coordinates. In odd degree the displayed primitive is evaluated at t, not w.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointCharts

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Endpoints)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap (Endpoint)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings (ChartRequest)
open Purelib.Riemann.RootContinuation.SquareRootChannelOwnership (parameter_nonzero)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs (PairData PairRequest)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {source :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {edge : Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge} {cell :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cell source edge}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {owners : Endpoints cap cell}
  {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairData regular owners} {target :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- A shared endpoint-reading stage and separate chart tolerances for an original arc endpoint pair.

The cached endpoints preserve the original coordinate owners; each tolerance also pays the corresponding root-parameter
nonzeroness bound. -/
structure ChartPlan (request : EndpointPairs.PairRequest data target floor)
    (capSample : Primitives.Sample cap differential index box) (chartTarget : InverseRootPolynomial.Coordinate) (minimum
      : Nat) where
  /-- The cached chart endpoint on the original first coordinate owner. -/ first : Coordinates.Overlap.Endpoint
    owners.first.coordinates capSample
  /-- The cached chart endpoint on the original last coordinate owner. -/ last : Coordinates.Overlap.Endpoint
    owners.last.coordinates capSample
  /-- The cached first endpoint tolerance paying both chart accuracy and root nonzeroness. -/ firstTolerance :
    InverseRootPolynomial.Coordinate
  /-- The first tolerance is the minimum of the original chart target and first root-parameter squared norm. -/
    firstTolerance_eq : firstTolerance = min chartTarget
    (Data.Gaussian.Norm.Basic.normSq ((parent.edge.point edge.left.parameter)⁻¹ ^
      HyperellipticReciprocal.originOrder curve))
  /-- The cached last endpoint tolerance paying both chart accuracy and root nonzeroness. -/ lastTolerance :
    InverseRootPolynomial.Coordinate
  /-- The last tolerance is the minimum of the original chart target and last root-parameter squared norm. -/
    lastTolerance_eq : lastTolerance = min chartTarget
    (Data.Gaussian.Norm.Basic.normSq ((parent.edge.point edge.right.parameter)⁻¹ ^
      HyperellipticReciprocal.originOrder curve))
  /-- The paid chart request on the actual original first endpoint owner. -/ firstRequest : ChartReadings.ChartRequest
    first firstTolerance minimum
  /-- The paid chart request on the actual original last endpoint owner. -/ lastRequest : ChartReadings.ChartRequest
    last lastTolerance minimum
  /-- The retained common endpoint reading stage. -/ stage : Nat
  /-- The common stage is the maximum of the original pair floor and both chart-request stages. -/ stage_eq : stage =
    max request.readingIndex (max firstRequest.stage lastRequest.stage)

constructive_injectivity ChartPlan

namespace ChartPlan

variable {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest data target floor}
  {chartTarget : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {minimum : Nat}

/-- Cache the original pair's endpoint charts, pay their separate tolerances and retain one stage above every reading
floor.

A positive chart target and each nonzero root parameter make the retained
minimum tolerance positive. The maximum stage pays both chart requests and
the original pair requirement. -/
@[expose] def build (request : EndpointPairs.PairRequest data target floor) (capSample : Primitives.Sample cap
  differential index box)
    (chartTarget : InverseRootPolynomial.Coordinate) (positive : 0 < chartTarget) (minimum : Nat) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointCharts.ChartPlan request capSample chartTarget minimum :=
  let first := Coordinates.Overlap.Endpoint.build owners.first.coordinates capSample
  let last := Coordinates.Overlap.Endpoint.build owners.last.coordinates capSample
  let firstTolerance := min chartTarget (Data.Gaussian.Norm.Basic.normSq ((parent.edge.point
    edge.left.parameter)⁻¹ ^ HyperellipticReciprocal.originOrder curve))
  let lastTolerance := min chartTarget (Data.Gaussian.Norm.Basic.normSq ((parent.edge.point
    edge.right.parameter)⁻¹ ^ HyperellipticReciprocal.originOrder curve))
  have firstPositive := Data.Gaussian.Norm.Basic.normSq_pos (SquareRootChannelOwnership.parameter_nonzero
    owners.first.coordinates.coordinate.certificate)
  have lastPositive := Data.Gaussian.Norm.Basic.normSq_pos (SquareRootChannelOwnership.parameter_nonzero
    owners.last.coordinates.coordinate.certificate)
  let firstRequest := ChartRequest.build first firstTolerance (Fraction.Order.Basic.lt_min positive firstPositive)
    minimum
  let lastRequest := ChartRequest.build last lastTolerance (Fraction.Order.Basic.lt_min positive lastPositive) minimum
  ⟨first, last, firstTolerance, rfl, lastTolerance, rfl, firstRequest, lastRequest,
    max request.readingIndex (max firstRequest.stage lastRequest.stage), rfl⟩

set_option genInjectivity false in
/-- The original endpoint pair evaluated at its actual retained root coordinates in the shared polynomial chart.

Both values, square residuals and nonzeroness certificates are cached together with the exact increment and original arc
discrepancy. -/
structure Evaluation (plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointCharts.ChartPlan request capSample
  chartTarget minimum)
    (sample : ArcSamples.Sample comparison capSample) (stage : Nat) where
  /-- The cached evaluation of the actual original arc endpoint pair. -/ original : PairRequest.Evaluation request
    sample stage
  /-- The cached polynomial-chart value at the actual original first root reading. -/ first :
    InverseRootPolynomial.Gaussian
  /-- The cached first value uses the original reciprocal parameter in even degree and actual root coordinate in odd
    degree. -/ first_eq : first = if HyperellipticReciprocal.originOrder curve = 0 then
    original.firstReading.coordinate * capSample.primitive.value.eval (parent.edge.point edge.left.parameter)⁻¹
    else capSample.primitive.value.eval original.firstReading.coordinate
  /-- The cached polynomial-chart value at the actual original last root reading. -/ last :
    InverseRootPolynomial.Gaussian
  /-- The cached last value uses the original reciprocal parameter in even degree and actual root coordinate in odd
    degree. -/ last_eq : last = if HyperellipticReciprocal.originOrder curve = 0 then
    original.lastReading.coordinate * capSample.primitive.value.eval (parent.edge.point edge.right.parameter)⁻¹
    else capSample.primitive.value.eval original.lastReading.coordinate
  /-- The original first endpoint value is within the retained chart target of its cached chart value. -/ first_close :
    Data.Gaussian.Norm.Basic.normSq (original.firstValue - first) < chartTarget
  /-- The original last endpoint value is within the retained chart target of its cached chart value. -/ last_close :
    Data.Gaussian.Norm.Basic.normSq (original.lastValue - last) < chartTarget
  /-- The original first root-coordinate square residual satisfies the chart target. -/ first_square :
    Data.Gaussian.Norm.Basic.normSq (original.firstReading.coordinate * original.firstReading.coordinate -
    (parent.edge.point edge.left.parameter)⁻¹ ^ HyperellipticReciprocal.originOrder curve) < chartTarget
  /-- The original last root-coordinate square residual satisfies the chart target. -/ last_square :
    Data.Gaussian.Norm.Basic.normSq (original.lastReading.coordinate * original.lastReading.coordinate -
    (parent.edge.point edge.right.parameter)⁻¹ ^ HyperellipticReciprocal.originOrder curve) < chartTarget
  /-- The actual retained first root-coordinate reading is nonzero. -/ first_nonzero : original.firstReading.coordinate
    ≠ 0
  /-- The actual retained last root-coordinate reading is nonzero. -/ last_nonzero : original.lastReading.coordinate ≠ 0
  /-- The cached difference of the original endpoint chart values. -/ increment : InverseRootPolynomial.Gaussian
  /-- The cached chart increment is exactly the last value minus the first. -/ increment_eq : increment = last - first
  /-- The original endpoint-pair increment differs from the cached chart increment by less than four chart targets. -/
    increment_close : Data.Gaussian.Norm.Basic.normSq (original.increment - increment) < 4 * chartTarget
  /-- The original retained arc increment satisfies the combined pair and chart discrepancy bound. -/ arc_close :
    Data.Gaussian.Norm.Basic.normSq (sample.increment - increment) < 2 * (target + 4 * chartTarget)

constructive_injectivity Evaluation

/-- Evaluate the original endpoint pair once at the paid common stage and cache both chart values and their certified
increment.

The supplied model and reading bounds pay the same retained endpoint owners.
Their separate residual certificates prove nonzeroness and bound the original
arc discrepancy without replacing either cached coordinate. -/
@[expose] def evaluate (plan : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointCharts.ChartPlan request capSample
  chartTarget minimum)
    (sample : ArcSamples.Sample comparison capSample) (modelLater : request.index ≤ index)
    (stage : Nat) (later : plan.stage ≤ stage) :
      Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointCharts.ChartPlan.Evaluation plan sample stage := by
  have indices := plan.stage_eq ▸ later
  let original := request.evaluateWithEndpoints sample plan.first plan.last modelLater stage
    ((Data.Nat.Order.le_max_left _ _).trans indices)
  let first := plan.firstRequest.evaluate original.firstReading
    ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans indices))
  let last := plan.lastRequest.evaluate original.lastReading
    ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans indices))
  have firstLe : plan.firstTolerance ≤ chartTarget := by
    rw [plan.firstTolerance_eq];
    exact Fraction.Order.Basic.min_le_left _ _
  have lastLe : plan.lastTolerance ≤ chartTarget := by
    rw [plan.lastTolerance_eq];
    exact Fraction.Order.Basic.min_le_left _ _
  have firstAccurate := first.accurate.trans_le firstLe
  have lastAccurate := last.accurate.trans_le lastLe
  have firstNonzero := Data.Gaussian.Norm.Bounds.coordinate_nonzero first.square_accurate (by
      rw [plan.firstTolerance_eq];
      exact Fraction.Order.Basic.min_le_right _ _)
  have lastNonzero := Data.Gaussian.Norm.Bounds.coordinate_nonzero last.square_accurate (by
      rw [plan.lastTolerance_eq];
      exact Fraction.Order.Basic.min_le_right _ _)
  let increment := last.value - first.value
  have incrementClose : Data.Gaussian.Norm.Basic.normSq (original.increment - increment) < 4 * chartTarget :=
    by
    rw [original.increment_eq]
    change Data.Gaussian.Norm.Basic.normSq (original.lastReading.value - original.firstReading.value -
      (last.value - first.value)) < _
    rw [show original.lastReading.value - original.firstReading.value - (last.value - first.value) =
      (original.lastReading.value - last.value) - (original.firstReading.value - first.value) by ring1]
    exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
      ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
        (Fraction.Order.Arithmetic.add_lt_add_direct lastAccurate firstAccurate)).trans_eq (by ring1))
  have arcClose := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via sample.increment original.increment increment).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct original.close incrementClose))
  exact ⟨original, first.value, first.value_eq, last.value, last.value_eq, firstAccurate, lastAccurate,
    first.square_accurate.trans_le firstLe, last.square_accurate.trans_le lastLe,
    firstNonzero, lastNonzero, increment, rfl, incrementClose, arcClose⟩

namespace Evaluation

variable {plan : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointCharts.ChartPlan request capSample
  chartTarget minimum}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample} {stage : Nat}

/-- Odd-degree chart values use the original retained t coordinates.

The polynomial degree is twice the genus plus one, so the original degree
balance selects the odd chart branch at both retained endpoint readings. -/
theorem odd_values (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointCharts.ChartPlan.Evaluation plan
  sample stage)
    (degree : curve.polynomial.natDegree = 2 * genus + 1) :
    evaluated.first = capSample.primitive.value.eval evaluated.original.firstReading.coordinate ∧
      evaluated.last = capSample.primitive.value.eval evaluated.original.lastReading.coordinate := by
  have balance := HyperellipticReciprocal.degree_balance curve
  rw [degree] at balance
  have branch : HyperellipticReciprocal.originOrder curve = 1 := by omega
  constructor
  · have selected := evaluated.first_eq
    rw [branch, if_neg (by decide : (1 : Nat) ≠ 0)] at selected
    exact selected
  · have selected := evaluated.last_eq
    rw [branch, if_neg (by decide : (1 : Nat) ≠ 0)] at selected
    exact selected

end Evaluation
end ChartPlan
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointCharts
