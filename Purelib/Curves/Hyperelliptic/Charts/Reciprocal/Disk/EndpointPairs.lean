module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Inverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
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
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

public section

/-!
# Requested increments between the actual cap endpoints

Both point budgets are prepared from the owners already retained by the
cell. One shared polynomial stage and one common coordinate-reading stage
suffice. Evaluation caches both primitive coefficients, both readings and
their difference, and certifies the error against the retained arc increment.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcOwners (Endpoints)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointComparison (Data Request)

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

set_option genInjectivity false in
/-- The comparison bounds retained for both original endpoint owners of one reciprocal cell.

The original endpoint owners, cached readings and polynomial and coordinate stage floors remain explicit in the paired
certificate. -/
structure PairData (regular : RegularBounds.Data cap) (owners : Endpoints cap cell) where
  /-- The retained original first endpoint bounds, request or cached endpoint. -/ first : EndpointComparison.Data
    regular owners.first
  /-- The retained original last endpoint bounds, request or cached endpoint. -/ last : EndpointComparison.Data regular
    owners.last

constructive_injectivity PairData

/-- Cache comparison bounds for the two endpoint owners already retained by the original reciprocal cell. -/
@[expose] def PairData.build (regular : RegularBounds.Data cap) (owners : Endpoints cap cell) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairData regular owners :=
  ⟨Data.build regular owners.first, EndpointComparison.Data.build regular owners.last⟩

set_option genInjectivity false in
/-- Paired original endpoint budgets with one common polynomial stage and an independent common coordinate-reading
stage.

Each endpoint keeps its own quarter-budget request and exact original root-coordinate owner. -/
structure PairRequest (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairData regular owners) (target
  : InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The retained original first endpoint bounds, request or cached endpoint. -/ first : EndpointComparison.Request
    data.first (target / 4) floor
  /-- The retained original last endpoint bounds, request or cached endpoint. -/ last : EndpointComparison.Request
    data.last (target / 4) floor
  /-- The common retained polynomial comparison stage. -/ index : Nat
  /-- The polynomial stage is the maximum of the two original endpoint request stages. -/ index_eq : index = max
    first.index last.index
  /-- The independent retained common coordinate-reading stage. -/ readingIndex : Nat
  /-- The coordinate stage is the maximum of the two original endpoint coordinate floors. -/ readingIndex_eq :
    readingIndex = max first.coordinate.rightIndex last.coordinate.rightIndex

constructive_injectivity PairRequest

namespace PairRequest

/-- Pay both original endpoint quarter targets and retain their common polynomial and coordinate-reading floors. -/
@[expose] def build (data : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairData regular owners) (target :
  InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest data target floor :=
  let budget := target / 4
  have budgetPositive : 0 < budget := Fraction.Order.Field.div_pos_direct positive (by decide)
  let first := EndpointComparison.Request.build data.first budget budgetPositive floor
  let last := EndpointComparison.Request.build data.last budget budgetPositive floor
  ⟨first, last, max first.index last.index, rfl, max first.coordinate.rightIndex last.coordinate.rightIndex, rfl⟩

variable {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairData regular owners} {target :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Data regular cell}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- The retained common polynomial stage respects the original request floor.

The original endpoint owners, cached readings and polynomial and coordinate stage floors remain explicit in the paired
certificate. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest data target floor) :
  floor ≤ request.index := by
  rw [request.index_eq]
  exact request.first.floor_le.trans (Data.Nat.Order.le_max_left _ _)

set_option genInjectivity false in
/-- The two actual cached endpoint readings and their certified original arc increment.

Both polynomial and coordinate floors remain explicit, and the result preserves the supplied endpoint values literally.
-/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest data target floor)
  (sample : ArcSamples.Sample comparison capSample)
    (readingIndex : Nat) where
  /-- The supplied shared polynomial stage meets the original paired request floor. -/ model_later : request.index ≤
    index
  /-- The actual common endpoint reading stage meets the retained coordinate floor. -/ reading_later :
    request.readingIndex ≤ readingIndex
  /-- The retained original first endpoint bounds, request or cached endpoint. -/ first : Coordinates.Overlap.Endpoint
    owners.first.coordinates capSample
  /-- The retained original last endpoint bounds, request or cached endpoint. -/ last : Coordinates.Overlap.Endpoint
    owners.last.coordinates capSample
  /-- The original cached first endpoint reading at the actual common stage. -/ firstReading :
    ChartReadings.Endpoint.Reading first readingIndex
  /-- The original cached last endpoint reading at the actual common stage. -/ lastReading :
    ChartReadings.Endpoint.Reading last readingIndex
  /-- The cached last-minus-first original endpoint reading increment. -/ increment : InverseRootPolynomial.Gaussian
  /-- The cached increment is exactly the difference of the two retained endpoint values. -/ increment_eq : increment =
    lastReading.value - firstReading.value
  /-- The retained first endpoint reading meets its original quarter-budget polynomial comparison. -/ first_close :
    Data.Gaussian.Norm.Basic.normSq (sample.firstValue - firstReading.value) < target / 4
  /-- The retained last endpoint reading meets its original quarter-budget polynomial comparison. -/ last_close :
    Data.Gaussian.Norm.Basic.normSq (sample.lastValue - lastReading.value) < target / 4
  /-- The cached endpoint increment differs from the original retained arc increment by less than the full target. -/
    close : Data.Gaussian.Norm.Basic.normSq (sample.increment - increment) < target

constructive_injectivity Evaluation

namespace Evaluation

variable {request : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest data target floor}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples.Sample comparison capSample} {readingIndex :
  Nat}

/-- Read the cached value of the original first endpoint. -/
abbrev firstValue (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest.Evaluation request
  sample readingIndex) : Gaussian := evaluated.firstReading.value

/-- Read the cached value of the original last endpoint. -/
abbrev lastValue (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest.Evaluation request
  sample readingIndex) : Gaussian := evaluated.lastReading.value

/-- The cached first endpoint value is the original endpoint approximation at the retained reading stage. -/
theorem firstValue_eq (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest.Evaluation
  request sample readingIndex) :
    evaluated.firstValue = evaluated.first.approximation.sample readingIndex := evaluated.firstReading.sample_eq

/-- The cached last endpoint value is the original endpoint approximation at the retained reading stage. -/
theorem lastValue_eq (evaluated : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest.Evaluation
  request sample readingIndex) :
    evaluated.lastValue = evaluated.last.approximation.sample readingIndex := evaluated.lastReading.sample_eq

end Evaluation

/-- Certify the existing endpoint readings without reevaluating their roots or polynomial factors. Both original cached
values are preserved literally.

The original endpoint owners, cached readings and polynomial and coordinate stage floors remain explicit in the paired
certificate. -/
@[expose] def evaluateWithReadings (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest data
  target floor) (sample : ArcSamples.Sample comparison capSample)
    {first : Coordinates.Overlap.Endpoint owners.first.coordinates capSample}
    {last : Coordinates.Overlap.Endpoint owners.last.coordinates capSample} {readingIndex : Nat}
    (firstReading : ChartReadings.Endpoint.Reading first readingIndex)
    (lastReading : ChartReadings.Endpoint.Reading last readingIndex)
    (later : request.index ≤ index) (readingLater : request.readingIndex ≤ readingIndex) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest.Evaluation request sample readingIndex := by
  have indices := later
  rw [request.index_eq] at indices
  have readingIndices := readingLater
  rw [request.readingIndex_eq] at readingIndices
  have firstClose : Data.Gaussian.Norm.Basic.normSq (sample.firstValue - firstReading.value) < target / 4 := by
    rw [sample.firstValue_eq, firstReading.sample_eq]
    exact request.first.accurate sample first ((Data.Nat.Order.le_max_left _ _).trans indices)
      ((Data.Nat.Order.le_max_left _ _).trans readingIndices)
  have lastClose : Data.Gaussian.Norm.Basic.normSq (sample.lastValue - lastReading.value) < target / 4 := by
    rw [sample.lastValue_eq, lastReading.sample_eq]
    exact request.last.accurate sample last ((Data.Nat.Order.le_max_right _ _).trans indices)
      ((Data.Nat.Order.le_max_right _ _).trans readingIndices)
  refine ⟨later, readingLater, first, last, firstReading, lastReading, lastReading.value - firstReading.value, rfl,
    firstClose, lastClose, ?_⟩
  rw [sample.increment_eq, show sample.lastValue - sample.firstValue - (lastReading.value - firstReading.value) =
    (sample.lastValue - lastReading.value) - (sample.firstValue - firstReading.value) by ring1]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    ((Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct lastClose firstClose)).trans_eq (by
        rw [show 2 * (target / 4 + target / 4) = target / 4 * 4 by ring1]
        exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

/-- Evaluate each supplied endpoint once, then use the same certificate constructor as clients that already retain both
readings. -/
@[expose] def evaluateWithEndpoints (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest
  data target floor) (sample : ArcSamples.Sample comparison capSample)
    (first : Coordinates.Overlap.Endpoint owners.first.coordinates capSample)
    (last : Coordinates.Overlap.Endpoint owners.last.coordinates capSample)
    (later : request.index ≤ index) (readingIndex : Nat) (readingLater : request.readingIndex ≤ readingIndex) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest.Evaluation request sample readingIndex :=
  request.evaluateWithReadings sample
    (ChartReadings.Endpoint.Reading.build first readingIndex)
    (ChartReadings.Endpoint.Reading.build last readingIndex) later readingLater

/-- The standalone acquisition uses the same cache-preserving endpoint evaluator. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest data target
  floor) (sample : ArcSamples.Sample comparison capSample)
    (later : request.index ≤ index) (readingIndex : Nat) (readingLater : request.readingIndex ≤ readingIndex) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs.PairRequest.Evaluation request sample readingIndex :=
  request.evaluateWithEndpoints sample
    (Coordinates.Overlap.Endpoint.build owners.first.coordinates capSample)
    (Coordinates.Overlap.Endpoint.build owners.last.coordinates capSample)
    later readingIndex readingLater

end PairRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.EndpointPairs
