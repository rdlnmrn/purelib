module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.ContinuedInverseRootRequests
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Tactic.Ring

public section

/-!
# Requested cap primitive increments on retained local segments

Both endpoint owners are continued from the actual terminal neighborhood.
Their cap-coordinate comparisons and the whole-segment derivative estimate
use one shared polynomial stage. The endpoint readings may advance
independently. Every endpoint factor and local model is retained for reuse.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison

open Purelib
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
open Purelib.Data.Rat
open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels (Terminal)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {point :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)} {count :
    Nat}
  {terminal : Terminal cap owner count} {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential
    genus}
  {comparison : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.Data terminal differential}

set_option genInjectivity false in
/-- Prepare the two actual continued endpoint occurrences once, before selecting a polynomial stage or materializing any
refined polynomial. -/
structure Data (segment : TerminalComparison.LocalSegment comparison) where
  /-- The retained first endpoint occurrence and its exact original coordinate data. -/ first :
    EndpointComparison.PreparedPoint comparison segment.comparison.first
  /-- The retained last endpoint occurrence and its exact original coordinate data. -/ last :
    EndpointComparison.PreparedPoint comparison segment.comparison.last

constructive_injectivity Data

namespace Data

/-- Prepare the two original continued endpoint occurrences of the retained local segment once. -/
@[expose] public def build (segment : TerminalComparison.LocalSegment comparison) :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Data segment :=
  ⟨EndpointComparison.PreparedPoint.build comparison segment.comparison.first segment.firstInside
    segment.comparison.firstCap,
    EndpointComparison.PreparedPoint.build comparison segment.comparison.last segment.lastInside
      segment.comparison.lastCap⟩

end Data

variable {segment : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison.LocalSegment comparison}

set_option genInjectivity false in
/-- Pay the interior comparison and both endpoint comparisons in one request. All three certified model floors
contribute to the shared index. -/
structure Request (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Data segment) (target :
  InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The requested local increment error target is strictly positive. -/ positive : 0 < target
  /-- The cached quarter target shared by the interior and combined endpoint comparisons. -/ budget :
    InverseRootPolynomial.Coordinate
  /-- The cached comparison budget is one quarter of the requested target. -/ budget_eq : budget = target / 4
  /-- The cached error target for each retained endpoint comparison. -/ endpointTarget :
    InverseRootPolynomial.Coordinate
  /-- Each endpoint receives one quarter of the retained comparison budget. -/ endpointTarget_eq : endpointTarget =
    budget / 4
  /-- The retained first endpoint request at its paid error target and original reading floor. -/ first :
    EndpointComparison.Request data.first.data endpointTarget floor
  /-- The retained last endpoint request at its paid error target and original reading floor. -/ last :
    EndpointComparison.Request data.last.data endpointTarget floor
  /-- The retained whole-segment comparison request on the original local segment. -/ interior : Segment.Request
    segment.comparison budget floor
  /-- The shared polynomial stage paying both endpoints and the interior comparison. -/ index : Nat
  /-- The retained stage is the maximum of the three original comparison floors. -/ index_eq : index = max (max
    first.index last.index) interior.index

constructive_injectivity Request

namespace Request

/-- Pay both original endpoint comparisons and the interior comparison at a shared polynomial stage. -/
@[expose] public def build (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Data segment) (target
  : InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Request data target floor :=
  let budget := target / 4
  have budgetPositive : 0 < budget := Fraction.Order.Field.div_pos_direct positive (by decide)
  let endpointTarget := budget / 4
  have endpointPositive : 0 < endpointTarget := Fraction.Order.Field.div_pos_direct budgetPositive (by decide)
  let first := EndpointComparison.Request.build data.first.data endpointTarget endpointPositive floor
  let last := EndpointComparison.Request.build data.last.data endpointTarget endpointPositive floor
  let interior := segment.request budget budgetPositive floor
  ⟨positive, budget, rfl, endpointTarget, rfl, first, last, interior, max (max first.index last.index) interior.index,
    rfl⟩

variable {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Data segment} {target :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The shared polynomial stage respects the requested floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Request data target floor) :
  floor ≤ request.index := by
  rw [request.index_eq]
  exact request.interior.floor_le.trans (Purelib.Data.Nat.Order.le_max_right _ _)

/-- The first retained coordinate-reading stage respects the requested floor. -/
theorem first_floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Request data target
  floor) : floor ≤ request.first.coordinate.rightIndex :=
  request.first.coordinate.right_ge

/-- The last retained coordinate-reading stage respects the requested floor. -/
theorem last_floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Request data target
  floor) : floor ≤ request.last.coordinate.rightIndex :=
  request.last.coordinate.right_ge

end Request

variable {index : Nat} {box : Purelib.Geometry.Rational.Box}

set_option genInjectivity false in
/-- One retained local primitive and comparison model, together with both cached cap polynomial endpoint factors at the
same shared cap stage. -/
structure Sample (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Data segment) (capSample :
  Primitives.Sample cap differential index box) where
  /-- The retained local primitive and comparison model at the shared cap sample stage. -/ retained :
    TerminalComparison.Sample comparison capSample
  /-- The cached primitive factor and reading channel at the retained first endpoint. -/ first : Overlap.Endpoint
    data.first.coordinates capSample
  /-- The cached primitive factor and reading channel at the retained last endpoint. -/ last : Overlap.Endpoint
    data.last.coordinates capSample

constructive_injectivity Sample

namespace Sample

/-- Cache the original local comparison model and both cap endpoint factors at the supplied sample stage. -/
@[expose] public def build (data : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Data segment)
  (capSample : Primitives.Sample cap differential index box) :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Sample data capSample :=
  let retained := TerminalComparison.Sample.build comparison capSample
  ⟨retained, Endpoint.build data.first.coordinates capSample,
    Endpoint.build data.last.coordinates capSample⟩

variable {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Data segment} {capSample :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Read only the two retained root coordinates and cached rational factors. -/
@[expose] public def increment (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Sample data
  capSample) (firstIndex lastIndex : Nat) : Gaussian :=
  sample.last.approximation.sample lastIndex - sample.first.approximation.sample firstIndex

end Sample

namespace Request

variable {data : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Data segment} {capSample :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- A complete local cap increment agrees with the actual retained local primitive. The proof pays both endpoint errors
and the full segment error. -/
theorem accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Request data target floor)
  (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Sample data capSample) {firstIndex lastIndex
  : Nat}
    (later : request.index ≤ index) (firstLater : request.first.coordinate.rightIndex ≤ firstIndex)
    (lastLater : request.last.coordinate.rightIndex ≤ lastIndex) :
    Data.Gaussian.Norm.Basic.normSq (sample.increment firstIndex lastIndex -
      (sample.retained.primitive.primitive.value.eval segment.comparison.last -
        sample.retained.primitive.primitive.value.eval segment.comparison.first)) < target := by
  have indices := later
  rw [request.index_eq] at indices
  have endpoints := (Purelib.Data.Nat.Order.le_max_left _ _).trans indices
  have first := request.first.accurate sample.retained.comparison sample.first ((Purelib.Data.Nat.Order.le_max_left _
    _).trans endpoints) firstLater
  have last := request.last.accurate sample.retained.comparison sample.last ((Purelib.Data.Nat.Order.le_max_right _
    _).trans endpoints) lastLater
  have interior := sample.retained.accurate request.interior ((Purelib.Data.Nat.Order.le_max_right _ _).trans indices)
  let firstValue := sample.first.approximation.sample firstIndex
  let lastValue := sample.last.approximation.sample lastIndex
  let firstModel := sample.retained.comparison.value.eval segment.comparison.first
  let lastModel := sample.retained.comparison.value.eval segment.comparison.last
  let primitive := sample.retained.primitive.primitive.value.eval segment.comparison.last -
    sample.retained.primitive.primitive.value.eval segment.comparison.first
  have endpointError : Data.Gaussian.Norm.Basic.normSq ((lastValue - firstValue) - (lastModel - firstModel)) <
    request.budget := by
    rw [show (lastValue - firstValue) - (lastModel - firstModel) = (firstModel - firstValue) - (lastModel - lastValue)
      by ring1]
    apply (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans_lt
    apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
        decide : (0 : InverseRootPolynomial.Coordinate) < 2)
      (Fraction.Order.Arithmetic.add_lt_add_direct first last)).trans_eq
    rw [show 2 * (request.endpointTarget + request.endpointTarget) = request.endpointTarget * 4 by ring1,
      request.endpointTarget_eq]
    exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  change Data.Gaussian.Norm.Basic.normSq ((lastValue - firstValue) - primitive) < target
  rw [show (lastValue - firstValue) - primitive =
    ((lastValue - firstValue) - (lastModel - firstModel)) + ((lastModel - firstModel) - primitive) by ring1]
  apply (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
  apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
    (Fraction.Order.Arithmetic.add_lt_add_direct endpointError interior)).trans_eq
  rw [show 2 * (request.budget + request.budget) = request.budget * 4 by ring1, request.budget_eq]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- The request itself supplies usable endpoint reading indices; evaluating the increment reuses the sample's cached
factors and retained root channels. -/
@[expose] public def increment (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Request data
  target floor) (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Sample data capSample) :
  Gaussian :=
  sample.increment request.first.coordinate.rightIndex request.last.coordinate.rightIndex

/-- The retained request's own endpoint reading indices give the requested local primitive increment accuracy. -/
theorem increment_accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Request data target
  floor) (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison.Sample data capSample) (later :
  request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (request.increment sample -
      (sample.retained.primitive.primitive.value.eval segment.comparison.last -
        sample.retained.primitive.primitive.value.eval segment.comparison.first)) < target :=
  request.accurate sample later (Nat.le_refl _) (Nat.le_refl _)

end Request
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
