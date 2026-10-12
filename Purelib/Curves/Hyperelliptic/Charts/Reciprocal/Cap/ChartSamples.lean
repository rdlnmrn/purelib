module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Polynomial.Approximation.Evaluation
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Endpoints
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootJoins
import Init.ByCases
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

public section

/-!
# Explicit rational readings of the global cap chart

Each chart sample reads the retained root coordinate once. In the odd chart
it evaluates the cached global primitive at that rational coordinate; in the
even chart it multiplies the primitive at w by the retained sheet reading.
Requests certify both the value comparison and the coordinate square residual.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Geometric
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
open Purelib.Data.Rat
open Purelib.Polynomial.Approximation
open Purelib.Polynomial.Approximation.Gaussian.Evaluation
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Topology

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent Comparison)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates (Overlap)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap (Join Endpoint chartPrimitive)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {point :
    Purelib.Data.Gaussian.Basic.Canonical}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}

/-- Evaluate the original global cap primitive through its retained coordinate channel, preserving the even sheet sign
or odd ramified coordinate. -/
@[expose] public def chartApproximation (overlap : RootCoordinates.Overlap cap point owner)
    (sample : Primitives.Sample cap differential index box) : GeometricApproximation :=
  let coordinate := GeometricApproximation.ofNamed overlap.coordinate.prepared.denominator.name
  if HyperellipticReciprocal.originOrder curve = 0 then
    coordinate.mul (.exact (sample.primitive.value.eval point))
  else Evaluation.evaluate sample.primitive.value coordinate

/-- The explicit retained chart approximation is operationally equivalent to the original cap primitive evaluator. -/
@[expose] public def chartApproximation_agrees (overlap : RootCoordinates.Overlap cap point owner)
    (sample : Primitives.Sample cap differential index box) :
    Gaussian.Equivalence.NamedEquivalent (overlap.chartPrimitive sample).name (overlap.chartApproximation
      sample).toApproximation.toNamed := by
  by_cases regular : HyperellipticReciprocal.originOrder curve = 0
  · simp only [Overlap.chartPrimitive,
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.chartApproximation, if_pos regular]
    exact CoherentEvaluation.mul_agrees overlap.coordinate.prepared.denominator
      (Horner.polynomialEval sample.primitive.value (Coherence.exact point))
      (.ofNamed overlap.coordinate.prepared.denominator.name) (.exact (sample.primitive.value.eval point))
      (CoherentEvaluation.named_agrees overlap.coordinate.prepared.denominator)
      ((Horner.polynomialEval_exact sample.primitive.value point).trans
        (CoherentEvaluation.exact_agrees _))
  · simp only [Overlap.chartPrimitive,
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.chartApproximation, if_neg regular]
    exact CoherentEvaluation.evaluate_agrees sample.primitive.value overlap.coordinate.prepared.denominator
      (.ofNamed overlap.coordinate.prepared.denominator.name) (CoherentEvaluation.named_agrees _)

/-- A retained owner join computes common-tail bounds for the actual rational chart readings, with independent starting
indices on its two patches. -/
@[expose] public def Join.readings {firstPoint lastPoint : Data.Gaussian.Basic.Canonical}
    {firstOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval firstPoint)}
    {lastOwner : SquareRootContinuationChain.Owner ((HyperellipticReciprocal.polynomial curve).eval lastPoint)}
    {first : RootCoordinates.Overlap cap firstPoint firstOwner} {last : RootCoordinates.Overlap cap lastPoint lastOwner}
    (join : Overlap.Join first last) (sample : Primitives.Sample cap differential index box) :
    Gaussian.Equivalence.Equivalent (first.chartApproximation sample).toApproximation (last.chartApproximation
      sample).toApproximation :=
  (Equivalent.toNamed_sampling (first.chartApproximation sample).toApproximation).symm.trans
    (Equivalent.trans ((first.chartApproximation_agrees sample).symm.trans
      ((join.primitive sample).trans (last.chartApproximation_agrees sample)))
      (Equivalent.toNamed_sampling (last.chartApproximation sample).toApproximation))

variable {overlap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap cap point owner} {sample
  : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

set_option genInjectivity false in
/-- Both rational values are cached, with literal coordinate and polynomial provenance. A rational coordinate reading is
not asserted to be an exact root. -/
structure ChartReading (overlap : RootCoordinates.Overlap cap point owner)
    (sample : Primitives.Sample cap differential index box) (stage : Nat) where
  /-- The cached rational reading of the original retained cap-coordinate channel. -/ coordinate :
    Data.Gaussian.Basic.Canonical
  /-- The cached coordinate equals the original retained channel's sample at this exact stage. -/ coordinate_eq :
    coordinate = (Sampling.approximation overlap.coordinate.prepared.denominator.name).sample stage
  /-- The cached rational original cap-chart primitive reading. -/ value : Data.Gaussian.Basic.Canonical
  /-- The cached value is exactly the retained coordinate times the original even-chart polynomial value, or the
    original odd-chart polynomial evaluated at that coordinate. -/ value_eq : value = if
    HyperellipticReciprocal.originOrder curve = 0 then coordinate * sample.primitive.value.eval point
    else sample.primitive.value.eval coordinate

constructive_injectivity ChartReading

namespace ChartReading

/-- Read the original retained coordinate once and cache its parity-selected original cap polynomial value. -/
@[expose] public def build (overlap : RootCoordinates.Overlap cap point owner) (sample : Primitives.Sample cap
  differential index box) (stage : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartReading overlap sample stage :=
  let coordinate := (Sampling.approximation overlap.coordinate.prepared.denominator.name).sample stage
  let value := if HyperellipticReciprocal.originOrder curve = 0 then coordinate * sample.primitive.value.eval point
    else sample.primitive.value.eval coordinate
  ⟨coordinate, rfl, value, rfl⟩

/-- The retained chart reading is exactly the original chart approximation sample at the same stage. -/
theorem value_sample {stage : Nat} (reading :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartReading overlap sample stage) :
    reading.value = (overlap.chartApproximation sample).sample stage := by
  rewrite [reading.value_eq, reading.coordinate_eq]
  by_cases regular : HyperellipticReciprocal.originOrder curve = 0
  · dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.chartApproximation]
    repeat' rewrite [if_pos regular]
    rewrite [Gaussian.Geometric.GeometricApproximation.mul_sample,
      Gaussian.Geometric.GeometricApproximation.ofNamed_sample,
      Gaussian.Geometric.GeometricApproximation.exact_sample]
    exact Eq.refl _
  · dsimp only [Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.chartApproximation]
    repeat' rewrite [if_neg regular]
    rewrite [Evaluation.evaluate_sample, Gaussian.Geometric.GeometricApproximation.ofNamed_sample]
    exact Eq.refl _

end ChartReading

set_option genInjectivity false in
/-- Abstract stream parameters keep the request independent of the concrete owner process's state representation. -/
structure ChartRequestData (source : Gaussian.Sequence.ApproximationData) (coordinate : Gaussian.Name.Basic.Named)
    (parameter : Data.Gaussian.Basic.Canonical) (expected : Gaussian.Geometric.GeometricApproximation) (target :
      Fraction.Rational) (floor : Nat) where
  /-- The original requested comparison target is strictly positive. -/ positive : 0 < target
  /-- The cached original geometric cap-chart approximation. -/ chart : Gaussian.Geometric.GeometricApproximation
  /-- The cached chart approximation is exactly the expected original evaluator. -/ chart_eq : chart = expected
  /-- The retained independent-tail comparison of the original endpoint stream with the same cached chart stream. -/
    comparison : Gaussian.Equivalence.Comparison source chart.toApproximation floor floor target
  /-- The retained independent-tail comparison of the original coordinate product stream with its exact radicand. -/
    square : Gaussian.Equivalence.Comparison (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation
    coordinate coordinate)
    (Sampling.approximation (Coherence.exact parameter).name) floor 0 target
  /-- The retained common chart stage satisfying both original comparison requests. -/ stage : Nat
  /-- The retained common chart stage is exactly the maximum of the original value and coordinate-square comparison
    stages. -/ stage_eq : stage = max comparison.rightIndex square.leftIndex

constructive_injectivity ChartRequestData

/-- The original endpoint comparison request retaining both the actual cap-chart value and coordinate square-residual
guarantees. -/
abbrev ChartRequest (endpoint : Overlap.Endpoint overlap sample) (target : Fraction.Rational) (floor : Nat) :=
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequestData endpoint.approximation
    overlap.coordinate.prepared.denominator.name
    (point ^ HyperellipticReciprocal.originOrder curve) (overlap.chartApproximation sample) target floor

namespace ChartRequest

/-- Compare the original endpoint and chart streams and select a shared stage paying both value discrepancy and
coordinate square residual. -/
@[expose] public def build (endpoint : Overlap.Endpoint overlap sample) (target : Fraction.Rational) (positive : 0 <
  target) (floor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequest endpoint target floor :=
  let chart := overlap.chartApproximation sample
  let agrees : Gaussian.Equivalence.Equivalent endpoint.approximation chart.toApproximation :=
    endpoint.sampled_agreement.symm.trans (Equivalent.trans (overlap.chartApproximation_agrees sample)
      (Equivalent.toNamed_sampling chart.toApproximation))
  let comparison := agrees.compare floor floor target positive
  let square := (SquareRootProvenance.sampled_square overlap.coordinate.square).compare floor 0 target positive
  ⟨positive, chart, rfl, comparison, square, max comparison.rightIndex square.leftIndex, rfl⟩

variable {endpoint : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.Endpoint overlap sample}
  {target : Purelib.Data.Rat.Fraction.Rational} {floor : Nat}

/-- The retained common chart stage is at least the original requested floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequest endpoint
  target floor) : floor ≤ request.stage := by
  rw [request.stage_eq]
  exact request.comparison.right_ge.trans (Purelib.Data.Nat.Order.le_max_left _ _)

/-- Later original endpoint and chart readings satisfy the retained value comparison target. -/
theorem accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequest endpoint
  target floor) {sourceStage chartStage : Nat}
    (reading : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartReading overlap sample
      chartStage) (sourceLater : request.comparison.leftIndex ≤ sourceStage)
    (chartLater : request.stage ≤ chartStage) : Data.Gaussian.Norm.Basic.normSq (endpoint.approximation.sample
      sourceStage - reading.value) < target := by
  rw [reading.value_sample, ← request.chart_eq]
  exact request.comparison.close sourceLater ((Purelib.Data.Nat.Order.le_max_left _ _).trans (request.stage_eq ▸
    chartLater))

/-- A later original coordinate reading has squared residual below the retained request target. -/
theorem square_accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequest
  endpoint target floor) {chartStage : Nat}
    (reading : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartReading overlap sample
      chartStage) (later : request.stage ≤ chartStage) :
    Data.Gaussian.Norm.Basic.normSq (reading.coordinate * reading.coordinate - point ^
      HyperellipticReciprocal.originOrder curve) < target := by
  rw [reading.coordinate_eq]
  exact request.square.close ((Purelib.Data.Nat.Order.le_max_right _ _).trans (request.stage_eq ▸ later)) (Nat.le_refl
    request.square.rightIndex)

set_option genInjectivity false in
/-- The reading index and both cached values are retained with independent certificates for the chart value and its
coordinate residual. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequest endpoint
  target floor) where
  /-- The retained chart reading stage of this original certified evaluation. -/ stage : Nat
  /-- The retained evaluation stage is at least the original certified common request stage. -/ stage_ge : request.stage
    ≤ stage
  /-- The cached original coordinate and chart value at this retained evaluation stage. -/ reading :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartReading overlap sample stage
  /-- The cached original endpoint-stream reading at its retained comparison index. -/ sourceValue :
    Data.Gaussian.Basic.Canonical
  /-- The cached endpoint source value equals its original stream sample at the retained request index. -/
    sourceValue_eq : sourceValue = endpoint.approximation.sample request.comparison.leftIndex
  /-- The cached original endpoint and chart values differ within the retained target. -/ accurate :
    Data.Gaussian.Norm.Basic.normSq (sourceValue - reading.value) < target
  /-- The cached original coordinate has squared residual within the retained target. -/ square_accurate :
    Data.Gaussian.Norm.Basic.normSq (reading.coordinate * reading.coordinate - point ^
    HyperellipticReciprocal.originOrder curve) < target

constructive_injectivity Evaluation

/-- Read and cache the original endpoint source and chart coordinate/value at the certified request stages, retaining
both value and square-residual bounds. -/
@[expose] public def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequest
  endpoint target floor) : Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequest.Evaluation
  request :=
  let reading := Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartReading.build overlap sample
    request.stage
  let sourceValue := endpoint.approximation.sample request.comparison.leftIndex
  ⟨request.stage, Nat.le_refl _, reading, sourceValue, rfl,
    request.accurate reading (Nat.le_refl _) (Nat.le_refl _), request.square_accurate reading (Nat.le_refl _)⟩

/-- Refine the chart channel while retaining the already evaluated source factor and the original certified request. -/
@[expose] public def Evaluation.refine {request :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequest endpoint target floor} (evaluated :
  Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequest.Evaluation request)
    (stage : Nat) (later : evaluated.stage ≤ stage) :
      Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartRequest.Evaluation request := by
  let reading := Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap.ChartReading.build overlap sample
    stage
  have ready := evaluated.stage_ge.trans later
  exact ⟨stage, ready, reading, evaluated.sourceValue, evaluated.sourceValue_eq,
    (by rw [evaluated.sourceValue_eq]; exact request.accurate reading (Nat.le_refl _) ready),
    request.square_accurate reading ready⟩

end ChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates.Overlap
