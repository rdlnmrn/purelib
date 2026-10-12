module
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Sequence.Arithmetic.Product
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Approximation.CoherentEvaluation
import Purelib.Polynomial.Approximation.Evaluation
import Purelib.Polynomial.Approximation.Gaussian.Evaluation.Horner

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.RootContinuation.SquareRootProvenance
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Endpoints
import Init.ByCases
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

public section

/-!
# Cached root coordinates and polynomial readings on the actual inverse boundary

The direct endpoint reader retains its rational root coordinate. A subsequent
chart reading evaluates the shared cap polynomial at that same cached value.
Operational square and primitive identities choose a sufficient common stage;
rational readings are never asserted to be exact square roots.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Geometric

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates

open Purelib.Polynomial.Approximation

open Purelib.Polynomial.Approximation.Gaussian.Evaluation

open Purelib.Riemann.Normalization

open Purelib.Riemann.RootContinuation

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap (Endpoint chartPrimitive)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Approximation.Gaussian.Geometric (GeometricApproximation)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent Equivalent Comparison)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed.Coherence (exact)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {point :
    Purelib.Riemann.Normalization.InverseRootPolynomial.Gaussian}
  {owner : Purelib.Riemann.Topology.SquareRootContinuationChain.Owner
    ((Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.polynomial curve).eval point)}
  {overlap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap cap point owner} {differential :
    Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus} {index : Nat} {box :
    Purelib.Geometry.Rational.Box}
  {sample : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

namespace Endpoint

set_option genInjectivity false in
/-- A cached rational coordinate reading and its endpoint value at one retained stage.

The value uses the original endpoint coefficient and preserves the exact sampled coordinate rather than claiming an
exact root. -/
structure Reading (endpoint : Overlap.Endpoint overlap sample) (stage : Nat) where
  /-- The cached rational reading of the original prepared quotient coordinate. -/ coordinate :
    InverseRootPolynomial.Gaussian
  /-- The cached coordinate is the exact original channel sample at the retained stage. -/ coordinate_eq : coordinate =
    (Sampling.approximation overlap.coordinate.prepared.denominator.name).sample stage
  /-- The cached value computed from the original retained coordinate reading. -/ value : InverseRootPolynomial.Gaussian
  /-- The cached endpoint value is the retained coordinate reading times the original endpoint coefficient. -/ value_eq
    : value = coordinate * endpoint.coefficient

constructive_injectivity Reading

namespace Reading

/-- Cache one coordinate-channel reading and its endpoint value.

The value multiplies that exact retained reading by the endpoint coefficient,
without replacing or reacquiring its quotient-coordinate channel. -/
@[expose] def build (endpoint : Overlap.Endpoint overlap sample) (stage : Nat) :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading endpoint stage :=
  let coordinate := (Sampling.approximation overlap.coordinate.prepared.denominator.name).sample stage
  ⟨coordinate, rfl, coordinate * endpoint.coefficient, rfl⟩

/-- The cached direct reading equals the original endpoint approximation at the same stage. -/
theorem sample_eq {endpoint : Overlap.Endpoint overlap sample} {stage : Nat} (reading :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading endpoint stage) :
    reading.value = endpoint.approximation.sample stage := by
  rw [reading.value_eq, reading.coordinate_eq, endpoint.sample_eq]

end Reading
end Endpoint

/-- Approximate the cap primitive on its retained quotient channel.

The reciprocal-origin parity selects multiplication by the fixed exact value
or evaluation of the same cached primitive polynomial at the channel. -/
@[expose] def chartApproximation (overlap : Coordinates.Overlap cap point owner)
    (sample : Primitives.Sample cap differential index box) : GeometricApproximation :=
  let coordinate := GeometricApproximation.ofNamed overlap.coordinate.prepared.denominator.name
  if HyperellipticReciprocal.originOrder curve = 0 then
    coordinate.mul (.exact (sample.primitive.value.eval point))
  else Evaluation.evaluate sample.primitive.value coordinate

/-- The chart approximation agrees operationally with the cap primitive.

Each reciprocal-origin branch transports the retained coordinate channel
through the corresponding multiplication or polynomial evaluation. -/
@[expose] def chartApproximation_agrees (overlap : Coordinates.Overlap cap point owner)
    (sample : Primitives.Sample cap differential index box) :
    Gaussian.Equivalence.NamedEquivalent (overlap.chartPrimitive sample).name
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.chartApproximation overlap
      sample).toApproximation.toNamed := by
  by_cases regular : HyperellipticReciprocal.originOrder curve = 0
  · rw [Overlap.chartPrimitive, chartApproximation]
    rw [if_pos regular, if_pos regular]
    exact CoherentEvaluation.mul_agrees overlap.coordinate.prepared.denominator
      (Horner.polynomialEval sample.primitive.value (Coherence.exact point))
      (.ofNamed overlap.coordinate.prepared.denominator.name) (.exact (sample.primitive.value.eval point))
      (CoherentEvaluation.named_agrees overlap.coordinate.prepared.denominator)
      ((Horner.polynomialEval_exact sample.primitive.value point).trans
        (CoherentEvaluation.exact_agrees _))
  · rw [Overlap.chartPrimitive, chartApproximation]
    rw [if_neg regular, if_neg regular]
    exact CoherentEvaluation.evaluate_agrees sample.primitive.value overlap.coordinate.prepared.denominator
      (.ofNamed overlap.coordinate.prepared.denominator.name) (CoherentEvaluation.named_agrees _)

set_option genInjectivity false in
/-- Retain the chart and coordinate-square comparisons at one shared stage.

The request stores each comparison and selects the maximum of its three
reading indices, preserving the direct endpoint and supplied error target. -/
structure ChartRequest (endpoint : Overlap.Endpoint overlap sample) (target : InverseRootPolynomial.Coordinate) (floor :
  Nat) where
  /-- The requested chart and coordinate-square error target is strictly positive. -/ positive : 0 < target
  /-- The retained geometric approximation to the original chart primitive. -/ chart :
    Gaussian.Geometric.GeometricApproximation
  /-- The retained chart is exactly the approximation built from the original overlap and sample. -/ chart_eq : chart =
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.chartApproximation overlap sample
  /-- The retained direct-endpoint versus chart comparison with independent reading floors. -/ comparison :
    Gaussian.Equivalence.Comparison endpoint.approximation chart.toApproximation floor floor target
  /-- The retained comparison of the original coordinate square with its exact reciprocal-origin power. -/ square :
    Gaussian.Equivalence.Comparison (Gaussian.Sequence.Arithmetic.Product.sampledProductApproximation
    overlap.coordinate.prepared.denominator.name overlap.coordinate.prepared.denominator.name)
    (Sampling.approximation (Coherence.exact (point ^ HyperellipticReciprocal.originOrder curve)).name) floor 0 target
  /-- The shared reading stage paying the chart and coordinate-square comparisons. -/ stage : Nat
  /-- The retained stage is the maximum of the three original comparison reading indices. -/ stage_eq : stage = max
    comparison.leftIndex (max comparison.rightIndex square.leftIndex)

constructive_injectivity ChartRequest

namespace ChartRequest

variable {endpoint : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Coordinates.Overlap.Endpoint overlap sample}
  {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Construct a chart request from the endpoint and positive target.

The two operational comparisons retain their separate reading floors and
indices; their maximum supplies the shared coordinate-reading stage. -/
@[expose] def build (endpoint : Overlap.Endpoint overlap sample) (target : InverseRootPolynomial.Coordinate) (positive :
  0 < target) (floor : Nat) :
    Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.ChartRequest endpoint target floor :=
  let chart := Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.chartApproximation overlap sample
  let agrees : Gaussian.Equivalence.Equivalent endpoint.approximation chart.toApproximation :=
    endpoint.sampled_agreement.symm.trans (Equivalent.trans
      (Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.chartApproximation_agrees overlap sample)
      (Equivalent.toNamed_sampling chart.toApproximation))
  let comparison := agrees.compare floor floor target positive
  let square := (SquareRootProvenance.sampled_square overlap.coordinate.square).compare floor 0 target positive
  ⟨positive, chart, rfl, comparison, square, max comparison.leftIndex (max comparison.rightIndex square.leftIndex), rfl⟩

/-- The shared coordinate-reading stage respects the requested floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.ChartRequest endpoint target
  floor) : floor ≤ request.stage := by
  rw [request.stage_eq]
  exact request.comparison.left_ge.trans (Data.Nat.Order.le_max_left _ _)

set_option genInjectivity false in
/-- Retain a chart evaluation on an existing endpoint reading.

The computed chart value and both error certificates use that same cached
coordinate and the request's target, without acquiring another root reading. -/
structure Evaluation (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.ChartRequest endpoint target
  floor) {stage : Nat} (reading : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading endpoint
  stage) where
  /-- The cached value computed from the original retained coordinate reading. -/ value : InverseRootPolynomial.Gaussian
  /-- The cached chart value is the parity-dependent original primitive evaluation on the retained reading. -/ value_eq
    : value = if HyperellipticReciprocal.originOrder curve = 0 then reading.coordinate * sample.primitive.value.eval
    point
    else sample.primitive.value.eval reading.coordinate
  /-- The cached chart value differs from the retained direct endpoint reading by less than the requested squared-norm
    target. -/ accurate : Data.Gaussian.Norm.Basic.normSq (reading.value - value) < target
  /-- The same retained coordinate reading squares within the requested error of the exact reciprocal-origin power. -/
    square_accurate : Data.Gaussian.Norm.Basic.normSq (reading.coordinate * reading.coordinate - point ^
    HyperellipticReciprocal.originOrder curve) < target

constructive_injectivity Evaluation

/-- Evaluate the cap polynomial on the retained coordinate reading.

A stage beyond the request's shared maximum supplies the chart and square
comparison certificates at the same supplied error target. -/
@[expose] def evaluate (request : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.ChartRequest endpoint target
  floor) {stage : Nat} (reading : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.Endpoint.Reading endpoint
  stage)
    (later : request.stage ≤ stage) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings.ChartRequest.Evaluation
      request reading := by
  let value := if HyperellipticReciprocal.originOrder curve = 0 then reading.coordinate * sample.primitive.value.eval
    point
    else sample.primitive.value.eval reading.coordinate
  have valueSample : value = request.chart.sample stage := by
    rw [request.chart_eq]
    dsimp only [value]
    rw [reading.coordinate_eq]
    by_cases regular : HyperellipticReciprocal.originOrder curve = 0
    · rw [chartApproximation]
      rw [if_pos regular, if_pos regular, Gaussian.Geometric.GeometricApproximation.mul_sample,
        Gaussian.Geometric.GeometricApproximation.ofNamed_sample,
        Gaussian.Geometric.GeometricApproximation.exact_sample]
    · rw [chartApproximation]
      rw [if_neg regular, if_neg regular, Purelib.Polynomial.Approximation.Evaluation.evaluate_sample,
        Gaussian.Geometric.GeometricApproximation.ofNamed_sample]
  have indices := request.stage_eq ▸ later
  have accurate : Data.Gaussian.Norm.Basic.normSq (reading.value - value) < target := by
    rw [reading.sample_eq, valueSample]
    exact request.comparison.close ((Data.Nat.Order.le_max_left _ _).trans indices)
      ((Data.Nat.Order.le_max_left _ _).trans ((Data.Nat.Order.le_max_right _ _).trans indices))
  have squareAccurate : Data.Gaussian.Norm.Basic.normSq (reading.coordinate * reading.coordinate - point ^
    HyperellipticReciprocal.originOrder curve) < target := by
    rw [reading.coordinate_eq]
    exact request.square.close ((Data.Nat.Order.le_max_right _ _).trans ((Data.Nat.Order.le_max_right _ _).trans
      indices)) le_rfl
  exact ⟨value, rfl, accurate, squareAccurate⟩

end ChartRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartReadings
