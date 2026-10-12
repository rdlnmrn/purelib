module
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.Nat.Order
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Approximation.Rational.Budget.Spatial
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocalCurve
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Polynomial.Dense.Derivative
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover
import Purelib.Riemann.Integration.UniformPreparedPrimitives
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Init.Prelude
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Geometric
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Apart
import Purelib.Approximation.Request.PairedFloors
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.CoordinateSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EndpointComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Owners
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.RootCoordinates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.SegmentComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalComparison
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.TerminalModels
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRootNames
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Normalization.ContinuedInverseRootRequests
import Purelib.Riemann.Normalization.InverseModelPrimitiveBounds
import Purelib.Riemann.Normalization.InverseModelRootChannels
import Purelib.Riemann.Normalization.InverseModelRootRequests
import Purelib.Riemann.Normalization.InverseModelRootSamples
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.TracedPrimitiveNeighborhood
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Tactic.Ring

public section

/-!
# Cap increments compared with actual prepared integration blocks

Negate the retained local primitive and its coefficient, preserving its
Taylor bound and inverse-model stage. The resulting positive differential
model feeds the existing prepared integrator on the original uniform patch.
The request pays both comparisons, including the reciprocal minus sign.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Budget
open Purelib.Approximation.Rational.Budget.Spatial
open Purelib.Approximation.Rational.Geometric
open Purelib.Approximation.Rational.Geometric.Basic
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration.Polynomial.Gaussian.Path.Basic
open Purelib.Polynomial
open Purelib.Polynomial.Dense
open Purelib.Polynomial.Dense.Basic
open _root_.Purelib.Polynomial.Dense.Basic renaming CoefficientPolynomial -> Dense
open Purelib.Polynomial.Dense.Gaussian.Primitive
open Purelib.Riemann.Branches
open Purelib.Riemann.Integration
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore
open Purelib.Riemann.Normalization
open Purelib.Riemann.Readings

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PathCover (Parent ParentData)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator differentialNumerator_eval)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow firstQuarterBelow_accurate)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Rational.Budget.Spatial (SpatialBudget)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectParentBlock directParentBlockAtDepth)

/-- Negate the retained coefficient and primitive while preserving the original rectangle and Taylor remainder ceiling.
-/
@[expose] public def negativePrimitive {coefficient : InverseRootPolynomial.Polynomial} {box :
  Rational.Box}
    (primitive : Certificate.DensePrimitive coefficient box) :
    Certificate.DensePrimitive (-coefficient) box where
  value := -primitive.value
  derivative_eq := fun point => by
    change (Derivative.derivative (-primitive.value)).eval point = _
    rw [Derivative.eval_derivative_neg, DensePolynomial.eval_neg]
    exact congrArg Neg.neg (primitive.derivative_eq point)
  remainderBound := primitive.remainderBound
  remainderBound_nonnegative := primitive.remainderBound_nonnegative
  increment_bound := by
    intro first last firstInside lastInside
    simp only [DensePolynomial.eval_neg]
    rw [show -primitive.value.eval last - -primitive.value.eval first -
      -coefficient.eval first * (last - first) =
        -(primitive.value.eval last - primitive.value.eval first - coefficient.eval first * (last - first)) by ring1,
      Data.Gaussian.Norm.Basic.normSq_neg]
    exact primitive.increment_bound firstInside lastInside

variable {genus : Nat} {curve : HyperellipticCurve genus} {collar :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve}
  {cap : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar} {differential :
    Differential genus} {count : Nat}
  {parent : Parent curve differential} {data : ParentData cap differential count parent}

/-- This model shares the retained primitive's coefficients and remainder budget through finite negation. No inverse
refinement or integration is repeated. -/
@[expose] public def positiveModel {index : Nat} {box : Rational.Box}
    {capSample : Primitives.Sample cap differential index box}
    (sample : PrimitiveComparison.Sample data.data capSample) :
    InverseRootPrimitive.PrimitiveModel data.terminal.neighborhood.patch index
      (PreparedPrimitiveSamples.differentialNumerator (HyperellipticReciprocal.reversedDifferential differential)) where
  coefficient := -sample.retained.primitive.coefficient
  coefficient_eq := fun point => by
    rw [DensePolynomial.eval_neg, sample.retained.primitive.coefficient_eq, data.comparison.numerator_eq,
      PreparedPrimitiveSamples.differentialNumerator_eval]
    ring1
  primitive := negativePrimitive
    sample.retained.primitive.primitive

set_option genInjectivity false in
/-- A shared cap and prepared-integral accuracy request on the original retained parent patch.

It keeps the numerator ceiling, polynomial floor and actual spatial child block, with exact equations tying each cache
to the original request. -/
structure Request (data : ParentData cap differential count parent) (target : InverseRootPolynomial.Coordinate) (floor :
  Nat) where
  /-- The original requested increment accuracy target is strictly positive. -/ positive : 0 < target
  /-- The retained quarter target shared by cap and integration comparisons. -/ budget :
    InverseRootPolynomial.Coordinate
  /-- The retained budget is exactly one quarter of the original target. -/ budget_eq : budget = target / 4
  /-- The retained original cap endpoint and segment comparison request. -/ capRequest : PrimitiveComparison.Request
    data.data budget floor
  /-- The cached finite squared-norm ceiling for the original reversed differential numerator. -/ numeratorBound :
    InverseRootPolynomial.Coordinate
  /-- The cached numerator ceiling is nonnegative. -/ numerator_nonnegative : 0 ≤ numeratorBound
  /-- The original differential numerator satisfies the cached ceiling throughout the retained neighborhood. -/
    numerator_le : ∀ point, data.terminal.neighborhood.patch.box.Contains point →
    Data.Gaussian.Norm.Basic.normSq ((PreparedPrimitiveSamples.differentialNumerator
      (HyperellipticReciprocal.reversedDifferential differential)).eval point) ≤ numeratorBound
  /-- The cached original prepared-integral root error scale. -/ scale : InverseRootPolynomial.Coordinate
  /-- The scale uses the original neighborhood, numerator ceiling and retained parent movement. -/ scale_eq : scale =
    PreparedPrimitiveRequests.rootScale (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
    data.terminal.neighborhood.patch numeratorBound
    (PreparedPrimitiveRequests.movement parent)
  /-- The selected polynomial stage paying the original integration allocation. -/ modelIndex : Nat
  /-- The model stage is the original finite geometric search with the requested floor. -/ modelIndex_eq : modelIndex =
    Search.firstQuarterBelow scale floor ((budget / 8) / 3)
  /-- The shared original polynomial stage paying both cap and integration requests. -/ index : Nat
  /-- The shared stage is the maximum of the original cap and integration floors. -/ index_eq : index = max
    capRequest.index modelIndex
  /-- The retained finite spatial budget on the original parent movement and model bounds. -/ spatial :
    Spatial.SpatialBudget (budget / 8) (PreparedPrimitiveRequests.movement parent)
    (4 * (4 * data.comparison.primitiveBounds.bound) * PreparedPrimitiveRequests.movement parent)
    (PreparedPrimitiveRequests.errorWeight (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
      data.terminal.neighborhood.patch numeratorBound (PreparedPrimitiveRequests.movement parent))
    (PreparedPrimitiveRequests.preparedScale parent) (PreparedPrimitiveRequests.denominatorLower (curve :=
      HyperellipticReciprocalCurve.reciprocalCurve curve) data.terminal.neighborhood.patch)
    (PreparedPrimitiveRequests.preparationDepth parent)
  /-- The actual original direct parent refinement block selected by the retained spatial budget. -/ block :
    PreparedDirectDyadicRefinements.DirectParentBlock parent
  /-- The retained child block has exactly the selected spatial depth. -/ block_depth : block.depth = spatial.depth
  /-- The retained child block has exactly the selected root-diameter bound. -/ block_rootDiameter : block.rootDiameter
    = spatial.rootDiameter

constructive_injectivity Request

namespace Request

/-- Select a shared cap and integration floor and retain the original paid spatial refinement block. -/
@[expose] public def build (data : ParentData cap differential count parent) (target : InverseRootPolynomial.Coordinate)
  (positive : 0 < target) (floor : Nat)
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Request data target floor :=
  let budget := target / 4
  have budgetPositive : 0 < budget := Fraction.Order.Field.div_pos_direct positive (by decide)
  let capRequest := PrimitiveComparison.Request.build data.data budget budgetPositive floor
  let numeratorBound := Dense.Gaussian.Bounds.Box.denseEvalNormBound
    (PreparedPrimitiveSamples.differentialNumerator (HyperellipticReciprocal.reversedDifferential differential))
      data.terminal.neighborhood.patch.box
  let scale := PreparedPrimitiveRequests.rootScale (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
    data.terminal.neighborhood.patch numeratorBound
    (PreparedPrimitiveRequests.movement parent)
  let modelIndex := Search.firstQuarterBelow scale floor ((budget / 8) / 3)
  have numeratorNonnegative := (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg
    (PreparedPrimitiveSamples.differentialNumerator (HyperellipticReciprocal.reversedDifferential differential))
      data.terminal.neighborhood.patch.box).1
  let spatial := SpatialBudget.acquire (budget / 8) (PreparedPrimitiveRequests.movement parent)
    (4 * (4 * data.comparison.primitiveBounds.bound) * PreparedPrimitiveRequests.movement parent)
    (PreparedPrimitiveRequests.errorWeight (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
      data.terminal.neighborhood.patch numeratorBound (PreparedPrimitiveRequests.movement parent))
    (PreparedPrimitiveRequests.preparedScale parent) (PreparedPrimitiveRequests.denominatorLower (curve :=
      HyperellipticReciprocalCurve.reciprocalCurve curve) data.terminal.neighborhood.patch)
    (PreparedPrimitiveRequests.preparationDepth parent)
    (Fraction.Order.Field.div_pos_direct budgetPositive (by decide)) (PreparedPrimitiveRequests.movement_nonnegative
      parent)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) data.comparison.primitiveBounds.bound_nonnegative))
      (PreparedPrimitiveRequests.movement_nonnegative parent))
    (PreparedPrimitiveRequests.errorWeight_nonnegative (curve := HyperellipticReciprocalCurve.reciprocalCurve curve) _
      numeratorNonnegative (PreparedPrimitiveRequests.movement_nonnegative parent))
    (PreparedPrimitiveRequests.preparedScale_nonnegative parent) (PreparedPrimitiveRequests.denominatorLower_positive
      (curve := HyperellipticReciprocalCurve.reciprocalCurve curve) _)
  let block := PreparedDirectDyadicRefinements.directParentBlockAtDepth parent proper spatial.rootDiameter
    spatial.rootDiameter_positive spatial.depth spatial.prepared_depth
  ⟨positive, budget, rfl, capRequest, numeratorBound,
    (Dense.Gaussian.Bounds.Box.denseHornerNormBounds_nonneg _ _).1,
    (fun _ inside => Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound _ inside),
    scale, rfl, modelIndex, rfl, max capRequest.index modelIndex, rfl, spatial, block, rfl, rfl⟩

variable {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The retained quarter-target comparison budget is strictly positive. -/
theorem budget_positive (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Request data target
  floor) : 0 < request.budget := by
  rw [request.budget_eq]
  exact Fraction.Order.Field.div_pos_direct request.positive (by decide)

/-- The shared cap and integration polynomial stage respects the original requested floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Request data target floor) :
  floor ≤ request.index := by
  rw [request.index_eq]
  exact request.capRequest.floor_le.trans (Purelib.Data.Nat.Order.le_max_left _ _)

/-- Every later shared polynomial stage pays the retained prepared-integral root error allocation. -/
theorem polynomial_accurate (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Request data target
  floor) {index : Nat} (later : request.index ≤ index) :
    Geometric.Basic.quarterRadius (PreparedPrimitiveRequests.rootScale (curve :=
      HyperellipticReciprocalCurve.reciprocalCurve curve) data.terminal.neighborhood.patch request.numeratorBound
      (PreparedPrimitiveRequests.movement parent)) index < (request.budget / 8) / 3 := by
  have nonnegative : 0 ≤ request.scale := by
    rw [request.scale_eq]
    exact PreparedPrimitiveRequests.rootScale_nonnegative (curve := HyperellipticReciprocalCurve.reciprocalCurve curve)
      _ request.numerator_nonnegative
      (PreparedPrimitiveRequests.movement_nonnegative parent)
  have selected : request.modelIndex ≤ index := (Purelib.Data.Nat.Order.le_max_right _ _).trans (request.index_eq ▸
    later)
  rw [← request.scale_eq]
  apply (quarterRadius_antitone nonnegative selected).trans_lt
  rw [request.modelIndex_eq]
  exact Search.firstQuarterBelow_accurate request.scale nonnegative floor _
    (Fraction.Order.Field.div_pos_direct
      (Fraction.Order.Field.div_pos_direct request.budget_positive (by decide)) (by decide))

end Request

/-- The original prepared integration block approximates its retained primitive increment under the exact
patch-neighborhood identity. -/
private theorem integral_error {target : InverseRootPolynomial.Coordinate} (patch :
  UniformPrimitiveSheetCompatibility.PreparedPatch parent)
    (neighborhood : ContinuedInverseRoot.ContinuedNeighborhood (HyperellipticReciprocal.polynomial curve) count)
    (equal : neighborhood = patch.neighborhood count)
    (request : PreparedPrimitiveRequests.Request parent neighborhood target) (positive : 0 < target)
    (finishInside : neighborhood.box.Contains (parent.edge.point 1)) :
    Data.Gaussian.Norm.Basic.normSq (request.model.primitive.value.eval (parent.edge.point 1) -
      request.model.primitive.value.eval (parent.edge.point 0) -
      (PathModel.mk (request.block.children.map CenteredEdge.model)).integralSample) < 8 * target := by
  cases equal
  have scalar := UniformPreparedPrimitives.request_integral_error_lt
    patch request positive finishInside
  rw [← Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar

set_option genInjectivity false in
/-- Retain the actual block and its integral alongside the cap endpoint reading. The exact sign equation includes
primitive constants at every point. -/
structure Sample {target : InverseRootPolynomial.Coordinate} {floor : Nat} (request :
  Request data target floor)
    {index : Nat} {box : Rational.Box} (capSample : Primitives.Sample cap differential index box) where
  /-- The cached original cap primitive comparison sample. -/ retained : PrimitiveComparison.Sample data.data capSample
  /-- The prepared-integral request consuming the same retained primitive through its exact finite negation. -/
    integration : PreparedPrimitiveRequests.Request parent data.terminal.neighborhood.patch (request.budget / 8)
  /-- The integration request reuses exactly the original retained child block. -/ block_eq : integration.block =
    request.block
  /-- The retained integration request uses exactly the supplied original cap sample stage. -/ index_eq :
    integration.index = index
  /-- At every point the retained integration primitive is the negative of the original cap comparison primitive. -/
    sign : ∀ point, integration.model.primitive.value.eval point = -retained.retained.primitive.primitive.value.eval
    point
  /-- The cached original cap endpoint increment. -/ increment : InverseRootPolynomial.Gaussian
  /-- The cached increment is exactly the original cap request applied to its retained sample. -/ increment_eq :
    increment = request.capRequest.increment retained
  /-- The cached original prepared child-block integral sample. -/ integral : InverseRootPolynomial.Gaussian
  /-- The cached integral is exactly the original retained child-block model sum. -/ integral_eq : integral =
    (PathModel.mk (integration.block.children.map CenteredEdge.model)).integralSample

constructive_injectivity Sample

namespace Sample

variable {target : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat} {request :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Request data target floor}
  {index : Nat} {box : Purelib.Geometry.Rational.Box} {capSample :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}

/-- Reuse the supplied cap sample, negate its retained primitive into the original integration request, and cache both
exact readings. -/
@[expose] public def build (request : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Request data target
  floor) (capSample : Primitives.Sample cap differential index box)
    (later : request.index ≤ index) :
    Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Sample request capSample :=
  let retained := PrimitiveComparison.Sample.build data.data capSample
  let integration : PreparedPrimitiveRequests.Request parent data.terminal.neighborhood.patch (request.budget / 8) :=
    { numeratorBound := request.numeratorBound
      numerator_nonnegative := request.numerator_nonnegative
      numerator_le := fun point inside => by
        have scalar := request.numerator_le point inside
        rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at scalar
        exact scalar
      index := index
      model := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.positiveModel retained
      polynomial_accurate := request.polynomial_accurate later
      budget := request.spatial
      block := request.block
      block_depth := request.block_depth
      block_rootDiameter := request.block_rootDiameter }
  ⟨retained, integration, rfl, rfl, (fun point => DensePolynomial.eval_neg _ point), request.capRequest.increment
    retained, rfl,
    (PathModel.mk (integration.block.children.map CenteredEdge.model)).integralSample, rfl⟩

/-- The positive prepared integral cancels the cap increment to the supplied accuracy, with the complete operational
child-block discrepancy included. -/
theorem accurate_at (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Sample request capSample)
  (later : request.index ≤ index)
    (firstIndex lastIndex : Nat)
    (firstLater : request.capRequest.first.coordinate.rightIndex ≤ firstIndex)
    (lastLater : request.capRequest.last.coordinate.rightIndex ≤ lastIndex) :
    Data.Gaussian.Norm.Basic.normSq (sample.retained.increment firstIndex lastIndex + sample.integral) < target
      := by
  let primitiveIncrement := sample.retained.retained.primitive.primitive.value.eval data.segment.comparison.last -
    sample.retained.retained.primitive.primitive.value.eval data.segment.comparison.first
  have capError : Data.Gaussian.Norm.Basic.normSq ((sample.retained.increment firstIndex lastIndex) -
    primitiveIncrement) < request.budget := by
    exact request.capRequest.accurate sample.retained ((Purelib.Data.Nat.Order.le_max_left _ _).trans (request.index_eq
      ▸ later)) firstLater lastLater
  have integrationError := Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.integral_error data.patch
    data.terminal.neighborhood.patch data.patch_eq sample.integration
    (Fraction.Order.Field.div_pos_direct request.budget_positive (by decide)) (data.last_eq ▸ data.segment.lastInside)
  rw [sample.sign, sample.sign, ← sample.integral_eq, ← data.first_eq, ← data.last_eq] at integrationError
  have integrationPaid : Data.Gaussian.Norm.Basic.normSq (primitiveIncrement + sample.integral) <
    request.budget := by
    rw [show -sample.retained.retained.primitive.primitive.value.eval data.segment.comparison.last -
      -sample.retained.retained.primitive.primitive.value.eval data.segment.comparison.first - sample.integral =
        -(primitiveIncrement + sample.integral) by dsimp only [primitiveIncrement]; ring1,
      Data.Gaussian.Norm.Basic.normSq_neg] at integrationError
    exact integrationError.trans_eq (by
      rw [Fraction.Field.mul_comm]
      exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide))
  rw [show (sample.retained.increment firstIndex lastIndex) + sample.integral =
    ((sample.retained.increment firstIndex lastIndex) - primitiveIncrement) + (primitiveIncrement + sample.integral) by
      ring1]
  apply (Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans_lt
  apply (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by
      decide : (0 : InverseRootPolynomial.Coordinate) < 2)
    (Fraction.Order.Arithmetic.add_lt_add_direct capError integrationPaid)).trans_eq
  rw [show 2 * (request.budget + request.budget) = request.budget * 4 by ring1, request.budget_eq]
  exact Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- The cached original readings remain a specialization of the same comparison, while chart consumers may advance
either endpoint independently. -/
theorem accurate (sample : Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives.Sample request capSample)
  (later : request.index ≤ index) :
    Data.Gaussian.Norm.Basic.normSq (sample.increment + sample.integral) < target := by
  rw [sample.increment_eq]
  exact sample.accurate_at later _ _ (Nat.le_refl _) (Nat.le_refl _)

end Sample
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.PreparedPrimitives
