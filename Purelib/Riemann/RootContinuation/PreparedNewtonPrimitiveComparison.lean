module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.NewtonBandBounds
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandBank
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Riemann.Paths.PathArea
import Purelib.RootIsolation.State.Raw

import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.RootContinuation.PreparedNewtonBandArea
import Purelib.Riemann.Integration.PreparedModelAccuracy
public import Purelib.Riemann.Integration.PreparedPrimitiveResampling
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples

public section

/-!
# The same retained primitive sum and an actual Newton-boundary sample

Resampling meets the Newton coefficient-error ceiling without replacing any
primitive polynomial. The returned boundary bank reads the very same direct
blocks as the primitive comparison. Both integral and full path-area bounds
therefore apply to that comparison's actual witness, even with differing child
depths. No equality between independently prepared integrations is assumed.
-/

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveComparison

open Purelib.RootIsolation.Newton.Band
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Riemann.Integration.PreparedDyadicRefinements (AllParentsProper)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents PrimitiveSumRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples.Sample
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandArea
open Purelib.Riemann.RootContinuation.PreparedNewtonBandBank (RefinedBoundaryParents)
open Purelib.Riemann.Integration.PreparedPrimitiveResampling.UniformPrimitiveNeighborhoods.RequestedParents
open Purelib.Riemann.Integration.PreparedPrimitiveResampling.UniformPrimitiveNeighborhoods.PrimitiveSumRequest
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectBlockRefinement)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target accuracy : Purelib.Data.Rat.Fraction.Rational} {band : PreparedBandRequest fixed target}

open Purelib.Data in
/-- Every retained parent request's model-error allowance is at most the supplied ceiling. -/
@[expose] def errorsBelow {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count accuracy parents) (ceiling : Rat.Fraction.Rational) : Prop :=
  match requests with
  | .nil => True
  | .cons head tail => head.request.budget.error ≤ ceiling ∧ errorsBelow tail ceiling

open Purelib.Riemann in
open Purelib.Data in
/-- The actual resampling of proper parents meets the supplied positive model-error ceiling. -/
theorem resample_errorsBelow {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count accuracy parents) (proper : AllParentsProper parents)
    {ceiling : Rat.Fraction.Rational} (positive : 0 < ceiling) :
    errorsBelow (Integration.PreparedPrimitiveResampling.UniformPrimitiveNeighborhoods.RequestedParents.resample
      requests proper positive) ceiling := by
  induction requests with
  | nil => trivial
  | cons head tail ih =>
    exact ⟨Integration.PreparedPrimitiveResampling.Request.resample_error_le head.request proper.1 positive, ih
      proper.2⟩

open Purelib.Riemann in
/-- Read the accepted primitive blocks as retained Newton-boundary refinements.

The adapter reuses each actual block and its numerical budget, together with the original parent's boundary evidence. -/
@[expose] def boundaryRequests (band : PreparedBandRequest fixed target) :
    ∀ {parents : List (CenteredEdge curve differential)} (requests : RequestedParents count accuracy parents),
      (∀ parent ∈ parents, ParentOnBoundary parent band.sample.output.box) →
        errorsBelow requests band.error → RefinedBoundaryParents band parents
  | _, .nil, _, _ => .nil
  | parent :: _, .cons head tail, boundary, errors =>
      .cons
        { boundary := boundary parent (List.mem_cons_self ..)
          accuracyProfile := Integration.PreparedModelAccuracy.Profile.build parent
          refinement :=
            { diameter := head.request.budget.rootDiameter
              diameterPositive := head.request.budget.rootDiameter_positive
              depth := head.request.budget.depth
              block := head.request.block
              block_depth := head.request.block_depth
              block_diameter := head.request.block_rootDiameter
              paid := head.request.budget.modelError_le.trans errors.1 } }
        (boundaryRequests band tail (fun other member => boundary other (List.mem_cons_of_mem _ member)) errors.2)

/-- The Newton-boundary adapter retains exactly the original request blocks. -/
theorem boundaryRequests_blocks {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count accuracy parents)
    (boundary : ∀ parent ∈ parents, ParentOnBoundary parent band.sample.output.box)
    (errors : errorsBelow requests band.error) : (boundaryRequests band requests boundary errors).blocks =
      requests.blocks := by
  induction requests with
  | nil => rfl
  | cons head tail ih =>
      exact congrArg (DirectBlockRefinement.cons head.request.block)
        (ih (fun other member => boundary other (List.mem_cons_of_mem _ member)) errors.2)

set_option genInjectivity false in
/-- Retain one literal resampling of the original primitive comparison and Newton boundary witness.

The primitive sum and polynomial values are preserved, while an exact block equation connects the boundary bank to the
actual sampled request. -/
structure PrimitiveSample {parents : List (CenteredEdge curve differential)}
    (band : PreparedBandRequest fixed target) (primitive : PrimitiveSumRequest parents count accuracy) where
  /-- The resampled request on the original parent list. -/ sample : PrimitiveSumRequest parents count accuracy
  /-- The cached primitive sum is exactly the original request's primitive sum. -/ sum_eq : sample.primitiveSum =
    primitive.primitiveSum
  /-- The retained primitive polynomial values equal the original request's values. -/ polynomials_eq :
    sample.requests.primitiveValues = primitive.requests.primitiveValues
  /-- The Newton-boundary refinement bank on the same original parents. -/ boundary : RefinedBoundaryParents band
    parents
  /-- The boundary bank and actual sampled request retain exactly the same blocks. -/ blocks_eq : boundary.blocks =
    sample.blocks

constructive_injectivity PrimitiveSample

namespace PrimitiveSample

variable {parents : List (CenteredEdge curve differential)} {primitive : PrimitiveSumRequest parents count accuracy}

open Purelib.Riemann in
/-- Resample the original primitive request to the Newton error ceiling once.

The proper-parent and boundary evidence build a bank reading those same accepted blocks while preserving the original
primitive polynomials and sum. -/
@[expose] def build (band : PreparedBandRequest fixed target) (primitive : PrimitiveSumRequest parents count accuracy)
    (proper : AllParentsProper parents)
    (boundary : ∀ parent ∈ parents, ParentOnBoundary parent band.sample.output.box) : PrimitiveSample band primitive :=
  let sample := Integration.PreparedPrimitiveResampling.UniformPrimitiveNeighborhoods.PrimitiveSumRequest.resample
    primitive proper band.errorPositive
  let requests := sample.requests
  let errors := resample_errorsBelow primitive.requests proper band.errorPositive
  ⟨sample, rfl,
    Integration.PreparedPrimitiveResampling.UniformPrimitiveNeighborhoods.RequestedParents.resample_primitiveValues
    primitive.requests proper band.errorPositive, boundaryRequests band requests boundary errors,
    boundaryRequests_blocks requests boundary errors⟩

open Purelib.Data in
/-- The actual resampled integral approximates the original retained primitive sum within its original target. -/
theorem accurate (result : PrimitiveSample band primitive) :
    Data.Gaussian.Norm.Basic.normSq (primitive.primitiveSum - result.sample.integralSample) < accuracy := by
  rw [← result.sum_eq, Gaussian.Norm.Basic.normSq_eq_canonical]
  exact result.sample.accurate

section
open Purelib.Riemann
open Purelib.Approximation
open Purelib.Data
/-- The actual resampled integral satisfies the retained density bound under the original count and movement
constraints. -/
theorem integral_density_bound (result : PrimitiveSample band primitive) (movement : Rat.Fraction.Rational) (depth :
  Nat)
    (countEq : parents.length = 2 ^ depth)
    (movements : ∀ parent ∈ parents, Readings.PreparedPrimitiveRequests.movement parent ≤
      Rational.Geometric.Basic.quarterRadius movement depth) :
    Data.Gaussian.Norm.Basic.normSq result.sample.integralSample ≤
      RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed band.error * movement := by
  rw [result.sample.integralSample_eq, ← result.blocks_eq]
  exact result.boundary.integral_density_bound movement depth countEq movements

/-- The original dyadic parent count and Newton movement ceiling pay the actual resampled integral within the band
target. -/
theorem integral_bound (result : PrimitiveSample band primitive) (movement : Rat.Fraction.Rational) (depth : Nat)
    (countEq : parents.length = 2 ^ depth) (movementLe : movement ≤ 32 * band.sample.output.radius ^ 2)
    (movements : ∀ parent ∈ parents, Readings.PreparedPrimitiveRequests.movement parent ≤
      Rational.Geometric.Basic.quarterRadius movement depth) :
    Data.Gaussian.Norm.Basic.normSq result.sample.integralSample ≤ target := by
  rw [result.sample.integralSample_eq, ← result.blocks_eq]
  exact result.boundary.bound movement depth countEq movementLe movements

/-- Bound the original face-comparison primitive sum by twice its accuracy target plus the Newton target.

Both payments concern the same retained resampled integral and original parent count and movement bounds. -/
theorem primitive_bound (result : PrimitiveSample band primitive) (movement : Rat.Fraction.Rational) (depth : Nat)
    (countEq : parents.length = 2 ^ depth) (movementLe : movement ≤ 32 * band.sample.output.radius ^ 2)
    (movements : ∀ parent ∈ parents, Readings.PreparedPrimitiveRequests.movement parent ≤
      Rational.Geometric.Basic.quarterRadius movement depth) :
    Data.Gaussian.Norm.Basic.normSq primitive.primitiveSum ≤ 2 * (accuracy + target) := by
  have sum := add_le_add result.accurate.le (result.integral_bound movement depth countEq movementLe movements)
  have bounded := (Gaussian.Norm.Bounds.normSq_add_le_two (primitive.primitiveSum - result.sample.integralSample)
    result.sample.integralSample).trans
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct sum (by decide))
  simpa only [sub_add_cancel, -eq_self, -iff_self] using bounded

end

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
/-- Bound the complete area of the same retained fine sample path.

The original dyadic parent count and movement ceiling control internal excursions through sixteen times the squared
density-movement product. -/
theorem area_density_bound (result : PrimitiveSample band primitive) (movement : Rat.Fraction.Rational) (depth : Nat)
    (movementNonnegative : 0 ≤ movement) (countEq : parents.length = 2 ^ depth)
    (movements : ∀ parent ∈ parents, Readings.PreparedPrimitiveRequests.movement parent ≤
      Rational.Geometric.Basic.quarterRadius movement depth) :
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.pathArea
      (Paths.PathArea.increments (Polynomial.Gaussian.Path.Basic.PathModel.mk (result.sample.blocks.children.map
        CenteredEdge.model)))) ≤
        16 * (RootContinuation.PreparedNewtonBandSamples.Sample.preparedDensity band.sample fixed band.error * movement)
          ^ 2 := by
  rw [← result.blocks_eq]
  exact RootContinuation.PreparedNewtonBandArea.RefinedBoundaryParents.area_density_bound
    result.boundary movement depth movementNonnegative countEq movements

end PrimitiveSample
end Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveComparison
