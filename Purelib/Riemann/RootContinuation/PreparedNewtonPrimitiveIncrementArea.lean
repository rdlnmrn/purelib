module
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.Integration.UniformPreparedPrimitives
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.RootIsolation.State.Raw

import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Topology.Surface.Boundary.HandleAreaBounds
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitiveArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Local increment error densities for the retained primitive and Newton cells. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request.PrimitiveComparison

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.Riemann.Integration.PreparedModelAccuracy (Profile Request Coordinate)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus count index : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {profile : Profile parent} {target : Coordinate}
  {request : Request profile target}

open Purelib.Approximation.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- The retained scalar error density of the original primitive comparison.

The exact model remainder, neighborhood numerator bound, inverse-error scale, dyadic depth and target determine the
original three terms. -/
@[expose] def errorDensity (comparison : PrimitiveComparison request count index) : Coordinate :=
  2 * comparison.2.1.primitive.remainderBound * Geometric.Basic.quarterRadius (movement parent) request.block.depth +
    (4 * Bounds.Box.denseEvalNormBound (differentialNumerator differential)
      (comparison.1.patch.neighborhood count).box *
      Geometric.Basic.quarterRadius (comparison.1.patch.neighborhood count).inverseErrorScale index + 40 * target)

/-- The cached original comparison bound equals its error density times parent movement. -/
theorem bound_eq_density (comparison : PrimitiveComparison request count index) :
    comparison.2.2.bound = comparison.errorDensity * movement parent := by
  rw [comparison.2.2.bound_eq]
  unfold errorDensity
  ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- An actual original child increment error is bounded by retained density times dyadic movement.

The child's membership supplies its original model accuracy and patch containment; the same original comparison model
evaluates both endpoints. -/
theorem child_error_le (comparison : PrimitiveComparison request count index)
    {child : CenteredEdge curve differential} (member : child ∈ request.block.children) :
    Data.Gaussian.Norm.Basic.normSq (comparison.2.1.primitive.value.eval (child.edge.point 1) -
      comparison.2.1.primitive.value.eval (child.edge.point 0) - child.model.integralSample) ≤
        comparison.errorDensity * Geometric.Basic.quarterRadius (movement parent) request.block.depth := by
  have starts := PreparedPrimitivePaths.block_starts_inside request.block (comparison.1.patch.neighborhood count).box
    (comparison.1.patch.start_inside count) comparison.1.finishInside
  have finishes := PreparedPrimitivePaths.block_finishes_inside request.block (comparison.1.patch.neighborhood
    count).box
    (comparison.1.patch.start_inside count) comparison.1.finishInside
  have numeratorLe := Bounds.Box.normSq_eval_le_denseEvalNormBound
    (differentialNumerator differential) (starts child member)
  rw [Norm.Basic.normSq_eq_canonical] at numeratorLe
  have bounded := UniformPreparedPrimitives.children_bounded comparison.1.patch comparison.2.1 request.block.roots
    (Bounds.Box.denseEvalNormBound (differentialNumerator differential) (comparison.1.patch.neighborhood count).box)
    target (Geometric.Basic.quarterRadius (movement parent) request.block.depth) child member (starts child member)
      (finishes child member)
    numeratorLe
    (request.child_error member) (PreparedPrimitivePaths.block_movement_le request.block member)
  rw [← Norm.Basic.normSq_eq_canonical] at bounded
  exact bounded.trans_eq (by unfold errorDensity; ring1)

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request.PrimitiveComparison

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent.PairedBoundaryParent

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request (PrimitiveComparison)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent (PairedBoundaryParent)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
variable {genus count index : Nat} {curve : HyperellipticCurve genus} {differential
  other : Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target} {parent : CenteredEdge
    curve differential}

/-- Pair original two-row primitive increments with their exact numerical child samples.

The original first-row child order determines both coordinates; the second numerical sample uses the exact differential
recast of that child. -/
@[expose] def primitiveIncrementPairs (paired : PairedBoundaryParent request parent other)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) : List (PrimitivePoint × PrimitivePoint) :=
  paired.refinement.first.block.children.map fun child =>
    (⟨first.2.1.primitive.value.eval (child.edge.point 1) - first.2.1.primitive.value.eval (child.edge.point 0),
      second.2.1.primitive.value.eval (child.edge.point 1) - second.2.1.primitive.value.eval (child.edge.point 0)⟩,
      ⟨child.model.integralSample, (recastCenteredEdge other child).model.integralSample⟩)

open Purelib.Riemann.RootContinuation in
/-- The numerical projection reads back the exact original paired increment list. -/
theorem primitiveIncrementPairs_numeric (paired : PairedBoundaryParent request parent other)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) :
    (paired.primitiveIncrementPairs first second).map Prod.snd =
      (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired) := by
  simp only [primitiveIncrementPairs, PreparedNewtonPairedIncrements.PairedBoundaryParent.increments,
    Data.List.Map.map_map, -eq_self, -iff_self]
  rfl

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Riemann.Readings in
/-- Every retained primitive/numerical pair satisfies the original maximum-density error bound.

The second-row child and depth are transported through the actual paired-refinement identities, preserving the shared
original dyadic movement. -/
theorem primitiveIncrementPairs_errors (paired : PairedBoundaryParent request parent other)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) :
    ∀ pair ∈ paired.primitiveIncrementPairs first second,
      PrimitiveAreaBounds.PrimitivePoint.Bounded (pair.1.sub pair.2)
        (max first.errorDensity second.errorDensity *
          Geometric.Basic.quarterRadius (PreparedPrimitiveRequests.movement parent) paired.refinement.first.block.depth)
            := by
  intro pair member
  obtain ⟨child, inChildren, rfl⟩ := Map.mem_map.mp member
  have distanceNonnegative := Geometric.Basic.quarterRadius_nonneg
    (PreparedPrimitiveRequests.movement_nonnegative parent) paired.refinement.first.block.depth
  constructor
  · rw [← Norm.Basic.normSq_eq_canonical]
    exact (first.child_error_le inChildren).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.le_max_left _ _)
        distanceNonnegative)
  · rw [← Norm.Basic.normSq_eq_canonical]
    have inSecond : recastCenteredEdge other child ∈ paired.refinement.second.block.children := by
      rw [paired.refinement.children_eq]
      exact Map.mem_map_of_mem inChildren
    have bounded := second.child_error_le inSecond
    have depths : paired.refinement.second.block.depth = paired.refinement.first.block.depth := by
      rw [paired.refinement.first_block, paired.refinement.second_block]
      rfl
    have charge : second.errorDensity *
        Geometric.Basic.quarterRadius (PreparedPrimitiveRequests.movement (recastCenteredEdge other parent))
          paired.refinement.second.block.depth =
      second.errorDensity * Geometric.Basic.quarterRadius (PreparedPrimitiveRequests.movement parent)
        paired.refinement.first.block.depth :=
      congrArg (fun depth => second.errorDensity * Geometric.Basic.quarterRadius (PreparedPrimitiveRequests.movement
        parent) depth) depths
    exact bounded.trans (charge.le.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.le_max_right _ _)
        distanceNonnegative))

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
open Purelib.Topology.Surface in
/-- Bound the original primitive and numerical paired increment areas.

The maximum error density is capped below by zero; the retained summed density and parent movement give the exact
factor-16 comparison payment without changing either ordered increment list. -/
theorem primitive_increment_area_error_le (paired : PairedBoundaryParent request parent other)
    (otherProfile : DifferentialProfile profile other.exponent)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) :
    let error := max 0 (max first.errorDensity second.errorDensity)
    let density := PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
      PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error
    Data.Gaussian.Norm.Basic.normSq
      (PairedIncrementArea.area ((paired.primitiveIncrementPairs first second).map Prod.fst) -
        PairedIncrementArea.area (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired)) ≤
      16 * error * (2 * (density + error)) * (PreparedPrimitiveRequests.movement parent)^2 := by
  intro error density
  let distance := Geometric.Basic.quarterRadius (PreparedPrimitiveRequests.movement parent)
    paired.refinement.first.block.depth
  have distanceNonnegative : 0 ≤ distance := Geometric.Basic.quarterRadius_nonneg
    (PreparedPrimitiveRequests.movement_nonnegative parent) _
  have errorNonnegative : 0 ≤ error := Fraction.Order.Basic.le_max_left _ _
  have densityNonnegative : 0 ≤ density := add_nonneg
    (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed request.errorPositive.le)
    (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample otherProfile request.errorPositive.le)
  have errors : ∀ pair ∈ paired.primitiveIncrementPairs first second, PrimitiveAreaBounds.PrimitivePoint.Bounded
    (pair.1.sub pair.2) (error * distance) := by
    intro pair member
    have bounded := paired.primitiveIncrementPairs_errors first second pair member
    have larger := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (Fraction.Order.Basic.le_max_right 0 (max
      first.errorDensity second.errorDensity)) distanceNonnegative
    exact ⟨bounded.1.trans larger, bounded.2.trans larger⟩
  have numeric : ∀ pair ∈ paired.primitiveIncrementPairs first second, PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2
    (density * distance) := by
    intro pair member
    apply PreparedNewtonPairedIncrements.PairedBoundaryParent.increments_bounded paired otherProfile
    rw [← paired.primitiveIncrementPairs_numeric first second]
    exact Map.mem_map_of_mem member
  have scalar : density * distance ≤ (2 * (density + error)) * distance := by
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct _ distanceNonnegative
    have sumNonnegative := add_nonneg densityNonnegative errorNonnegative
    exact (le_add_of_nonneg_right errorNonnegative).trans
      ((le_add_of_nonneg_right sumNonnegative).trans_eq (by ring1))
  have leftBound : ∀ pair ∈ paired.primitiveIncrementPairs first second,
      PrimitiveAreaBounds.PrimitivePoint.Bounded pair.1 ((2 * (density + error)) * distance) := by
    intro pair member
    have bounded := Boundary.HandleAreaBounds.PrimitivePoint.perturbation_bounded (numeric pair member) (errors pair
      member)
    have equal : 2 * (density * distance + error * distance) = (2 * (density + error)) * distance := by ring1
    rw [equal] at bounded
    exact bounded
  have rightBound : ∀ pair ∈ paired.primitiveIncrementPairs first second,
      PrimitiveAreaBounds.PrimitivePoint.Bounded pair.2 ((2 * (density + error)) * distance) := by
    intro pair member
    exact ⟨(numeric pair member).1.trans scalar, (numeric pair member).2.trans scalar⟩
  have bounded := PairedIncrementComparison.dyadic_area_difference_bound
    (paired.primitiveIncrementPairs first second) paired.refinement.first.block.depth
    (by rw [primitiveIncrementPairs, Data.List.Map.length_map]; exact paired.refinement.first.block.childCount)
    (PreparedPrimitiveRequests.movement_nonnegative parent) errorNonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg densityNonnegative errorNonnegative)) errors
      leftBound rightBound
  rw [paired.primitiveIncrementPairs_numeric first second] at bounded
  exact bounded

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent.PairedBoundaryParent
