module
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.RootIsolation.State.Raw

import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.Readings.PreparedPairedPrimitiveRequests
public import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveAreaReadback
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveIncrementArea
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedVertices
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! A positive request pays the full local primitive-versus-Newton area. -/
namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request (PrimitiveComparison)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent (PairedBoundaryParent)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target} {parent : CenteredEdge
    curve differential}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Periods in
open Purelib.Riemann.RootContinuation in
/-- A paired parent whose original area and both endpoint comparisons meet one target.

The dependent tuple retains its exact paired refinement, common model index and distinct primitive comparisons with
three separate paid inequalities. -/
@[expose] def RequestedPrimitiveParent (request : PreparedBandRequest fixed target)
    (parent : CenteredEdge curve differential) (other : Differentials.Basic.Differential genus) (count : Nat)
      (areaTarget : Fraction.Rational) :=
  (paired : PairedBoundaryParent request parent other) × (index : Nat) ×
  (first : PrimitiveComparison paired.refinement.first count index) ×
    { second : PrimitiveComparison paired.refinement.second count index //
      Data.Gaussian.Norm.Basic.normSq (CenteredBilinearPath.area
          (fun vertex : Fin ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length + 1) =>
            paired.primitiveVertex first second vertex.val) -
        PairedIncrementArea.traceArea PrimitivePoint.zero
          (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired)) ≤ areaTarget ∧
      first.2.2.bound ≤ areaTarget ∧ second.2.2.bound ≤ areaTarget }

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Prepare an original paired parent paying both area and endpoint errors.

The retained density and parent movement define an area-plus-endpoint weight; a positive unit-capped allowance selects
the shared primitive request and keeps the original patch, boundary and properness witnesses. -/
@[expose] def RequestedPrimitiveParent.build (request : PreparedBandRequest fixed target)
    (parent : CenteredEdge curve differential) (other : Differentials.Basic.Differential genus)
    (otherProfile : DifferentialProfile profile other.exponent)
    (boundary : PreparedBoundarySegments.ParentOnBoundary parent request.sample.output.box)
    (patch : PreparedPatch parent) (count : Nat)
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (areaTarget : Fraction.Rational) (positive : 0 < areaTarget) :
    RequestedPrimitiveParent request parent other count areaTarget := by
  let density := PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
    PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error
  let movement := PreparedPrimitiveRequests.movement parent
  have densityNonnegative : 0 ≤ density := add_nonneg
    (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed request.errorPositive.le)
    (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample otherProfile request.errorPositive.le)
  have movementSquaredNonnegative : 0 ≤ movement^2 :=
    Fraction.Order.Arithmetic.pow_nonneg_direct (PreparedPrimitiveRequests.movement_nonnegative parent) 2
  let areaWeight := 32 * (density + 1) * movement^2
  have areaWeightNonnegative : 0 ≤ areaWeight := Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg densityNonnegative (by decide)))
      movementSquaredNonnegative
  let weight := areaWeight + movement
  have movementNonnegative : 0 ≤ movement := PreparedPrimitiveRequests.movement_nonnegative parent
  have weightNonnegative : 0 ≤ weight := add_nonneg areaWeightNonnegative movementNonnegative
  let allowance := min (1 : Fraction.Rational) (Budget.Weighted.allowance areaTarget weight)
  have allowancePositive : 0 < allowance := Fraction.Order.Basic.lt_min (by decide)
    (Budget.Weighted.allowance_positive positive weightNonnegative)
  have allowanceSmall : allowance ≤ 1 := Fraction.Order.Basic.min_le_left _ _
  have allowancePaid : weight * allowance ≤ areaTarget :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right _ _)
      weightNonnegative).trans
      (Budget.Weighted.mul_allowance_le positive.le weightNonnegative)
  have areaAllowancePaid : areaWeight * allowance ≤ areaTarget :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (le_add_of_nonneg_right movementNonnegative) allowancePositive.le).trans allowancePaid
  have endpointAllowancePaid : allowance * movement ≤ areaTarget := by
    rw [Fraction.Field.mul_comm]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (le_add_of_nonneg_left areaWeightNonnegative) allowancePositive.le).trans allowancePaid
  let selected := PreparedPairedPrimitiveRequests.PaidPrimitivePair.build parent other patch count finishInside proper
    request.error allowance request.errorPositive allowancePositive
  let paired : PairedBoundaryParent request parent other := ⟨boundary, selected.1⟩
  let first := selected.2.2.1
  let second := selected.2.2.2.val
  let error := max (0 : Fraction.Rational) (max first.errorDensity second.errorDensity)
  have errorNonnegative : 0 ≤ error := Fraction.Order.Basic.le_max_left _ _
  have errorLe : error ≤ allowance := Fraction.Order.Basic.max_le allowancePositive.le
    (Fraction.Order.Basic.max_le selected.2.2.2.property.1 selected.2.2.2.property.2)
  have estimate := paired.primitive_vertex_area_error_le otherProfile first second
  have factorLe : 2 * (density + error) ≤ 2 * (density + 1) :=
    Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add (le_refl density) (errorLe.trans
      allowanceSmall)) (by decide)
  have productLe : 16 * error * (2 * (density + error)) ≤ 16 * allowance * (2 * (density + 1)) :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct factorLe
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) errorNonnegative)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorLe (by decide +kernel))
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg densityNonnegative (by decide))))
  have paid : 16 * error * (2 * (density + error)) * movement^2 ≤ areaTarget :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct productLe movementSquaredNonnegative).trans
      ((show 16 * allowance * (2 * (density + 1)) * movement^2 = areaWeight * allowance by
          dsimp only [areaWeight, -eq_self, -iff_self];
          ring1).le.trans areaAllowancePaid)
  have firstEndpoint : first.2.2.bound ≤ areaTarget := by
    rw [first.bound_eq_density]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct selected.2.2.2.property.1
      movementNonnegative).trans endpointAllowancePaid
  have secondEndpoint : second.2.2.bound ≤ areaTarget := by
    rw [second.bound_eq_density]
    exact (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct selected.2.2.2.property.2
      movementNonnegative).trans endpointAllowancePaid
  exact ⟨paired, selected.2.1, first, second, estimate.trans paid, firstEndpoint, secondEndpoint⟩

end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParent
