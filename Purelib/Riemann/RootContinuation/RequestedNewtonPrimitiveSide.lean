module
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.TracedCoveredSegment
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Meshes.UniformPrimitiveMesh
import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.RootContinuation.RequestedNewtonPrimitivePolygon
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Paths.PreparedTraceBudget
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveAreaReadback
import Purelib.Topology.Polygon.Stokes
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! A full side request pays internal areas and the parent-endpoint polygon. -/
namespace Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveSide

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents (RequestedPrimitiveParents)
open Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveParents.RequestedPrimitiveParents (build)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredSegment CoveredParents)
open _root_.Purelib.Riemann.Paths (TracedCoveredSegment)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide (PairedBoundarySide)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_nonneg)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential other :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target}

open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
/-- Cached original primitive and numerical path summaries with paid area and endpoint errors.

The retained local target and requested parent bank index both actual increment lists, with separate guarantees against
the same overall target. -/
@[expose] def FullAreaRequest (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential
  genus)
    (count : Nat) (parents : List (CenteredEdge curve differential)) (areaTarget : Fraction.Rational) :=
  (localTarget : Fraction.Rational) ×
  (prepared : RequestedPrimitiveParents request other count localTarget parents) ×
  (numerical : PairedIncrementArea.Summary prepared.bank.incrementBlocks.flatten) ×
    { primitive : PairedIncrementArea.Summary prepared.primitives.primitiveBlocks.flatten //
      Data.Gaussian.Norm.Basic.normSq (primitive.areaValue - numerical.areaValue) ≤ areaTarget ∧
      PrimitiveAreaBounds.PrimitivePoint.Bounded
        (primitive.totalValue.sub numerical.totalValue) areaTarget }

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Prepare the original covered parents to pay the complete area and endpoint comparison.

A unit-capped allowance uses the exact parent count and numerical magnitude weight; the resulting original bank supplies
both cached summaries and their separate payments. -/
@[expose] def fullAcquire (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential genus)
    (otherProfile : DifferentialProfile profile other.exponent)
    {parents : List (CenteredEdge curve differential)}
    (covered : Observation.UniformPreparedMesh.CoveredParents count parents)
    (boundary : ∀ parent ∈ parents, PreparedBoundarySegments.ParentOnBoundary parent request.sample.output.box)
    (proper : PreparedDyadicRefinements.AllParentsProper parents)
    (movement : Fraction.Rational) (movementNonnegative : 0 ≤ movement)
    (movements : ∀ parent ∈ parents, PreparedPrimitiveRequests.movement parent ≤ movement)
    (areaTarget : Fraction.Rational) (positive : 0 < areaTarget) :
    FullAreaRequest request other count parents areaTarget := by
  let magnitude := (PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
    PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) * movement
  have magnitudeNonnegative : 0 ≤ magnitude := Fraction.Order.Arithmetic.mul_nonneg_direct
    (add_nonneg (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed
      request.errorPositive.le)
      (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample otherProfile
        request.errorPositive.le)) movementNonnegative
  let n : Fraction.Rational := parents.length
  have nNonnegative : 0 ≤ n := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  let weight := 2 * (n^2 + 32 * n^4 * (magnitude + 1))
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Fraction.Order.Arithmetic.pow_nonneg_direct nNonnegative 2)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Fraction.Order.Arithmetic.pow_nonneg_direct nNonnegative 4))
        (add_nonneg magnitudeNonnegative (by decide))))
  let localTarget := min (1 : Fraction.Rational) (Budget.Weighted.allowance areaTarget weight)
  have localPositive : 0 < localTarget := Fraction.Order.Basic.lt_min (by decide)
    (Budget.Weighted.allowance_positive positive weightNonnegative)
  have paid : weight * localTarget ≤ areaTarget :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right _ _)
      weightNonnegative).trans
      (Budget.Weighted.mul_allowance_le positive.le weightNonnegative)
  let prepared := build request other otherProfile count localTarget localPositive covered boundary proper
  have bounded := prepared.full_area_error_le magnitudeNonnegative localPositive.le (Fraction.Order.Basic.min_le_left _
    _)
    (prepared.endpointPairs_numerical otherProfile movements)
  let numerical := PairedIncrementArea.Summary.build prepared.bank.incrementBlocks.flatten
  let primitive := PairedIncrementArea.Summary.build prepared.primitives.primitiveBlocks.flatten
  have squareNonnegative : 0 ≤ n^2 := Fraction.Order.Arithmetic.pow_nonneg_direct nNonnegative 2
  have polygonNonnegative : 0 ≤ 32 * n^4 * (magnitude + 1) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.pow_nonneg_direct nNonnegative 4))
      (add_nonneg magnitudeNonnegative (by decide))
  have weightGe : n^2 ≤ weight :=
    (le_add_of_nonneg_right polygonNonnegative).trans
      ((le_add_of_nonneg_right (add_nonneg squareNonnegative polygonNonnegative)).trans_eq (by
          dsimp only [weight, -eq_self, -iff_self];
          ring1))
  have endpointPaid : n^2 * localTarget ≤ areaTarget :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct weightGe localPositive.le).trans paid
  have endpoints := prepared.total_error_le localPositive.le primitive numerical
  refine ⟨localTarget, prepared, numerical, primitive, ?_, endpoints.1.trans endpointPaid, endpoints.2.trans
    endpointPaid⟩
  rw [primitive.area_eq, numerical.area_eq]
  exact bounded.trans paid

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Meshes in
open Purelib.Riemann.Paths in
/-- Acquire the full comparison for an original covered side using its endpoint movement bound.

The retained side, coverage, owner and sheet supply the exact parent geometry and properness witnesses. -/
@[expose] def fullOfCovered (request : PreparedBandRequest fixed target) (other : Differentials.Basic.Differential
  genus)
    (otherProfile : DifferentialProfile profile other.exponent)
    {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish}
    {within : segment.WithinAmbient}
    {owner : Observation.UniformPreparedMesh.Owner (curve.polynomial.eval (segment.pointAt
      UniformPrimitiveMesh.firstEndpoint.parameter))}
    {sheet : Fin 2} (covered : Observation.UniformPreparedMesh.CoveredSegment segment within owner differential sheet
      count)
    (side : PreparedBoundarySegments.SameSide request.sample.output.box start finish)
    (areaTarget : Fraction.Rational) (positive : 0 < areaTarget) :
    FullAreaRequest request other count covered.parents areaTarget :=
  fullAcquire request other otherProfile covered.covered
    (fun _ member => UniformPreparedBoundarySegments.CoveredSegment.parent_boundary covered side member)
      covered.parents_proper
    (Data.Gaussian.Norm.Basic.normSq (finish - start)) (Norm.Basic.normSq_nonneg _)
    (fun _ member => by
      have scalar := UniformPreparedBoundarySegments.CoveredSegment.parent_movement covered member
      rw [← Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.le.trans
        (Geometric.Basic.quarterRadius_le_scale
          (Norm.Basic.normSq_nonneg _) covered.mesh.depth))
    areaTarget positive

open Purelib.Curves.Hyperelliptic.Integration in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
open Purelib.Riemann.Paths in
/-- Retain the original traced side and the numerical summary from its full-area request.

The covered segment, trace budget and request-fit proof are reused with the exact requested bank and cached numerical
summary. -/
@[expose] def FullAreaRequest.toSide {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish}
    {within : segment.WithinAmbient} {owner : Observation.UniformPreparedMesh.Owner (curve.polynomial.eval start)}
    {sheet : Fin 2} (traced : TracedCoveredSegment segment within (PreparedClearPathModels.ownerAtStart segment owner)
      differential sheet 0)
    {areaTarget : Fraction.Rational} (result : FullAreaRequest request other 0 traced.covered.parents areaTarget) :
    PairedBoundarySide request other segment within owner sheet :=
  ⟨traced.covered, traced.budget, traced.fits, result.2.1.bank, result.2.2.1⟩

end Purelib.Riemann.RootContinuation.RequestedNewtonPrimitiveSide
