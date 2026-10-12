module
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.UniformPreparedBoundarySegments
import Purelib.RootIsolation.State.Raw

import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

open Purelib.Data

public section

/-! Actual paired side totals use the same subdivision-independent budget. -/
namespace Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.Newton.Band
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples.Sample (preparedDensity preparedDensity_nonnegative)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBank (PairedBoundaryParents)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedSide (PairedBoundarySide)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedBudget (PairedBandSelection)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.Integration.Path.PairedIncrementArea (total total_bound)
open Purelib.Integration.Path.PairedAreaBlocks (total_flatten)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.PreparedBoundarySegments (ParentOnBoundary)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

namespace PreparedNewtonPairedBank.PairedBoundaryParents
variable {request : PreparedBandRequest fixed target} {other :
  Differential genus}

open Purelib.Approximation.Rational in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
/-- Bound the total of the retained paired increment blocks by their joint density.

For the original dyadic parent count and quarter-radius movement bounds, transports the block totals through flattening
and cancels the exact dyadic count factor. -/
theorem total_density_bound
  {parents : List (CenteredEdge curve differential)}
    (bank : PairedBoundaryParents request other parents) (otherProfile : DifferentialProfile profile other.exponent)
    (movement : Fraction.Rational) (depth : Nat) (nonnegative : 0 ≤ movement) (count : parents.length = 2 ^ depth)
    (movements : ∀ parent ∈ parents,
      PreparedPrimitiveRequests.movement parent ≤ Geometric.Basic.quarterRadius movement depth) :
    Bounded (PairedIncrementArea.total bank.incrementBlocks.flatten)
      ((preparedDensity request.sample fixed request.error +
        preparedDensity request.sample otherProfile request.error) * movement) := by
  rw [PairedAreaBlocks.total_flatten]
  let density := preparedDensity request.sample fixed request.error + preparedDensity request.sample otherProfile
    request.error
  have densityNonnegative : 0 ≤ density := add_nonneg
    (preparedDensity_nonnegative request.sample fixed request.errorPositive.le)
    (preparedDensity_nonnegative request.sample otherProfile request.errorPositive.le)
  have bound := PairedIncrementArea.total_bound
    (Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative
      (Geometric.Basic.quarterRadius_nonneg nonnegative depth))
    (values := bank.incrementBlocks.map PairedIncrementArea.total)
    (fun value member => by
      obtain ⟨block, inBlocks, rfl⟩ := Map.mem_map.mp member
      exact (bank.block_bounds otherProfile movements block inBlocks).2)
    (count := 2 ^ depth) (by rw [List.Map.length_map, bank.incrementBlocks_length, count])
  have cancel : (((2 ^ depth : Nat) : Fraction.Rational)^2 * (density * Geometric.Basic.quarterRadius movement depth)) =
    density * movement := by
    calc
      _ = density * (((2 ^ depth : Nat) : Fraction.Rational) *
        (((2 ^ depth : Nat) : Fraction.Rational) * Geometric.Basic.quarterRadius movement depth)) := by ring1
      _ = _ := by rw [Geometric.DyadicCount.dyadic_count_cancel]
  rwa [cancel] at bound

end PreparedNewtonPairedBank.PairedBoundaryParents
namespace PreparedNewtonPairedSide.PairedBoundarySide
variable {request : PreparedBandRequest fixed target} {other :
  Differential genus} {start finish :
  Purelib.Data.Gaussian.Basic.Canonical}
  {segment : Purelib.Polynomial.Geometry.ClearPath.ClearSegment curve.polynomial request.sample.output.box start finish}
  {within : segment.WithinAmbient} {owner : Owner (curve.polynomial.eval start)} {sheet : Fin 2}

open Purelib.Data.Gaussian in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
/-- Bound a paired side summary total by joint density and endpoint movement.

Uses the actual covered mesh depth, parent count and movement certificates together with the summary total readback. -/
theorem total_density_bound (side :
  PairedBoundarySide request other segment within owner sheet)
    (otherProfile : DifferentialProfile profile other.exponent) :
    Bounded side.summary.totalValue ((preparedDensity request.sample fixed request.error +
      preparedDensity request.sample otherProfile request.error) * Data.Gaussian.Norm.Basic.normSq (finish - start)) :=
        by
  rw [side.summary.total_eq]
  exact side.refined.total_density_bound otherProfile _ side.covered.mesh.depth
    (Norm.Basic.normSq_nonneg _)
    (side.covered.parents_length.trans side.covered.mesh.edgeCount_eq)
    (fun _ member => by
      simpa only [PreparedPrimitiveRequests.movement,
        Norm.Basic.normSq_eq_canonical] using
        (UniformPreparedBoundarySegments.CoveredSegment.parent_movement side.covered member).le)

end PreparedNewtonPairedSide.PairedBoundarySide
namespace PreparedNewtonPairedBudget.PairedBandSelection
variable {other : Differential genus} {right : DifferentialProfile
  profile other.exponent} {radius : Purelib.Data.Rat.Fraction.Rational}
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Polynomial in
/-- The retained paired side total fits the selected target in both components.

Combines the actual endpoint containment and band diagonal bound with the joint density payment, preserving the cached
summary. -/
theorem side_total_bound
  (selection : PairedBandSelection fixed right target radius)
    {start finish : Basic.Canonical}
    {segment : Geometry.ClearPath.ClearSegment curve.polynomial selection.sample.output.box start finish}
    {within : segment.WithinAmbient}
    {owner : Owner (curve.polynomial.eval start)} {sheet : Fin 2}
    (side : PairedBoundarySide selection.sourceRequest other segment within owner sheet) :
    Bounded side.summary.totalValue target := by
  have firstInside : selection.sample.output.box.Contains start := by
    simpa only [Geometry.ClearPath.ClearSegment.pointAt_zero] using segment.pointAt_contains within 0 (by decide)
  have lastInside : selection.sample.output.box.Contains finish := by
    simpa only [Geometry.ClearPath.ClearSegment.pointAt_one] using segment.pointAt_contains within 1 (by decide)
  have movement := (selection.sample.output.box.normSq_sub_le_diagonalSq lastInside firstInside).trans
    (selection.sample.output.band.diagonalSq_le selection.sample.output.radiusPositive)
  have nonnegative := add_nonneg
    (preparedDensity_nonnegative selection.sample fixed selection.errorPositive.le)
    (preparedDensity_nonnegative selection.sample right selection.errorPositive.le)
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct movement nonnegative).trans
    selection.densities_paid
  have estimate := side.total_density_bound right
  exact ⟨estimate.1.trans paid, estimate.2.trans paid⟩

end PreparedNewtonPairedBudget.PairedBandSelection
end Purelib.Riemann.RootContinuation
