module
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.RootIsolation.State.Raw

public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
public import Purelib.Riemann.Paths.PathArea
import Purelib.Riemann.Periods.BilinearBoundaryRibbon

public section

/-! Paired child increments retain both actual models on one Newton mesh. -/
namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements

open Purelib.Data.List

open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent (PairedBoundaryParent)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.RootIsolation.Newton.Band
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

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

namespace PairedBoundaryParent
variable {request : PreparedBandRequest fixed target} {parent : CenteredEdge curve differential}
  {other : Differential genus}

/-- Pair the two actual child-model increments on one retained Newton boundary refinement.

The first block's children determine the list, and each second component reads that exact child recast to the other
differential. -/
@[expose] def increments (paired : PairedBoundaryParent request parent other) : List PrimitivePoint :=
  paired.refinement.first.block.children.map fun child =>
    ⟨child.model.integralSample, (recastCenteredEdge other child).model.integralSample⟩

/-- The paired increment count is the retained first block's dyadic child count.

Mapping each retained child to its two readings preserves the original first block's certified dyadic count. -/
theorem increments_length (paired : PairedBoundaryParent request parent other) :
    (increments paired).length = 2 ^ paired.refinement.first.block.depth := by
  rw [increments, Map.length_map]
  exact paired.refinement.first.block.childCount

section
open Purelib.Integration.Polynomial.Gaussian.Path.Basic
open Purelib.Riemann
/-- The left components are exactly the first retained child model's path increments.

The paired list reads the same retained first child models, so scalar projection agrees with their original path
increments. -/
theorem increments_left (paired : PairedBoundaryParent request parent other) :
    (increments paired).map PrimitivePoint.left =
      Paths.PathArea.increments (PathModel.mk (paired.refinement.first.block.children.map CenteredEdge.model)) := by
  unfold increments Paths.PathArea.increments
  dsimp only
  simp only [Map.map_map, -eq_self, -iff_self]
  dsimp only [Function.comp_def]

/-- The right components are exactly the second retained child model's path increments.

The original child-list agreement identifies the second retained models; scalar projection preserves their cached path
readings. -/
theorem increments_right (paired : PairedBoundaryParent request parent other) :
    (increments paired).map PrimitivePoint.right =
      Paths.PathArea.increments (PathModel.mk (paired.refinement.second.block.children.map CenteredEdge.model)) := by
  rw [paired.refinement.children_eq]
  unfold increments Paths.PathArea.increments
  dsimp only
  simp only [Map.map_map, -eq_self, -iff_self]
  dsimp only [Function.comp_def]

end

section
open Purelib.Data.Gaussian.Norm.Sum.Basic
open Purelib.Integration.Polynomial.Gaussian.Path.Basic
open Purelib.Riemann
/-- Summing the left components gives the first retained child model's integral sample. -/
theorem total_left (paired : PairedBoundaryParent request parent other) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((increments paired).map PrimitivePoint.left) =
      (PathModel.mk (paired.refinement.first.block.children.map CenteredEdge.model)).integralSample := by
  rw [increments_left paired, Paths.PathArea.increments_sum]

/-- Summing the right components gives the second retained child model's integral sample. -/
theorem total_right (paired : PairedBoundaryParent request parent other) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((increments paired).map PrimitivePoint.right) =
      (PathModel.mk (paired.refinement.second.block.children.map CenteredEdge.model)).integralSample := by
  rw [increments_right paired, Paths.PathArea.increments_sum]

end

open Purelib.Approximation.Rational.Geometric in
open Purelib.Data in
open Purelib.Data.Rat.Fraction.Order in
open Purelib.Riemann in
open Purelib.Riemann.Readings.PrimitiveAreaBounds in
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples in
/-- Bound both components of every actual paired child increment on the Newton mesh.

The two differential profiles use the same retained root sample, certified error and boundary starts. Their nonnegative
densities multiply the original parent's quarter-radius movement at the actual child depth. -/
theorem increments_bounded (paired : PairedBoundaryParent request parent other)
    (otherProfile : DifferentialProfile profile other.exponent) :
    ∀ value ∈ increments paired,
      PrimitivePoint.Bounded value ((Sample.preparedDensity request.sample fixed request.error +
        Sample.preparedDensity request.sample otherProfile request.error) *
        Basic.quarterRadius (movement parent) paired.refinement.first.block.depth) := by
  intro value member
  change value ∈ paired.refinement.first.block.children.map (fun child =>
    (⟨child.model.integralSample, (recastCenteredEdge other child).model.integralSample⟩ : PrimitivePoint)) at member
  obtain ⟨child, inChildren, rfl⟩ := List.Map.mem_map.mp member
  have boundary := paired.boundary.child_starts paired.refinement.first.block child inChildren
  have first := Sample.prepared_integral_bound request.sample fixed child boundary
    (paired.refinement.first_error inChildren) request.error_accurate
  have second := Sample.prepared_integral_bound request.sample otherProfile (recastCenteredEdge other child) boundary
    (paired.refinement.second_error inChildren) request.error_accurate
  have movement := Paths.PreparedPrimitivePaths.block_movement_le paired.refinement.first.block inChildren
  have firstNonnegative := Sample.preparedDensity_nonnegative request.sample fixed request.errorPositive.le
  have secondNonnegative := Sample.preparedDensity_nonnegative request.sample otherProfile request.errorPositive.le
  have radiusNonnegative := Basic.quarterRadius_nonneg
    (Readings.PreparedPrimitiveRequests.movement_nonnegative parent) paired.refinement.first.block.depth
  constructor
  · exact first.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct movement firstNonnegative).trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_right secondNonnegative) radiusNonnegative))
  · exact second.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct movement secondNonnegative).trans
      (Arithmetic.mul_le_mul_of_nonneg_right_direct
        (le_add_of_nonneg_left firstNonnegative) radiusNonnegative))

end PairedBoundaryParent
end Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
