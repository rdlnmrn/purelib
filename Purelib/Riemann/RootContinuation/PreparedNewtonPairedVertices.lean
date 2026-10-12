module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Prefix.Take
import Purelib.Data.List.Map
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Paths.PathArea
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.RootIsolation.State.Raw

import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitivePrefixes
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedIncrements
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Paired primitive vertices and numerical prefixes use the same retained mesh. -/
namespace Purelib.Riemann.Paths.PreparedPrimitivePaths

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)

open Purelib.Curves.Hyperelliptic in
/-- Differential recasting preserves every original child-prefix endpoint. -/
theorem prefixPoint_recast {genus : Nat} {curve : Basic.HyperellipticCurve genus}
    {first : Differentials.Basic.Differential genus} (other : Differentials.Basic.Differential genus) (start : Gaussian)
    (children : List (CenteredEdge curve first)) (length : Nat) :
    prefixPoint start (children.map (recastCenteredEdge other)) length = prefixPoint start children length := by
  induction children generalizing start length with
  | nil => rfl
  | cons head tail ih =>
    cases length with
    | zero => rfl
    | succ length => exact ih _ length

end Purelib.Riemann.Paths.PreparedPrimitivePaths

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent.PairedBoundaryParent

open Purelib
open Purelib.Data.Rat
open Purelib.RootIsolation.Newton.Band
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request (PrimitiveComparison)
open Purelib.Riemann.RootContinuation.NewtonBandBounds (Profile)
open Purelib.Riemann.RootContinuation.NewtonBandDifferentials (DifferentialProfile)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent (PairedBoundaryParent)
open Purelib.Riemann.Readings.PrimitiveAreaBounds.PrimitivePoint (Bounded)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
variable {genus count index : Nat} {curve : HyperellipticCurve genus} {differential
  other : Differential genus}
  {ambient : Purelib.Geometry.Rational.Box} {current : Purelib.RootIsolation.State.Raw.RawWindingState
    curve.polynomial ambient}
  {profile : Profile curve.squarefree current.box} {fixed : DifferentialProfile profile differential.exponent}
  {target : Purelib.Data.Rat.Fraction.Rational} {request : PreparedBandRequest fixed target} {parent : CenteredEdge
    curve differential}

open Purelib.Integration.Path in
open Purelib.Riemann.RootContinuation in
/-- Read the paired numerical prefix total from the original increment list. -/
@[expose] def numericalVertex (paired : PairedBoundaryParent request parent other) (length : Nat) : PrimitivePoint :=
  PairedIncrementArea.total ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).take length)

section
open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Riemann.Paths
open Purelib.Riemann.RootContinuation
/-- The first numerical coordinate is the exact original first-row prefix integral sample. -/
theorem numericalVertex_left (paired : PairedBoundaryParent request parent other) (length : Nat) :
    (paired.numericalVertex length).left =
      (Basic.PathModel.mk ((paired.refinement.first.block.children.map CenteredEdge.model).take length)).integralSample
        := by
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum (((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments
    paired).take
    length).map PrimitivePoint.left) = _
  rw [Data.List.Map.map_take, PreparedNewtonPairedIncrements.PairedBoundaryParent.increments_left paired]
  simpa only [PathArea.increments, Data.List.Map.map_take, -eq_self, -iff_self] using
    PathArea.increments_sum
      (Basic.PathModel.mk ((paired.refinement.first.block.children.map CenteredEdge.model).take length))

/-- The second numerical coordinate is the exact original second-row prefix integral sample. -/
theorem numericalVertex_right (paired : PairedBoundaryParent request parent other) (length : Nat) :
    (paired.numericalVertex length).right =
      (Basic.PathModel.mk ((paired.refinement.second.block.children.map CenteredEdge.model).take length)).integralSample
        := by
  change Data.Gaussian.Norm.Sum.Basic.gaussianSum (((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments
    paired).take
    length).map PrimitivePoint.right) = _
  rw [Data.List.Map.map_take, PreparedNewtonPairedIncrements.PairedBoundaryParent.increments_right paired]
  simpa only [PathArea.increments, Data.List.Map.map_take, -eq_self, -iff_self] using
    PathArea.increments_sum
      (Basic.PathModel.mk ((paired.refinement.second.block.children.map CenteredEdge.model).take length))

end

open Purelib.Riemann.Paths in
/-- Evaluate both original primitive models at the same retained first-row prefix point.

Each coordinate subtracts its own original model value at the parent start; the shared geometry and distinct models
remain explicit. -/
@[expose] def primitiveVertex (paired : PairedBoundaryParent request parent other)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) (length : Nat) : PrimitivePoint :=
  let point := PreparedPrimitivePaths.prefixPoint (parent.edge.segment.pointAt parent.edge.left.parameter)
    paired.refinement.first.block.children length
  ⟨first.2.1.primitive.value.eval point - first.2.1.primitive.value.eval (parent.edge.point 0),
    second.2.1.primitive.value.eval point - second.2.1.primitive.value.eval (parent.edge.point 0)⟩

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
/-- The original primitive and numerical prefix vertices differ by their retained maximum error bound.

The second-row endpoint is identified through the exact differential-recast child list, preserving both original
comparisons. -/
theorem vertices_accurate (paired : PairedBoundaryParent request parent other)
    (first : PrimitiveComparison paired.refinement.first count index)
    (second : PrimitiveComparison paired.refinement.second count index) (length : Nat) :
    PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((paired.primitiveVertex first second length).sub (paired.numericalVertex length))
      (max first.2.2.bound second.2.2.bound) := by
  constructor
  · rw [← Norm.Basic.normSq_eq_canonical]
    change Data.Gaussian.Norm.Basic.normSq (_ - (paired.numericalVertex length).left) ≤ _
    rw [paired.numericalVertex_left]
    exact (first.vertex_error_le paired.refinement.accuracyPositive.le length).trans (Fraction.Order.Basic.le_max_left _
      _)
  · rw [← Norm.Basic.normSq_eq_canonical]
    change Data.Gaussian.Norm.Basic.normSq (_ - (paired.numericalVertex length).right) ≤ _
    rw [paired.numericalVertex_right]
    have bounded := second.vertex_error_le paired.refinement.accuracyPositive.le length
    have pointEq : PreparedPrimitivePaths.prefixPoint
        (parent.edge.segment.pointAt parent.edge.left.parameter)
        paired.refinement.second.block.children length =
      PreparedPrimitivePaths.prefixPoint (parent.edge.segment.pointAt parent.edge.left.parameter)
        paired.refinement.first.block.children length := by
      rw [paired.refinement.children_eq, PreparedPrimitivePaths.prefixPoint_recast]
    change Data.Gaussian.Norm.Basic.normSq (second.2.1.primitive.value.eval
        (PreparedPrimitivePaths.prefixPoint (parent.edge.segment.pointAt parent.edge.left.parameter)
          paired.refinement.second.block.children length) - second.2.1.primitive.value.eval (parent.edge.point 0) -
      (Basic.PathModel.mk ((paired.refinement.second.block.children.map CenteredEdge.model).take
        length)).integralSample) ≤ _ at bounded
    rw [pointEq] at bounded
    exact bounded.trans (Fraction.Order.Basic.le_max_right _ _)

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Every original numerical prefix vertex is bounded by the summed densities times parent movement.

The retained dyadic increment count and quarter-radius cancellation give the same uniform bound for all prefix lengths.
-/
theorem numericalVertex_bounded (paired : PairedBoundaryParent request parent other)
    (otherProfile : DifferentialProfile profile other.exponent) (length : Nat) :
    PrimitiveAreaBounds.PrimitivePoint.Bounded
      (paired.numericalVertex length) ((PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed
        request.error +
        PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error) *
          PreparedPrimitiveRequests.movement parent) := by
  let density := PreparedNewtonBandSamples.Sample.preparedDensity request.sample fixed request.error +
    PreparedNewtonBandSamples.Sample.preparedDensity request.sample otherProfile request.error
  let movement := PreparedPrimitiveRequests.movement parent
  let depth := paired.refinement.first.block.depth
  have densityNonnegative : 0 ≤ density := add_nonneg
    (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample fixed request.errorPositive.le)
    (PreparedNewtonBandSamples.Sample.preparedDensity_nonnegative request.sample otherProfile request.errorPositive.le)
  have nonnegative : 0 ≤ density * Geometric.Basic.quarterRadius movement depth :=
    Fraction.Order.Arithmetic.mul_nonneg_direct densityNonnegative
      (Geometric.Basic.quarterRadius_nonneg (PreparedPrimitiveRequests.movement_nonnegative parent) depth)
  have bounded := PairedIncrementArea.total_bound nonnegative
    (fun value member => PreparedNewtonPairedIncrements.PairedBoundaryParent.increments_bounded paired otherProfile
      value (List.mem_of_mem_take member))
    (count := 2 ^ depth) (show ((PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).take
      length).length ≤ 2 ^ depth from
      (by
        rw [Data.List.Prefix.Take.length_take]
        have retained : min length (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length ≤
            (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length := by
          change (if length ≤ (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length then
            length else (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length) ≤
              (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length
          by_cases ordered : length ≤ (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments paired).length
          · rewrite [if_pos ordered]
            exact ordered
          · rewrite [if_neg ordered]
            exact Nat.le_refl _
        exact retained.trans_eq (PreparedNewtonPairedIncrements.PairedBoundaryParent.increments_length paired)))
  have identity : (((2 ^ depth : Nat) : Fraction.Rational)^2 *
      (density * Geometric.Basic.quarterRadius movement depth)) = density * movement := by
    calc
      _ = density * (((2 ^ depth : Nat) : Fraction.Rational) *
        (((2 ^ depth : Nat) : Fraction.Rational) * Geometric.Basic.quarterRadius movement depth)) := by ring1
      _ = _ := by rw [Geometric.DyadicCount.dyadic_count_cancel]
  rw [identity] at bounded
  exact bounded

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedParent.PairedBoundaryParent
