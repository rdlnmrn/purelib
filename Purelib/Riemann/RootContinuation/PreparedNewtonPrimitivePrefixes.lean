module
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Nat.Order
import Purelib.Data.List.Prefix.Take
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Riemann.Integration.UniformPreparedPrimitives
public import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive

import Purelib.Integration.Path.IncrementArea
public import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Polynomial.Dense.Evaluation
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Every prefix of the existing Newton child list has a primitive comparison.
The full dyadic count bounds every prefix, so its cancellation is uniform. -/
namespace Purelib.CCL.Calculus.PathPrimitive

open Purelib
open Purelib.Data.Rat
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)

open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Path in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Bound every original cell prefix error by full-list count squared times its common scalar budget.

The retained pointwise error bound is restricted to the actual prefix, keeping the original full-list count as a uniform
upper bound. -/
theorem prefix_error_le (primitive : Basic.Canonical → Basic.Canonical) (cells : List Basic.CellModel)
    (length : Nat) {budget : Fraction.Rational} (nonnegative : 0 ≤ budget)
    (bounded : ∀ cell ∈ cells,
      Data.Gaussian.Norm.Basic.normSq (primitive cell.finish - primitive cell.start - cell.integralSample) ≤ budget) :
    Data.Gaussian.Norm.Basic.normSq (Primitive.incrementSum primitive (cells.take length) - (Basic.PathModel.mk
      (cells.take
      length)).integralSample) ≤
      (cells.length : Fraction.Rational)^2 * budget := by
  rw [← Primitive.errorTerms_sum]
  apply IncrementArea.sum_bound_of_length nonnegative
  · intro error member
    obtain ⟨cell, inCells, rfl⟩ := Map.mem_map.mp member
    exact bounded cell (List.mem_of_mem_take inCells)
  · rw [Primitive.errorTerms, Data.List.Map.length_map]
    rw [Data.List.Prefix.Take.length_take]
    change (if length ≤ cells.length then length else cells.length) ≤ cells.length
    by_cases ordered : length ≤ cells.length
    · rewrite [if_pos ordered]
      exact ordered
    · rewrite [if_neg ordered]
      exact Nat.le_refl _

end Purelib.CCL.Calculus.PathPrimitive

namespace Purelib.Riemann.Paths.PreparedPrimitivePaths

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (DirectPathChain)
variable {genus : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}

/-- Read the endpoint reached by an original ordered child prefix.

Zero length retains the supplied start; advancing follows actual child endpoints, and lengths beyond the list retain its
final reached endpoint. -/
@[expose] def prefixPoint (start : Gaussian) : List (CenteredEdge curve differential) → Nat → Gaussian
  | [], _ => start
  | _ :: _, 0 => start
  | head :: tail, length + 1 =>
      prefixPoint (head.edge.segment.pointAt head.edge.request.endpoint.parameter) tail length

open Purelib.Geometry.Path.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original primitive increment sum telescopes along each retained direct-chain prefix.

The exact original start and actual child-prefix endpoint determine the difference, including empty and overlong
prefixes. -/
theorem prefix_incrementSum (primitive : Gaussian → Gaussian)
    {children : List (CenteredEdge curve differential)} {start finish : Lifted.Basic.LiftedPoint 2}
    (chain : DirectPathChain children (start := start) (finish := finish)) (length : Nat) :
    Primitive.incrementSum primitive ((children.map CenteredEdge.model).take length) =
      primitive (prefixPoint start.coordinate children length) - primitive start.coordinate := by
  induction chain generalizing length with
  | nil point =>
    simp only [List.map_nil, List.take_nil, Primitive.incrementSum, prefixPoint, -eq_self, -iff_self]
    ring1
  | cons parent tail ih =>
    cases length with
    | zero =>
      simp only [List.take_zero, Primitive.incrementSum, prefixPoint, -eq_self, -iff_self]
      ring1
    | succ length =>
      simp only [List.map_cons, List.take_succ_cons, Primitive.incrementSum, prefixPoint, -eq_self, -iff_self]
      rw [ih]
      change primitive (parent.edge.point 1) - primitive (parent.edge.point 0) +
        (primitive (prefixPoint _ _ length) - primitive _) = _
      rw [parent.edge.point_one, parent.edge.point_zero]
      ring1

end Purelib.Riemann.Paths.PreparedPrimitivePaths

namespace Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request

open Purelib
open Purelib.Data.Rat
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.Riemann.Integration.PreparedModelAccuracy (Profile Request Coordinate)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {profile : Profile parent} {target : Coordinate}

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
open Purelib.Riemann.Readings in
/-- Every original prepared prefix satisfies the retained primitive comparison error formula.

The nonnegative target, actual model and endpoint containment retain the original dyadic count cancellation and separate
remainder/coefficient terms. -/
theorem primitive_prefix_error_le (request : Request profile target) (positive : 0 ≤ target)
    (patch : PreparedPatch parent) {index : Nat}
    (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator differential))
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1)) (length : Nat) :
    Data.Gaussian.Norm.Basic.normSq (Primitive.incrementSum model.primitive.value.eval
        ((request.block.children.map CenteredEdge.model).take length) -
      (Basic.PathModel.mk ((request.block.children.map CenteredEdge.model).take length)).integralSample) ≤
        2 * model.primitive.remainderBound * movement parent * Geometric.Basic.quarterRadius (movement parent)
          request.block.depth +
          (4 * Bounds.Box.denseEvalNormBound (differentialNumerator differential) (patch.neighborhood count).box *
            Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale index + 40 * target) * movement
              parent := by
  let numerator := Bounds.Box.denseEvalNormBound (differentialNumerator differential) (patch.neighborhood count).box
  let distance := Geometric.Basic.quarterRadius (movement parent) request.block.depth
  let coefficient := 4 * numerator * Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale index +
    40 * target
  have numeratorNonnegative : 0 ≤ numerator :=
    (Bounds.Box.denseHornerNormBounds_nonneg (differentialNumerator differential) (patch.neighborhood count).box).1
  have distanceNonnegative : 0 ≤ distance :=
    Geometric.Basic.quarterRadius_nonneg (PreparedPrimitiveRequests.movement_nonnegative parent) _
  have coefficientNonnegative : 0 ≤ coefficient := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      numeratorNonnegative)
      (Geometric.Basic.quarterRadius_nonneg (patch.neighborhood count).inverseErrorScale_positive.le index))
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) positive)
  have nonnegative : 0 ≤ 2 * model.primitive.remainderBound * distance^2 + coefficient * distance :=
    add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
      (by decide +kernel) model.primitive.remainderBound_nonnegative)
      (Fraction.Order.Arithmetic.pow_nonneg_direct distanceNonnegative 2))
      (Fraction.Order.Arithmetic.mul_nonneg_direct coefficientNonnegative distanceNonnegative)
  have starts := PreparedPrimitivePaths.block_starts_inside request.block (patch.neighborhood count).box
    (patch.start_inside count) finishInside
  have finishes := PreparedPrimitivePaths.block_finishes_inside request.block (patch.neighborhood count).box
    (patch.start_inside count) finishInside
  have bounded := UniformPreparedPrimitives.children_bounded
    patch model request.block.roots numerator target distance
  have estimate := CCL.Calculus.PathPrimitive.prefix_error_le model.primitive.value.eval
    (request.block.children.map CenteredEdge.model) length nonnegative (by
      intro cell member
      obtain ⟨child, inChildren, rfl⟩ := Map.mem_map.mp member
      have numeratorLe := Bounds.Box.normSq_eval_le_denseEvalNormBound
        (differentialNumerator differential) (starts child inChildren)
      rw [Norm.Basic.normSq_eq_canonical] at numeratorLe
      have scalar := bounded child inChildren (starts child inChildren) (finishes child inChildren) numeratorLe
        (request.child_error inChildren) (PreparedPrimitivePaths.block_movement_le request.block inChildren)
      rw [← Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar)
  rw [Data.List.Map.length_map, request.block.childCount] at estimate
  have cancel := Geometric.DyadicCount.dyadic_count_cancel (movement parent) request.block.depth
  have identity : (((2 ^ request.block.depth : Nat) : Coordinate)^2 *
      (2 * model.primitive.remainderBound * distance^2 + coefficient * distance)) =
        2 * model.primitive.remainderBound * movement parent * distance + coefficient * movement parent := by
    calc
      _ = (2 * model.primitive.remainderBound * distance + coefficient) *
        (((2 ^ request.block.depth : Nat) : Coordinate) *
          (((2 ^ request.block.depth : Nat) : Coordinate) * distance)) := by ring1
      _ = _ := by rw [cancel]; ring1
  exact estimate.trans_eq identity

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Paths in
/-- The original primitive value at a retained prefix vertex satisfies the numerical prefix bound.

The exact direct-chain telescoping identity identifies that vertex without changing the underlying child list or model.
-/
theorem primitive_vertex_error_le (request : Request profile target) (positive : 0 ≤ target)
    (patch : PreparedPatch parent) {index : Nat}
    (model : PrimitiveModel (patch.neighborhood count) index (differentialNumerator differential))
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1)) (length : Nat) :
    Data.Gaussian.Norm.Basic.normSq (model.primitive.value.eval
        (PreparedPrimitivePaths.prefixPoint (parent.edge.segment.pointAt parent.edge.left.parameter)
          request.block.children length) - model.primitive.value.eval (parent.edge.point 0) -
      (Basic.PathModel.mk ((request.block.children.map CenteredEdge.model).take length)).integralSample) ≤
        2 * model.primitive.remainderBound * movement parent * Geometric.Basic.quarterRadius (movement parent)
          request.block.depth +
          (4 * Bounds.Box.denseEvalNormBound (differentialNumerator differential) (patch.neighborhood count).box *
            Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale index + 40 * target) * movement
              parent := by
  have bounded := primitive_prefix_error_le request positive patch model finishInside length
  rw [PreparedPrimitivePaths.prefix_incrementSum _ request.block.chain length] at bounded
  rw [parent.edge.point_zero]
  exact bounded

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
/-- Read the retained comparison bound at any original prepared prefix vertex. -/
theorem PrimitiveComparison.vertex_error_le {request : Request profile target} {index : Nat}
    (comparison : PrimitiveComparison request count index) (positive : 0 ≤ target) (length : Nat) :
    Data.Gaussian.Norm.Basic.normSq (comparison.2.1.primitive.value.eval
        (PreparedPrimitivePaths.prefixPoint (parent.edge.segment.pointAt parent.edge.left.parameter)
          request.block.children length) - comparison.2.1.primitive.value.eval (parent.edge.point 0) -
      (Basic.PathModel.mk ((request.block.children.map CenteredEdge.model).take length)).integralSample) ≤
        comparison.2.2.bound := by
  rw [comparison.2.2.bound_eq]
  exact primitive_vertex_error_le request positive comparison.1.patch comparison.2.1
    comparison.1.finishInside length

end Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request
