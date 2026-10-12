module
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Paths.PathArea
import Purelib.Riemann.Paths.PreparedNestedDyadicPaths

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths
import Purelib.Integration.Path.IncrementArea
public import Purelib.Riemann.Readings.PreparedDyadicPrimitiveArea
import Purelib.Integration.Path.Dyadic.DyadicAreaRefinement
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Integration.PreparedConstantModels
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.List.Membership
import Purelib.Data.Nat.Subtraction
open Purelib.Data.List

open Purelib.Data.Nat

@[expose] public section

/-! Full per-parent primitive traces at two dyadic depths. The parent-total
polygon is retained; only its identical copies cancel in the difference. -/
namespace Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Integration.Path.BoundaryRibbon (Coordinate Gaussian)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)
open Purelib.Riemann.Readings.PreparedDyadicPrimitiveArea (dyadicPrimitivePath refinementAreaPairs_dyadic)
open Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea (refinement_trace_bound)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (remainderMaximum coefficientMaximum)
open Purelib.Integration.Path.IncrementArea (traceArea)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {source :
  Differential genus} {target :
  Coordinate}

open Purelib.Integration.Path in
/-- A shared squared-slope bound for each original requested primitive along its parent parameter interval.

For parameters between zero and one, squared primitive displacement is bounded by the retained slope times squared
parameter displacement; every parent request keeps its own original model. -/
def PrimitiveSlopeBound (slope : BoundaryRibbon.Coordinate) : ∀ {parents : List (CenteredEdge curve source)},
    RequestedParents count target parents → Prop
  | _, .nil => True
  | parent :: _, .cons request tail =>
      (∀ first last : BoundaryRibbon.Coordinate, 0 ≤ first ∧ first ≤ 1 → 0 ≤ last ∧ last ≤ 1 →
        normSq (request.request.model.primitive.value.eval (parent.edge.point last) -
          request.request.model.primitive.value.eval (parent.edge.point first)) ≤ slope * (last - first) ^ 2) ∧
      PrimitiveSlopeBound slope tail

open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- Concatenate the original requested primitive paths at their individually retained block depths. -/
def preparedPrimitivePath : ∀ {parents : List (CenteredEdge curve source)},
    RequestedParents count target parents → List BoundaryRibbon.Gaussian
  | _, .nil => []
  | parent :: _, .cons request tail =>
      DyadicPrimitivePaths.dyadicIncrements (fun parameter => request.request.model.primitive.value.eval
        (parent.edge.point parameter))
        request.request.block.depth 0 1 ++ preparedPrimitivePath tail

/-- The maximum of zero and the original requests' selected dyadic block depths. -/
def preparedDepthMaximum : ∀ {parents : List (CenteredEdge curve source)},
    RequestedParents count target parents → Nat
  | _, .nil => 0
  | _, .cons request tail => max request.request.block.depth (preparedDepthMaximum tail)

/-- Each original requested block depth lies between the retained lower and upper depths. -/
def PreparedDepthBounds (lower upper : Nat) : ∀ {parents : List (CenteredEdge curve source)},
    RequestedParents count target parents → Prop
  | _, .nil => True
  | _, .cons request tail =>
      (lower ≤ request.request.block.depth ∧ request.request.block.depth ≤ upper) ∧ PreparedDepthBounds lower upper tail

open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- The ordered differences between shared-depth and individually prepared primitive areas. -/
private def areaErrors (scheduled : Nat) : ∀ {parents : List (CenteredEdge curve source)},
    RequestedParents count target parents → List BoundaryRibbon.Gaussian
  | _, .nil => []
  | parent :: _, .cons request tail =>
      let value := fun parameter => request.request.model.primitive.value.eval (parent.edge.point parameter)
      (DyadicBoundaryRibbon.dyadicArea value scheduled 0 1 - DyadicBoundaryRibbon.dyadicArea value
        request.request.block.depth 0 1) :: areaErrors scheduled tail

/-- There is exactly one retained area-resampling error for each original parent. -/
private theorem areaErrors_length {parents : List (CenteredEdge curve source)}
    (requests : RequestedParents count target parents) (scheduled : Nat) :
    (areaErrors scheduled requests).length = parents.length := by
  induction requests with
  | nil => rfl
  | cons request tail ih => exact congrArg Nat.succ ih

open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- Changing a single primitive path's dyadic depth changes trace area by its exact dyadic-area difference. -/
private theorem trace_difference (value : BoundaryRibbon.Coordinate → BoundaryRibbon.Gaussian) (start :
  BoundaryRibbon.Gaussian) (first second : Nat) :
    IncrementArea.traceArea start (DyadicPrimitivePaths.dyadicIncrements value first 0 1) - IncrementArea.traceArea
      start (DyadicPrimitivePaths.dyadicIncrements value second 0 1) =
      DyadicBoundaryRibbon.dyadicArea value first 0 1 - DyadicBoundaryRibbon.dyadicArea value second 0 1 := by
  have left := DyadicPrimitivePaths.traceArea_dyadicIncrements value first 0 1
  have right := DyadicPrimitivePaths.traceArea_dyadicIncrements value second 0 1
  rw [IncrementArea.traceArea_eq, DyadicPrimitivePaths.dyadicIncrements_sum] at left right
  rw [IncrementArea.traceArea_eq, IncrementArea.traceArea_eq,
    DyadicPrimitivePaths.dyadicIncrements_sum, DyadicPrimitivePaths.dyadicIncrements_sum, ← left, ← right]
  ring1

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
open Purelib.Integration.Path.Dyadic in
/-- The full original trace-resampling difference equals the sum of its retained per-parent area errors. -/
private theorem trace_difference_eq {parents : List (CenteredEdge curve source)}
    (requests : RequestedParents count target parents) (scheduled : Nat) (start : BoundaryRibbon.Gaussian) :
    IncrementArea.traceArea start (dyadicPrimitivePath scheduled requests) - IncrementArea.traceArea start
      (preparedPrimitivePath requests) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (areaErrors scheduled requests) := by
  induction requests generalizing start with
  | nil => change (0 : BoundaryRibbon.Gaussian) - 0 = 0; ring1
  | cons request tail ih =>
      rw [dyadicPrimitivePath, preparedPrimitivePath, IncrementArea.traceArea_append, IncrementArea.traceArea_append,
        DyadicPrimitivePaths.dyadicIncrements_sum, DyadicPrimitivePaths.dyadicIncrements_sum]
      rw [show ∀ a b c d : BoundaryRibbon.Gaussian, a + b - (c + d) = (a - c) + (b - d) from fun _ _ _ _ => by ring1,
        trace_difference, ih]
      rfl

section
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Path.Dyadic in
/-- Every original area-resampling error meets the quarter-radius bound at the retained minimum depth.

The shared scheduled depth is above each actual prepared depth, and the same nonnegative slope bounds every original
requested primitive. -/
private theorem areaErrors_bounded {parents : List (CenteredEdge curve source)}
    (requests : RequestedParents count target parents) {slope : BoundaryRibbon.Coordinate} (nonnegative : 0 ≤ slope)
    (bounded : PrimitiveSlopeBound slope requests) {minimum scheduled : Nat}
    (depths : PreparedDepthBounds minimum scheduled requests) :
    ∀ error ∈ areaErrors scheduled requests, normSq error ≤ Geometric.Basic.quarterRadius (4 * slope ^ 2) minimum := by
  induction requests with
  | nil => intro error member; cases member
  | @cons parent _ request tail ih =>
      intro error member
      rcases Membership.mem_cons.mp member with equal | member
      · subst error
        have slopeBounds : ∀ first last : Fraction.Rational, 0 ≤ first ∧ first ≤ 1 → 0 ≤ last ∧ last ≤ 1 →
            Data.Gaussian.Norm.Basic.normSq
              (request.request.model.primitive.value.eval (parent.edge.point last) -
                request.request.model.primitive.value.eval (parent.edge.point first)) ≤ slope * (last - first) ^ 2 := by
          intro first last firstInside lastInside
          have scalar := bounded.1 first last firstInside lastInside
          simpa only [Norm.Basic.normSq_eq_canonical] using scalar
        have bound := DyadicAreaRefinement.dyadicArea_refinement_bound
          (fun parameter => request.request.model.primitive.value.eval (parent.edge.point parameter)) nonnegative
            slopeBounds
          request.request.block.depth (scheduled - request.request.block.depth)
          (first := 0) (last := 1) ⟨le_rfl, by decide⟩ ⟨by decide, le_rfl⟩ (by decide)
        rw [Subtraction.add_sub_of_le depths.1.2, (show (1 : Fraction.Rational) - 0 = 1 by decide +kernel), one_pow,
          Fraction.Field.mul_one_direct] at bound
        have scalar := bound.trans (quarterRadius_antitone
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : BoundaryRibbon.Coordinate) ≤ 4)
            (Fraction.Order.Arithmetic.sq_nonneg_direct slope)) depths.1.1)
        simpa only [Norm.Basic.normSq_eq_canonical] using scalar
      · exact ih bounded.2 depths.2 error member

/-- Bound the original prepared-path trace change under uniform resampling.

The squared original parent count scales the quarter-radius error determined by the same slope and minimum prepared
depth; the starting point is preserved. -/
theorem preparedPrimitivePath_refinement_bound {parents : List (CenteredEdge curve source)}
    (requests : RequestedParents count target parents) {slope : BoundaryRibbon.Coordinate} (nonnegative : 0 ≤ slope)
    (bounded : PrimitiveSlopeBound slope requests) {minimum scheduled : Nat}
    (depths : PreparedDepthBounds minimum scheduled requests) (start : BoundaryRibbon.Gaussian) :
    normSq (IncrementArea.traceArea start (dyadicPrimitivePath scheduled requests) - IncrementArea.traceArea start
      (preparedPrimitivePath requests)) ≤
      (parents.length : BoundaryRibbon.Coordinate) ^ 2 * Geometric.Basic.quarterRadius (4 * slope ^ 2) minimum := by
  rw [trace_difference_eq]
  have bound := Norm.Sum.Bounds.normSq_sum_le (areaErrors scheduled requests)
    (Geometric.Basic.quarterRadius (4 * slope ^ 2) minimum) (by
      intro value member
      have scalar := areaErrors_bounded requests nonnegative bounded depths value member
      simpa only [Norm.Basic.normSq_eq_canonical] using scalar)
  rw [areaErrors_length] at bound
  have scalar : Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (areaErrors scheduled
    requests)) ≤
      (parents.length : Fraction.Rational) ^ 2 * Geometric.Basic.quarterRadius (4 * slope ^ 2) minimum :=
    bound.trans_eq (by ring1)
  simpa only [Norm.Basic.normSq_eq_canonical] using scalar

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
open Purelib.Riemann.RootContinuation in
/-- Bound the original prepared primitive trace against its retained refined integral trace.

The estimate keeps the model/allowance error, start-point contribution and prepared-depth resampling charge separate
before applying the exact outer factor two. -/
theorem refinement_trace_resampling_bound {parents children : List (CenteredEdge curve source)}
    (requests : RequestedParents count target parents)
    (refinement : PreparedSubedgeRootQueries.RootSubedgeRefinement parents children)
    {minimum scheduled : Nat} (depths : PreparedDepthBounds minimum scheduled requests)
    (paths : PreparedNestedDyadicPaths.DyadicPaths scheduled refinement)
    {slope distance sampleBound : BoundaryRibbon.Coordinate} (slopeNonnegative : 0 ≤ slope)
    (bounded : PrimitiveSlopeBound slope requests) (distanceNonnegative : 0 ≤ distance)
    (sampleNonnegative : 0 ≤ sampleBound)
    (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance)
    (samples : (children.length : BoundaryRibbon.Coordinate) * Norm.Sum.Basic.gaussianNormSqSum
      (PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model))) ≤ sampleBound)
    (start : BoundaryRibbon.Gaussian) :
    let error := (remainderMaximum requests * distance + coefficientMaximum requests) *
      PreparedRefinementMovement.movementMass children +
      (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).aggregateAllowance
    normSq (IncrementArea.traceArea start (preparedPrimitivePath requests) -
      IncrementArea.traceArea start (PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model)))) ≤
      2 * (64 * error * (sampleBound + error) + 8 * normSq start * error +
        (parents.length : BoundaryRibbon.Coordinate) ^ 2 * Geometric.Basic.quarterRadius (4 * slope ^ 2) minimum) := by
  have model := refinement_trace_bound requests refinement start distanceNonnegative sampleNonnegative movements samples
  rw [refinementAreaPairs_dyadic requests refinement paths] at model
  have resampling := preparedPrimitivePath_refinement_bound requests slopeNonnegative bounded depths start
  have split : IncrementArea.traceArea start (preparedPrimitivePath requests) -
      IncrementArea.traceArea start (PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model))) =
      (IncrementArea.traceArea start (dyadicPrimitivePath scheduled requests) -
        IncrementArea.traceArea start (PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model)))) -
      (IncrementArea.traceArea start (dyadicPrimitivePath scheduled requests) - IncrementArea.traceArea start
        (preparedPrimitivePath requests)) := by ring1
  rw [split]
  have triangle := Norm.Bounds.normSq_sub_le_two
    (IncrementArea.traceArea start (dyadicPrimitivePath scheduled requests) -
      IncrementArea.traceArea start (PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model))))
    (IncrementArea.traceArea start (dyadicPrimitivePath scheduled requests) -
      IncrementArea.traceArea start (preparedPrimitivePath requests))
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  exact triangle.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct model
      resampling) (by decide : (0 : BoundaryRibbon.Coordinate) ≤ 2))

end

end Purelib.Riemann.Integration.PreparedDyadicPrimitiveResampling

