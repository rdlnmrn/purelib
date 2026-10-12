module
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Paths.PathArea

import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
public import Purelib.Riemann.Readings.PreparedNestedPrimitiveArea
import Purelib.Integration.Path.IncrementAreaMassComparison
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Complete retained primitive polygons on an actual refinement

Each ancestor keeps its own primitive. Concatenating the literal paired
increments retains the polygon of parent totals without a separate growing
parent-count loss. All estimates charge only the actual descendant models.
-/

namespace Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeRefinement)
open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents)
open Purelib.Riemann.Readings.PreparedNestedPrimitiveArea (descendantPairs descendantPairs_right
  descendantPairs_left_total descendant_error_sum_bound)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (remainderMaximum coefficientMaximum refinement_error_bound)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementSum movementSum_nonnegative movementMass
  movementMass_eq movementMass_nonnegative)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained primitive area bounds. -/
private abbrev Coordinate := Fraction.Rational

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus} {target : Purelib.Data.Rat.Fraction.Rational}

/-- Concatenate the original descendant primitive/integral pairs in parent-refinement order. -/
@[expose] def refinementAreaPairs : ∀ {parents children : List (CenteredEdge curve differential)},
    RequestedParents count target parents → RootSubedgeRefinement parents children → List (Gaussian × Gaussian)
  | _, _, .nil, .nil => []
  | _, _, .cons request tail, .cons (block := block) _ _ remaining =>
      descendantPairs request block ++ refinementAreaPairs tail remaining

open Purelib.Riemann.Readings in
/-- The retained refinement pair list has exactly the original child count. -/
theorem refinementAreaPairs_length : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children),
    (refinementAreaPairs requests refinement).length = children.length
  | _, _, .nil, .nil => rfl
  | _, _, .cons _ tail, .cons _ _ remaining => by
      rw [refinementAreaPairs, Purelib.Data.List.Append.length_append, PreparedNestedPrimitiveArea.descendantPairs,
        Purelib.Data.List.Map.length_map, refinementAreaPairs_length tail remaining,
          Purelib.Data.List.Append.length_append]

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
/-- The retained second components equal the original child model's integral increments. -/
theorem refinementAreaPairs_right : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children),
    (refinementAreaPairs requests refinement).map Prod.snd =
      PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model))
  | _, _, .nil, .nil => rfl
  | _, _, .cons request tail, .cons _ _ remaining => by
      rw [refinementAreaPairs, Purelib.Data.List.Map.map_append, descendantPairs_right request,
        refinementAreaPairs_right tail remaining]
      simp only [-eq_self, -iff_self, Purelib.Data.List.Map.map_append, PathArea.increments]
      rfl

open Purelib.Data.Gaussian in
open Purelib.Integration.Path in
/-- The original first-component total is the retained parent-request increment sum. -/
theorem refinementAreaPairs_left_total : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children),
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((refinementAreaPairs requests refinement).map Prod.fst) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments
  | _, _, .nil, .nil => rfl
  | _, _, .cons request tail, .cons chain _ remaining => by
      rw [refinementAreaPairs, Purelib.Data.List.Map.map_append, IncrementArea.sum_append,
        descendantPairs_left_total request chain, refinementAreaPairs_left_total tail remaining]
      rfl

open Purelib.Data.Gaussian in

/-- The original parent movement sum is additive across concatenated lists. -/
private theorem movementSum_append (first last : List (CenteredEdge curve differential)) :
    movementSum (first ++ last) = movementSum first + movementSum last := by
  induction first with
  | nil => change movementSum last = 0 + movementSum last; ring1
  | cons value first ih =>
      change value.edge.pointMovement + movementSum (first ++ last) = _
      rw [ih, movementSum]
      ring1

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original total weighted allowance is additive across concatenated child models. -/
private theorem allowance_append (first last : List (CenteredEdge curve differential)) :
    (Basic.PathModel.mk ((first ++ last).map CenteredEdge.model)).totalWeightedAllowance =
      (Basic.PathModel.mk (first.map CenteredEdge.model)).totalWeightedAllowance +
        (Basic.PathModel.mk (last.map CenteredEdge.model)).totalWeightedAllowance := by
  induction first with
  | nil =>
      change (Basic.PathModel.mk (last.map CenteredEdge.model)).totalWeightedAllowance =
        0 + (Basic.PathModel.mk (last.map CenteredEdge.model)).totalWeightedAllowance
      ring1
  | cons child first ih =>
      change child.model.weightedAllowance + (Basic.PathModel.mk ((first ++ last).map
        CenteredEdge.model)).totalWeightedAllowance = _
      rw [ih]
      change _ = (child.model.weightedAllowance + (Basic.PathModel.mk (first.map
        CenteredEdge.model)).totalWeightedAllowance) + _
      ring1

section
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Bound the original paired-error sum using uniform request maxima, movement and allowance. -/
private theorem errors_le : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children)
    {distance remainder coefficient : Fraction.Rational}, 0 ≤ distance → remainderMaximum requests ≤ remainder →
    coefficientMaximum requests ≤ coefficient →
    (∀ child ∈ children, child.edge.pointMovement ≤ distance) →
    Norm.Sum.Basic.gaussianNormSqSum ((refinementAreaPairs requests refinement).map (fun pair => pair.1 - pair.2)) ≤
      (remainder * distance + coefficient) * movementSum children +
        (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).totalWeightedAllowance
  | _, _, .nil, .nil, _, _, _, _, _, _, _ => by
      change (0 : Fraction.Rational) ≤ _ * 0 + (5 / 2) * 0
      rw [Fraction.Field.mul_zero_direct, Fraction.Field.mul_zero_direct, _root_.zero_add]
  | _, _, .cons request tail, .cons (block := block) _ roots remaining, _, _, _, distanceNonnegative, rUpper, cUpper,
    movements =>
    by
      have head := descendant_error_sum_bound request roots (fun child member => movements child (List.mem_append_left _
        member))
      have rate := Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct ((Purelib.Data.Rat.Fraction.Order.Basic.le_max_left
          _ _).trans rUpper) distanceNonnegative)
        ((Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _).trans cUpper)
      have headLe := head.trans (Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rate (movementSum_nonnegative block)) le_rfl)
      have tailLe := errors_le tail remaining distanceNonnegative
        ((Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _).trans rUpper)
          ((Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _).trans cUpper)
        (fun child member => movements child (List.mem_append_right _ member))
      rw [refinementAreaPairs, Purelib.Data.List.Map.map_append,
        Purelib.Data.Gaussian.Norm.Sum.Basic.gaussianNormSqSum_append]
      exact (Fraction.Order.Arithmetic.add_le_add_direct headLe tailLe).trans_eq (by
          rw [movementSum_append, allowance_append];
          ring1)

/-- Bound count-weighted paired errors by retained movement mass and aggregate allowance.

The exact original child count scales both the error sum and the movement/allowance quantities, preserving their shared
refinement owner. -/
theorem refinement_error_mass_bound {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children)
    {distance : Fraction.Rational} (distanceNonnegative : 0 ≤ distance)
    (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance) :
    (children.length : Fraction.Rational) *
      Norm.Sum.Basic.gaussianNormSqSum ((refinementAreaPairs requests refinement).map (fun pair => pair.1 - pair.2)) ≤
        (remainderMaximum requests * distance + coefficientMaximum requests) * movementMass children +
          (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).aggregateAllowance := by
  have countNonnegative : (0 : Fraction.Rational) ≤ children.length := Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le _)
  have errorBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (errors_le requests refinement distanceNonnegative le_rfl le_rfl movements) countNonnegative
  have errorEq : (children.length : Fraction.Rational) *
      ((remainderMaximum requests * distance + coefficientMaximum requests) * movementSum children +
        (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).totalWeightedAllowance) =
      (remainderMaximum requests * distance + coefficientMaximum requests) * movementMass children +
        (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).aggregateAllowance := by
    rw [movementMass_eq, Basic.PathModel.aggregateAllowance]
    dsimp only [Basic.PathModel.cells]
    rw [Purelib.Data.List.Map.length_map]
    ring1
  rw [errorEq] at errorBound
  exact errorBound

end

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Path
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Riemann.Paths
/-- The original primitive and integral path areas differ within the retained mass-error bound.

A nonnegative sample-mass bound and uniform child movement bound give the exact factor thirty-two times error times
sample-plus-error estimate. -/
theorem refinement_area_bound {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children)
    {distance sampleBound : Fraction.Rational} (distanceNonnegative : 0 ≤ distance) (sampleNonnegative : 0 ≤
      sampleBound)
    (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance)
    (bounded : (children.length : Fraction.Rational) *
      Norm.Sum.Basic.gaussianNormSqSum (PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model))) ≤
        sampleBound) :
    let error := (remainderMaximum requests * distance + coefficientMaximum requests) * movementMass children +
      (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).aggregateAllowance
    normSq (IncrementArea.pathArea ((refinementAreaPairs requests refinement).map Prod.fst) -
      IncrementArea.pathArea (PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model)))) ≤
        32 * error * (sampleBound + error) := by
  have countNonnegative : (0 : Fraction.Rational) ≤ children.length := Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le _)
  have errorBound := refinement_error_mass_bound requests refinement distanceNonnegative movements
  have errorsNonnegative : 0 ≤ Norm.Sum.Basic.gaussianNormSqSum ((refinementAreaPairs requests refinement).map (fun pair
    => pair.1 - pair.2)) := by
    generalize (refinementAreaPairs requests refinement).map (fun pair => pair.1 - pair.2) = values
    induction values with
    | nil => exact le_rfl
    | cons value values ih => exact add_nonneg (Basic.Canonical.normSq_nonneg value) ih
  rw [← refinementAreaPairs_right requests refinement, ← Norm.Basic.normSq_eq_canonical]
  apply IncrementAreaMassComparison.pathArea_difference_of_mass_bounds _
    ((Fraction.Order.Arithmetic.mul_nonneg_direct countNonnegative errorsNonnegative).trans errorBound)
    sampleNonnegative
  · rw [refinementAreaPairs_length]; exact errorBound
  · rw [refinementAreaPairs_length, refinementAreaPairs_right]
    exact bounded

/-- Bound primitive-versus-integral trace-area error at the retained starting point.

The path-area bound and original total-increment error supply the factor-sixty-four term and the separate
eight-times-start-norm boundary contribution. -/
theorem refinement_trace_bound {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children)
    (start : Gaussian) {distance sampleBound : Fraction.Rational}
    (distanceNonnegative : 0 ≤ distance) (sampleNonnegative : 0 ≤ sampleBound)
    (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance)
    (bounded : (children.length : Fraction.Rational) *
      Norm.Sum.Basic.gaussianNormSqSum (PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model))) ≤
        sampleBound) :
    let error := (remainderMaximum requests * distance + coefficientMaximum requests) * movementMass children +
      (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).aggregateAllowance
    normSq (IncrementArea.traceArea start ((refinementAreaPairs requests refinement).map Prod.fst) -
      IncrementArea.traceArea start (PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model)))) ≤
        64 * error * (sampleBound + error) + 8 * normSq start * error := by
  have areaBound := refinement_area_bound requests refinement distanceNonnegative sampleNonnegative movements bounded
  have totalBound := refinement_error_bound requests refinement movements
  rw [← refinementAreaPairs_left_total requests refinement, ← PathArea.increments_sum] at totalBound
  have ribbon := BoundaryRibbon.area_bound start
    (gaussianSum ((refinementAreaPairs requests refinement).map Prod.fst) -
      gaussianSum (PathArea.increments (PathModel.mk (children.map CenteredEdge.model))))
  simp only [-eq_self, -iff_self, Norm.Basic.normSq_eq_canonical] at ribbon
  have ribbon := ribbon.trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct totalBound
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (by decide : (0 : Fraction.Rational) ≤ 4) (Basic.Canonical.normSq_nonneg start)))
  have difference (left right : Gaussian) : BoundaryRibbon.area start left - BoundaryRibbon.area start right =
      BoundaryRibbon.area start (left - right) := by
    apply Basic.ext <;> simp only [-eq_self, -iff_self, BoundaryRibbon.area, Data.Gaussian.Basic.conj, Basic.sub_re,
      Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
  rw [IncrementArea.traceArea_eq, IncrementArea.traceArea_eq,
    show ∀ a b c d : Gaussian, a + b - (c + d) = (a - c) + (b - d) from fun _ _ _ _ => by ring1,
    difference]
  have scalar := Norm.Bounds.normSq_add_le_two
    (IncrementArea.pathArea ((refinementAreaPairs requests refinement).map Prod.fst) -
      IncrementArea.pathArea (PathArea.increments (PathModel.mk (children.map CenteredEdge.model))))
    (BoundaryRibbon.area start
      (gaussianSum ((refinementAreaPairs requests refinement).map Prod.fst) -
        gaussianSum (PathArea.increments (PathModel.mk (children.map CenteredEdge.model)))))
  simp only [-eq_self, -iff_self, Norm.Basic.normSq_eq_canonical] at scalar
  exact scalar.trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct areaBound
      ribbon) (by decide : (0 : Fraction.Rational) ≤ 2)).trans_eq (by ring1))

end Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea
