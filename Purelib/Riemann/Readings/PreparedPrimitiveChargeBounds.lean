module
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
public import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
public import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Separate polynomial, spatial and prepared-model error charges

The retained polynomial bank gives finite maxima for the Taylor remainder
and inverse-root coefficient error.  All child-count dependence is absorbed
by the count-weighted movement mass and the existing model allowance.  This
keeps polynomial accuracy separate from spatial subdivision accuracy.
-/

namespace Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds

open Purelib.Data.Rat
open Purelib.Data.List

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge RootSubedgeBlock RootSubedgeRefinement)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementSum movementMass movementMass_eq)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained primitive error charges. -/
abbrev Coordinate := Fraction.Rational

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus} {target : Coordinate}

open Purelib.Approximation.Rational in
/-- Four times the retained numerator bound and inverse-error quarter-radius. -/
@[expose] def localCoefficient {parent : CenteredEdge curve differential} (request : LocalRequest parent count target) :
  Coordinate :=
  4 * request.request.numeratorBound * Geometric.Basic.quarterRadius request.neighborhood.inverseErrorScale
    request.request.index

/-- The maximum of zero and twice each original requested primitive remainder bound. -/
@[expose] def remainderMaximum : {parents : List (CenteredEdge curve differential)} → RequestedParents count target
  parents → Coordinate
  | _, .nil => 0
  | _, .cons request tail => max (2 * request.request.model.primitive.remainderBound) (remainderMaximum tail)

/-- The maximum of zero and the original requests' local inverse-error coefficients. -/
@[expose] def coefficientMaximum : {parents : List (CenteredEdge curve differential)} → RequestedParents count target
  parents → Coordinate
  | _, .nil => 0
  | _, .cons request tail => max (localCoefficient request) (coefficientMaximum tail)

/-- The retained primitive remainder maximum is nonnegative.

The empty request bank contributes zero. Each original request extends the
retained maximum while keeping the nonnegative tail below it. -/
theorem remainderMaximum_nonnegative : ∀ {parents : List (CenteredEdge curve differential)} (requests : RequestedParents
  count target parents),
    0 ≤ remainderMaximum requests
  | _, .nil => le_rfl
  | _, .cons _ tail => (remainderMaximum_nonnegative tail).trans (Fraction.Order.Basic.le_max_right _ _)

/-- The retained inverse-error coefficient maximum is nonnegative.

The empty request bank contributes zero. Each original coefficient extends
the retained maximum while preserving the nonnegative tail bound. -/
theorem coefficientMaximum_nonnegative : ∀ {parents : List (CenteredEdge curve differential)} (requests :
  RequestedParents count target parents),
    0 ≤ coefficientMaximum requests
  | _, .nil => le_rfl
  | _, .cons _ tail => (coefficientMaximum_nonnegative tail).trans (Fraction.Order.Basic.le_max_right _ _)

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Riemann.Integration in
/-- The original child weighted allowance equals sixteen times its model error and squared movement. -/
private theorem weightedAllowance_eq (child : CenteredEdge curve differential) :
    child.model.weightedAllowance = child.edge.pointMovement * (16 * child.edge.modelErrorAllowance) := by
  unfold PreparedSubdivisionModelCore.CenteredEdge.model
    Basic.CellModel.weightedAllowance
    Basic.CellModel.displacement
    PreparedConstantModels.PreparedEdge.centeredModel PreparedConstantModels.PreparedEdge.pointMovement
  rw [Norm.Basic.normSq_eq_canonical]

/-- The retained child charge from remainder, linear movement and five-halves weighted allowance.

The remainder multiplies squared movement, the coefficient multiplies movement, and the allowance term retains the
original centered child model. -/
@[expose] def charge (remainder coefficient : Coordinate) (child : CenteredEdge curve differential) : Coordinate :=
  remainder * child.edge.pointMovement ^ 2 + coefficient * child.edge.pointMovement + (5 / 2) *
    child.model.weightedAllowance

/-- Sum the retained child charges in their original list order. -/
@[expose] def chargeSum (remainder coefficient : Coordinate) : List (CenteredEdge curve differential) → Coordinate
  | [] => 0
  | child :: children => charge remainder coefficient child + chargeSum remainder coefficient children

/-- Child charges add across the original list concatenation. -/
private theorem chargeSum_append (remainder coefficient : Coordinate) (first second : List (CenteredEdge curve
  differential)) :
    chargeSum remainder coefficient (first ++ second) = chargeSum remainder coefficient first + chargeSum remainder
      coefficient second := by
  induction first with
  | nil => change chargeSum remainder coefficient second = 0 + chargeSum remainder coefficient second; ring1
  | cons child children ih => simp only [List.cons_append, chargeSum, ih]; ring1

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A compatible child's original primitive error charge is bounded by supplied uniform coefficients.

The retained root-subedge witness supplies neighborhood membership; the original numerator and model-error bounds yield
the exact remainder and five-halves allowance terms. -/
private theorem childCharge_le {parent child : CenteredEdge curve differential} (request : LocalRequest parent count
  target)
    (relation : RootSubedge parent child) {remainder coefficient : Coordinate}
    (rUpper : 2 * request.request.model.primitive.remainderBound ≤ remainder)
    (cUpper : localCoefficient request ≤ coefficient) :
      Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.childCharge request child ≤ charge remainder
      coefficient child := by
  have coefficientLe : 4 * normSq ((PreparedPrimitiveSamples.differentialNumerator differential).eval (child.edge.point
    0)) *
      Geometric.Basic.quarterRadius request.neighborhood.inverseErrorScale request.request.index ≤ coefficient :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (request.request.numerator_le _ (Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.child_inside
          request relation 0 child.edge.baseInside)) (by decide))
      (Geometric.Basic.quarterRadius_nonneg request.neighborhood.inverseErrorScale_positive.le _)).trans cUpper
  have main := add_le_add
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct rUpper (Fraction.Order.Arithmetic.sq_nonneg_direct
      child.edge.pointMovement))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientLe (Norm.Basic.normSq_nonneg
      (child.edge.point 1 - child.edge.point 0)))
  calc
    _ = (2 * request.request.model.primitive.remainderBound * child.edge.pointMovement ^ 2 +
      (4 * normSq ((PreparedPrimitiveSamples.differentialNumerator differential).eval (child.edge.point 0)) *
        Geometric.Basic.quarterRadius request.neighborhood.inverseErrorScale request.request.index) *
          child.edge.pointMovement) +
          40 * child.edge.modelErrorAllowance * child.edge.pointMovement := by
      unfold Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.childCharge; ring1
    _ ≤ (remainder * child.edge.pointMovement ^ 2 + coefficient * child.edge.pointMovement) +
          40 * child.edge.modelErrorAllowance * child.edge.pointMovement := add_le_add main le_rfl
    _ = _ := by
      rw [charge, weightedAllowance_eq, show (40 : Coordinate) = (5 / 2) * 16 by decide +kernel]
      ring1

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original child-block primitive errors have squared-norm sum bounded by the retained charge sum. -/
private theorem localErrors_le {parent : CenteredEdge curve differential} (request : LocalRequest parent count target)
    {children : List (CenteredEdge curve differential)} (roots : RootSubedgeBlock parent children)
    {remainder coefficient : Coordinate}
    (rUpper : 2 * request.request.model.primitive.remainderBound ≤ remainder)
    (cUpper : localCoefficient request ≤ coefficient) :
    Norm.Sum.Basic.gaussianNormSqSum (Primitive.errorTerms request.request.model.primitive.value.eval
      (children.map CenteredEdge.model)) ≤ chargeSum remainder coefficient children := by
  induction roots with
  | nil => exact le_rfl
  | cons head tail ih =>
      exact add_le_add
        ((Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.child_error_le request head).trans
        (childCharge_le request head rUpper cUpper)) ih

section
open Purelib.Data.Gaussian
/-- The ordered Gaussian sum is additive across list concatenation. -/
private theorem gaussianSum_append (first second : List Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (first ++ second) = Data.Gaussian.Norm.Sum.Basic.gaussianSum first +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum second := by
  induction first with
  | nil =>
      change Data.Gaussian.Norm.Sum.Basic.gaussianSum second = 0 + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        second; ring1
  | cons head tail ih => simp only [List.cons_append, Data.Gaussian.Norm.Sum.Basic.gaussianSum, ih]; ring1

/-- The Gaussian squared-norm sum is additive across list concatenation. -/
private theorem gaussianNormSqSum_append (first second : List Basic.Canonical) :
    Norm.Sum.Basic.gaussianNormSqSum (first ++ second) = Norm.Sum.Basic.gaussianNormSqSum first +
      Norm.Sum.Basic.gaussianNormSqSum second := by
  induction first with
  | nil => change Norm.Sum.Basic.gaussianNormSqSum second = 0 + Norm.Sum.Basic.gaussianNormSqSum second; ring1
  | cons head tail ih => simp only [List.cons_append, Norm.Sum.Basic.gaussianNormSqSum, ih]; ring1

end

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The ordered original child primitive errors for each retained parent request. -/
private def cellErrors : ∀ {parents children : List (CenteredEdge curve differential)},
    RequestedParents count target parents → RootSubedgeRefinement parents children → List Basic.Canonical
  | _, _, .nil, .nil => []
  | _, _, .cons request tail, .cons (block := block) _ _ remaining =>
      Primitive.errorTerms request.request.model.primitive.value.eval (block.map CenteredEdge.model) ++ cellErrors tail
        remaining

open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The retained error list has exactly one entry for each original child cell.

Each retained parent block contributes the original child-model error list.
Concatenation preserves the block lengths and original child order. -/
private theorem cellErrors_length : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children),
    (cellErrors requests refinement).length = children.length
  | _, _, .nil, .nil => rfl
  | _, _, .cons _ tail, .cons _ _ remaining => by
      simp only [cellErrors, Append.length_append, Primitive.errorTerms, Map.length_map, cellErrors_length tail
        remaining, -eq_self, -iff_self]
      rfl

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
/-- The retained error sum is the original requested primitive increment sum minus the child integral sample.

The original root-subedge chain identifies each parent increment with its
ordered child increments. Concatenation retains every signed error occurrence. -/
private theorem cellErrors_sum : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children),
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (cellErrors requests refinement) = Data.Gaussian.Norm.Sum.Basic.gaussianSum
      requests.increments -
      (Basic.PathModel.mk (children.map CenteredEdge.model)).integralSample
  | _, _, .nil, .nil => by change (0 : Basic.Canonical) = 0 - 0; ring1
  | parent :: _, _, .cons request tail, .cons chain _ remaining => by
      rw [cellErrors, gaussianSum_append, Primitive.errorTerms_sum,
        PreparedPrimitivePaths.incrementSum_eq _ chain, cellErrors_sum tail remaining]
      rw [← parent.edge.point_one, ← parent.edge.point_zero]
      simp only [RequestedParents.increments, Data.Gaussian.Norm.Sum.Basic.gaussianSum, Map.map_append,
        Basic.PathModel.integralSample_mk_append]
      ring1

open Purelib.Data.Gaussian in
/-- Uniform original request maxima bound the full refinement's squared-error sum by its retained charges.

Each retained parent block uses the same remainder and coefficient maxima.
The recursive tail carries those bounds through the unchanged child list. -/
private theorem cellErrors_le : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children)
    {remainder coefficient : Coordinate}, remainderMaximum requests ≤ remainder → coefficientMaximum requests ≤
      coefficient →
    Norm.Sum.Basic.gaussianNormSqSum (cellErrors requests refinement) ≤ chargeSum remainder coefficient children
  | _, _, .nil, .nil, _, _, _, _ => le_rfl
  | _, _, .cons request tail, .cons _ roots remaining, _, _, rUpper, cUpper => by
      rw [cellErrors, gaussianNormSqSum_append, chargeSum_append]
      exact add_le_add
        (localErrors_le request roots ((Fraction.Order.Basic.le_max_left _ _).trans rUpper)
          ((Fraction.Order.Basic.le_max_left _ _).trans cUpper))
        (cellErrors_le tail remaining ((Fraction.Order.Basic.le_max_right _ _).trans rUpper)
          ((Fraction.Order.Basic.le_max_right _ _).trans cUpper))

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Path
/-- A uniform child movement bound controls the charge sum by movement sum and total weighted allowance. -/
private theorem chargeSum_le {remainder coefficient distance : Coordinate} (rNonneg : 0 ≤ remainder)
    (children : List (CenteredEdge curve differential))
    (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance) :
    chargeSum remainder coefficient children ≤ (remainder * distance + coefficient) * movementSum children +
      (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).totalWeightedAllowance := by
  induction children with
  | nil =>
      change (0 : Coordinate) ≤ _ * 0 + (5 / 2) * 0
      rw [Fraction.Field.mul_zero_direct, Fraction.Field.mul_zero_direct]
      decide
  | cons child children ih =>
      have square : child.edge.pointMovement ^ 2 ≤ distance * child.edge.pointMovement := by
        have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (movements child (List.mem_cons_self ..)) (Norm.Basic.normSq_nonneg (child.edge.point 1 - child.edge.point 0))
        exact (show child.edge.pointMovement ^ 2 = child.edge.pointMovement * child.edge.pointMovement by
          ring1).trans_le scaled
      have head : charge remainder coefficient child ≤
          (remainder * distance + coefficient) * child.edge.pointMovement + (5 / 2) * child.model.weightedAllowance :=
            by
        have bounded : remainder * child.edge.pointMovement ^ 2 + coefficient * child.edge.pointMovement + (5 / 2) *
          child.model.weightedAllowance ≤
            remainder * (distance * child.edge.pointMovement) + coefficient * child.edge.pointMovement + (5 / 2) *
              child.model.weightedAllowance :=
          add_le_add (add_le_add
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square rNonneg) le_rfl) le_rfl
        exact bounded.trans_eq (by ring1)
      have total := add_le_add head (ih fun other member => movements other (List.mem_cons_of_mem child member))
      exact total.trans_eq (by
        simp only [movementSum, List.map_cons, Basic.PathModel.totalWeightedAllowance, List.foldr_cons]
        ring1)

/-- Bound the total primitive-versus-integral error using retained movement mass and aggregate allowance.

The original request maxima and uniform child movement bound control the exact refined child list; the allowance
coefficient remains five halves. -/
theorem refinement_error_bound {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children)
    {distance : Coordinate} (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance) :
    normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum requests.increments - (Basic.PathModel.mk (children.map
      CenteredEdge.model)).integralSample) ≤
      (remainderMaximum requests * distance + coefficientMaximum requests) * movementMass children +
        (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).aggregateAllowance := by
  have charges := cellErrors_le requests refinement le_rfl le_rfl
  have errors := Norm.Sum.Basic.normSq_gaussianSum_le (cellErrors requests refinement)
  rw [cellErrors_sum, cellErrors_length] at errors
  have summed := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (charges.trans (chargeSum_le (coefficient := coefficientMaximum requests) (remainderMaximum_nonnegative requests)
      children movements))
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le children.length))
  exact (errors.trans summed).trans_eq (by
    rw [movementMass_eq, Basic.PathModel.aggregateAllowance]
    dsimp only [Basic.PathModel.cells]
    rw [Map.length_map]
    ring1)

end Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
