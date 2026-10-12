module
import Purelib.Algebra.FiniteSum.Rational.Squares
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore

public import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
public import Purelib.Riemann.Paths.PathArea
import Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Riemann.Integration.PreparedConstantModels
public import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Retained primitive areas on actual descendant cells

The primitive polynomial belongs to the retained ancestor. Every paired
integral belongs to an actual root-compatible descendant, with no uniform
mesh or equality to independently prepared children assumed. The area error
uses the same summed child charges as the primitive-total comparison.
-/

namespace Purelib.Riemann.Readings.PreparedNestedPrimitiveArea

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Algebra.FiniteSum.Rational.Squares (coordinateSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeBlock)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementSum)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds (localCoefficient)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)

open Purelib.Data.Rat in
/-- The rational coordinate carrier of the retained descendant error bounds. -/
private abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier of the retained primitive increments. -/
private abbrev Gaussian := Basic.Canonical

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data.Gaussian in
/-- Pair each original child's requested primitive increment with its exact integral sample. -/
def descendantPairs (request : LocalRequest parent count target) (children : List (CenteredEdge curve differential)) :
    List (Basic.Canonical × Basic.Canonical) :=
  children.map fun child =>
    (request.request.model.primitive.value.eval (child.edge.point 1) -
      request.request.model.primitive.value.eval (child.edge.point 0), child.model.integralSample)

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Paths in
/-- The retained second components are exactly the child path model's integral increments. -/
theorem descendantPairs_right (request : LocalRequest parent count target) (children : List (CenteredEdge curve
  differential)) :
    (descendantPairs request children).map Prod.snd =
      PathArea.increments (Basic.PathModel.mk (children.map CenteredEdge.model)) := by
  induction children with
  | nil => rfl
  | cons child children ih => exact congrArg (child.model.integralSample :: ·) ih

open Purelib in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Riemann.Integration in
open Purelib.Riemann.Paths in
/-- The retained primitive increments telescope to the original parent request along its exact child chain. -/
theorem descendantPairs_left_total (request : LocalRequest parent count target)
    {children : List (CenteredEdge curve differential)}
    (chain : PreparedDirectDyadicRefinements.DirectPathChain children
      (start := ⟨parent.edge.segment.pointAt parent.edge.left.parameter, parent.edge.sheet⟩)
      (finish := ⟨parent.edge.segment.pointAt parent.edge.request.endpoint.parameter, parent.edge.sheet⟩)) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum ((descendantPairs request children).map Prod.fst) =
      Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.increment request := by
  have readback (cells : List (CenteredEdge curve differential)) :
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((descendantPairs request cells).map Prod.fst) =
        Primitive.incrementSum request.request.model.primitive.value.eval (cells.map CenteredEdge.model) := by
    induction cells with
    | nil => rfl
    | cons cell cells ih =>
        exact congrArg (fun tail => request.request.model.primitive.value.eval (cell.edge.point 1) -
          request.request.model.primitive.value.eval (cell.edge.point 0) + tail) ih
  have total := (readback children).trans (PreparedPrimitivePaths.incrementSum_eq _ chain)
  rw [← parent.edge.point_one, ← parent.edge.point_zero] at total
  exact total

open Purelib in
open Purelib.Algebra in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The original descendant paired errors have squared-norm sum bounded by their retained local charges. -/
private theorem descendant_errors (request : LocalRequest parent count target)
    {children : List (CenteredEdge curve differential)} (roots : RootSubedgeBlock parent children) :
    Norm.Sum.Basic.gaussianNormSqSum ((descendantPairs request children).map (fun pair => pair.1 - pair.2)) ≤
      FiniteSum.Rational.Squares.coordinateSum (children.map
        (Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.childCharge request)) := by
  induction roots with
  | nil => exact le_rfl
  | cons head tail ih =>
      simp only [descendantPairs, List.map_cons, Norm.Sum.Basic.gaussianNormSqSum,
        FiniteSum.Rational.Squares.coordinateSum]
      exact Fraction.Order.Arithmetic.add_le_add_direct
        (Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.child_error_le request head) ih

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Riemann.Integration in
/-- The original child weighted allowance equals sixteen times its model error and movement. -/
private theorem weightedAllowance_eq (child : CenteredEdge curve differential) :
    child.model.weightedAllowance = child.edge.pointMovement * (16 * child.edge.modelErrorAllowance) := by
  unfold PreparedSubdivisionModelCore.CenteredEdge.model
    Basic.CellModel.weightedAllowance
    Basic.CellModel.displacement
    PreparedConstantModels.PreparedEdge.centeredModel
    PreparedConstantModels.PreparedEdge.pointMovement
  rw [Norm.Basic.normSq_eq_canonical]

open Purelib in
open Purelib.Algebra in
open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The original descendant charges are bounded by movement sum and five-halves weighted allowance.

The exact root-subedge block supplies the neighborhood comparisons; the retained remainder and numerator coefficient
remain indexed by the same parent request. -/
private theorem charges_le (request : LocalRequest parent count target)
    {children : List (CenteredEdge curve differential)} (roots : RootSubedgeBlock parent children)
    {distance : Fraction.Rational} (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance) :
      FiniteSum.Rational.Squares.coordinateSum (children.map
        (Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.childCharge request)) ≤
      (2 * request.request.model.primitive.remainderBound * distance + localCoefficient request) * movementSum children
        +
        (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).totalWeightedAllowance := by
  induction roots with
  | nil =>
      change (0 : Fraction.Rational) ≤ _ * 0 + (5 / 2) * 0
      rw [Fraction.Field.mul_zero_direct, Fraction.Field.mul_zero_direct, _root_.zero_add]
  | @cons child children head tail ih =>
      have coefficientLe :
          4 * normSq ((PreparedPrimitiveSamples.differentialNumerator differential).eval (child.edge.point 0)) *
            Geometric.Basic.quarterRadius request.neighborhood.inverseErrorScale request.request.index ≤
              localCoefficient request :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (request.request.numerator_le _
              (Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.child_inside request head 0
              child.edge.baseInside)) (by decide))
          (Geometric.Basic.quarterRadius_nonneg request.neighborhood.inverseErrorScale_positive.le _)
      have pointNonnegative : 0 ≤ child.edge.pointMovement := Norm.Basic.normSq_nonneg (child.edge.point 1 -
        child.edge.point 0)
      have square : child.edge.pointMovement ^ 2 ≤ distance * child.edge.pointMovement :=
        (show child.edge.pointMovement ^ 2 = child.edge.pointMovement * child.edge.pointMovement by ring1).trans_le
          (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (movements child (List.mem_cons_self ..))
            pointNonnegative)
      have main := Fraction.Order.Arithmetic.add_le_add_direct
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square
          (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 2)
            request.request.model.primitive.remainderBound_nonnegative))
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct coefficientLe pointNonnegative)
      have childLe : Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.childCharge request child ≤
          (2 * request.request.model.primitive.remainderBound * distance + localCoefficient request) *
            child.edge.pointMovement +
            (5 / 2) * child.model.weightedAllowance := by
        rw [weightedAllowance_eq]
        have scaled := Fraction.Order.Arithmetic.add_le_add_direct main (le_rfl :
          40 * child.edge.modelErrorAllowance * child.edge.pointMovement ≤ 40 * child.edge.modelErrorAllowance *
            child.edge.pointMovement)
        exact (show Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.childCharge request child = _ by
          unfold Riemann.Comparison.PreparedNestedPrimitiveComparison.LocalRequest.childCharge; ring1).trans_le
            (scaled.trans_eq (by
          rw [show (5 / 2 : Fraction.Rational) * (child.edge.pointMovement * (16 * child.edge.modelErrorAllowance)) =
            ((5 / 2) * 16) * child.edge.pointMovement * child.edge.modelErrorAllowance by ring1,
            show (5 / 2 : Fraction.Rational) * 16 = 40 by decide +kernel]
          ring1))
      exact (Fraction.Order.Arithmetic.add_le_add_direct childLe
        (ih fun other member => movements other (List.mem_cons_of_mem child member))).trans_eq (by
          simp only [movementSum, List.map_cons, Basic.PathModel.totalWeightedAllowance, List.foldr_cons]
          ring1)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- Control the retained descendant paired-error sum by the original primitive remainder, movement and allowance bounds.
-/
theorem descendant_error_sum_bound (request : LocalRequest parent count target)
    {children : List (CenteredEdge curve differential)} (roots : RootSubedgeBlock parent children)
    {distance : Fraction.Rational} (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance) :
    Norm.Sum.Basic.gaussianNormSqSum ((descendantPairs request children).map (fun pair => pair.1 - pair.2)) ≤
      (2 * request.request.model.primitive.remainderBound * distance + localCoefficient request) * movementSum children
        +
        (5 / 2) * (Basic.PathModel.mk (children.map CenteredEdge.model)).totalWeightedAllowance :=
  (descendant_errors request roots).trans (charges_le request roots movements)

end Purelib.Riemann.Readings.PreparedNestedPrimitiveArea
