module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.ComparisonAllowance
public import Purelib.Integration.Polynomial.Gaussian.Path.Constant
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
public import Purelib.Integration.Polynomial.Gaussian.Path.ConstantRefinement
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
import Purelib.Data.List.Append
import Purelib.Data.List.Map

open Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel (ConstantCells)

public section

/-!
# Compatible constant-path refinements

Original parent and child lists retain their certified comparison blocks.
The comparison allowance controls the exact child-minus-parent sample.
-/

section

open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Data.Gaussian
open Purelib.Polynomial.Ascending
open Purelib.Data.Rat

set_option backward.match.sparseCases false
section

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

set_option genInjectivity false in
/-- An ordered constant-path refinement whose child blocks carry parent-child comparison allowances.

The original parent and child models remain fixed; each certificate names the comparison block for its actual parent. -/
inductive CompatibleConstantPathRefinement :
    List Basic.CellModel -> List Basic.CellModel -> Type
  /-- The empty paths form a compatible constant refinement. -/ | nil :
    CompatibleConstantPathRefinement [] []
  /-- Prepend the original parent's comparison-block certificate to the retained remaining refinement. -/ | cons {parent
    : Basic.CellModel} {parents childCells children : List Basic.CellModel}
      (head : Basic.PathModel.ConstantPartitionCertificate parent
        (Basic.PathModel.comparisonBlock parent (Basic.PathModel.mk childCells)))
      (remaining : CompatibleConstantPathRefinement parents
        children) :
      CompatibleConstantPathRefinement (parent :: parents)
        (childCells ++ children)

constructive_injectivity Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel.CompatibleConstantPathRefinement

end Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

open Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel (CompatibleConstantPathRefinement)

section

namespace Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement.PathModel.CompatibleConstantPathRefinement

/-- Construct the exact self-refinement of a retained constant-cell path using zero coefficient errors. -/
@[expose] def refl : forall {cells : List Basic.CellModel},
    ConstantCells cells -> CompatibleConstantPathRefinement cells cells
  | [], .nil => .nil
  | cell :: cells, .cons head tail =>
      @CompatibleConstantPathRefinement.cons cell cells [cell] cells
        { reference := head.coefficient
          parent_polynomial_eq := head.polynomial_eq
          errors := [0]
          comparison := .cons head.coefficient 0
            (by
              change cell.polynomial =
                Gaussian.Basic.constant head.coefficient
              exact head.polynomial_eq)
            (Basic.sub_self _)
            (by
              rw [Basic.Canonical.normSq_zero]
              change 0 <= Basic.PathModel.parentChildAllowance cell cell
              exact Basic.PathModel.parentChildAllowance_nonneg cell cell)
            .nil
          displacement_eq := by
            simp only [Basic.PathModel.comparisonBlock, List.map, Basic.PathModel.displacementSum_cons,
              Basic.PathModel.displacementSum_nil, Basic.PathModel.comparisonCell,
              Basic.CellModel.withAllowance_displacement]
            exact Basic.add_zero _ }

          (refl
          tail)

/-- The original child weighted allowance is bounded by its parent-child comparison allowance. -/
private theorem child_weightedAllowance_le_comparisonCell
    (parent child : Basic.CellModel) :
    child.weightedAllowance <=
      (Basic.PathModel.comparisonCell parent child).weightedAllowance := by
  have allowanceSumNonnegative :
      0 <= parent.localAllowance + child.localAllowance :=
    add_nonneg parent.localAllowance_nonneg child.localAllowance_nonneg
  have childAllowance_le : child.localAllowance <=
      Basic.PathModel.parentChildAllowance parent child := by
    unfold Basic.PathModel.parentChildAllowance
    calc
      child.localAllowance <=
          parent.localAllowance + child.localAllowance :=
        le_add_of_nonneg_left parent.localAllowance_nonneg
      _ <= (parent.localAllowance + child.localAllowance) +
          (parent.localAllowance + child.localAllowance) :=
        le_add_of_nonneg_right allowanceSumNonnegative
      _ = 2 * (parent.localAllowance + child.localAllowance) := by ring1
  unfold Basic.CellModel.weightedAllowance Basic.PathModel.comparisonCell Basic.CellModel.withAllowance
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    childAllowance_le (Basic.Canonical.normSq_nonneg child.displacement)

/-- Appending retained cell lists adds their exact total weighted allowances. -/
private theorem totalWeightedAllowance_append
    (first second : List Basic.CellModel) :
    (Basic.PathModel.mk (first ++ second)).totalWeightedAllowance =
      (Basic.PathModel.mk first).totalWeightedAllowance +
        (Basic.PathModel.mk second).totalWeightedAllowance := by
  induction first with
  | nil =>
      simp only [List.nil_append, Basic.PathModel.totalWeightedAllowance, List.foldr_nil]
      rw [_root_.zero_add]
  | cons cell remaining inductionHypothesis =>
      simp only [List.cons_append, Basic.PathModel.totalWeightedAllowance, List.foldr_cons]
      change
        (remaining ++ second).foldr
            (fun cell total => cell.weightedAllowance + total) 0 =
          remaining.foldr
              (fun cell total => cell.weightedAllowance + total) 0 +
            second.foldr
              (fun cell total => cell.weightedAllowance + total) 0 at inductionHypothesis
      rw [inductionHypothesis]
      ring1

/-- The retained child total weighted allowance is bounded by that of its parent comparison block. -/
private theorem totalWeightedAllowance_le_comparisonBlock
    (parent : Basic.CellModel) (children : List Basic.CellModel) :
    (Basic.PathModel.mk children).totalWeightedAllowance <=
      (Basic.PathModel.comparisonBlock parent (Basic.PathModel.mk children)).totalWeightedAllowance := by
  induction children with
  | nil => exact Purelib.Data.Rat.Fraction.Order.Basic.le_refl _
  | cons child remaining inductionHypothesis =>
      simp only [Basic.PathModel.totalWeightedAllowance, List.foldr_cons, Basic.PathModel.comparisonBlock,
        List.map_cons]
      exact Purelib.Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct
        (child_weightedAllowance_le_comparisonCell
          parent child)
        inductionHypothesis

/-- Flatten the exact comparison blocks in the original compatible refinement order. -/
@[expose] def comparisonCells : forall {parents children : List Basic.CellModel},
    CompatibleConstantPathRefinement parents children -> List Basic.CellModel
  | _, _, .nil => []
  | _, _, @CompatibleConstantPathRefinement.cons parent parents childCells
      children _head remaining =>
      (Basic.PathModel.comparisonBlock parent (Basic.PathModel.mk childCells)).cells ++

          comparisonCells
          remaining

/-- Retain the original block certificates as a constant refinement to the exact comparison cells. -/
@[expose] def toConstantPathRefinement : forall {parents children : List Basic.CellModel}
    (refinement : CompatibleConstantPathRefinement parents children),
    Basic.PathModel.ConstantPathRefinement parents
      (comparisonCells refinement)
  | _, _, .nil => .nil
  | _, _, .cons head remaining =>
      .cons head
        (toConstantPathRefinement
        remaining)

/-- The retained comparison cells preserve the original child path's exact integral sample. -/
theorem comparisonCells_integralSample :
    forall {parents children : List Basic.CellModel}
      (refinement : CompatibleConstantPathRefinement parents children),
      (Basic.PathModel.mk (comparisonCells
        refinement)).integralSample =
        (Basic.PathModel.mk children).integralSample
  | _, _, .nil => rfl
  | _, _, @CompatibleConstantPathRefinement.cons parent parents childCells
      children head remaining => by
      calc
        (Basic.PathModel.mk
            ((Basic.PathModel.comparisonBlock parent (Basic.PathModel.mk childCells)).cells ++
              (comparisonCells
                remaining))).integralSample =
            (Basic.PathModel.comparisonBlock parent
                (Basic.PathModel.mk childCells)).integralSample +
              (Basic.PathModel.mk (comparisonCells
                remaining)).integralSample :=
          Basic.PathModel.integralSample_concat
            (Basic.PathModel.comparisonBlock parent (Basic.PathModel.mk childCells))
            (Basic.PathModel.mk (comparisonCells
              remaining))
        _ = (Basic.PathModel.mk childCells).integralSample +
              (Basic.PathModel.mk children).integralSample := by
          rw [Basic.PathModel.comparisonBlock_integralSample,

              comparisonCells_integralSample
              remaining]
        _ = (Basic.PathModel.mk (childCells ++ children)).integralSample :=
          (Basic.PathModel.integralSample_concat (Basic.PathModel.mk childCells)
            (Basic.PathModel.mk children)).symm

/-- The retained comparison path has exactly the original child cell count.

Each comparison block retains exactly one cell per original child. The retained remainder certificate transports its
length equality through scalar natural addition. -/
@[simp] theorem comparisonCells_length :
    forall {parents children : List Basic.CellModel}
      (refinement : CompatibleConstantPathRefinement parents children),
      (comparisonCells refinement).length =
        children.length
  | _, _, .nil => rfl
  | _, _, @CompatibleConstantPathRefinement.cons parent parents childCells
      children head remaining => by
      change (((childCells.map (Basic.PathModel.comparisonCell parent)) ++
          comparisonCells remaining).length) =
        (childCells ++ children).length
      rewrite [Purelib.Data.List.Append.length_append, Purelib.Data.List.Append.length_append,
        Purelib.Data.List.Map.length_map,
        comparisonCells_length remaining]
      exact Eq.refl _

/-- Self-comparison has exactly four times the original total weighted allowance. -/
private theorem refl_comparisonCells_totalWeightedAllowance :
    forall {cells : List Basic.CellModel} (constant : ConstantCells cells),
      (Basic.PathModel.mk
        (comparisonCells
          (refl constant))).totalWeightedAllowance =
        4 * (Basic.PathModel.mk cells).totalWeightedAllowance
  | [], .nil => by
      unfold Basic.PathModel.totalWeightedAllowance
      rfl
  | cell :: cells, .cons head tail => by
      simp only [refl,
        comparisonCells,
        Basic.PathModel.comparisonBlock, List.map, List.singleton_append]
      change
        (Basic.PathModel.comparisonCell cell cell).weightedAllowance +
            (Basic.PathModel.mk
              (comparisonCells
                (refl tail))).totalWeightedAllowance =
          4 * (cell.weightedAllowance +
            (Basic.PathModel.mk cells).totalWeightedAllowance)
      rw
        [refl_comparisonCells_totalWeightedAllowance
        tail]
      unfold Basic.PathModel.comparisonCell Basic.CellModel.withAllowance Basic.CellModel.weightedAllowance
        Basic.CellModel.displacement Basic.PathModel.parentChildAllowance
      ring1

/-- The original children have no greater total weighted allowance than their retained comparison cells. -/
private theorem children_totalWeightedAllowance_le_comparisonCells :
    forall {parents children : List Basic.CellModel}
      (refinement : CompatibleConstantPathRefinement parents children),
      (Basic.PathModel.mk children).totalWeightedAllowance <=
        (Basic.PathModel.mk (comparisonCells
          refinement)).totalWeightedAllowance
  | _, _, .nil => Purelib.Data.Rat.Fraction.Order.Basic.le_refl _
  | _, _, @CompatibleConstantPathRefinement.cons parent parents childCells
      children head remaining => by
      change
        (Basic.PathModel.mk (childCells ++ children)).totalWeightedAllowance <=
          (Basic.PathModel.mk
            ((Basic.PathModel.comparisonBlock parent (Basic.PathModel.mk childCells)).cells ++
              (comparisonCells
                remaining))).totalWeightedAllowance
      rw [show
        (Basic.PathModel.mk (childCells ++ children)).totalWeightedAllowance =
          (Basic.PathModel.mk childCells).totalWeightedAllowance +
            (Basic.PathModel.mk children).totalWeightedAllowance from
        totalWeightedAllowance_append childCells
          children]
      rw [show
        (Basic.PathModel.mk
          ((Basic.PathModel.comparisonBlock parent (Basic.PathModel.mk childCells)).cells ++
            (comparisonCells
              remaining))).totalWeightedAllowance =
          (Basic.PathModel.comparisonBlock parent
              (Basic.PathModel.mk childCells)).totalWeightedAllowance +
            (Basic.PathModel.mk (comparisonCells
              remaining)).totalWeightedAllowance from
        totalWeightedAllowance_append _ _]
      exact Purelib.Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct
        (totalWeightedAllowance_le_comparisonBlock
          parent childCells)

          (children_totalWeightedAllowance_le_comparisonCells
          remaining)

/-- The aggregate allowance of the exact ordered comparison cells. -/
@[expose] def comparisonAllowance {parents children : List Basic.CellModel}
    (refinement : CompatibleConstantPathRefinement parents children) :
    Fraction.Rational :=
  (Basic.PathModel.mk (comparisonCells
    refinement)).aggregateAllowance

/-- The exact self-refinement comparison allowance is four times the original aggregate allowance. -/
theorem comparisonAllowance_refl_eq {cells : List Basic.CellModel}
    (constant : ConstantCells cells) :
    (comparisonAllowance
      (refl constant)) =
      4 * (Basic.PathModel.mk cells).aggregateAllowance := by
  unfold comparisonAllowance
    Basic.PathModel.aggregateAllowance
  rw [comparisonCells_length,
    refl_comparisonCells_totalWeightedAllowance
      constant]
  ring1

/-- The retained refinement comparison allowance is nonnegative. -/
theorem comparisonAllowance_nonneg {parents children : List Basic.CellModel}
    (refinement : CompatibleConstantPathRefinement parents children) :
    0 <= (comparisonAllowance refinement) :=
  (Basic.PathModel.mk (comparisonCells
    refinement)).aggregateAllowance_nonneg

/-- The original child path's aggregate allowance meets the retained comparison allowance. -/
theorem childAggregateAllowance_le_comparisonAllowance
    {parents children : List Basic.CellModel}
    (refinement : CompatibleConstantPathRefinement parents children) :
    (Basic.PathModel.mk children).aggregateAllowance <=
      (comparisonAllowance refinement) := by
  unfold Basic.PathModel.aggregateAllowance
    comparisonAllowance
  change (children.length : Fraction.Rational) *
      (Basic.PathModel.mk children).totalWeightedAllowance <=
    ((comparisonCells refinement).length :
      Fraction.Rational) *
      (Basic.PathModel.mk (comparisonCells
        refinement)).totalWeightedAllowance
  rw [(comparisonCells_length refinement)]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (children_totalWeightedAllowance_le_comparisonCells
      refinement)
    (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le children.length))

/-- The original child-minus-parent sample meets the exact compatible refinement's comparison allowance. -/
theorem integral_difference_le {parents children : List Basic.CellModel}
    (refinement : CompatibleConstantPathRefinement parents children) :
    Basic.Canonical.normSq ((Basic.PathModel.mk children).integralSample -
        (Basic.PathModel.mk parents).integralSample) <=
      (comparisonAllowance refinement) := by
  have bounded := ConstantRefinement.PathModel.ConstantPathRefinement.integral_difference_le
    (toConstantPathRefinement refinement)
  rw [(comparisonCells_integralSample
    refinement)] at bounded
  exact bounded

end Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement.PathModel.CompatibleConstantPathRefinement

end
end

end

end
