module

import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.ConstantComparison
import Purelib.Integration.Polynomial.Gaussian.Path.Errors
import Purelib.Integration.Polynomial.Gaussian.Path.Errors.Append
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Ordered constant-path refinements

Each parent retains a certified child block. Flattened errors and sample bounds
follow the original parent order and the exact appended child lists.
-/

section

open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Data.Gaussian

set_option backward.match.sparseCases false
section

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

set_option genInjectivity false in
/-- An ordered refinement pairing each constant parent with its retained certified child block.

The constructor indices retain the exact original parent list and flattened child order. -/
inductive ConstantPathRefinement :
    List Basic.CellModel -> List Basic.CellModel -> Type
  /-- The empty parent path refines to the empty child path. -/ | nil :
    ConstantPathRefinement [] []
  /-- Prepend the exact parent's certified child block to the retained remaining refinement. -/ | cons {parent :
    Basic.CellModel} {parents childCells children : List Basic.CellModel}
      (head : Basic.PathModel.ConstantPartitionCertificate parent (Basic.PathModel.mk childCells))
      (remaining : ConstantPathRefinement parents children)
        :
      ConstantPathRefinement (parent :: parents)
        (childCells ++ children)

constructive_injectivity Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel.ConstantPathRefinement

end Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

open Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel (ConstantPathRefinement)

section

namespace Purelib.Integration.Polynomial.Gaussian.Path.ConstantRefinement.PathModel.ConstantPathRefinement

/-- Flatten the retained block error lists in the same order as the original refinement. -/
@[expose] def errors {parents children : List Basic.CellModel}
    (refinement : ConstantPathRefinement parents children) : List Basic.Canonical :=
  match refinement with
  | .nil => []
  | .cons head remaining => head.errors ++
    (errors remaining)

/-- The refinement's flattened errors are valid for the exact retained child cells. -/
theorem errorsValid : forall {parents children : List Basic.CellModel}
    (refinement : ConstantPathRefinement parents children),
    Basic.PathModel.ErrorsValid children (errors refinement)
  | parents, children, refinement => by
      induction refinement with
      | nil => exact True.intro
      | cons head remaining inductionHypothesis =>
          exact Basic.PathModel.ErrorsValid.append (Basic.PathModel.ConstantComparison.errorsValid
            head.comparison)
            inductionHypothesis

/-- The exact child-minus-parent path sample equals the refinement's retained weighted error sum. -/
theorem integral_difference_eq : forall {parents children : List Basic.CellModel}
    (refinement : ConstantPathRefinement parents children),
    (Basic.PathModel.mk children).integralSample -
        (Basic.PathModel.mk parents).integralSample =
      Basic.PathModel.weightedErrorSum children (errors refinement)
  | parents, children, refinement => by
    induction refinement with
    | nil =>
      apply Basic.ext <;>
        simp only [Basic.PathModel.integralSample, List.foldr_nil, Basic.sub_re, Basic.sub_im,
          Basic.zero_re, Basic.zero_im, Basic.PathModel.weightedErrorSum] <;> ring1
    | @cons parent parents childCells children head remaining
        inductionHypothesis =>
      have childConcat :
          (Basic.PathModel.mk (childCells ++ children)).integralSample =
            (Basic.PathModel.mk childCells).integralSample +
              (Basic.PathModel.mk children).integralSample := by
        exact Basic.PathModel.integralSample_concat
          (Basic.PathModel.mk childCells) (Basic.PathModel.mk children)
      have headDifference := (ConstantComparison.PathModel.ConstantPartitionCertificate.integral_difference_eq head)
      have remainingDifference := inductionHypothesis
      have errorConcat := Basic.PathModel.weightedErrorSum_append childCells children
        head.errors (errors remaining)
          (Basic.PathModel.ConstantComparison.errorsValid head.comparison)
      rw [childConcat]
      change
        ((Basic.PathModel.mk childCells).integralSample +
            (Basic.PathModel.mk children).integralSample) -
          (parent.integralSample +
            (Basic.PathModel.mk parents).integralSample) =
        Basic.PathModel.weightedErrorSum (childCells ++ children)
          (head.errors ++ (errors remaining))
      rw [errorConcat]
      have differenceIdentity :
          ((Basic.PathModel.mk childCells).integralSample +
              (Basic.PathModel.mk children).integralSample) -
            (parent.integralSample +
              (Basic.PathModel.mk parents).integralSample) =
          ((Basic.PathModel.mk childCells).integralSample - parent.integralSample) +
            ((Basic.PathModel.mk children).integralSample -
              (Basic.PathModel.mk parents).integralSample) := by
        apply Basic.ext <;>
          simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im] <;> ring1
      rw [differenceIdentity, headDifference, remainingDifference]

/-- The squared sample difference meets the aggregate allowance of the exact retained child path. -/
theorem integral_difference_le {parents children : List Basic.CellModel}
    (refinement : ConstantPathRefinement parents children) :
    Basic.Canonical.normSq ((Basic.PathModel.mk children).integralSample -
        (Basic.PathModel.mk parents).integralSample) <=
      (Basic.PathModel.mk children).aggregateAllowance := by
  rw [(integral_difference_eq refinement)]
  exact Basic.PathModel.weightedErrorSum_le children (errors
    refinement)
    (errorsValid refinement)

end Purelib.Integration.Polynomial.Gaussian.Path.ConstantRefinement.PathModel.ConstantPathRefinement

end
end

end

end
