module

import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Errors
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Integration.Polynomial.Gaussian

public section

/-!
# Constant-cell path comparison

Each retained child coefficient carries its exact difference from the common
reference. Displacement agreement relates the resulting sample and weighted error.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path

open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Polynomial.Ascending

set_option backward.match.sparseCases false
section PathModel

/-! ## Constant-cell partition comparison -/

namespace Basic.PathModel

/-- Sum the retained cell displacements in their original order. -/
@[expose] def displacementSum (cells : List
  Basic.CellModel) : Basic.Canonical :=
  cells.foldr (fun cell total => cell.displacement + total) 0

end Basic.PathModel

namespace Basic.PathModel

/-- The empty cell list has zero displacement sum. -/
@[simp] theorem displacementSum_nil :
  displacementSum [] = 0 := rfl

end Basic.PathModel

namespace Basic.PathModel

/-- A nonempty displacement sum is its head displacement plus the retained tail sum. -/
@[simp] theorem displacementSum_cons (cell :
  Basic.CellModel)
    (cells : List Basic.CellModel) :
    displacementSum (cell :: cells) =
      cell.displacement + displacementSum cells := rfl

end Basic.PathModel

namespace Basic.PathModel

set_option genInjectivity false in
/-- An ordered constant-cell comparison against one retained reference coefficient.

Every cell retains its own coefficient, exact difference from the reference and certified error bound, with indices
preserving the paired cell and error lists. -/
inductive ConstantComparison (reference :
  Basic.Canonical) :
    List Basic.CellModel -> List Basic.Canonical -> Type
  /-- The empty path and error list form a constant comparison. -/ | nil :
    ConstantComparison reference [] []
  /-- Prepend a certified constant cell and its exact bounded reference error to the retained comparison. -/ | cons
    {cell : Basic.CellModel} {cells : List Basic.CellModel}
      {errors : List Basic.Canonical}
      (coefficient error : Basic.Canonical)
      (polynomial_eq : cell.polynomial =
        Gaussian.Basic.constant coefficient)
      (difference_eq : coefficient - reference = error)
      (error_le : Basic.Canonical.normSq error <= cell.localAllowance)
      (remaining : ConstantComparison reference cells
        errors) :
      ConstantComparison reference (cell :: cells) (error
        :: errors)

constructive_injectivity ConstantComparison

end Basic.PathModel

namespace Basic.PathModel.ConstantComparison.cons

end Basic.PathModel.ConstantComparison.cons

namespace Basic.PathModel.ConstantComparison.cons

end Basic.PathModel.ConstantComparison.cons

namespace Basic.PathModel.ConstantComparison

/-- The retained constant comparison supplies valid paired local errors. -/
theorem errorsValid {reference : Basic.Canonical} :
    forall {cells : List Basic.CellModel} {errors : List Basic.Canonical},
      Basic.PathModel.ConstantComparison reference cells errors -> Basic.PathModel.ErrorsValid cells errors
  | [], [], .nil => True.intro
  | _ :: _, _ :: _, .cons _ _ _ _ error_le remaining =>
      ⟨error_le,
        errorsValid
        remaining⟩

/-- The constant comparison splits the exact path sample into reference displacement and retained weighted error. -/
theorem integralSample_eq_reference_add_error {reference : Basic.Canonical} :
    forall {cells : List Basic.CellModel} {errors : List Basic.Canonical},
      (comparison : Basic.PathModel.ConstantComparison reference cells errors) ->
      (Basic.PathModel.mk cells).integralSample =
        Basic.PathModel.displacementSum cells * reference + Basic.PathModel.weightedErrorSum cells errors
  | cells, errors, comparison => by
      induction comparison with
      | nil =>
          apply Basic.ext <;>
            simp only [Basic.PathModel.integralSample, List.foldr_nil,
              Basic.PathModel.displacementSum,
              Basic.zero_mul,
              Basic.PathModel.weightedErrorSum, Basic.add_re, Basic.add_im, Basic.zero_re, Basic.zero_im] <;> ring1
      | @cons cell cells errors coefficient error polynomial_eq difference_eq
          error_le remaining inductionHypothesis =>
          have coefficientIdentity : coefficient = reference + error := by
            apply Basic.ext
            · have realIdentity := congrArg
                Basic.re difference_eq
              change coefficient.re = reference.re + error.re
              simp only [Basic.sub_re] at realIdentity
              change coefficient.re - reference.re = error.re at realIdentity
              rw [← realIdentity]
              ring1
            · have imaginaryIdentity := congrArg
                Basic.im difference_eq
              change coefficient.im = reference.im + error.im
              simp only [Basic.sub_im] at imaginaryIdentity
              change coefficient.im - reference.im = error.im at imaginaryIdentity
              rw [← imaginaryIdentity]
              ring1
          rw [Basic.PathModel.integralSample, List.foldr_cons,
            Cell.Basic.CellModel.integralSample_constant cell coefficient polynomial_eq]
          change cell.displacement * coefficient +
              (Basic.PathModel.mk cells).integralSample =
            Basic.PathModel.displacementSum (cell :: cells) * reference +
              Basic.PathModel.weightedErrorSum (cell :: cells) (error :: errors)
          rw [inductionHypothesis]
          simp only [Basic.PathModel.displacementSum_cons, Basic.PathModel.weightedErrorSum]
          rw [coefficientIdentity]
          apply Basic.ext <;>
            simp only [Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1

end Basic.PathModel.ConstantComparison

namespace Basic.PathModel

set_option genInjectivity false in
/-- A constant parent and ordered child path with exact coefficient comparisons and displacement agreement.

The original parent, child cells and error list remain linked through their polynomial and displacement equations. -/
structure ConstantPartitionCertificate (parent :
  Basic.CellModel)
    (children : Basic.PathModel) where
  /-- The retained reference coefficient of the original constant parent. -/ reference : Basic.Canonical
  /-- The original parent polynomial is the exact retained reference constant. -/ parent_polynomial_eq :
    parent.polynomial =
    Gaussian.Basic.constant reference
  /-- The ordered retained child coefficient errors. -/ errors : List Basic.Canonical
  /-- The exact paired constant comparison for the retained child cells and errors. -/ comparison :
    ConstantComparison reference children.cells errors
  /-- The retained child displacement sum equals the original parent displacement. -/ displacement_eq :
    displacementSum children.cells = parent.displacement

constructive_injectivity ConstantPartitionCertificate

end Basic.PathModel

namespace Basic.PathModel.ConstantPartitionCertificate.mk

end Basic.PathModel.ConstantPartitionCertificate.mk

namespace Basic.PathModel.ConstantPartitionCertificate.mk

end Basic.PathModel.ConstantPartitionCertificate.mk

namespace ConstantComparison.PathModel.ConstantPartitionCertificate

/-- The exact child-minus-parent integral sample equals the retained weighted error sum. -/
theorem integral_difference_eq {parent : Basic.CellModel} {children : Basic.PathModel}
    (certificate : Basic.PathModel.ConstantPartitionCertificate parent children) :
    children.integralSample - parent.integralSample =
      Basic.PathModel.weightedErrorSum children.cells certificate.errors := by
  rw [(Basic.PathModel.ConstantComparison.integralSample_eq_reference_add_error certificate.comparison),
    Cell.Basic.CellModel.integralSample_constant parent certificate.reference
      certificate.parent_polynomial_eq,
    certificate.displacement_eq]
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1

/-- The squared child-minus-parent sample difference meets the retained children's aggregate allowance. -/
theorem integral_difference_le {parent : Basic.CellModel} {children : Basic.PathModel}
    (certificate : Basic.PathModel.ConstantPartitionCertificate parent children) :
    Basic.Canonical.normSq (children.integralSample - parent.integralSample) <=
      children.aggregateAllowance := by
  rw [(integral_difference_eq certificate)]
  exact Basic.PathModel.weightedErrorSum_le children.cells certificate.errors
    (Basic.PathModel.ConstantComparison.errorsValid certificate.comparison)

end ConstantComparison.PathModel.ConstantPartitionCertificate
end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path

end
