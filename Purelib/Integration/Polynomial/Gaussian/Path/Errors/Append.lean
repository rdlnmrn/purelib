module
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Errors
import Purelib.Tactic.Ring

public section

/-!
# Concatenating displacement-weighted errors

A valid first pairing retains every term of the second pairing when the cell and
error lists are appended. Both validity and exact weighted sums respect this order.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path

set_option backward.match.sparseCases false
namespace PathModel

/-- Appending two valid paired cell-error lists preserves their exact local error bounds and order. -/
theorem ErrorsValid.append : forall {firstCells
  secondCells : List Basic.CellModel}
    {firstErrors secondErrors : List Basic.Canonical},
    Basic.PathModel.ErrorsValid firstCells firstErrors ->
      Basic.PathModel.ErrorsValid secondCells secondErrors ->
        Basic.PathModel.ErrorsValid (firstCells ++ secondCells) (firstErrors ++ secondErrors)
  | firstCells, secondCells, firstErrors, secondErrors,
      firstValid, secondValid => by
    induction firstCells generalizing firstErrors with
    | nil =>
        cases firstErrors with
        | nil => exact secondValid
        | cons _ _ => exact False.elim firstValid
    | cons cell cells inductionHypothesis =>
        cases firstErrors with
        | nil => exact False.elim firstValid
        | cons error errors =>
            exact ⟨firstValid.1,
              inductionHypothesis errors firstValid.2⟩

/-- The weighted error of appended lists is the sum of their weighted errors when the first pairing is valid.

The first pairing certificate prevents truncation from discarding any of the retained second-list terms. -/
theorem weightedErrorSum_append : forall
    (firstCells secondCells : List Basic.CellModel)
    (firstErrors secondErrors : List Basic.Canonical),
    Basic.PathModel.ErrorsValid firstCells firstErrors ->
    Basic.PathModel.weightedErrorSum (firstCells ++ secondCells)
        (firstErrors ++ secondErrors) =
      Basic.PathModel.weightedErrorSum firstCells firstErrors +
        Basic.PathModel.weightedErrorSum secondCells secondErrors
  | firstCells, secondCells, firstErrors, secondErrors, valid => by
    induction firstCells generalizing firstErrors with
    | nil =>
        cases firstErrors with
        | nil =>
            change Basic.PathModel.weightedErrorSum secondCells secondErrors =
              0 + Basic.PathModel.weightedErrorSum secondCells secondErrors
            exact (Basic.zero_add _).symm
        | cons _ _ => exact False.elim valid
    | cons cell cells inductionHypothesis =>
        cases firstErrors with
        | nil => exact False.elim valid
        | cons error errors =>
            simp only [List.cons_append, Basic.PathModel.weightedErrorSum]
            rw [inductionHypothesis errors valid.2]
            apply Basic.ext <;>
              simp only [Basic.add_re, Basic.add_im] <;> ring1
end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path.Basic

end
