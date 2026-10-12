module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Data.Rat.Fraction.Order.Basic

public section

/-!
# Displacement-weighted path errors

Paired finite cell and error lists retain their ordering and local error bounds.
Their weighted sums are bounded by the original path aggregate allowance.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Data.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Data.Rat

set_option backward.match.sparseCases false
namespace PathModel

/-- Sum paired cell-displacement times error entries, stopping when either retained list ends. -/
@[expose] def weightedErrorSum : List
  Basic.CellModel -> List Basic.Canonical -> Basic.Canonical
  | cell :: cells, error :: errors =>
      cell.displacement * error + weightedErrorSum cells
        errors
  | _, _ => 0

/-- Read paired displacement-weighted error terms in their original list order. -/
@[expose] def weightedErrorTerms : List
  Basic.CellModel -> List Basic.Canonical -> List Basic.Canonical
  | cell :: cells, error :: errors =>
      cell.displacement * error :: weightedErrorTerms cells
        errors
  | _, _ => []

/-- Each retained cell has exactly one paired error whose squared norm meets that cell's local allowance. -/
@[expose] def ErrorsValid : List Basic.CellModel ->
  List Basic.Canonical -> Prop
  | [], [] => True
  | cell :: cells, error :: errors =>
      Basic.Canonical.normSq error <= cell.localAllowance ∧
        ErrorsValid cells errors
  | _, _ => False

/-- Summing the retained weighted terms equals the recursive weighted error sum. -/
theorem gaussianSum_weightedErrorTerms (cells : List
  Basic.CellModel)
    (errors : List Basic.Canonical) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (weightedErrorTerms cells errors) = weightedErrorSum cells errors := by
  induction cells generalizing errors with
  | nil => cases errors <;> rfl
  | cons cell cells inductionHypothesis =>
      cases errors with
      | nil => rfl
      | cons error errors =>
          simp only [weightedErrorTerms,
            Data.Gaussian.Norm.Sum.Basic.gaussianSum, weightedErrorSum]
          rw [inductionHypothesis]

/-- A valid paired error list gives exactly one weighted term per retained cell. -/
theorem weightedErrorTerms_length : forall (cells :
  List Basic.CellModel)
    (errors : List Basic.Canonical), ErrorsValid cells errors ->
      (weightedErrorTerms cells errors).length = cells.length
  | [], [], _ => rfl
  | [], _ :: _, valid => by exact False.elim valid
  | _ :: _, [], valid => by exact False.elim valid
  | cell :: cells, error :: errors, valid => by
      rcases valid with ⟨errorBound, remainingValid⟩
      simp only [weightedErrorTerms, List.length_cons]
      exact congrArg Nat.succ
        (weightedErrorTerms_length cells errors
          remainingValid)

/-- The sum of squared weighted errors is bounded by the retained path's total weighted allowance.

A valid pairing supplies each head error bound and the original remaining pairing. Direct rational addition combines the
head estimate with the retained tail estimate. -/
theorem gaussianNormSqSum_weightedErrorTerms_le :
    forall (cells : List Basic.CellModel) (errors : List Basic.Canonical),
      ErrorsValid cells errors ->
      Norm.Sum.Basic.gaussianNormSqSum
          (weightedErrorTerms cells errors) <=
        (Basic.PathModel.mk cells).totalWeightedAllowance
  | [], [], _ => Purelib.Data.Rat.Fraction.Order.Basic.le_refl _
  | [], _ :: _, valid => by exact False.elim valid
  | _ :: _, [], valid => by exact False.elim valid
  | cell :: cells, error :: errors, valid => by
      rcases valid with ⟨errorBound, remainingValid⟩
      simp only [weightedErrorTerms,
        Norm.Sum.Basic.gaussianNormSqSum,
        Basic.PathModel.totalWeightedAllowance, List.foldr_cons]
      apply Purelib.Data.Rat.Fraction.Order.Arithmetic.add_le_add_direct
      · exact cell.weighted_error_le errorBound
      · exact gaussianNormSqSum_weightedErrorTerms_le cells
          errors
          remainingValid

/-- Valid cellwise errors bound the squared norm of the weighted error sum by the retained path's aggregate allowance.

The estimate retains the exact cell count and the separate displacement-weighted local allowances. -/
theorem weightedErrorSum_le : forall (cells : List
  Basic.CellModel)
    (errors : List Basic.Canonical), ErrorsValid cells errors ->
      Basic.Canonical.normSq (weightedErrorSum cells errors) <=
        (Basic.PathModel.mk cells).aggregateAllowance
  | cells, errors, valid => by
      rw [← gaussianSum_weightedErrorTerms cells errors]
      calc
        Basic.Canonical.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum
            (weightedErrorTerms cells errors)) <=
            ((weightedErrorTerms cells errors).length : Fraction.Rational) *
              Norm.Sum.Basic.gaussianNormSqSum
                (weightedErrorTerms cells errors) :=
          Norm.Sum.Basic.normSq_gaussianSum_le _
        _ = (cells.length : Fraction.Rational) *
              Norm.Sum.Basic.gaussianNormSqSum
                (weightedErrorTerms cells errors) := by
          rw [weightedErrorTerms_length cells errors valid]
        _ <= (cells.length : Fraction.Rational) *
              (Basic.PathModel.mk cells).totalWeightedAllowance :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (gaussianNormSqSum_weightedErrorTerms_le cells errors valid)
            (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le cells.length))
        _ = (Basic.PathModel.mk cells).aggregateAllowance := rfl
end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path.Basic

end
