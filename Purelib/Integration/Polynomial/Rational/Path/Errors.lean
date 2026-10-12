module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Rational.Cell.Basic
import Purelib.Integration.Polynomial.Rational.Path.Basic
public import Purelib.Integration.Polynomial.Rational.Path.Allowance
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Mathlib.Order.Basic
import Purelib.Integration.Polynomial.Rational.Cell.Allowance

open Purelib.Integration.Polynomial.Rational.Cell.Basic (CellModel)

section
@[expose] public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Polynomial.Rational.Path.Basic
namespace PathModel

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
set_option backward.match.sparseCases false in
/-- Sum cell displacements times the corresponding error entries in their original paired order.

The recursion stops when either input list ends; validity separately certifies matching lengths. -/
def weightedErrorSum : List
  CellModel → List Basic.Canonical → Basic.Canonical
  | cell :: cells, error :: errors =>
      cell.displacement * error + weightedErrorSum cells
        errors
  | _, _ => 0

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
set_option backward.match.sparseCases false in
/-- A list of errors matching the cell list exactly, with each squared norm below its own local allowance.

The empty lists are valid together; a nonempty pair retains its head bound and tail validity. Every mismatched-length
case is false. -/
def ErrorsValid : List CellModel
  → List Basic.Canonical → Prop
  | [], [] => True
  | cell :: cells, error :: errors =>
      Basic.Canonical.normSq error ≤ cell.localAllowance ∧
        ErrorsValid cells errors
  | _, _ => False

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
/-- Valid per-cell errors bound the squared norm of their displacement-weighted sum by the exact aggregate allowance.

Each error is controlled by its own original cell allowance. The proof follows the retained list order and the
doubled-tail recurrence, without replacing the aggregate budget by an unordered sum. -/
theorem weightedErrorSum_le : ∀ (cells : List
  CellModel)
    (errors : List Basic.Canonical), ErrorsValid cells errors →
      Basic.Canonical.normSq (weightedErrorSum cells errors) ≤
        (Rational.Path.Basic.PathModel.mk cells).aggregateAllowance
  | [], [], _valid => by
      change Basic.Canonical.normSq (0 : Basic.Canonical) ≤ 0
      rewrite [Basic.Canonical.normSq_zero]
      exact Fraction.Order.Basic.le_refl 0
  | [], _ :: _, valid => False.elim valid
  | _ :: _, [], valid => False.elim valid
  | cell :: cells, error :: errors, valid => by
      rcases valid with ⟨errorBound, remainingValid⟩
      change
        Basic.Canonical.normSq
            (cell.displacement * error + weightedErrorSum cells errors) ≤
          2 * (cell.weightedAllowance +
            (Rational.Path.Basic.PathModel.mk cells).aggregateAllowance)
      have scalar := Norm.Bounds.normSq_add_le_two (cell.displacement * error)
        (weightedErrorSum cells errors)
      rw [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical] at scalar
      exact scalar.trans
        (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct (cell.weighted_error_le errorBound)
            (weightedErrorSum_le cells errors
              remainingValid))
          (by decide))
end PathModel

end Purelib.Integration.Polynomial.Rational.Path.Basic

end
