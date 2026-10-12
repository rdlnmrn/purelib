module
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction

public section

/-!
# Parent-child comparison allowances

Comparison cells retain the original child geometry and coefficient while
paying for both local allowances. Ordered blocks preserve exact integral samples.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic

open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Integration.Polynomial.Gaussian.Path

set_option backward.match.sparseCases false
namespace PathModel

/-! ## Parent--child comparison allowances

An independently sampled child coefficient cannot in general approach one
fixed rational parent sample using the child's semantic allowance alone.  A
constructive comparison instead pays for the uncertainty of both displayed
models.  The following layer records that honest allowance while retaining
the exact constant-partition algebra above. -/

/-- Twice the sum of the retained parent and child local allowances. -/
@[expose] def parentChildAllowance (parent child :
  Basic.CellModel) : Fraction.Rational :=
  2 * (parent.localAllowance + child.localAllowance)

/-- The parent-child comparison allowance is nonnegative. -/
theorem parentChildAllowance_nonneg (parent child :
  Basic.CellModel) :
    0 <= parentChildAllowance parent child := by
  unfold parentChildAllowance
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg parent.localAllowance_nonneg child.localAllowance_nonneg)

/-- Retain the child geometry and polynomial with the certified parent-child comparison allowance. -/
@[expose] def comparisonCell (parent child :
  Basic.CellModel) : Basic.CellModel :=
  child.withAllowance (parentChildAllowance parent child)
    (parentChildAllowance_nonneg parent child)

/-- Changing the comparison allowance preserves the child's exact integral sample. -/
@[simp] theorem comparisonCell_integralSample
  (parent child : Basic.CellModel) :
    (comparisonCell parent child).integralSample = child.integralSample := rfl

/-- Retain the ordered child path with each allowance replaced by its comparison allowance against the same parent. -/
@[expose] def comparisonBlock (parent :
  Basic.CellModel) (children : Basic.PathModel) : Basic.PathModel :=
  ⟨children.cells.map (comparisonCell parent)⟩

/-- The comparison block preserves the original ordered child path's exact integral sample.

Induction on the retained child list transports the tail sample equality through addition of the unchanged head sample.
Allowance replacement leaves each original coefficient and displacement unchanged. -/
theorem comparisonBlock_integralSample (parent :
  Basic.CellModel)
    (children : Basic.PathModel) :
    (comparisonBlock parent children).integralSample =
      children.integralSample := by
  unfold comparisonBlock Basic.PathModel.integralSample
  induction children.cells with
  | nil => rfl
  | cons child remaining inductionHypothesis =>
      change child.integralSample +
          (remaining.map (comparisonCell parent)).foldr
            (fun cell total => cell.integralSample + total) 0 =
        child.integralSample + remaining.foldr
            (fun cell total => cell.integralSample + total) 0
      exact congrArg (fun total => child.integralSample + total) inductionHypothesis
end PathModel

end Purelib.Integration.Polynomial.Gaussian.Path.Basic

end
