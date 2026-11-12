module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Primitive
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Data.Gaussian.Norm.Bounds

/-! # The original variable polynomial integral against a fixed scalar

The original cell, polynomial, displacement, observations and allowance are
unchanged. The scalar reference is used only in the finite integral proof;
it does not replace the source model or its operational observations.
-/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Primitive

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Polynomial.Ascending

/-- A uniform scalar-to-polynomial payment bounds the SAME original variable cell integral.

The finite primitive difference theorem is applied to the actual cell.
The auxiliary exact constant is a proof reference, with the same original
endpoints; the conclusion keeps the actual variable cell's integral sample.
-/
theorem integral_sub_coefficient_le (cell : Basic.CellModel) (coefficient : Canonical)
    (bound : Fraction.Rational)
    (bounded : ∀ parameter : Fraction.Rational, unitInterval.Contains parameter →
      Norm.Basic.normSq
        (coefficient - Gaussian.Evaluation.eval cell.polynomial ⟨parameter, 0⟩) ≤ bound) :
    Norm.Basic.normSq (cell.integralSample - cell.displacement * coefficient) ≤
      2 * bound * Norm.Basic.normSq cell.displacement := by
  let reference := Basic.CellModel.exact cell.start cell.finish (Gaussian.Basic.constant coefficient)
  have paid := integral_difference_le cell reference rfl rfl bound (by
    intro parameter inside
    change Norm.Basic.normSq (Gaussian.Evaluation.eval cell.polynomial ⟨parameter, 0⟩ -
      Gaussian.Evaluation.eval (Gaussian.Basic.constant coefficient) ⟨parameter, 0⟩) ≤ bound
    rewrite [Gaussian.Evaluation.eval_constant, Norm.Bounds.normSq_sub_symm]
    exact bounded parameter inside)
  have scalar := Basic.CellModel.integralSample_constant reference coefficient rfl
  change reference.integralSample = cell.displacement * coefficient at scalar
  rewrite [scalar] at paid
  exact paid

end Purelib.Integration.Polynomial.Gaussian.Cell.Primitive

end
