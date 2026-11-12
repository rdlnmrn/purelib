module

public import Purelib.Integration.Program.Gaussian.Concatenation
public import Purelib.Integration.Polynomial.Gaussian.Path.Concatenation
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Internally bounded concatenation of equally resolved integral programs -/

public section

namespace Purelib.Integration.Program.Gaussian.Basic.RefinementProgram

open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Path

/-- Concatenate both original model sequences, deriving the aggregate bound from their equal finite cell counts.

The returned models retain the original ordered cells. Their samples add the
two original samples, and the existing program constructor supplies the
combined geometric error and magnitude bounds without a caller-supplied
allowance certificate.
-/
@[expose] def concatOfEqualCounts (first second : RefinementProgram)
    (count : ∀ index, (first.model index).cells.length = (second.model index).cells.length) : RefinementProgram :=
  first.concat second
    { aggregate_le := by
        intro index
        rewrite [Basic.PathModel.aggregateAllowance_concat_of_length_eq _ _ (count index)]
        apply (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Arithmetic.add_le_add_direct (first.modelAllowance_le index)
            (second.modelAllowance_le index)) (by decide +kernel : (0 : Fraction.Rational) ≤ 2)).trans_eq
        rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
          Geometric.Basic.quarterRadius_eq_mul_pow]
        ring1 }

/-- Read the same two original cached models in their exact concatenation order. -/
theorem concatOfEqualCounts_model (first second : RefinementProgram)
    (count : ∀ index, (first.model index).cells.length = (second.model index).cells.length) (index : Nat) :
    (first.concatOfEqualCounts second count).model index = (first.model index).concat (second.model index) := rfl

/-- The constructed program retains the sum of the two actual original integral samples. -/
theorem concatOfEqualCounts_sample (first second : RefinementProgram)
    (count : ∀ index, (first.model index).cells.length = (second.model index).cells.length) (index : Nat) :
    ((first.concatOfEqualCounts second count).model index).integralSample =
      (first.model index).integralSample + (second.model index).integralSample :=
  Basic.PathModel.integralSample_concat _ _

end Purelib.Integration.Program.Gaussian.Basic.RefinementProgram
