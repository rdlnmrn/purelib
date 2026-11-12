module

public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.List.Append
import Purelib.Algebra.NatCast
import Purelib.Tactic.Ring

/-! # Exact allowance arithmetic for concatenated original integration paths -/

public section

namespace Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel

open Purelib.Data.Rat

/-- Concatenation adds the original ordered displacement-weighted allowances. -/
theorem totalWeightedAllowance_concat (first second : PathModel) :
    (first.concat second).totalWeightedAllowance = first.totalWeightedAllowance + second.totalWeightedAllowance := by
  cases first with
  | mk cells =>
      change (cells ++ second.cells).foldr (fun cell total => cell.weightedAllowance + total) 0 =
        cells.foldr (fun cell total => cell.weightedAllowance + total) 0 + second.totalWeightedAllowance
      induction cells with
      | nil =>
          change second.totalWeightedAllowance = 0 + second.totalWeightedAllowance
          exact (Fraction.Field.zero_add _).symm
      | cons cell cells ih =>
          change cell.weightedAllowance +
            (cells ++ second.cells).foldr (fun cell total => cell.weightedAllowance + total) 0 =
              (cell.weightedAllowance + cells.foldr (fun cell total => cell.weightedAllowance + total) 0) +
                second.totalWeightedAllowance
          rewrite [ih]
          ring1

/-- Equal original cell counts give exactly twice the sum of the two aggregate allowances. -/
theorem aggregateAllowance_concat_of_length_eq (first second : PathModel)
    (count : first.cells.length = second.cells.length) :
    (first.concat second).aggregateAllowance = 2 * (first.aggregateAllowance + second.aggregateAllowance) := by
  change ((first.cells ++ second.cells).length : Fraction.Rational) *
    (first.concat second).totalWeightedAllowance =
      2 * ((first.cells.length : Fraction.Rational) * first.totalWeightedAllowance +
        (second.cells.length : Fraction.Rational) * second.totalWeightedAllowance)
  rewrite [List.length_append, Purelib.Algebra.NatCast.add, totalWeightedAllowance_concat, count]
  ring1

end Purelib.Integration.Polynomial.Gaussian.Path.Basic.PathModel
