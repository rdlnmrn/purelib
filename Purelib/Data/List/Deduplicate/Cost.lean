module
public import Purelib.Data.Gaussian.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Nat.Multiplication

/-!
# Duplicate comparison counts

The exact structural count adds the original tail length for each head.
Its scalar square bound retains the original list and multiplication expression.
-/
namespace Purelib.Data.List.Deduplicate.Cost

open Purelib.Data.Gaussian.Basic

open Purelib.Data.Nat

/-- Count all head-versus-tail comparisons in a complete finite duplicate scan.

At each nonempty list add the remaining tail length and recurse. The count is the
number of unordered pairs of positions, independent of their Gaussian values. -/
@[expose] public def duplicateComparisonCount : List Canonical → Nat
  | [] => 0
  | _ :: remaining => remaining.length + duplicateComparisonCount remaining

open Purelib.Data.List.Deduplicate in
/-- A complete pairwise duplicate scan uses at most the square of the input length.

Each recursive head contributes at most the tail length; induction and natural
arithmetic give the coarse quadratic bound. -/
public theorem duplicateComparisonCount_le_square : ∀ values : List Canonical,
    duplicateComparisonCount values ≤ values.length * values.length
  | [] => Nat.le_refl 0
  | _ :: remaining => by
      simp only [duplicateComparisonCount, List.length_cons]
      have inductionBound := duplicateComparisonCount_le_square remaining
      calc
        remaining.length + duplicateComparisonCount remaining ≤
            remaining.length + remaining.length * remaining.length :=
          Nat.add_le_add_left inductionBound remaining.length
        _ ≤ (remaining.length + 1) * (remaining.length + 1) := by
          rewrite [Multiplication.right_distrib, Multiplication.left_distrib]
          simp only [Nat.one_mul, Nat.mul_one]
          omega
end Purelib.Data.List.Deduplicate.Cost
