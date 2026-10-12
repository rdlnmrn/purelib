module

section
@[expose] public section

/-!
# Normalized rational arithmetic

This module retains the reduction-aware size and step accounting API.  The
underlying semantic type is now itself the canonical reduced record, so
`value` and `ofRational` no longer erase to or select from a quotient.

Addition first removes the gcd shared by the two denominators.  Multiplication
cross-cancels numerator/denominator pairs before forming either product.
Inversion swaps the already coprime components.  Multiplication is reduced
by cross-cancellation alone; addition's remaining gcd uses only the shared
denominator factor.  Reducedness certificates are retained as erased proofs,
not reconstructed by a redundant final gcd.
-/

namespace Purelib.Data.Nat.GCD.Resource.Clauses

/-! ## Euclidean-clause budgets -/

/-- Count clauses visited by a natural Euclidean recursion with explicit fuel.

Zero fuel contributes zero. With remaining fuel, a zero second input contributes its
terminal clause; otherwise the count includes the current clause and continues with
the divisor and remainder. -/
def gcdClausesAux : Nat → Nat → Nat → Nat
  | 0, _, _ => 0
  | _ + 1, _, 0 => 1
  | fuel + 1, first, second + 1 =>
      1 + gcdClausesAux fuel (second + 1) (first % (second + 1))

open Purelib.Data.Nat.GCD.Resource
/-- Count Euclidean clauses with the second input plus one units of fuel.

The count uses the same ordered inputs and fuel as the scalar gcd recursion and
includes the terminal zero clause. -/
def gcdClauses (first second : Nat) : Nat :=
  gcdClausesAux (second + 1) first second

/-- Check Euclidean clause counts at zero inputs and a displayed nontrivial pair.

The examples distinguish the asymmetric input order and verify that the pair 1071,
462 contributes four clauses. -/
theorem gcdClauses_regressions :
    gcdClauses 0 0 = 1 ∧ gcdClauses 37 0 = 1 ∧
      gcdClauses 0 37 = 2 ∧ gcdClauses 1071 462 = 4 := by
  decide +kernel

/-- The Euclidean clause count with its supplied fuel is strictly positive. -/
theorem gcdClauses_pos (first second : Nat) :
    0 < gcdClauses first second := by
  cases second with
  | zero => exact Nat.zero_lt_succ 0
  | succ second =>
      change 0 < 1 + gcdClausesAux (second + 1)
        (second + 1) (first % (second + 1))
      rw [Nat.one_add]
      exact Nat.zero_lt_succ _

/-- The Euclidean clause count is bounded by the second input plus one.

Each visited clause consumes one unit of the supplied finite fuel. This bounds
recursive clauses only, without estimating the cost of an individual remainder
calculation. -/
theorem gcdClauses_le (first second : Nat) :
    gcdClauses first second ≤ second + 1 := by
  have auxiliary : ∀ fuel left right,
      gcdClausesAux fuel left right ≤ fuel := by
    intro fuel
    induction fuel with
    | zero =>
        intro left right
        exact Nat.le_refl 0
    | succ fuel inductionHypothesis =>
        intro left right
        cases right with
        | zero => exact Nat.succ_le_succ (Nat.zero_le fuel)
        | succ right =>
            change 1 + gcdClausesAux fuel (right + 1) (left % (right + 1)) ≤
              fuel + 1
            simpa only [Nat.add_comm fuel 1] using
              Nat.add_le_add_left
                (inductionHypothesis (right + 1) (left % (right + 1))) 1
  exact auxiliary (second + 1) first second
end Purelib.Data.Nat.GCD.Resource.Clauses

end
