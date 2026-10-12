module

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Remainder

open Purelib.Data.Nat

/-!
# Row-major codes for finite pairs

The original bounded coordinates determine a natural row-major code.
Ordinary division and remainder recover both coordinates directly.
-/

namespace Purelib.Data.Fin.Product.Code

/-- Encoding a finite pair in row-major order is injective.

For a pair in Fin m × Fin n, the natural code is the first coordinate times n plus the second coordinate. Division and
remainder recover the two coordinates whenever a pair exists. -/
public theorem pairCode_injective {m n : Nat} : Function.Injective
    (fun pair : Fin m × Fin n => pair.1.val * n + pair.2.val) := by
  intro first second equal
  have divisorPositive : 0 < n := (Nat.zero_le first.2.val).trans_lt first.2.isLt
  have codeDiv (i : Nat) (j : Fin n) : (i * n + j.val) / n = i := by
    rewrite [Nat.mul_comm i n, Division.mul_add_div divisorPositive,
      Division.div_eq_of_lt j.isLt, Nat.add_zero]
    exact Eq.refl _
  have codeMod (i : Nat) (j : Fin n) : (i * n + j.val) % n = j.val := by
    rewrite [Nat.mul_comm i n, Remainder.mul_add_mod, Remainder.mod_eq_of_lt j.isLt]
    exact Eq.refl _
  have quotient := congrArg (fun value => value / n) equal
  have remainder := congrArg (fun value => value % n) equal
  have firstValues : first.1.val = second.1.val :=
    (codeDiv first.1.val first.2).symm.trans
      (quotient.trans (codeDiv second.1.val second.2))
  have secondValues : first.2.val = second.2.val :=
    (codeMod first.1.val first.2).symm.trans
      (remainder.trans (codeMod second.1.val second.2))
  exact Prod.ext (Fin.ext firstValues) (Fin.ext secondValues)

end Purelib.Data.Fin.Product.Code
