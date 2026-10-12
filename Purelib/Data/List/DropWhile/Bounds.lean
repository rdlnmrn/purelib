module
import Purelib.Data.List.DropWhile.Basic
public import Purelib.Algebra.Field.ExplicitField

import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring.Basic
import Purelib.Tactic.QuotientFreeOmega

open Purelib

section
@[expose] public section

/-!
# Removing leading zeroes from finite lists

Removing an initial zero prefix cannot enlarge the original list. An
explicit leading zero certifies a strict decrease in its length.
-/

namespace Purelib.Data.List.DropWhile.Bounds

open Purelib.Data.List

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [DecidableEq K]

/-- Removing a leading zero prefix cannot increase the coefficient-list length. -/
public theorem length_dropWhile_zero_le (as : List K) :
    (as.dropWhile (· = 0)).length ≤ as.length := by
  exact DropWhile.length_le _ as

/-- Removing an explicitly zero head strictly decreases the coefficient-list length. -/
public theorem length_dropWhile_cons_zero_lt (as : List K) :
    ((0 :: as).dropWhile (· = 0)).length < (0 :: as).length := by
  exact DropWhile.length_lt_cons_of_true _ 0 as (decide_eq_true rfl)

end Purelib.Data.List.DropWhile.Bounds

end
