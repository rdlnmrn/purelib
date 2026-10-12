module

import Purelib.Data.Fin
public import Purelib.Data.Fin.Check
import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

section
public section

/-!
# Exact replay of integral pairing reductions

An untrusted producer supplies only oriented unit pivots. Each successful
stage retains its shear and reduced matrix; invalidity identifies a bad pivot
or an entry which fails the claimed final normal form. Rejection is only of
this submitted reduction, not of the existence of another integral basis.
-/

namespace Purelib.LinearAlgebra.Matrix.Integral.Check

set_option genInjectivity false in
/-- The certified result of comparing all entries of two integral matrices.

A valid result proves equality at every pair of bounded row and column indices. An invalid result retains one row, one
column and a proof that the corresponding entries differ. -/
inductive EntryCheck {rows columns : Nat} (left
  right : Fin rows → Fin columns → Int) where
  /-- Every pair of corresponding matrix entries is equal. -/ | valid (checked : ∀ row column, left row column = right
    row column)
  /-- Retain a row and column at which the corresponding matrix entries differ. -/ | invalid (row : Fin rows) (column :
    Fin columns) (different : left row column ≠ right row column)

constructive_injectivity EntryCheck

open Purelib.Data.Fin.Check (check) in
open Purelib.LinearAlgebra.Matrix.Integral in
/-- Compare integral matrices entry by entry and retain equality or a counterexample.

The procedure checks each row from column zero upwards, then recurses on the remaining rows. It returns universal entry
equality or the first differing entry in row order, with the original bounded indices and a proof of inequality. -/
@[expose] def checkEntries {columns : Nat} :
  {rows : Nat} →
    (left right : Fin rows → Fin columns → Int) → Check.EntryCheck left right
  | 0, _, _ => .valid (fun row => Fin.elim0 row)
  | _ + 1, left, right =>
      match check (fun column => left 0 column = right 0 column) with
      | .invalid column different => .invalid 0 column different
      | .valid head =>
          match Purelib.LinearAlgebra.Matrix.Integral.Check.checkEntries (fun row => left row.succ)
            (fun row => right row.succ) with
          | .invalid row column different => .invalid row.succ column different
          | .valid tail => .valid (Purelib.Data.Fin.casesDependent head tail)
end Purelib.LinearAlgebra.Matrix.Integral.Check

end
