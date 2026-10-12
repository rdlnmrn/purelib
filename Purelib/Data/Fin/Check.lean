module

public import Purelib.Data.Fin
public import Purelib.Data.Nat.Order
meta import Mathlib.Tactic.Linter.Lint
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

namespace Purelib.Data.Fin

set_option genInjectivity false in
/-- The certified result of checking a predicate on a finite index type.

A valid result carries a proof at every index. An invalid result retains a particular bounded index and a proof that the
predicate fails there. -/
inductive Check {size : Nat} (predicate : Fin size → Prop) where
  /-- The predicate holds at every bounded index. -/ | valid (checked : ∀ index, predicate index)
  /-- Retain a bounded index and a proof that its predicate fails. -/ | invalid (index : Fin size) (different : ¬
    predicate index)

constructive_injectivity Check

namespace Check.invalid

end Check.invalid
namespace Check

open Purelib.Data.Fin.Check in
/-- Decide a predicate at every bounded natural index and retain the evidence.

Using the supplied decidable predicate, inspect indices from zero upwards. Return either a proof that all indices
satisfy it or the first failing index with its refutation. -/
@[expose] def check : {size : Nat} → (predicate : Fin size → Prop) → [DecidablePred
  predicate] → Check predicate
  | 0, _, _ => .valid (fun index => Fin.elim0 index)
  | _ + 1, predicate, _ =>
      if head : predicate 0 then
        match Data.Fin.Check.check (fun index => predicate index.succ) with
        | .invalid index different => .invalid index.succ different
        | .valid tail => .valid (Purelib.Data.Fin.casesDependent head tail)
      else .invalid 0 head

end Check
end Purelib.Data.Fin

end
