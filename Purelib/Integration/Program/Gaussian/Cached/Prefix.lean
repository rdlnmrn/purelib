module

public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Generated finite allocation and extension policies for integration models

The cache owns a finite prefix of lazy, complete cached models.  Extension
retains every earlier thunk verbatim; each new thunk computes its canonical
source stage only when requested.  A read outside the allocated prefix uses
the original source procedure.  All numerical equality laws are derived from
these constructors, not supplied by a policy's caller.

This cache applies to the actual program being wrapped, including canonical
period programs whose preparation differs from the explicit Legendre fixture.
It complements prepared-state caches by retaining the integrated model's
sample and allowance as well as the model itself.
-/

namespace Purelib.Integration.Program.Gaussian.Cached.Prefix

open Purelib.Integration.Program.Gaussian.Cached

set_option genInjectivity false in
/-- A retained prefix of lazy stage values indexed by the exact original program and cached stage count.

Each appended thunk carries equality with its original program stage, preserving the previous cache as retained data. -/
inductive Cache (program : Basic.CachedProgram) : Nat → Type where
  /-- The exact original program has an empty stage-prefix cache. -/ | empty :
    Purelib.Integration.Program.Gaussian.Cached.Prefix.Cache program 0
  /-- Append a lazy stage value and its exact original-stage equation to the retained previous cache. -/ | snoc {count :
    Nat} (previous : Purelib.Integration.Program.Gaussian.Cached.Prefix.Cache program count) (value : Thunk
    Basic.CachedModel)
      (value_eq : value.get = program.stage count) : Purelib.Integration.Program.Gaussian.Cached.Prefix.Cache program
        (count + 1)

constructive_injectivity Cache

/-- Append one lazy exact original stage to the retained prefix cache.

The new thunk retains the same original program and next stage index. Every earlier thunk remains in the supplied prefix
unchanged. -/
@[expose] def Cache.push {program : Basic.CachedProgram} {count : Nat} (cache : Prefix.Cache program count) :
  Prefix.Cache program (count + 1) :=
  .snoc cache ⟨fun _ => program.stage count⟩ rfl

/-- Build the original stage-prefix cache in increasing stage order.

Each successor appends the same original stage thunk to the unchanged prefix, preserving increasing stage order. -/
@[expose] def Cache.canonical (program : Basic.CachedProgram) : (count : Nat) → Prefix.Cache program count
  | 0 => .empty
  | count + 1 => (Purelib.Integration.Program.Gaussian.Cached.Prefix.Cache.canonical program count).push

/-- Append the requested number of exact lazy stages to the existing retained cache.

The supplied prefix remains the retained parent at every append. Only the requested next stage thunks are added. -/
@[expose] def Cache.extend {program : Basic.CachedProgram} {count : Nat} (cache : Prefix.Cache program count) :
    (extra : Nat) → Prefix.Cache program (count + extra)
  | 0 => cache
  | extra + 1 => (cache.extend extra).push

/-- Read the original retained stage thunk using its explicit in-range bound.

The explicit bound excludes the empty cache. The original index chooses either the unchanged previous prefix or the
retained last thunk. -/
@[expose] def Cache.get {program : Basic.CachedProgram} {count : Nat} (cache : Prefix.Cache program count)
    (index : Nat) (within : index < count) : Thunk Basic.CachedModel :=
  match cache with
  | .empty => by omega
  | @Prefix.Cache.snoc _ count previous value _ =>
      if old : index < count then previous.get index old else value

/-- Forcing the retained in-range thunk gives the exact original program stage.

Each cached thunk carries its exact original-stage equation. The explicit bound and comparison identify the same index
in the retained prefix. -/
theorem Cache.get_eq {program : Basic.CachedProgram} {count : Nat} (cache : Prefix.Cache program count)
    (index : Nat) (within : index < count) : (cache.get index within).get = program.stage index := by
  induction cache with
  | empty => exact (Nat.not_lt_zero index within).elim
  | @snoc count previous value valueEqual induction =>
      unfold Prefix.Cache.get
      by_cases old : index < count
      · rw [dif_pos old]
        exact induction old
      · rw [dif_neg old]
        have equal : index = count := by omega
        exact equal ▸ valueEqual

/-- Extending the cache preserves the exact old retained thunk at every originally valid index.

Extension retains the original prefix as its parent. Each original valid index follows that same prefix and returns the
identical stored thunk. -/
theorem Cache.get_extend {program : Basic.CachedProgram} {count : Nat} (cache : Prefix.Cache program count)
    (extra index : Nat) (within : index < count) :
    (cache.extend extra).get index (within.trans_le (Nat.le_add_right _ _)) = cache.get index within := by
  induction extra with
  | zero => rfl
  | succ extra induction =>
      change (if old : index < count + extra then (cache.extend extra).get index old
        else (⟨fun _ => program.stage (count + extra)⟩ : Thunk Basic.CachedModel)) = cache.get index within
      rw [dif_pos (within.trans_le (Nat.le_add_right count extra))]
      exact induction

/-- Use the retained cached thunk for an in-range stage and the original program stage outside the cached prefix.

An explicit comparison selects either the exact retained in-range thunk or the same original program stage at the
supplied index. -/
@[expose] def Cache.lookup {program : Basic.CachedProgram} {count : Nat} (cache : Prefix.Cache program count) (index :
  Nat) : Basic.CachedModel :=
  if within : index < count then (cache.get index within).get else program.stage index

/-- Cache lookup gives the exact original program stage at every index.

The in-range cache specification and the out-of-range fallback both read the same original program stage. -/
theorem Cache.lookup_eq {program : Basic.CachedProgram} {count : Nat} (cache : Prefix.Cache program count) (index : Nat)
  :
    cache.lookup index = program.stage index := by
  unfold Prefix.Cache.lookup
  split
  · exact cache.get_eq index _
  · rfl
end Purelib.Integration.Program.Gaussian.Cached.Prefix
end
