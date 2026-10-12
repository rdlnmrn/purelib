module

import Purelib.Integration.Program.Gaussian.Cached.Basic
public import Purelib.Integration.Program.Gaussian.Cached.Prefix
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

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

namespace Purelib.Integration.Program.Gaussian.Cached

namespace Allocation

open Purelib.Integration.Program.Gaussian.Cached in
set_option genInjectivity false in
/-- A retained stage-prefix cache with its count for the exact original source program. -/
structure Retained (source : Basic.CachedProgram) where
  /-- The retained original source cache's stage count. -/ count : Nat
  /-- The exact original source prefix cache indexed by its retained count. -/ cache : Prefix.Cache source count

constructive_injectivity Retained

end Allocation

namespace Allocation.Retained.mk

end Allocation.Retained.mk

namespace Allocation.Retained.mk

end Allocation.Retained.mk

section
open Purelib.Integration.Program.Gaussian.Cached
namespace Allocation.Retained

/-- Allocate the original source's lazy prefix cache at the requested initial count. -/
def canonical (source : Basic.CachedProgram)
  (count : Nat) : Allocation.Retained source :=
  ⟨count, Prefix.Cache.canonical source count⟩

end Allocation.Retained

namespace Allocation.Retained

/-- Append the requested number of lazy original stages while preserving the retained prior cache. -/
def extend {source : Basic.CachedProgram}
  (retained : Allocation.Retained source) (extra : Nat) : Allocation.Retained source :=
  ⟨retained.count + extra, retained.cache.extend extra⟩

end Allocation.Retained

namespace Allocation.Retained

/-- Extend the retained original cache by each requested chunk size in order. -/
def chunks {source : Basic.CachedProgram}
  (retained : Allocation.Retained source) : List Nat → Allocation.Retained source
  | [] => retained
  | extra :: rest => (retained.extend extra).chunks rest

end Allocation.Retained

namespace Allocation.Retained

/-- The resulting retained count is the ordered sum of the original count and extension sizes. -/
theorem chunks_count {source :
  Basic.CachedProgram} (retained : Allocation.Retained source) (chunks : List Nat) :
    (retained.chunks chunks).count = chunks.foldl Nat.add retained.count := by
  induction chunks generalizing retained with
  | nil => rfl
  | cons extra rest induction => exact induction (retained.extend extra)

end Allocation.Retained

end

set_option genInjectivity false in
/-- An initial stage-prefix size followed by the retained ordered list of extension sizes. -/
structure Allocation where
  /-- The requested initial source-prefix size. -/ initial : Nat
  /-- The retained ordered list of cache-extension sizes. -/ extensions : List Nat
deriving DecidableEq

constructive_injectivity Allocation

namespace Allocation.mk

end Allocation.mk

namespace Allocation.mk

end Allocation.mk

namespace Allocation

open Purelib.Integration.Program.Gaussian.Cached in
/-- Allocate the original source cache and perform the exact ordered requested extensions. -/
def compile (allocation :
  Allocation) (source : Basic.CachedProgram) : Allocation.Retained source :=
  (Allocation.Retained.canonical source allocation.initial).chunks allocation.extensions

end Allocation

end Purelib.Integration.Program.Gaussian.Cached

end
