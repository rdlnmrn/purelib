module
import Purelib.Integration.Program.Gaussian.Cached.Basic
public import Purelib.Integration.Program.Gaussian.Cached.Prefix
import Purelib.Integration.CertifiedProgram
import Purelib.Integration.Polynomial.Gaussian.Path.Basic

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

namespace Purelib.Integration.Program.Gaussian.Cached.Prefix
namespace Cache

open Purelib.Integration.Program.Gaussian.Cached in
/-- Expose the exact retained source cache as a certified stage program.

In-range queries force the retained stage thunks; other indices use the original source. The exact lookup equations
transport all original numerical guarantees. -/
def program {source : Basic.CachedProgram} {count : Nat}
  (cache : Prefix.Cache source count) : Basic.CachedProgram where
  stage := cache.lookup
  errorScale := source.errorScale
  errorScale_nonneg := source.errorScale_nonneg
  modelAllowance_le := by
    intro index
    rw [cache.lookup_eq]
    exact source.modelAllowance_le index
  later_close := by
    intro earlier later order
    rw [cache.lookup_eq, cache.lookup_eq]
    exact source.later_close order
  centerBound := source.centerBound
  centerBound_nonneg := source.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [cache.lookup_eq]
    exact source.sample_bounded index

end Cache
end Purelib.Integration.Program.Gaussian.Cached.Prefix

end
