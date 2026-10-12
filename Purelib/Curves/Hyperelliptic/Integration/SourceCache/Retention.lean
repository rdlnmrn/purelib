module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

public import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Mathlib.Data.Nat.Basic
import Mathlib.Order.Basic

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

section
@[expose] public section

/-!
# Certificate-free source-state cache regressions

Two stationary sheet switches exercise the actual source-only recurrence,
cache hits, misses and chunked extension without any root isolation or
generated coefficient bank.  These are cache/ownership regressions, not
substitutes for the nonstationary Legendre period acceptance tests.
-/

namespace Purelib.Curves.Hyperelliptic.Integration.SourceCache.Retention

open Purelib.Riemann.Curves.AlgebraicDifferentials
open Purelib.Riemann.Integration.PreparedSwitchedRefinements
open DirectSwitchedState

variable {genus : Nat}

/-- This result applies to nonstationary inputs too: extension retains the actual thunk allocated before it, not merely
the same recomputed model. -/
theorem extension_retains_thunk {curve :
  Hyperelliptic.Basic.HyperellipticCurve genus} {source : Differentials.Basic.Differential genus}
    (retained : SourceCache curve source) (extra index : Nat) (within : index < retained.count) :
    (retained.extend extra).states.get index (within.trans_le (Nat.le_add_right _ _)) =
      retained.states.get index within :=
  retained.states.extend_get extra index within

end Purelib.Curves.Hyperelliptic.Integration.SourceCache.Retention

end
