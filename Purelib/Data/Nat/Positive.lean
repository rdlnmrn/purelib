module

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Finite root families, branch-selected roots, and rational powers

For an exact Gaussian-rational radicand, the polynomial `T^q - y` supplies
the public `q`th-root operation: its finite RFAP decomposition produces
exactly `q` root occurrences, counting displayed multiplicity.  Each
squarefree factor is either an exact rational terminal or a finite family of
independently shrinking CCL tracks.  Any additional displayed rational
candidate can also be checked and promoted immediately to a terminating CCL.
For automatic discovery, the special form `T^q-y` avoids a generic coordinate
Sylvester construction.  A sparse norm equation first enumerates the possible
rational quadrances.  At each one, a finite Lucas recurrence supplies the two
coordinate polynomials.  Their endpoint-divisor candidates are crossed,
deduplicated, and checked by the same exact power test.

The logarithmic formula `exp(log(y) / q)` remains useful, but it selects only
one explicitly anchored branch.  It is therefore named `selectedRoot`, not
the multi-valued `q`th-root operation.  All constructions stay inside finite
CCL arithmetic and never complete an input, logarithm, or root stream.
-/

namespace Purelib.Data.Nat.Positive

set_option genInjectivity false in
/-- A natural value retained together with a proof that it is positive.

The positive field rules out zero while preserving the supplied natural degree as
executable data. -/
structure RootDegree where
  /-- The retained natural degree. -/ value : Nat
  /-- The retained degree is strictly positive. -/ positive : 0 < value

constructive_injectivity RootDegree

open Purelib.Data.Nat.Positive in
/-- The positive degree whose retained natural value is two. -/
def squareRootDegree : RootDegree := ⟨2, by decide⟩
end Purelib.Data.Nat.Positive

end
