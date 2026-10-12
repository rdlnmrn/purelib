module
import Purelib.Data.Gaussian.Basic
public import Purelib.Algebra.Power.Gaussian.ExactRoot.Family
import Purelib.Data.Nat.Positive

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init

open Purelib

open Purelib.Algebra.Power.Gaussian.ExactRoot.Family

open Purelib.Data.Nat

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

namespace Test.Algebra.Power.Gaussian

/-- Both complex square roots of the exact input `4` are found in one finite candidate batch, so this example produces
two terminating CCL states rather than one arbitrarily selected branch. -/
theorem squareRootsOfFour_exact :
    (ExactRootFamily.ofCandidates? (4 : Data.Gaussian.Basic.Canonical) Positive.squareRootDegree
      [(2 : Data.Gaussian.Basic.Canonical), (-2 : Data.Gaussian.Basic.Canonical)]).isSome = true := by
  decide
end Test.Algebra.Power.Gaussian

end
