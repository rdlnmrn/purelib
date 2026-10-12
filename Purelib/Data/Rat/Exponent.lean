module

public import Purelib.Data.Nat.Positive
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

namespace Purelib.Data.Rat.Exponent

open Purelib.Data.Nat in
set_option genInjectivity false in
/-- Retain an integer exponent numerator and its original positive natural denominator.

The denominator remains the original positive RootDegree owner. No normalization or evaluation is performed, so the
signed numerator and positive degree stay available as executable data. -/
structure RationalExponent where
  /-- The retained signed integer numerator. -/ numerator : Int
  /-- The original positive RootDegree denominator of the signed exponent. -/ denominator : Positive.RootDegree

constructive_injectivity RationalExponent

end Purelib.Data.Rat.Exponent

end
