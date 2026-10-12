module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
public import Purelib.Polynomial.Power.Gaussian
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic

open Purelib.Data

open Purelib.Data.Nat.Positive

open Purelib.Polynomial

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

namespace Purelib.Algebra.Power.Gaussian

/-! ## Immediate promotion of displayed exact roots -/

set_option genInjectivity false in
/-- A Gaussian point carrying an exact positive-degree power identity.

The input and degree index the retained point and its proof that raising it to that degree gives the input. -/
structure ExactRoot (input : Canonical) (degree : RootDegree) where
  /-- The displayed Gaussian rational root. -/ point : Canonical
  /-- The positive-degree power of the displayed root equals the input. -/ power_eq : point ^ degree.value = input

constructive_injectivity ExactRoot

namespace ExactRoot

end ExactRoot
namespace ExactRoot

open Purelib.Algebra.Power.Gaussian.ExactRoot in
/-- A certified exact power root vanishes in its corresponding power polynomial.

Evaluation of the polynomial at the retained point reduces to the certified power identity. -/
theorem polynomialRoot
    {input : Canonical} {degree : RootDegree}
    (root : ExactRoot input degree) :
    (Power.Gaussian.rootPolynomial input degree).eval root.point = 0 := by
  rw [Power.Gaussian.rootPolynomial_eval, root.power_eq,
    Gaussian.Basic.sub_self]
end ExactRoot
end Purelib.Algebra.Power.Gaussian

end
