module

import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.Power.Gaussian.ExactRoot
public import Purelib.Algebra.Power.Gaussian.ExactRoot.Family
import Purelib.Data.Nat.Positive
import Purelib.Data.List.Map
import Purelib.Polynomial.Power.Gaussian
import Purelib.RootIsolation.Roots.CCL.Terminal.Basic
public import Purelib.RootIsolation.Roots.CCL.Terminal.Build
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Polynomial.Dense.Gaussian.Roots.Certificate

open Purelib

open Purelib.Data

open Purelib.Polynomial

open Purelib.RootIsolation

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

namespace Purelib.Algebra.Power.Gaussian.ExactRoot
section ExactRoot

/-- A displayed exact member is encoded as a genuinely terminating CCL (or
the distinguished exact-zero terminal), never as an endless shrinking
approximation. -/
def terminal
    {input : Gaussian.Basic.Canonical} {degree : Data.Nat.Positive.RootDegree}
    (root : ExactRoot input degree) :
    RootIsolation.Roots.CCL.Terminal (Power.Gaussian.rootPolynomial input degree) :=
  Roots.CCL.Terminal.Build.terminalOfExactRoot
    { point := root.point, root := root.polynomialRoot }

end ExactRoot
namespace Family.ExactRootFamily

/-- Encode every retained exact power root as a finite nonzero terminal or the distinguished zero terminal. -/
def terminals {input : Gaussian.Basic.Canonical}
  {degree : Data.Nat.Positive.RootDegree}
    (family : Algebra.Power.Gaussian.ExactRoot.Family.ExactRootFamily input degree) :
    List (RootIsolation.Roots.CCL.Terminal
      (Power.Gaussian.rootPolynomial input degree)) :=
  family.members.map terminal

/-- The encoded terminal list retains exactly the original positive degree many entries. -/
theorem terminals_length {input :
  Gaussian.Basic.Canonical} {degree : Data.Nat.Positive.RootDegree}
    (family : Algebra.Power.Gaussian.ExactRoot.Family.ExactRootFamily input degree) :
    family.terminals.length = degree.value := by
  change (family.members.map terminal).length = degree.value
  exact (Data.List.Map.length_map ..).trans family.count
end Family.ExactRootFamily
end Purelib.Algebra.Power.Gaussian.ExactRoot

end
