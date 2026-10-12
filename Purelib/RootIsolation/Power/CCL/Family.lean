module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Nat.Positive
import Purelib.Polynomial.Dense.Gaussian.Multiplicity.Basis.Positive
import Purelib.RootIsolation.FTA.Positive.CCL.Basic
public import Purelib.RootIsolation.FTA.Positive.CCL.Build
public import Purelib.RootIsolation.Power.Family

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Decomposition.Basic
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Part
import Purelib.RootIsolation.FTA.Positive.Input

open Purelib.Data

open Purelib

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

namespace Purelib.RootIsolation.Power

set_option genInjectivity false in
/-- One squarefree factor in the finite root family.  Its multiplicity counts
how many root occurrences it contributes per isolated root, while `result`
provides either its exact linear terminal or all its shrinking CCL tracks. -/
structure CCL.Family.RootFactor where
  /-- The original positive multiplicity-basis entry. -/ entry :
    Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry
  /-- The positive-degree CCL result for this exact retained factor polynomial. -/ result :
    FTA.Positive.CCL.Basic.PositiveResult entry.part.polynomial

constructive_injectivity CCL.Family.RootFactor

namespace CCL.Family.RootFactor

/-- Count root occurrences as the retained positive multiplicity times the factor's degree. -/
def occurrenceCount (factor : Power.CCL.Family.RootFactor) :
  Nat :=
  factor.entry.multiplicity * factor.entry.part.polynomial.natDegree

/-- The retained root factor has positive multiplicity. -/
theorem multiplicityPositive (factor :
  Power.CCL.Family.RootFactor) :
    0 < factor.entry.multiplicity :=
  factor.entry.multiplicityPositive

end CCL.Family.RootFactor

/-- Construct the exact linear terminal or complete CCL box family of the supplied positive factor. -/
def CCL.Family.isolateRootFactor (entry :
  Dense.Gaussian.Multiplicity.Basis.Positive.PositiveEntry) : CCL.Family.RootFactor :=
  { entry := entry
    result := FTA.Positive.CCL.Build.provePositive
      { squarefree := entry.factor.squarefree
        degreePositive := entry.factor.degreePositive } }
namespace Family.RootFamily

/-- Isolate each original positive factor in the retained power-root family, preserving list order. -/
def factors {input : Gaussian.Basic.Canonical} {degree :
  Data.Nat.Positive.RootDegree}
    (family : Power.Family.RootFamily input degree) : List Power.CCL.Family.RootFactor :=
  family.entries.map Power.CCL.Family.isolateRootFactor

open Purelib.Data.List in
/-- The isolated factor list has exactly the length of the retained positive-entry list. -/
@[simp] theorem factors_length
    {input : Gaussian.Basic.Canonical} {degree : Data.Nat.Positive.RootDegree}
    (family : Power.Family.RootFamily input degree) :
    family.factors.length = family.entries.length := by
  rw [factors]
  exact Map.length_map _ _

end Family.RootFamily
end Purelib.RootIsolation.Power

end
