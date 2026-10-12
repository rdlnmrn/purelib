module
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.List.BinaryPrefix.Truncation
public import Purelib.Measure.BinaryPrefix.Coupling
public import Purelib.Measure.CCL.Prefix.Distribution
import Purelib.Measure.Coupling.Law.Basic

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.List.BinaryPrefix.Basic

section
@[expose] public section

/-!
# Joint finite profile of a completed CCL prefix

A completed-block prefix carries two deliberately separate rational data:

* its fair-bit symbolic cylinder weight, calculated from the raw word; and
* its geometric squared-chordal spread, calculated from block contraction.

Both improve under finite extension, but no theorem identifies them.  A
finite realization certificate also turns the prefix into an inhabited
finite observation, without choosing a point from an eventual intersection.
-/

namespace Purelib.Measure.CCL.Prefix

open Purelib in
open Purelib.Data.CCL.Encoding in
open Purelib.Measure in
/-- Couple each deeper completed-prefix extension with its exact retained extra-depth ancestor.

The marginals are the original extension laws at depths `depth + extra` and `depth`, preserving their weighted binary
occurrences. -/
def completedPrefixExtensionAncestorLawCoupling
    (blocks : List Data.CCL.Encoding.Block) (depth extra : Nat) :
    Measure.LawCoupling
      (CCL.Prefix.completedPrefixExtensionDistribution blocks (depth + extra))
      (CCL.Prefix.completedPrefixExtensionDistribution blocks depth) :=
  BinaryPrefix.rawExtensionAncestorLawCoupling
    (Block.Basic.rawWord blocks) depth extra

open Purelib.Data in
open Purelib.Data.CCL.Encoding in
open Purelib.Measure in
/-- The retained ancestor coupling has zero probability of violating its exact ancestor relation. -/
theorem completedPrefixExtensionAncestorLawCoupling_mismatchProbability
    (blocks : List Data.CCL.Encoding.Block) (depth extra : Nat) :
    LawCoupling.mismatchProbability
        (completedPrefixExtensionAncestorLawCoupling blocks depth extra)
        (List.BinaryPrefix.rawAncestorRelation extra) = 0 :=
  BinaryPrefix.rawExtensionAncestorLawCoupling_mismatchProbability
    (Block.Basic.rawWord blocks) depth extra
end Purelib.Measure.CCL.Prefix

end
