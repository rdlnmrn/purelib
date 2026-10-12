module
import Purelib.Data.Gaussian.Basic
public import Purelib.Computation.Arithmetic.Cost.Gaussian

section
@[expose] public section

/-!
# Finite bit-work account for automatic rational roots

This file supplies an executable, phase-by-phase bit-size account for the
automatic exact-root search for `T^q-y`.  It is deliberately a coarse
schoolbook model, but it is not a unit-cost count:

* every natural, integer, rational, and Gaussian operand is charged at its
  displayed binary width;
* one exact rational arithmetic operation is charged quadratically in the
  combined input/output width;
* its canonical gcd normalization is charged separately and cubically in the
  output width (a defensive allowance for finite Euclidean arithmetic);
* Horner evaluation and repeated powering are followed through their actual
  finite intermediate values;
* denominator clearance follows the actual recursive cleared coefficient
  lists;
* divisor scans, duplicate comparisons, and every exact final power test are
  all charged explicitly.

The account describes this finite algorithm, not wall-clock time of Lean's
runtime.  Its purpose is to close the former hidden-unit-cost gap and to make
every improvement target visible.  Faster multiplication, gcd, divisor, or
deduplication implementations can replace an individual displayed charge
without changing the root-completeness theorem.
-/

namespace Purelib.Data.Gaussian.List.Deduplicate.Cost

open Purelib.Computation.Arithmetic.Cost in
open Purelib.Data.Gaussian in
/-- Sum the Gaussian equality cost of comparing one candidate with every entry in the supplied list.

Traverse the full list and add the original equality cost for each pair, including entries after any possible match.
This models the retained comparison traversal exactly as defined. -/
def membershipComparisonCost (candidate : Basic.Canonical) : List
  Basic.Canonical → Nat
  | [] => 0
  | value :: remaining =>
      Gaussian.gaussianEqualityCost candidate value +
        membershipComparisonCost candidate remaining

open Purelib.Data.Gaussian in
/-- Sum the comparison costs for each head against its remaining tail during duplicate removal.

For each head, count comparison against every later entry, then continue with the original tail. The recurrence
preserves occurrence order and includes the full pairwise comparison work. -/
def duplicateRemovalCost : List Basic.Canonical → Nat
  | [] => 0
  | candidate :: remaining =>
      membershipComparisonCost candidate remaining +
        duplicateRemovalCost remaining
end Purelib.Data.Gaussian.List.Deduplicate.Cost

end
