module

import Purelib.Measure.Distribution.Basic
public import Purelib.Measure.Distribution.Partition.Basic
import Purelib.Measure.Event.Family
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Measure.Weighted.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
/-!
# Conditional expectation over displayed finite partitions

This module proves the finite rational form of the law of total expectation.
Every partition cell is an executable Boolean event, every sum is a displayed
list sum, and positivity of conditioning cells is carried explicitly.  No
sigma-algebra, completion, or limiting conditional expectation is formed.
-/

@[expose] public section

namespace Purelib.Measure

set_option genInjectivity false in
/-- Retain a finite partition of the exact distribution with strictly positive probability for every displayed event.

Keep the original event list, occurrence-wise disjointness and coverage, and the positive probability witnesses needed
to condition on its exact cells. -/
structure PositiveEventPartition {α : Type}
    (distribution : Distribution α) where
  /-- The exact ordered finite partition event list. -/ events : List (α → Bool)
  /-- The retained events are mutually disjoint on the original distribution atoms. -/ disjoint : MutuallyDisjointOn
    distribution.atoms events
  /-- Their union selects every retained original distribution occurrence. -/ covers : ∀ atom, atom ∈ distribution.atoms
    →
    unionEvents events atom.item = true
  /-- Every event belonging to the exact retained partition has strictly positive original probability. -/ positive : ∀
    event, event ∈ events →
    0 < distribution.probability event

constructive_injectivity PositiveEventPartition

namespace PositiveEventPartition

/-- Forget positivity while retaining the same exact partition events, disjointness and coverage certificates. -/
def toEventPartition {α : Type} {distribution : Distribution α}
    (partition : PositiveEventPartition distribution) :
    EventPartition distribution where
  events := partition.events
  disjoint := partition.disjoint
  covers := partition.covers
end PositiveEventPartition

end Purelib.Measure

end
