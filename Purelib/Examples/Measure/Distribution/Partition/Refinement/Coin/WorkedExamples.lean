module
import Purelib.Data.List.Membership
public import Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic

import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Measure.Distribution.Partition.Refinement
import Purelib.Examples.Measure.Distribution.Coin.Basic
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Partition.Positive
import Purelib.Measure.Event.Family
import Purelib.Measure.Weighted.Basic

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Distribution.Partition.Refinement.Coin.WorkedExamples

open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic (positiveCoinPartition wholeCoinPartition)

/-- The explicit refinement grouping the two positive singleton coin cells into the original one-cell whole-event
partition. -/
def coinPartitionRefinesWhole :
  PositivePartitionRefinement
    positiveCoinPartition
      wholeCoinPartition where
  cellsFor := fun _ => positiveCoinPartition.events
  cells_mem := by
    intro coarseEvent coarseMember fineEvent fineMember
    exact fineMember
  cells_disjoint := by
    intro coarseEvent coarseMember
    exact positiveCoinPartition.disjoint
  agrees_on_atoms := by
    intro coarseEvent coarseMember atom atomMember
    simp only [-eq_self, -iff_self,
      wholeCoinPartition] at coarseMember
    have coarseMember := Purelib.Data.List.Membership.mem_singleton.mp coarseMember
    subst coarseEvent
    exact positiveCoinPartition.covers atom atomMember

end Purelib.Examples.Measure.Distribution.Partition.Refinement.Coin.WorkedExamples

end
