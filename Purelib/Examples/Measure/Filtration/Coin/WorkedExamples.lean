module
import Purelib.Examples.Measure.Distribution.Coin.Basic
import Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic
public import Purelib.Examples.Measure.Distribution.Partition.Refinement.Coin.WorkedExamples

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Measure.Filtration.Basic
public import Purelib.Measure.Filtration.Cellwise

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Filtration.Coin.WorkedExamples

open Purelib.Examples
open Purelib.Measure
open Purelib.Examples.Measure.Distribution.Partition.Positive.Coin.Basic (positiveCoinPartition)

/-- The two-stage fair-coin filtration refining the whole-event cell into its two positive singleton cells. -/
def coinFiltration : Filtration
  Measure.Distribution.Coin.Basic.fairCoin positiveCoinPartition :=
  .extend (.base Measure.Distribution.Partition.Positive.Coin.Basic.wholeCoinPartition)
    positiveCoinPartition
    Measure.Distribution.Partition.Refinement.Coin.WorkedExamples.coinPartitionRefinesWhole

/-- Every observable represented on the coarse whole-event partition remains represented on the original singleton
refinement. -/
theorem coinFiltrationCellwiseCompatible :
    coinFiltration.CellwiseCompatible := by
  constructor
  · trivial
  · intro value represented
    rcases represented with ⟨represented⟩
    refine ⟨{
      cellValue := fun _ => represented.cellValue (fun _ : Bool => true)
      agrees := ?_ }⟩
    intro fineEvent fineMember atom atomMember selected
    exact represented.agrees (fun _ : Bool => true) List.mem_cons_self
      atom atomMember rfl

/-- The retained coin filtration has depth two. -/
example : coinFiltration.depth = 2 := by
  decide

end Purelib.Examples.Measure.Filtration.Coin.WorkedExamples

end
