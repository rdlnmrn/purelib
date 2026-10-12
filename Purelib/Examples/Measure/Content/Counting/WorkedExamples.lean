module
import Purelib.Measure.Content.Counting

import Purelib.Tactic.QuotientFreeOmega

@[expose] public section

/-!
# Executable finite measure examples

All numerical examples reduce to finite rational calculations checked by the
kernel.  The final examples exercise the generic CCL area-request interface
without postulating a completed CCL value.
-/

namespace Purelib.Examples.Measure.Content.Counting.WorkedExamples

open Purelib.Examples

/-! ## Exact finite probability -/

/-- The retained finite observations [1,2,2,4], including the repeated two. -/
def observedRolls : List Nat := [1, 2, 2, 4]

/-- The decidable event that a natural-number observation is even. -/
def observedEven (value : Nat) : Bool := value % 2 == 0

/-- The counting content of the retained observations has total mass four. -/
example : (Purelib.Measure.countingContent observedRolls).total = 4 := by
  decide

/-- The retained observations have even-event counting mass three. -/
example : (Purelib.Measure.countingContent observedRolls).measure
  observedEven = 3 := by
  decide

end Purelib.Examples.Measure.Content.Counting.WorkedExamples

end
