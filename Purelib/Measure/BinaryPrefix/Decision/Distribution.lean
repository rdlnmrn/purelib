module
import Purelib.Data.List.Map
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Decision.Basic
import Purelib.Measure.Classified.Basic
public import Purelib.Measure.Classified.Payload
public import Purelib.Measure.Distribution.Basic
import Purelib.Data.List.Event
public import Purelib.Measure.BinaryPrefix.Decision.Classification
import Purelib.Measure.BinaryPrefix.Decision.Valuation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# A finite Boolean algebra of raw-prefix decisions

`RawEvent` is a finite binary decision tree.  Its valuation is computed by
finite recursion, assigning half of the current symbolic weight to each raw
bit branch.  It is deliberately not a set of completed bit streams and does
not assert that the CCL decoder preserves this symbolic valuation.
-/

namespace Purelib.Data.List.BinaryPrefix
namespace RawEvent

open Purelib in
open Purelib.Data in
/-- Normalize the raw decision event's exact terminal frontier into a finite distribution on classified prefixes.

The original terminal entries and dyadic weights are retained directly, with their unit-total proof; no entries are
merged or reordered. -/
def terminalDistribution (event : List.BinaryPrefix.RawEvent) :
    Measure.Distribution (Measure.Classified List.BinaryPrefix.CCLMeasureWord)
    where
  atoms := event.terminalFrontier.map List.BinaryPrefix.RawEvent.terminalWeighted
  total_one := by
    rw [List.BinaryPrefix.RawEvent.totalWeight_terminalWeighted, event.terminalFrontier_weight]

open Purelib.Data in
open Purelib.Measure in
/-- Inside probability under the exact terminal distribution equals the raw decision event's computed weight. -/
theorem terminalDistribution_probability_inside (event :
  List.BinaryPrefix.RawEvent) :
    event.terminalDistribution.probability List.BinaryPrefix.RawEvent.terminalInside = event.weight := by
  unfold terminalDistribution Distribution.probability
  rw [List.BinaryPrefix.RawEvent.eventWeight_terminalInside, event.terminalFrontier_lower]

open Purelib.Data in
open Purelib.Data.List in
/-- The terminal distribution retains exactly as many atom occurrences as its original terminal frontier. -/
theorem terminalDistribution_atoms_length (event :
  List.BinaryPrefix.RawEvent) :
    event.terminalDistribution.atoms.length =
      event.terminalFrontier.length := by
  simp only [terminalDistribution, -eq_self, -iff_self]
  exact Map.length_map _ _
end RawEvent

end Purelib.Data.List.BinaryPrefix

end
