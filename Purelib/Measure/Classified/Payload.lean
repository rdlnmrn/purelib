module
public import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Measure.Classified.Basic
import Purelib.Measure.Weighted.Basic
public import Purelib.Measure.Weighted.Event
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction

open Purelib.Data.List.BinaryPrefix (CCLMeasureWord)

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

section
open Purelib
open Purelib.Data
/-- Retain a classified prefix entry as a weighted payload with its exact original atom weight and nonnegativity proof.
-/
def terminalWeighted
    (entry : Measure.Classified CCLMeasureWord) :
    Measure.Weighted (Measure.Classified CCLMeasureWord) where
  item := entry
  weight := entry.atom.weight
  nonnegative := entry.atom.nonnegative

/-- Select precisely the entries classified inside, rejecting outside and unresolved entries. -/
def terminalInside
    (entry : Measure.Classified CCLMeasureWord) : Bool :=
  match entry.status with
  | .inside => true
  | .outside | .unresolved => false

/-- Wrapping classified entries as weighted payloads preserves their exact total classified weight.

Every original occurrence keeps its weight through the retained payload wrapper, preserving the ordered finite total. -/
public theorem totalWeight_terminalWeighted
    (entries : List (Measure.Classified CCLMeasureWord)) :
    Measure.totalWeight (entries.map terminalWeighted) =
      Measure.classifiedWeight entries := by
  induction entries with
  | nil => rfl
  | cons entry remaining inductionHypothesis =>
      simp only [List.map_cons, Measure.totalWeight,
        terminalWeighted, Measure.classifiedWeight,
        inductionHypothesis, -eq_self, -iff_self]
      rfl

/-- The inside-event weight of the exact wrapped entries equals their original lower classified weight.

The retained classification selects the same inside occurrences on both sides, with every other original occurrence
contributing zero. -/
public theorem eventWeight_terminalInside
    (entries : List (Measure.Classified CCLMeasureWord)) :
    Measure.eventWeight (entries.map terminalWeighted)
        terminalInside =
      Measure.lowerWeight entries := by
  induction entries with
  | nil => rfl
  | cons entry remaining inductionHypothesis =>
      rcases entry with ⟨atom, status⟩
      cases status <;>
        simp only [List.map_cons, Measure.eventWeight,
          terminalWeighted, terminalInside, Measure.lowerWeight,
          inductionHypothesis, -eq_self, -iff_self] <;> rfl

end

end RawEvent

end Purelib.Data.List.BinaryPrefix

end
