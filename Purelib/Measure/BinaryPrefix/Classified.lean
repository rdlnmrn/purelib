module
import Purelib.Data.List.Membership
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Dyadic
import Purelib.Data.Rat.Interval.Basic
public import Purelib.Measure.BinaryPrefix.Content
import Purelib.Measure.Classified.Basic
public import Purelib.Measure.Classified.Split
import Purelib.Measure.Weighted.Basic
import Purelib.Data.Rat.Fraction

open Purelib.Data.List.BinaryPrefix (CCLMeasureWord)

section
@[expose] public section

/-!
# Symbolic dyadic weight of raw CCL prefixes

This is the fair-bit valuation on the raw binary address tree.  It is a
symbolic prefix weight, not geometric area and not the pushforward of
Lebesgue measure through the CCL decoder.  The distinction is explicit in the
API.
-/

namespace Purelib.Measure.BinaryPrefix

/-! ## Event bounds on raw-prefix frontiers -/

section
open Purelib
open Purelib.Data
open Purelib.Measure
/-- Attach the supplied classification status to the exact word's dyadic prefix atom. -/
def rawClassified (word : CCLMeasureWord) (status :
  Measure.Status) :
    Measure.Classified CCLMeasureWord where
  atom := BinaryPrefix.rawPrefixAtom word
  status := status

/-- Retain the false and true extensions with their respective supplied classification statuses. -/
def rawBinaryChildren (word : CCLMeasureWord)
    (falseStatus trueStatus : Measure.Status) :
    List (Measure.Classified CCLMeasureWord) :=
  [rawClassified (word ++ [false]) falseStatus,
    rawClassified (word ++ [true]) trueStatus]

/-- Certify a split of the exact unresolved prefix atom into its two classified children.

The child dyadic weights sum to the original parent weight; arbitrary supplied child statuses satisfy the unresolved
parent's compatibility requirement. -/
def rawUnresolvedSplit (word : CCLMeasureWord)
    (falseStatus trueStatus : Measure.Status) :
    Measure.Split (β := CCLMeasureWord)
      (rawClassified word Status.unresolved) where
  children := rawBinaryChildren word falseStatus trueStatus
  conserved := by
    simp only [rawBinaryChildren, rawClassified, BinaryPrefix.rawPrefixAtom,
      Measure.classifiedWeight, add_zero]
    exact List.BinaryPrefix.rawPrefixWeight_children_add word
  statuses := by
    intro child member
    simp only [-eq_self, -iff_self, rawBinaryChildren] at member
    rcases List.Membership.mem_cons.mp member with rfl | tail
    · trivial
    · rcases List.Membership.mem_cons.mp tail with rfl | impossible
      · trivial
      · cases impossible

end

open Purelib in
open Purelib.Data in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The two classified children's event bound refines the original unresolved prefix atom's bound. -/
theorem rawUnresolvedSplit_eventBound_refines
    (word : CCLMeasureWord) (falseStatus trueStatus : Measure.Status) :
    Interval.Refines
      (Measure.eventBound
        (rawBinaryChildren word falseStatus trueStatus))
      (Measure.eventBound
        [rawClassified word Status.unresolved]) :=
  (rawUnresolvedSplit word falseStatus trueStatus).eventBound_refines

end Purelib.Measure.BinaryPrefix

end
