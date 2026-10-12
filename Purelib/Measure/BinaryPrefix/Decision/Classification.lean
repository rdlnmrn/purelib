module
import Purelib.Data.List.Append
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Decision.Basic
import Purelib.Data.List.BinaryPrefix.Dyadic
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Measure.BinaryPrefix.Classified
import Purelib.Measure.BinaryPrefix.Content
public import Purelib.Measure.BinaryPrefix.Decision.Valuation
import Purelib.Measure.Classified.Basic
import Purelib.Measure.Classified.Split
public import Purelib.Measure.Refinement
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Weighted.Basic
import Purelib.Tactic.Ring

open Purelib.Data.List.BinaryPrefix (CCLMeasureWord)

open Purelib.Data.List

section
public section

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
/-- Classify a prefix against the exact finite raw decision event.

Empty and full leaves decide outside and inside; an exhausted prefix at a branch is unresolved, while a further bit
selects its original child. -/
@[expose] def classify : List.BinaryPrefix.RawEvent →
  CCLMeasureWord → Measure.Status
  | .empty, _ => .outside
  | .full, _ => .inside
  | .branch _ _, [] => .unresolved
  | .branch falseChild trueChild, bit :: remaining =>
      if bit then trueChild.classify remaining
      else falseChild.classify remaining

open Purelib.Data in
/-- Complementing a raw event exchanges inside and outside classification and retains unresolved classification. -/
theorem classify_complement : ∀ (event : List.BinaryPrefix.RawEvent)
  (word : CCLMeasureWord),
    event.complement.classify word =
      match event.classify word with
      | .inside => .outside
      | .outside => .inside
      | .unresolved => .unresolved
  | .empty, _ => rfl
  | .full, _ => rfl
  | .branch _ _, [] => rfl
  | .branch falseChild trueChild, bit :: remaining => by
      cases bit with
      | false => exact classify_complement falseChild remaining
      | true => exact classify_complement trueChild remaining

section
open Purelib.Data
open Purelib.Measure
/-- Every extension of a prefix is inside that prefix's exact raw decision event. -/
theorem ofPrefix_classify_append (stem suffix :
  CCLMeasureWord) :
    (List.BinaryPrefix.RawEvent.ofPrefix stem).classify (stem ++ suffix) =
      Status.inside := by
  induction stem with
  | nil => rfl
  | cons bit remaining inductionHypothesis =>
      cases bit <;> exact inductionHypothesis

/-- A prefix is inside its own raw decision event. -/
theorem ofPrefix_classify_self (stem : CCLMeasureWord)
  :
    (List.BinaryPrefix.RawEvent.ofPrefix stem).classify stem = Status.inside := by
  simpa only [-eq_self, -iff_self, Append.append_nil] using ofPrefix_classify_append stem []

/-! ## Executing a finite decision tree as a classified prefix frontier -/

end

section
open Purelib
open Purelib.Data
section
open Purelib.Measure
/-- Attach exact dyadic weights and raw-event classifications to the original ordered prefix frontier. -/
@[expose] def classifyFrontier (event : List.BinaryPrefix.RawEvent)
  (frontier : List CCLMeasureWord) :
    List (Measure.Classified CCLMeasureWord) :=
  frontier.map fun word => BinaryPrefix.rawClassified word (event.classify word)

/-- Split an unresolved original prefix into its two exact immediate children with retained classifications and
conserved weight. -/
@[expose] def classifySplit (event : List.BinaryPrefix.RawEvent) (word :
  CCLMeasureWord)
    (unresolved : event.classify word =
      Status.unresolved) :
    Measure.Split (β := CCLMeasureWord)
      (BinaryPrefix.rawClassified word (event.classify word)) where
  children := BinaryPrefix.rawBinaryChildren word
    (event.classify (word ++ [false]))
    (event.classify (word ++ [true]))
  conserved := by
    simp only [-eq_self, -iff_self, BinaryPrefix.rawBinaryChildren, BinaryPrefix.rawClassified,
      BinaryPrefix.rawPrefixAtom,
      Measure.classifiedWeight, add_zero]; try rfl
    exact List.BinaryPrefix.rawPrefixWeight_children_add word
  statuses := by
    rw [unresolved]
    intro child member
    trivial

/-- Replacing an unresolved prefix by its exact two children yields a certified refinement of the classified frontier.
-/
theorem classifyFrontier_split_refines (event :
  List.BinaryPrefix.RawEvent)
    (before after : List CCLMeasureWord) (word : CCLMeasureWord)
    (unresolved : event.classify word =
      Status.unresolved) :
    Measure.FrontierRefines
      (classifyFrontier event (BinaryPrefix.splitRawFrontier before after word))
      (classifyFrontier event (before ++ [word] ++ after)) := by
  simpa only [-eq_self, -iff_self, classifyFrontier, BinaryPrefix.splitRawFrontier,
    Map.map_append,
    List.map_cons, List.map_nil, classifySplit, BinaryPrefix.rawBinaryChildren] using
      (FrontierRefines.split
        (before.map fun candidate =>
          BinaryPrefix.rawClassified candidate (event.classify candidate))
        (after.map fun candidate =>
          BinaryPrefix.rawClassified candidate (event.classify candidate))
        (BinaryPrefix.rawClassified word (event.classify word))
        (classifySplit event word unresolved))

/-- Expand the raw decision tree below the retained prefix into its ordered inside and outside leaf frontier.

Branch expansion appends the false-child frontier before the true-child frontier, retaining each resulting prefix and
its dyadic weight. -/
@[expose] def terminalFrontierAt (stem :
  CCLMeasureWord) : List.BinaryPrefix.RawEvent →
    List (Measure.Classified CCLMeasureWord)
  | .empty => [BinaryPrefix.rawClassified stem Status.outside]
  | .full => [BinaryPrefix.rawClassified stem Status.inside]
  | .branch falseChild trueChild =>
      terminalFrontierAt (stem ++ [false]) falseChild ++
        terminalFrontierAt (stem ++ [true]) trueChild

/-- The terminal frontier below a prefix has exactly that prefix's original dyadic weight. -/
theorem terminalFrontierAt_weight : ∀ (event :
  List.BinaryPrefix.RawEvent) (stem : CCLMeasureWord),
    Measure.classifiedWeight (terminalFrontierAt stem event) =
      List.BinaryPrefix.rawPrefixWeight stem
  | .empty, stem => by
      simp only [-eq_self, -iff_self, terminalFrontierAt, Measure.classifiedWeight,
        BinaryPrefix.rawClassified, BinaryPrefix.rawPrefixAtom, add_zero]; try rfl
  | .full, stem => by
      simp only [-eq_self, -iff_self, terminalFrontierAt, Measure.classifiedWeight,
        BinaryPrefix.rawClassified, BinaryPrefix.rawPrefixAtom, add_zero]; try rfl
  | .branch falseChild trueChild, stem => by
      rw [terminalFrontierAt,
        Measure.classifiedWeight_append,
        terminalFrontierAt_weight falseChild,
        terminalFrontierAt_weight trueChild]
      exact List.BinaryPrefix.rawPrefixWeight_children_add stem

end

section
open Purelib.Data.Rat
open Purelib.Measure
/-- The terminal frontier's lower weight equals the original prefix weight times the raw event's weight. -/
theorem terminalFrontierAt_lower : ∀ (event : List.BinaryPrefix.RawEvent)
  (stem : CCLMeasureWord),
    Measure.lowerWeight (terminalFrontierAt stem event) =
      List.BinaryPrefix.rawPrefixWeight stem * event.weight
  | .empty, stem => by
      simp only [-eq_self, -iff_self, terminalFrontierAt, Measure.lowerWeight,
        BinaryPrefix.rawClassified, BinaryPrefix.rawPrefixAtom, List.BinaryPrefix.RawEvent.weight, mul_zero, add_zero];
          try rfl
  | .full, stem => by
      simp only [-eq_self, -iff_self, terminalFrontierAt, Measure.lowerWeight,
        BinaryPrefix.rawClassified, BinaryPrefix.rawPrefixAtom, List.BinaryPrefix.RawEvent.weight, mul_one, add_zero];
          try rfl
  | .branch falseChild trueChild, stem => by
      rw [terminalFrontierAt, Measure.lowerWeight_append,
        terminalFrontierAt_lower falseChild,
        terminalFrontierAt_lower trueChild,
        List.BinaryPrefix.rawPrefixWeight_child, List.BinaryPrefix.rawPrefixWeight_child,
          List.BinaryPrefix.RawEvent.weight]
      let half : Fraction.Rational := 1 / 2
      change List.BinaryPrefix.rawPrefixWeight stem * half * falseChild.weight +
          List.BinaryPrefix.rawPrefixWeight stem * half * trueChild.weight =
        List.BinaryPrefix.rawPrefixWeight stem *
          ((falseChild.weight + trueChild.weight) * half)
      ring1

/-- The terminal frontier's upper weight equals the original prefix weight times the raw event's weight. -/
theorem terminalFrontierAt_upper : ∀ (event : List.BinaryPrefix.RawEvent)
  (stem : CCLMeasureWord),
    Measure.upperWeight (terminalFrontierAt stem event) =
      List.BinaryPrefix.rawPrefixWeight stem * event.weight
  | .empty, stem => by
      simp only [-eq_self, -iff_self, terminalFrontierAt, Measure.upperWeight,
        BinaryPrefix.rawClassified, BinaryPrefix.rawPrefixAtom, List.BinaryPrefix.RawEvent.weight, mul_zero, add_zero];
          try rfl
  | .full, stem => by
      simp only [-eq_self, -iff_self, terminalFrontierAt, Measure.upperWeight,
        BinaryPrefix.rawClassified, BinaryPrefix.rawPrefixAtom, List.BinaryPrefix.RawEvent.weight, mul_one, add_zero];
          try rfl
  | .branch falseChild trueChild, stem => by
      rw [terminalFrontierAt, Measure.upperWeight_append,
        terminalFrontierAt_upper falseChild,
        terminalFrontierAt_upper trueChild,
        List.BinaryPrefix.rawPrefixWeight_child, List.BinaryPrefix.rawPrefixWeight_child,
          List.BinaryPrefix.RawEvent.weight]
      let half : Fraction.Rational := 1 / 2
      change List.BinaryPrefix.rawPrefixWeight stem * half * falseChild.weight +
          List.BinaryPrefix.rawPrefixWeight stem * half * trueChild.weight =
        List.BinaryPrefix.rawPrefixWeight stem *
          ((falseChild.weight + trueChild.weight) * half)
      ring1

end

open Purelib.Measure in
/-- The exact terminal frontier below any prefix has zero unresolved weight. -/
theorem terminalFrontierAt_unresolved : ∀ (event :
  List.BinaryPrefix.RawEvent) (stem : CCLMeasureWord),
    Measure.unresolvedWeight (terminalFrontierAt stem event) = 0
  | .empty, stem => by
      simp only [-eq_self, -iff_self, terminalFrontierAt, Measure.unresolvedWeight,
        BinaryPrefix.rawClassified, BinaryPrefix.rawPrefixAtom, add_zero]; try rfl
  | .full, stem => by
      simp only [-eq_self, -iff_self, terminalFrontierAt, Measure.unresolvedWeight,
        BinaryPrefix.rawClassified, BinaryPrefix.rawPrefixAtom, add_zero]; try rfl
  | .branch falseChild trueChild, stem => by
      rw [terminalFrontierAt, Measure.unresolvedWeight_append,
        terminalFrontierAt_unresolved falseChild,
        terminalFrontierAt_unresolved trueChild, add_zero]

/-- Expand the raw decision tree from the empty prefix into its exact ordered terminal classified frontier. -/
@[expose] def terminalFrontier (event : List.BinaryPrefix.RawEvent) :
    List (Measure.Classified CCLMeasureWord) :=
  terminalFrontierAt [] event

/-- The full terminal classified frontier has total weight one. -/
theorem terminalFrontier_weight (event : List.BinaryPrefix.RawEvent) :
    Measure.classifiedWeight event.terminalFrontier = 1 := by
  rw [terminalFrontier, terminalFrontierAt_weight,
    List.BinaryPrefix.rawPrefixWeight_nil]

section
open Purelib.Data.Rat
/-- The full terminal frontier's lower weight is the raw event's exact weight. -/
theorem terminalFrontier_lower (event : List.BinaryPrefix.RawEvent) :
    Measure.lowerWeight event.terminalFrontier = event.weight := by
  rw [terminalFrontier, terminalFrontierAt_lower,
    List.BinaryPrefix.rawPrefixWeight_nil,
    Fraction.Field.one_mul]

/-- The full terminal frontier's upper weight is the raw event's exact weight. -/
theorem terminalFrontier_upper (event : List.BinaryPrefix.RawEvent) :
    Measure.upperWeight event.terminalFrontier = event.weight := by
  rw [terminalFrontier, terminalFrontierAt_upper,
    List.BinaryPrefix.rawPrefixWeight_nil,
    Fraction.Field.one_mul]

end

/-- The full terminal classified frontier has zero unresolved weight. -/
theorem terminalFrontier_unresolved (event : List.BinaryPrefix.RawEvent)
  :
    Measure.unresolvedWeight event.terminalFrontier = 0 :=
  terminalFrontierAt_unresolved event []
end

end RawEvent

end Purelib.Data.List.BinaryPrefix

end
