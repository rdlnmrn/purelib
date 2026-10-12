module
import Purelib.Data.List.Append
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Interval.Basic
import Purelib.Measure.Classified.Basic
public import Purelib.Measure.Classified.Split
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic

/-!
# Finite refinement histories

This module closes certified single-cell splits under reflexivity and finite
composition.  It is the finite filtration layer: total weight is conserved,
lower event weight can only rise, upper event weight can only fall, and the
unresolved budget can only shrink.
-/

@[expose] public section

namespace Purelib.Measure

/-- Certify refinement of an exact classified frontier by retained mass-preserving splits and their composition.

Each split replaces one original occurrence by its certified children within the same ordered before and after contexts.
-/
inductive FrontierRefines {α : Type} :
    List (Classified α) → List (Classified α) → Prop where
  /-- Every exact frontier refines itself. -/ | refl (frontier : List (Classified α)) :
      Purelib.Measure.FrontierRefines frontier frontier
  /-- Replace the specified original occurrence by its certified children in the exact retained list contexts. -/ |
    split (before after : List (Classified α))
      (parent : Classified α) (children : Split (β := α) parent) :
      Purelib.Measure.FrontierRefines
        (before ++ children.children ++ after)
        (before ++ [parent] ++ after)
  /-- Compose two refinement certificates through the same exact intermediate frontier. -/ | trans {inner middle outer :
    List (Classified α)} :
      Purelib.Measure.FrontierRefines inner middle → Purelib.Measure.FrontierRefines middle outer →
      Purelib.Measure.FrontierRefines inner outer

namespace FrontierRefines

open Purelib in
open Purelib.Data.Rat in
/-- A certified frontier refinement narrows the exact event-bound interval. -/
theorem eventBound_refines {α : Type}
    {inner outer : List (Classified α)}
    (refines : Measure.FrontierRefines inner outer) :
    Interval.Refines (eventBound inner) (eventBound outer) := by
  induction refines with
  | refl frontier => exact Interval.Refines.refl (eventBound frontier)
  | split before after parent children =>
      exact children.frontier_eventBound_refines before after
  | trans innerMiddle middleOuter innerHypothesis middleHypothesis =>
      exact innerHypothesis.trans middleHypothesis

section
open Purelib
/-- A certified frontier refinement can only increase its lower classified weight. -/
theorem lower_mono {α : Type} {inner outer : List (Classified α)}
    (refines : Measure.FrontierRefines inner outer) :
    lowerWeight outer ≤ lowerWeight inner :=
  refines.eventBound_refines.lower

/-- A certified frontier refinement can only decrease its upper classified weight. -/
theorem upper_antitone {α : Type} {inner outer : List (Classified α)}
    (refines : Measure.FrontierRefines inner outer) :
    upperWeight inner ≤ upperWeight outer :=
  refines.eventBound_refines.upper

/-- A certified frontier refinement can only decrease its unresolved weight. -/
theorem unresolved_le {α : Type} {inner outer : List (Classified α)}
    (refines : Measure.FrontierRefines inner outer) :
    unresolvedWeight inner ≤ unresolvedWeight outer := by
  rw [← Measure.eventBound_width, ← Measure.eventBound_width]
  exact refines.eventBound_refines.width_le

end

open Purelib in
open Purelib.Data.Rat in
/-- A frontier refining an epsilon-resolved frontier remains epsilon-resolved. -/
theorem resolves {α : Type} {inner outer : List (Classified α)}
    (refines : Measure.FrontierRefines inner outer) {epsilon : Fraction.Rational}
    (outerResolves : Resolves outer epsilon) : Resolves inner epsilon :=
  (refines.unresolved_le).trans_lt outerResolves

open Purelib.Data.List in
/-- Replacing one retained occurrence by its certified children preserves total weight in the exact surrounding
contexts. -/
private theorem classifiedWeight_context_split
    {α : Type} (before after : List (Classified α))
    (parent : Classified α) (children : Split (β := α) parent) :
    classifiedWeight (before ++ children.children ++ after) =
      classifiedWeight (before ++ [parent] ++ after) := by
  rw [Append.append_assoc, Append.append_assoc]
  rw [classifiedWeight_append before (children.children ++ after),
    classifiedWeight_append children.children after,
    classifiedWeight_append before ([parent] ++ after),
    classifiedWeight_append [parent] after]
  simp only [classifiedWeight, add_zero]
  rw [children.conserved]

open Purelib in
open Purelib.Data.List in
/-- Certified frontier refinement preserves the exact total classified weight. -/
theorem weight_conserved {α : Type}
    {inner outer : List (Classified α)}
    (refines : Measure.FrontierRefines inner outer) :
    classifiedWeight inner = classifiedWeight outer := by
  induction refines with
  | refl frontier => rfl
  | split before after parent children =>
      exact classifiedWeight_context_split before after parent children
  | trans innerMiddle middleOuter innerHypothesis middleHypothesis =>
      exact innerHypothesis.trans middleHypothesis

end FrontierRefines

end Purelib.Measure

end
