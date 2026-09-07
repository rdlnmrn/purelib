import FiniteMeasure.Content

/-!
# Finite refinement histories

This module closes certified single-cell splits under reflexivity and finite
composition.  It is the finite filtration layer: total weight is conserved,
lower event weight can only rise, upper event weight can only fall, and the
unresolved budget can only shrink.
-/

namespace FiniteMeasure

/-- Constructively generated refinement of one displayed finite frontier by
finitely many certified cell splits. -/
inductive FrontierRefines {α : Type} :
    List (Classified α) → List (Classified α) → Prop where
  | refl (frontier : List (Classified α)) :
      FrontierRefines frontier frontier
  | split (before after : List (Classified α))
      (parent : Classified α) (children : Split (β := α) parent) :
      FrontierRefines
        (before ++ children.children ++ after)
        (before ++ [parent] ++ after)
  | trans {inner middle outer : List (Classified α)} :
      FrontierRefines inner middle → FrontierRefines middle outer →
      FrontierRefines inner outer

namespace FrontierRefines

/-- Every generated finite frontier refinement narrows its event enclosure. -/
theorem eventBound_refines {α : Type}
    {inner outer : List (Classified α)}
    (refines : FrontierRefines inner outer) :
    Bound.Refines (eventBound inner) (eventBound outer) := by
  induction refines with
  | refl frontier => exact Bound.Refines.refl (eventBound frontier)
  | split before after parent children =>
      exact children.frontier_eventBound_refines before after
  | trans innerMiddle middleOuter innerHypothesis middleHypothesis =>
      exact innerHypothesis.trans middleHypothesis

/-- Lower certified event content is monotone under finite refinement. -/
theorem lower_mono {α : Type} {inner outer : List (Classified α)}
    (refines : FrontierRefines inner outer) :
    lowerWeight outer ≤ lowerWeight inner :=
  refines.eventBound_refines.lower

/-- Upper certified event content is antitone under finite refinement. -/
theorem upper_antitone {α : Type} {inner outer : List (Classified α)}
    (refines : FrontierRefines inner outer) :
    upperWeight inner ≤ upperWeight outer :=
  refines.eventBound_refines.upper

/-- The exact unresolved rational budget cannot increase under refinement. -/
theorem unresolved_le {α : Type} {inner outer : List (Classified α)}
    (refines : FrontierRefines inner outer) :
    unresolvedWeight inner ≤ unresolvedWeight outer := by
  rw [← eventBound_width, ← eventBound_width]
  exact refines.eventBound_refines.width_le

/-- Once a finite event frontier meets an accuracy request, every certified
later frontier meets the same request. -/
theorem resolves {α : Type} {inner outer : List (Classified α)}
    (refines : FrontierRefines inner outer) {epsilon : Coordinate}
    (outerResolves : Resolves outer epsilon) : Resolves inner epsilon :=
  (refines.unresolved_le).trans_lt outerResolves

private theorem classifiedWeight_context_split
    {α : Type} (before after : List (Classified α))
    (parent : Classified α) (children : Split (β := α) parent) :
    classifiedWeight (before ++ children.children ++ after) =
      classifiedWeight (before ++ [parent] ++ after) := by
  rw [List.append_assoc, List.append_assoc]
  rw [classifiedWeight_append before (children.children ++ after),
    classifiedWeight_append children.children after,
    classifiedWeight_append before ([parent] ++ after),
    classifiedWeight_append [parent] after]
  simp only [classifiedWeight, add_zero]
  rw [children.conserved]

/-- Refinement redistributes but never creates or destroys displayed total
weight. -/
theorem weight_conserved {α : Type}
    {inner outer : List (Classified α)}
    (refines : FrontierRefines inner outer) :
    classifiedWeight inner = classifiedWeight outer := by
  induction refines with
  | refl frontier => rfl
  | split before after parent children =>
      exact classifiedWeight_context_split before after parent children
  | trans innerMiddle middleOuter innerHypothesis middleHypothesis =>
      exact innerHypothesis.trans middleHypothesis

end FrontierRefines

end FiniteMeasure
