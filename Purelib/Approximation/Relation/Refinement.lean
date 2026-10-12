module

public import Purelib.Approximation.Relation.Fibre
public import Purelib.Data.List.Flatten
public import Purelib.Data.List.Membership
import Purelib.Data.List.Append
meta import Mathlib.Tactic.Linter.Lint
public import Init.Data.List.Lemmas
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Relation

open Purelib.Data.List

section
/-!
# Finite multivalued relations with persistent ownership

The fibre displayed here is finite and local.  Refinement maps one old label
to a finite family of new labels, so clusters may split or merge without being
misrepresented as permutations.  A permutation is recovered only from an
explicit collision-free loop certificate.

No declaration claims that a displayed fibre enumerates an unbounded or
completed mathematical fibre.
-/

public section

namespace Purelib.Approximation.Relation

universe u v w x y

set_option genInjectivity false in
/-- One finite refinement between displayed fibres. The continuation family may contain zero, one, or several new
labels. `covers` stores an explicit old owner for every new label, and `persists` certifies each displayed edge. -/
structure Refinement
    {Output : Type u} {Separated : Output → Output → Type v}
    {OldWitness : Output → Type w} {NewWitness : Output → Type x}
    (old : Fibre Output Separated OldWitness)
    (new : Fibre Output Separated NewWitness)
    (Continues : Output → Output → Prop) : Type (max u v w x) where
  /-- The finite new-label family continuing each original label. -/ continues : Fin old.count → List (Fin new.count)
  /-- An explicit old owner and membership proof for every new label. -/ covers : ∀ newLabel,
    { oldLabel : Fin old.count // newLabel ∈ continues oldLabel }
  /-- Every displayed continuation edge satisfies the specified relation. -/ persists : ∀ oldLabel newLabel, newLabel ∈
    continues oldLabel →
    Continues (old.candidate oldLabel) (new.candidate newLabel)

constructive_injectivity Refinement

namespace Refinement

/-- A singleton continuation induced by explicit inverse label maps. Keeping the casts here prevents concrete adapters
from repeatedly unfolding large fibre definitions merely to establish equal label cardinalities. -/
@[expose] def ofLabelEquivalence
    {Output : Type u} {Separated : Output → Output → Type v}
    {OldWitness : Output → Type w} {NewWitness : Output → Type x}
    {old : Fibre Output Separated OldWitness}
    {new : Fibre Output Separated NewWitness}
    {Continues : Output → Output → Prop}
    (forward : Fin old.count → Fin new.count)
    (backward : Fin new.count → Fin old.count)
    (rightInverse : ∀ label, forward (backward label) = label)
    (persists : ∀ label,
      Continues (old.candidate label) (new.candidate (forward label))) :
    Refinement old new Continues where
  continues label := [forward label]
  covers label :=
    ⟨backward label, by rw [rightInverse]; exact List.mem_cons_self⟩
  persists := by
    intro oldLabel newLabel member
    have equal : newLabel = forward oldLabel := Membership.mem_singleton.mp member
    subst newLabel
    exact persists oldLabel

/-- A refinement induced by inverse label maps retains the singleton forward image. -/
@[simp] theorem ofLabelEquivalence_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {OldWitness : Output → Type w} {NewWitness : Output → Type x}
    {old : Fibre Output Separated OldWitness}
    {new : Fibre Output Separated NewWitness}
    {Continues : Output → Output → Prop}
    (forward : Fin old.count → Fin new.count)
    (backward : Fin new.count → Fin old.count)
    (rightInverse : ∀ label, forward (backward label) = label)
    (persists : ∀ label,
      Continues (old.candidate label) (new.candidate (forward label)))
    (label : Fin old.count) :
    (ofLabelEquivalence forward backward rightInverse
      persists).continues label = [forward label] := rfl

/-- Identity continuation displays exactly the same label once. -/
@[expose] def identity
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    {Continues : Output → Output → Prop}
    (fibre : Fibre Output Separated Witness)
    (continuesRefl : ∀ output, Continues output output) :
    Refinement fibre fibre Continues where
  continues label := [label]
  covers label := ⟨label, by exact List.Mem.head []⟩
  persists := by
    intro oldLabel newLabel member
    have equal : newLabel = oldLabel := Membership.mem_singleton.mp member
    subst newLabel
    exact continuesRefl (fibre.candidate oldLabel)

/-- Identity refinement retains exactly the original label. -/
@[simp] theorem identity_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {Witness : Output → Type w}
    {Continues : Output → Output → Prop}
    (fibre : Fibre Output Separated Witness)
    (continuesRefl : ∀ output, Continues output output)
    (label : Fin fibre.count) :
    (identity fibre continuesRefl).continues label = [label] := rfl

/-- Compose owner-to-family maps by finite list flattening. -/
@[expose] def compose
    {Output : Type u} {Separated : Output → Output → Type v}
    {FirstWitness : Output → Type w}
    {MiddleWitness : Output → Type x}
    {LastWitness : Output → Type y}
    {firstFibre : Fibre Output Separated FirstWitness}
    {middleFibre : Fibre Output Separated MiddleWitness}
    {lastFibre : Fibre Output Separated LastWitness}
    {Continues : Output → Output → Prop}
    (first : Refinement firstFibre middleFibre Continues)
    (second : Refinement middleFibre lastFibre Continues)
    (continuesTrans : ∀ {left middle right},
      Continues left middle → Continues middle right → Continues left right) :
    Refinement firstFibre lastFibre Continues where
  continues oldLabel :=
    (first.continues oldLabel).flatMap second.continues
  covers newLabel := by
    let middleOwner := second.covers newLabel
    let oldOwner := first.covers middleOwner.val
    exact ⟨oldOwner.val, Flatten.mem_flatMap.mpr
      ⟨middleOwner.val, oldOwner.property, middleOwner.property⟩⟩
  persists := by
    intro oldLabel newLabel member
    rcases Flatten.mem_flatMap.mp member with
      ⟨middleLabel, middleMember, newMember⟩
    exact continuesTrans
      (first.persists oldLabel middleLabel middleMember)
      (second.persists middleLabel newLabel newMember)

/-- Composite refinement flattens the two retained continuation families. -/
@[simp] theorem compose_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {FirstWitness : Output → Type w}
    {MiddleWitness : Output → Type x}
    {LastWitness : Output → Type y}
    {firstFibre : Fibre Output Separated FirstWitness}
    {middleFibre : Fibre Output Separated MiddleWitness}
    {lastFibre : Fibre Output Separated LastWitness}
    {Continues : Output → Output → Prop}
    (first : Refinement firstFibre middleFibre Continues)
    (second : Refinement middleFibre lastFibre Continues)
    (continuesTrans : ∀ {left middle right},
      Continues left middle → Continues middle right → Continues left right)
    (label : Fin firstFibre.count) :
    (compose first second continuesTrans).continues label =
      (first.continues label).flatMap second.continues := rfl

/-- Left identity of finite continuation families. -/
theorem identity_compose_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {FirstWitness : Output → Type w}
    {SecondWitness : Output → Type x}
    {firstFibre : Fibre Output Separated FirstWitness}
    {secondFibre : Fibre Output Separated SecondWitness}
    {Continues : Output → Output → Prop}
    (refinement : Refinement firstFibre secondFibre Continues)
    (continuesRefl : ∀ output, Continues output output)
    (continuesTrans : ∀ {left middle right},
      Continues left middle → Continues middle right → Continues left right)
    (label : Fin firstFibre.count) :
    (compose (identity
      firstFibre continuesRefl) refinement
      continuesTrans).continues label = refinement.continues label := by
  simp only [compose_continues,
    identity_continues, Flatten.flatMap_cons,
    -eq_self, -iff_self]
  change refinement.continues label ++ [] = refinement.continues label
  exact Append.append_nil _

/-- Right identity of finite continuation families. -/
theorem compose_identity_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {FirstWitness : Output → Type w}
    {SecondWitness : Output → Type x}
    {firstFibre : Fibre Output Separated FirstWitness}
    {secondFibre : Fibre Output Separated SecondWitness}
    {Continues : Output → Output → Prop}
    (refinement : Refinement firstFibre secondFibre Continues)
    (continuesRefl : ∀ output, Continues output output)
    (continuesTrans : ∀ {left middle right},
      Continues left middle → Continues middle right → Continues left right)
    (label : Fin firstFibre.count) :
    (compose refinement
      (identity secondFibre continuesRefl)
      continuesTrans).continues label = refinement.continues label := by
  simp only [compose_continues]
  induction refinement.continues label with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [Flatten.flatMap_cons, identity_continues,
        List.singleton_append, inductionHypothesis, -eq_self, -iff_self]
      rfl

/-- Subdividing a finite path does not change its endpoint owner family: composition is associative at the executable
continuation-list level. -/
theorem compose_assoc_continues
    {Output : Type u} {Separated : Output → Output → Type v}
    {FirstWitness : Output → Type w}
    {SecondWitness : Output → Type x}
    {ThirdWitness : Output → Type y}
    {FourthWitness : Output → Type}
    {firstFibre : Fibre Output Separated FirstWitness}
    {secondFibre : Fibre Output Separated SecondWitness}
    {thirdFibre : Fibre Output Separated ThirdWitness}
    {fourthFibre : Fibre Output Separated FourthWitness}
    {Continues : Output → Output → Prop}
    (first : Refinement firstFibre secondFibre Continues)
    (second : Refinement secondFibre thirdFibre Continues)
    (third : Refinement thirdFibre fourthFibre Continues)
    (continuesTrans : ∀ {left middle right},
      Continues left middle → Continues middle right → Continues left right)
    (label : Fin firstFibre.count) :
    (Refinement.compose (Refinement.compose first
      second continuesTrans) third
        continuesTrans).continues label =
      (Refinement.compose first (Refinement.compose
        second third continuesTrans)
        continuesTrans).continues label := by
  rw [Refinement.compose_continues,
    Refinement.compose_continues,
    Flatten.flatMap_assoc_direct second.continues third.continues]
  apply Flatten.flatMap_congr_direct _ _ (first.continues label)
  intro middleLabel _member
  exact Refinement.compose_continues second third continuesTrans middleLabel

/-- Every displayed new label has concrete finite provenance. -/
@[expose] def ownerOf
    {Output : Type u} {Separated : Output → Output → Type v}
    {OldWitness : Output → Type w} {NewWitness : Output → Type x}
    {old : Fibre Output Separated OldWitness}
    {new : Fibre Output Separated NewWitness}
    {Continues : Output → Output → Prop}
    (refinement : Refinement old new Continues)
    (newLabel : Fin new.count) : Fin old.count :=
  (refinement.covers newLabel).val

/-- The new label belongs to its retained old owner's continuation family. -/
theorem ownerOf_contains
    {Output : Type u} {Separated : Output → Output → Type v}
    {OldWitness : Output → Type w} {NewWitness : Output → Type x}
    {old : Fibre Output Separated OldWitness}
    {new : Fibre Output Separated NewWitness}
    {Continues : Output → Output → Prop}
    (refinement : Refinement old new Continues)
    (newLabel : Fin new.count) :
    newLabel ∈ refinement.continues (refinement.ownerOf newLabel) :=
  (refinement.covers newLabel).property

end Refinement

end Purelib.Approximation.Relation

end

public section
namespace Purelib.Approximation.Relation.Refinement

namespace mk

end mk

end Purelib.Approximation.Relation.Refinement
end
