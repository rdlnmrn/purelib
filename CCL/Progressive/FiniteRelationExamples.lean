import CCL.Progressive.FiniteRelation

/-!
# Executable finite-relation examples

These tiny fibres exercise the two cases which a fixed-cardinality
permutation-only interface cannot express: one owner splitting into two new
owners, and an unresolved collision cluster becoming separated.  A final
two-label loop demonstrates the explicitly certified permutation
specialization.
-/

namespace CCL.FiniteMultivaluedRelationExamples

open CCL.FiniteMultivaluedRelation

def NatSeparated (left right : Nat) : Type := PLift (left ≠ right)

def NatWitness (_value : Nat) : Type := PUnit

def singletonFibre : Fibre Nat NatSeparated NatWitness where
  count := 1
  candidate _ := 0
  certified _ := PUnit.unit
  clusterCount := 0
  cluster := Fin.elim0
  pairResolution := by
    intro left right different
    exact (different (Subsingleton.elim left right)).elim

def separatedPair : Fibre Nat NatSeparated NatWitness :=
  Fibre.ofPairwiseSeparated 2 (fun label => label.val)
    (fun _ => PUnit.unit)
    (by
      intro left right different
      exact ⟨fun valuesEqual => different (Fin.ext valuesEqual)⟩)

def AlwaysContinues (_old _new : Nat) : Prop := True

/-- One old owner explicitly continues to both new labels. -/
def splitRefinement :
    Refinement singletonFibre separatedPair AlwaysContinues where
  continues _ := List.ofFn id
  covers newLabel :=
    ⟨⟨0, by decide⟩, List.mem_ofFn.mpr ⟨newLabel, rfl⟩⟩
  persists := by
    intro _oldLabel _newLabel _member
    trivial

theorem split_has_two_children :
    (splitRefinement.continues ⟨0, by decide⟩).length = 2 := by
  decide

theorem every_split_child_has_owner (label : Fin separatedPair.count) :
    label ∈ splitRefinement.continues (splitRefinement.ownerOf label) :=
  splitRefinement.ownerOf_contains label

/-- Two currently indistinguishable candidates are kept in one explicit
cluster instead of being assigned a fabricated separation. -/
def clusteredPair : Fibre Nat NatSeparated NatWitness where
  count := 2
  candidate _ := 0
  certified _ := PUnit.unit
  clusterCount := 1
  cluster _ := List.ofFn id
  pairResolution := by
    intro left right _different
    exact Sum.inr
      ⟨⟨0, by decide⟩,
        List.mem_ofFn.mpr ⟨left, rfl⟩,
        List.mem_ofFn.mpr ⟨right, rfl⟩⟩

/-- Splitting the collision retains the caller's two persistent labels. -/
def clusterSplit :
    Refinement clusteredPair separatedPair AlwaysContinues where
  continues label := [label]
  covers label := ⟨label, by simp⟩
  persists := by
    intro _oldLabel _newLabel _member
    trivial

@[simp] theorem cluster_split_retains_label (label : Fin 2) :
    clusterSplit.continues label = [label] := rfl

/-- The nontrivial permutation of two labels, written without any global
enumeration or choice. -/
def swap : Fin 2 → Fin 2 :=
  Fin.cases ⟨1, by decide⟩ (fun _ => ⟨0, by decide⟩)

theorem swap_involutive (label : Fin 2) : swap (swap label) = label := by
  refine Fin.cases ?_ (fun tail => ?_) label
  · rfl
  · have tail_eq : tail = ⟨0, by decide⟩ := Subsingleton.elim _ _
    subst tail
    rfl

def swapRefinement :
    Refinement separatedPair separatedPair AlwaysContinues where
  continues label := [swap label]
  covers label :=
    ⟨swap label, by rw [swap_involutive]; simp⟩
  persists := by
    intro _oldLabel _newLabel _member
    trivial

def swapLoop : CollisionFreeLoop swapRefinement where
  forward := swap
  backward := swap
  leftInverse := swap_involutive
  rightInverse := swap_involutive
  continues_eq _ := rfl

theorem swap_loop_moves_zero :
    swapLoop.permutation.forward ⟨0, by decide⟩ = ⟨1, by decide⟩ := rfl

end CCL.FiniteMultivaluedRelationExamples
