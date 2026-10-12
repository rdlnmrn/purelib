module
public import Purelib.Data.Fin
public import Purelib.Data.List.OfFn.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Approximation.Relation.Fibre
public import Purelib.Approximation.Relation.Loop
import Purelib.Approximation.Relation.Refinement
import Purelib.Data.Fin.Bijection.Basic

@[expose] public section

/-!
# Executable finite-relation examples

These tiny fibres exercise the two cases which a fixed-cardinality
permutation-only interface cannot express: one owner splitting into two new
owners, and an unresolved collision cluster becoming separated.  A final
two-label loop demonstrates the explicitly certified permutation
specialization.
-/

namespace Purelib.Examples.Approximation.Relation.WorkedExamples

open Purelib.Approximation.Relation
open Purelib

/-- A data-carrying proof that two natural-number candidates differ. -/
def NatSeparated (left right : Nat) : Type := PLift (left ≠ right)

/-- The trivial certificate attached to each natural-number candidate. -/
def NatWitness (_value : Nat) : Type := PUnit

/-- The certified one-candidate fibre at zero with no unresolved clusters. -/
def singletonFibre : Approximation.Relation.Fibre Nat NatSeparated
  NatWitness where
  count := 1
  candidate _ := 0
  certified _ := PUnit.unit
  clusterCount := 0
  cluster := Fin.elim0
  pairResolution := by
    intro left right different
    have leftZero : left.val = 0 := by
      have bound := left.isLt
      omega0
    have rightZero : right.val = 0 := by
      have bound := right.isLt
      omega0
    exact (different (Fin.ext (leftZero.trans rightZero.symm))).elim

/-- The two-candidate fibre at zero and one with explicit separation evidence. -/
def separatedPair : Approximation.Relation.Fibre Nat NatSeparated
  NatWitness :=
  Approximation.Relation.Fibre.ofPairwiseSeparated 2 (fun label => label.val)
    (fun _ => PUnit.unit)
    (by
      intro left right different
      exact ⟨fun valuesEqual => different (Fin.ext valuesEqual)⟩)

/-- The unrestricted continuation relation between natural-number candidates. -/
def AlwaysContinues (_old _new : Nat) : Prop := True

/-- A refinement sending the original singleton label to both separated labels.

Retains the finite child enumeration, an original owner for every child and the trivial continuation evidence. -/
def splitRefinement :
    Approximation.Relation.Refinement singletonFibre
      separatedPair
      AlwaysContinues where
  continues _ := List.ofFn id
  covers newLabel :=
    ⟨⟨0, by decide⟩, Purelib.Data.List.OfFn.Basic.mem_ofFn.mpr ⟨newLabel, rfl⟩⟩
  persists := by
    intro _oldLabel _newLabel _member
    trivial

/-- The retained singleton refinement lists exactly two children. -/
theorem split_has_two_children :
    (splitRefinement.continues ⟨0, by decide⟩).length = 2 := by
  decide

/-- Every separated child belongs to its retained original parent's list. -/
theorem every_split_child_has_owner (label : Fin separatedPair.count) :
    label ∈ splitRefinement.continues
      (splitRefinement.ownerOf label) :=
  splitRefinement.ownerOf_contains label

/-- Two retained labels at zero with one cluster containing both labels.

Pair resolution records original cluster membership rather than asserting separation of equal candidate values. -/
def clusteredPair : Approximation.Relation.Fibre Nat NatSeparated
  NatWitness where
  count := 2
  candidate _ := 0
  certified _ := PUnit.unit
  clusterCount := 1
  cluster _ := List.ofFn id
  pairResolution := by
    intro left right _different
    exact Sum.inr
      ⟨⟨0, by decide⟩,
        Purelib.Data.List.OfFn.Basic.mem_ofFn.mpr ⟨left, rfl⟩,
        Purelib.Data.List.OfFn.Basic.mem_ofFn.mpr ⟨right, rfl⟩⟩

/-- Resolve the two-label cluster while retaining each original label. -/
def clusterSplit :
    Approximation.Relation.Refinement clusteredPair
      separatedPair
      AlwaysContinues where
  continues label := [label]
  covers label := ⟨label, .head _⟩
  persists := by
    intro _oldLabel _newLabel _member
    trivial

/-- The clustered refinement keeps each label as its singleton child. -/
@[simp] theorem cluster_split_retains_label (label : Fin 2) :
    clusterSplit.continues label = [label] := rfl

/-- The explicit permutation swapping the two finite labels. -/
def swap : Fin 2 → Fin 2 :=
  Data.Fin.casesByRecursion ⟨1, by decide⟩ (fun _ => ⟨0, by decide⟩)

/-- Applying the retained two-label swap twice returns the original label. -/
theorem swap_involutive (label : Fin 2) : swap
  (swap label) = label := by
  refine Data.Fin.casesByRecursion ?_ (fun tail => ?_) label
  · rfl
  · have tail_eq : tail = ⟨0, by decide⟩ := Fin.ext (by
      have bound := tail.isLt
      omega0)
    subst tail
    rfl

/-- The original separated pair refined through its swapped label assignment. -/
def swapRefinement :
    Approximation.Relation.Refinement separatedPair
      separatedPair
      AlwaysContinues where
  continues label := [swap label]
  covers label :=
    ⟨swap label, by
      rewrite [swap_involutive]
      exact .head _⟩
  persists := by
    intro _oldLabel _newLabel _member
    trivial

/-- The collision-free loop retaining the swap and its exact two inverse identities. -/
def swapLoop : Approximation.Relation.Loop.CollisionFreeLoop
  swapRefinement where
  forward := swap
  backward := swap
  leftInverse := swap_involutive
  rightInverse := swap_involutive
  continues_eq _ := rfl

/-- The retained loop permutation sends label zero to label one. -/
theorem swap_loop_moves_zero :
    swapLoop.permutation.forward ⟨0, by decide⟩ = ⟨1, by decide⟩ := rfl

end Purelib.Examples.Approximation.Relation.WorkedExamples

end
