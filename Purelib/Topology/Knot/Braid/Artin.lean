module
import Purelib.Algebra.Group.Int
import Purelib.Data.List.Append
import Purelib.Data.Fin.Bijection.Basic
import Purelib.Data.Fin.Bijection.Transposition
import Purelib.Topology.Knot.Braid.Basic
import Purelib.Topology.Knot.Braid.Word.Basic
public import Purelib.Topology.Knot.Braid.Word.Writhe
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Int.Defs

namespace Purelib.Topology.Knot.Braid.Artin

open Purelib.Data.Fin.Bijection
open Purelib.Data.Fin.Bijection.Basic

public section

/-!
# Constructive Artin relations on finite braid words

The braid relation is represented by finite local rewrites under displayed
word contexts.  Its reflexive, symmetric, transitive closure is an explicit
proof object rather than a quotient.  The main soundness theorems show that
every such proof preserves both the executable strand permutation and the
integer writhe.
-/

open Purelib.Topology.Knot.Braid

namespace Generator

/-- The lower generator in one displayed adjacent Artin pair. -/
@[expose] def lower {strands : Nat} (index : Fin (strands - 2))
    (sign : CrossingSign) : Generator strands :=
  { index := ⟨index.val, by omega⟩
    sign := sign }

/-- The upper generator in one displayed adjacent Artin pair. -/
@[expose] def upper {strands : Nat} (index : Fin (strands - 2))
    (sign : CrossingSign) : Generator strands :=
  { index := ⟨index.val + 1, by omega⟩
    sign := sign }

/-- The original adjacent lower and upper generators share their middle strand. -/
theorem lower_right_eq_upper_left {strands : Nat}
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    (lower index sign).right = (upper index sign).left := by
  apply Fin.ext
  rfl

/-- The outer endpoints of the original adjacent generator pair are distinct. -/
theorem lower_left_ne_upper_right {strands : Nat}
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    (lower index sign).left ≠ (upper index sign).right := by
  intro equal
  have values := congrArg Fin.val equal
  change index.val = index.val + 1 + 1 at values
  omega

/-- Two generator indices separated by at least one untouched strand have disjoint transposition endpoints. -/
theorem disjoint_of_far {strands : Nat}
    (first second : Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    first.left ≠ second.left ∧ first.left ≠ second.right ∧
      first.right ≠ second.left ∧ first.right ≠ second.right := by
  rcases far with forward | backward
  · constructor
    · intro equal
      have values := congrArg Fin.val equal
      change first.index.val = second.index.val at values
      omega
    · constructor
      · intro equal
        have values := congrArg Fin.val equal
        change first.index.val = second.index.val + 1 at values
        omega
      · constructor
        · intro equal
          have values := congrArg Fin.val equal
          change first.index.val + 1 = second.index.val at values
          omega
        · intro equal
          have values := congrArg Fin.val equal
          change first.index.val + 1 = second.index.val + 1 at values
          omega
  · constructor
    · intro equal
      have values := congrArg Fin.val equal
      change first.index.val = second.index.val at values
      omega
    · constructor
      · intro equal
        have values := congrArg Fin.val equal
        change first.index.val = second.index.val + 1 at values
        omega
      · constructor
        · intro equal
          have values := congrArg Fin.val equal
          change first.index.val + 1 = second.index.val at values
          omega
        · intro equal
          have values := congrArg Fin.val equal
          change first.index.val + 1 = second.index.val + 1 at values
          omega

end Generator

namespace Word

/-- The original braid words induce pointwise equal executable strand permutations. -/
@[expose] def PermutationSame {strands : Nat} (left right : Word strands) : Prop :=
  Data.Fin.Bijection.Same
    left.permutation right.permutation

/-- Every original braid word has the same strand permutation as itself. -/
theorem permutationSame_refl {strands : Nat} (word : Word strands) :
    Word.PermutationSame word word := fun _ => rfl

/-- Reverse pointwise equality of the original word permutations. -/
theorem permutationSame_symm {strands : Nat} {left right : Word strands}
    (same : Word.PermutationSame left right) : Word.PermutationSame right left :=
  Data.Fin.Bijection.same_symm same

/-- Compose pointwise equalities of three original word permutations. -/
theorem permutationSame_trans {strands : Nat} {first second third : Word strands}
    (firstSecond : Word.PermutationSame first second)
    (secondThird : Word.PermutationSame second third) :
    Word.PermutationSame first third :=
  Data.Fin.Bijection.same_trans firstSecond secondThird

/-- Prefixing the same original word preserves permutation equality. -/
theorem permutationSame_append_left {strands : Nat}
    (before : Word strands) {left right : Word strands}
    (same : Word.PermutationSame left right) :
    Word.PermutationSame (before ++ left) (before ++ right) := by
  intro index
  calc
    (before ++ left).permutation.forward index =
        left.permutation.forward (before.permutation.forward index) :=
      Word.permutation_append before left index
    _ = right.permutation.forward (before.permutation.forward index) :=
      same (before.permutation.forward index)
    _ = (before ++ right).permutation.forward index :=
      (Word.permutation_append before right index).symm

/-- Appending the same original suffix preserves permutation equality. -/
theorem permutationSame_append_right {strands : Nat}
    {left right : Word strands} (suffix : Word strands)
    (same : Word.PermutationSame left right) :
    Word.PermutationSame (left ++ suffix) (right ++ suffix) := by
  intro index
  calc
    (left ++ suffix).permutation.forward index =
        suffix.permutation.forward (left.permutation.forward index) :=
      Word.permutation_append left suffix index
    _ = suffix.permutation.forward (right.permutation.forward index) := by
      rw [same]
    _ = (right ++ suffix).permutation.forward index :=
      (Word.permutation_append right suffix index).symm

/-- The same original prefix and suffix preserve permutation equality of the middle words. -/
theorem permutationSame_context {strands : Nat}
    (before after : Word strands) {left right : Word strands}
    (same : Word.PermutationSame left right) :
    Word.PermutationSame (before ++ left ++ after)
      (before ++ right ++ after) :=
  Word.permutationSame_append_right after
    (Word.permutationSame_append_left before same)

/-- An original generator followed by its reverse induces the empty word's permutation. -/
theorem cancellation_permutationSame {strands : Nat}
    (generator : Generator strands) :
    Word.PermutationSame [generator, generator.reverse] [] := by
  intro index
  change Transposition.swapIndices generator.left generator.right
      (Transposition.swapIndices generator.left generator.right index) = index
  exact Transposition.swapIndices_involutive generator.left generator.right index

/-- Original generators with disjoint adjacent strand pairs commute as executable permutations. -/
theorem far_permutationSame {strands : Nat}
    (first second : Generator strands)
    (far : first.index.val + 1 < second.index.val ∨
      second.index.val + 1 < first.index.val) :
    Word.PermutationSame [first, second] [second, first] := by
  intro index
  change Transposition.swapIndices second.left second.right
      (Transposition.swapIndices first.left first.right index) =
    Transposition.swapIndices first.left first.right
      (Transposition.swapIndices second.left second.right index)
  obtain ⟨leftLeft, leftRight, rightLeft, rightRight⟩ :=
    Artin.Generator.disjoint_of_far first second far
  exact Transposition.swapIndices_commute_of_disjoint leftLeft leftRight rightLeft
    rightRight index

/-- The two original three-generator Artin words induce the same strand permutation. -/
theorem artin_permutationSame {strands : Nat}
    (index : Fin (strands - 2)) (sign : CrossingSign) :
    Word.PermutationSame
      [Artin.Generator.lower index sign, Artin.Generator.upper index sign,
        Artin.Generator.lower index sign]
      [Artin.Generator.upper index sign, Artin.Generator.lower index sign,
        Artin.Generator.upper index sign] := by
  intro strand
  let lower := Artin.Generator.lower index sign
  let upper := Artin.Generator.upper index sign
  have shared : lower.right = upper.left :=
    Artin.Generator.lower_right_eq_upper_left index sign
  have outside : lower.left ≠ upper.right :=
    Artin.Generator.lower_left_ne_upper_right index sign
  change Transposition.swapIndices lower.left lower.right
      (Transposition.swapIndices upper.left upper.right
        (Transposition.swapIndices lower.left lower.right strand)) =
    Transposition.swapIndices upper.left upper.right
      (Transposition.swapIndices lower.left lower.right
        (Transposition.swapIndices upper.left upper.right strand))
  rw [← shared]
  exact Transposition.swapIndices_braid lower.left_ne_right outside upper.left_ne_right strand

end Word

/-! ## Local rewrites and their finite closure -/

/-- One finite contextual Artin move on original signed braid words.

The constructors retain generator cancellation, disjoint commutation or the adjacent three-strand relation with their
exact surrounding words. -/
inductive Rewrite {strands : Nat} : Word strands → Word strands → Prop
  /-- Remove an original generator and its reverse inside the retained word context. -/ | cancel (before after : Word
    strands) (generator : Generator strands) :
      Purelib.Topology.Knot.Braid.Artin.Rewrite (before ++ [generator, generator.reverse] ++ after)
        (before ++ after)
  /-- Exchange the two original separated generators inside their retained word context. -/ | far (before after : Word
    strands) (first second : Generator strands)
      (separated : first.index.val + 1 < second.index.val ∨
        second.index.val + 1 < first.index.val) :
      Purelib.Topology.Knot.Braid.Artin.Rewrite (before ++ [first, second] ++ after)
        (before ++ [second, first] ++ after)
  /-- Apply the original adjacent three-strand relation inside the retained word context. -/ | artin (before after :
    Word strands) (index : Fin (strands - 2))
      (sign : CrossingSign) :
      Purelib.Topology.Knot.Braid.Artin.Rewrite
        (before ++ [Artin.Generator.lower index sign, Artin.Generator.upper index sign,
          Artin.Generator.lower index sign] ++ after)
        (before ++ [Artin.Generator.upper index sign, Artin.Generator.lower index sign,
          Artin.Generator.upper index sign] ++ after)

namespace Rewrite

/-- Append the same original suffix to both sides of a retained Artin rewrite. -/
theorem append_right {strands : Nat} {left right : Word strands}
    (rewrite : Artin.Rewrite left right) (suffix : Word strands) :
    Artin.Rewrite (left ++ suffix) (right ++ suffix) := by
  cases rewrite with
  | cancel before after generator =>
      simpa only [Purelib.Data.List.Append.append_assoc] using
        Artin.Rewrite.cancel before (after ++ suffix) generator
  | far before after first second separated =>
      simpa only [Purelib.Data.List.Append.append_assoc] using
        Artin.Rewrite.far before (after ++ suffix) first second separated
  | artin before after index sign =>
      simpa only [Purelib.Data.List.Append.append_assoc] using
        Artin.Rewrite.artin before (after ++ suffix) index sign

/-- Prefix both sides of a retained Artin rewrite by the same original word. -/
theorem append_left {strands : Nat} (beforeWord : Word strands)
    {left right : Word strands} (rewrite : Artin.Rewrite left right) :
    Artin.Rewrite (beforeWord ++ left) (beforeWord ++ right) := by
  cases rewrite with
  | cancel before after generator =>
      simpa only [Purelib.Data.List.Append.append_assoc] using
        Artin.Rewrite.cancel (beforeWord ++ before) after generator
  | far before after first second separated =>
      simpa only [Purelib.Data.List.Append.append_assoc] using
        Artin.Rewrite.far (beforeWord ++ before) after first second separated
  | artin before after index sign =>
      simpa only [Purelib.Data.List.Append.append_assoc] using
        Artin.Rewrite.artin (beforeWord ++ before) after index sign

/-- Every retained local Artin rewrite preserves the original executable strand permutation. -/
theorem permutationSame {strands : Nat} {left right : Word strands}
    (rewrite : Artin.Rewrite left right) : Artin.Word.PermutationSame left right := by
  cases rewrite with
  | cancel before after generator =>
      simpa only [Purelib.Data.List.Append.append_nil] using
        Artin.Word.permutationSame_context before after
          (Artin.Word.cancellation_permutationSame generator)
  | far before after first second separated =>
      exact Artin.Word.permutationSame_context before after
        (Artin.Word.far_permutationSame first second separated)
  | artin before after index sign =>
      exact Artin.Word.permutationSame_context before after
        (Artin.Word.artin_permutationSame index sign)

/-- Every retained local Artin rewrite preserves the original integer writhe. -/
theorem writhe_eq {strands : Nat} {left right : Word strands}
    (rewrite : Artin.Rewrite left right) : left.writhe = right.writhe := by
  cases rewrite with
  | cancel before after generator =>
      simp only [Word.writhe_append,
        Word.writhe_cons,
        Word.writhe_nil, add_zero,
        Generator.weight_reverse]
      omega
  | far before after first second separated =>
      simp only [Word.writhe_append,
        Word.writhe_cons,
        Word.writhe_nil, add_zero]
      omega
  | artin before after index sign =>
      rewrite [Word.writhe_append, Word.writhe_append, Word.writhe_append,
        Word.writhe_append, Word.writhe_cons, Word.writhe_cons,
        Word.writhe_cons, Word.writhe_cons, Word.writhe_cons, Word.writhe_cons]
      exact Eq.refl _

end Rewrite

/-- Constructive equivalence generated by the finite Artin rewrites. -/
inductive Equivalent {strands : Nat} : Word strands → Word strands → Prop
  /-- Retain the identity equivalence of one original word. -/ | refl (word : Word strands) :
    Purelib.Topology.Knot.Braid.Artin.Equivalent word word
  /-- Include one original checked Artin rewrite in the finite equivalence. -/ | step {left right : Word strands}
    (rewrite : Artin.Rewrite left right) :
      Purelib.Topology.Knot.Braid.Artin.Equivalent left right
  /-- Reverse a retained finite Artin equivalence. -/ | symm {left right : Word strands} (relation :
    Purelib.Topology.Knot.Braid.Artin.Equivalent left right) :
      Purelib.Topology.Knot.Braid.Artin.Equivalent right left
  /-- Concatenate retained equivalences through the same original intermediate word. -/ | trans {first second third :
    Word strands}
      (firstSecond : Purelib.Topology.Knot.Braid.Artin.Equivalent first second)
      (secondThird : Purelib.Topology.Knot.Braid.Artin.Equivalent second third) :
        Purelib.Topology.Knot.Braid.Artin.Equivalent first third

namespace Equivalent

/-- Append a common original suffix to a retained finite Artin equivalence. -/
theorem append_right {strands : Nat} {left right : Word strands}
    (relation : Artin.Equivalent left right) (suffix : Word strands) :
    Artin.Equivalent (left ++ suffix) (right ++ suffix) := by
  induction relation with
  | refl word => exact .refl _
  | step rewrite => exact .step (rewrite.append_right suffix)
  | symm relation inductionHypothesis => exact .symm inductionHypothesis
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact .trans firstHypothesis secondHypothesis

/-- Prefix a retained finite Artin equivalence by the same original word. -/
theorem append_left {strands : Nat} (beforeWord : Word strands)
    {left right : Word strands} (relation : Artin.Equivalent left right) :
    Artin.Equivalent (beforeWord ++ left) (beforeWord ++ right) := by
  induction relation with
  | refl word => exact .refl _
  | step rewrite => exact .step (rewrite.append_left beforeWord)
  | symm relation inductionHypothesis => exact .symm inductionHypothesis
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact .trans firstHypothesis secondHypothesis

/-- Concatenate two retained finite Artin equivalences along their original word pairs. -/
theorem append {strands : Nat}
    {firstLeft firstRight secondLeft secondRight : Word strands}
    (first : Artin.Equivalent firstLeft firstRight)
    (second : Artin.Equivalent secondLeft secondRight) :
    Artin.Equivalent (firstLeft ++ secondLeft) (firstRight ++ secondRight) :=
  .trans (first.append_right secondLeft) (second.append_left firstRight)

open Purelib.Data.List in
/-- A word followed by its explicitly reversed signed word cancels by finite Artin rewrites.

The equivalence retains the original word and cancels its reversed signed
generators through the displayed finite sequence of local rewrites. -/
theorem append_inverse {strands : Nat} :
    ∀ word : Word strands,
      Artin.Equivalent (word ++ Word.inverse word) []
  | [] => .refl []
  | generator :: remaining => by
      have middle := (Purelib.Topology.Knot.Braid.Artin.Equivalent.append_inverse remaining).append_left [generator]
      have context := middle.append_right [generator.reverse]
      have reduceMiddle : Artin.Equivalent
          ([generator] ++ (remaining ++
            Word.inverse remaining) ++
            [generator.reverse])
          ([generator] ++ [] ++ [generator.reverse]) := by
        simpa only [Purelib.Data.List.Append.append_assoc] using context
      have cancel : Artin.Equivalent
          ([generator] ++ [] ++ [generator.reverse]) [] := by
        simpa only [List.nil_append, Purelib.Data.List.Append.append_nil, List.cons_append] using
          Artin.Equivalent.step (Artin.Rewrite.cancel [] [] generator)
      have normalized :
          (generator :: remaining) ++
              Word.inverse (generator :: remaining) =
            [generator] ++ (remaining ++
              Word.inverse remaining) ++
              [generator.reverse] := by
        rewrite [Word.inverse_cons]
        change generator :: (remaining ++ (Word.inverse remaining ++ [generator.reverse])) =
          generator :: ((remaining ++ Word.inverse remaining) ++ [generator.reverse])
        exact congrArg (List.cons generator)
          (Append.append_assoc remaining (Word.inverse remaining) [generator.reverse]).symm
      rw [normalized]
      exact .trans reduceMiddle cancel

/-- Finite Artin equivalence preserves the original executable strand permutation. -/
theorem permutationSame {strands : Nat} {left right : Word strands}
    (relation : Artin.Equivalent left right) : Artin.Word.PermutationSame left right := by
  induction relation with
  | refl word => exact Artin.Word.permutationSame_refl word
  | step rewrite => exact rewrite.permutationSame
  | symm relation inductionHypothesis =>
      exact Artin.Word.permutationSame_symm inductionHypothesis
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact Artin.Word.permutationSame_trans firstHypothesis secondHypothesis

/-- Finite Artin equivalence preserves the original integer writhe. -/
theorem writhe_eq {strands : Nat} {left right : Word strands}
    (relation : Artin.Equivalent left right) : left.writhe = right.writhe := by
  induction relation with
  | refl word => rfl
  | step rewrite => exact rewrite.writhe_eq
  | symm relation inductionHypothesis => exact inductionHypothesis.symm
  | trans firstSecond secondThird firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

end Equivalent

end

end Purelib.Topology.Knot.Braid.Artin
