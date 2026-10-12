module

import Purelib.Data.List.Membership
public import Purelib.Data.Vector.Boolean.Basic
meta import Purelib.Elab.ConstructiveInjectivity

public section

/-!
# Finite Boolean spans with retained word witnesses

This module incrementally spans one supplied finite list of fixed-length
Boolean vectors under XOR.  It never forms a function space or an ambient
infinite vector space.  Every distinct image vector retains a Boolean word
witness; the result also caches closure, completeness, duplicate-freeness,
rank, and the exact power-of-two length formula.
-/

namespace Purelib.LinearAlgebra.Span.Boolean.Basic

open Purelib
open Purelib.LinearAlgebra.Span

set_option backward.match.sparseCases false in
/-- Evaluate one finite Boolean word against one finite generator list.

Each true bit XORs its original generator with the retained recursive tail;
a false bit keeps that tail. Exhausting either list yields the zero vector. -/
@[expose] def evaluate {width : Nat} : List Bool → List (Data.Vector.Boolean width) →
  Data.Vector.Boolean width
  | [], _ => Data.Vector.Boolean.Basic.zero width
  | _ :: _, [] => Data.Vector.Boolean.Basic.zero width
  | selected :: choices, generator :: generators =>
      match selected with
      | true => Data.Vector.Boolean.Basic.xor generator (Purelib.LinearAlgebra.Span.Boolean.Basic.evaluate choices
        generators)
      | false => Purelib.LinearAlgebra.Span.Boolean.Basic.evaluate choices generators

/-- Selecting no generators evaluates to the zero Boolean vector.

Every original generator is ignored by its retained false bit; the recursion ends at the same fixed-width zero vector.
-/
theorem evaluate_allFalse {width : Nat} :
    ∀ generators : List (Data.Vector.Boolean width),
      Boolean.Basic.evaluate (List.replicate generators.length false) generators =
        Data.Vector.Boolean.Basic.zero width
  | [] => rfl
  | _generator :: generators => by
      change Boolean.Basic.evaluate (List.replicate generators.length false) generators =
        Data.Vector.Boolean.Basic.zero width
      exact Purelib.LinearAlgebra.Span.Boolean.Basic.evaluate_allFalse generators

/-- A retained generator has a Boolean selection word of the original generator-list length.

The membership witness selects the original generator occurrence. Its word retains one bit for every entry of that same
generator list. -/
theorem generator_evaluation {width : Nat}
    {generator : Data.Vector.Boolean width} :
    ∀ {generators : List (Data.Vector.Boolean width)}, generator ∈ generators →
      ∃ choices : List Bool,
        choices.length = generators.length ∧
          Boolean.Basic.evaluate choices generators = generator
  | [], impossible => by nomatch impossible
  | head :: tail, member => by
      rcases Data.List.Membership.mem_cons.mp member with equal | tailMember
      · subst head
        let choices := true :: List.replicate tail.length false
        refine ⟨choices, ?_, ?_⟩
        · exact congrArg Nat.succ (Data.List.Replicate.length_replicate tail.length false)
        · change Data.Vector.Boolean.Basic.xor generator
            (Boolean.Basic.evaluate (List.replicate tail.length false) tail) = generator
          rw [Boolean.Basic.evaluate_allFalse, Data.Vector.Boolean.Basic.xor_zero]
      · rcases generator_evaluation tailMember with
          ⟨tailChoices, tailLength, tailEvaluation⟩
        exact ⟨false :: tailChoices, congrArg Nat.succ tailLength,
          tailEvaluation⟩

set_option genInjectivity false in
/-- One distinct image vector with a retained Boolean generator word.

The retained selection word has exactly the original generator-list length and evaluates to the exact stored vector at
the supplied width. -/
structure Entry {width : Nat} (generators : List (Data.Vector.Boolean width)) where
  /-- The retained Boolean image vector. -/ vector : Data.Vector.Boolean width
  /-- The Boolean selection word over the original generators. -/ choices : List Bool
  /-- The selection word has exactly the original generator-list length. -/ choices_length : choices.length =
    generators.length
  /-- The retained selection word evaluates to this exact image vector. -/ evaluates : Boolean.Basic.evaluate choices
    generators = vector

constructive_injectivity Entry

/-- Extend a retained generator word by ignoring one prepended generator.

The output vector is unchanged and the word length remains tied to the enlarged generator list. -/
@[expose] def prependFalse {width : Nat} (generator : Data.Vector.Boolean width)
    {generators : List (Data.Vector.Boolean width)} (entry : Boolean.Basic.Entry generators) :
    Boolean.Basic.Entry (generator :: generators) where
  vector := entry.vector
  choices := false :: entry.choices
  choices_length := congrArg Nat.succ entry.choices_length
  evaluates := entry.evaluates

/-- Extend a retained generator word by selecting one prepended generator.

The output is its XOR with the original retained vector, with a certificate for the enlarged generator list. -/
@[expose] def prependTrue {width : Nat} (generator : Data.Vector.Boolean width)
    {generators : List (Data.Vector.Boolean width)} (entry : Boolean.Basic.Entry generators) :
    Boolean.Basic.Entry (generator :: generators) where
  vector := Data.Vector.Boolean.Basic.xor generator entry.vector
  choices := true :: entry.choices
  choices_length := congrArg Nat.succ entry.choices_length
  evaluates := by
    change Data.Vector.Boolean.Basic.xor generator (Boolean.Basic.evaluate entry.choices generators) =
      Data.Vector.Boolean.Basic.xor generator entry.vector
    rw [entry.evaluates]

/-- Prepending a false choice to every retained entry preserves the displayed vector list.

Each original entry keeps its vector while its selection word is extended; structural list traversal preserves the exact
entry order. -/
theorem falseVectors {width : Nat} {generator : Data.Vector.Boolean width}
    {generators : List (Data.Vector.Boolean width)} :
    ∀ entries : List (Boolean.Basic.Entry generators),
      (entries.map (Boolean.Basic.prependFalse generator)).map Boolean.Basic.Entry.vector =
        entries.map Boolean.Basic.Entry.vector
  | [] => rfl
  | head :: tail =>
      congrArg (List.cons head.vector) (Purelib.LinearAlgebra.Span.Boolean.Basic.falseVectors tail)

/-- Prepending a true choice to every retained entry XORs each vector with the new generator.

Each original entry retains its order and is XORed with the same prepended generator, matching its extended true
selection word. -/
theorem trueVectors {width : Nat} {generator : Data.Vector.Boolean width}
    {generators : List (Data.Vector.Boolean width)} :
    ∀ entries : List (Boolean.Basic.Entry generators),
      (entries.map (Boolean.Basic.prependTrue generator)).map Boolean.Basic.Entry.vector =
        (entries.map Boolean.Basic.Entry.vector).map (Data.Vector.Boolean.Basic.xor generator)
  | [] => rfl
  | head :: tail =>
      congrArg (List.cons (Data.Vector.Boolean.Basic.xor generator head.vector))
        (Purelib.LinearAlgebra.Span.Boolean.Basic.trueVectors tail)

set_option genInjectivity false in
/-- The distinct finite XOR span with retained generator words and an exact rank count.

The original generator list indexes every entry, and the result certifies completeness, XOR closure and its power-of-two
length. -/
structure Result {width : Nat} (generators : List (Data.Vector.Boolean width)) where
  /-- The retained rank of the finite Boolean span. -/ rank : Nat
  /-- The cached distinct image entries with their original generator words. -/ entries : List (Boolean.Basic.Entry
    generators)
  /-- The displayed image vectors contain no repetitions. -/ vectors_nodup : (entries.map
    Boolean.Basic.Entry.vector).Nodup
  /-- The cached entry count is exactly two raised to the retained rank. -/ length_eq : entries.length = 2 ^ rank
  /-- Every correctly sized generator word has an equal image among the retained entries. -/ complete : ∀ choices : List
    Bool,
    choices.length = generators.length →
      ∃ entry ∈ entries, Boolean.Basic.evaluate choices generators = entry.vector
  /-- The XOR of two retained entries occurs among those same entries. -/ closed : ∀ left ∈ entries, ∀ right ∈ entries,
    ∃ output ∈ entries, Data.Vector.Boolean.Basic.xor left.vector right.vector = output.vector

constructive_injectivity Result

/-- The retained finite span contains an entry for the zero vector.

The all-false word has the original generator-list length and completeness supplies a retained entry with that same zero
evaluation. -/
theorem Result.zero_mem {width : Nat}
    {generators : List (Data.Vector.Boolean width)} (result : Boolean.Basic.Result generators) :
    ∃ entry ∈ result.entries, entry.vector = Data.Vector.Boolean.Basic.zero width := by
  rcases result.complete (List.replicate generators.length false)
      (Data.List.Replicate.length_replicate generators.length false) with ⟨entry, member, evaluation⟩
  exact ⟨entry, member, evaluation.symm.trans
    (Boolean.Basic.evaluate_allFalse generators)⟩

/-- Every retained generator occurs as an entry of the computed finite span. -/
theorem Result.generator_mem {width : Nat}
    {generators : List (Data.Vector.Boolean width)} (result : Boolean.Basic.Result generators)
    {generator : Data.Vector.Boolean width} (member : generator ∈ generators) :
    ∃ entry ∈ result.entries, entry.vector = generator := by
  rcases Boolean.Basic.generator_evaluation member with
    ⟨choices, choicesLength, evaluates⟩
  rcases result.complete choices choicesLength with
    ⟨entry, entryMember, classified⟩
  exact ⟨entry, entryMember, classified.symm.trans evaluates⟩

/-- Classify the XOR fold of any supplied finite word whose displayed vectors
all belong to the generator list. -/
theorem Result.classifyXorWord {width : Nat}
    {generators : List (Data.Vector.Boolean width)} (result : Boolean.Basic.Result generators) :
    ∀ word : List (Data.Vector.Boolean width),
      (∀ vector ∈ word, vector ∈ generators) →
        ∃ entry ∈ result.entries,
          word.foldr Data.Vector.Boolean.Basic.xor (Data.Vector.Boolean.Basic.zero width) = entry.vector
  | [], _allMembers => by
      rcases result.zero_mem with ⟨entry, member, vectorEq⟩
      exact ⟨entry, member, vectorEq.symm⟩
  | head :: tail, allMembers => by
      have headMember : head ∈ generators :=
        allMembers head (List.Mem.head tail)
      have tailMembers : ∀ vector ∈ tail, vector ∈ generators := by
        intro vector member
        exact allMembers vector (List.Mem.tail head member)
      rcases result.generator_mem headMember with
        ⟨headEntry, headEntryMember, headVector⟩
      rcases result.classifyXorWord tail tailMembers with
        ⟨tailEntry, tailEntryMember, tailVector⟩
      rcases result.closed headEntry headEntryMember tailEntry tailEntryMember
        with ⟨output, outputMember, outputVector⟩
      refine ⟨output, outputMember, ?_⟩
      change Data.Vector.Boolean.Basic.xor head (tail.foldr Data.Vector.Boolean.Basic.xor
        (Data.Vector.Boolean.Basic.zero width)) = output.vector
      rw [← headVector, tailVector]
      exact outputVector
end Purelib.LinearAlgebra.Span.Boolean.Basic
