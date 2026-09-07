import CCL.Boxes
import CCL.RationalEncoder

/-!
# Finite verification search for CCL-compatible rational samples

The geometric sampler in Lemma 10.4 produces a finite list of Gaussian
rational candidates.  This module supplies the final, fully executable
verification layer: a candidate is accepted exactly when it lies in the
requested rational box, is nonzero, and its actual terminating CCL encoding
extends the requested finite word.  Exhaustive list search is proved both
sound and complete relative to the supplied finite candidate list.
-/

namespace FTA
namespace CCLCompatibleSearch

open CCL

abbrev QI := CCL.GaussianRat

/-- The terminating CCL encoding when the rational input is nonzero. -/
def encoding? (q : QI) : Option Prefix.Word :=
  if nonzero : q = 0 then none
  else some (RationalEncoder.encode q nonzero)

/-- A finite word is compatible with a rational point when the point's actual
terminating encoder output extends it. -/
def Compatible (word : Prefix.Word) (q : QI) : Prop :=
  match encoding? q with
  | none => False
  | some full => word <+: full

instance (word : Prefix.Word) (q : QI) : Decidable (Compatible word q) := by
  unfold Compatible
  split <;> infer_instance

/-- Compatibility suitable for a nonterminal coupled state: the requested
word must be a proper prefix of the rational's complete encoding.  Equality
with the complete word is reserved for an exact polynomial-root terminal. -/
def StrictCompatible (word : Prefix.Word) (q : QI) : Prop :=
  match encoding? q with
  | none => False
  | some full => word <+: full ∧ word ≠ full

instance (word : Prefix.Word) (q : QI) :
    Decidable (StrictCompatible word q) := by
  unfold StrictCompatible
  split <;> infer_instance

/-- Proper encoder-prefix compatibility is exactly nonzero affine raw-parser
semantics. -/
theorem strictCompatible_iff_nonzero_represented
    (word : Prefix.Word) (q : QI) :
    StrictCompatible word q ↔
      q ≠ 0 ∧ RawParserSemantics.Represented word q := by
  by_cases nonzero : q = 0
  · subst q
    simp [StrictCompatible, encoding?]
  · simp only [StrictCompatible, encoding?, nonzero]
    exact ⟨fun proper =>
      ⟨nonzero, (RationalEncoder.represented_iff_strictPrefix_encode
        q nonzero word).2 proper⟩,
      fun represented =>
        (RationalEncoder.represented_iff_strictPrefix_encode
          q nonzero word).1 represented.2⟩

theorem compatible_iff_exists_encoder_prefix (word : Prefix.Word) (q : QI) :
    Compatible word q ↔
      ∃ nonzero : q ≠ 0, word <+: RationalEncoder.encode q nonzero := by
  by_cases nonzero : q = 0
  · subst q
    simp [Compatible, encoding?]
  · simp [Compatible, encoding?, nonzero]

theorem Compatible.nonzero {word : Prefix.Word} {q : QI}
    (compatible : Compatible word q) : q ≠ 0 := by
  exact (compatible_iff_exists_encoder_prefix word q).mp compatible |>.choose

/-- The executable compatibility test is exactly the affine raw-parser
semantics, except for the complete encoder word itself, which is the finite
projective terminal case. -/
theorem compatible_iff_represented_or_complete
    (word : Prefix.Word) (q : QI) :
    Compatible word q ↔
      ∃ nonzero : q ≠ 0,
        RawParserSemantics.Represented word q ∨
          word = RationalEncoder.encode q nonzero := by
  constructor
  · intro compatible
    rcases (compatible_iff_exists_encoder_prefix word q).mp compatible with
      ⟨nonzero, isPrefix⟩
    refine ⟨nonzero, ?_⟩
    by_cases complete : word = RationalEncoder.encode q nonzero
    · exact Or.inr complete
    · exact Or.inl
        ((RationalEncoder.represented_iff_strictPrefix_encode
          q nonzero word).2 ⟨isPrefix, complete⟩)
  · rintro ⟨nonzero, represented | complete⟩
    · apply (compatible_iff_exists_encoder_prefix word q).2
      exact ⟨nonzero,
        ((RationalEncoder.represented_iff_strictPrefix_encode
          q nonzero word).1 represented).1⟩
    · apply (compatible_iff_exists_encoder_prefix word q).2
      exact ⟨nonzero, by rw [complete]⟩

theorem represented_of_compatible_of_incomplete
    {word : Prefix.Word} {q : QI} (nonzero : q ≠ 0)
    (compatible : Compatible word q)
    (incomplete : word ≠ RationalEncoder.encode q nonzero) :
    RawParserSemantics.Represented word q := by
  apply (RationalEncoder.represented_iff_strictPrefix_encode
    q nonzero word).2
  exact ⟨(compatible_iff_exists_encoder_prefix word q).mp compatible |>.choose_spec,
    incomplete⟩

/-- Exact acceptance predicate for one finite-search candidate. -/
def Accepts (word : Prefix.Word) (box : RatBox) (q : QI) : Prop :=
  box.Contains q ∧ Compatible word q

instance (word : Prefix.Word) (box : RatBox) (q : QI) :
    Decidable (Accepts word box q) := by
  unfold Accepts RatBox.Contains
  infer_instance

/-- Exact acceptance predicate for a nonterminal represented sample. -/
def StrictAccepts (word : Prefix.Word) (box : RatBox) (q : QI) : Prop :=
  box.Contains q ∧ StrictCompatible word q

instance (word : Prefix.Word) (box : RatBox) (q : QI) :
    Decidable (StrictAccepts word box q) := by
  unfold StrictAccepts RatBox.Contains
  infer_instance

/-- Exhaustive executable verification of a finite rational candidate list. -/
def firstCompatible?
    (word : Prefix.Word) (box : RatBox) (candidates : List QI) : Option QI :=
  candidates.find? fun q => decide (Accepts word box q)

/-- Exhaustive verification search restricted to proper encoder prefixes. -/
def firstStrictCompatible?
    (word : Prefix.Word) (box : RatBox) (candidates : List QI) : Option QI :=
  candidates.find? fun q => decide (StrictAccepts word box q)

theorem firstCompatible?_some_mem
    {word : Prefix.Word} {box : RatBox} {candidates : List QI} {q : QI}
    (search : firstCompatible? word box candidates = some q) :
    q ∈ candidates := by
  exact List.mem_of_find?_eq_some search

theorem firstCompatible?_some_accepts
    {word : Prefix.Word} {box : RatBox} {candidates : List QI} {q : QI}
    (search : firstCompatible? word box candidates = some q) :
    Accepts word box q := by
  have check := List.find?_some search
  exact of_decide_eq_true check

theorem firstStrictCompatible?_some_mem
    {word : Prefix.Word} {box : RatBox} {candidates : List QI} {q : QI}
    (search : firstStrictCompatible? word box candidates = some q) :
    q ∈ candidates := by
  exact List.mem_of_find?_eq_some search

theorem firstStrictCompatible?_some_accepts
    {word : Prefix.Word} {box : RatBox} {candidates : List QI} {q : QI}
    (search : firstStrictCompatible? word box candidates = some q) :
    StrictAccepts word box q := by
  have check := List.find?_some search
  exact of_decide_eq_true check

/-- Every successful strict search result is a nonzero affine parser sample
inside the requested box. -/
theorem firstStrictCompatible?_some_certifies
    {word : Prefix.Word} {box : RatBox} {candidates : List QI} {q : QI}
    (search : firstStrictCompatible? word box candidates = some q) :
    box.Contains q ∧ q ≠ 0 ∧
      RawParserSemantics.Represented word q := by
  have accepted := firstStrictCompatible?_some_accepts search
  exact ⟨accepted.1,
    (strictCompatible_iff_nonzero_represented word q).mp accepted.2⟩

/-- Every successful search result lies in the box and its real terminating
encoder output extends the requested word. -/
theorem firstCompatible?_some_certifies
    {word : Prefix.Word} {box : RatBox} {candidates : List QI} {q : QI}
    (search : firstCompatible? word box candidates = some q) :
    box.Contains q ∧
      ∃ nonzero : q ≠ 0, word <+: RationalEncoder.encode q nonzero := by
  have accepted := firstCompatible?_some_accepts search
  exact ⟨accepted.1,
    (compatible_iff_exists_encoder_prefix word q).mp accepted.2⟩

/-- Relative completeness: if the supplied finite list contains any accepted
candidate, exhaustive verification returns some candidate. -/
theorem firstCompatible?_isSome_of_mem
    {word : Prefix.Word} {box : RatBox} {candidates : List QI} {q : QI}
    (member : q ∈ candidates) (accepted : Accepts word box q) :
    (firstCompatible? word box candidates).isSome := by
  rw [firstCompatible?, List.find?_isSome]
  exact ⟨q, member, by simp [accepted]⟩

theorem firstStrictCompatible?_isSome_of_mem
    {word : Prefix.Word} {box : RatBox} {candidates : List QI} {q : QI}
    (member : q ∈ candidates) (accepted : StrictAccepts word box q) :
    (firstStrictCompatible? word box candidates).isSome := by
  rw [firstStrictCompatible?, List.find?_isSome]
  exact ⟨q, member, by simp [accepted]⟩

/-- Failure of exhaustive verification excludes every member of the supplied
finite list. -/
theorem firstCompatible?_none_iff
    (word : Prefix.Word) (box : RatBox) (candidates : List QI) :
    firstCompatible? word box candidates = none ↔
      ∀ q ∈ candidates, ¬Accepts word box q := by
  simp [firstCompatible?]

theorem firstStrictCompatible?_none_iff
    (word : Prefix.Word) (box : RatBox) (candidates : List QI) :
    firstStrictCompatible? word box candidates = none ↔
      ∀ q ∈ candidates, ¬StrictAccepts word box q := by
  simp [firstStrictCompatible?]

end CCLCompatibleSearch
end FTA
