module

public import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.Prefix.Take

open Purelib.Data.List

open Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.List.BinaryPrefix.Basic renaming SourceEncodingPrefixTowerWordAlias -> Word

section
@[expose] public section

/-!
# Finite approximation towers for exact CCL names

This module packages the elementary prefix clauses of the manuscript's
finite-name tower without introducing a completed stream or a collection of
all points in a cylinder.
-/

namespace Purelib.Data.List.Prefix

/-- Decide prefix containment by comparing the original finite list spines.

Each successful step retains the same suffix witness. A mismatching head or
an exhausted second list returns a proof of the specific failed prefix claim.
-/
def decidable {Alpha : Type u} [DecidableEq Alpha] :
    (earlier later : List Alpha) → Decidable (earlier.IsPrefix later)
  | [], later => .isTrue ⟨later, rfl⟩
  | _ :: _, [] => .isFalse (by intro ⟨suffix, equal⟩; nomatch equal)
  | head :: tail, first :: rest =>
      if equal : head = first then
        match decidable tail rest with
        | .isTrue contained => .isTrue (by
            rcases contained with ⟨suffix, tailEqual⟩
            cases equal
            exact ⟨suffix, congrArg (List.cons head) tailEqual⟩)
        | .isFalse failed => .isFalse (by
            intro ⟨suffix, same⟩
            exact failed ⟨suffix, (List.cons.inj same).2⟩)
      else .isFalse (by
        intro ⟨suffix, same⟩
        exact equal (List.cons.inj same).1)

/-- Take at most the supplied number of leading bits from a displayed finite word. -/
def prefixAt (word : Word) (count : Nat) : Word := word.take count

/-- Every bounded take of a finite word is a prefix of that word. -/
theorem prefixAt_isPrefix (word : Word) (count : Nat) :
    (prefixAt word count).IsPrefix word :=
  List.take_prefix count word

/-- Increasing a finite-prefix request by one extends the preceding prefix. -/
theorem prefixAt_successive (word : Word) (count : Nat) :
    (prefixAt word count).IsPrefix (prefixAt word (count + 1)) := by
  refine ⟨word[count]?.toList, ?_⟩
  exact Prefix.Take.take_add_one word count |>.symm
end Purelib.Data.List.Prefix

end
