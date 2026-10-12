module

import Purelib.Data.List.Append

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.List.BinaryPrefix.Basic
public import Purelib.Data.List.Prefix
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.List

open Purelib.Data.List.BinaryPrefix

open Purelib.Data.List.BinaryPrefix.Basic

open Purelib.Data.Rat.Fraction

open Purelib.Data.List.BinaryPrefix.Basic renaming SourceEncodingPrefixMinimaxWordAlias -> GaugeWord,
  SourceEncodingPrefixTowerWordAlias -> PrefixWord

section
public section

/-!
# Finite prefix minimax over the pure CCL bitstream

This module formalizes the information-theoretic theorem of Section 7.  It is
only about finite `List Bool` tags.  Chordal geometry, boxed names, arithmetic
sidecars, completed streams, and collections of all compatible values do not
occur here.
-/

namespace Purelib.Data.List.BinaryPrefix

set_option genInjectivity false in
/-- A positive rational value on finite Boolean words that strictly decreases at each
child.

The value function is retained with pointwise positivity and strict contraction for
either appended bit. It describes a finite-prefix gauge without constructing any
completed word space. -/
structure Gauge where
  /-- The retained rational value assigned to each finite Boolean word. -/ value : GaugeWord → Rational
  /-- Every retained word value is strictly positive. -/ positive : ∀ word, 0 < value word
  /-- Appending either bit strictly decreases the retained word value. -/ child_lt : ∀ word bit, value (word ++ [bit]) <
    value word

constructive_injectivity Gauge

namespace Gauge

open Purelib.Data.List.BinaryPrefix.Gauge in
/-- Extending a finite word cannot increase its retained gauge value. -/
theorem append_le (gauge : Gauge) (word suffix : GaugeWord) :
    gauge.value (word ++ suffix) ≤ gauge.value word := by
  induction suffix generalizing word with
  | nil =>
      rewrite [Append.append_nil]
      exact Order.Basic.le_refl _
  | cons bit remaining inductionHypothesis =>
      calc
        gauge.value (word ++ bit :: remaining) =
            gauge.value ((word ++ [bit]) ++ remaining) := by
          congr 1
          simp only [-eq_self, -iff_self, Append.append_assoc, List.singleton_append]; try rfl
        _ ≤ gauge.value (word ++ [bit]) :=
          inductionHypothesis (word ++ [bit])
        _ ≤ gauge.value word := (gauge.child_lt word bit).le

open Purelib.Data.List.BinaryPrefix.Gauge in
/-- Appending a nonempty Boolean suffix strictly decreases the gauge value. -/
theorem append_lt_of_nonempty (gauge : Gauge) (word suffix :
  GaugeWord)
    (nonempty : suffix ≠ []) :
    gauge.value (word ++ suffix) < gauge.value word := by
  cases suffix with
  | nil => exact (nonempty rfl).elim
  | cons bit remaining =>
      calc
        gauge.value (word ++ bit :: remaining) =
            gauge.value ((word ++ [bit]) ++ remaining) := by
          congr 1
          simp only [-eq_self, -iff_self, Append.append_assoc, List.singleton_append]; try rfl
        _ ≤ gauge.value (word ++ [bit]) :=
          gauge.append_le (word ++ [bit]) remaining
        _ < gauge.value word := gauge.child_lt word bit

open Purelib.Data.List.BinaryPrefix.Gauge in
/-- A strict extension of a finite word has a strictly smaller gauge value. -/
theorem lt_of_strict_prefix (gauge : Gauge) {shorter longer :
  GaugeWord}
    (isPrefix : shorter.IsPrefix longer) (different : shorter ≠ longer) :
    gauge.value longer < gauge.value shorter := by
  rcases isPrefix with ⟨suffix, identity⟩
  have suffixNonempty : suffix ≠ [] := by
    intro suffixEmpty
    apply different
    rw [← identity, suffixEmpty, Append.append_nil]
  rw [← identity]
  exact gauge.append_lt_of_nonempty shorter suffix suffixNonempty

/- Opaque injectivity of the original retained fields. -/

end Gauge

open Purelib.Data.List.BinaryPrefix.Gauge
namespace Gauge

/-- Compute the gauge value of the common prefix of two unequal finite words.

Equal words have distance zero. Unequal words use the retained gauge at their longest
common Boolean prefix. -/
@[expose] def distance (gauge : Gauge) (left right : GaugeWord) : Rational
  :=
  if left = right then 0 else gauge.value (Basic.lcp left right)

/-- The finite common-prefix gauge distance is nonnegative. -/
theorem distance_nonneg (gauge : Gauge) (left right : GaugeWord) :
    0 ≤ Gauge.distance gauge left right := by
  unfold Gauge.distance
  split
  · exact le_rfl
  · exact (gauge.positive _).le

/-- A displayed common stem bounds the gauge distance of two finite words.

Both words must extend the same stem. Their longest common prefix extends it too, and
gauge values decrease under extension. -/
theorem distance_le_of_common_prefix (gauge : Gauge)
    {stem left right : GaugeWord}
    (leftPrefix : stem.IsPrefix left)
    (rightPrefix : stem.IsPrefix right) :
    Gauge.distance gauge left right ≤ gauge.value stem := by
  rcases leftPrefix with ⟨leftSuffix, rfl⟩
  rcases rightPrefix with ⟨rightSuffix, rfl⟩
  unfold Gauge.distance
  split
  · exact (gauge.positive stem).le
  · rw [Basic.lcp_append_same]
    exact gauge.append_le stem (Basic.lcp leftSuffix rightSuffix)

/-- The distance from a word to any strict one-bit-and-tail extension equals its gauge
value. -/
theorem distance_prefix_child (gauge : Gauge)
    (stem tail : GaugeWord) (bit : Bool) :
    Gauge.distance gauge stem (stem ++ bit :: tail) = gauge.value stem := by
  have different : stem ≠ stem ++ bit :: tail := by
    intro equal
    have lengths := congrArg List.length equal
    have strict : stem.length < (stem ++ bit :: tail).length := by
      rw [Append.length_append, List.length_cons]
      exact Nat.lt_add_of_pos_right (Nat.zero_lt_succ tail.length)
    exact (Nat.ne_of_lt strict) lengths
  rw [Gauge.distance, if_neg different]
  have lcpIdentity : Basic.lcp stem (stem ++ bit :: tail) = stem := by
    calc
      Basic.lcp stem (stem ++ bit :: tail) =
          Basic.lcp (stem ++ []) (stem ++ bit :: tail) := by
        rw [Append.append_nil]
      _ = stem ++ Basic.lcp [] (bit :: tail) := Basic.lcp_append_same _ _ _
      _ = stem := by simp only [-eq_self, -iff_self, Basic.lcp_nil_left, Append.append_nil]; try rfl
  rw [lcpIdentity]

/-- Words continuing in opposite bit branches have distance equal to their common stem's
gauge. -/
theorem distance_opposite_child (gauge : Gauge)
    (stem leftTail rightTail : GaugeWord) (bit : Bool) :
    Gauge.distance gauge (stem ++ bit :: leftTail)
        (stem ++ (!bit) :: rightTail) = gauge.value stem := by
  cases bit with
  | false =>
      have different : stem ++ false :: leftTail ≠
          stem ++ true :: rightTail := by
        intro equal
        have cancelled := List.append_cancel_left equal
        have bits : false = true := congrArg (fun word : List Bool => word.headD false) cancelled
        exact Bool.noConfusion bits
      simp only [-eq_self, -iff_self, Bool.not_false]; try rfl
      rw [Gauge.distance, if_neg different, Basic.lcp_append_same]
      simp only [-eq_self, -iff_self, Basic.lcp, if_neg (by decide : false ≠ true), Append.append_nil]; try rfl
  | true =>
      have different : stem ++ true :: leftTail ≠
          stem ++ false :: rightTail := by
        intro equal
        have cancelled := List.append_cancel_left equal
        have bits : true = false := congrArg (fun word : List Bool => word.headD false) cancelled
        exact Bool.noConfusion bits
      simp only [-eq_self, -iff_self, Bool.not_true]; try rfl
      rw [Gauge.distance, if_neg different, Basic.lcp_append_same]
      simp only [-eq_self, -iff_self, Basic.lcp, if_neg (by decide : true ≠ false), Append.append_nil]; try rfl

end Gauge
end Purelib.Data.List.BinaryPrefix

end

section
section
public section

/-!
# Finite approximation towers for exact CCL names

This module packages the elementary prefix clauses of the manuscript's
finite-name tower without introducing a completed stream or a collection of
all points in a cylinder.
-/

namespace Purelib.Data.List.BinaryPrefix.Gauge
open Purelib.Data.List.BinaryPrefix.Gauge
/-- The original finite-word Gauge carrier, retained as an exact reducible alias. -/
abbrev SourceEncodingPrefixTowerGaugeAlias := Gauge

/-- Before the end of a finite word, its truncated-prefix distance is the gauge of that
prefix.

The count must be strictly below the word length. The retained indexed next bit
exhibits a strict extension of the prefix to the complete word. -/
theorem distance_prefixAt (gauge : SourceEncodingPrefixTowerGaugeAlias)
  (word : PrefixWord) (count : Nat)
    (beforeEnd : count < word.length) :
    Gauge.distance gauge (Prefix.prefixAt word count) word =
      gauge.value (Prefix.prefixAt word count) := by
  have split :
      word = Prefix.prefixAt word count ++
        word[count] :: word.drop (count + 1) := by
    calc
      word = word.take count ++ word.drop count :=
        (List.take_append_drop count word).symm
      _ = word.take count ++
          word[count] :: word.drop (count + 1) :=
        congrArg (fun suffix => word.take count ++ suffix)
          (List.drop_eq_getElem_cons beforeEnd)
  calc
    Gauge.distance gauge (Prefix.prefixAt word count) word =
        Gauge.distance gauge (Prefix.prefixAt word count)
          (Prefix.prefixAt word count ++
            word[count] :: word.drop (count + 1)) :=
      congrArg
        (Gauge.distance gauge (Prefix.prefixAt word count))
        split
    _ = gauge.value (Prefix.prefixAt word count) :=
      Gauge.distance_prefix_child gauge
        (Prefix.prefixAt word count) (word.drop (count + 1)) word[count]

end Purelib.Data.List.BinaryPrefix.Gauge

end

end
