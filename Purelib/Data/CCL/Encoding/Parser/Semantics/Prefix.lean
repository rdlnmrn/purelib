module
import Purelib.Data.List.Filter
import Purelib.Data.List.Reverse
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.CCL.Encoding.Block.Matrix
import Purelib.Data.CCL.Encoding.Parser.Constraint
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Semantics.State
public import Purelib.Data.CCL.Encoding.Parser.Semantics.Transition
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Data.List.BinaryPrefix.Decision
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix
import Purelib.Data.Gaussian.Norm.Basic

/-!
# Affine semantics of constructive raw-parser states

Parser constraints are evaluated on the current affine tail.  These finite
algebraic lemmas prove that decoder homographies compose in parser order and
that completing a raw block preserves the represented original input.
-/

public section

namespace Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix

section
open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
section
open Purelib.Data.List
/-- Require an exact Gaussian tail representing the input after parsing the retained finite word. -/
@[expose] def Represented (word :
  BinaryPrefix.Basic.SourceEncodingRawParserSemanticsWordAlias) (input : Basic.Canonical) : Prop :=
  ∃ tail, State.Represents (State.parse word) input tail

/-- Removing the last bit preserves representation of the original Gaussian input. -/
theorem represented_drop_last
    {word : BinaryPrefix.Basic.SourceEncodingRawParserSemanticsWordAlias} {bit : Bool} {input : Basic.Canonical}
    (represented : Represented (word ++ [bit]) input) :
    Represented word input := by
  rcases represented with ⟨tail, represented⟩
  refine ⟨Transition.previousTail (State.parse word) bit tail, ?_⟩
  apply Transition.step_represents_previous (State.parse word) bit input tail
  simpa only [State.parse_append_singleton, -eq_self, -iff_self] using represented

end

/-- The empty word represents every Gaussian input using that same value as its tail. -/
theorem represented_nil (input : Basic.Canonical) :
  Represented [] input :=
  ⟨input, State.initialState_represents input⟩

/-- Every finite initial-low unary prefix represents the native affine zero.

Its initial false bit is followed by the supplied finite number of true bits.
The decoder remains the identity and its tail remains zero; this gives finite
progress without a terminal nonzero-fraction encoding for zero.
-/
theorem represented_zero_low (count : Nat) :
    Represented (false :: List.replicate count true) (0 : Basic.Canonical) := by
  have parsed : State.parse (false :: List.replicate count true) =
      ⟨.lowUnary count, LinearAlgebra.Coordinates2.Matrix.identityMatrix, []⟩ := by
    change (List.replicate count true).foldl State.step
      ⟨.lowUnary 0, LinearAlgebra.Coordinates2.Matrix.identityMatrix, []⟩ = _
    exact (State.foldl_true_unary .initialLow count 0 _ []).trans
      (congrArg (fun value => State.mk (.lowUnary value) _ []) (Nat.zero_add count))
  refine ⟨0, ?_⟩
  rewrite [parsed]
  have initial := State.initialState_represents (0 : Basic.Canonical)
  refine ⟨initial.1, initial.2.1, ?_, ?_⟩
  · intro constraint member
    nomatch member
  · cases count with
    | zero => decide
    | succ count =>
        change (2 : Rat.Fraction.Rational) ^ count * Basic.Canonical.normSq 0 < 1
        change (2 : Rat.Fraction.Rational) ^ count * 0 < 1
        rewrite [Rat.Fraction.Field.mul_zero_direct]
        decide

open Purelib.Data.List in
/-- Every retained prefix of a represented word represents the same original Gaussian input. -/
theorem represented_of_prefix
    {shorter word : BinaryPrefix.Basic.SourceEncodingRawParserSemanticsWordAlias} {input : Basic.Canonical}
    (isPrefix : shorter.IsPrefix word) (represented : Represented word input) :
    Represented shorter input := by
  rcases isPrefix with ⟨suffix, rfl⟩
  have removeReversed : ∀ reversed : BinaryPrefix.Basic.SourceEncodingRawParserSemanticsWordAlias,
      Represented (shorter ++ reversed.reverse) input →
        Represented shorter input := by
    intro reversed
    induction reversed with
    | nil =>
        intro retained
        rewrite [List.reverse_nil, Append.append_nil]
          at retained
        exact retained
    | cons bit remaining inductionHypothesis =>
        intro representedAll
        apply inductionHypothesis
        apply represented_drop_last
          (word := shorter ++ remaining.reverse) (bit := bit)
        simpa only [Reverse.reverse_cons, Append.append_assoc, -eq_self, -iff_self]
          using representedAll
  apply removeReversed suffix.reverse
  simpa only [Reverse.reverse_reverse, -eq_self, -iff_self] using represented

/-- Require an exact Gaussian tail representing the original input after the supplied next parser bit. -/
@[expose] def CanStep (state : State) (input :
  Basic.Canonical) (bit : Bool) : Prop :=
  ∃ tail, State.Represents (State.step state bit) input tail

end

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
open Purelib.Data.Rat in
open Purelib.Geometry.Projective in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- A parser state with nonsingular retained matrix cannot represent the same input after both Boolean next bits. -/
theorem not_canStep_false_and_true
    (state : State) (input : Basic.Canonical)
    (determinant : Matrix2.Matrix2.determinant state.matrix ≠ 0) :
    ¬(CanStep state input false ∧ CanStep state input true) := by
  rintro ⟨⟨falseTail, falseRepresents⟩,
    ⟨trueTail, trueRepresents⟩⟩
  have falsePrevious := Transition.step_represents_previous state false input falseTail
    falseRepresents
  have truePrevious := Transition.step_represents_previous state true input trueTail
    trueRepresents
  have previousEqual := State.Represents.tail_unique determinant falsePrevious
    truePrevious
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simp only [Transition.previousTail, -eq_self, -iff_self]
        at previousEqual
      subst trueTail
      have low := falseRepresents.2.2.2
      have high := trueRepresents.2.2.2
      change Basic.Canonical.normSq falseTail < 2 at low
      change (2 : Fraction.Rational) ^ 1 ≤ Basic.Canonical.normSq falseTail at high
      rw [pow_one] at high
      exact (not_lt_of_ge high) low
  | highUnary count =>
      simp only [Transition.previousTail, -eq_self, -iff_self]
        at previousEqual
      subst trueTail
      have upper := falseRepresents.2.2.2.1.2
      have lower := trueRepresents.2.2.2
      exact (not_lt_of_ge lower) upper
  | lowUnary count =>
      simp only [Transition.previousTail, -eq_self, -iff_self]
        at previousEqual
      subst trueTail
      have lower := falseRepresents.2.2.2.1.1
      have upper := trueRepresents.2.2.2
      exact (not_lt_of_ge lower) upper
  | loopUnary count =>
      simp only [Transition.previousTail, -eq_self, -iff_self]
        at previousEqual
      subst trueTail
      have upper := falseRepresents.2.2.2.1.2
      have lower := trueRepresents.2.2.2
      exact (not_lt_of_ge upper) lower
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp only [Transition.previousTail, -eq_self, -iff_self]
            at previousEqual
          subst trueTail
          rcases falseRepresents.2.2.2 with
            ⟨_, falseSector, falseMember, falseHolds⟩
          rcases trueRepresents.2.2.2 with
            ⟨_, trueSector, trueMember, trueHolds⟩
          have sectorEqual :=
            Sector.holds_unique falseHolds trueHolds
          subst trueSector
          have falsePrefix : BinaryPrefix.Decision.isWordPrefix [false] falseSector.code = true :=
            (Filter.mem_filter.mp falseMember).2
          have truePrefix : BinaryPrefix.Decision.isWordPrefix [true] falseSector.code = true :=
            (Filter.mem_filter.mp trueMember).2
          cases falseSector <;> first | exact Bool.noConfusion falsePrefix | exact Bool.noConfusion truePrefix
      | one first =>
          simp only [Transition.previousTail, -eq_self, -iff_self]
            at previousEqual
          subst trueTail
          rcases falseRepresents.2.2.2 with
            ⟨_, falseSector, falseMember, falseHolds⟩
          rcases trueRepresents.2.2.2 with
            ⟨_, trueSector, trueMember, trueHolds⟩
          have sectorEqual :=
            Sector.holds_unique falseHolds trueHolds
          subst trueSector
          have falsePrefix :
              BinaryPrefix.Decision.isWordPrefix [first, false] falseSector.code = true :=
            (Filter.mem_filter.mp falseMember).2
          have truePrefix :
              BinaryPrefix.Decision.isWordPrefix [first, true] falseSector.code = true :=
            (Filter.mem_filter.mp trueMember).2
          cases first <;> cases falseSector <;>
            first
            | exact Bool.noConfusion falsePrefix
            | exact Bool.noConfusion truePrefix
      | two first second =>
          let falseSector := Sector.Code.sectorOfBits first second false
          let trueSector := Sector.Code.sectorOfBits first second true
          let falseBlock := Block.Matrix.blockMatrix kind exponent falseSector
          let trueBlock := Block.Matrix.blockMatrix kind exponent trueSector
          have falseNewest :
              (Constraint.mk falseBlock kind exponent falseSector).Holds
                falseTail := by
            apply falseRepresents.2.2.1
            change Constraint.mk falseBlock kind exponent falseSector ∈
              Constraint.mk falseBlock kind exponent falseSector ::
                history.map (fun item => item.precompose falseBlock)
            exact List.mem_cons_self
          have trueNewest :
              (Constraint.mk trueBlock kind exponent trueSector).Holds
                trueTail := by
            apply trueRepresents.2.2.1
            change Constraint.mk trueBlock kind exponent trueSector ∈
              Constraint.mk trueBlock kind exponent trueSector ::
                history.map (fun item => item.precompose trueBlock)
            exact List.mem_cons_self
          have falseHolds : falseSector.Holds
              (Basic.normalizedValue kind exponent
                (Homography.Basic.homographic falseBlock falseTail)) := falseNewest.2.2
          have trueHolds : trueSector.Holds
              (Basic.normalizedValue kind exponent
                (Homography.Basic.homographic trueBlock trueTail)) := trueNewest.2.2
          change Homography.Basic.homographic falseBlock falseTail =
            Homography.Basic.homographic trueBlock trueTail at previousEqual
          have normalizedEqual := congrArg
            (Basic.normalizedValue kind exponent) previousEqual
          rw [normalizedEqual] at falseHolds
          have sectorEqual :=
            Sector.holds_unique falseHolds trueHolds
          cases first <;> cases second <;>
            exact ComplexContinuedFraction.Encoding.Sector.noConfusion sectorEqual

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Two possible next bits of the same nonsingular retained parser state and input are equal. -/
theorem canStep_unique
    {state : State} {input : Basic.Canonical} {left right : Bool}
    (determinant : Matrix2.Matrix2.determinant state.matrix ≠ 0)
    (leftPossible : CanStep state input left)
    (rightPossible : CanStep state input right) : left = right := by
  cases left <;> cases right
  · rfl
  · exact (not_canStep_false_and_true state input determinant
      ⟨leftPossible, rightPossible⟩).elim
  · exact (not_canStep_false_and_true state input determinant
      ⟨rightPossible, leftPossible⟩).elim
  · rfl

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
/-- Two represented one-bit extensions of the same finite word and Gaussian input have the same last bit. -/
theorem represented_child_unique
    {word : BinaryPrefix.Basic.SourceEncodingRawParserSemanticsWordAlias} {input : Basic.Canonical} {left right : Bool}
    (leftRepresented : Represented (word ++ [left]) input)
    (rightRepresented : Represented (word ++ [right]) input) :
    left = right := by
  apply canStep_unique (State.parse_det_ne word)
  · rcases leftRepresented with ⟨tail, represented⟩
    exact ⟨tail, by simpa only [State.parse_append_singleton, -eq_self, -iff_self] using represented⟩
  · rcases rightRepresented with ⟨tail, represented⟩
    exact ⟨tail, by simpa only [State.parse_append_singleton, -eq_self, -iff_self] using represented⟩

section PrefixChain

open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.List

/-- Compare represented suffixes after the same original finite stem by their lengths. -/
private theorem represented_suffix_prefix
    (left : List Bool) : ∀ (stem right : List Bool) (input : Basic.Canonical),
      left.length ≤ right.length → Represented (stem ++ left) input →
      Represented (stem ++ right) input → left.IsPrefix right := by
  induction left with
  | nil =>
      intro stem right input _ _ _
      exact ⟨right, rfl⟩
  | cons bit remaining induction =>
      intro stem right input length leftRepresented rightRepresented
      cases right with
      | nil => exact (Nat.not_succ_le_zero remaining.length length).elim
      | cons other tail =>
          have leftChild : Represented (stem ++ [bit]) input :=
            represented_of_prefix
              ⟨remaining, Append.append_assoc stem [bit] remaining⟩ leftRepresented
          have rightChild : Represented (stem ++ [other]) input :=
            represented_of_prefix
              ⟨tail, Append.append_assoc stem [other] tail⟩ rightRepresented
          have same := represented_child_unique leftChild rightChild
          cases same
          have retainedLeft : Represented ((stem ++ [bit]) ++ remaining) input :=
            (Append.append_assoc stem [bit] remaining).symm ▸ leftRepresented
          have retainedRight : Represented ((stem ++ [bit]) ++ tail) input :=
            (Append.append_assoc stem [bit] tail).symm ▸ rightRepresented
          rcases induction (stem ++ [bit]) tail input
            (Nat.le_of_succ_le_succ length) retainedLeft retainedRight with ⟨suffix, equal⟩
          exact ⟨suffix, congrArg (List.cons bit) equal⟩

/-- Two affine words representing the same rational input follow one ordered prefix chain.

The shorter represented word is a literal prefix of the longer one. The
proof compares the actual next bits after each shared stem; it retains the
original half-open parser decisions and does not identify words merely from
their projective decoder values.
-/
theorem represented_prefix_of_length_le
    {left right : List Bool} {input : Basic.Canonical}
    (length : left.length ≤ right.length)
    (leftRepresented : Represented left input) (rightRepresented : Represented right input) :
    left.IsPrefix right :=
  represented_suffix_prefix left [] right input length leftRepresented rightRepresented

end PrefixChain

end Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix

end
