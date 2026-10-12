module
import Purelib.Data.List.Filter
import Purelib.Data.List.Reverse
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
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
  ∃ tail, Parser.Semantics.State.Represents (Parser.State.parse word) input tail

/-- Removing the last bit preserves representation of the original Gaussian input. -/
theorem represented_drop_last
    {word : BinaryPrefix.Basic.SourceEncodingRawParserSemanticsWordAlias} {bit : Bool} {input : Basic.Canonical}
    (represented : Represented (word ++ [bit]) input) :
    Represented word input := by
  rcases represented with ⟨tail, represented⟩
  refine ⟨Parser.Semantics.Transition.previousTail (Parser.State.parse word) bit tail, ?_⟩
  apply Parser.Semantics.Transition.step_represents_previous (Parser.State.parse word) bit input tail
  simpa only [Parser.State.parse_append_singleton, -eq_self, -iff_self] using represented

end

/-- The empty word represents every Gaussian input using that same value as its tail. -/
theorem represented_nil (input : Basic.Canonical) :
  Represented [] input :=
  ⟨input, Parser.Semantics.State.initialState_represents input⟩

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
        rewrite [List.reverse_nil, Purelib.Data.List.Append.append_nil]
          at retained
        exact retained
    | cons bit remaining inductionHypothesis =>
        intro representedAll
        apply inductionHypothesis
        apply represented_drop_last
          (word := shorter ++ remaining.reverse) (bit := bit)
        simpa only [Purelib.Data.List.Reverse.reverse_cons, Purelib.Data.List.Append.append_assoc, -eq_self, -iff_self]
          using representedAll
  apply removeReversed suffix.reverse
  simpa only [Purelib.Data.List.Reverse.reverse_reverse, -eq_self, -iff_self] using represented

/-- Require an exact Gaussian tail representing the original input after the supplied next parser bit. -/
@[expose] def CanStep (state : State) (input :
  Basic.Canonical) (bit : Bool) : Prop :=
  ∃ tail, Parser.Semantics.State.Represents (Parser.State.step state bit) input tail

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
  have falsePrevious := Parser.Semantics.Transition.step_represents_previous state false input falseTail
    falseRepresents
  have truePrevious := Parser.Semantics.Transition.step_represents_previous state true input trueTail
    trueRepresents
  have previousEqual := Parser.Semantics.State.Represents.tail_unique determinant falsePrevious
    truePrevious
  rcases state with ⟨phase, matrix, history⟩
  cases phase with
  | initial =>
      simp only [Parser.Semantics.Transition.previousTail, -eq_self, -iff_self]
        at previousEqual
      subst trueTail
      have low := falseRepresents.2.2.2
      have high := trueRepresents.2.2.2
      change Basic.Canonical.normSq falseTail < 2 at low
      change (2 : Fraction.Rational) ^ 1 ≤ Basic.Canonical.normSq falseTail at high
      rw [pow_one] at high
      exact (not_lt_of_ge high) low
  | highUnary count =>
      simp only [Parser.Semantics.Transition.previousTail, -eq_self, -iff_self]
        at previousEqual
      subst trueTail
      have upper := falseRepresents.2.2.2.1.2
      have lower := trueRepresents.2.2.2
      exact (not_lt_of_ge lower) upper
  | lowUnary count =>
      simp only [Parser.Semantics.Transition.previousTail, -eq_self, -iff_self]
        at previousEqual
      subst trueTail
      have lower := falseRepresents.2.2.2.1.1
      have upper := trueRepresents.2.2.2
      exact (not_lt_of_ge lower) upper
  | loopUnary count =>
      simp only [Parser.Semantics.Transition.previousTail, -eq_self, -iff_self]
        at previousEqual
      subst trueTail
      have upper := falseRepresents.2.2.2.1.2
      have lower := trueRepresents.2.2.2
      exact (not_lt_of_ge upper) lower
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          simp only [Parser.Semantics.Transition.previousTail, -eq_self, -iff_self]
            at previousEqual
          subst trueTail
          rcases falseRepresents.2.2.2 with
            ⟨_, falseSector, falseMember, falseHolds⟩
          rcases trueRepresents.2.2.2 with
            ⟨_, trueSector, trueMember, trueHolds⟩
          have sectorEqual :=
            ComplexContinuedFraction.Encoding.Sector.holds_unique falseHolds trueHolds
          subst trueSector
          have falsePrefix : BinaryPrefix.Decision.isWordPrefix [false] falseSector.code = true :=
            (Purelib.Data.List.Filter.mem_filter.mp falseMember).2
          have truePrefix : BinaryPrefix.Decision.isWordPrefix [true] falseSector.code = true :=
            (Purelib.Data.List.Filter.mem_filter.mp trueMember).2
          cases falseSector <;> first | exact Bool.noConfusion falsePrefix | exact Bool.noConfusion truePrefix
      | one first =>
          simp only [Parser.Semantics.Transition.previousTail, -eq_self, -iff_self]
            at previousEqual
          subst trueTail
          rcases falseRepresents.2.2.2 with
            ⟨_, falseSector, falseMember, falseHolds⟩
          rcases trueRepresents.2.2.2 with
            ⟨_, trueSector, trueMember, trueHolds⟩
          have sectorEqual :=
            ComplexContinuedFraction.Encoding.Sector.holds_unique falseHolds trueHolds
          subst trueSector
          have falsePrefix :
              BinaryPrefix.Decision.isWordPrefix [first, false] falseSector.code = true :=
            (Purelib.Data.List.Filter.mem_filter.mp falseMember).2
          have truePrefix :
              BinaryPrefix.Decision.isWordPrefix [first, true] falseSector.code = true :=
            (Purelib.Data.List.Filter.mem_filter.mp trueMember).2
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
              (Parser.Semantics.Basic.normalizedValue kind exponent
                (Homography.Basic.homographic falseBlock falseTail)) := falseNewest.2.2
          have trueHolds : trueSector.Holds
              (Parser.Semantics.Basic.normalizedValue kind exponent
                (Homography.Basic.homographic trueBlock trueTail)) := trueNewest.2.2
          change Homography.Basic.homographic falseBlock falseTail =
            Homography.Basic.homographic trueBlock trueTail at previousEqual
          have normalizedEqual := congrArg
            (Parser.Semantics.Basic.normalizedValue kind exponent) previousEqual
          rw [normalizedEqual] at falseHolds
          have sectorEqual :=
            ComplexContinuedFraction.Encoding.Sector.holds_unique falseHolds trueHolds
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
  apply canStep_unique (Parser.State.parse_det_ne word)
  · rcases leftRepresented with ⟨tail, represented⟩
    exact ⟨tail, by simpa only [Parser.State.parse_append_singleton, -eq_self, -iff_self] using represented⟩
  · rcases rightRepresented with ⟨tail, represented⟩
    exact ⟨tail, by simpa only [Parser.State.parse_append_singleton, -eq_self, -iff_self] using represented⟩

end Purelib.Data.CCL.Encoding.Parser.Semantics.Prefix

end
