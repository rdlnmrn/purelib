module

public import Purelib.Data.CCL.Encoding.Parser.Next
public import Purelib.Data.CCL.Encoding.Parser.Terminal.Normalization
import Purelib.Data.List.Append

/-!
# Canonical terminal words

A terminal word retains an affine represented precursor at the original
two-bit sector phase. Its final bit encodes the exact normalized sector
representative and changes the final tail to projective infinity.
-/

public section

namespace Purelib.Data.CCL.Encoding.Parser.Terminal

open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.List
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

/-- An exact sector representative in the original two-bit phase admits no further affine bit. -/
theorem sectorTwo_noStep (state : State) (input tail : Basic.Canonical)
    (kind : Syntax.BlockKind) (exponent : Nat) (first second third : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (represented : Semantics.State.Represents state input tail)
    (determinant : Matrix2.Matrix2.determinant state.matrix ≠ 0)
    (terminal : Semantics.Basic.normalizedValue kind exponent tail =
      (Sector.Code.sectorOfBits first second third).rep) :
    ∀ bit, ¬Semantics.Prefix.CanStep state input bit := by
  intro bit possible
  have advance := (Next.canStep_iff_canAdvanceAt state input tail determinant represented bit).mp possible
  unfold Next.CanAdvanceAt at advance
  rewrite [phase] at advance
  have holds := advance.1.2
  rewrite [terminal] at holds
  have sectorEq := Sector.holds_unique
    (Sector.rep_holds (Sector.Code.sectorOfBits first second third)) holds
  have residualZero : Semantics.Basic.normalizedValue kind exponent tail -
      (Sector.Code.sectorOfBits first second bit).rep = 0 := by
    rewrite [terminal, sectorEq]
    exact Basic.sub_self _
  exact advance.2 residualZero

namespace Word

/-- A complete canonical word ends with the exact sector representative of its affine precursor.

The witness retains the original parser's two-bit phase and affine constraints.
Its final bit records the same sector at projective infinity; the completed
word itself is not an affine prefix.
-/
@[expose] def Represents (word : List Bool) (input : Basic.Canonical) : Prop :=
  ∃ (stem : List Bool) (kind : Syntax.BlockKind) (exponent : Nat)
      (first second third : Bool) (tail : Basic.Canonical),
    word = stem ++ [third] ∧
      (State.parse stem).phase = .sector kind exponent (.two first second) ∧
      Semantics.State.Represents (State.parse stem) input tail ∧
      Semantics.Basic.normalizedValue kind exponent tail =
        (Sector.Code.sectorOfBits first second third).rep

/-- A represented terminal precursor forbids an affine extension of its exact word. -/
theorem noStep {word : List Bool} {input : Basic.Canonical}
    (represented : Represents word input) :
    ∃ stem bit, word = stem ++ [bit] ∧ Semantics.Prefix.Represented stem input ∧
      ∀ next, ¬Semantics.Prefix.CanStep (State.parse stem) input next := by
  rcases represented with ⟨stem, kind, exponent, first, second, third, tail,
    wordEq, phase, retained, terminal⟩
  exact ⟨stem, third, wordEq, ⟨tail, retained⟩,
    sectorTwo_noStep (State.parse stem) input tail kind exponent first second third
      phase retained (State.parse_det_ne stem) terminal⟩

/-- A represented affine word is strictly shorter than a canonical terminal word for the same input. -/
theorem affine_length_lt {word affine : List Bool} {input : Basic.Canonical}
    (terminal : Represents word input) (represented : Semantics.Prefix.Represented affine input) :
    affine.length < word.length := by
  rcases noStep terminal with ⟨stem, bit, wordEq, stemRepresents, stopped⟩
  have lengthBound : affine.length ≤ stem.length := by
    by_cases order : affine.length ≤ stem.length
    · exact order
    · have opposite : stem.length ≤ affine.length := Nat.le_of_lt (Nat.lt_of_not_ge order)
      rcases Semantics.Prefix.represented_prefix_of_length_le opposite stemRepresents represented with
        ⟨suffix, identity⟩
      cases suffix with
      | nil =>
          have same : stem = affine := (Append.append_nil stem).symm.trans identity
          exact same.symm ▸ Nat.le_refl stem.length
      | cons next remaining =>
          have child : Semantics.Prefix.Represented (stem ++ [next]) input :=
            Semantics.Prefix.represented_of_prefix
              ⟨remaining, (Append.append_assoc stem [next] remaining).trans identity⟩ represented
          rcases child with ⟨tail, retained⟩
          have possible : Semantics.Prefix.CanStep (State.parse stem) input next :=
            ⟨tail, (State.parse_append_singleton stem next) ▸ retained⟩
          exact (stopped next possible).elim
  rewrite [wordEq, Append.length_append]
  change affine.length < stem.length + 1
  exact Nat.lt_succ_of_le lengthBound

/-- Every represented affine word is a literal prefix of the canonical terminal precursor. -/
theorem affine_prefix {word affine : List Bool} {input : Basic.Canonical}
    (terminal : Represents word input) (represented : Semantics.Prefix.Represented affine input) :
    affine.IsPrefix word := by
  rcases noStep terminal with ⟨stem, bit, wordEq, stemRepresents, _⟩
  have bound := affine_length_lt terminal represented
  rewrite [wordEq, Append.length_append] at bound
  have length : affine.length ≤ stem.length := Nat.le_of_lt_succ bound
  rcases Semantics.Prefix.represented_prefix_of_length_le length represented stemRepresents with
    ⟨suffix, identity⟩
  refine ⟨suffix ++ [bit], ?_⟩
  exact (Append.append_assoc affine suffix [bit]).symm.trans
    ((congrArg (fun earlier => earlier ++ [bit]) identity).trans wordEq.symm)

/-- Complete canonical terminal words for the same rational input are literally equal.

The represented affine precursors have equal lengths and lie on the same
original parser prefix chain. Their retained tail and phase then identify
the final selected-sector bit.
-/
theorem unique {left right : List Bool} {input : Basic.Canonical}
    (leftRepresents : Represents left input) (rightRepresents : Represents right input) : left = right := by
  rcases leftRepresents with ⟨leftStem, leftKind, leftExponent, leftFirst, leftSecond, leftThird, leftTail,
    leftWord, leftPhase, leftRetained, leftTerminal⟩
  rcases rightRepresents with ⟨rightStem, rightKind, rightExponent, rightFirst, rightSecond, rightThird, rightTail,
    rightWord, rightPhase, rightRetained, rightTerminal⟩
  have leftCertificate : Represents left input :=
    ⟨leftStem, leftKind, leftExponent, leftFirst, leftSecond, leftThird, leftTail,
      leftWord, leftPhase, leftRetained, leftTerminal⟩
  have rightCertificate : Represents right input :=
    ⟨rightStem, rightKind, rightExponent, rightFirst, rightSecond, rightThird, rightTail,
      rightWord, rightPhase, rightRetained, rightTerminal⟩
  have leftBound := affine_length_lt rightCertificate ⟨leftTail, leftRetained⟩
  have rightBound := affine_length_lt leftCertificate ⟨rightTail, rightRetained⟩
  rewrite [rightWord, Append.length_append] at leftBound
  rewrite [leftWord, Append.length_append] at rightBound
  have leftLe : leftStem.length ≤ rightStem.length := Nat.le_of_lt_succ leftBound
  have rightLe : rightStem.length ≤ leftStem.length := Nat.le_of_lt_succ rightBound
  have lengthEq := Nat.le_antisymm leftLe rightLe
  rcases Semantics.Prefix.represented_prefix_of_length_le leftLe ⟨leftTail, leftRetained⟩
    ⟨rightTail, rightRetained⟩ with ⟨suffix, appended⟩
  have lengthSuffix := congrArg List.length appended
  rewrite [Append.length_append, ← lengthEq] at lengthSuffix
  have zero : suffix.length = 0 := Nat.add_left_cancel
    (lengthSuffix.trans (Nat.add_zero leftStem.length).symm)
  have suffixEq : suffix = [] := by
    cases suffix with
    | nil => rfl
    | cons bit rest => exact Nat.noConfusion zero
  rewrite [suffixEq, Append.append_nil] at appended
  cases appended
  have phaseEq := leftPhase.symm.trans rightPhase
  rcases Syntax.Phase.sector.inj phaseEq with ⟨kindEq, exponentEq, bitsEq⟩
  cases kindEq
  cases exponentEq
  rcases Sector.Code.SectorBits.two.inj bitsEq with ⟨firstEq, secondEq⟩
  cases firstEq
  cases secondEq
  have tailEq := Semantics.State.Represents.tail_unique (State.parse_det_ne leftStem)
    leftRetained rightRetained
  cases tailEq
  have repsEq := leftTerminal.symm.trans rightTerminal
  have selectedEq := congrArg Sector.select repsEq
  rewrite [Sector.select_rep, Sector.select_rep] at selectedEq
  have codesEq := congrArg Sector.code selectedEq
  rewrite [Sector.Code.sectorOfBits_code, Sector.Code.sectorOfBits_code] at codesEq
  have thirdEq := (List.cons.inj (List.cons.inj (List.cons.inj codesEq).2).2).1
  exact leftWord.trans ((congrArg (fun bit => leftStem ++ [bit]) thirdEq).trans rightWord.symm)

end Word

end Purelib.Data.CCL.Encoding.Parser.Terminal

end
