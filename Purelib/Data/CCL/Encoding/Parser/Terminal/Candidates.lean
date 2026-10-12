module
import Purelib.Data.Rat.Fraction
import Purelib.Data.List.Membership
public import Purelib.Data.CCL.Encoding.Parser.Next
import Purelib.Data.CCL.Encoding.Parser.Semantics.Basic
import Purelib.Data.CCL.Encoding.Parser.Semantics.Normalization
import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.CCL.Encoding.Parser.State
import Purelib.Data.CCL.Encoding.Parser.Syntax
public import Purelib.Data.CCL.Encoding.Parser.Terminal.Normalization
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.BinaryPrefix.Decision
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Projective.Homography.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.BinaryPrefix.Basic
import Purelib.Tactic.Ring

/-!
# Finite candidates for a local CCL terminal

A represented value can stop immediately before the third sector bit only
when its normalized tail is exactly one of the two sector representatives
compatible with the already-read two-bit fragment.  This module makes those
two candidates explicit.  It is the bounded replacement for repeatedly
excluding arbitrary rational terminal samples.
-/

public section

namespace Purelib.Data.CCL.Encoding.Parser.Terminal

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
/-- Recover the exact terminal Gaussian for a retained kind, exponent, two sector bits and final Boolean choice. -/
@[expose] def candidateBefore
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (first second bit : Bool) : Basic.Canonical :=
  Parser.Terminal.terminalBefore kind exponent (Sector.Code.sectorOfBits first second bit)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Geometry.Projective in
/-- Apply the retained parser matrix homography to its exact terminal candidate tail. -/
@[expose] def candidateInput
    (state : State) (kind : Parser.Syntax.BlockKind) (exponent : Nat)
    (first second bit : Bool) : Basic.Canonical :=
  Homography.Basic.homographic state.matrix
    (candidateBefore kind exponent first second bit)

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
/-- The retained radial bracket provides a sector witness for the phase with no sector bits read. -/
private theorem sectorZero_active_of_radial
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (value : Basic.Canonical)
    (radial : Parser.Semantics.Basic.radialBracket kind exponent value) :
    Parser.Semantics.Basic.activeHolds (.sector kind exponent .zero) value := by
  let sector := ComplexContinuedFraction.Encoding.Sector.select (Parser.Semantics.Basic.normalizedValue kind exponent
    value)
  have band := Parser.Semantics.Normalization.normalizedValue_band_of_radialBracket kind exponent value radial
  refine ⟨radial, sector, ?_, ComplexContinuedFraction.Encoding.Sector.select_spec _ band.1⟩
  rw [Sector.Code.sectorCandidates_zero]
  cases sector <;> decide

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- A represented input admitting neither next bit is in the phase with exactly two retained sector bits. -/
theorem phase_eq_sectorTwo_of_no_advance
    (state : State) (input before : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents state input before)
    (terminal : ∀ bit, ¬Parser.Next.CanAdvanceAt state bit before) :
    ∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second) := by
  rcases state with ⟨phase, matrix, history⟩
  have historyHolds := represents.2.2.1
  have active := represents.2.2.2
  cases phase with
  | initial =>
      by_cases low : Basic.Canonical.normSq before < 2
      · exact (terminal false (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds, low⟩)).elim
      · have high : (2 : Fraction.Rational) ^ 1 ≤ Basic.Canonical.normSq before := by
          rw [pow_one]
          exact le_of_not_gt low
        exact (terminal true (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds, high⟩)).elim
  | highUnary count =>
      by_cases higher : (2 : Fraction.Rational) ^ (count + 1) ≤ Basic.Canonical.normSq before
      · exact (terminal true (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds, higher⟩)).elim
      · have radial : Parser.Semantics.Basic.radialBracket .initialHigh count before :=
          ⟨active, lt_of_not_ge higher⟩
        exact (terminal false (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds,
            sectorZero_active_of_radial .initialHigh count before radial⟩)).elim
  | lowUnary count =>
      cases count with
      | zero =>
          by_cases lower : 1 ≤ Basic.Canonical.normSq before
          · have upper : Basic.Canonical.normSq before < 2 := by
              exact active
            have radial : Parser.Semantics.Basic.radialBracket .initialLow 0 before := by
              simpa only [Parser.Semantics.Basic.radialBracket, pow_zero, Fraction.Field.one_mul, -eq_self, -iff_self]
                using And.intro lower upper
            exact (terminal false (by
              change (∀ constraint ∈ history, constraint.Holds before) ∧ _
              exact ⟨historyHolds,
                sectorZero_active_of_radial .initialLow 0 before radial⟩)).elim
          · have next : Basic.Canonical.normSq before < 1 := lt_of_not_ge lower
            exact (terminal true (by
              change (∀ constraint ∈ history, constraint.Holds before) ∧ _
              refine ⟨historyHolds, ?_⟩
              simpa only [Parser.State.step, Parser.Semantics.Basic.activeHolds, pow_zero, Fraction.Field.one_mul,
                if_pos (Eq.refl true), -eq_self, -iff_self] using next)).elim
      | succ count =>
          by_cases lower :
              1 ≤ (2 : Fraction.Rational) ^ (count + 1) * Basic.Canonical.normSq before
          · have upper :
                (2 : Fraction.Rational) ^ (count + 1) * Basic.Canonical.normSq before < 2 := by
              calc
                (2 : Fraction.Rational) ^ (count + 1) * Basic.Canonical.normSq before =
                    2 * ((2 : Fraction.Rational) ^ count * Basic.Canonical.normSq before) := by
                      rw [pow_succ]
                      ring1
                _ < 2 * 1 :=
                  Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                    (by decide) active
                _ = 2 := by ring1
            have radial : Parser.Semantics.Basic.radialBracket .initialLow (count + 1) before :=
              ⟨lower, upper⟩
            exact (terminal false (by
              change (∀ constraint ∈ history, constraint.Holds before) ∧ _
              exact ⟨historyHolds,
                sectorZero_active_of_radial .initialLow (count + 1) before
                  radial⟩)).elim
          · have next :
                (2 : Fraction.Rational) ^ (count + 1) * Basic.Canonical.normSq before < 1 :=
              lt_of_not_ge lower
            exact (terminal true (by
              change (∀ constraint ∈ history, constraint.Holds before) ∧ _
              exact ⟨historyHolds, next⟩)).elim
  | loopUnary count =>
      by_cases higher :
          (2 : Fraction.Rational) ^ (count + 1) < Basic.Canonical.normSq before
      · exact (terminal true (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds, higher⟩)).elim
      · have radial : Parser.Semantics.Basic.radialBracket .loop count before :=
          ⟨active, le_of_not_gt higher⟩
        exact (terminal false (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds,
            sectorZero_active_of_radial .loop count before radial⟩)).elim
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          rcases active with ⟨radial, sector, member, sectorHolds⟩
          rcases Sector.Code.Boundary.sectorCandidate_zero_child sector member with
            ⟨bit, childMember⟩
          exact (terminal bit (by
            change (∀ constraint ∈ history, constraint.Holds before) ∧ _
            exact ⟨historyHolds, radial, sector, childMember, sectorHolds⟩)).elim
      | one first =>
          rcases active with ⟨radial, sector, member, sectorHolds⟩
          rcases Sector.Code.Boundary.sectorCandidate_one_child first sector member with
            ⟨bit, childMember⟩
          exact (terminal bit (by
            change (∀ constraint ∈ history, constraint.Holds before) ∧ _
            exact ⟨historyHolds, radial, sector, childMember, sectorHolds⟩)).elim
      | two first second =>
          exact ⟨kind, exponent, first, second, rfl⟩

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
open Purelib.Data.List in
/-- A terminal tail in the two-bit sector phase equals one of its two exact final-bit candidates. -/
theorem before_eq_candidate_of_sectorTwo_terminal
    (state : State) (input before : Basic.Canonical)
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (first second : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (represents : Parser.Semantics.State.Represents state input before)
    (terminal : ∀ bit, ¬Parser.Next.CanAdvanceAt state bit before) :
    before = candidateBefore kind exponent first second false ∨
      before = candidateBefore kind exponent first second true := by
  have active := represents.2.2.2
  rw [phase] at active
  rcases active with ⟨radial, sector, member, sectorHolds⟩
  have selected : sector = Sector.Code.sectorOfBits first second false ∨
      sector = Sector.Code.sectorOfBits first second true := by
    cases first <;> cases second <;> cases sector <;>
      first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | exact False.elim (by revert member; decide)
  rcases selected with selected | selected
  · left
    subst sector
    have residualZero : Parser.Semantics.Basic.normalizedValue kind exponent before -
        (Sector.Code.sectorOfBits first second false).rep = 0 := by
      by_contra residualNonzero
      apply terminal false
      unfold Parser.Next.CanAdvanceAt
      rw [phase]
      exact ⟨⟨radial, sectorHolds⟩, residualNonzero⟩
    apply Parser.Terminal.eq_terminalBefore_of_normalized_eq
    exact Basic.gaussian_eq_of_sub_eq_zero residualZero
  · right
    subst sector
    have residualZero : Parser.Semantics.Basic.normalizedValue kind exponent before -
        (Sector.Code.sectorOfBits first second true).rep = 0 := by
      by_contra residualNonzero
      apply terminal true
      unfold Parser.Next.CanAdvanceAt
      rw [phase]
      exact ⟨⟨radial, sectorHolds⟩, residualNonzero⟩
    apply Parser.Terminal.eq_terminalBefore_of_normalized_eq
    exact Basic.gaussian_eq_of_sub_eq_zero residualZero

open Purelib.Data.CCL.Encoding in
open Purelib.Data.ComplexContinuedFraction.Encoding in
open Purelib.Data.Gaussian in
/-- The represented input of a terminal two-bit sector phase equals one of its two candidate homography images. -/
theorem input_eq_candidate_of_sectorTwo_terminal
    (state : State) (input before : Basic.Canonical)
    (kind : Parser.Syntax.BlockKind) (exponent : Nat) (first second : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (represents : Parser.Semantics.State.Represents state input before)
    (terminal : ∀ bit, ¬Parser.Next.CanAdvanceAt state bit before) :
    input = candidateInput state kind exponent first second false ∨
      input = candidateInput state kind exponent first second true := by
  rcases before_eq_candidate_of_sectorTwo_terminal state input before kind
      exponent first second phase represents terminal with left | right
  · left
    change before = Parser.Terminal.terminalBefore kind exponent
      (Sector.Code.sectorOfBits first second false) at left
    rw [candidateInput, candidateBefore, ← left]
    exact represents.2.1
  · right
    change before = Parser.Terminal.terminalBefore kind exponent
      (Sector.Code.sectorOfBits first second true) at right
    rw [candidateInput, candidateBefore, ← right]
    exact represents.2.1

open Purelib.Data.CCL.Encoding in
open Purelib.Data.Gaussian in
/-- Every represented input admitting neither next bit has a retained two-bit sector phase and one of its two exact
candidate inputs. -/
theorem input_eq_candidate_of_terminal
    (state : State) (input before : Basic.Canonical)
    (represents : Parser.Semantics.State.Represents state input before)
    (terminal : ∀ bit, ¬Parser.Next.CanAdvanceAt state bit before) :
    ∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second) ∧
        (input = candidateInput state kind exponent first second false ∨
          input = candidateInput state kind exponent first second true) := by
  rcases phase_eq_sectorTwo_of_no_advance state input before represents
      terminal with ⟨kind, exponent, first, second, phase⟩
  exact ⟨kind, exponent, first, second, phase,
    input_eq_candidate_of_sectorTwo_terminal state input before kind exponent
      first second phase represents terminal⟩

end Purelib.Data.CCL.Encoding.Parser.Terminal

end
