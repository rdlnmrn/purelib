import mathlib.Tactic.QuotientFreeRing
import CCL.Boundary.NextBit

/-!
# Finite candidates for a local CCL terminal

A represented value can stop immediately before the third sector bit only
when its normalized tail is exactly one of the two sector representatives
compatible with the already-read two-bit fragment.  This module makes those
two candidates explicit.  It is the bounded replacement for repeatedly
excluding arbitrary rational terminal samples.
-/

namespace CCL.CCLTerminalCandidates

abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev State := CCL.RawParser.State
abbrev BlockKind := CCL.RawParser.BlockKind
abbrev Sector := CCL.Sectors.Sector

open RFAP.ConstructiveGaussian.Gaussian
open CCL.Sectors
open CCL.RawParser
open CCL.RawParserSemantics
open CCL.ParserStep

/-- Tail value whose selected normalized residual is exactly zero. -/
def terminalBefore
    (kind : BlockKind) (exponent : Nat) (sector : Sector) : Gaussian :=
  match kind with
  | .initialLow => (natPow gamma exponent)⁻¹ * sector.rep
  | .initialHigh | .loop => natPow gamma exponent * sector.rep

theorem normalizedValue_terminalBefore
    (kind : BlockKind) (exponent : Nat) (sector : Sector) :
    normalizedValue kind exponent (terminalBefore kind exponent sector) =
      sector.rep := by
  have powerNonzero : natPow gamma exponent ≠ 0 :=
    natPow_ne_zero_direct gamma (by decide) exponent
  have cancellation : natPow gamma exponent *
      (natPow gamma exponent)⁻¹ = 1 := by
    exact RFAP.CanonicalGaussian.Gaussian.mul_inv_cancel _ powerNonzero
  cases kind with
  | initialLow =>
      simp only [normalizedValue, terminalBefore]
      calc
        natPow gamma exponent *
            ((natPow gamma exponent)⁻¹ * sector.rep) =
          (natPow gamma exponent * (natPow gamma exponent)⁻¹) *
            sector.rep :=
          (RFAP.ConstructiveGaussian.Gaussian.mul_assoc _ _ _).symm
        _ = 1 * sector.rep := by rw [cancellation]
        _ = sector.rep := RFAP.ConstructiveGaussian.Gaussian.one_mul _
  | initialHigh | loop =>
      simp only [normalizedValue, terminalBefore]
      calc
        (natPow gamma exponent * sector.rep) *
            (natPow gamma exponent)⁻¹ =
          sector.rep *
            (natPow gamma exponent * (natPow gamma exponent)⁻¹) := by
          apply RFAP.ConstructiveGaussian.Gaussian.ext <;>
            simp only [mul_re, mul_im] <;> ring1
        _ = sector.rep * 1 := by rw [cancellation]
        _ = sector.rep := RFAP.ConstructiveGaussian.Gaussian.mul_one _

theorem normalizedValue_injective
    (kind : BlockKind) (exponent : Nat) :
    Function.Injective (normalizedValue kind exponent) := by
  intro left right equal
  have powerNonzero : natPow gamma exponent ≠ 0 :=
    natPow_ne_zero_direct gamma (by decide) exponent
  cases kind with
  | initialLow =>
      apply RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne powerNonzero
      calc
        left * natPow gamma exponent =
            natPow gamma exponent * left :=
          RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
        _ = natPow gamma exponent * right := equal
        _ = right * natPow gamma exponent :=
          RFAP.ConstructiveGaussian.Gaussian.mul_comm _ _
  | initialHigh | loop =>
      have inverseNonzero : (natPow gamma exponent)⁻¹ ≠ 0 :=
        inv_ne_zero_direct powerNonzero
      exact RFAP.ConstructiveGaussian.Gaussian.mul_right_cancel_of_ne
        inverseNonzero equal

theorem eq_terminalBefore_of_normalized_eq
    (kind : BlockKind) (exponent : Nat) (sector : Sector)
    {before : Gaussian}
    (equal : normalizedValue kind exponent before = sector.rep) :
    before = terminalBefore kind exponent sector := by
  apply normalizedValue_injective kind exponent
  rw [normalizedValue_terminalBefore]
  exact equal

/-- The two possible pre-third-bit terminal tails. -/
def candidateBefore
    (kind : BlockKind) (exponent : Nat) (first second bit : Bool) : Gaussian :=
  terminalBefore kind exponent (sectorOfBits first second bit)

/-- The corresponding original-input candidate through the current finite
decoder matrix. -/
def candidateInput
    (state : State) (kind : BlockKind) (exponent : Nat)
    (first second bit : Bool) : Gaussian :=
  homographic state.matrix
    (candidateBefore kind exponent first second bit)

private theorem sectorZero_active_of_radial
    (kind : BlockKind) (exponent : Nat) (value : Gaussian)
    (radial : radialBracket kind exponent value) :
    activeHolds (.sector kind exponent .zero) value := by
  let sector := Sector.select (normalizedValue kind exponent value)
  have band := normalizedValue_band_of_radialBracket kind exponent value radial
  refine ⟨radial, sector, ?_, Sector.select_spec _ band.1⟩
  rw [sectorCandidates_zero]
  cases sector <;> simp [sectorTable]

private theorem sectorCandidate_zero_child
    (sector : Sector) (member : sector ∈ sectorCandidates .zero) :
    ∃ bit, sector ∈ sectorCandidates (.one bit) := by
  cases sector <;> simp_all

private theorem sectorCandidate_one_child
    (first : Bool) (sector : Sector)
    (member : sector ∈ sectorCandidates (.one first)) :
    ∃ bit, sector ∈ sectorCandidates (.two first bit) := by
  cases first <;> cases sector <;> simp_all

/-- A represented affine value can fail to admit both Boolean children only
immediately before the third sector bit.  All radial and shorter-sector
phases have an explicit child selected by finite rational comparisons. -/
theorem phase_eq_sectorTwo_of_no_advance
    (state : State) (input before : Gaussian)
    (represents : Represents state input before)
    (terminal : ∀ bit, ¬CanAdvanceAt state bit before) :
    ∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second) := by
  rcases state with ⟨phase, matrix, history⟩
  have historyHolds := represents.2.2.1
  have active := represents.2.2.2
  cases phase with
  | initial =>
      by_cases low : normSq before < 2
      · exact (terminal false (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds, low⟩)).elim
      · have high : (2 : Coordinate) ^ 1 ≤ normSq before := by
          rw [pow_one]
          exact le_of_not_gt low
        exact (terminal true (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds, high⟩)).elim
  | highUnary count =>
      by_cases higher : (2 : Coordinate) ^ (count + 1) ≤ normSq before
      · exact (terminal true (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds, higher⟩)).elim
      · have radial : radialBracket .initialHigh count before :=
          ⟨active, lt_of_not_ge higher⟩
        exact (terminal false (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds,
            sectorZero_active_of_radial .initialHigh count before radial⟩)).elim
  | lowUnary count =>
      cases count with
      | zero =>
          by_cases lower : 1 ≤ normSq before
          · have upper : normSq before < 2 := by
              simpa [activeHolds] using active
            have radial : radialBracket .initialLow 0 before := by
              simpa [radialBracket] using And.intro lower upper
            exact (terminal false (by
              change (∀ constraint ∈ history, constraint.Holds before) ∧ _
              exact ⟨historyHolds,
                sectorZero_active_of_radial .initialLow 0 before radial⟩)).elim
          · have next : normSq before < 1 := lt_of_not_ge lower
            exact (terminal true (by
              change (∀ constraint ∈ history, constraint.Holds before) ∧ _
              refine ⟨historyHolds, ?_⟩
              simpa [step, activeHolds] using next)).elim
      | succ count =>
          by_cases lower :
              1 ≤ (2 : Coordinate) ^ (count + 1) * normSq before
          · have upper :
                (2 : Coordinate) ^ (count + 1) * normSq before < 2 := by
              calc
                (2 : Coordinate) ^ (count + 1) * normSq before =
                    2 * ((2 : Coordinate) ^ count * normSq before) := by
                      rw [pow_succ]
                      ring1
                _ < 2 * 1 :=
                  RFAP.ConstructiveFraction.mul_lt_mul_of_pos_left_direct
                    (by decide) active
                _ = 2 := by ring1
            have radial : radialBracket .initialLow (count + 1) before :=
              ⟨lower, upper⟩
            exact (terminal false (by
              change (∀ constraint ∈ history, constraint.Holds before) ∧ _
              exact ⟨historyHolds,
                sectorZero_active_of_radial .initialLow (count + 1) before
                  radial⟩)).elim
          · have next :
                (2 : Coordinate) ^ (count + 1) * normSq before < 1 :=
              lt_of_not_ge lower
            exact (terminal true (by
              change (∀ constraint ∈ history, constraint.Holds before) ∧ _
              exact ⟨historyHolds, next⟩)).elim
  | loopUnary count =>
      by_cases higher :
          (2 : Coordinate) ^ (count + 1) < normSq before
      · exact (terminal true (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds, higher⟩)).elim
      · have radial : radialBracket .loop count before :=
          ⟨active, le_of_not_gt higher⟩
        exact (terminal false (by
          change (∀ constraint ∈ history, constraint.Holds before) ∧ _
          exact ⟨historyHolds,
            sectorZero_active_of_radial .loop count before radial⟩)).elim
  | sector kind exponent bits =>
      cases bits with
      | zero =>
          rcases active with ⟨radial, sector, member, sectorHolds⟩
          rcases sectorCandidate_zero_child sector member with
            ⟨bit, childMember⟩
          exact (terminal bit (by
            change (∀ constraint ∈ history, constraint.Holds before) ∧ _
            exact ⟨historyHolds, radial, sector, childMember, sectorHolds⟩)).elim
      | one first =>
          rcases active with ⟨radial, sector, member, sectorHolds⟩
          rcases sectorCandidate_one_child first sector member with
            ⟨bit, childMember⟩
          exact (terminal bit (by
            change (∀ constraint ∈ history, constraint.Holds before) ∧ _
            exact ⟨historyHolds, radial, sector, childMember, sectorHolds⟩)).elim
      | two first second =>
          exact ⟨kind, exponent, first, second, rfl⟩

/-- At the two-bit sector phase, absence of both possible next bits forces
the represented tail to be one of the two explicit terminal candidates. -/
theorem before_eq_candidate_of_sectorTwo_terminal
    (state : State) (input before : Gaussian)
    (kind : BlockKind) (exponent : Nat) (first second : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (represents : Represents state input before)
    (terminal : ∀ bit, ¬CanAdvanceAt state bit before) :
    before = candidateBefore kind exponent first second false ∨
      before = candidateBefore kind exponent first second true := by
  have active := represents.2.2.2
  rw [phase] at active
  rcases active with ⟨radial, sector, member, sectorHolds⟩
  have selected : sector = sectorOfBits first second false ∨
      sector = sectorOfBits first second true := by
    cases first <;> cases second <;> cases sector <;>
      simp_all [sectorCandidates, sectorTable, Sector.code, SectorBits.word,
        isWordPrefix, sectorOfBits]
  rcases selected with selected | selected
  · left
    subst sector
    have residualZero : normalizedValue kind exponent before -
        (sectorOfBits first second false).rep = 0 := by
      by_contra residualNonzero
      apply terminal false
      unfold CanAdvanceAt
      rw [phase]
      exact ⟨⟨radial, sectorHolds⟩, residualNonzero⟩
    apply eq_terminalBefore_of_normalized_eq
    exact CCL.ParserStep.gaussian_eq_of_sub_eq_zero residualZero
  · right
    subst sector
    have residualZero : normalizedValue kind exponent before -
        (sectorOfBits first second true).rep = 0 := by
      by_contra residualNonzero
      apply terminal true
      unfold CanAdvanceAt
      rw [phase]
      exact ⟨⟨radial, sectorHolds⟩, residualNonzero⟩
    apply eq_terminalBefore_of_normalized_eq
    exact CCL.ParserStep.gaussian_eq_of_sub_eq_zero residualZero

theorem input_eq_candidate_of_sectorTwo_terminal
    (state : State) (input before : Gaussian)
    (kind : BlockKind) (exponent : Nat) (first second : Bool)
    (phase : state.phase = .sector kind exponent (.two first second))
    (represents : Represents state input before)
    (terminal : ∀ bit, ¬CanAdvanceAt state bit before) :
    input = candidateInput state kind exponent first second false ∨
      input = candidateInput state kind exponent first second true := by
  rcases before_eq_candidate_of_sectorTwo_terminal state input before kind
      exponent first second phase represents terminal with left | right
  · left
    change before = terminalBefore kind exponent
      (sectorOfBits first second false) at left
    rw [candidateInput, candidateBefore, ← left]
    exact represents.2.1
  · right
    change before = terminalBefore kind exponent
      (sectorOfBits first second true) at right
    rw [candidateInput, candidateBefore, ← right]
    exact represents.2.1

/-- Every represented local terminal is one of a phase-computable pair of
original-input candidates. -/
theorem input_eq_candidate_of_terminal
    (state : State) (input before : Gaussian)
    (represents : Represents state input before)
    (terminal : ∀ bit, ¬CanAdvanceAt state bit before) :
    ∃ kind exponent first second,
      state.phase = .sector kind exponent (.two first second) ∧
        (input = candidateInput state kind exponent first second false ∨
          input = candidateInput state kind exponent first second true) := by
  rcases phase_eq_sectorTwo_of_no_advance state input before represents
      terminal with ⟨kind, exponent, first, second, phase⟩
  exact ⟨kind, exponent, first, second, phase,
    input_eq_candidate_of_sectorTwo_terminal state input before kind exponent
      first second phase represents terminal⟩

end CCL.CCLTerminalCandidates
