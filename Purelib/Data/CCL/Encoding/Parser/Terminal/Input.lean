module

public import Purelib.Data.CCL.Encoding.Parser.Terminal.Candidates

/-!
# Exact terminal inputs and certified continuation

The retained parser phase determines at most two possible terminal inputs.
Excluding their exact homography images turns the original local decision
into a certified unique next bit, with the parser's boundary conventions
unchanged.
-/

public section

namespace Purelib.Data.CCL.Encoding.Parser.Terminal

open Purelib.Data.Gaussian

/-- Compute the exact possible terminal input images from the original parser phase and retained matrix.

Only the phase with two already-read sector bits can be terminal. Its two
final-bit choices determine the original candidate tails and their retained
matrix images; every other phase returns the empty list.
-/
@[expose] def inputs (state : State) : List Basic.Canonical :=
  match state.phase with
  | .sector kind exponent (.two first second) =>
      [candidateInput state kind exponent first second false,
        candidateInput state kind exponent first second true]
  | _ => []

/-- The actual finite terminal-input list has at most two entries. -/
theorem inputs_length_le_two (state : State) : (inputs state).length ≤ 2 := by
  unfold inputs
  cases state.phase with
  | initial => exact Nat.zero_le _
  | highUnary _ => exact Nat.zero_le _
  | lowUnary _ => exact Nat.zero_le _
  | loopUnary _ => exact Nat.zero_le _
  | sector _ _ bits =>
      cases bits with
      | zero => exact Nat.zero_le _
      | one _ => exact Nat.zero_le _
      | two _ _ => exact Nat.le_refl _

/-- Every represented input with no locally admissible next bit occurs in the exact retained terminal-input list. -/
theorem input_mem_of_no_advance (state : State) (input before : Basic.Canonical)
    (represented : Semantics.State.Represents state input before)
    (none : ∀ bit, ¬Next.CanAdvanceAt state bit before) : input ∈ inputs state := by
  rcases input_eq_candidate_of_terminal state input before represented none with
    ⟨kind, exponent, first, second, phase, candidate⟩
  unfold inputs
  rewrite [phase]
  rcases candidate with left | right
  · rewrite [left]
    exact List.Mem.head _
  · rewrite [right]
    exact List.Mem.tail _ (List.Mem.head [])

end Purelib.Data.CCL.Encoding.Parser.Terminal

namespace Purelib.Data.CCL.Encoding.Parser.Next

open Purelib.Data.Gaussian
open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2

set_option genInjectivity false in
/-- Retain the actual unique admissible next bit for one original parser state and represented input.

The original input and parser state index both the existential affine-tail
certificate and uniqueness law. No terminal padding or replacement input is
included in this exact raw-parser continuation.
-/
structure AdmissibleBit (state : State) (input : Basic.Canonical) where
  /-- The actual Boolean selected by the original local parser decision. -/ bit : Bool
  /-- The selected bit has an exact affine representation of this same input. -/ possible :
    Semantics.Prefix.CanStep state input bit
  /-- Every admissible Boolean at these same parents equals the selected bit. -/ unique :
    ∀ other, Semantics.Prefix.CanStep state input other → other = bit

/-- Compute the unique next bit after excluding the exact original terminal-input list.

The builder runs the original local decision once. Its terminal branch is
excluded by the retained candidate theorem; success retains the very same
bit, possibility certificate and uniqueness proof returned by that decision.
-/
def admissibleBitOfExcluded (state : State) (input before : Basic.Canonical)
    (determinant : Matrix2.Matrix2.determinant state.matrix ≠ 0)
    (represented : Semantics.State.Represents state input before)
    (excluded : input ∉ Terminal.inputs state) : AdmissibleBit state input := by
  match decideLocal state input before determinant represented with
  | .next bit possible unique => exact ⟨bit, possible, unique⟩
  | .terminal noBits =>
      have noAdvance : ∀ bit, ¬CanAdvanceAt state bit before := by
        intro bit advance
        exact noBits bit ((canStep_iff_canAdvanceAt state input before determinant represented bit).mpr advance)
      exact (excluded (Terminal.input_mem_of_no_advance state input before represented noAdvance)).elim

end Purelib.Data.CCL.Encoding.Parser.Next
