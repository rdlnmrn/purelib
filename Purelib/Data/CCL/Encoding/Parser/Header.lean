module

public import Purelib.Data.CCL.Encoding.Parser.Semantics.State
import Purelib.Data.List.Fold
import Purelib.Data.List.Append
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Code
import Purelib.Tactic.QuotientFreeOmega

/-!
# Exact unary-header readback

These laws consume the original initial high, initial low and loop headers.
They retain the parser's matrix and ordered history, and transfer an affine
representation using the final radial bracket and selected sector.
-/

public section

namespace Purelib.Data.CCL.Encoding.Parser.State

open Purelib.Data.CCL.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Data.ComplexContinuedFraction.Encoding

/-- Consume a positive initial-high header while retaining the initial matrix and history. -/
theorem foldl_initialHigh_header (state : State) (exponent : Nat)
    (phase : state.phase = .initial) (positive : 1 ≤ exponent) :
    (List.replicate exponent true ++ [false]).foldl step state =
      ⟨.sector .initialHigh exponent .zero, state.matrix, state.history⟩ := by
  cases state with
  | mk original matrix history =>
      cases phase
      cases exponent with
      | zero => exact (Nat.not_succ_le_zero 0 positive).elim
      | succ count =>
          rewrite [Fold.foldl_append, List.replicate_succ, List.foldl_cons]
          change step ((List.replicate count true).foldl step
            ⟨.highUnary 1, matrix, history⟩) false = _
          have folded := foldl_true_unary .initialHigh count 1 matrix history
          change (List.replicate count true).foldl step ⟨.highUnary 1, matrix, history⟩ =
            ⟨.highUnary (1 + count), matrix, history⟩ at folded
          rewrite [folded]
          have counter : 1 + count = count + 1 := by omega0
          rewrite [counter]
          rfl

/-- Consume the leading-false initial-low header and its exact unary count. -/
theorem foldl_initialLow_header (state : State) (exponent : Nat)
    (phase : state.phase = .initial) :
    (false :: (List.replicate exponent true ++ [false])).foldl step state =
      ⟨.sector .initialLow exponent .zero, state.matrix, state.history⟩ := by
  cases state with
  | mk original matrix history =>
      cases phase
      rewrite [List.foldl_cons, Fold.foldl_append]
      change step ((List.replicate exponent true).foldl step
        ⟨.lowUnary 0, matrix, history⟩) false = _
      have folded := foldl_true_unary .initialLow exponent 0 matrix history
      change (List.replicate exponent true).foldl step ⟨.lowUnary 0, matrix, history⟩ =
        ⟨.lowUnary (0 + exponent), matrix, history⟩ at folded
      rewrite [folded, Nat.zero_add]
      rfl

/-- Consume an exact loop header from its original zero unary counter. -/
theorem foldl_loop_header (state : State) (exponent : Nat)
    (phase : state.phase = .loopUnary 0) :
    (List.replicate exponent true ++ [false]).foldl step state =
      ⟨.sector .loop exponent .zero, state.matrix, state.history⟩ := by
  cases state with
  | mk original matrix history =>
      cases phase
      rewrite [Fold.foldl_append]
      have folded := foldl_true_unary .loop exponent 0 matrix history
      change (List.replicate exponent true).foldl step ⟨.loopUnary 0, matrix, history⟩ =
        ⟨.loopUnary (0 + exponent), matrix, history⟩ at folded
      rewrite [folded, Nat.zero_add]
      rfl

/-- A retained affine representation survives changing only its active phase when the new phase holds. -/
theorem represents_phase {state : State} {input tail : Basic.Canonical}
    (represented : Semantics.State.Represents state input tail)
    (phase : Syntax.Phase) (active : Semantics.Basic.activeHolds phase tail) :
    Semantics.State.Represents ⟨phase, state.matrix, state.history⟩ input tail :=
  ⟨represented.1, represented.2.1, represented.2.2.1, active⟩

/-- A radial bracket and selected-sector condition certify the same unfinished zero-bit sector phase. -/
theorem represents_sectorZero {state : State} {input tail : Basic.Canonical}
    (represented : Semantics.State.Represents state input tail)
    (kind : Syntax.BlockKind) (exponent : Nat) (sector : Sector)
    (radial : Semantics.Basic.radialBracket kind exponent tail)
    (selected : sector.Holds (Semantics.Basic.normalizedValue kind exponent tail)) :
    Semantics.State.Represents
      ⟨.sector kind exponent .zero, state.matrix, state.history⟩ input tail := by
  apply represents_phase represented
  refine ⟨radial, sector, ?_, selected⟩
  rewrite [Sector.Code.sectorCandidates_zero]
  exact Sector.Code.mem_sectorTable sector

/-- Reading the first two bits of a selected sector preserves the affine tail and all original constraints. -/
theorem represents_sectorTwo {state : State} {input tail : Basic.Canonical}
    (represented : Semantics.State.Represents state input tail)
    (kind : Syntax.BlockKind) (exponent : Nat) (first second third : Bool)
    (phase : state.phase = .sector kind exponent .zero)
    (full : Semantics.Basic.fullBlockHolds kind exponent
      (Sector.Code.sectorOfBits first second third) tail) :
    Semantics.State.Represents (step (step state first) second) input tail := by
  have stateEq : step (step state first) second =
      ⟨.sector kind exponent (.two first second), state.matrix, state.history⟩ := by
    cases state with
    | mk original matrix history => cases phase; rfl
  rewrite [stateEq]
  apply represents_phase represented
  exact ⟨full.1, Sector.Code.sectorOfBits first second third,
    Sector.Code.sectorOfBits_mem_two_candidates first second third, full.2⟩

end Purelib.Data.CCL.Encoding.Parser.State

end
