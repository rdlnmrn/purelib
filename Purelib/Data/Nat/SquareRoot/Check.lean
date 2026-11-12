module

public import Purelib.Data.Nat.SquareRoot
import Purelib.Data.Nat.Multiplication
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Exact natural-square decisions from a retained floor

The certified floor bounds identify every possible natural square root. A
single exact comparison therefore either supplies the root or excludes all
natural roots, retaining the original input and the computed floor.
-/

public section

namespace Purelib.Data.Nat.SquareRoot

open Purelib.Data.Nat

/-- Every exact natural square root is the retained floor root. -/
theorem Output.root_eq_of_square {value : Nat} (output : Output value)
    (candidate : Nat) (same : candidate ^ 2 = value) : output.root = candidate := by
  have lower : output.root ^ 2 ≤ candidate ^ 2 := by
    calc
      output.root ^ 2 ≤ value := output.square_le
      _ = candidate ^ 2 := same.symm
  rewrite [Multiplication.pow_two, Multiplication.pow_two] at lower
  have upper : candidate ^ 2 < (output.root + 1) ^ 2 := by
    calc
      candidate ^ 2 = value := same
      _ < (output.root + 1) ^ 2 := output.lt_succ_square
  rewrite [Multiplication.pow_two, Multiplication.pow_two] at upper
  have candidate_le : candidate ≤ output.root :=
    Nat.le_of_not_gt (by
      intro above
      have monotone := Nat.mul_self_le_mul_self (Nat.succ_le_of_lt above)
      exact Nat.not_le_of_gt upper monotone)
  have root_le : output.root ≤ candidate :=
    Nat.le_of_not_lt (by
      intro above
      have positive := Nat.lt_of_le_of_lt (Nat.zero_le candidate) above
      have first := Nat.mul_le_mul_left candidate (Nat.le_of_lt above)
      have second := Nat.mul_lt_mul_of_pos_right above positive
      exact Nat.not_le_of_gt (Nat.lt_of_le_of_lt first second) lower)
  exact Nat.le_antisymm root_le candidate_le

/-- An unequal floor square excludes every natural square root of the original value. -/
theorem Output.not_square {value : Nat} (output : Output value)
    (different : output.root ^ 2 ≠ value) : ∀ candidate : Nat, candidate ^ 2 ≠ value := by
  intro candidate same
  exact different ((congrArg (fun root : Nat => root ^ 2)
    (output.root_eq_of_square candidate same)).trans same)

set_option genInjectivity false in
/-- An exact square witness or a certified floor excluding every natural square root. -/
inductive Decision (value : Nat) where
  /-- Retain the computed floor and its exact defining square equation. -/
  | square (floor : Output value) (same : floor.root ^ 2 = value)
  /-- Retain the computed floor, its unequal square and the resulting all-input exclusion. -/
  | nonsquare (floor : Output value) (different : floor.root ^ 2 ≠ value)
      (excludes : ∀ candidate : Nat, candidate ^ 2 ≠ value)

constructive_injectivity Decision

set_option genInjectivity false in
/-- A complete natural-square decision retaining the original value as executable data. -/
structure Inspection (original : Nat) where
  /-- The actual original natural value inspected by the procedure. -/
  value : Nat
  /-- The retained value is the entire original request. -/
  value_eq : value = original
  /-- The exact witness or complete exclusion at this same retained value. -/
  decision : Decision value

constructive_injectivity Inspection

/-- Transport the retained decision to the original input without recomputing its floor. -/
@[expose] def Inspection.result {original : Nat} (inspection : Inspection original) : Decision original :=
  inspection.value_eq ▸ inspection.decision

/-- Decide natural squareness with one certified floor computation and one exact comparison. -/
@[expose] def inspect (value : Nat) : Inspection value :=
  let floor := compute value
  let decision := if same : floor.root ^ 2 = value then
      Decision.square floor same
    else .nonsquare floor same (floor.not_square same)
  ⟨value, rfl, decision⟩

end Purelib.Data.Nat.SquareRoot

end
