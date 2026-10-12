module

public import Init.Data.Int.Basic
import Purelib.Data.Nat.Division
import Purelib.Algebra.Ring.Int
import Purelib.Tactic.Ring

/-!
# Retained same-parity integer divisibility witnesses

The original natural quotients by two and common remainder supply the
same signed integer factors for differences and sums of the two inputs.
All statements concern those original natural inputs and integer casts.
-/

open Purelib.Data

namespace Purelib.Data.Int.Parity

public section

/-- Casting the natural numeral two to Int gives the integer numeral two. -/
theorem natCast_two_int : ((2 : Nat) : Int) = 2 := by decide

/-- Equal natural parities make the integer difference even.

Equality of the two remainders modulo two gives an explicit integer factor witnessing
that two divides the difference of their casts. -/
theorem two_dvd_int_sub_of_same_parity
    {left right : Nat} (sameParity : left % 2 = right % 2) :
    (2 : Int) ∣ (left : Int) - (right : Int) := by
  have leftDivision : left % 2 + 2 * (left / 2) = left :=
    Nat.Division.mod_add_div left 2
  have rightDivision : right % 2 + 2 * (right / 2) = right :=
    Nat.Division.mod_add_div right 2
  have leftCast :
      (left : Int) = ((left % 2 : Nat) : Int) +
        2 * ((left / 2 : Nat) : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) leftDivision
    exact castEquation.symm
  have rightCast :
      (right : Int) = ((right % 2 : Nat) : Int) +
        2 * ((right / 2 : Nat) : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) rightDivision
    exact castEquation.symm
  refine ⟨((left / 2 : Nat) : Int) - ((right / 2 : Nat) : Int), ?_⟩
  have sameParityCast :
      ((left % 2 : Nat) : Int) = ((right % 2 : Nat) : Int) :=
    congrArg (fun value : Nat => (value : Int)) sameParity
  rw [leftCast, rightCast, sameParityCast]
  ring1

/-- Equal natural parities make the integer sum even.

Equality of the two remainders modulo two gives an explicit integer factor witnessing
that two divides the sum of their casts. -/
theorem two_dvd_int_add_of_same_parity
    {left right : Nat} (sameParity : left % 2 = right % 2) :
    (2 : Int) ∣ (left : Int) + (right : Int) := by
  have leftDivision : left % 2 + 2 * (left / 2) = left :=
    Nat.Division.mod_add_div left 2
  have rightDivision : right % 2 + 2 * (right / 2) = right :=
    Nat.Division.mod_add_div right 2
  have leftCast :
      (left : Int) = ((left % 2 : Nat) : Int) +
        2 * ((left / 2 : Nat) : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) leftDivision
    exact castEquation.symm
  have rightCast :
      (right : Int) = ((right % 2 : Nat) : Int) +
        2 * ((right / 2 : Nat) : Int) := by
    have castEquation :=
      congrArg (fun value : Nat => (value : Int)) rightDivision
    exact castEquation.symm
  refine ⟨((left / 2 : Nat) : Int) + ((right / 2 : Nat) : Int) +
    ((left % 2 : Nat) : Int), ?_⟩
  have sameParityCast :
      ((left % 2 : Nat) : Int) = ((right % 2 : Nat) : Int) :=
    congrArg (fun value : Nat => (value : Int)) sameParity
  rw [leftCast, rightCast, sameParityCast]
  ring1

end

end Purelib.Data.Int.Parity
