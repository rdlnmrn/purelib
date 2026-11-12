module

/-!
# Finite coded register-machine syntax

Values are finite trees of naturals, pairs and encoded instruction lists.
Programs may inspect inputs, form coded pairs and call a program supplied
as finite input data. No executable function is stored in an instruction
or value. Register readback and extension are explicit finite recursions.
-/

public section

namespace Purelib.Computation.Machine

set_option genInjectivity false in
mutual
  /-- A finite machine value is a natural, an ordered pair or the literal code of a finite program. -/
  inductive Value where
    /-- A retained natural input or result. -/ | number (value : Nat)
    /-- An ordered pair of two original finite values. -/ | pair (left right : Value)
    /-- The original finite instruction list, used as executable program input. -/ | program
      (instructions : List Instruction)

  /-- A finite register instruction has explicit operands and targets, including invocation of supplied code. -/
  inductive Instruction where
    /-- Return register zero to the caller, or halt at the outermost frame. -/ | halt
    /-- Advance without changing any register. -/ | tick
    /-- Store one literal finite value in the displayed register. -/ | constant (target : Nat) (value : Value)
    /-- Copy an original register value to the displayed target. -/ | copy (target source : Nat)
    /-- Store the successor of the supplied natural register reading. -/ | successor (target source : Nat)
    /-- Store the predecessor of the supplied natural register reading. -/ | predecessor (target source : Nat)
    /-- Set the instruction counter to the displayed target. -/ | jump (target : Nat)
    /-- Branch on whether the supplied natural register reading is zero. -/ | jumpZero
      (source zeroTarget nonzeroTarget : Nat)
    /-- Store an ordered pair of the two original register readings. -/ | pair (target left right : Nat)
    /-- Store the first component of a supplied pair. -/ | first (target source : Nat)
    /-- Store the second component of a supplied pair. -/ | second (target source : Nat)
    /-- Invoke supplied program code with its original input, returning its result to register zero. -/ | call
      (code input : Nat)
end

/-- The original finite instruction list is the machine program representation. -/
abbrev Program := List Instruction

namespace Value

/-- Embed the exact finite program as explicit input data without changing its instructions. -/
@[expose] def encode (program : Program) : Value := .program program

/-- Decode only an actual finite program-code constructor. -/
@[expose] def decode : Value → Option Program
  | .program instructions => some instructions
  | .number _ | .pair _ _ => none

/-- Decoding the original encoded program returns the same exact instruction list. -/
theorem decode_encode (program : Program) : decode (encode program) = some program := rfl

/-- Read a natural value; nonnumeric data have the displayed zero reading. -/
@[expose] def natural : Value → Nat
  | .number value => value
  | .pair _ _ | .program _ => 0

end Value

namespace Registers

/-- Read one original finite register; an absent register has the displayed zero value. -/
@[expose] def get : List Value → Nat → Value
  | [], _ => .number 0
  | value :: _, 0 => value
  | _ :: remaining, index + 1 => get remaining index

/-- Store one finite register value, explicitly extending absent preceding registers with zero. -/
@[expose] def put : List Value → Nat → Value → List Value
  | [], 0, value => [value]
  | [], index + 1, value => .number 0 :: put [] index value
  | _ :: remaining, 0, value => value :: remaining
  | earlier :: remaining, index + 1, value => earlier :: put remaining index value

/-- Readback of the updated register is the exact value supplied to that same update. -/
theorem get_put (registers : List Value) (index : Nat) (value : Value) :
    get (put registers index value) index = value := by
  induction index generalizing registers with
  | zero => cases registers <;> rfl
  | succ index induction =>
      cases registers with
      | nil => exact induction []
      | cons _ remaining => exact induction remaining

end Registers

end Purelib.Computation.Machine

end
