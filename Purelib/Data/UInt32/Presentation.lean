module

public import Init.Data.UInt.BasicAux
public import Purelib.Data.Presentation

namespace Purelib.Data.UInt32.Presentation

/-- A natural code is valid when it fits the original unsigned 32-bit owner. -/
@[expose] public def Valid (code : Nat) : Prop := code < _root_.UInt32.size

set_option genInjectivity false in
/-- The result of checking a natural code against the original UInt32 bound. -/
public inductive Check (code : Nat) where
  /-- The code fits in the retained 32-bit payload. -/ | valid (bound : Valid code)
  /-- The code is at least the first value outside that payload. -/
  | outOfRange (lower : _root_.UInt32.size ≤ code)

/-- Check the original bound, retaining evidence for acceptance or rejection. -/
@[expose] public def check (code : Nat) : Check code :=
  if bound : code < _root_.UInt32.size then .valid bound
  else .outOfRange (Nat.le_of_not_gt bound)

/-- Derive the validity decision from the same bounded-payload checker. -/
@[expose] public def recognize (code : Nat) : Decidable (Valid code) :=
  match check code with
  | .valid bound => .isTrue bound
  | .outOfRange lower => .isFalse (Nat.not_lt_of_ge lower)

/-- A natural payload and its original 32-bit bound certificate. -/
public abbrev Display := {code : Nat // Valid code}

/-- Construct the original UInt32 owner from a bounded natural payload. -/
@[expose] public def read (display : Display) : _root_.UInt32 :=
  _root_.UInt32.ofNatLT display.val display.property

/-- Project the original UInt32 payload and its retained Fin bound. -/
@[expose] public def quote (value : _root_.UInt32) : Display :=
  ⟨value.toNat, value.toBitVec.toFin.isLt⟩

/-- A constructed UInt32 retains the supplied natural payload. -/
public theorem read_toNat (display : Display) : (read display).toNat = display.val := rfl

/-- Reading a quoted payload recovers the original UInt32 value. -/
public theorem read_quote (value : _root_.UInt32) : read (quote value) = value := by
  cases value with
  | ofBitVec bits =>
    cases bits with
    | ofFin index =>
      cases index
      rfl

/-- Quoting a read value recovers the original bounded display. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  exact read_toNat display

/-- Two displays are the same when their original payloads agree. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Compare the two finite natural payloads. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Payload equality agrees exactly with equality of the original UInt32 values. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro equal
    cases left with
    | mk left _ =>
      cases right with
      | mk right _ =>
        cases equal
        rfl
  · intro equal
    exact (read_toNat left).symm.trans ((congrArg _root_.UInt32.toNat equal).trans (read_toNat right))

/-- The bounded natural-payload presentation of the original UInt32 owner. -/
@[expose] public def payload : Purelib.Data.Presentation Nat where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-!
The input is a typed natural number. `check` accepts it only below
`UInt32.size`, and otherwise retains the failed bound. `read` uses the
original `UInt32.ofNatLT`; `quote` retains the original `BitVec`/`Fin` value
and bound. The round trips and `same_iff_read_eq` identify code equality
with original UInt32 equality. This checker is distinct from `UInt32.ofNat`,
which reduces an arbitrary input modulo the size. Logical and native
construction dependencies remain separate admission obligations.
-/

end Purelib.Data.UInt32.Presentation
