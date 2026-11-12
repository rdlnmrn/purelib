module

public import Init.Data.Char.Basic
public import Purelib.Data.Presentation

namespace Purelib.Data.Char.Presentation

/-- A literal scalar code is valid exactly when it is a Unicode scalar value. -/
@[expose] public def Valid (code : Nat) : Prop := code.isValidChar

set_option genInjectivity false in
/-- The checked result of a proposed natural Unicode scalar code. -/
public inductive Check (code : Nat) where
  /-- The code is a valid scalar. -/ | valid (proof : Valid code)
  /-- The code is in the UTF-16 surrogate range. -/
  | surrogate (lower : 0xd800 ≤ code) (upper : code < 0xe000)
  /-- The code is beyond the Unicode scalar range. -/
  | outOfRange (lower : 0x110000 ≤ code)

/-- Check the original scalar range, retaining a precise reason for rejection. -/
@[expose] public def check (code : Nat) : Check code :=
  if low : code < 0xd800 then .valid (.inl low)
  else if surrogate : code < 0xe000 then
    .surrogate (Nat.le_of_not_gt low) surrogate
  else if high : code < 0x110000 then
    .valid (.inr ⟨Nat.le_of_not_gt surrogate, high⟩)
  else .outOfRange (Nat.le_of_not_gt high)

/-- Derive the validity decision from the same typed scalar check. -/
@[expose] public def recognize (code : Nat) : Decidable (Valid code) :=
  match check code with
  | .valid proof => .isTrue proof
  | .surrogate lower upper => .isFalse (fun proof =>
      match proof with
      | .inl low => Nat.not_lt_of_ge lower low
      | .inr ⟨high, _⟩ => Nat.not_lt_of_ge high upper)
  | .outOfRange lower => .isFalse (fun proof =>
      match proof with
      | .inl low => Nat.not_lt_of_ge lower (Nat.lt_trans low (by decide))
      | .inr ⟨_, high⟩ => Nat.not_lt_of_ge lower high)

/-- A natural scalar code and its original validity certificate. -/
public abbrev Display := {code : Nat // Valid code}

/-- Construct the original character from an admissible code. -/
@[expose] public def read (display : Display) : _root_.Char :=
  _root_.Char.ofNatAux display.val display.property

/-- Project the original character's scalar and its validity certificate. -/
@[expose] public def quote (character : _root_.Char) : Display :=
  ⟨character.toNat, character.valid⟩

/-- A constructed character retains the supplied natural scalar. -/
public theorem read_toNat (display : Display) : (read display).toNat = display.val := rfl

/-- Reading a quoted character recovers its original value. -/
public theorem read_quote (character : _root_.Char) : read (quote character) = character := by
  cases character with
  | mk value valid =>
    cases value with
    | ofBitVec bits =>
      cases bits with
      | ofFin index =>
        cases index
        rfl

/-- Quoting a read character recovers the original scalar display. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  apply Subtype.ext
  exact read_toNat display

/-- Two displays are the same when their scalar codes agree. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Compare the two finite natural scalar codes. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Scalar equality agrees exactly with equality of the original characters. -/
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
    exact (read_toNat left).symm.trans ((congrArg _root_.Char.toNat equal).trans (read_toNat right))

/-- The finite scalar-code presentation of the original character owner. -/
@[expose] public def scalar : Purelib.Data.Presentation Nat where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

/-!
The typed input is a natural Unicode scalar code, not a byte sequence or a
string parser. `check` accepts precisely `Nat.isValidChar` and separately
identifies the surrogate range and values beyond the Unicode limit. `read` and
`quote` preserve the original `Char`/`UInt32` owner, with equality and both
round trips proved above. The existing `Char.ofNat` remains a separate total
conversion whose invalid input falls back to zero. Comparisons and construction
inherit their finite logical dependencies and the separate runtime and
construction-admission obligations.
-/

end Purelib.Data.Char.Presentation
