module

-- Retain the original decimal-number carrier and the original literal builders.
public import Lean.Data.Json.Basic
import Purelib.Data.Int.Decimal
import Purelib.Data.String.Basic
import Init.Data.String.Bootstrap

/-!
# JSON decimal scalars

These operations retain Lean.JsonNumber's original mantissa and decimal exponent.
Scalar decoding recognizes the exact integer representation; equality compares
those retained fields and does not identify differently scaled equal values.
Decimal rendering retains the original mantissa, scale and scientific threshold.
-/

namespace Purelib.Data.Json.Number

/-- Compare decimal-number representations by their original fields.

This reuses the original record equality decision, as in the original JSON Boolean
comparison. Equal values with different retained decimal scales remain distinct. -/
@[expose] public def beq (left right : Lean.JsonNumber) : Bool :=
  decide (left = right)

set_option backward.match.sparseCases false in
/-- Decode a natural number from the original nonnegative exponent-zero representation.

Decimal-scale records are rejected even when their mathematical value is integral.
Negative records are rejected, retaining the original scalar decoder semantics. -/
@[expose] public def getNat? : Lean.JsonNumber → Except String Nat
  | ⟨Int.ofNat value, 0⟩ => .ok value
  | ⟨Int.ofNat _, Nat.succ _⟩ => .error "Natural number expected"
  | ⟨Int.negSucc _, 0⟩ => .error "Natural number expected"
  | ⟨Int.negSucc _, Nat.succ _⟩ => .error "Natural number expected"

/-- Decode an integer from the original exponent-zero representation.

Both integer constructors retain their original signed value. Any positive decimal
scale is rejected, matching the existing integer JSON decoder convention. -/
@[expose] public def getInt? : Lean.JsonNumber → Except String Int
  | ⟨value, 0⟩ => .ok value
  | ⟨_, Nat.succ _⟩ => .error "Integer expected"

/-- The original natural-number JSON builder decodes to its retained natural value.

The original builder stores an Int.ofNat mantissa with decimal exponent zero.
No printing, normalization, ordered map or JSON carrier is involved. -/
public theorem getNat?_fromNat (value : Nat) :
    getNat? (Lean.JsonNumber.fromNat value) = .ok value := rfl

/-- The original integer JSON builder decodes to its retained integer value.

The original builder stores that exact signed mantissa with decimal exponent zero.
No approximation or decimal-scale normalization is performed. -/
public theorem getInt?_fromInt (value : Int) :
    getInt? (Lean.JsonNumber.fromInt value) = .ok value := rfl

open Purelib.Data.String (append)
open Purelib.Data.Int

/-- Count the decimal digits of a retained natural magnitude.

Zero has one digit. Each recursive step divides the original magnitude by ten,
retaining the decimal printer's existing digit-count convention. -/
private partial def countDigits (value : Nat) : Nat :=
  loop value 1
where
  /-- Retain the number of divisions needed to reach a single decimal digit.

  The current digit count increases once for each division by ten. The original
  nonnegative magnitude and its current quotient determine every recursive step. -/
  loop (remaining digits : Nat) : Nat :=
    if remaining ≤ 9 then digits else loop (remaining / 10) (digits + 1)

/-- Remove the final ASCII zero characters from a decimal digit string.

The scan retains the original string and remembers the end of its last nonzero
character. Extraction uses that original string and the retained byte positions. -/
private partial def trimZeros (value : String) : String :=
  scan ⟨0⟩ ⟨0⟩
where
  /-- Scan the retained string and remember the last nonzero character boundary.

  Position advancement and final extraction use the same input string. Final
  zeros change only the remembered boundary, not the retained original bytes. -/
  scan (position retainedEnd : String.Pos.Raw) : String :=
    if String.Internal.atEnd value position then
      String.Internal.extract value ⟨0⟩ retainedEnd
    else
      let next := String.Internal.next value position
      let retainedEnd :=
        if (String.Internal.get value position).toNat == 48 then retainedEnd else next
      scan next retainedEnd

set_option backward.match.sparseCases false in
/-- Render a retained JSON decimal number using its original mantissa and scale.

The nine-digit scientific-notation threshold and removal of trailing fractional
zeros follow the original decimal convention. Natural magnitudes use Nat.repr;
negative prefixes use the owned signed renderer without changing the scalar data. -/
public def repr : Lean.JsonNumber → String
  | ⟨mantissa, 0⟩ => Decimal.repr mantissa
  | ⟨mantissa, Nat.succ exponent⟩ =>
      let exponent := Nat.succ exponent
      let sign := match mantissa with
        | Int.ofNat _ => ""
        | Int.negSucc _ => "-"
      let magnitude := mantissa.natAbs
      let candidate : Int := 9 + Int.ofNat (countDigits magnitude) - Int.ofNat exponent
      let scientific : Int := match candidate with
        | Int.ofNat _ => Int.ofNat 0
        | Int.negSucc negative => Int.negSucc negative
      let divisor := Nat.pow 10 (exponent - scientific.natAbs)
      let whole := Nat.repr (magnitude / divisor)
      let remainder := magnitude % divisor
      if remainder == 0 && scientific == 0 then
        append sign whole
      else
        let fractional := trimZeros (String.Internal.drop (Nat.repr (divisor + remainder)) 1)
        let suffix := if scientific == 0 then "" else append "e" (Decimal.repr scientific)
        append (append (append (append sign whole) ".") fractional) suffix

end Purelib.Data.Json.Number
