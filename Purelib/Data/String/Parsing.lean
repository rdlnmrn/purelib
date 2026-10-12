module

import Purelib.Data.String.Basic

/-!
# Decimal String parsing

The retained UTF8 bytes recognize the same ASCII decimal grammar as the pinned
String parser. Single underscores separate digits; they cannot be first, last
or adjacent. Signed parsing permits one initial minus and keeps the same exact
natural magnitude, including signed zero and leading zeroes.
-/

namespace Purelib.Data.String

set_option backward.match.sparseCases false

/-- Read one retained decimal byte list with its magnitude and separator state.

Only ASCII digits and a single underscore following a digit advance the scan.
A final digit is required, so empty inputs and trailing separators fail. -/
private def decimalMagnitude : List UInt8 → Nat → Bool → Option Nat
  | [], magnitude, lastDigit => if lastDigit then some magnitude else none
  | byte :: tail, magnitude, lastDigit =>
      if byte.toNat == 95 then
        if lastDigit then decimalMagnitude tail magnitude false else none
      else if 48 ≤ byte.toNat && byte.toNat ≤ 57 then
        decimalMagnitude tail (magnitude * 10 + (byte.toNat - 48)) true
      else none

/-- Parse a natural decimal with the original digit-separator grammar.

The retained String encoding is accepted exactly when its bytes are ASCII
digits with optional single intervening underscores. No whitespace, signs,
non-ASCII numeral or empty input is accepted. The magnitude is exact and unbounded. -/
public def toNat? (text : _root_.String) : Option Nat :=
  decimalMagnitude text.toByteArray.data.toList 0 false

/-- Parse a decimal integer with the original optional-minus grammar.

A single leading minus selects Int.negOfNat of the same parsed magnitude.
Otherwise Int.ofNat retains that magnitude; plus signs, extra signs and malformed
separator positions fail through the same natural parser. -/
public def toInt? (text : _root_.String) : Option Int :=
  match text.toByteArray.data.toList with
  | [] => none
  | first :: tail =>
      if first.toNat == 45 then
        match decimalMagnitude tail 0 false with
        | none => none
        | some magnitude => some (Int.negOfNat magnitude)
      else
        match decimalMagnitude (first :: tail) 0 false with
        | none => none
        | some magnitude => some (Int.ofNat magnitude)

end Purelib.Data.String
