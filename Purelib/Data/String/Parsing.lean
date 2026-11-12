module

import Purelib.Data.String.Basic
import Purelib.Data.Nat.Multiplication

/-!
# Decimal String parsing

The retained UTF8 bytes recognize the same ASCII decimal grammar as the pinned
String parser. Single underscores separate digits; they cannot be first, last
or adjacent. Signed parsing permits one initial minus and keeps the same exact
natural magnitude, including signed zero and leading zeroes.
-/

namespace Purelib.Data.String

open Purelib.Data.Nat

set_option backward.match.sparseCases false

/-- Read one retained decimal byte list with its magnitude and separator state.

Only ASCII digits and a single underscore following a digit advance the scan.
A final digit is required, so empty inputs and trailing separators fail. -/
@[expose] public def decimalMagnitude : List UInt8 → Nat → Bool → Option Nat
  | [], magnitude, lastDigit => if lastDigit then some magnitude else none
  | byte :: tail, magnitude, lastDigit =>
      if byte.toNat == 95 then
        if lastDigit then decimalMagnitude tail magnitude false else none
      else if 48 ≤ byte.toNat && byte.toNat ≤ 57 then
        decimalMagnitude tail (magnitude * 10 + (byte.toNat - 48)) true
      else none

/-- Read decimal blocks in reverse order, retaining each block's positional factor. -/
private def decimalBlocks : List (Nat × Nat) → Nat
  | [] => 0
  | (factor, value) :: tail => decimalBlocks tail * factor + value

/-- Append a decimal block by merging adjacent blocks of the same width.

Each pair retains its positional factor and value, including leading zeroes.
Merging equal-width blocks carries through the stack, so complete nine-digit
blocks form balanced products instead of repeatedly multiplying the entire prefix. -/
private def pushDecimalBlock (factor value : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(factor, value)]
  | (oldFactor, oldValue) :: tail =>
      if factor = oldFactor then
        pushDecimalBlock (oldFactor * factor) (oldValue * factor + value) tail
      else (factor, value) :: (oldFactor, oldValue) :: tail

/-- Appending and carrying a block preserves its exact positional value. -/
private theorem decimalBlocks_push (blocks : List (Nat × Nat)) (factor value : Nat) :
    decimalBlocks (pushDecimalBlock factor value blocks) = decimalBlocks blocks * factor + value := by
  induction blocks generalizing factor value with
  | nil => rfl
  | cons block tail ih =>
      rcases block with ⟨oldFactor, oldValue⟩
      change
        decimalBlocks (if factor = oldFactor then
          pushDecimalBlock (oldFactor * factor) (oldValue * factor + value) tail
        else (factor, value) :: (oldFactor, oldValue) :: tail) =
          (decimalBlocks tail * oldFactor + oldValue) * factor + value
      split
      · rewrite [ih, Multiplication.right_distrib, Multiplication.mul_assoc, Nat.add_assoc]
        rfl
      · rfl

/-- Parse nine-digit leaves with balanced carries and the original separator state. -/
private def decimalChunks : List UInt8 → List (Nat × Nat) → Nat → Nat → Nat → Bool → Option Nat
  | [], blocks, factor, chunk, _, lastDigit =>
      if lastDigit then some (decimalBlocks blocks * factor + chunk) else none
  | byte :: tail, blocks, factor, chunk, count, lastDigit =>
      if byte.toNat == 95 then
        if lastDigit then decimalChunks tail blocks factor chunk count false else none
      else if 48 ≤ byte.toNat && byte.toNat ≤ 57 then
        let nextFactor := factor * 10
        let nextChunk := chunk * 10 + (byte.toNat - 48)
        if count = 8 then
          decimalChunks tail (pushDecimalBlock nextFactor nextChunk blocks) 1 0 0 true
        else decimalChunks tail blocks nextFactor nextChunk (count + 1) true
      else none

/-- One retained chunk update represents exactly the original scalar decimal update. -/
private theorem decimalUpdate (magnitude factor chunk digit : Nat) :
    magnitude * (factor * 10) + (chunk * 10 + digit) =
      (magnitude * factor + chunk) * 10 + digit := by
  rewrite [Multiplication.right_distrib, Multiplication.mul_assoc, Nat.add_assoc]
  rfl

/-- The batched parser agrees with the original scalar recurrence for all bytes and retained states. -/
private theorem decimalChunks_eq (bytes : List UInt8) (blocks : List (Nat × Nat))
    (factor chunk count : Nat) (lastDigit : Bool) :
    decimalChunks bytes blocks factor chunk count lastDigit =
      decimalMagnitude bytes (decimalBlocks blocks * factor + chunk) lastDigit := by
  induction bytes generalizing blocks factor chunk count lastDigit with
  | nil => rfl
  | cons byte tail ih =>
      change
        (if byte.toNat == 95 then
          if lastDigit then decimalChunks tail blocks factor chunk count false else none
        else if 48 ≤ byte.toNat && byte.toNat ≤ 57 then
          if count = 8 then
            decimalChunks tail (pushDecimalBlock (factor * 10) (chunk * 10 + (byte.toNat - 48)) blocks) 1 0 0 true
          else
            decimalChunks tail blocks (factor * 10) (chunk * 10 + (byte.toNat - 48)) (count + 1) true
        else none) =
        (if byte.toNat == 95 then
          if lastDigit then decimalMagnitude tail (decimalBlocks blocks * factor + chunk) false else none
        else if 48 ≤ byte.toNat && byte.toNat ≤ 57 then
          decimalMagnitude tail ((decimalBlocks blocks * factor + chunk) * 10 + (byte.toNat - 48)) true
        else none)
      split
      · split
        · exact ih blocks factor chunk count false
        · rfl
      · split
        · split
          · rewrite [ih, Nat.mul_one, Nat.add_zero, decimalBlocks_push, decimalUpdate]
            rfl
          · rewrite [ih, decimalUpdate]
            rfl
        · rfl

/-- Parse a natural decimal with the original digit-separator grammar.

The retained String encoding is accepted exactly when its bytes are ASCII
digits with optional single intervening underscores. No whitespace, signs,
non-ASCII numeral or empty input is accepted. The magnitude is exact and unbounded. -/
public def toNat? (text : _root_.String) : Option Nat :=
  decimalChunks text.toByteArray.data.toList [] 1 0 0 false

/-- Natural parsing preserves the original scalar grammar and value for every retained byte sequence. -/
public theorem toNat?_eq_decimalMagnitude (text : _root_.String) :
    toNat? text = decimalMagnitude text.toByteArray.data.toList 0 false :=
  decimalChunks_eq _ [] 1 0 0 false

/-- Parse a decimal integer with the original optional-minus grammar.

A single leading minus selects Int.negOfNat of the same parsed magnitude.
Otherwise Int.ofNat retains that magnitude; plus signs, extra signs and malformed
separator positions fail through the same natural parser. -/
public def toInt? (text : _root_.String) : Option Int :=
  match text.toByteArray.data.toList with
  | [] => none
  | first :: tail =>
      if first.toNat == 45 then
        match decimalChunks tail [] 1 0 0 false with
        | none => none
        | some magnitude => some (Int.negOfNat magnitude)
      else
        match decimalChunks (first :: tail) [] 1 0 0 false with
        | none => none
        | some magnitude => some (Int.ofNat magnitude)

/-- Signed parsing preserves the complete original minus, signed-zero and decimal grammar for every input. -/
public theorem toInt?_eq_decimalMagnitude (text : _root_.String) :
    toInt? text =
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
            | some magnitude => some (Int.ofNat magnitude) := by
  unfold toInt?
  cases input : text.toByteArray.data.toList with
  | nil => rfl
  | cons first tail =>
      dsimp only
      split
      · rewrite [decimalChunks_eq]
        rfl
      · rewrite [decimalChunks_eq]
        rfl

end Purelib.Data.String
