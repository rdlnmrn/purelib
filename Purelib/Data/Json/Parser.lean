module

/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Marc Huisinga

The grammar and diagnostic conventions follow the pinned Lean JSON parser.
Private cursor operations retain the original input without Std.Parsec wrappers.
-/

-- Public parsing retains this exact JSON value owner and original decimal fields.
public import Purelib.Data.Json.Basic
import Purelib.Data.Json.Number
import Purelib.Data.String.Basic
import Init.Data.String.Bootstrap

/-!
# Finite JSON parsing

Parsing retains the original input String, original byte-offset positions and
original decimal mantissa/scale convention. Private cursor operations consume
only that input; public failures retain the original offset and diagnostic text.
-/

namespace Purelib.Data.Json

open Purelib.Data.String (append)

/-- A private parser result retaining its original position and success or error data. -/
private abbrev ParseResult (Alpha : Type) :=
  Except (String.Pos.Raw × String) (Alpha × String.Pos.Raw)

/-- A private parser retaining one original input String and its raw byte position. -/
private abbrev Parser (Alpha : Type) := String → String.Pos.Raw → ParseResult Alpha

/-- Sequence private parsing without changing the original input owner. -/
private instance : Monad Parser where
  pure value := fun _ position => .ok (value, position)
  bind action next := fun input position =>
    match action input position with
    | .error error => .error error
    | .ok (value, position) => next value input position

/-- Retain the current input position together with a parsing failure. -/
private def fail {Alpha : Type} (message : String) : Parser Alpha :=
  fun _ position => .error (position, message)

/-- Recognize the end of the original input at its retained byte position. -/
private def isEof : Parser Bool :=
  fun input position => .ok (String.Internal.atEnd input position, position)

/-- Peek at the original Unicode scalar without consuming its byte position. -/
private def peek : Parser Char := fun input position =>
  if String.Internal.atEnd input position then
    .error (position, "unexpected end of input")
  else
    .ok (String.Internal.get input position, position)

/-- Consume one original Unicode scalar and retain its next byte position. -/
private def consume : Parser Char := fun input position =>
  if String.Internal.atEnd input position then
    .error (position, "unexpected end of input")
  else
    .ok (String.Internal.get input position, String.Internal.next input position)

/-- Advance past one original scalar or retain the end-of-input error. -/
private def skip : Parser Unit := do
  let _ ← consume
  return ()

/-- Require a scalar predicate without consuming the original input.

A missing scalar retains the original end-of-input error. A present scalar that
fails the predicate retains the original expected-description diagnostic. -/
private def lookahead (predicate : Char → Bool) (description : String) : Parser Unit := do
  if predicate (← peek) then return ()
  else fail (append "expected " description)

/-- Consume exactly a retained ASCII keyword or fail at its original start position.

The keyword's input position is restored on mismatch, matching the original
prefix check. A success advances across each original keyword character once. -/
private def keyword (characters : List Nat) (text : String) : Parser Unit :=
  fun input start =>
    let rec loop (characters : List Nat) (position : String.Pos.Raw) : ParseResult Unit :=
      match characters with
      | [] => .ok ((), position)
      | character :: rest =>
          if String.Internal.atEnd input position then
            .error (start, append "expected: " text)
          else if (String.Internal.get input position).toNat == character then
            loop rest (String.Internal.next input position)
          else
            .error (start, append "expected: " text)
    loop characters start

/-- Consume exactly JSON's four ASCII whitespace characters.

Space, tab, newline and carriage return advance the original byte cursor. Every
other Unicode scalar remains available to the following grammar operation. -/
private partial def whitespace : Parser Unit := fun input position =>
  if String.Internal.atEnd input position then .ok ((), position)
  else
    let character := (String.Internal.get input position).toNat
    if character == 9 || character == 10 || character == 13 || character == 32 then
      whitespace input (String.Internal.next input position)
    else .ok ((), position)

/-- Decode one consumed hexadecimal digit with the original failure position.

Decimal digits and both ASCII letter cases retain their values from zero to
fifteen. An invalid consumed character reports the original hexadecimal error. -/
private def hexDigit : Parser Nat := do
  let value := (← consume).toNat
  if 48 ≤ value && value ≤ 57 then return value - 48
  else if 97 ≤ value && value ≤ 102 then return value - 97 + 10
  else if 65 ≤ value && value ≤ 70 then return value - 65 + 10
  else fail "invalid hex character"

/-- Construct the original Char carrier from its directly checked scalar value.

The Char proof field certifies that the retained UInt32 value is a Unicode scalar.
Failure preserves the supplied grammar error without inventing a replacement value. -/
private def checkedCharacter (value : Nat) (message : String := "") : Parser Char := do
  let scalar := UInt32.ofNat value
  if valid : scalar.isValidChar then return ⟨scalar, valid⟩
  else fail message

/-- Finish an escaped surrogate pair with its original consumed-character checks.

The second escape must begin with backslash, u and d or D, followed by a low
surrogate suffix. The result retains the original supplementary Unicode scalar. -/
private def surrogatePair (leading : Nat) : Parser Char := do
  if (← consume).toNat != 92 then fail ""
  if (← consume).toNat != 117 then fail ""
  let first := (← consume).toNat
  if first != 100 && first != 68 then fail ""
  let second ← hexDigit
  let third ← hexDigit
  let fourth ← hexDigit
  let trailing := second * 256 + third * 16 + fourth
  if trailing < 0xC00 then fail ""
  checkedCharacter ((leading - 0xD800) * 0x400 + (trailing - 0xC00) + 0x10000)

set_option backward.match.sparseCases false in
/-- Decode one escaped JSON character with the original surrogate fallback.

Unmatched surrogate escapes produce U+FFFD. A failed pair attempt restores its
initial position before returning that replacement, so later string parsing sees
all unconsumed following characters and preserves their own errors. -/
private def escapedCharacter : Parser Char := do
  let value := (← consume).toNat
  if value == 92 then return '\\'
  else if value == 34 then return '"'
  else if value == 47 then return '/'
  else if value == 98 then return '\x08'
  else if value == 102 then return '\x0c'
  else if value == 110 then return '\n'
  else if value == 114 then return '\x0d'
  else if value == 116 then return '\t'
  else if value == 117 then
    let first ← hexDigit
    let second ← hexDigit
    let third ← hexDigit
    let fourth ← hexDigit
    let scalar := first * 4096 + second * 256 + third * 16 + fourth
    if scalar < 0xD800 then checkedCharacter scalar
    else if scalar < 0xE000 then
      if scalar < 0xDC00 then
        fun input position =>
          match surrogatePair scalar input position with
          | .ok retained => .ok retained
          | .error _ => .ok ('\ufffd', position)
      else return '\ufffd'
    else checkedCharacter scalar
  else fail "illegal \\u escape"

/-- Read a quoted string after its opening quote, retaining original escape rules.

Ordinary Unicode scalars append to the retained string accumulator. Unescaped
controls fail after consumption; the closing quote is consumed exactly once. -/
private partial def stringContents (retained : String) : Parser String := do
  let character ← peek
  if character.toNat == 34 then
    skip
    return retained
  else
    let character ← consume
    if character.toNat == 92 then
      stringContents (String.Internal.pushn retained (← escapedCharacter) 1)
    else if 32 ≤ character.toNat && character.toNat ≤ 0x10ffff then
      stringContents (String.Internal.pushn retained character 1)
    else fail "unexpected character in string"

/-- Consume decimal digits while retaining their magnitude and exact digit count.

The first nondigit remains unconsumed. Each digit updates the original magnitude
by multiplication by ten and retains one additional decimal scale position. -/
private partial def digits (magnitude count : Nat) : Parser (Nat × Nat) := do
  if ← isEof then return (magnitude, count)
  else
    let value := (← peek).toNat
    if 48 ≤ value && value ≤ 57 then
      skip
      digits (10 * magnitude + (value - 48)) (count + 1)
    else return (magnitude, count)

/-- Require and consume at least one decimal digit with its original description.

The description distinguishes fractional digits, exponent digits and the leading
nonzero digit requirement. Failure retains the original unconsumed position. -/
private def requiredDigits (minimum : Nat) (description : String) : Parser (Nat × Nat) := do
  lookahead (fun character => minimum ≤ character.toNat && character.toNat ≤ 57) description
  digits 0 0

/-- Parse a decimal number with the original mantissa and scale convention.

A leading zero consumes only that digit. Fractional digits retain their exact
count; signed exponent translation uses the original mantissa multiplication and
scale subtraction, including the existing platform-size checks. -/
private def number : Parser Lean.JsonNumber := do
  let negative := (← peek).toNat == 45
  if negative then skip
  let first := (← peek).toNat
  let whole ← if first == 48 then do
      skip
      pure 0
    else do
      let (whole, _) ← requiredDigits 49 "1-9"
      pure whole
  let (magnitude, scale) ← if ← isEof then pure (whole, 0)
    else do
      let character ← peek
      if character.toNat == 46 then do
        skip
        let (fraction, places) ← requiredDigits 48 "digit"
        if places > USize.size then fail "too many decimals"
        pure (whole * Nat.pow 10 places + fraction, places)
      else pure (whole, 0)
  let mantissa := if negative then Int.neg (Int.ofNat magnitude) else Int.ofNat magnitude
  if ← isEof then return ⟨mantissa, scale⟩
  else
    let character := (← peek).toNat
    if character == 101 || character == 69 then
      skip
      let sign := (← peek).toNat
      if sign == 45 then
        skip
        let (shift, _) ← requiredDigits 48 "0-9"
        return ⟨mantissa, scale + shift⟩
      else
        if sign == 43 then skip
        let (shift, _) ← requiredDigits 48 "0-9"
        if shift > USize.size then fail "exp too large"
        return ⟨mantissa * Int.ofNat (Nat.pow 10 (shift - scale)), scale - shift⟩
    else return ⟨mantissa, scale⟩

mutual

/-- Read one finite JSON value and consume its following JSON whitespace.

Each constructor retains the original grammar's dispatch and consumed input.
Objects retain original key strings and the final value at repeated keys; arrays
retain their original ordered entries and initial capacity convention. -/
private partial def value : Parser Json := do
  let character := (← peek).toNat
  if character == 91 then
    skip
    whitespace
    if (← peek).toNat == 93 then
      skip
      whitespace
      return .arr (Array.mkEmpty 0)
    else
      return .arr (← arrayContents (Array.mkEmpty 4))
  else if character == 123 then
    skip
    whitespace
    if (← peek).toNat == 125 then
      skip
      whitespace
      return .obj []
    else
      return .obj (← objectContents [])
  else if character == 34 then
    skip
    let text ← stringContents ""
    whitespace
    return .str text
  else if character == 102 then
    keyword [102, 97, 108, 115, 101] "false"
    whitespace
    return .bool false
  else if character == 116 then
    keyword [116, 114, 117, 101] "true"
    whitespace
    return .bool true
  else if character == 110 then
    keyword [110, 117, 108, 108] "null"
    whitespace
    return .null
  else if character == 45 || (48 ≤ character && character ≤ 57) then
    let scalar ← number
    whitespace
    return .num scalar
  else fail "unexpected input"

/-- Read nonempty ordered array entries after the original opening bracket.

Each successful value is pushed once into the retained array cache. A closing
bracket finishes the original array; every other consumed separator except comma
retains the original unexpected-character failure and its byte position. -/
private partial def arrayContents (retained : Array Json) : Parser (Array Json) := do
  let entry ← value
  let retained := retained.push entry
  let separator := (← consume).toNat
  if separator == 93 then
    whitespace
    return retained
  else if separator == 44 then
    whitespace
    arrayContents retained
  else fail "unexpected character in array"

/-- Read nonempty object fields after the original opening brace.

A field is inserted only after its following comma or closing brace is checked.
Insertion retains original key strings and the latest value at each key; malformed
input retains the original grammar's lookahead and consumed-separator failures. -/
private partial def objectContents (retained : List (String × Json)) :
    Parser (List (String × Json)) := do
  lookahead (fun character => character.toNat == 34) "\""
  skip
  let key ← stringContents ""
  whitespace
  lookahead (fun character => character.toNat == 58) ":"
  skip
  whitespace
  let entry ← value
  let separator := (← consume).toNat
  if separator == 125 then
    whitespace
    return insertField key entry retained
  else if separator == 44 then
    whitespace
    objectContents (insertField key entry retained)
  else fail "unexpected character in object"

end

/-- Parse exactly one JSON value, retaining original byte-offset failures.

The complete original input String is consumed except for allowed JSON whitespace.
Success retains finite typed JSON data; failure reports the original grammar
message and byte offset without asserting any mathematical invalidity beyond it. -/
public def parse (input : String) : Except String Json :=
  match (do
    whitespace
    let parsed ← value
    unless ← isEof do fail "expected end of input"
    return parsed) input ⟨0⟩ with
  | .ok (parsed, _) => .ok parsed
  | .error (position, message) =>
      .error (append (append (append "offset " (Nat.repr position.byteIdx)) ": ") message)

end Purelib.Data.Json
