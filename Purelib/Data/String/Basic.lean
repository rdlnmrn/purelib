module

import Init.Data.String.Defs
import Init.Data.String.Bootstrap
import Purelib.Data.Nat.Remainder
import Purelib.Tactic.QuotientFreeOmega
-- The exposed append body retains this owner's original UTF8 certificate.
public import Purelib.Data.ByteArray.UTF8
-- Exposed bytewise comparison retains this original byte-list operation.
public import Purelib.Data.ByteArray.Basic

/-!
# String concatenation, comparison and retained pattern operations

The original String carrier retains its original appended byte-array data. Only
the proof of UTF8 validity uses the direct concatenation certificate. Comparison
consumes those original UTF8 byte arrays without decoding the input strings.
-/

namespace Purelib.Data.String

set_option backward.match.sparseCases false

open Purelib.Data.ByteArray

/-- Append two strings while retaining their original UTF8 byte-array append.

Both original strings keep their original carriers and byte data. Their existing
validity witnesses certify the same concatenation without decoding either string.
Compiled calls retain the original native string append and its borrowed right input. -/
@[extern "lean_string_append", expose] public def append
    (left : _root_.String) (right : @& _root_.String) : _root_.String where
  toByteArray := left.toByteArray ++ right.toByteArray
  isValidUTF8 := UTF8.append left.isValidUTF8 right.isValidUTF8

/-- String concatenation reads back as the original byte-array concatenation.

The two input encodings occur exactly once, in order, in the retained result. The
UTF8 certificate does not alter the bytes used by checkpoint hashes and writes. -/
public theorem toUTF8_append (left right : _root_.String) :
    (append left right).toUTF8 = left.toUTF8 ++ right.toUTF8 := by
  rewrite [_root_.String.toUTF8_eq_toByteArray,
    _root_.String.toUTF8_eq_toByteArray, _root_.String.toUTF8_eq_toByteArray]
  exact Eq.refl _

/-- Use the retained original string append data with its direct UTF8 certificate.

Opening this scope selects the same original native append and appended byte
arrays. The retained UTF8 witnesses supply only the validity proof field;
all original string data and the two input owners remain unchanged. -/
public scoped instance (priority := 1001) : Append _root_.String where
  append := append

open Purelib.Data.ByteArray (compareBytes) in
/-- Compare the original UTF8 byte encodings of two strings lexicographically.

Both original byte arrays are read directly, without decoding either string.
The first unequal byte decides the order; equal prefixes retain the order of the
remaining encodings. No generic ordered carrier or comparison instance is retained. -/
@[expose] public def compare (left right : _root_.String) : Ordering :=
  compareBytes left.toByteArray.data.toList right.toByteArray.data.toList

/-- Compare a retained byte prefix with the beginning of the original byte input.

Every successful step retains the same byte equality and original tails.
An empty prefix matches any input; a remaining prefix cannot match an empty input. -/
private def bytePrefix : List UInt8 → List UInt8 → Bool
  | [], _ => true
  | _ :: _, [] => false
  | first :: pattern, head :: input => first == head && bytePrefix pattern input

/-- Test whether the original String begins with the displayed String prefix.

Both complete valid UTF8 encodings are compared in order. This is the same
byte comparison used by the pinned String-pattern implementation, and an empty
prefix matches every input without constructing or slicing a UTF8 encoding. -/
public def startsWith (text pattern : _root_.String) : Bool :=
  bytePrefix pattern.toByteArray.data.toList text.toByteArray.data.toList

/-- Test whether the original String ends with the displayed String suffix.

Reverse byte comparison retains the same complete UTF8 encodings and scalar
suffix length. An empty suffix matches every input; a longer suffix cannot match.
No byte sequence is decoded or materialized as a potentially invalid String. -/
public def endsWith (text suffix : _root_.String) : Bool :=
  bytePrefix suffix.toByteArray.data.toList.reverse text.toByteArray.data.toList.reverse

/-- Match a separator at the same original Unicode-scalar cursor.

The input and separator cursors advance only through their original bootstrap
next operations after their end tests. The separator byte size bounds its scalar
steps, and success retains the actual input cursor immediately after the match. -/
private def matchSeparator (text separator : _root_.String) :
    Nat → _root_.String.Pos.Raw → _root_.String.Pos.Raw → Option _root_.String.Pos.Raw
  | 0, position, separatorPosition =>
      if _root_.String.Internal.atEnd separator separatorPosition then some position else none
  | fuel + 1, position, separatorPosition =>
      if _root_.String.Internal.atEnd separator separatorPosition then some position
      else if _root_.String.Internal.atEnd text position then none
      else if _root_.String.Internal.get text position ==
          _root_.String.Internal.get separator separatorPosition then
        matchSeparator text separator fuel
          (_root_.String.Internal.next text position)
          (_root_.String.Internal.next separator separatorPosition)
      else none

/-- Scan original scalar positions for first non-overlapping separator matches.

Start and current positions remain original code-point boundaries. Completed
pieces use bootstrap extraction between those positions, retaining empty pieces,
original order and the same tail after a complete separator match. -/
private def splitPieces (text separator : _root_.String) :
    Nat → _root_.String.Pos.Raw → _root_.String.Pos.Raw → List _root_.String →
      List _root_.String
  | 0, start, _, completed =>
      (_root_.String.Internal.extract text start ⟨text.utf8ByteSize⟩ :: completed).reverse
  | fuel + 1, start, position, completed =>
      if _root_.String.Internal.atEnd text position then
        (_root_.String.Internal.extract text start position :: completed).reverse
      else
        match matchSeparator text separator separator.utf8ByteSize position ⟨0⟩ with
        | some after => splitPieces text separator fuel after after
            (_root_.String.Internal.extract text start position :: completed)
        | none => splitPieces text separator fuel start
            (_root_.String.Internal.next text position) completed

/-- Split the original String on first non-overlapping String separators.

An empty separator retains the single original input. Nonempty separators are
matched at its original scalar boundaries; extraction retains empty leading,
trailing and adjacent pieces in the same order as the pinned splitOn operation. -/
public def splitOn (text : _root_.String) (separator : _root_.String := " ") :
    List _root_.String :=
  if separator.toByteArray.size == 0 then [text]
  else splitPieces text separator text.utf8ByteSize ⟨0⟩ ⟨0⟩ []

/-- Retain the first and last non-whitespace scalar boundaries of an original String.

The scan advances the original bootstrap cursor once per scalar. Its byte size
bounds the number of steps; four ASCII whitespace scalars leave the retained
start and end unchanged, while each other scalar advances the final boundary. -/
private def trimBounds (text : _root_.String) :
    Nat → _root_.String.Pos.Raw → Option _root_.String.Pos.Raw →
      _root_.String.Pos.Raw → _root_.String.Pos.Raw × _root_.String.Pos.Raw
  | 0, position, first, last =>
      match first with
      | none => (position, position)
      | some start => (start, last)
  | fuel + 1, position, first, last =>
      if _root_.String.Internal.atEnd text position then
        match first with
        | none => (position, position)
        | some start => (start, last)
      else
        let character := _root_.String.Internal.get text position
        let next := _root_.String.Internal.next text position
        if character == ' ' || character == '\t' ||
            character == '\r' || character == '\n' then
          trimBounds text fuel next first last
        else
          match first with
          | none => trimBounds text fuel next (some position) next
          | some start => trimBounds text fuel next (some start) next

/-- Remove leading and trailing ASCII whitespace from an original String.

Only space, tab, carriage return and newline are removed, matching the original
ASCII whitespace grammar. The original scalar boundaries delimit the retained
substring; empty or entirely whitespace inputs yield the original empty slice. -/
public def trimAscii (text : _root_.String) : _root_.String :=
  let bounds := trimBounds text text.utf8ByteSize ⟨0⟩ none ⟨0⟩
  _root_.String.Internal.extract text bounds.1 bounds.2

/-- Construct an original string from exactly certified finite UTF8 bytes.

Successful decoding retains the original byte array in the original String
constructor. Its proof field uses the retained character-list encoding equality;
failure returns none without an unchecked conversion or replacement character. -/
public def fromUTF8? (bytes : _root_.ByteArray) : Option _root_.String :=
  match UTF8.decode? bytes with
  | none => none
  | some decoded => some ⟨bytes, UTF8.valid decoded⟩

/-- A successful certified conversion retains every original input byte.

The returned original String stores the supplied byte array itself. Its decoded
character witness changes only the proof of validity, never the stored encoding. -/
public theorem fromUTF8?_toByteArray {bytes : _root_.ByteArray} {text : _root_.String}
    (retained : fromUTF8? bytes = some text) : text.toByteArray = bytes := by
  unfold fromUTF8? at retained
  cases decoded : UTF8.decode? bytes with
  | none =>
      rw [decoded] at retained
      cases retained
  | some witness =>
      rw [decoded] at retained
      exact congrArg _root_.String.toByteArray (Option.some.inj retained.symm)

open Purelib.Data.Nat in
/-- Lowercase the first ASCII uppercase character of an original String.

An empty input and every other first Unicode scalar retain the original input.
An uppercase ASCII letter is replaced by its corresponding lowercase scalar;
the original suffix is extracted from the same following scalar boundary. -/
public def decapitalize (text : _root_.String) : _root_.String :=
  if _root_.String.Internal.atEnd text ⟨0⟩ then text
  else
    let character := _root_.String.Internal.get text ⟨0⟩
    if bounds : 65 ≤ character.val.toNat ∧ character.val.toNat ≤ 90 then
      let lowered : Char := ⟨UInt32.ofNat (character.val.toNat + 32), Or.inl (by
        change (character.val.toNat + 32) % 4294967296 < 55296
        have small : character.val.toNat + 32 < 55296 := by omega0
        have bounded : character.val.toNat + 32 < 4294967296 := by omega0
        rw [Remainder.mod_eq_of_lt bounded]
        exact small)⟩
      let suffix := _root_.String.Internal.extract text
        (_root_.String.Internal.next text ⟨0⟩) ⟨text.utf8ByteSize⟩
      append (_root_.String.Internal.pushn "" lowered 1) suffix
    else text

/-- Join an ordered list of strings with one retained separator between entries.

The original first string initializes the accumulator. Each remaining string
appends the same separator and original entry, in order; an empty list returns
the original empty string without evaluating an append.
-/
@[expose] public def intercalate (separator : _root_.String) : List _root_.String → _root_.String
  | [] => ""
  | first :: remaining => go first separator remaining
where
  go (accumulator separator : _root_.String) : List _root_.String → _root_.String
    | first :: remaining => go (append (append accumulator separator) first) separator remaining
    | [] => accumulator

end Purelib.Data.String
