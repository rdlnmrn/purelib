module

import Purelib.Data.String.Basic
import Purelib.Data.Char.Presentation
import Purelib.Data.UInt32.Presentation
import Purelib.Data.UInt8.Presentation
import Purelib.System.IO
meta import Purelib.Data.Char.Presentation
meta import Purelib.Data.UInt32.Presentation
meta import Purelib.Data.UInt8.Presentation

/-!
# Retained string concatenation and Unicode scalar counts

Literal results specify the original bytes independently of the append
certificate. The checks cover empty inputs, ASCII, controls and multibyte
UTF8, including selection of the owned scoped instance.
-/

namespace TestPurelib.Data.String

open Purelib.Data.String (append length length_of_utf8_encoding)

namespace ScalarPresentation

open Purelib.Data.Char.Presentation
open Purelib.Data.Char

private def ascii : Display := ⟨65, .inl (by decide)⟩

private def nul : Display := ⟨0, .inl (by decide)⟩

example (character : _root_.Char) : read (quote character) = character := read_quote character

example (display : Display) : quote (read display) = display := quote_read display

example (first second : Display) : Same first second ↔ read first = read second :=
  same_iff_read_eq first second

example (first second : Valid 65) : read ⟨65, first⟩ = read ⟨65, second⟩ := rfl

/-- Distinguish the three typed recognition outcomes for bounded regressions. -/
private def result (code : Nat) : Nat :=
  match check code with
  | .valid _ => 0
  | .surrogate _ _ => 1
  | .outOfRange _ => 2

/-- info: (0, 0, 1, 1, 0, 0, 2, 2) -/
#guard_msgs in
#eval (result 0, result 0xd7ff, result 0xd800, result 0xdfff,
  result 0xe000, result 0x10ffff, result 0x110000, result 0x100000000)

/-- info: (true, true, 0, 65) -/
#guard_msgs in
#eval ((match Presentation.compare ascii ascii with | .isTrue _ => true | .isFalse _ => false),
  (match Presentation.compare ascii nul with | .isTrue _ => false | .isFalse _ => true),
  (_root_.Char.ofNat 0xd800).toNat, (read ascii).toNat)

end ScalarPresentation

namespace UInt32Presentation

open Purelib.Data.UInt32.Presentation
open Purelib.Data.UInt32

private def zero : Display := ⟨0, by change 0 < _root_.UInt32.size; decide⟩

private def letter : Display := ⟨65, by change 65 < _root_.UInt32.size; decide⟩

example (value : _root_.UInt32) : read (quote value) = value := read_quote value

example (display : Display) : quote (read display) = display := quote_read display

example (first second : Display) : Same first second ↔ read first = read second :=
  same_iff_read_eq first second

example (first second : Valid 65) : read ⟨65, first⟩ = read ⟨65, second⟩ := rfl

/-- Distinguish acceptance from the proved out-of-range result. -/
private def accepted (code : Nat) : Bool :=
  match check code with
  | .valid _ => true
  | .outOfRange _ => false

/-- info: (true, true, false, false) -/
#guard_msgs in
#eval (accepted 0, accepted 0xffffffff, accepted 0x100000000, accepted 0x100000001)

/-- info: (true, true, 65, 0) -/
#guard_msgs in
#eval ((match Presentation.compare zero zero with | .isTrue _ => true | .isFalse _ => false),
  (match Presentation.compare zero letter with | .isTrue _ => false | .isFalse _ => true),
  (read letter).toNat, (_root_.UInt32.ofNat 0x100000000).toNat)

end UInt32Presentation

namespace UInt8Presentation

open Purelib.Data.UInt8.Presentation
open Purelib.Data.UInt8

private def zero : Display := ⟨0, by change 0 < _root_.UInt8.size; decide⟩

private def letter : Display := ⟨65, by change 65 < _root_.UInt8.size; decide⟩

example (value : _root_.UInt8) : read (quote value) = value := read_quote value

example (display : Display) : quote (read display) = display := quote_read display

example (first second : Display) : Same first second ↔ read first = read second :=
  same_iff_read_eq first second

example (first second : Valid 65) : read ⟨65, first⟩ = read ⟨65, second⟩ := rfl

/-- Distinguish acceptance from the proved out-of-range result. -/
private def accepted (code : Nat) : Bool :=
  match check code with
  | .valid _ => true
  | .outOfRange _ => false

/-- info: (true, true, false, false) -/
#guard_msgs in
#eval (accepted 0, accepted 0xff, accepted 0x100, accepted 0x101)

/-- info: (true, true, 65, 0) -/
#guard_msgs in
#eval ((match Presentation.compare zero zero with | .isTrue _ => true | .isFalse _ => false),
  (match Presentation.compare zero letter with | .isTrue _ => false | .isFalse _ => true),
  (read letter).toNat, (_root_.UInt8.ofNat 0x100).toNat)

end UInt8Presentation

/-- An empty left input retains the original right string.

The complete string record reduces to the displayed literal, including its
original byte-array data. -/
private theorem empty_left : append "" "checkpoint" = "checkpoint" := rfl

/-- An empty right input retains the original left string.

The complete string record reduces to the displayed literal without adding
any bytes. -/
private theorem empty_right : append "checkpoint" "" = "checkpoint" := rfl

/-- Concatenation preserves the original ASCII path bytes in order.

The two input literals supply the path prefix and retained checkpoint name;
the result keeps their exact consecutive byte sequence. -/
private theorem ascii_bytes :
    append "attempt/" "manifest.json" = "attempt/manifest.json" := rfl

/-- Control bytes remain literal string data during concatenation.

Tabs, line endings, quotes and backslashes retain their exact byte sequence
before any separate JSON escaping operation. -/
private theorem controls : append "\t\n" "\r\"\\" = "\t\n\r\"\\" := rfl

/-- Non-ASCII scalars retain their original multibyte encodings.

The displayed Latin, Greek and supplementary-plane characters concatenate
as their original consecutive UTF8 byte sequences. -/
private theorem unicode_bytes : append "éδ" "🙂" = "éδ🙂" := rfl

open scoped Purelib.Data.String in
/-- The scoped append instance retains the same multibyte string data.

Instance selection uses the owned concatenation operation, and its complete
result reduces to the independently specified literal. -/
private theorem scoped_append : "éδ" ++ "🙂" = "éδ🙂" := rfl

/-- Every original character encoding has its original finite scalar count.

The quantified input retains the original String constructor and its own UTF8
encoding witness. No concrete runtime corpus replaces this all-input readback. -/
private theorem encoded_length (characters : List Char) :
    length (⟨characters.utf8Encode, .intro characters rfl⟩ : _root_.String) =
      characters.length :=
  length_of_utf8_encoding _ characters rfl

/-- Mixed one-, two-, three- and four-byte scalars count once each.

The original encoded byte array has ten bytes, while its four original Unicode
scalars give the displayed count. -/
private theorem mixed_length : length "aé中🙂" = 4 :=
  length_of_utf8_encoding _ ['a', 'é', '中', '🙂'] rfl

/-- A combining mark retains its own scalar occurrence in the original count.

The base character and following combining accent are two Unicode scalars even
though they can be displayed as one glyph. -/
private theorem combining_length : length "e\u0301" = 2 :=
  length_of_utf8_encoding _ ['e', '\u0301'] rfl

/-- Embedded NUL and ASCII controls remain individual original characters.

No terminator convention removes their retained Unicode scalar occurrences. -/
private theorem control_length : length "\x00\t\n\r" = 4 :=
  length_of_utf8_encoding _ ['\x00', '\t', '\n', '\r'] rfl

/-- Check the owned character count on original mixed-width and control strings.

Independent literal counts exercise native certified decoding for empty, ASCII,
multibyte, supplementary-plane, combining-mark and embedded-NUL inputs. -/
public def checkLength : IO Unit := do
  let cases : List (_root_.String × Nat) :=
    [("", 0), ("checkpoint", 10), ("é", 1), ("中", 1), ("🙂", 1),
      ("aé中🙂", 4), ("e\u0301", 2), ("\x00\t\n\r", 4),
      ("\u0080\u07ff\u0800\uffff", 4)]
  for (text, expected) in cases do
    unless length text == expected do
      throw (IO.userError "owned original UTF8 scalar length disagrees with its literal count")
  Purelib.System.IO.println "owned UTF8 scalar lengths: ASCII, mixed widths, combining mark and NUL checked"

end TestPurelib.Data.String
