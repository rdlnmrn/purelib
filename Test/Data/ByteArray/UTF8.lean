module

-- Kernel fixtures must reduce the original private byte-decision computation.
import all Purelib.Data.ByteArray.Basic
-- Kernel fixtures must reduce the retained decoder's private scalar/byte loops.
import all Purelib.Data.ByteArray.UTF8
-- Kernel fixtures must reduce the otherwise opaque certified String conversion.
import all Purelib.Data.String.Basic

/-!
# Certified UTF8 byte boundaries

Independent finite byte lists specify accepted and malformed scalar sequences.
Positive fixtures check exact retained output bytes through the owned byte
comparison. Negative fixtures check failure without importing the old conversion,
a replacement character, or an original generic String equality instance.
-/

namespace Test.Data.ByteArray.UTF8

open Purelib.Data.String (fromUTF8?)

/-- Materialize a displayed finite byte corpus in the original byte-array carrier.

The input numerals are the specified encoded bytes, in their displayed order.
The original UInt8 constructor and list materializer retain that finite data. -/
private def materialize (bytes : List Nat) : _root_.ByteArray :=
  (bytes.map UInt8.ofNat).toByteArray

/-- Recognize successful certified conversion with exact retained input bytes.

A positive result checks the returned original String's stored byte array against
the supplied byte array. Failure and changed bytes both return false; this Bool
is an internal regression observation rather than a public checking contract. -/
private def accepted (input : List Nat) : Bool :=
  let bytes := materialize input
  match fromUTF8? bytes with
  | none => false
  | some text =>
      match Purelib.Data.ByteArray.decEq text.toByteArray bytes with
      | .isTrue _ => true
      | .isFalse _ => false

/-- Recognize failure of the certified conversion on the complete original input.

Only the none constructor yields true. A successful result remains a regression
failure regardless of its retained character data or byte-array readback. -/
private def rejected (input : List Nat) : Bool :=
  match fromUTF8? (materialize input) with
  | none => true
  | some _ => false

/-- The empty encoding succeeds with its exact original byte array.

No scalar or byte is added to the original empty input. -/
private theorem empty : accepted [] = true := by decide

/-- ASCII and embedded NUL retain every original control byte.

The displayed minimum, ordinary and maximum ASCII values all use one byte. -/
private theorem ascii_controls : accepted [0, 65, 127] = true := by decide

/-- The minimal two-byte scalar retains its exact original encoding.

The C2 leading-byte boundary excludes shorter overlong sequences. -/
private theorem two_minimum : accepted [0xc2, 0x80] = true := by decide

/-- The maximal two-byte scalar retains its exact original encoding.

Both retained bytes occupy the upper end of their accepted ranges. -/
private theorem two_maximum : accepted [0xdf, 0xbf] = true := by decide

/-- The minimal three-byte scalar retains its exact original encoding.

The E0 second-byte lower bound excludes every shorter overlong scalar. -/
private theorem three_minimum : accepted [0xe0, 0xa0, 0x80] = true := by decide

/-- The last scalar before the surrogate range retains its exact bytes.

The ED second-byte upper bound permits this original Unicode scalar. -/
private theorem before_surrogates : accepted [0xed, 0x9f, 0xbf] = true := by decide

/-- The first scalar after the surrogate range retains its exact bytes.

The original EE sequence lies beyond the excluded surrogate interval. -/
private theorem after_surrogates : accepted [0xee, 0x80, 0x80] = true := by decide

/-- The maximal three-byte scalar retains its exact original encoding.

All three retained bytes remain in their accepted branch ranges. -/
private theorem three_maximum : accepted [0xef, 0xbf, 0xbf] = true := by decide

/-- The minimal four-byte scalar retains its exact original encoding.

The F0 second-byte lower bound excludes every shorter overlong scalar. -/
private theorem four_minimum : accepted [0xf0, 0x90, 0x80, 0x80] = true := by decide

/-- The maximal Unicode scalar retains its exact four original bytes.

The F4 second-byte upper bound accepts U+10FFFF and excludes larger values. -/
private theorem four_maximum : accepted [0xf4, 0x8f, 0xbf, 0xbf] = true := by decide

/-- Mixed scalar widths retain their exact original consecutive bytes.

The decoder passes the actual remaining input from one scalar branch to the next. -/
private theorem mixed_widths : accepted [65, 0xc2, 0x80, 0xe0, 0xa0, 0x80, 0xf4, 0x8f, 0xbf, 0xbf, 0] = true := by
  decide

/-- A stray continuation byte fails certified conversion.

The initial byte does not identify any original UTF8 scalar sequence. -/
private theorem stray_continuation : rejected [0x80] = true := by decide

/-- An overlong two-byte sequence fails certified conversion.

The C1 leading byte lies below the accepted C2 two-byte boundary. -/
private theorem overlong_two : rejected [0xc1, 0xbf] = true := by decide

/-- An overlong three-byte sequence fails certified conversion.

The E0 second byte lies below its accepted A0 boundary. -/
private theorem overlong_three : rejected [0xe0, 0x9f, 0xbf] = true := by decide

/-- The minimal encoded surrogate fails certified conversion.

The ED second byte violates the scalar branch upper bound. -/
private theorem surrogate_minimum : rejected [0xed, 0xa0, 0x80] = true := by decide

/-- The maximal encoded surrogate fails certified conversion.

The entire original UTF16 surrogate interval is excluded from Unicode scalars. -/
private theorem surrogate_maximum : rejected [0xed, 0xbf, 0xbf] = true := by decide

/-- An overlong four-byte sequence fails certified conversion.

The F0 second byte lies below the accepted 90 boundary. -/
private theorem overlong_four : rejected [0xf0, 0x8f, 0xbf, 0xbf] = true := by decide

/-- The first value above U+10FFFF fails certified conversion.

The F4 second byte exceeds the accepted Unicode maximum boundary. -/
private theorem above_maximum : rejected [0xf4, 0x90, 0x80, 0x80] = true := by decide

/-- An invalid leading byte fails certified conversion.

The FF byte belongs to no accepted original Unicode encoding branch. -/
private theorem invalid_leading : rejected [0xff] = true := by decide

/-- A truncated two-byte scalar fails certified conversion.

The original tail does not supply the required continuation byte. -/
private theorem two_truncated : rejected [0xc2] = true := by decide

/-- A truncated three-byte scalar fails certified conversion.

The original tail lacks its third byte after the accepted first two. -/
private theorem three_truncated : rejected [0xe0, 0xa0] = true := by decide

/-- A truncated four-byte scalar fails certified conversion.

The original tail lacks its final continuation byte. -/
private theorem four_truncated : rejected [0xf0, 0x90, 0x80] = true := by decide

/-- An ASCII second byte fails a two-byte scalar branch.

The supplied original tail violates the continuation-byte range. -/
private theorem bad_second : rejected [0xc2, 65] = true := by decide

/-- An ASCII third byte fails a three-byte scalar branch.

Earlier accepted bytes do not mask the invalid retained third byte. -/
private theorem bad_third : rejected [0xe0, 0xa0, 65] = true := by decide

/-- An ASCII fourth byte fails a four-byte scalar branch.

The final retained byte must satisfy the original continuation range. -/
private theorem bad_fourth : rejected [0xf0, 0x90, 0x80, 65] = true := by decide

/-- An invalid interior byte fails the complete certified conversion.

The preceding ASCII scalar does not discard or replace the invalid remaining input. -/
private theorem invalid_interior : rejected [65, 0xff, 66] = true := by decide

end Test.Data.ByteArray.UTF8
