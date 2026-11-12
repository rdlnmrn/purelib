module

-- Kernel fixtures must reduce the original private byte-decision computation.
import all Purelib.Data.ByteArray.Basic
-- Kernel fixtures must reduce the retained decoder's private scalar/byte loops.
import all Purelib.Data.ByteArray.UTF8
-- Kernel fixtures must reduce the otherwise opaque certified String conversion.
import all Purelib.Data.String.Basic
import Purelib.System.IO

/-!
# Certified UTF8 byte boundaries

Independent finite byte lists specify accepted and malformed scalar sequences.
Positive fixtures check exact retained output bytes through the owned byte
comparison. Negative fixtures check failure without importing the old conversion,
a replacement character, or an original generic String equality instance.
-/

namespace TestPurelib.Data.ByteArray.UTF8

open Purelib

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
      match Data.ByteArray.decEq text.toByteArray bytes with
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

/-- Compare the original byte-list readbacks with their original natural-valued byte tests.

This retained reference measures the former native allocation path. It is a
benchmark observation only; the production decision retains its own equality
certificate and complete original kernel definition. -/
private def listReference : List UInt8 → List UInt8 → Bool
  | [], [] => true
  | first :: left, second :: right =>
      match _root_.decEq first.toNat second.toNat with
      | .isFalse _ => false
      | .isTrue _ => listReference left right
  | _, _ => false

/-- Force the original owned byte decision through an opaque IO timing boundary. -/
@[noinline] private def originalDecision (left right : _root_.ByteArray) : IO Bool :=
  pure (match Data.ByteArray.decEq left right with
    | .isTrue _ => true
    | .isFalse _ => false)

/-- Force the former byte-list allocation path through the same IO timing boundary. -/
@[noinline] private def referenceDecision (left right : _root_.ByteArray) : IO Bool :=
  pure (listReference left.data.toList right.data.toList)

/-- Read the original validity decision's constructor through an opaque IO boundary. -/
@[noinline] private def originalValidity (bytes : _root_.ByteArray) : IO Bool :=
  pure (match Data.ByteArray.UTF8.decValid bytes with
    | .isTrue _ => true
    | .isFalse _ => false)

/-- Force the complete certified UTF8 conversion through an opaque IO timing boundary. -/
@[noinline] private def certifiedDecode (bytes : _root_.ByteArray) : IO (Option String) :=
  pure (fromUTF8? bytes)

/-- Measure a fully evaluated IO result using the original monotonic clock. -/
private def timed {α : Type} (action : IO α) : IO (α × Nat) := do
  let start ← IO.monoNanosNow
  let result ← action
  return (result, (← IO.monoNanosNow) - start)

/-- Check native byte decisions and certified scalar boundaries against independent finite inputs.

Every byte value is compared on separately materialized arrays. Fixed unequal
lengths and first, interior and last mismatches exercise negative decisions;
one-byte inputs check the ASCII bound, and every two-byte input compares the
native validity result with the retained structural decoder. Scalar boundary
fixtures preserve the exact accepted and malformed UTF8 byte contract. -/
public def check : IO Unit := do
  for value in List.range 256 do
    let left := materialize [value]
    unless (← originalDecision left (materialize [value])) do
      throw (IO.userError "owned native byte comparison rejected an equal byte")
    if (← originalDecision left (materialize [(value + 1) % 256])) then
      throw (IO.userError "owned native byte comparison accepted a changed byte")
    unless (← originalValidity left) == decide (value < 128) do
      throw (IO.userError "owned native UTF8 validity changed a one-byte decision")
  for value in List.range 65536 do
    let bytes := materialize [value / 256, value % 256]
    unless (← originalValidity bytes) == (Data.ByteArray.UTF8.decode? bytes).isSome do
      throw (IO.userError "owned native UTF8 validity disagreed with the original two-byte decoder")
  let pairs : List (List Nat × List Nat × Bool) :=
    [([], [], true), ([0], [], false), ([], [0], false), ([0, 0], [0], false),
      ([0, 255, 127], [0, 255, 127], true), ([0, 255, 127], [1, 255, 127], false),
      ([0, 255, 127], [0, 254, 127], false), ([0, 255, 127], [0, 255, 126], false)]
  for (left, right, expected) in pairs do
    unless (← originalDecision (materialize left) (materialize right)) == expected do
      throw (IO.userError "owned native byte comparison changed an independent boundary fixture")
  let valid := [[], [0, 65, 127], [0xc2, 0x80], [0xdf, 0xbf], [0xe0, 0xa0, 0x80],
    [0xed, 0x9f, 0xbf], [0xee, 0x80, 0x80], [0xef, 0xbf, 0xbf],
    [0xf0, 0x90, 0x80, 0x80], [0xf4, 0x8f, 0xbf, 0xbf],
    [65, 0xc2, 0x80, 0xe0, 0xa0, 0x80, 0xf4, 0x8f, 0xbf, 0xbf, 0]]
  for input in valid do
    unless accepted input do throw (IO.userError "owned native UTF8 conversion changed valid original bytes")
  let invalid := [[0x80], [0xc1, 0xbf], [0xe0, 0x9f, 0xbf], [0xed, 0xa0, 0x80], [0xed, 0xbf, 0xbf],
    [0xf0, 0x8f, 0xbf, 0xbf], [0xf4, 0x90, 0x80, 0x80], [0xff], [0xc2], [0xe0, 0xa0], [0xf0, 0x90, 0x80],
    [0xc2, 65], [0xe0, 0xa0, 65], [0xf0, 0x90, 0x80, 65], [65, 0xff, 66]]
  for input in invalid do
    unless rejected input do throw (IO.userError "owned native UTF8 conversion accepted malformed original bytes")
  Purelib.System.IO.println "owned native byte decisions and exact UTF8 boundaries passed"

/-- Compare the actual retained file bytes and time their complete certified UTF8 conversion.

Two independent binary reads provide equal packed arrays without a shared
pointer shortcut. Both byte-comparison orders are measured, and every result
and decoded byte record is checked outside its timed interval. -/
public def profile (path : System.FilePath) : IO Unit := do
  let left ← IO.FS.readBinFile path
  let right ← IO.FS.readBinFile path
  unless left.size = right.size do throw (IO.userError "retained file changed between independent reads")
  for round in List.range 3 do
    let (productionFirst, firstTime) ← timed (originalDecision left right)
    let (referenceLast, referenceTime) ← timed (referenceDecision left right)
    let (referenceFirst, reverseReferenceTime) ← timed (referenceDecision right left)
    let (productionLast, reverseTime) ← timed (originalDecision right left)
    unless productionFirst && referenceLast && referenceFirst && productionLast do
      throw (IO.userError "retained original byte comparisons disagreed")
    let (decoded, decodeTime) ← timed (certifiedDecode left)
    let some text := decoded | throw (IO.userError "retained original file has invalid UTF8")
    unless (← originalDecision text.toByteArray left) do
      throw (IO.userError "certified conversion changed the retained original file bytes")
    Purelib.System.IO.println s!"byte-array-profile: round {round}; bytes {left.size}; \
      production_ns {firstTime}; reference_ns {referenceTime}; \
      reverse_reference_ns {reverseReferenceTime}; reverse_production_ns {reverseTime}; \
      certified_decode_ns {decodeTime}; all_original_bytes_agree"

end TestPurelib.Data.ByteArray.UTF8
