module

public import Init.Data.String.Defs
import Purelib.Data.ByteArray.Basic
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Reverse
import Purelib.Data.Nat.Remainder
import Purelib.Data.Nat.Division
import Purelib.Tactic.QuotientFreeOmega

/-!
# UTF8 concatenation and certified decoding

Concatenation retains the original character-list witnesses and appended bytes.
The finite decoder consumes original byte tails with a retained reverse scalar
accumulator and certifies their exact original character-list encoding.
-/

namespace Purelib.Data.ByteArray.UTF8

open Purelib.Data.List
open Purelib.Data.Nat

/-- UTF8 encoding of concatenated character lists appends their encoded bytes.

The original per-character encoder supplies the byte fibers. The owned flat-map
composition law on two retained lists and byte materialization preserve all fibers. -/
public theorem utf8Encode_append (left right : List Char) :
    (left ++ right).utf8Encode = left.utf8Encode ++ right.utf8Encode := by
  have fibers := Flatten.flatMap_assoc_direct
    (fun (characters : List Char) => characters) _root_.String.utf8EncodeChar [left, right]
  change (left ++ (right ++ [])).flatMap _root_.String.utf8EncodeChar =
    left.flatMap _root_.String.utf8EncodeChar ++
      (right.flatMap _root_.String.utf8EncodeChar ++ []) at fibers
  rw [Append.append_nil right,
    Append.append_nil (right.flatMap _root_.String.utf8EncodeChar)] at fibers
  change ((left ++ right).flatMap _root_.String.utf8EncodeChar).toByteArray =
    (left.flatMap _root_.String.utf8EncodeChar).toByteArray ++
      (right.flatMap _root_.String.utf8EncodeChar).toByteArray
  rw [fibers]
  exact Purelib.Data.ByteArray.toByteArray_append
    (left.flatMap _root_.String.utf8EncodeChar)
    (right.flatMap _root_.String.utf8EncodeChar)

/-- Appending two retained valid UTF8 byte arrays retains UTF8 validity.

The two original validity witnesses display character lists with the retained
encodings. Their concatenation witnesses the same original byte-array append. -/
public theorem append {left right : _root_.ByteArray}
    (leftValid : left.IsValidUTF8) (rightValid : right.IsValidUTF8) :
    (left ++ right).IsValidUTF8 := by
  cases leftValid with
  | intro leftCharacters leftEquation =>
      cases rightValid with
      | intro rightCharacters rightEquation =>
          refine .intro (leftCharacters ++ rightCharacters) ?_
          calc
            left ++ right = leftCharacters.utf8Encode ++ rightCharacters.utf8Encode :=
              congrArg₂ (fun a b : _root_.ByteArray => a ++ b) leftEquation rightEquation
            _ = (leftCharacters ++ rightCharacters).utf8Encode :=
              (utf8Encode_append leftCharacters rightCharacters).symm

/-- A bounded byte constructor retains its original natural value.

No wrap occurs below the original UInt8 range; the original modulo operation
reduces to its supplied bounded dividend. -/
private theorem byte_value {value : Nat} (bound : value < 256) :
    (UInt8.ofNat value).toNat = value := by
  change value % 256 = value
  exact Remainder.mod_eq_of_lt bound

/-- A bounded scalar constructor retains its original natural value.

No wrap occurs below the original UInt32 range. The comparison concerns the
original value and original constructor rather than a replacement scalar type. -/
private theorem scalar_value {value : Nat} (bound : value < 4294967296) :
    (UInt32.ofNat value).toNat = value := by
  change value % 4294967296 = value
  exact Remainder.mod_eq_of_lt bound

/-- The original UInt32 record is determined by its retained natural value.

Direct transport of its UInt32, BitVec and Fin layers preserves all fields;
only the correctness-bearing bound proof is propositionally irrelevant. -/
private theorem scalar_eq {left right : UInt32} (same : left.toNat = right.toNat) :
    left = right := by
  cases left with
  | ofBitVec left =>
      cases right with
      | ofBitVec right =>
          cases left with
          | ofFin left =>
              cases right with
              | ofFin right =>
                  cases left with
                  | mk left leftBound =>
                      cases right with
                      | mk right rightBound =>
                          change left = right at same
                          cases same
                          rfl

/-- Repacking an original Unicode scalar retains its original UInt32 value.

The original character's finite bound rules out overflow in UInt32.ofNat.
The result is equality of the complete original scalar record. -/
private theorem repack_scalar (character : Char) :
    UInt32.ofNat character.toNat = character.val := by
  apply scalar_eq
  exact scalar_value character.val.toBitVec.toFin.isLt

/-- Check a scalar before constructing its original character proof field.

The predicate is the original UInt32 Unicode-scalar predicate. Invalid values
produce no character and never use a replacement scalar. -/
private def scalar? (value : Nat) : Option Char :=
  let scalar := UInt32.ofNat value
  if valid : scalar.isValidChar then some ⟨scalar, valid⟩ else none

/-- Checking an original character value returns that same complete character.

The original scalar bound ensures repacking is exact, and its retained validity
proof supplies the successful check without selecting another witness. -/
private theorem repack_character (character : Char) :
    scalar? character.toNat = some character := by
  unfold scalar?
  rw [repack_scalar character, dif_pos character.valid]

/-- Two retained base-64 digit values reconstruct a bounded scalar.

The quotient and remainder are supplied scalar observations with their exact
reconstruction equation. No division expression is reinterpreted by this proof. -/
private theorem two_linear {value quotient remainder : Nat}
    (bound : value < 2048) (retained : remainder + 64 * quotient = value) :
    quotient < 32 ∧ quotient * 64 + remainder = value := by
  constructor <;> omega0

/-- Three retained digit observations reconstruct their bounded scalar.

The displayed quotient and remainder equations relate the original successive
base-64 readings. Their scalar bounds identify the same highest digit. -/
private theorem three_linear {value lowQuotient lowRemainder middleQuotient
    middleRemainder highQuotient highRemainder : Nat}
    (bound : value < 65536)
    (low : lowRemainder + 64 * lowQuotient = value)
    (middle : middleRemainder + 64 * middleQuotient = lowQuotient)
    (high : highRemainder + 4096 * highQuotient = value)
    (lowBound : lowRemainder < 64) (middleBound : middleRemainder < 64)
    (highBound : highRemainder < 4096) :
    highQuotient < 16 ∧ highQuotient * 4096 + middleRemainder * 64 + lowRemainder = value := by
  constructor <;> omega0

/-- Four retained digit observations reconstruct their bounded scalar.

All original low, middle and highest quotient/remainder readings occur with
explicit reconstruction equations and bounds. These identify their common
base-64 hierarchy without adding a second division procedure. -/
private theorem four_linear {value lowQuotient lowRemainder middleQuotient
    middleRemainder highQuotient highRemainder highMiddleQuotient highMiddleRemainder
    topQuotient topRemainder : Nat}
    (bound : value < 0x110000)
    (low : lowRemainder + 64 * lowQuotient = value)
    (middle : middleRemainder + 64 * middleQuotient = lowQuotient)
    (high : highRemainder + 4096 * highQuotient = value)
    (highMiddle : highMiddleRemainder + 64 * highMiddleQuotient = highQuotient)
    (top : topRemainder + 262144 * topQuotient = value)
    (lowBound : lowRemainder < 64) (middleBound : middleRemainder < 64)
    (highBound : highRemainder < 4096) (highMiddleBound : highMiddleRemainder < 64)
    (topBound : topRemainder < 262144) :
    topQuotient < 8 ∧ topQuotient * 262144 + highMiddleRemainder * 4096 +
      middleRemainder * 64 + lowRemainder = value := by
  constructor <;> omega0

/-- The original quotient gives the high digit of a two-byte scalar.

For values below 2048 the base-64 quotient fits in the original five-bit high
digit. The original remainder equation reconstructs the complete scalar. -/
private theorem two_byte_digits {value : Nat} (bound : value < 2048) :
    (value / 64) % 32 * 64 + value % 64 = value := by
  have retained := two_linear bound (Division.mod_add_div value 64)
  rw [Remainder.mod_eq_of_lt retained.1]
  exact retained.2

/-- Three original base-64 digits reconstruct a scalar below 65536.

The retained quotient and remainder identities cover both low digits. Their
bounds show that the high quotient fits the encoder's four-bit high digit. -/
private theorem three_byte_digits {value : Nat} (bound : value < 65536) :
    (value / 4096) % 16 * 4096 +
      (value / 64) % 64 * 64 + value % 64 = value := by
  have retained := three_linear bound
    (Division.mod_add_div value 64) (Division.mod_add_div (value / 64) 64)
    (Division.mod_add_div value 4096)
    (Nat.mod_lt value (show 0 < 64 from by decide))
    (Nat.mod_lt (value / 64) (show 0 < 64 from by decide))
    (Nat.mod_lt value (show 0 < 4096 from by decide))
  rw [Remainder.mod_eq_of_lt retained.1]
  exact retained.2

/-- Four original base-64 digits reconstruct a scalar below U+110000.

The retained original division equations distinguish each finite base-64 digit.
The leading quotient fits the original encoder's three-bit high digit. -/
private theorem four_byte_digits {value : Nat} (bound : value < 0x110000) :
    (value / 262144) % 8 * 262144 +
      (value / 4096) % 64 * 4096 +
      (value / 64) % 64 * 64 + value % 64 = value := by
  have retained := four_linear bound
    (Division.mod_add_div value 64) (Division.mod_add_div (value / 64) 64)
    (Division.mod_add_div value 4096) (Division.mod_add_div (value / 4096) 64)
    (Division.mod_add_div value 262144)
    (Nat.mod_lt value (show 0 < 64 from by decide))
    (Nat.mod_lt (value / 64) (show 0 < 64 from by decide))
    (Nat.mod_lt value (show 0 < 4096 from by decide))
    (Nat.mod_lt (value / 4096) (show 0 < 64 from by decide))
    (Nat.mod_lt value (show 0 < 262144 from by decide))
  rw [Remainder.mod_eq_of_lt retained.1]
  exact retained.2

/-- Recognize one continuation byte in the original UTF8 representation. -/
private abbrev continuation (byte : UInt8) : Prop :=
  0x80 ≤ byte.toNat ∧ byte.toNat ≤ 0xBF

/-- Decode the original finite byte list into candidate Unicode scalar values.

Each successful step consumes exactly one original UTF8 sequence and retains
its scalar in the original reverse accumulator. The final original reversal
returns those same scalars in their input order. The leading
and continuation ranges reject overlong encodings, surrogates and values above
U+10FFFF; truncated sequences retain failure rather than replacement characters. -/
private def decodeLoop : List UInt8 → List Char → Option (List Char)
  | [], retained => some retained.reverse
  | first :: rest, retained =>
      let leading := first.toNat
      if leading < 0x80 then do
        let character ← scalar? leading
        decodeLoop rest (character :: retained)
      else if leading < 0xC2 then none
      else match rest with
      | [] => none
      | second :: tail =>
          let next := second.toNat
          if leading ≤ 0xDF then
            if continuation second then do
              let character ← scalar? ((leading - 0xC0) * 64 + (next - 0x80))
              decodeLoop tail (character :: retained)
            else none
          else match tail with
          | [] => none
          | third :: tail =>
              let nextNext := third.toNat
              if leading ≤ 0xEF then
                let lower := if leading = 0xE0 then 0xA0 else 0x80
                let upper := if leading = 0xED then 0x9F else 0xBF
                if lower ≤ next ∧ next ≤ upper ∧ continuation third then do
                  let character ← scalar?
                    ((leading - 0xE0) * 4096 + (next - 0x80) * 64 + (nextNext - 0x80))
                  decodeLoop tail (character :: retained)
                else none
              else if leading ≤ 0xF4 then
                match tail with
                | [] => none
                | fourth :: tail =>
                    let lower := if leading = 0xF0 then 0x90 else 0x80
                    let upper := if leading = 0xF4 then 0x8F else 0xBF
                    if lower ≤ next ∧ next ≤ upper ∧
                        continuation third ∧ continuation fourth then do
                      let character ← scalar? ((leading - 0xF0) * 262144 +
                        (next - 0x80) * 4096 + (nextNext - 0x80) * 64 +
                        (fourth.toNat - 0x80))
                      decodeLoop tail (character :: retained)
                    else none
              else none

/-- Decoding the original ASCII encoding returns the original character.

A successful step transfers the scalar into the supplied reverse accumulator.
The byte suffix and that same extended accumulator are retained by the recursive
call; only the original one-byte fiber is consumed by this equation. -/
private theorem decodeLoop_ascii (character : Char) (ascii : character.toNat ≤ 0x7F)
    (retained : List Char) (suffix : List UInt8) :
    decodeLoop (_root_.String.utf8EncodeChar character ++ suffix) retained =
      decodeLoop suffix (character :: retained) := by
  have byteBound : character.toNat < 256 := by omega0
  have leadingBound : character.toNat < 0x80 := by omega0
  change character.val.toNat ≤ 0x7F at ascii
  rw [_root_.String.utf8EncodeChar, if_pos ascii]
  change decodeLoop (UInt8.ofNat character.toNat :: suffix) retained =
    decodeLoop suffix (character :: retained)
  conv => lhs; unfold decodeLoop
  dsimp only
  rw [byte_value byteBound, if_pos leadingBound, repack_character]
  rfl

/-- Decoding an original two-byte UTF8 fiber retains its original character.

The original quotient and remainder supply both finite byte values and their
bounds. Decoding consumes that fiber once before retaining the original suffix. -/
private theorem decodeLoop_two (character : Char)
    (notAscii : ¬ character.toNat ≤ 0x7F) (small : character.toNat ≤ 0x7FF)
    (retained : List Char) (suffix : List UInt8) :
    decodeLoop (_root_.String.utf8EncodeChar character ++ suffix) retained =
      decodeLoop suffix (character :: retained) := by
  let value := character.toNat
  let first := (value / 64) % 32 + 0xC0
  let second := value % 64 + 0x80
  have reconstruction := Division.mod_add_div value 64
  have quotientBound : value / 64 < 32 := by omega0
  have quotientReduced := Remainder.mod_eq_of_lt quotientBound
  have lowBound := Nat.mod_lt value (show 0 < 64 from by decide)
  have firstBound : first < 256 := by omega0
  have secondBound : second < 256 := by omega0
  have notFirstAscii : ¬ first < 0x80 := by omega0
  have notFirstInvalid : ¬ first < 0xC2 := by omega0
  have firstSmall : first ≤ 0xDF := by omega0
  have secondContinuation : continuation (UInt8.ofNat second) := by
    change 0x80 ≤ (UInt8.ofNat second).toNat ∧ (UInt8.ofNat second).toNat ≤ 0xBF
    rw [byte_value secondBound]
    constructor <;> omega0
  have scalarIdentity : (first - 0xC0) * 64 + (second - 0x80) = value := by
    have digits := two_byte_digits (show value < 2048 from by omega0)
    omega0
  change ¬ character.val.toNat ≤ 0x7F at notAscii
  change character.val.toNat ≤ 0x7FF at small
  rw [_root_.String.utf8EncodeChar, if_neg notAscii, if_pos small]
  change decodeLoop (UInt8.ofNat first :: UInt8.ofNat second :: suffix) retained =
    decodeLoop suffix (character :: retained)
  conv => lhs; unfold decodeLoop
  dsimp only
  rw [byte_value firstBound, if_neg notFirstAscii,
    if_neg notFirstInvalid]
  rw [if_pos firstSmall, if_pos secondContinuation,
    byte_value secondBound, scalarIdentity, repack_character]
  rfl

/-- Decoding an original three-byte UTF8 fiber retains its original character.

The original scalar validity excludes surrogate values. Together with the
quotient and remainder bounds it supplies the exact E0 and ED second-byte ranges. -/
private theorem decodeLoop_three (character : Char)
    (notAscii : ¬ character.toNat ≤ 0x7F) (notTwo : ¬ character.toNat ≤ 0x7FF)
    (small : character.toNat ≤ 0xFFFF) (retained : List Char) (suffix : List UInt8) :
    decodeLoop (_root_.String.utf8EncodeChar character ++ suffix) retained =
      decodeLoop suffix (character :: retained) := by
  let value := character.toNat
  let first := (value / 4096) % 16 + 0xE0
  let second := (value / 64) % 64 + 0x80
  let third := value % 64 + 0x80
  have low := Division.mod_add_div value 64
  have middle := Division.mod_add_div (value / 64) 64
  have top := Division.mod_add_div value 4096
  have remainderBound := Nat.mod_lt value (show 0 < 4096 from by decide)
  have middleBound := Nat.mod_lt (value / 64) (show 0 < 64 from by decide)
  have lowBound := Nat.mod_lt value (show 0 < 64 from by decide)
  have highBound : value / 4096 < 16 := by omega0
  have quotientIdentity : (value / 64) / 64 = value / 4096 := by omega0
  have quotientReduced := Remainder.mod_eq_of_lt highBound
  have firstBound : first < 256 := by omega0
  have secondBound : second < 256 := by omega0
  have thirdBound : third < 256 := by omega0
  have notFirstAscii : ¬ first < 0x80 := by omega0
  have notFirstInvalid : ¬ first < 0xC2 := by omega0
  have notFirstTwo : ¬ first ≤ 0xDF := by omega0
  have firstSmall : first ≤ 0xEF := by omega0
  have lowerBound : (if first = 0xE0 then 0xA0 else 0x80) ≤ second := by
    by_cases retained : first = 0xE0
    · rw [if_pos retained]
      omega0
    · rw [if_neg retained]
      omega0
  have scalarValid := character.valid
  change value < 0xD800 ∨ (0xDFFF < value ∧ value < 0x110000) at scalarValid
  have upperBound : second ≤ (if first = 0xED then 0x9F else 0xBF) := by
    by_cases retained : first = 0xED
    · rw [if_pos retained]
      omega0
    · rw [if_neg retained]
      omega0
  have thirdContinuation : continuation (UInt8.ofNat third) := by
    change 0x80 ≤ (UInt8.ofNat third).toNat ∧ (UInt8.ofNat third).toNat ≤ 0xBF
    rw [byte_value thirdBound]
    constructor <;> omega0
  have nextBounds :
      (if first = 0xE0 then 0xA0 else 0x80) ≤ (UInt8.ofNat second).toNat ∧
      (UInt8.ofNat second).toNat ≤ (if first = 0xED then 0x9F else 0xBF) ∧
      continuation (UInt8.ofNat third) := by
    rw [byte_value secondBound]
    exact ⟨lowerBound, upperBound, thirdContinuation⟩
  have scalarIdentity :
      (first - 0xE0) * 4096 + (second - 0x80) * 64 + (third - 0x80) = value := by
    have digits := three_byte_digits (show value < 65536 from by omega0)
    omega0
  change ¬ character.val.toNat ≤ 0x7F at notAscii
  change ¬ character.val.toNat ≤ 0x7FF at notTwo
  change character.val.toNat ≤ 0xFFFF at small
  rw [_root_.String.utf8EncodeChar, if_neg notAscii, if_neg notTwo, if_pos small]
  change decodeLoop (UInt8.ofNat first :: UInt8.ofNat second ::
    UInt8.ofNat third :: suffix) retained =
      decodeLoop suffix (character :: retained)
  conv => lhs; unfold decodeLoop
  dsimp only
  rw [byte_value firstBound, if_neg notFirstAscii,
    if_neg notFirstInvalid]
  rw [if_neg notFirstTwo]
  rw [if_pos firstSmall, if_pos nextBounds,
    byte_value secondBound, byte_value thirdBound, scalarIdentity, repack_character]
  rfl

/-- Decoding an original four-byte UTF8 fiber retains its original character.

The original scalar validity bounds the top digit below U+110000. The original
quotient and remainder identities supply the F0 and F4 second-byte restrictions. -/
private theorem decodeLoop_four (character : Char)
    (notAscii : ¬ character.toNat ≤ 0x7F) (notTwo : ¬ character.toNat ≤ 0x7FF)
    (notThree : ¬ character.toNat ≤ 0xFFFF) (retained : List Char) (suffix : List UInt8) :
    decodeLoop (_root_.String.utf8EncodeChar character ++ suffix) retained =
      decodeLoop suffix (character :: retained) := by
  let value := character.toNat
  let first := (value / 262144) % 8 + 0xF0
  let second := (value / 4096) % 64 + 0x80
  let third := (value / 64) % 64 + 0x80
  let fourth := value % 64 + 0x80
  have scalarValid := character.valid
  change value < 0xD800 ∨ (0xDFFF < value ∧ value < 0x110000) at scalarValid
  have valueBound : value < 0x110000 := by omega0
  have low := Division.mod_add_div value 64
  have middle := Division.mod_add_div (value / 64) 64
  have high := Division.mod_add_div (value / 4096) 64
  have top := Division.mod_add_div value 262144
  have base4096 := Division.mod_add_div value 4096
  have lowBound := Nat.mod_lt value (show 0 < 64 from by decide)
  have middleBound := Nat.mod_lt (value / 64) (show 0 < 64 from by decide)
  have highRemainderBound := Nat.mod_lt (value / 4096) (show 0 < 64 from by decide)
  have remainder4096Bound := Nat.mod_lt value (show 0 < 4096 from by decide)
  have remainder262144Bound := Nat.mod_lt value (show 0 < 262144 from by decide)
  have middleIdentity : (value / 64) / 64 = value / 4096 := by omega0
  have highIdentity : (value / 4096) / 64 = value / 262144 := by omega0
  have topBound : value / 262144 < 8 := by omega0
  have quotientReduced := Remainder.mod_eq_of_lt topBound
  have firstBound : first < 256 := by omega0
  have secondBound : second < 256 := by omega0
  have thirdBound : third < 256 := by omega0
  have fourthBound : fourth < 256 := by omega0
  have notFirstAscii : ¬ first < 0x80 := by omega0
  have notFirstInvalid : ¬ first < 0xC2 := by omega0
  have notFirstTwo : ¬ first ≤ 0xDF := by omega0
  have notFirstThree : ¬ first ≤ 0xEF := by omega0
  have firstSmall : first ≤ 0xF4 := by omega0
  have lowerBound : (if first = 0xF0 then 0x90 else 0x80) ≤ second := by
    by_cases retained : first = 0xF0
    · rw [if_pos retained]
      omega0
    · rw [if_neg retained]
      omega0
  have upperBound : second ≤ (if first = 0xF4 then 0x8F else 0xBF) := by
    by_cases retained : first = 0xF4
    · rw [if_pos retained]
      omega0
    · rw [if_neg retained]
      omega0
  have thirdContinuation : continuation (UInt8.ofNat third) := by
    change 0x80 ≤ (UInt8.ofNat third).toNat ∧ (UInt8.ofNat third).toNat ≤ 0xBF
    rw [byte_value thirdBound]
    constructor <;> omega0
  have fourthContinuation : continuation (UInt8.ofNat fourth) := by
    change 0x80 ≤ (UInt8.ofNat fourth).toNat ∧ (UInt8.ofNat fourth).toNat ≤ 0xBF
    rw [byte_value fourthBound]
    constructor <;> omega0
  have nextBounds :
      (if first = 0xF0 then 0x90 else 0x80) ≤ (UInt8.ofNat second).toNat ∧
      (UInt8.ofNat second).toNat ≤ (if first = 0xF4 then 0x8F else 0xBF) ∧
      continuation (UInt8.ofNat third) ∧ continuation (UInt8.ofNat fourth) := by
    rw [byte_value secondBound]
    exact ⟨lowerBound, upperBound, thirdContinuation, fourthContinuation⟩
  have scalarIdentity : (first - 0xF0) * 262144 + (second - 0x80) * 4096 +
      (third - 0x80) * 64 + (fourth - 0x80) = value := by
    have digits := four_byte_digits valueBound
    omega0
  change ¬ character.val.toNat ≤ 0x7F at notAscii
  change ¬ character.val.toNat ≤ 0x7FF at notTwo
  change ¬ character.val.toNat ≤ 0xFFFF at notThree
  rw [_root_.String.utf8EncodeChar, if_neg notAscii, if_neg notTwo, if_neg notThree]
  change decodeLoop (UInt8.ofNat first :: UInt8.ofNat second ::
    UInt8.ofNat third :: UInt8.ofNat fourth :: suffix) retained =
      decodeLoop suffix (character :: retained)
  conv => lhs; unfold decodeLoop
  dsimp only
  rw [byte_value firstBound, if_neg notFirstAscii,
    if_neg notFirstInvalid]
  rw [if_neg notFirstTwo]
  rw [if_neg notFirstThree, if_pos firstSmall]
  rw [ if_pos nextBounds, byte_value secondBound,
    byte_value thirdBound, byte_value fourthBound, scalarIdentity, repack_character]
  rfl

/-- Decoding any original UTF8 character fiber retains its original character.

The four original encoding branches exhaust every Unicode scalar. Each branch
consumes exactly its own original bytes and retains the decoded original suffix. -/
private theorem decodeLoop_character (character : Char) (retained : List Char) (suffix : List UInt8) :
    decodeLoop (_root_.String.utf8EncodeChar character ++ suffix) retained =
      decodeLoop suffix (character :: retained) := by
  by_cases ascii : character.toNat ≤ 0x7F
  · exact decodeLoop_ascii character ascii retained suffix
  · by_cases two : character.toNat ≤ 0x7FF
    · exact decodeLoop_two character ascii two retained suffix
    · by_cases three : character.toNat ≤ 0xFFFF
      · exact decodeLoop_three character ascii two three retained suffix
      · exact decodeLoop_four character ascii two three retained suffix

/-- Decoding an original character encoding retains the exact reverse accumulator.

The original supplied prefix is reversed once at the end. Each supplied scalar
is transferred into that same accumulator, preserving the original list order. -/
private theorem decodeLoop_characters : ∀ (characters retained : List Char),
    decodeLoop (characters.flatMap _root_.String.utf8EncodeChar) retained =
      some (retained.reverse ++ characters)
  | [], retained => by
      change some retained.reverse = some (retained.reverse ++ [])
      rw [Append.append_nil]
  | character :: characters, retained => by
      change decodeLoop (_root_.String.utf8EncodeChar character ++
        characters.flatMap _root_.String.utf8EncodeChar) retained =
          some (retained.reverse ++ (character :: characters))
      rw [decodeLoop_character, decodeLoop_characters characters (character :: retained),
        Reverse.reverse_cons, Append.append_assoc]
      rfl

/-- Decode finite original bytes with one retained reversed-character accumulator.

The tail-recursive loop consumes original byte tails and never recomputes a
prefix. A single original reversal returns the retained scalars in their order. -/
private def decodeCharacters (bytes : List UInt8) : Option (List Char) :=
  decodeLoop bytes []

/-- Decoding any original finite character encoding retains that complete list.

The accumulator invariant with the original empty prefix returns every original
character, occurrence and order. No runtime agreement corpus supplies this fact. -/
private theorem decode_characters (characters : List Char) :
    decodeCharacters (characters.flatMap _root_.String.utf8EncodeChar) = some characters :=
  decodeLoop_characters characters []

/-- Encode a retained character list using the original executable byte materializer.

The supplied scalar fibers, finite list order and original materialization loop
are retained exactly; the original model encoding is definitionally the same data. -/
private def encode (characters : List Char) : _root_.ByteArray :=
  (characters.flatMap _root_.String.utf8EncodeChar).toByteArray

/-- This executable encoding is the original UTF8 witness encoding.

The equality concerns the same original scalar list and complete original byte
array, rather than a readback approximation or an alternate scalar carrier. -/
private theorem encode_eq_utf8Encode (characters : List Char) :
    encode characters = characters.utf8Encode := rfl

/-- Retain the exact original UTF8 encoding witness for the supplied bytes.

The scalar list is executable data and its equation certifies the original bytes.
Its bound and validity proof fields remain those of the original Char carrier. -/
public abbrev Decoded (bytes : _root_.ByteArray) :=
  { characters : List Char // bytes = characters.utf8Encode }

/-- Decode original finite bytes and check the exact retained scalar encoding.

Candidates are computed once from the original byte readback. Structural byte
comparison certifies the original input, without using Core UTF8 decidability. -/
public def decode? (bytes : _root_.ByteArray) : Option (Decoded bytes) :=
  match decodeCharacters bytes.data.toList with
  | none => none
  | some characters =>
      let encoded := encode characters
      match Purelib.Data.ByteArray.decEq bytes encoded with
      | .isFalse _ => none
      | .isTrue same => some ⟨characters, same.trans (encode_eq_utf8Encode characters)⟩

/-- The returned scalar list certifies original-byte UTF8 validity.

The original IsValidUTF8 constructor receives that retained scalar list and its
exact encoding equality, so successful certification cannot accept invalid bytes. -/
public theorem valid {bytes : _root_.ByteArray} (decoded : Decoded bytes) : bytes.IsValidUTF8 :=
  .intro decoded.val decoded.property

/-- Every original finite character encoding succeeds in the certified decoder.

The structural scalar decoder retains the supplied list. Its exact byte check
then succeeds on the same original encoding; the checked equality is proof data. -/
private theorem decode_encoded (characters : List Char) :
    ∃ decoded : Decoded (encode characters), decode? (encode characters) = some decoded := by
  cases checked : Purelib.Data.ByteArray.decEq (encode characters) (encode characters) with
  | isFalse different => exact False.elim (different rfl)
  | isTrue same =>
      refine ⟨⟨characters, same.trans (encode_eq_utf8Encode characters)⟩, ?_⟩
      unfold decode?
      have readback : (encode characters).data.toList =
          characters.flatMap _root_.String.utf8EncodeChar :=
        Purelib.Data.ByteArray.toList_data_toByteArray _
      rw [readback, decode_characters]
      dsimp only
      rw [checked]

/-- Every input carrying the original UTF8 validity predicate succeeds.

Case elimination retains its displayed finite character list and exact input
encoding equality. The same original input is certified without choosing a witness. -/
public theorem decode_of_valid {bytes : _root_.ByteArray} (retained : bytes.IsValidUTF8) :
    ∃ decoded : Decoded bytes, decode? bytes = some decoded := by
  cases retained with
  | intro characters same =>
      have exactEncoding : bytes = encode characters := same.trans (encode_eq_utf8Encode characters).symm
      cases exactEncoding
      exact decode_encoded characters

/-- Certified-decoder failure is exactly original UTF8 invalidity.

Success supplies the original validity witness and validity supplies success.
Thus neither a runtime agreement corpus nor a guessed negative predicate is used
as a substitute for all-input acceptance and rejection equivalence. -/
public theorem decode_none_iff (bytes : _root_.ByteArray) :
    decode? bytes = none ↔ ¬ bytes.IsValidUTF8 := by
  constructor
  · intro failed retained
    obtain ⟨decoded, accepted⟩ := decode_of_valid retained
    rw [failed] at accepted
    cases accepted
  · intro invalid
    cases result : decode? bytes with
    | none => rfl
    | some decoded => exact False.elim (invalid (valid decoded))

end Purelib.Data.ByteArray.UTF8
