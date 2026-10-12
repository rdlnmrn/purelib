module

public import Init.Data.ByteArray.Basic
import Purelib.Data.List.Append

/-!
# Byte-array materialization and comparison

The readback laws follow the original list-to-byte-array accumulator and relate
concatenation of retained byte lists to the original byte-array append operation.
-/

namespace Purelib.Data.ByteArray

open Purelib.Data.List

/-- Appending one byte at the end of a byte list is singleton concatenation.

Structural recursion retains each earlier byte and relates the original concat
operation to the corresponding appended singleton. -/
private theorem concat_eq_append : ∀ (bytes : List UInt8) (byte : UInt8),
    bytes.concat byte = bytes ++ [byte]
  | [], _ => rfl
  | head :: tail, byte =>
      congrArg (List.cons head) (concat_eq_append tail byte)

/-- Pushing a byte appends that byte to the retained array readback.

The original packed-byte push delegates to the original array push. Its list
readback retains the old entries and adds only the supplied final byte. -/
private theorem push_readback (bytes : _root_.ByteArray) (byte : UInt8) :
    (bytes.push byte).data.toList = bytes.data.toList ++ [byte] :=
  concat_eq_append bytes.data.toList byte

/-- The original byte-array accumulator appends every remaining byte in order.

Its starting array is retained exactly. Structural recursion follows the original
loop and transports only the current push before retaining the remaining suffix. -/
private theorem materialize_readback :
    ∀ (bytes : List UInt8) (initial : _root_.ByteArray),
      (List.toByteArray.loop bytes initial).data.toList = initial.data.toList ++ bytes
  | [], initial => (Append.append_nil initial.data.toList).symm
  | byte :: bytes, initial => by
      calc
        (List.toByteArray.loop (byte :: bytes) initial).data.toList =
            (initial.push byte).data.toList ++ bytes :=
          materialize_readback bytes (initial.push byte)
        _ = (initial.data.toList ++ [byte]) ++ bytes :=
          congrArg (fun retained => retained ++ bytes) (push_readback initial byte)
        _ = initial.data.toList ++ ([byte] ++ bytes) :=
          Append.append_assoc initial.data.toList [byte] bytes
        _ = initial.data.toList ++ (byte :: bytes) := rfl

/-- Materializing a retained byte list has exactly that list as its readback.

The original accumulator begins with the original empty byte array and follows
its displayed byte-list input without changing order or repeated occurrences. -/
public theorem toList_data_toByteArray (bytes : List UInt8) :
    bytes.toByteArray.data.toList = bytes :=
  materialize_readback bytes _root_.ByteArray.empty

/-- Byte arrays with equal retained list readbacks are equal.

Both packed arrays contain the same original finite list of byte entries. Pattern
matching on their two record layers transports that scalar list equality directly. -/
private theorem eq_of_readback_eq : ∀ {left right : _root_.ByteArray},
    left.data.toList = right.data.toList → left = right
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Materializing a concatenated byte list appends its two materialized arrays.

The original list-to-array builder retains every displayed byte. Both readbacks
are the same concatenation, using the original byte-array append operation. -/
public theorem toByteArray_append (left right : List UInt8) :
    (left ++ right).toByteArray = left.toByteArray ++ right.toByteArray := by
  apply eq_of_readback_eq
  change (left ++ right).toByteArray.data.toList =
    left.toByteArray.data.toList ++ right.toByteArray.data.toList
  rw [toList_data_toByteArray, toList_data_toByteArray, toList_data_toByteArray]

/-- Compare retained finite byte lists in lexicographic order.

The comparison consumes a byte from each nonempty input at every recursive step.
The first unequal byte decides the order; equal prefixes retain the order of the
remaining lists, with an empty list preceding a nonempty list. -/
@[expose] public def compareBytes : List UInt8 → List UInt8 → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | first :: left, second :: right =>
      if first.toNat < second.toNat then .lt
      else if second.toNat < first.toNat then .gt
      else compareBytes left right

/-- Decide equality of two bytes from their original bounded natural values.

The positive branch transports only the value equality through the original
UInt8, BitVec and Fin records. Their bound proofs are propositionally irrelevant. -/
private def byteDecEq (left right : UInt8) : Decidable (left = right) :=
  match left, right with
  | ⟨⟨⟨leftValue, _⟩⟩⟩, ⟨⟨⟨rightValue, _⟩⟩⟩ =>
    match _root_.decEq leftValue rightValue with
    | .isTrue same => .isTrue (by cases same; rfl)
    | .isFalse different =>
        .isFalse (fun same => different (congrArg UInt8.toNat same))

/-- Decide equality of finite byte lists while retaining their original entries.

Each recursive step compares the original head bytes and then the original
suffixes. A negative branch projects the particular head or suffix disagreement. -/
private def bytesDecEq : (left right : List UInt8) → Decidable (left = right)
  | [], [] => .isTrue rfl
  | [], _ :: _ => .isFalse (by intro same; cases same)
  | _ :: _, [] => .isFalse (by intro same; cases same)
  | first :: left, second :: right =>
      match byteDecEq first second with
      | .isFalse different =>
          .isFalse (fun same => different (Option.some.inj (congrArg List.head? same)))
      | .isTrue heads =>
          match bytesDecEq left right with
          | .isFalse different =>
              .isFalse (fun same => different (congrArg List.tail same))
          | .isTrue tails => .isTrue (by cases heads; cases tails; rfl)

/-- Decide equality of the original byte arrays through their retained list data.

Both readbacks are compared structurally, without an array extensionality
proposition equality. The positive result transports the original record layers. -/
public def decEq (left right : _root_.ByteArray) : Decidable (left = right) :=
  match bytesDecEq left.data.toList right.data.toList with
  | .isTrue same => .isTrue (eq_of_readback_eq same)
  | .isFalse different =>
      .isFalse (fun same => different (congrArg (fun bytes => bytes.data.toList) same))

end Purelib.Data.ByteArray
