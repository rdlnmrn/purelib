module

public import Init.Data.UInt.Basic
public import Purelib.Data.Nat.Bitwise

/-!
# Natural readbacks of unsigned 64-bit operations

The original unsigned carrier keeps its modular factory. Bit operations read its
natural values and return the same wrapped values without rebuilding bit-vector
bound certificates.
-/

open Purelib.Data

namespace Purelib.Data.UInt64

/-- Take the bitwise exclusive-or of two retained unsigned values.

The finite natural bitwise recurrence consumes both complete original values. The
original 64-bit factory retains the same modular unsigned result.
-/
@[expose] public def xor (left right : _root_.UInt64) : _root_.UInt64 :=
  _root_.UInt64.ofNat (Nat.bitwise bne left.toNat right.toNat)

/-- Shift a retained unsigned value right by the original modulo-64 amount.

The natural amount uses the same modulo-64 remainder as the original unsigned
operation. The original factory retains the complete shifted unsigned value.
-/
@[expose] public def shiftRight (value amount : _root_.UInt64) : _root_.UInt64 :=
  _root_.UInt64.ofNat (_root_.Nat.shiftRight value.toNat (amount.toNat % 64))

end Purelib.Data.UInt64
