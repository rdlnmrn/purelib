module

import Purelib.Data.Nat.Decimal
import Purelib.Data.ByteArray.Basic
-- The closed digit regression reduces the original decimal character constructor.
import all Init.Data.Repr
import Purelib.Data.Int.Decimal
import Purelib.Data.String.Basic
import Purelib.System.IO

namespace TestPurelib.Data.Nat.Decimal

open Purelib.Data.Nat.Decimal
  (repr_eq digits_binaryFuel_eq groupedDigits_eq repr_eq_binaryFuel places repr_bytes)
open Purelib.Data.String (append)
open Purelib.Data.Nat

example (value : Nat) : Decimal.repr value = Nat.repr value := repr_eq value

/-- The public all-input byte readback needs no private implementation unfolding. -/
example (value : Nat) : (Decimal.repr value).toByteArray = (Nat.repr value).toByteArray :=
  repr_bytes value

example (width fuel value : Nat) (digits : List Char)
    (bound : value < 2 ^ width) (enough : value < fuel) :
    Nat.toDigitsCore 10 (width + 1) value digits = Nat.toDigitsCore 10 fuel value digits :=
  digits_binaryFuel_eq width fuel value digits bound enough

example (width value : Nat) (digits : List Char) (bound : value < 2 ^ width) :
    Decimal.groupedDigits width value digits =
      Nat.toDigitsCore 10 (9 * width + 1) value digits := groupedDigits_eq width value digits bound

example (value : Nat) :
    Decimal.repr value = if value < USize.size then Nat.repr value else
      _root_.String.ofList (Nat.toDigitsCore 10 (Purelib.Data.Nat.BitWidth.natWidth value + 1) value []) :=
  repr_eq_binaryFuel value

example : places 9 7 [] = ['0', '0', '0', '0', '0', '0', '0', '0', '7'] := by rfl

/-- The closed padding regression exceeds either permitted platform word size.

The original platform fact has exactly the 32-bit and 64-bit alternatives; no
particular host word size is assumed by the kernel computation below.
-/
private theorem largeValue_branch : ¬ (10 ^ 36 + 1000000001 : Nat) < USize.size := by
  intro bound
  rcases System.Platform.numBits_eq with first | second
  · change (10 ^ 36 + 1000000001 : Nat) < 2 ^ System.Platform.numBits at bound
    rewrite [first] at bound
    exact (by decide +kernel : ¬ (10 ^ 36 + 1000000001 : Nat) < 2 ^ 32) bound
  · change (10 ^ 36 + 1000000001 : Nat) < 2 ^ System.Platform.numBits at bound
    rewrite [second] at bound
    exact (by decide +kernel : ¬ (10 ^ 36 + 1000000001 : Nat) < 2 ^ 64) bound

/-- The original exposed renderer reduces a complete large value through an ordinary import. -/
example : Decimal.repr (10 ^ 36 + 1000000001) = "1000000000000000000000000001000000001" := by
  unfold Decimal.repr
  rewrite [if_neg largeValue_branch]
  rfl

/-- Check original complete bytes across caches, word boundaries, large magnitudes and signed prefixes. -/
public def check : IO Unit := do
  letI : DecidableEq _root_.ByteArray := Purelib.Data.ByteArray.decEq
  let values : List Nat :=
    [0, 1, 127, 128, 999999999, 1000000000, USize.size - 1, USize.size,
      USize.size + 1, 10 ^ 18 - 1, 10 ^ 18, 10 ^ 18 + 1,
      10 ^ 27 - 1, 10 ^ 27, 10 ^ 27 + 7, 10 ^ 36 + 1000000001, 10 ^ 100, 10 ^ 100 + 1]
  for value in values do
    unless (Decimal.repr value).toByteArray = (Nat.repr value).toByteArray do
      throw (IO.userError "natural rendering changed original bytes")
    unless (Purelib.Data.Int.Decimal.repr (Int.ofNat value)).toByteArray = (Nat.repr value).toByteArray do
      throw (IO.userError "shortened positive integer rendering changed original bytes")
    unless (Purelib.Data.Int.Decimal.repr (Int.negSucc value)).toByteArray =
        (append "-" (Nat.repr (value + 1))).toByteArray do
      throw (IO.userError "shortened negative integer rendering changed original prefix or magnitude bytes")
  Purelib.System.IO.println "original decimal cache, word boundaries, large values and signed bytes passed"

end TestPurelib.Data.Nat.Decimal
