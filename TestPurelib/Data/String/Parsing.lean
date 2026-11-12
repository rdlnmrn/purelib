module

import Purelib.Data.String.Parsing
import Purelib.System.IO

namespace TestPurelib.Data.String.Parsing

open Purelib.Data.String (toNat? toInt? decimalMagnitude toNat?_eq_decimalMagnitude toInt?_eq_decimalMagnitude)

example (text : _root_.String) : toNat? text = decimalMagnitude text.toByteArray.data.toList 0 false :=
  toNat?_eq_decimalMagnitude text

example : toNat? "12345678_9" = some 123456789 := by
  rewrite [toNat?_eq_decimalMagnitude]
  decide +kernel

/-- Evaluate the unchanged signed scalar recurrence for native comparison. -/
private def originalInt (text : _root_.String) : Option Int :=
  match text.toByteArray.data.toList with
  | [] => none
  | first :: tail =>
      if first.toNat == 45 then
        match decimalMagnitude tail 0 false with
        | none => none
        | some value => some (Int.negOfNat value)
      else
        match decimalMagnitude (first :: tail) 0 false with
        | none => none
        | some value => some (Int.ofNat value)

/-- Check chunk boundaries, underscores, signs, zeroes and invalid UTF8 decimal characters. -/
public def check : IO Unit := do
  let naturals : List (_root_.String × Option Nat) :=
    [("", none), ("0", some 0), ("0000", some 0), ("123456789", some 123456789),
      ("1234567890", some 1234567890), ("123456789012345678", some 123456789012345678),
      ("1234567890123456789", some 1234567890123456789), ("12345678_9", some 123456789),
      ("123456789012345678901234567890123456", some 123456789012345678901234567890123456),
      ("1234567890123456789012345678901234567", some 1234567890123456789012345678901234567),
      ("123456789012345678901234567890123456789012345678901234567890123456789012345678",
        some 123456789012345678901234567890123456789012345678901234567890123456789012345678),
      ("000000000000000000000000000000000001", some 1),
      ("123456789_012345678_901234567_890123456", some 123456789012345678901234567890123456),
      ("1_234_567_890_123_456_789", some 1234567890123456789), ("_1", none), ("1_", none),
      ("123456789_012345678__9", none), ("123456789012345678901234567890123456_", none),
      ("1__2", none), ("123456789_", none), ("+1", none), ("-1", none), ("1 2", none),
      ("1\n", none), ("١", none), ("123456789é", none)]
  for (text, expected) in naturals do
    unless toNat? text = expected ∧ decimalMagnitude text.toByteArray.data.toList 0 false = expected do
      throw (IO.userError s!"batched natural parser disagrees on {text}")
  let integers : List (_root_.String × Option Int) :=
    [("", none), ("-", none), ("-0", some 0), ("-0000", some 0), ("1234567890", some 1234567890),
      ("-1234567890", some (-1234567890)), ("-1_234_567_890", some (-1234567890)),
      ("-123456789_012345678_901234567_890123456", some (-123456789012345678901234567890123456)),
      ("-000000000000000000000000000000000000", some 0),
      ("--1", none), ("+1", none), ("-_1", none), ("-1_", none), ("-1__2", none), ("−1", none)]
  for (text, expected) in integers do
    unless toInt? text = expected ∧ originalInt text = expected do
      throw (IO.userError s!"batched signed parser disagrees on {text}")
  Purelib.System.IO.println "balanced decimal carries, signs, separator failures and original values passed"

/-- Evaluate the original sequential nine-digit recurrence as a native timing reference. -/
private def sequentialChunks : List UInt8 → Nat → Nat → Nat → Nat → Bool → Option Nat
  | [], magnitude, factor, chunk, _, lastDigit =>
      if lastDigit then some (magnitude * factor + chunk) else none
  | byte :: tail, magnitude, factor, chunk, count, lastDigit =>
      if byte.toNat == 95 then
        if lastDigit then sequentialChunks tail magnitude factor chunk count false else none
      else if 48 ≤ byte.toNat && byte.toNat ≤ 57 then
        let nextFactor := factor * 10
        let nextChunk := chunk * 10 + (byte.toNat - 48)
        if count = 8 then
          sequentialChunks tail (magnitude * nextFactor + nextChunk) 1 0 0 true
        else sequentialChunks tail magnitude nextFactor nextChunk (count + 1) true
      else none

/-- Parse with the sequential reference behind a separate native call boundary. -/
@[noinline] private def sequential (text : _root_.String) : IO (Option Nat) :=
  pure (sequentialChunks text.toByteArray.data.toList 0 1 0 0 false)

/-- Parse with the balanced library parser behind a separate native call boundary. -/
@[noinline] private def balanced (text : _root_.String) : IO (Option Nat) := pure (toNat? text)

/-- Compare complete parse results and quiet timings in both execution orders.

The sequential nine-digit recurrence is the reference on the same retained
string. Native call boundaries keep the computations separate; equality is
checked after the timed regions, without formatting the resulting large natural. -/
public def profile (text : _root_.String) : IO Unit := do
  let started ← IO.monoNanosNow
  let original ← sequential text
  let sequentialEnded ← IO.monoNanosNow
  let actual ← balanced text
  let balancedEnded ← IO.monoNanosNow
  let secondStarted ← IO.monoNanosNow
  let actualAgain ← balanced text
  let secondBalancedEnded ← IO.monoNanosNow
  let originalAgain ← sequential text
  let secondSequentialEnded ← IO.monoNanosNow
  unless actual = original ∧ actualAgain = original ∧ originalAgain = original do
    throw (IO.userError "balanced decimal parser changed the complete original result")
  Purelib.System.IO.println s!"decimal parser: sequential {sequentialEnded - started} ns, \
    balanced {balancedEnded - sequentialEnded} ns; reverse balanced {secondBalancedEnded - secondStarted} ns, \
    sequential {secondSequentialEnded - secondBalancedEnded} ns; complete original results retained"

end TestPurelib.Data.String.Parsing
