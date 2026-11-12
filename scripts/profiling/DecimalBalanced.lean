module

import Purelib.Data.Nat.Decimal
import Purelib.Data.Nat.BitWidth
import Purelib.Data.String.Parsing
import Purelib.Data.ByteArray.Basic
import Purelib.Data.Json.Codec
import Purelib.Data.Json.Parser
import Purelib.System.IO

namespace DecimalBalancedBenchmark

open Purelib
open Purelib.Data (Json)

/-- Read the exact retained numerator magnitudes and denominators once before timing. -/
private def readMagnitudes (path : System.FilePath) : IO (List Nat) := do
  let bytes ← System.IO.FS.readFile path
  let raw ← match Json.parse bytes with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  let mut magnitudes := []
  for field in ["dividend", "divisor", "quotient", "remainder"] do
    let coefficients ← match raw.getObjValAs? (Array Json) field with
      | .ok value => pure value
      | .error message => throw (IO.userError message)
    for coefficient in coefficients do
      let numerator ← match coefficient.getObjValAs? String "numerator" with
        | .ok value => pure value
        | .error message => throw (IO.userError message)
      let denominator ← match coefficient.getObjValAs? String "denominator" with
        | .ok value => pure value
        | .error message => throw (IO.userError message)
      let some signed := Data.String.toInt? numerator
        | throw (IO.userError "invalid retained original numerator")
      let some natural := Data.String.toNat? denominator
        | throw (IO.userError "invalid retained original denominator")
      unless 0 < natural do throw (IO.userError "nonpositive retained original denominator")
      magnitudes := natural :: signed.natAbs :: magnitudes
  pure magnitudes.reverse

/-- Force the unchanged nine-digit implementation through an opaque IO timing boundary. -/
@[noinline] private def grouped (value : Nat) : IO String := pure (
  if value < USize.size then Nat.repr value else
    String.ofList (Data.Nat.Decimal.groupedDigits (Data.Nat.BitWidth.natWidth value) value []))

/-- Force the production retained half-power renderer through the same IO timing boundary. -/
@[noinline] private def balanced (value : Nat) : IO String := pure (Data.Nat.Decimal.repr value)

/-- Retain original full decimal strings for byte checks outside the timed comparisons. -/
@[noinline] private def original (value : Nat) : IO String := pure (Nat.repr value)

/-- Execute and fully materialize one renderer on the retained magnitudes before reading the ending clock. -/
private def timed (render : Nat → IO String) (magnitudes : List Nat) : IO (List String × Nat) := do
  let beginning ← IO.monoNanosNow
  let values ← magnitudes.mapM render
  let ending ← IO.monoNanosNow
  pure (values, ending - beginning)

/-- Compare both rendering orders on the same original magnitudes and complete original bytes. -/
private def profile (path : System.FilePath) : IO Unit :=
  letI : DecidableEq _root_.ByteArray := Data.ByteArray.decEq
  do
    let magnitudes ← readMagnitudes path
    let reference ← magnitudes.mapM original
    let referenceBytes := reference.map String.toByteArray
    for round in List.range 3 do
      let (groupedFirst, groupedTime) ← timed grouped magnitudes
      let (balancedLast, balancedTime) ← timed balanced magnitudes
      let (balancedFirst, reverseBalancedTime) ← timed balanced magnitudes
      let (groupedLast, reverseGroupedTime) ← timed grouped magnitudes
      for actual in [groupedFirst, balancedLast, balancedFirst, groupedLast] do
        unless actual.map String.toByteArray = referenceBytes do
          throw (IO.userError "balanced rendering changed complete original decimal bytes")
      System.IO.println s!"decimal-balanced {path}: round {round}; grouped {groupedTime} ns, \
        balanced {balancedTime} ns; reverse balanced {reverseBalancedTime} ns, \
        grouped {reverseGroupedTime} ns; magnitudes {magnitudes.length}; all original bytes agree"

/-- Compare decimal renderers on the two explicitly supplied complete codec fixtures. -/
public def _root_.main (arguments : List String) : IO Unit := do
  unless arguments.length = 2 do throw (IO.userError "expected exactly two retained fixture paths")
  for path in arguments do profile (System.FilePath.mk path)
