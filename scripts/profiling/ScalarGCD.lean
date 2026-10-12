module
public import Purelib.Data.Array.Basic
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.List.Control
import Purelib.Data.Nat.GCD.Extended
import Purelib.Data.Rat.Fraction

import Purelib.Data.Nat.GCD.Scalar
public import Purelib.Data.Rat.Fraction.Arithmetic
import Init.Data.Int.Basic
import Init.Data.List.Basic
import Init.Prelude
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Nat.Defs

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.List

open Purelib.Data.Nat.GCD

open Purelib.Data.Rat

public section

/-!
Certificate-free scalar-versus-extended Euclid benchmark.  Every measured
pair must return the same gcd, and timing order alternates.  Inputs are
displayed finite integer powers, not generated period data.  This establishes
only arithmetic timings; it is not an end-to-end period performance claim.

Build `scalar_gcd_benchmark`; diagnostic runs require an explicit SIGKILL
timeout and systemd memory bound.  The harness does not import generated certificate data.

The arithmetic profiles below exercise the production constructors with
universal canonical-equality proofs.  Their reference explicitly performs the
former final normalization; timings remain synthetic, not period performance claims.
-/

namespace ScalarGCDBenchmark

/-- Evaluate a thunk through IO without inlining its timing boundary. -/
@[noinline, expose] def evaluate {α : Type} (work : Unit → α) : IO α := pure (work ())

/-- Print and flush one exact-arithmetic benchmark message. -/
@[expose] def report (message : String) : IO Unit := do
  Purelib.System.IO.println message
  (← IO.getStdout).flush

/-- Return the evaluated result together with elapsed monotonic nanoseconds. -/
@[expose] def timed {α : Type} (work : Unit → α) : IO (α × Nat) := do
  let start ← IO.monoNanosNow
  let value ← evaluate work
  pure (value, (← IO.monoNanosNow) - start)

/-- Independent numerical reference: the original extended normalization of the unreduced integer display, before
cross-cancellation shortcuts. -/
@[expose] def extendedProfile (numerator : Int) (denominator : Nat) : Int × Nat :=
  let divisor := (Extended.compute numerator.natAbs denominator).gcd
  (numerator / (divisor : Int), denominator / divisor)

/-- Profile the proved constructor itself, not an untyped multiplication shortcut. -/
@[expose] def productProduction (left right : Fraction.Rational) : Int × Nat :=
  let result := Fraction.mul left right
  (result.num, result.den)

/-- Profile the proved reduced-addition constructor itself. -/
@[expose] def additionProduction (left right : Fraction.Rational) : Int × Nat :=
  let result := Fraction.add left right
  (result.num, result.den)

/-- Check canonical normalization, addition and multiplication against extended Euclidean reduction.

The finite signed and zero-containing sample set compares the exact reduced numerator and denominator for every pair. -/
@[expose] def arithmeticRegressions : IO Unit :=
  letI : ForIn' IO (Array Fraction.Rational) Fraction.Rational inferInstance :=
    ⟨Purelib.Data.Array.forIn'⟩
  do
    let mut fractions : Array Fraction.Rational := #[]
    for numerator in [(-1071 : Int), -37, -1, 0, 1, 6, 37, 1071] do
      for predecessor in [0, 1, 7, 15, 36, 461, 1070] do
        let denominator := predecessor + 1
        let fraction := Fraction.normalize
          ⟨numerator, denominator, Nat.zero_lt_succ predecessor⟩
        unless (fraction.num, fraction.den) == extendedProfile numerator denominator do
          throw (IO.userError "normalization changed the canonical record")
        fractions := fractions.push fraction
    let mut pairs := 0
    for left in fractions do
      for right in fractions do
        let expectedSum := extendedProfile
          (left.num * (right.den : Int) + right.num * (left.den : Int)) (left.den * right.den)
        unless additionProduction left right == expectedSum do
          throw (IO.userError "addition changed the canonical record")
        unless productProduction left right ==
            extendedProfile (left.num * right.num) (left.den * right.den) do
          throw (IO.userError "multiplication changed the canonical record")
        pairs := pairs + 1
    report
      s!"Arithmetic: {fractions.size} signed/zero normalizations and {pairs} addition/multiplication pairs matched \
        extended normalization."

/-- Time two arithmetic implementations in the requested order and require exact profile equality. -/
@[expose] def compareProfiles (reverse : Bool) (reference candidate : Unit → Int × Nat) : IO (Nat × Nat) := do
  let (referenceResult, candidateResult) ← if reverse then do
      let candidateResult ← timed candidate
      let referenceResult ← timed reference
      pure (referenceResult, candidateResult)
    else do
      let referenceResult ← timed reference
      let candidateResult ← timed candidate
      pure (referenceResult, candidateResult)
  unless referenceResult.1 == candidateResult.1 do
    throw (IO.userError "measured arithmetic candidate changed the canonical profile")
  pure (referenceResult.2, candidateResult.2)

/-- Inputs are normalized before timing. Balanced operands exercise ordinary arithmetic; wide-plus-small operands model
one step in a rational accumulation. These remain synthetic data, not a claim about period execution time. -/
@[expose] def arithmeticTimings : IO Unit := do
  for (exponent, count) in [(64, 200), (512, 40), (4096, 4), (16384, 1)] do
    for (label, rightExponent) in [("balanced", exponent), ("wide+small", 32)] do
      let mut sumReference := 0
      let mut sumProduction := 0
      let mut productReference := 0
      let mut productProductionTime := 0
      for index in List.range count do
        let left ← evaluate fun _ => Fraction.normalize
          ⟨Int.ofNat (3 ^ exponent + 43 + 17 * index),
            5 ^ exponent + 71 + 13 * index + 1, Nat.zero_lt_succ _⟩
        let right ← evaluate fun _ => Fraction.normalize
          ⟨Int.ofNat (7 ^ rightExponent + 29 + 7 * index),
            11 ^ rightExponent + 37 + 19 * index + 1, Nat.zero_lt_succ _⟩
        let sumTimes ← compareProfiles (index % 2 = 0)
          (fun _ =>
            let result := Fraction.normalize (Fraction.addRaw left right)
            (result.num, result.den))
          (fun _ => additionProduction left right)
        let productTimes ← compareProfiles (index % 2 = 0)
          (fun _ =>
            let result := Fraction.normalize (Fraction.mulRaw left right)
            (result.num, result.den))
          (fun _ => productProduction left right)
        sumReference := sumReference + sumTimes.1
        sumProduction := sumProduction + sumTimes.2
        productReference := productReference + productTimes.1
        productProductionTime := productProductionTime + productTimes.2
      report
        s!"arithmetic/{label}, exponent={exponent}, pairs={count}: add normalized-reference={sumReference / 1000} us, \
          production={sumProduction / 1000} us; mul normalized-reference={productReference / 1000} us, \
          production={productProductionTime / 1000} us; all profiles equal"

/-- Check scalar GCD edge cases and time finite exact-result GCD and rational-arithmetic comparisons. -/
@[expose] def main : IO Unit := do
  arithmeticRegressions
  for left in [0, 1, 2, 16, 37, 462, 1071] do
    for right in [0, 1, 2, 16, 37, 462, 1071] do
      unless Scalar.gcd left right == (Extended.compute left right).gcd do
        throw (IO.userError "scalar gcd changed an edge case")
  report "All 49 zero/unit/common-factor edge cases passed."
  for (exponent, count) in [(64, 400), (512, 100), (4096, 8), (16384, 2)] do
    let left := 3 ^ exponent + 43
    let right := 5 ^ exponent + 71
    report s!"gcd: input bits=({left.log2 + 1}, {right.log2 + 1}); pairs={count}"
    let mut scalarNs := 0
    let mut extendedNs := 0
    for index in List.range count do
      let first := left + 17 * index
      let second := right + 13 * index
      let scalar := fun _ => Scalar.gcd first second
      let extended := fun _ => (Extended.compute first second).gcd
      let (scalarResult, extendedResult) ← if index % 2 = 0 then do
          let scalarResult ← timed scalar
          let extendedResult ← timed extended
          pure (scalarResult, extendedResult)
        else do
          let extendedResult ← timed extended
          let scalarResult ← timed scalar
          pure (scalarResult, extendedResult)
      unless scalarResult.1 == extendedResult.1 do
        throw (IO.userError "scalar gcd changed a measured result")
      scalarNs := scalarNs + scalarResult.2
      extendedNs := extendedNs + extendedResult.2
    report s!"gcd: scalar={scalarNs / 1000} us; extended={extendedNs / 1000} us; all {count} results equal"
  arithmeticTimings

end ScalarGCDBenchmark

/-- Run the scalar GCD and canonical rational-arithmetic benchmark. -/
@[expose] def main : IO Unit := ScalarGCDBenchmark.main
