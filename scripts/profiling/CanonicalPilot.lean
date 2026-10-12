module
public import Purelib.System.IO
import Purelib.Data.String.Basic
public import Purelib.Data.Range
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Rat.SignedFraction.Normalization
import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Evaluation.Gaussian.NewtonResidual

import Purelib.Polynomial.Dense.Derivative
import Init.Prelude
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.SignedFraction.Basic
import Purelib.Polynomial.Dense.Evaluation

set_option backward.match.sparseCases false

open scoped Purelib.Data.String Purelib.Data.Range

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.SignedFraction

open Purelib.Polynomial

open Purelib.Polynomial.Dense

open Purelib.Polynomial.Evaluation.Gaussian

section
public section

/-!
Reproducible execution comparison for the Stage-2 quotient-free pilot.

Both paths compute one Newton update for `X² - 2`, alternating between the
displayed samples `3/2` and `2`.  The loop checks the exact expected finite
result so the calculation cannot be discarded.
-/

namespace CanonicalPilotBenchmark

namespace Legacy
/-- Dense polynomials over the canonical Gaussian-rational carrier. -/
abbrev Polynomial := Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical

/-- Normalize a signed integer fraction with its retained positive denominator. -/
private def coordinate (numerator denominator : Int)
    (positive : 0 < denominator) : Fraction.Rational :=
  Normalization.ofFraction
    ⟨numerator, denominator, positive⟩

/-- The normalized rational three halves. -/
private def threeHalves : Fraction.Rational := coordinate 3 2 (by decide)
/-- The normalized rational seventeen twelfths. -/
private def seventeenTwelfths : Fraction.Rational := coordinate 17 12 (by decide)
/-- The quadratic polynomial X squared minus two. -/
private def polynomial : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -2]⟩
/-- The real Gaussian sample three halves. -/
private def firstSample : Data.Gaussian.Basic.Canonical := ⟨threeHalves, 0⟩
/-- The real Gaussian sample two. -/
private def secondSample : Data.Gaussian.Basic.Canonical := ⟨2, 0⟩
/-- The exact Newton update seventeen twelfths of the first sample. -/
private def firstExpected : Data.Gaussian.Basic.Canonical := ⟨seventeenTwelfths, 0⟩
/-- The exact Newton update three halves of the second sample. -/
private def secondExpected : Data.Gaussian.Basic.Canonical := ⟨threeHalves, 0⟩

/-- Compute one scalar Newton update using direct polynomial and derivative evaluation. -/
private def newtonCenter (sample : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.Canonical :=
  sample - polynomial.eval sample /
    (Derivative.derivative polynomial).eval sample

/-- Check the exact Newton result for the sample selected by the iteration parity. -/
@[expose] def trial (index : Nat) : Bool :=
  let threeHalves : Fraction.Rational :=
    Normalization.ofFraction
      ⟨3, 2, by decide⟩
  let seventeenTwelfths : Fraction.Rational :=
    Normalization.ofFraction
      ⟨17, 12, by decide⟩
  let polynomial : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -2]⟩
  let firstSample : Data.Gaussian.Basic.Canonical := ⟨threeHalves, 0⟩
  let secondSample : Data.Gaussian.Basic.Canonical := ⟨2, 0⟩
  let firstExpected : Data.Gaussian.Basic.Canonical := ⟨seventeenTwelfths, 0⟩
  let secondExpected : Data.Gaussian.Basic.Canonical := ⟨threeHalves, 0⟩
  let newtonCenter := fun sample : Data.Gaussian.Basic.Canonical =>
    sample - polynomial.eval sample /
      (Derivative.derivative polynomial).eval sample
  if index % 2 = 0 then
    decide (newtonCenter firstSample = firstExpected)
  else
    decide (newtonCenter secondSample = secondExpected)

end Legacy

namespace Canonical

/-- The reduced rational three halves with its explicit Bézout witness. -/
private def threeHalves : Fraction.Rational :=
  ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩

/-- The reduced rational seventeen twelfths with its explicit Bézout witness. -/
private def seventeenTwelfths : Fraction.Rational :=
  ⟨17, 12, by decide, ⟨⟨5, -7, by decide⟩⟩⟩

/-- The quadratic polynomial X squared minus two. -/
private def polynomial : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -2]⟩
/-- The real Gaussian sample three halves. -/
private def firstSample : Data.Gaussian.Basic.Canonical := ⟨threeHalves, 0⟩
/-- The real Gaussian sample two. -/
private def secondSample : Data.Gaussian.Basic.Canonical := ⟨2, 0⟩
/-- The exact Newton update seventeen twelfths of the first sample. -/
private def firstExpected : Data.Gaussian.Basic.Canonical := ⟨seventeenTwelfths, 0⟩
/-- The exact Newton update three halves of the second sample. -/
private def secondExpected : Data.Gaussian.Basic.Canonical := ⟨threeHalves, 0⟩

/-- Check the canonical Newton operation against its exact alternating expected results. -/
@[expose] def trial (index : Nat) : Bool :=
  let polynomial : (Dense.Basic.DensePolynomial Data.Gaussian.Basic.Canonical) := ⟨[1, 0, -2]⟩
  let firstSample : Data.Gaussian.Basic.Canonical :=
    ⟨⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩, 0⟩
  let secondSample : Data.Gaussian.Basic.Canonical := ⟨2, 0⟩
  let firstExpected : Data.Gaussian.Basic.Canonical :=
    ⟨⟨17, 12, by decide, ⟨⟨5, -7, by decide⟩⟩⟩, 0⟩
  let secondExpected : Data.Gaussian.Basic.Canonical :=
    ⟨⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩, 0⟩
  if index % 2 = 0 then
    decide (NewtonResidual.newtonCenter polynomial firstSample =
      firstExpected)
  else
    decide (NewtonResidual.newtonCenter polynomial secondSample =
      secondExpected)

end Canonical

/-- Count successful trials while consuming the supplied finite iteration count. -/
private def countSuccessful (trial : Nat → Bool) : Nat → Nat → Nat
  | 0, successes => successes
  | remaining + 1, successes =>
      countSuccessful trial remaining
        (if trial remaining then successes + 1 else successes)

/-- Time a finite trial loop and reject any incorrect result. -/
private def timed (label : String) (trial : Nat → Bool)
    (iterations : Nat) : IO Nat := do
  let start <- IO.monoMsNow
  let successes := countSuccessful trial iterations 0
  unless successes = iterations do
    throw (IO.userError s!"{label} produced a wrong result")
  let finish <- IO.monoMsNow
  Purelib.System.IO.println s!"{label}: {finish - start} ms ({successes}/{iterations})"
  return successes

/-- Time a finite trial loop with its counter retained inside the measurement operation. -/
@[expose] def timedRun (label : String) (trial : Nat → Bool)
    (iterations : Nat) : IO Nat := do
  let rec countSuccessful : Nat → Nat → Nat
    | 0, successes => successes
    | remaining + 1, successes =>
        countSuccessful remaining
          (if trial remaining then successes + 1 else successes)
  let start <- IO.monoMsNow
  let successes := countSuccessful iterations 0
  unless successes = iterations do
    throw (IO.userError s!"{label} produced a wrong result")
  let finish <- IO.monoMsNow
  Purelib.System.IO.println s!"{label}: {finish - start} ms ({successes}/{iterations})"
  return successes

/-- Warm both Newton implementations and run five exact-result timing comparisons. -/
@[expose] def main : IO Unit := do
  let iterations := 200000
  let _ <- timedRun "legacy warm-up" Legacy.trial 1000
  let _ <- timedRun "canonical warm-up" Canonical.trial 1000
  for _ in [0:5] do
    let legacy <- timedRun "legacy" Legacy.trial iterations
    let canonical <- timedRun "canonical" Canonical.trial iterations
    unless legacy = iterations && canonical = iterations do
      throw (IO.userError "canonical pilot benchmark produced a wrong result")

end CanonicalPilotBenchmark

/-- Run the canonical Newton pilot benchmark. -/
@[expose] def main : IO Unit := CanonicalPilotBenchmark.main

end
