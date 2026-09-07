import mathlib.RFAP.CanonicalResidual
import mathlib.RFAP.ConstructiveGaussian
import mathlib.RFAP.ComputableDerivative

/-!
Reproducible execution comparison for the Stage-2 quotient-free pilot.

Both paths compute one Newton update for `X² - 2`, alternating between the
displayed samples `3/2` and `2`.  The loop checks the exact expected finite
result so the calculation cannot be discarded.
-/

namespace CanonicalPilotBenchmark

namespace Legacy

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Polynomial := RFAP.ComputablePolynomial.DensePolynomial Gaussian

private def coordinate (numerator denominator : Int)
    (positive : 0 < denominator) : Coordinate :=
  RFAP.ConstructiveFraction.ofFraction
    ⟨numerator, denominator, positive⟩

private def threeHalves : Coordinate := coordinate 3 2 (by decide)
private def seventeenTwelfths : Coordinate := coordinate 17 12 (by decide)
private def polynomial : Polynomial := ⟨[1, 0, -2]⟩
private def firstSample : Gaussian := ⟨threeHalves, 0⟩
private def secondSample : Gaussian := ⟨2, 0⟩
private def firstExpected : Gaussian := ⟨seventeenTwelfths, 0⟩
private def secondExpected : Gaussian := ⟨threeHalves, 0⟩

private def newtonCenter (sample : Gaussian) : Gaussian :=
  sample - polynomial.eval sample /
    (RFAP.ComputableDerivative.derivative polynomial).eval sample

def trial (index : Nat) : Bool :=
  if index % 2 = 0 then
    decide (newtonCenter firstSample = firstExpected)
  else
    decide (newtonCenter secondSample = secondExpected)

end Legacy

namespace Canonical

abbrev Coordinate := RFAP.CanonicalFraction.Rational
abbrev Gaussian := RFAP.CanonicalGaussian.Gaussian
abbrev Polynomial := RFAP.CanonicalPolynomial.Polynomial

private def threeHalves : Coordinate :=
  ⟨3, 2, by decide, ⟨⟨1, -1, by decide⟩⟩⟩

private def seventeenTwelfths : Coordinate :=
  ⟨17, 12, by decide, ⟨⟨5, -7, by decide⟩⟩⟩

private def polynomial : Polynomial := ⟨[1, 0, -2]⟩
private def firstSample : Gaussian := ⟨threeHalves, 0⟩
private def secondSample : Gaussian := ⟨2, 0⟩
private def firstExpected : Gaussian := ⟨seventeenTwelfths, 0⟩
private def secondExpected : Gaussian := ⟨threeHalves, 0⟩

def trial (index : Nat) : Bool :=
  if index % 2 = 0 then
    decide (RFAP.CanonicalResidual.newtonCenter polynomial firstSample =
      firstExpected)
  else
    decide (RFAP.CanonicalResidual.newtonCenter polynomial secondSample =
      secondExpected)

end Canonical

private def countSuccessful (trial : Nat → Bool) : Nat → Nat → Nat
  | 0, successes => successes
  | remaining + 1, successes =>
      countSuccessful trial remaining
        (if trial remaining then successes + 1 else successes)

private def timed (label : String) (trial : Nat → Bool)
    (iterations : Nat) : IO Nat := do
  let start <- IO.monoMsNow
  let successes := countSuccessful trial iterations 0
  unless successes = iterations do
    throw (IO.userError s!"{label} produced a wrong result")
  let finish <- IO.monoMsNow
  IO.println s!"{label}: {finish - start} ms ({successes}/{iterations})"
  return successes

def main : IO Unit := do
  let iterations := 200000
  let _ <- timed "legacy warm-up" Legacy.trial 1000
  let _ <- timed "canonical warm-up" Canonical.trial 1000
  for _ in [0:5] do
    let legacy <- timed "legacy" Legacy.trial iterations
    let canonical <- timed "canonical" Canonical.trial iterations
    unless legacy = iterations && canonical = iterations do
      throw (IO.userError "canonical pilot benchmark produced a wrong result")

end CanonicalPilotBenchmark

def main : IO Unit := CanonicalPilotBenchmark.main
