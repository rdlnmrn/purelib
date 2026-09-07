import mathlib.Tactic.QuotientFreeRing
import CCL.Geometry.PositiveDyadic
import CCL.Progressive.Log

/-!
# Finite dyadic range reduction for the progressive logarithm

A logarithm needs branch information.  This module records that information
as one finite dyadic chart: a natural exponent, a scaling direction, and a
proof that every candidate at the displayed input state is carried into the
overlapping real interval `[1/2,2]`.

The output is the local finite logarithm of the scaled input plus or minus an
explicit natural multiple of the independently generated finite `log 2`
samples.  No completed logarithm, limiting value, or infinite functional
equation appears in the construction.
-/

namespace CCL.ProgressiveLogRange

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named

abbrev Direction := CCL.PositiveDyadic.Direction

def dyadicPower (exponent : Nat) : Coordinate :=
  CCL.PositiveDyadic.power exponent

def dyadicScalar (direction : Direction) (exponent : Nat) : Coordinate :=
  CCL.PositiveDyadic.factor direction exponent

def dyadicFactor : Direction → Nat → Gaussian
  | direction, exponent => ⟨dyadicScalar direction exponent, 0⟩

theorem dyadicFactor_mul_re (direction : Direction) (exponent : Nat)
    (value : Gaussian) :
    (dyadicFactor direction exponent * value).re =
      dyadicScalar direction exponent * value.re := by
  simp only [dyadicFactor, RFAP.ConstructiveGaussian.Gaussian.mul_re]
  ring1

theorem dyadicFactor_mul_im_of_real (direction : Direction) (exponent : Nat)
    {value : Gaussian} (real : value.im = 0) :
    (dyadicFactor direction exponent * value).im = 0 := by
  simp only [dyadicFactor, RFAP.ConstructiveGaussian.Gaussian.mul_im, real]
  ring1

def scaledInput (input : Named) (direction : Direction)
    (exponent : Nat) : Named :=
  CCL.ProgressiveTransducer.Named.mul
    (CCL.ProgressiveTransducer.Named.exact
      (dyadicFactor direction exponent)) input

/-- All data needed to select one finite branch-safe logarithm chart. -/
structure DyadicChart (input : Named) where
  direction : Direction
  exponent : Nat
  localChart : CCL.ProgressiveLog.Chart
    (scaledInput input direction exponent)

/-- The local finite logarithm stream at the exact rational input `2`. -/
def logTwo : Named :=
  CCL.ProgressiveLog.named
    (CCL.ProgressiveTransducer.Named.exact ⟨2, 0⟩)
    (CCL.ProgressiveLog.Chart.exact 2 (by decide) le_rfl)

/-- Signed finite correction coefficient.  Downscaling gives
`log(x / 2^n) + n log 2`; upscaling gives
`log(2^n x) - n log 2`. -/
def correctionCoefficient (direction : Direction)
    (exponent : Nat) : Gaussian :=
  match direction with
  | .down => ⟨(exponent : Coordinate), 0⟩
  | .up => ⟨-(exponent : Coordinate), 0⟩

def correction (direction : Direction) (exponent : Nat) : Named :=
  CCL.ProgressiveTransducer.Named.mul
    (CCL.ProgressiveTransducer.Named.exact
      (correctionCoefficient direction exponent)) logTwo

/-- Global finite logarithm output from one explicit branch-safe dyadic
chart. -/
def named (input : Named) (chart : DyadicChart input) : Named :=
  CCL.ProgressiveTransducer.Named.add
    (CCL.ProgressiveLog.named
      (scaledInput input chart.direction chart.exponent) chart.localChart)
    (correction chart.direction chart.exponent)

theorem productive (input : Named) (chart : DyadicChart input)
    (count : Nat) :
    (named input chart).machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          (named input chart).machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          (named input chart).machine count).emitted.length = count :=
  (named input chart).productive count

end CCL.ProgressiveLogRange
