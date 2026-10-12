module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Exponential
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Reciprocal
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.CCL.Request
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Automatic finite transport for progressive quadratic traces

The semantic trace layer records five Gaussian-rational sequences with one
geometric modulus and one centre bound.  This file proves that the elementary
finite channel algebra computes new moduli and bounds.  Multiplication and
composition can consequently synthesize their `Trace.Transport` records;
callers no longer have to restate continuity as an external premise.

Reciprocal transport is intentionally not inferred from pointwise
nonzeroness.  Its constructive interface, added below, requires a displayed
positive lower quadrance valid at every finite stage.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.CCL.Output

section Output

section
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic
open Purelib.Data
/-- The automatic exponential trace satisfies the finite common-index request contract.

Base, output displacement and increment quadrances are at most one at every index. At any positive request target, the
resulting trace preserves its quadratic law and the requested finite word growth. -/
theorem
  exponentialAutomatic_bitstream_and_quadratic_law
    {increment : Nat → Canonical} (inner : Trace increment)
    (baseUnit : ∀ index, Gaussian.Norm.Basic.normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      Gaussian.Norm.Basic.normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Gaussian.Norm.Basic.normSq (increment index) ≤ 1)
    (current : Nat) (target : Rational) (positive : 0 < target)
    (count : Nat) :
    Trace.RequestContract
      (Exponential.exponentialAutomatic inner (by
          intro index;
          have scalar := baseUnit index;
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using scalar) (by
            intro index;
            have scalar := movementUnit index;
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using scalar) (by
            intro index;
            have scalar := incrementUnit index;
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using scalar))
      current target positive count :=
  Trace.bitstream_and_quadratic_law
    (Exponential.exponentialAutomatic inner (by
        intro index;
        have scalar := baseUnit index;
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using scalar) (by
          intro index;
          have scalar := movementUnit index;
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using scalar) (by
          intro index;
          have scalar := incrementUnit index;
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using scalar))
    current target positive count

/-- The automatic reducedLog trace satisfies the finite common-index request contract.

Output displacement quadrance is at most one ninth, and increment quadrance is at most one at every index. At any
positive request target, the resulting trace preserves its quadratic law and the requested finite word growth. -/
theorem
  reducedLogAutomatic_bitstream_and_quadratic_law
    {increment : Nat → Canonical} (inner : Trace increment)
    (movementDisk : ∀ index,
      Gaussian.Norm.Basic.normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1 / 9)
    (incrementUnit : ∀ index, Gaussian.Norm.Basic.normSq (increment index) ≤ 1)
    (current : Nat) (target : Rational) (positive : 0 < target)
    (count : Nat) :
    Trace.RequestContract
      (ReducedLog.reducedLogAutomatic inner movementDisk incrementUnit)
      current target positive count :=
  Trace.bitstream_and_quadratic_law
    (ReducedLog.reducedLogAutomatic inner movementDisk incrementUnit)
    current target positive count

/-- The automatic sine trace satisfies the finite common-index request contract.

The rotated trace has unit bounds for its base and output displacement, and the original increment has a unit bound at
every index. At any positive request target, the resulting trace preserves its quadratic law and the requested finite
word growth. -/
theorem
  sineAutomatic_bitstream_and_quadratic_law
    {increment : Nat → Canonical} (inner : Trace increment)
    (rotatedBaseUnit : ∀ index,
      Gaussian.Norm.Basic.normSq ((Trigonometric.rotateAutomatic inner).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      Gaussian.Norm.Basic.normSq (((Trigonometric.rotateAutomatic inner).certificate index).output -
        ((Trigonometric.rotateAutomatic inner).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Gaussian.Norm.Basic.normSq (increment index) ≤ 1)
    (current : Nat) (target : Rational) (positive : 0 < target)
    (count : Nat) :
    Trace.RequestContract
      (Trigonometric.sineAutomatic inner (by
          intro index;
          have scalar := rotatedBaseUnit index;
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using scalar) (by
            intro index;
            have scalar := rotatedMovementUnit index;
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using scalar) (by
            intro index;
            have scalar := incrementUnit index;
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using scalar))
      current target positive count :=
  Trace.bitstream_and_quadratic_law
    (Trigonometric.sineAutomatic inner (by
        intro index;
        have scalar := rotatedBaseUnit index;
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using scalar) (by
          intro index;
          have scalar := rotatedMovementUnit index;
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using scalar) (by
          intro index;
          have scalar := incrementUnit index;
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using scalar))
    current target positive count

/-- The automatic cosine trace satisfies the finite common-index request contract.

The rotated trace has unit bounds for its base and output displacement, and the original increment has a unit bound at
every index. At any positive request target, the resulting trace preserves its quadratic law and the requested finite
word growth. -/
theorem
  cosineAutomatic_bitstream_and_quadratic_law
    {increment : Nat → Canonical} (inner : Trace increment)
    (rotatedBaseUnit : ∀ index,
      Gaussian.Norm.Basic.normSq ((Trigonometric.rotateAutomatic inner).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      Gaussian.Norm.Basic.normSq (((Trigonometric.rotateAutomatic inner).certificate index).output -
        ((Trigonometric.rotateAutomatic inner).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Gaussian.Norm.Basic.normSq (increment index) ≤ 1)
    (current : Nat) (target : Rational) (positive : 0 < target)
    (count : Nat) :
    Trace.RequestContract
      (Trigonometric.cosineAutomatic inner (by
          intro index;
          have scalar := rotatedBaseUnit index;
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using scalar) (by
            intro index;
            have scalar := rotatedMovementUnit index;
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using scalar) (by
            intro index;
            have scalar := incrementUnit index;
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using scalar))
      current target positive count :=
  Trace.bitstream_and_quadratic_law
    (Trigonometric.cosineAutomatic inner (by
        intro index;
        have scalar := rotatedBaseUnit index;
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using scalar) (by
          intro index;
          have scalar := rotatedMovementUnit index;
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using scalar) (by
          intro index;
          have scalar := incrementUnit index;
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using scalar))
    current target positive count

/-- The automatic div trace satisfies the finite common-index request contract.

The denominator has uniform positive rational lower bounds for its base and output quadrances. At any positive request
target, the resulting trace preserves its quadratic law and the requested finite word growth. -/
theorem
  divAutomatic_bitstream_and_quadratic_law
    {increment : Nat → Canonical}
    (numerator denominator : Trace increment)
    (baseLower outputLower : Rational)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ Gaussian.Norm.Basic.normSq (denominator.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ Gaussian.Norm.Basic.normSq (denominator.certificate index).output)
    (current : Nat) (target : Rational) (positive : 0 < target)
    (count : Nat) :
    Trace.RequestContract
      (Reciprocal.divAutomatic numerator denominator baseLower outputLower
        baseLowerPositive outputLowerPositive baseApart outputApart)
      current target positive count :=
  Trace.bitstream_and_quadratic_law
    (Reciprocal.divAutomatic numerator denominator baseLower outputLower
      baseLowerPositive outputLowerPositive baseApart outputApart)
    current target positive count

end

end Output

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.CCL.Output

end
