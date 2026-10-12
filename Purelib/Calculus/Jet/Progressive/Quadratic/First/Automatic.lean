module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Calculus.Jet.Progressive.Quadratic.First
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Reciprocal
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Exponential
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)
open Purelib.Data.Gaussian.Basic (Canonical)

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

namespace Purelib.Calculus.Jet.Progressive.Quadratic.First.Automatic

namespace FirstJet

section
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic
open Purelib.Calculus.Jet.Progressive.Quadratic.First
open Purelib.Data
/-- Scale a first jet by a Gaussian rational with automatically computed transport. -/
def scaleAutomatic (scalar :
  Canonical) {increment : Nat → Canonical}
    (jet : FirstJet increment) : FirstJet increment :=
  ⟨Trace.Automatic.Arithmetic.scaleAutomatic scalar jet.trace⟩

/-- Multiply first jets over the same increment sequence with automatically computed transport. -/
def mulAutomatic {increment : Nat →
  Canonical}
    (left right : FirstJet increment) : FirstJet increment :=
  ⟨Trace.Automatic.Arithmetic.mulAutomatic left.trace right.trace⟩

/-- Invert a first jet using uniform positive base and output quadrance bounds.

The supplied rational lower bounds hold at every index. Reciprocal transport is computed from those bounds and the
original trace's common estimates. -/
def reciprocalAutomatic {increment : Nat →
  Canonical}
    (jet : FirstJet increment) (baseLower outputLower : Rat.Fraction.Rational)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ Canonical.normSq (jet.trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ Canonical.normSq (jet.trace.certificate index).output) :
    FirstJet increment :=
  ⟨Trace.Automatic.Reciprocal.reciprocalAutomatic jet.trace baseLower outputLower
    baseLowerPositive outputLowerPositive (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using baseApart index)
      (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using outputApart index)⟩

/-- Divide first jets using uniform positive quadrance bounds for the denominator.

The jets share their increment sequence. The denominator's base and output bounds determine the automatic reciprocal
transport used in the quotient. -/
def divAutomatic {increment : Nat →
  Canonical}
    (numerator denominator : FirstJet increment)
    (baseLower outputLower : Rat.Fraction.Rational)
    (baseLowerPositive : 0 < baseLower)
    (outputLowerPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ Canonical.normSq (denominator.trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ Canonical.normSq (denominator.trace.certificate index).output) :
    FirstJet increment :=
  ⟨Trace.Automatic.Reciprocal.divAutomatic numerator.trace denominator.trace
    baseLower outputLower
    baseLowerPositive outputLowerPositive (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using baseApart index)
      (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using outputApart index)⟩

/-- Compose first jets whose outer increments match the inner output displacement.

The original increment has quadrance at most one at every index. The trace constructor computes transport for the
resulting composed certificates. -/
def composeAutomatic {increment : Nat →
  Canonical}
    (inner : FirstJet increment)
    (outer : FirstJet (fun index =>
      (inner.trace.certificate index).output -
        (inner.trace.certificate index).base))
    (unit : ∀ index, Canonical.normSq (increment index) ≤ 1) : FirstJet increment :=
  ⟨Trace.Automatic.Arithmetic.composeAutomatic inner.trace outer.trace unit⟩

/-- Form the finite exponential of a first jet with automatically computed transport.

Base, output displacement and increment each have quadrance at most one at every index. The supplied disk evidence is
passed to the indexed exponential trace construction. -/
def exponentialAutomatic {increment : Nat →
  Canonical}
    (inner : FirstJet increment)
    (baseUnit : ∀ index,
      Canonical.normSq (inner.trace.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      Canonical.normSq ((inner.trace.certificate index).output -
        (inner.trace.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) :
    FirstJet increment :=
  ⟨Trace.Automatic.Exponential.exponentialAutomatic inner.trace baseUnit
    movementUnit (fun index => by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
        using incrementUnit index)⟩

/-- Form the finite reduced logarithm of a first jet with automatically computed transport.

Output displacement has quadrance at most one ninth, and increment quadrance is at most one at each index. These bounds
fix the local logarithm construction. -/
def reducedLogAutomatic {increment : Nat →
  Canonical}
    (inner : FirstJet increment)
    (movementDisk : ∀ index,
      Canonical.normSq ((inner.trace.certificate index).output -
        (inner.trace.certificate index).base) ≤ 1 / 9)
    (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) :
    FirstJet increment :=
  ⟨Trace.Automatic.ReducedLog.reducedLogAutomatic inner.trace (fun index => by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
        using movementDisk index) (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using incrementUnit index)⟩

/-- Form the finite sine of a first jet under the rotated unit-disk conditions.

The rotated trace's base and output displacement have quadrance at most one, as does the original increment at every
index. Its transport is computed by the sine trace constructor. -/
def sineAutomatic {increment : Nat →
  Canonical}
    (inner : FirstJet increment)
    (rotatedBaseUnit : ∀ index,
      Canonical.normSq
        ((Trace.Automatic.Trigonometric.rotateAutomatic inner.trace).certificate
        index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      Canonical.normSq
        (((Trace.Automatic.Trigonometric.rotateAutomatic inner.trace).certificate
        index).output -
        ((Trace.Automatic.Trigonometric.rotateAutomatic inner.trace).certificate
          index).base) ≤ 1)
    (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) :
    FirstJet increment :=
  ⟨Trace.Automatic.Trigonometric.sineAutomatic inner.trace rotatedBaseUnit
    rotatedMovementUnit
    incrementUnit⟩

/-- Form the finite cosine of a first jet under the rotated unit-disk conditions.

The rotated trace's base and output displacement have quadrance at most one, as does the original increment at every
index. Its transport is computed by the cosine trace constructor. -/
def cosineAutomatic {increment : Nat →
  Canonical}
    (inner : FirstJet increment)
    (rotatedBaseUnit : ∀ index,
      Canonical.normSq
        ((Trace.Automatic.Trigonometric.rotateAutomatic inner.trace).certificate
        index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      Canonical.normSq
        (((Trace.Automatic.Trigonometric.rotateAutomatic inner.trace).certificate
        index).output -
        ((Trace.Automatic.Trigonometric.rotateAutomatic inner.trace).certificate
          index).base) ≤ 1)
    (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) :
    FirstJet increment :=
  ⟨Trace.Automatic.Trigonometric.cosineAutomatic inner.trace rotatedBaseUnit
    rotatedMovementUnit
    incrementUnit⟩

end

end FirstJet

end Purelib.Calculus.Jet.Progressive.Quadratic.First.Automatic

end
