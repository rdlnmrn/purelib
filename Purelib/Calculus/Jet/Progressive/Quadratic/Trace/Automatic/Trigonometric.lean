module

public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Arithmetic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Exponential
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

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

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric

section Trace

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic
open Purelib.Data
/-- Multiply a quadratic trace by the imaginary unit with automatic transport. -/
def rotateAutomatic {increment :
  Nat → Canonical} (inner : Trace increment) :
    Trace increment :=
  Arithmetic.scaleAutomatic Gaussian.Constants.imaginaryUnit inner

/-- Construct the finite sine trace from positive and negative imaginary-phase exponentials.

The rotated base and displacement have quadrance at most one, and so does the original increment. Subtracting the two
finite exponential traces and scaling by the inverse of twice the imaginary unit gives the result. -/
def sineAutomatic {increment : Nat
  → Canonical} (inner : Trace increment)
    (rotatedBaseUnit : ∀ index,
      Canonical.normSq ((rotateAutomatic inner).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      Canonical.normSq (((rotateAutomatic inner).certificate index).output -
        ((rotateAutomatic inner).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) :
    Trace increment := by
  let rotated := rotateAutomatic inner
  let negativeRotated := Trace.neg
    rotated
  have negativeBaseUnit : ∀ index,
      Canonical.normSq (negativeRotated.certificate index).base ≤ 1 := by
    intro index
    change Canonical.normSq (-(rotated.certificate index).base) ≤ 1
    rw [Canonical.normSq_neg]
    exact rotatedBaseUnit index
  have negativeMovementUnit : ∀ index,
      Canonical.normSq ((negativeRotated.certificate index).output -
        (negativeRotated.certificate index).base) ≤ 1 := by
    intro index
    change Canonical.normSq
      (-(rotated.certificate index).output -
        -(rotated.certificate index).base) ≤ 1
    have identity :
        -(rotated.certificate index).output -
            -(rotated.certificate index).base =
          -((rotated.certificate index).output -
            (rotated.certificate index).base) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1
    rw [identity, Canonical.normSq_neg]
    exact rotatedMovementUnit index
  let positivePhase := Exponential.exponentialAutomatic rotated rotatedBaseUnit
    rotatedMovementUnit incrementUnit
  let negativePhase := Exponential.exponentialAutomatic negativeRotated negativeBaseUnit
    negativeMovementUnit incrementUnit
  exact Arithmetic.scaleAutomatic Gaussian.Constants.inverseTwoI
    (Trace.add positivePhase
      (Trace.neg negativePhase))

/-- Construct the finite cosine trace from positive and negative imaginary-phase exponentials.

The rotated base and displacement have quadrance at most one, and so does the original increment. The result is half the
sum of the two automatically transported exponential traces. -/
def cosineAutomatic {increment :
  Nat → Canonical} (inner : Trace increment)
    (rotatedBaseUnit : ∀ index,
      Canonical.normSq ((rotateAutomatic inner).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      Canonical.normSq (((rotateAutomatic inner).certificate index).output -
        ((rotateAutomatic inner).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) :
    Trace increment := by
  let rotated := rotateAutomatic inner
  let negativeRotated := Trace.neg
    rotated
  have negativeBaseUnit : ∀ index,
      Canonical.normSq (negativeRotated.certificate index).base ≤ 1 := by
    intro index
    change Canonical.normSq (-(rotated.certificate index).base) ≤ 1
    rw [Canonical.normSq_neg]
    exact rotatedBaseUnit index
  have negativeMovementUnit : ∀ index,
      Canonical.normSq ((negativeRotated.certificate index).output -
        (negativeRotated.certificate index).base) ≤ 1 := by
    intro index
    change Canonical.normSq
      (-(rotated.certificate index).output -
        -(rotated.certificate index).base) ≤ 1
    have identity :
        -(rotated.certificate index).output -
            -(rotated.certificate index).base =
          -((rotated.certificate index).output -
            (rotated.certificate index).base) := by
      apply Gaussian.Basic.ext <;>
        simp only [Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1
    rw [identity, Canonical.normSq_neg]
    exact rotatedMovementUnit index
  let positivePhase := Exponential.exponentialAutomatic rotated rotatedBaseUnit
    rotatedMovementUnit incrementUnit
  let negativePhase := Exponential.exponentialAutomatic negativeRotated negativeBaseUnit
    negativeMovementUnit incrementUnit
  exact Arithmetic.scaleAutomatic Gaussian.Constants.half
    (Trace.add positivePhase
      negativePhase)
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric

end
