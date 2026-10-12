module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Reciprocal
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Exponential
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Arithmetic
import Purelib.Data.Rat.Fraction
public import Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Program)
open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# One certified finite program for progressive quadratic CCL calculus

The lower trace modules construct the arithmetic and analytic certificates.
This file packages those constructors into one indexed finite program.  The
index is the actual semantic `Trace`, so a program cannot pair unrelated value
and slope names: every node computes one common increment, base, output,
slope, remainder, and rational quadratic factor.

Partial nodes store their displayed lower-quadrance or disk evidence in the
constructor.  The total decision wrappers expose a precise missing
certificate.  Finally, the strengthened request contract combines the
quadratic law with persistent word extension, exact raw-parser semantics, and
the requested projective-cylinder diameter for every one of the five live CCL
channels.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
namespace Calculation

open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic in
open Purelib.Data in
/-- Package an existing quadratic trace as a source calculation. -/
def source {increment : Nat →
  Canonical} (trace : Trace increment) :
    Calculation increment := ⟨trace, Program.source trace⟩

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic in
open Purelib.Data in
/-- Scale the retained trace and extend its construction evidence by a scalar node. -/
def scale (scalar :
  Canonical) {increment : Nat → Canonical}
    (calculation : Calculation increment) : Calculation increment :=
  ⟨Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic.scaleAutomatic
      scalar calculation.trace,
    Program.scale scalar calculation.program⟩

section
open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
open Purelib.Data
/-- Add two calculations over the same increments and retain both input programs. -/
def add {increment : Nat →
  Canonical}
    (left right : Calculation increment) : Calculation increment :=
  ⟨Trace.add left.trace right.trace,
    Program.add left.program right.program⟩

/-- Negate the retained trace and wrap its construction evidence in a negation node. -/
def neg {increment : Nat →
  Canonical} (calculation : Calculation increment) :
    Calculation increment :=
  ⟨Trace.neg calculation.trace,
    Program.neg calculation.program⟩

end

open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic in
open Purelib.Data in
/-- Subtract calculations by adding the left calculation to the negated right calculation. -/
def sub {increment : Nat →
  Canonical}
    (left right : Calculation increment) : Calculation increment :=
  add left (neg right)

section
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic
open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
open Purelib.Data
/-- Multiply the retained traces using automatic transport and retain both input programs. -/
def mul {increment : Nat →
  Canonical}
    (left right : Calculation increment) : Calculation increment :=
  ⟨Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic.mulAutomatic
      left.trace right.trace,
    Program.mul left.program right.program⟩

/-- Invert a calculation using uniform positive bounds on base and output quadrances.

The supplied bounds hold at every trace index. Automatic reciprocal transport computes the resulting trace, while the
program node retains the original calculation and apartness evidence. -/
def reciprocal {increment : Nat →
  Canonical}
    (calculation : Calculation increment)
    (baseLower outputLower : Rat.Fraction.Rational)
    (basePositive : 0 < baseLower) (outputPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ Gaussian.Norm.Basic.normSq (calculation.trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ Gaussian.Norm.Basic.normSq (calculation.trace.certificate index).output) :
    Calculation increment :=
  ⟨Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Reciprocal.reciprocalAutomatic
      calculation.trace baseLower outputLower basePositive outputPositive
        baseApart outputApart,
    Program.reciprocal calculation.program baseLower outputLower basePositive
      outputPositive (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using baseApart index) (fun
        index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using outputApart index)⟩

/-- Divide two calculations with uniform positive quadrance bounds for the denominator.

Both traces share the increment sequence. The denominator's base and output satisfy the retained positive lower bounds
at every index, and the resulting program retains both inputs. -/
def div {increment : Nat →
  Canonical}
    (numerator denominator : Calculation increment)
    (baseLower outputLower : Rat.Fraction.Rational)
    (basePositive : 0 < baseLower) (outputPositive : 0 < outputLower)
    (baseApart : ∀ index,
      baseLower ≤ Gaussian.Norm.Basic.normSq (denominator.trace.certificate index).base)
    (outputApart : ∀ index,
      outputLower ≤ Gaussian.Norm.Basic.normSq (denominator.trace.certificate index).output) :
    Calculation increment :=
  ⟨Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Reciprocal.divAutomatic
      numerator.trace denominator.trace baseLower outputLower basePositive
        outputPositive baseApart outputApart,
    Program.div numerator.program denominator.program baseLower outputLower
      basePositive outputPositive (fun index => by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using baseApart index)
      (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using outputApart index)⟩

/-- Compose calculations whose outer increments equal the inner output displacements.

The common original increment has quadrance at most one at every index. Automatic composition computes the trace, and
the program node records both indexed inputs and the bound. -/
def compose {increment : Nat →
  Canonical}
    (inner : Calculation increment)
    (outer : Calculation (fun index =>
      (inner.trace.certificate index).output -
        (inner.trace.certificate index).base))
    (incrementUnit : ∀ index, Gaussian.Norm.Basic.normSq (increment index) ≤ 1) :
    Calculation increment :=
  ⟨Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic.composeAutomatic
      inner.trace outer.trace (fun index => by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using incrementUnit index),
    Program.compose inner.program outer.program (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using incrementUnit index)⟩

/-- Compose a calculation with the finite exponential construction under unit-disk bounds.

The base, output displacement and increment have quadrance at most one at every index. The computed trace and its
program node retain these exact premises. -/
def exponential {increment : Nat →
  Canonical}
    (inner : Calculation increment)
    (baseUnit : ∀ index, Gaussian.Norm.Basic.normSq (inner.trace.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      Gaussian.Norm.Basic.normSq ((inner.trace.certificate index).output -
        (inner.trace.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Gaussian.Norm.Basic.normSq (increment index) ≤ 1) :
    Calculation increment :=
  ⟨Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Exponential.exponentialAutomatic
      inner.trace (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using baseUnit index) (fun index
        => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using movementUnit index) (fun index => by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using incrementUnit index),
    Program.exponential inner.program (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using baseUnit index)
      (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using movementUnit index)
      (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using incrementUnit index)⟩

/-- Compose a calculation with the finite reduced-logarithm construction.

Output displacement has quadrance at most one ninth, and increment quadrance is at most one at every index. The result
retains the constructed trace and its indexed program evidence. -/
def reducedLog {increment : Nat →
  Canonical}
    (inner : Calculation increment)
    (movementDisk : ∀ index,
      Gaussian.Norm.Basic.normSq ((inner.trace.certificate index).output -
        (inner.trace.certificate index).base) ≤ 1 / 9)
    (incrementUnit : ∀ index, Gaussian.Norm.Basic.normSq (increment index) ≤ 1) :
    Calculation increment :=
  ⟨Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog.reducedLogAutomatic
      inner.trace movementDisk incrementUnit,
    Program.reducedLog inner.program (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using movementDisk index) (fun index => by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using incrementUnit index)⟩

/-- Build the finite sine calculation with unit-disk evidence for the rotated trace.

The rotated base and output displacement have quadrance at most one, as does the original increment at every index. The
program retains the source calculation and these bounds. -/
def sine {increment : Nat →
  Canonical} (inner : Calculation increment)
    (rotatedBaseUnit : ∀ index,
      Gaussian.Norm.Basic.normSq
        ((Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric.rotateAutomatic
          inner.trace).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      Gaussian.Norm.Basic.normSq
        (((Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric.rotateAutomatic
            inner.trace).certificate index).output -
          ((Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric.rotateAutomatic
            inner.trace).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Gaussian.Norm.Basic.normSq (increment index) ≤ 1) :
    Calculation increment :=
  ⟨Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric.sineAutomatic
      inner.trace (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using rotatedBaseUnit index)
        (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using rotatedMovementUnit index) (fun
        index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using incrementUnit index),
    Program.sine inner.program (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using rotatedBaseUnit index) (fun index => by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using rotatedMovementUnit index)
      (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using incrementUnit index)⟩

/-- Build the finite cosine calculation with unit-disk evidence for the rotated trace.

The rotated base and output displacement have quadrance at most one, as does the original increment at every index. The
program retains the source calculation and these bounds. -/
def cosine {increment : Nat →
  Canonical} (inner : Calculation increment)
    (rotatedBaseUnit : ∀ index,
      Gaussian.Norm.Basic.normSq
        ((Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric.rotateAutomatic
          inner.trace).certificate index).base ≤ 1)
    (rotatedMovementUnit : ∀ index,
      Gaussian.Norm.Basic.normSq
        (((Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric.rotateAutomatic
            inner.trace).certificate index).output -
          ((Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric.rotateAutomatic
            inner.trace).certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Gaussian.Norm.Basic.normSq (increment index) ≤ 1) :
    Calculation increment :=
  ⟨Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric.cosineAutomatic
      inner.trace (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using rotatedBaseUnit index)
        (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using rotatedMovementUnit index) (fun
        index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using incrementUnit index),
    Program.cosine inner.program (fun index => by
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
          using rotatedBaseUnit index) (fun index => by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
            using rotatedMovementUnit index)
      (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using incrementUnit index)⟩
end

end Calculation

end Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic

end
