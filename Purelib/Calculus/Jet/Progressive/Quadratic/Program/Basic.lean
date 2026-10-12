module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Arithmetic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Exponential
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Reciprocal
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Trigonometric
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

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

namespace Purelib.Calculus.Jet.Progressive.Quadratic

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
/-- Finite construction evidence indexed by the exact resulting quadratic trace.

Each arithmetic or finite analytic constructor retains evidence for its input programs and any required disk or positive
quadrance bounds. The output index is the trace computed by that constructor. -/
inductive Program : {increment : Nat →
  Canonical} → Trace increment → Prop
  /-- Register an already certified trace as a source program. -/ | source (trace : Trace increment) :
    Program trace
  /-- Retain an input program and record scalar multiplication of its trace. -/ | scale (scalar :
    Canonical) {trace : Trace increment} :
      Program trace →
      Program
        (Trace.Automatic.Arithmetic.scaleAutomatic
          scalar trace)
  /-- Retain both input programs and record addition of their traces. -/ | add {left right : Trace increment} :
    Program left →
    Program right →
      Program (Trace.add left right)
  /-- Retain the input program and record negation of its trace. -/ | neg {trace : Trace increment} :
    Program trace →
      Program (Trace.neg trace)
  /-- Retain both input programs and record their automatically transported product. -/ | mul {left right : Trace
    increment} : Program left →
    Program right →
      Program
        (Trace.Automatic.Arithmetic.mulAutomatic
          left right)
  /-- Record reciprocal construction with uniform positive bounds for base and output quadrances. -/ | reciprocal {trace
    : Trace increment} : Program trace →
      (baseLower outputLower : Rat.Fraction.Rational) →
      (basePositive : 0 < baseLower) →
      (outputPositive : 0 < outputLower) →
      (baseApart : ∀ index,
        baseLower ≤ Canonical.normSq (trace.certificate index).base) →
      (outputApart : ∀ index,
        outputLower ≤ Canonical.normSq (trace.certificate index).output) →
      Program
        (Trace.Automatic.Reciprocal.reciprocalAutomatic
          trace baseLower outputLower basePositive outputPositive (fun index => by
              simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
                using baseApart index)
            (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using outputApart index))
  /-- Record division with uniform positive bounds for the denominator's base and output quadrances. -/ | div {numerator
    denominator : Trace increment} :
      Program numerator →
        Program denominator →
      (baseLower outputLower : Rat.Fraction.Rational) →
      (basePositive : 0 < baseLower) →
      (outputPositive : 0 < outputLower) →
      (baseApart : ∀ index,
        baseLower ≤ Canonical.normSq (denominator.certificate index).base) →
      (outputApart : ∀ index,
        outputLower ≤ Canonical.normSq (denominator.certificate index).output) →
      Program
        (Trace.Automatic.Reciprocal.divAutomatic
          numerator denominator baseLower outputLower basePositive
            outputPositive (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using baseApart index)
              (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using outputApart index))
  /-- Record composition with matching outer increments and the unit increment bound. -/ | compose {inner : Trace
    increment}
      {outer : Trace (fun index =>
        (inner.certificate index).output - (inner.certificate index).base)} :
      Program inner →
        Program outer →
      (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) →
      Program
        (Trace.Automatic.Arithmetic.composeAutomatic
          inner outer incrementUnit)
  /-- Record finite exponential composition with unit bounds for base, movement and increment. -/ | exponential {inner :
    Trace increment} : Program inner →
      (baseUnit : ∀ index, Canonical.normSq (inner.certificate index).base ≤ 1) →
      (movementUnit : ∀ index,
        Canonical.normSq ((inner.certificate index).output -
          (inner.certificate index).base) ≤ 1) →
      (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) →
      Program
        (Trace.Automatic.Exponential.exponentialAutomatic
          inner baseUnit movementUnit (fun index => by
              simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
                using incrementUnit index))
  /-- Record finite reduced-logarithm composition with movement quadrance at most one ninth. -/ | reducedLog {inner :
    Trace increment} : Program inner →
      (movementDisk : ∀ index,
        Canonical.normSq ((inner.certificate index).output -
          (inner.certificate index).base) ≤ 1 / 9) →
      (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) →
      Program
        (Trace.Automatic.ReducedLog.reducedLogAutomatic
          inner (fun index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using movementDisk index) (fun
            index => by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using incrementUnit index))
  /-- Record finite sine construction with unit bounds for the rotated base and movement. -/ | sine {inner : Trace
    increment} : Program inner →
      (rotatedBaseUnit : ∀ index,
        Canonical.normSq
          ((Trace.Automatic.Trigonometric.rotateAutomatic
            inner).certificate index).base ≤ 1) →
      (rotatedMovementUnit : ∀ index,
        Canonical.normSq
          (((Trace.Automatic.Trigonometric.rotateAutomatic
              inner).certificate index).output -
            ((Trace.Automatic.Trigonometric.rotateAutomatic
              inner).certificate index).base) ≤ 1) →
      (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) →
      Program
        (Trace.Automatic.Trigonometric.sineAutomatic
          inner rotatedBaseUnit rotatedMovementUnit incrementUnit)
  /-- Record finite cosine construction with unit bounds for the rotated base and movement. -/ | cosine {inner : Trace
    increment} : Program inner →
      (rotatedBaseUnit : ∀ index,
        Canonical.normSq
          ((Trace.Automatic.Trigonometric.rotateAutomatic
            inner).certificate index).base ≤ 1) →
      (rotatedMovementUnit : ∀ index,
        Canonical.normSq
          (((Trace.Automatic.Trigonometric.rotateAutomatic
              inner).certificate index).output -
            ((Trace.Automatic.Trigonometric.rotateAutomatic
              inner).certificate index).base) ≤ 1) →
      (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) →
      Program
        (Trace.Automatic.Trigonometric.cosineAutomatic
          inner rotatedBaseUnit rotatedMovementUnit incrementUnit)

namespace Program.Basic

set_option genInjectivity false in
open Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic in
open Purelib.Data in
/-- A quadratic trace paired with finite construction evidence for that exact trace.

The increment sequence is a type index. The program field refers to the retained trace, including its certificates and
common bounds. -/
structure Calculation (increment : Nat →
  Canonical) where
  /-- The retained quadratic trace at the indexed increment sequence. -/ trace : Trace increment
  /-- Finite construction evidence indexed by the retained trace. -/ program : Program trace

constructive_injectivity Calculation

end Program.Basic

end Purelib.Calculus.Jet.Progressive.Quadratic

end
