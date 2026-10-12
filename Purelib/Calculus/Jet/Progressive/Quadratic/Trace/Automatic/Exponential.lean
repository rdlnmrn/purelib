module

import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.QuadraticJet
import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Channel
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Local.Channel

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

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Exponential

section Trace

open Purelib.Approximation.Gaussian.Sequence.Geometric in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace in
open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Build a finite exponential trace at the inner trace's output displacements.

The inner base and displacement each have quadrance at most one at every index. Finite exponential samples of these two
channels provide the base, output and slope; the residual channel supplies the exact remainder. -/
def exponentialOuterTrace {increment
  : Nat → Canonical}
    (inner : Trace increment)
    (baseUnit : ∀ index, Canonical.normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      Canonical.normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1) :
    Trace (fun index =>
      (inner.certificate index).output - (inner.certificate index).base) := by
  let movementChannel := (Channel.outputField inner).sub (Channel.baseField inner)
  let certificates := fun index =>
    Certificate.exponential
          (base := (inner.certificate index).base)
          (increment := (inner.certificate index).output - (inner.certificate index).base)
      (by rw [Gaussian.Norm.Basic.normSq_eq_canonical]; exact baseUnit index) (by
          rw [Gaussian.Norm.Basic.normSq_eq_canonical];
          exact movementUnit index) index
  let baseExp := (Channel.baseField inner).expSample (source := fun index => (inner.certificate index).base) (fun
    index => by rw [Gaussian.Norm.Basic.normSq_eq_canonical]; exact baseUnit index)
  let movementExp := movementChannel.expSample (source := fun index => (inner.certificate index).output -
    (inner.certificate index).base) (fun index => by
        rw [Gaussian.Norm.Basic.normSq_eq_canonical];
        exact movementUnit index)
  let outputExp := baseExp.mul movementExp
  let remainderChannel :=
    (outputExp.sub baseExp).sub (movementChannel.mul baseExp)
  have incrementChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index =>
      (inner.certificate index).output -
        (inner.certificate index).base) :=
    movementChannel.map (by intro index; rfl)
  have baseChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).base) :=
    baseExp.map (by intro index; rfl)
  have outputChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).output) :=
    outputExp.map (by intro index; rfl)
  have slopeChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).slope) :=
    baseExp.map (by intro index; rfl)
  have remainderChannel' :
      Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by intro index; rfl)
  exact Trace.ofTransport
    (Transport.Channel.transportOfChannels incrementChannel' baseChannel' outputChannel'
      slopeChannel' remainderChannel')

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- The outer exponential trace retains the indexed translated exponential certificate. -/
@[simp] theorem
  exponentialOuterTrace_certificate
    {increment : Nat → Canonical} (inner : Trace increment)
    (baseUnit : ∀ index, Canonical.normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      Canonical.normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1)
    (index : Nat) :
    (exponentialOuterTrace inner baseUnit movementUnit).certificate index =
      Certificate.exponential
          (base := (inner.certificate index).base)
          (increment := (inner.certificate index).output - (inner.certificate index).base)
        (by rw [Gaussian.Norm.Basic.normSq_eq_canonical]; exact baseUnit index) (by
            rw [Gaussian.Norm.Basic.normSq_eq_canonical];
            exact movementUnit index) index := rfl

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
/-- Compose an inner trace with its automatically transported finite exponential trace.

Base, output displacement and original increment each have quadrance at most one at every index. The resulting trace is
indexed by the original increment sequence. -/
def exponentialAutomatic {increment
  : Nat → Canonical}
    (inner : Trace increment)
    (baseUnit : ∀ index, Canonical.normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      Canonical.normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1) :
    Trace increment :=
  Arithmetic.composeAutomatic inner
    (exponentialOuterTrace inner baseUnit movementUnit) incrementUnit

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Each automatic exponential certificate is the inner certificate composed with its finite exponential certificate. -/
@[simp] theorem
  exponentialAutomatic_certificate
    {increment : Nat → Canonical} (inner : Trace increment)
    (baseUnit : ∀ index, Canonical.normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      Canonical.normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1)
    (index : Nat) :
    Trace.certificate
        (exponentialAutomatic inner baseUnit movementUnit incrementUnit)
        index =
      (inner.certificate index).compose
        (Certificate.exponential
          (base := (inner.certificate index).base)
          (increment := (inner.certificate index).output - (inner.certificate index).base)
          (by rw [Gaussian.Norm.Basic.normSq_eq_canonical]; exact baseUnit index) (by
              rw [Gaussian.Norm.Basic.normSq_eq_canonical];
              exact movementUnit index) index)
        (incrementUnit index) := rfl
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Exponential

end
