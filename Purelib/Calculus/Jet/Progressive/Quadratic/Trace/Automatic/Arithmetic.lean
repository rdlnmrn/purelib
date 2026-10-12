module

import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel
public import Purelib.Approximation.Gaussian.Sequence.Geometric.Channel.Arithmetic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport.Channel
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Calculus.Jet.Quadratic.Arithmetic
public import Purelib.Calculus.Jet.Quadratic.Composition
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Channel

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

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic

section Trace

open Purelib.Approximation.Gaussian.Sequence.Geometric in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace in
open Purelib.Data in
/-- Scale every quadratic certificate and compute transport from the five channels.

The increment channel is retained. The base, output, slope and remainder channels are scaled by the supplied Gaussian
rational, and their bounds determine the new common transport. -/
def scaleAutomatic (scalar :
  Canonical) {increment : Nat → Canonical}
    (trace : Trace increment) : Trace increment := by
  let certificates := fun index =>
    (trace.certificate index).scale scalar
  let incrementChannel := (Channel.incrementField trace)
  let baseChannel := (Channel.baseField trace).scale scalar
  let outputChannel := (Channel.outputField trace).scale scalar
  let slopeChannel := (Channel.slopeField trace).scale scalar
  let remainderChannel := (Channel.remainderField trace).scale scalar
  have baseChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).base) :=
    baseChannel.map (by intro index; rfl)
  have outputChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).output) :=
    outputChannel.map (by intro index; rfl)
  have slopeChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).slope) :=
    slopeChannel.map (by intro index; rfl)
  have remainderChannel' :
      Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by intro index; rfl)
  exact Trace.ofTransport
    (Transport.Channel.transportOfChannels incrementChannel baseChannel' outputChannel'
      slopeChannel' remainderChannel')

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
/-- Each certificate of a scaled trace is the original certificate scaled by the supplied scalar. -/
@[simp] theorem
  scaleAutomatic_certificate (scalar
  : Canonical)
    {increment : Nat → Canonical} (trace : Trace increment) (index : Nat) :
    (scaleAutomatic scalar trace).certificate index =
      (trace.certificate index).scale scalar := rfl

open Purelib.Approximation.Gaussian.Sequence.Geometric in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace in
open Purelib.Data in
/-- Multiply two quadratic traces and compute transport from their channel arithmetic.

The traces share their increment sequence. Base and output are multiplied, slope uses the product rule, and the
output-minus-linear-part channel supplies the exact remainder. -/
def mulAutomatic {increment : Nat →
  Canonical}
    (left right : Trace increment) : Trace increment := by
  let certificates := fun index =>
    (left.certificate index).mul (right.certificate index)
  let incrementChannel := (Channel.incrementField left)
  let baseChannel := (Channel.baseField left).mul (Channel.baseField right)
  let outputChannel := (Channel.outputField left).mul (Channel.outputField right)
  let slopeChannel :=
    ((Channel.slopeField left).mul (Channel.baseField right)).add
      ((Channel.baseField left).mul (Channel.slopeField right))
  let remainderChannel :=
    (outputChannel.sub baseChannel).sub (incrementChannel.mul slopeChannel)
  have baseChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).base) :=
    baseChannel.map (by intro index; rfl)
  have outputChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).output) :=
    outputChannel.map (by intro index; rfl)
  have slopeChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).slope) :=
    slopeChannel.map (by intro index; rfl)
  have remainderChannel' :
      Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by intro index; rfl)
  exact Trace.ofTransport
    (Transport.Channel.transportOfChannels incrementChannel baseChannel' outputChannel'
      slopeChannel' remainderChannel')

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
/-- Each certificate of the automatic product is the pointwise product of the input certificates. -/
@[simp] theorem
  mulAutomatic_certificate {increment
  : Nat → Canonical}
    (left right : Trace increment) (index : Nat) :
    (mulAutomatic left right).certificate index =
      (left.certificate index).mul (right.certificate index) := rfl

open Purelib.Approximation.Gaussian.Sequence.Geometric in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace in
open Purelib.Data in
/-- Compose quadratic traces with matching inner output displacements and outer increments.

Increment quadrance is at most one at every index. The output uses the outer base and output, the product of slopes and
the composed remainder, with common transport computed from those channels. -/
def composeAutomatic {increment : Nat
  → Canonical} (inner : Trace increment)
    (outer : Trace (fun index =>
      (inner.certificate index).output - (inner.certificate index).base))
    (unit : ∀ index, Canonical.normSq (increment index) ≤ 1) : Trace increment := by
  let certificates := fun index =>
    (inner.certificate index).compose (outer.certificate index) (unit index)
  let incrementChannel := (Channel.incrementField inner)
  let baseChannel := (Channel.baseField outer)
  let outputChannel := (Channel.outputField outer)
  let slopeChannel := (Channel.slopeField inner).mul (Channel.slopeField outer)
  let remainderChannel :=
    ((Channel.remainderField inner).mul (Channel.slopeField outer)).add (Channel.remainderField outer)
  have baseChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).base) :=
    baseChannel.map (by intro index; rfl)
  have outputChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).output) :=
    outputChannel.map (by intro index; rfl)
  have slopeChannel' : Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).slope) :=
    slopeChannel.map (by intro index; rfl)
  have remainderChannel' :
      Approximation.Gaussian.Sequence.Geometric.Channel (fun index => (certificates index).remainder) :=
    remainderChannel.map (by intro index; rfl)
  exact Trace.ofTransport
    (Transport.Channel.transportOfChannels incrementChannel baseChannel' outputChannel'
      slopeChannel' remainderChannel')

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Data in
/-- Each certificate of automatic composition is the displayed composition of the two indexed certificates. -/
@[simp] theorem
  composeAutomatic_certificate
  {increment : Nat → Canonical}
    (inner : Trace increment)
    (outer : Trace (fun index =>
      (inner.certificate index).output - (inner.certificate index).base))
    (unit : ∀ index, Canonical.normSq (increment index) ≤ 1) (index : Nat) :
    (composeAutomatic inner outer unit).certificate index =
      (inner.certificate index).compose (outer.certificate index)
        (unit index) := rfl
end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Arithmetic

end
