module

import Purelib.Data.Gaussian.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport
import Purelib.Calculus.Jet.Quadratic.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Projection
import Purelib.Calculus.Jet.Quadratic.Arithmetic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Exact
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Arithmetic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport.Arithmetic
import Purelib.Calculus.Jet.Quadratic.Composition
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
public section

/-!
# Synchronized quadratic laws for nonterminating CCL channels

A quadratic trace is one natural-number program which returns an exact
displayed quadratic certificate at every finite stage.  All five displayed
fields share one explicit geometric refinement modulus and one rational
centre bound.  Projecting a field therefore gives an ordinary coherent CCL
name, while retaining the common index at which the quadratic identity was
proved.  This is the semantic certificate missing from a bare value/slope
pair.

The trace never packages a completed value.  A request selects one natural
index, reads five Gaussian rationals, checks the exact identity there, and
starts five persistent ordinary CCL cursors at precisely that index.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.First

open Purelib.Data in
set_option genInjectivity false in
/-- A first jet whose value, slope and remainder come from one quadratic trace.

The trace retains a common increment sequence, geometric closeness scale and center bound. Its indexed quadratic
certificates link the projected channels. -/
structure FirstJet (increment : Nat → Canonical)
  where
  /-- The common quadratic trace supplying all projected jet channels. -/ trace : Trace increment

constructive_injectivity FirstJet

namespace FirstJet

section
open Purelib.Calculus.Jet.Progressive.Quadratic.First
open Purelib.Approximation
open Purelib.Data
/-- Project the coherent output channel of the retained quadratic trace. -/
@[expose] def value {increment : Nat →
  Canonical} (jet : FirstJet increment) :
    CoherentNamed := jet.trace.outputChannel

/-- Project the coherent slope channel of the retained quadratic trace. -/
@[expose] def slope {increment : Nat →
  Canonical} (jet : FirstJet increment) :
    CoherentNamed := jet.trace.slopeChannel

/-- Project the coherent remainder channel of the retained quadratic trace. -/
@[expose] def remainder {increment : Nat →
  Canonical} (jet : FirstJet increment) :
    CoherentNamed := jet.trace.remainderChannel

end

open Purelib.Calculus.Jet.Progressive.Quadratic.First in
open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Make a constant first jet from one exact displayed quadratic certificate. -/
@[expose] def exact {increment :
  Canonical} (certificate : Certificate increment) :
    FirstJet (fun _ => increment) :=
  ⟨Trace.exact certificate⟩

section
open Purelib.Calculus.Jet.Progressive.Quadratic.First
open Purelib.Data
/-- Add two first jets over the same increment sequence using trace addition. -/
@[expose] def add {increment : Nat →
  Canonical} (left right : FirstJet increment)
    : FirstJet increment :=
  ⟨Trace.add left.trace right.trace⟩

/-- Negate a first jet using the pointwise negation of its retained trace. -/
@[expose] def neg {increment : Nat →
  Canonical} (jet : FirstJet increment) :
    FirstJet increment :=
  ⟨Trace.neg jet.trace⟩

/-- Multiply two first jets with transport evidence for their pointwise certificate products.

The transport is indexed by exactly those products at the common increment sequence. It supplies the bounds retained by
the resulting trace. -/
@[expose] def mul {increment : Nat →
  Canonical} (left right : FirstJet increment)
    (transport : Trace.Transport increment
      (fun index => (left.trace.certificate index).mul
        (right.trace.certificate index))) : FirstJet increment :=
  ⟨Trace.mul left.trace right.trace transport⟩

end

open Purelib.Calculus.Jet.Progressive.Quadratic.First in
open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Compose a first jet with indexed outer certificates and matching transport evidence.

Each outer certificate uses the inner certificate's output displacement. Increment quadrance is at most one at every
index, and the transport concerns the exact composed certificates. -/
@[expose] def compose {increment : Nat →
  Canonical} (inner : FirstJet increment)
    (outer : (index : Nat) →
      Certificate ((inner.trace.certificate index).output -
        (inner.trace.certificate index).base))
    (unit : ∀ index, Gaussian.Norm.Basic.normSq (increment index) ≤ 1)
    (transport : Trace.Transport increment
      (fun index => (inner.trace.certificate index).compose (outer index)
        (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using unit index))) : FirstJet increment :=
  ⟨Trace.compose inner.trace outer (fun index => (by
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
        using unit index)) transport⟩
end FirstJet

end Purelib.Calculus.Jet.Progressive.Quadratic.First

end
