module
import Purelib.Data.Gaussian.Basic
public import Purelib.Approximation.Gaussian.Exponential.Horner.QuadraticJet
public import Purelib.Approximation.Gaussian.Logarithm.Local.QuadraticJet
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport
import Purelib.Calculus.Jet.Quadratic.Basic
public import Purelib.Calculus.Jet.Quadratic.Arithmetic
public import Purelib.Calculus.Jet.Quadratic.Composition

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

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

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace
section Trace

section
open Purelib.Data
/-- Package pointwise certificate products with their supplied common transport.

The transport is indexed by the actual product certificates at the shared increment sequence, and its retained estimates
become the resulting trace's estimates. -/
def mul {increment : Nat → Canonical}
  (left right : Trace increment)
    (transport : Trace.Transport increment
      (fun index => (left.certificate index).mul (right.certificate index))) :
    Trace increment :=
  Trace.ofTransport transport

/-- Package pointwise reciprocal certificates with their supplied transport.

At every index, the displayed base and output must be nonzero. The transport concerns exactly the reciprocal
certificates formed with those witnesses. -/
def reciprocal {increment : Nat →
  Canonical} (trace : Trace increment)
    (baseNonzero : ∀ index, (trace.certificate index).base ≠ 0)
    (outputNonzero : ∀ index, (trace.certificate index).output ≠ 0)
    (transport : Trace.Transport increment
      (fun index => (trace.certificate index).reciprocal
        (baseNonzero index) (outputNonzero index))) : Trace increment :=
  Trace.ofTransport transport

/-- Package pointwise quotient certificates with their supplied transport.

The denominator has nonzero base and output at every index. The transport is indexed by the quotient certificates
computed from the two original traces and those witnesses. -/
def div {increment : Nat → Canonical}
  (numerator denominator : Trace increment)
    (baseNonzero : ∀ index, (denominator.certificate index).base ≠ 0)
    (outputNonzero : ∀ index, (denominator.certificate index).output ≠ 0)
    (transport : Trace.Transport increment
      (fun index => (numerator.certificate index).div
        (denominator.certificate index) (baseNonzero index)
          (outputNonzero index))) : Trace increment :=
  Trace.ofTransport transport

section
open Purelib.Calculus.Jet.Quadratic.Basic
/-- Package pointwise certificate composition with its supplied transport.

Each outer certificate is indexed by the inner output displacement. Increment quadrance is at most one at every stage,
and the supplied transport bounds exactly the resulting composed certificates. -/
def compose {increment : Nat →
  Canonical} (inner : Trace increment)
    (outer : (index : Nat) →
      Certificate ((inner.certificate index).output -
        (inner.certificate index).base))
    (unit : ∀ index, Canonical.normSq (increment index) ≤ 1)
    (transport : Trace.Transport increment
      (fun index => (inner.certificate index).compose (outer index)
        (unit index))) : Trace increment :=
  Trace.ofTransport transport

/-- Package finite exponential certificate composition with explicit disk and transport evidence.

At every stage the inner base, inner displacement and common increment have quadrance at most one. The exponential
certificate uses that stage's natural index as its finite depth, and the transport concerns the resulting composed
sequence. -/
def exponential {increment : Nat →
  Canonical} (inner : Trace increment)
    (baseUnit : ∀ index, Canonical.normSq (inner.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      Canonical.normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1)
    (transport : Trace.Transport increment
      (fun index => (inner.certificate index).compose
        (Certificate.exponential
          (base := (inner.certificate index).base)
          (increment := (inner.certificate index).output - (inner.certificate index).base)
          (by
            rw [Gaussian.Norm.Basic.normSq_eq_canonical]; exact baseUnit index)
          (by
            rw [Gaussian.Norm.Basic.normSq_eq_canonical]; exact movementUnit index) index)
        (incrementUnit index))) : Trace increment :=
  Trace.ofTransport transport

/-- Package finite logarithm-of-one-plus certificate composition with supplied transport.

The inner displacement has quadrance at most one quarter, and the common increment has quadrance at most one at every
stage. The finite logarithm certificate uses the same stage index as its depth. -/
def logarithm1p {increment : Nat →
  Canonical} (inner : Trace increment)
    (movementDisk : ∀ index,
      Canonical.normSq ((inner.certificate index).output -
        (inner.certificate index).base) ≤ 1 / 4)
    (incrementUnit : ∀ index, Canonical.normSq (increment index) ≤ 1)
    (transport : Trace.Transport increment
      (fun index => (inner.certificate index).compose
        (Certificate.logarithm1p
          (increment := (inner.certificate index).output - (inner.certificate index).base)
          (by rw [Gaussian.Norm.Basic.normSq_eq_canonical]; exact movementDisk index) index)
        (incrementUnit index))) : Trace increment :=
  Trace.ofTransport transport

end

/-- Each certificate of a transported product trace is the pointwise certificate product. -/
@[simp] theorem mul_certificate {increment : Nat →
  Canonical}
    (left right : Trace increment)
    (transport : Trace.Transport increment
      (fun index => (left.certificate index).mul (right.certificate index)))
    (index : Nat) :
    (mul left right transport).certificate index =
      (left.certificate index).mul (right.certificate index) := rfl

open Purelib.Calculus.Jet.Quadratic.Basic in
/-- Each certificate of a transported composition is the displayed pointwise composition. -/
@[simp] theorem compose_certificate {increment : Nat
  → Canonical}
    (inner : Trace increment)
    (outer : (index : Nat) →
      Certificate ((inner.certificate index).output -
        (inner.certificate index).base))
    (unit : ∀ index, Canonical.normSq (increment index) ≤ 1)
    (transport : Trace.Transport increment
      (fun index => (inner.certificate index).compose (outer index)
        (unit index))) (index : Nat) :
    (compose inner outer unit transport).certificate index =
      (inner.certificate index).compose (outer index) (unit index) := rfl

end

end Trace

end Purelib.Calculus.Jet.Progressive.Quadratic.Trace

end
