module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Exponential.Horner.QuadraticJet
public import Purelib.Calculus.Jet.Preparation.Diagnostic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Calculus.Jet.Quadratic.Arithmetic
import Purelib.Calculus.Jet.Quadratic.Composition
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Transport.Arithmetic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
public section

/-!
# Explicit finite failure states for partial progressive operations

Reciprocal, division, logarithm, chart transition, and branch selection are
not total operations on opaque CCL names.  Their constructors below consume a
finite evidence state and return either a constructed program or a visible
reason why the request cannot proceed.  Thus failure is data; it is never a
silent appeal to a completed nonzero value or a globally chosen branch.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation.Manual

universe u

open Purelib.Data in
set_option genInjectivity false in
/-- Pointwise nonzero evidence and matching reciprocal transport, or a missing requirement.

The supplied transport is indexed by the exact reciprocal certificates computed with the retained nonzero witnesses.
Missing transport retains those witnesses while identifying the unresolved bound record. -/
inductive TraceReciprocalEvidence {increment
  : Nat → Canonical}
    (trace : Trace increment) where
  /-- Retain base and output nonzeroness together with transport for their exact reciprocal certificates. -/ | supplied
    :
      (baseNonzero : ∀ index, (trace.certificate index).base ≠ 0) →
      (outputNonzero : ∀ index, (trace.certificate index).output ≠ 0) →
      Trace.Transport increment
        (fun index => (trace.certificate index).reciprocal
          (baseNonzero index) (outputNonzero index)) →
      TraceReciprocalEvidence trace
  /-- Record missing pointwise nonzeroness of the base samples. -/ | missingBaseApartness :
    TraceReciprocalEvidence trace
  /-- Record missing pointwise nonzeroness of the output samples. -/ | missingOutputApartness :
    TraceReciprocalEvidence trace
  /-- Retain both pointwise nonzero witnesses while recording the missing reciprocal transport. -/ | missingTransport :
      (baseNonzero : ∀ index, (trace.certificate index).base ≠ 0) →
      (outputNonzero : ∀ index, (trace.certificate index).output ≠ 0) →
      TraceReciprocalEvidence trace

constructive_injectivity TraceReciprocalEvidence

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation in
open Purelib.Calculus.Jet.Preparation.Diagnostic in
open Purelib.Data in
/-- Build a reciprocal trace from matching evidence or return its missing requirement.

The supplied branch consumes the exact pointwise nonzero witnesses and transport. Other branches distinguish missing
base apartness, output apartness and quadratic transport. -/
@[expose] def traceReciprocal {increment :
  Nat → Canonical} (trace : Trace increment) :
    TraceReciprocalEvidence trace → Decision (Trace increment)
  | .supplied baseNonzero outputNonzero transport =>
      .accepted (trace.reciprocal baseNonzero outputNonzero transport)
  | .missingBaseApartness => .rejected .denominatorApartness
  | .missingOutputApartness => .rejected .outputApartness
  | .missingTransport _ _ => .rejected .quadraticTransport

section
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation
open Purelib.Data
/-- Missing base evidence returns the denominator-apartness diagnostic. -/
@[simp] theorem
  traceReciprocal_missing_exposes_requirement
    {increment : Nat → Canonical} (trace : Trace increment) :
    (traceReciprocal trace .missingBaseApartness).missing? =
      some .denominatorApartness := rfl

/-- Missing output evidence returns the output-apartness diagnostic. -/
@[simp] theorem
  traceReciprocal_missing_output_exposes_requirement
    {increment : Nat → Canonical} (trace : Trace increment) :
    (traceReciprocal trace .missingOutputApartness).missing? =
      some .outputApartness := rfl

/-- Supplied nonzeroness without transport returns the quadratic-transport diagnostic. -/
@[simp] theorem
  traceReciprocal_missing_transport_exposes_requirement
    {increment : Nat → Canonical} (trace : Trace increment)
    (baseNonzero : ∀ index, (trace.certificate index).base ≠ 0)
    (outputNonzero : ∀ index, (trace.certificate index).output ≠ 0) :
    (traceReciprocal trace
      (.missingTransport baseNonzero outputNonzero)).missing? =
        some .quadraticTransport := rfl

end

open Purelib.Data in
open Purelib.Calculus.Jet.Quadratic.Basic in
set_option genInjectivity false in
/-- Disk evidence and matching exponential transport, or a missing requirement.

The supplied transport concerns the exact composed finite exponential certificates at each stage. Missing transport
retains the base, movement and increment disk witnesses. -/
inductive TraceExponentialEvidence {increment
  : Nat → Canonical}
    (trace : Trace increment) where
  /-- Retain all three unit-disk bounds and transport for the exact composed exponential certificates. -/ | supplied :
      (baseUnit : ∀ index,
        Gaussian.Norm.Basic.normSq
          (trace.certificate index).base ≤ 1) →
      (movementUnit : ∀ index,
        Gaussian.Norm.Basic.normSq
          ((trace.certificate index).output -
            (trace.certificate index).base) ≤ 1) →
      (incrementUnit : ∀ index,
        Gaussian.Norm.Basic.normSq (increment index) ≤ 1) →
      Trace.Transport increment
        (fun index => (trace.certificate index).compose
          (Certificate.exponential
            (baseUnit index) (movementUnit index) index)
          (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using incrementUnit index)) →
      TraceExponentialEvidence trace
  /-- Record missing unit-disk evidence for the exponential construction. -/ | missingDisk :
    TraceExponentialEvidence trace
  /-- Retain the disk witnesses while recording the missing exponential transport. -/ | missingTransport :
      (baseUnit : ∀ index,
        Gaussian.Norm.Basic.normSq
          (trace.certificate index).base ≤ 1) →
      (movementUnit : ∀ index,
        Gaussian.Norm.Basic.normSq
          ((trace.certificate index).output -
            (trace.certificate index).base) ≤ 1) →
      (incrementUnit : ∀ index,
        Gaussian.Norm.Basic.normSq (increment index) ≤ 1) →
      TraceExponentialEvidence trace

constructive_injectivity TraceExponentialEvidence

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation in
open Purelib.Calculus.Jet.Preparation.Diagnostic in
open Purelib.Data in
/-- Build an exponential trace from matching disk and transport evidence.

The supplied branch preserves the given transport for the composed certificates. Other branches report either the
missing input disk or the missing quadratic transport. -/
@[expose] def traceExponential {increment :
  Nat → Canonical} (trace : Trace increment) :
    TraceExponentialEvidence trace → Decision (Trace increment)
  | .supplied baseUnit movementUnit incrementUnit transport =>
      .accepted
        (trace.exponential (fun index => (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using baseUnit index))
          (fun index => (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using movementUnit index)) (fun index
          => (by simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using incrementUnit index)) transport)
  | .missingDisk => .rejected .inputDisk
  | .missingTransport _ _ _ => .rejected .quadraticTransport

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation
open Purelib.Data
/-- Missing exponential disk evidence returns the input-disk diagnostic. -/
@[simp] theorem
  traceExponential_missing_exposes_requirement
    {increment : Nat → Canonical} (trace : Trace increment) :
    (traceExponential trace .missingDisk).missing? = some .inputDisk := rfl

/-- Supplied disk bounds without transport return the quadratic-transport diagnostic. -/
@[simp] theorem
  traceExponential_missing_transport_exposes_requirement
    {increment : Nat → Canonical} (trace : Trace increment)
    (baseUnit : ∀ index,
      Gaussian.Norm.Basic.normSq
        (trace.certificate index).base ≤ 1)
    (movementUnit : ∀ index,
      Gaussian.Norm.Basic.normSq
        ((trace.certificate index).output -
          (trace.certificate index).base) ≤ 1)
    (incrementUnit : ∀ index,
      Gaussian.Norm.Basic.normSq (increment index) ≤ 1) :
    (traceExponential trace
      (.missingTransport baseUnit movementUnit incrementUnit)).missing? =
        some .quadraticTransport := rfl
end Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation.Manual

end
