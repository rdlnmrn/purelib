module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Calculus.Jet.Preparation.Diagnostic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Exponential
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.Reciprocal
public import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic.ReducedLog
import Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Basic
import Purelib.Data.Gaussian.Norm.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Calculus.Jet.Progressive.Quadratic (Trace)

section
@[expose] public section

/-!
# Explicit finite failure states for partial progressive operations

Reciprocal, division, logarithm, chart transition, and branch selection are
not total operations on opaque CCL names.  Their constructors below consume a
finite evidence state and return either a constructed program or a visible
reason why the request cannot proceed.  Thus failure is data; it is never a
silent appeal to a completed nonzero value or a globally chosen branch.
-/

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation.Automatic

universe u

/-! ## Automatically transported semantic traces -/

set_option genInjectivity false in
open Purelib.Data in
/-- Uniform positive quadrance evidence, or a missing-bound state, for a reciprocal trace.

Supplied evidence retains rational lower bounds for the base and output at every index, together with positivity. The
other constructors identify which apartness requirement remains unavailable. -/
inductive AutomaticReciprocalEvidence
  {increment : Nat → Canonical}
    (trace : Trace increment) where
  /-- Retain positive rational lower bounds for all base and output quadrances. -/ | supplied :
      (baseLower outputLower : Rat.Fraction.Rational) →
      0 < baseLower → 0 < outputLower →
      (∀ index, baseLower ≤
        Gaussian.Norm.Basic.normSq
          (trace.certificate index).base) →
      (∀ index, outputLower ≤
        Gaussian.Norm.Basic.normSq
          (trace.certificate index).output) →
      AutomaticReciprocalEvidence trace
  /-- Record that the base quadrance lower bound has not been supplied. -/ | missingBaseApartness :
    AutomaticReciprocalEvidence trace
  /-- Record that the output quadrance lower bound has not been supplied. -/ | missingOutputApartness :
    AutomaticReciprocalEvidence trace

constructive_injectivity AutomaticReciprocalEvidence

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation in
open Purelib.Calculus.Jet.Preparation.Diagnostic in
open Purelib.Data in
/-- Build an automatically transported reciprocal or report the missing apartness evidence.

The supplied branch passes the retained positive lower bounds to the reciprocal constructor. The missing branches
distinguish base apartness from output apartness. -/
def automaticReciprocal {increment : Nat →
  Canonical} (trace : Trace increment) :
    AutomaticReciprocalEvidence trace → Decision (Trace increment)
  | .supplied baseLower outputLower basePositive outputPositive
      baseApart outputApart =>
    .accepted
      (Automatic.Reciprocal.reciprocalAutomatic
        trace baseLower outputLower basePositive outputPositive baseApart
          outputApart)
  | .missingBaseApartness => .rejected .denominatorApartness
  | .missingOutputApartness => .rejected .outputApartness

section
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation
open Purelib.Data
/-- Missing base evidence returns the denominator-apartness diagnostic. -/
@[simp] theorem
  automaticReciprocal_missing_base_exposes_requirement
    {increment : Nat → Canonical} (trace : Trace increment) :
    (automaticReciprocal trace .missingBaseApartness).missing? =
      some .denominatorApartness := rfl

/-- Missing output evidence returns the output-apartness diagnostic. -/
@[simp] theorem
  automaticReciprocal_missing_output_exposes_requirement
    {increment : Nat → Canonical} (trace : Trace increment) :
    (automaticReciprocal trace .missingOutputApartness).missing? =
      some .outputApartness := rfl

end

open Purelib.Data in
/-- Unit-disk evidence, or a missing-disk state, for a finite exponential trace.

Supplied evidence bounds the base, output displacement and increment quadrances by one at every index. Automatic
transport needs no separately supplied transport record. -/
inductive AutomaticExponentialEvidence
  {increment : Nat → Canonical}
    (trace : Trace increment) where
  /-- Retain the base, movement and increment unit-quadrance bounds at every index. -/ | supplied :
      (∀ index,
        Gaussian.Norm.Basic.normSq
          (trace.certificate index).base ≤ 1) →
      (∀ index,
        Gaussian.Norm.Basic.normSq
          ((trace.certificate index).output -
            (trace.certificate index).base) ≤ 1) →
      (∀ index,
        Gaussian.Norm.Basic.normSq (increment index) ≤ 1) →
      AutomaticExponentialEvidence trace
  /-- Record that the required unit-disk evidence has not been supplied. -/ | missingDisk :
    AutomaticExponentialEvidence trace

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation in
open Purelib.Calculus.Jet.Preparation.Diagnostic in
open Purelib.Data in
/-- Build an automatically transported exponential or report the missing disk evidence.

The supplied branch uses the exact retained base, movement and increment bounds. The missing branch returns the
input-disk diagnostic. -/
def automaticExponential {increment : Nat
  → Canonical} (trace : Trace increment) :
    AutomaticExponentialEvidence trace → Decision (Trace increment)
  | .supplied baseUnit movementUnit incrementUnit =>
    .accepted
      (Automatic.Exponential.exponentialAutomatic
        trace (fun index => (by
            simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
              using baseUnit index)) (fun index
          => (by
              simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
                using movementUnit index)) (fun index => (by
              simpa only [Gaussian.Norm.Basic.normSq_eq_canonical]
                using incrementUnit index)))
  | .missingDisk => .rejected .inputDisk

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation in
open Purelib.Data in
/-- Missing exponential disk evidence returns the input-disk diagnostic. -/
@[simp] theorem
  automaticExponential_missing_exposes_requirement
    {increment : Nat → Canonical} (trace : Trace increment) :
    (automaticExponential trace .missingDisk).missing? =
      some .inputDisk := rfl

open Purelib.Data in
/-- Local chart evidence, or a missing-chart state, for a finite reduced-logarithm trace.

Supplied evidence bounds movement quadrance by one ninth and increment quadrance by one at every index. These premises
determine the automatic local construction. -/
inductive AutomaticReducedLogEvidence
  {increment : Nat → Canonical}
    (trace : Trace increment) where
  /-- Retain the movement quadrance bound of one ninth and the unit increment bound. -/ | supplied :
      (∀ index,
        Gaussian.Norm.Basic.normSq
          ((trace.certificate index).output -
            (trace.certificate index).base) ≤ 1 / 9) →
      (∀ index,
        Gaussian.Norm.Basic.normSq (increment index) ≤ 1) →
      AutomaticReducedLogEvidence trace
  /-- Record that the required logarithm chart evidence has not been supplied. -/ | missingChart :
    AutomaticReducedLogEvidence trace

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Automatic in
open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation in
open Purelib.Calculus.Jet.Preparation.Diagnostic in
open Purelib.Data in
/-- Build an automatically transported reduced logarithm or report the missing chart.

The supplied branch passes the retained movement and increment bounds to the local constructor. The missing branch
identifies the safe-logarithm-chart requirement. -/
def automaticReducedLog {increment : Nat →
  Canonical} (trace : Trace increment) :
    AutomaticReducedLogEvidence trace → Decision (Trace increment)
  | .supplied movementDisk incrementUnit =>
    .accepted
      (Automatic.ReducedLog.reducedLogAutomatic
        trace movementDisk incrementUnit)
  | .missingChart => .rejected .safeLogarithmChart

open Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation in
open Purelib.Data in
/-- Missing reduced-logarithm evidence returns the safe-chart diagnostic. -/
@[simp] theorem
  automaticReducedLog_missing_exposes_requirement
    {increment : Nat → Canonical} (trace : Trace increment) :
    (automaticReducedLog trace .missingChart).missing? =
      some .safeLogarithmChart := rfl
end Purelib.Calculus.Jet.Progressive.Quadratic.Trace.Preparation.Automatic

end
