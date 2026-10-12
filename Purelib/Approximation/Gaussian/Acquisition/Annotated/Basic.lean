module
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Data.Gaussian.Basic

public import Purelib.Approximation.Gaussian.Acquisition.Provenance
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Init.Prelude
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Provenance.Rational.Basic

section
@[expose] public section

/-!
# Numerical channels with automatically propagated finite provenance

Arithmetic constructors keep the actual numerical program. Their sidecars
are derived by operational laws, never by treating approximate samples as
exact values. Unsupported combinations lose only the sidecar. This is a
small supported rule set, not general algebraic-number normalization.
-/

namespace Purelib.Approximation.Gaussian.Acquisition

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

set_option genInjectivity false in
/-- An original coherent numerical channel with optional finite provenance.

The provenance remains indexed by that exact channel; absence of a sidecar does not alter the numerical program. -/
structure Annotated where
  /-- The original coherent numerical channel. -/ channel : Coherent.CoherentNamed
  /-- Optional rational or square-root provenance indexed by the retained channel. -/ provenance : Option
    (Provenance channel)

constructive_injectivity Annotated

namespace Annotated.mk

end Annotated.mk

namespace Annotated

/-- Retain the supplied coherent channel without a provenance sidecar. -/
def «opaque» (channel :
  Coherent.CoherentNamed) : Annotated := ⟨channel, none⟩

/-- Construct the exact Gaussian channel with its executable rational provenance. -/
def rational (value :
  Data.Gaussian.Basic.Canonical) : Annotated :=
  ⟨Coherence.exact value, some (.inl (RationalSidecar.exact value))⟩

/-- Remove the provenance sidecar while retaining the same coherent channel. -/
def forget (input :
  Annotated) :
  Annotated := ⟨input.channel, none⟩

/-- Forgetting provenance preserves the exact original channel. -/
@[simp] theorem forget_channel (input :
  Annotated) : input.forget.channel = input.channel := rfl

set_option backward.match.sparseCases false in
/-- Read the retained Gaussian value when the annotation specifically carries rational provenance. -/
def rationalValue (input :
  Annotated) : Option Data.Gaussian.Basic.Canonical :=
  match input.provenance with
  | some (.inl rational) => some rational.value
  | _ => none

end Annotated

end Purelib.Approximation.Gaussian.Acquisition

end
