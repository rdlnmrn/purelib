module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Approximation.Gaussian.Acquisition.Signed.Requested
import Purelib.Approximation.Gaussian.Acquisition.State
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

public import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Provenance
public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Acquisition.Signed

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary

open Purelib.Data.Rat

section
public section

/-!
# Evidence-directed finite Legendre words

Reuse a cached provider or separation first. Nonreal rational provenance
automatically constructs and transports an all-row provider. Otherwise one
signed numerical inspection prepares either half-plane, or returns retained
near-boundary evidence. Nonzeroness of the input alone is not used as a
certificate for every intermediate word denominator. Real inputs and
unsupported symbolic provenance may remain inconclusive by this sufficient
test; this is not a decision procedure for each particular real word.
-/

namespace Purelib.Curves.Legendre.Acquisition.Words.State

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic (Provider)

set_option genInjectivity false in
/-- The retained search state and optional semantic evidence for word preparation.

Provenance, an all-matrix preparation provider and unsigned imaginary separation remain separate optional data tied to
the input channel. -/
structure InputPayload.{u, v, w, x}
    (stateType : Type u) (provenanceType : Type v) (providerType : Type w) (separationType : Type x) where
  /-- The current retained channel-inspection state. -/ state : stateType
  /-- Optional exact semantic provenance for the coherent channel. -/ provenance : Option provenanceType
  /-- An optional cached provider preparing every invertible denominator row. -/ provider : Option providerType := none
  /-- An optional retained unsigned imaginary separation certificate. -/ separation : Option separationType := none

constructive_injectivity Purelib.Curves.Legendre.Acquisition.Words.State.InputPayload

/-- A word-preparation input whose search state and optional certificates share one coherent channel. -/
@[expose] def Input (tau : Coherent.CoherentNamed) :=
  InputPayload
  (Approximation.Gaussian.Acquisition.State tau)
  (Approximation.Gaussian.Acquisition.Provenance tau) (Preparation.Basic.Provider tau)
      (Approximation.Gaussian.Process.Imaginary.Separation tau)

/-- Initialize word preparation from an annotated channel, retaining its original provenance. -/
@[expose] def start (input :
    Approximation.Gaussian.Acquisition.Annotated) :
  Input input.channel :=
  { state := State.initial input.channel
    provenance := input.provenance }

/-- The evidence route used by a finite word-preparation step. -/
inductive Route where
  /-- An already cached all-matrix preparation provider was reused. -/ | cached /-- An existing unsigned imaginary
    separation certificate supplied preparation. -/ | separation /-- Nonreal rational provenance supplied a preparation
    provider. -/ | rational /-- A finite inspection produced positive imaginary evidence. -/ | positive /-- A finite
    inspection produced negative imaginary evidence. -/ | negative /-- The finite inspection retained unresolved
    near-boundary evidence. -/ | near
  deriving DecidableEq

set_option genInjectivity false in
/-- A retained word-preparation update with its route and persistence guarantees.

The update preserves exact provenance and the request index, and every possible value at its new source remains possible
at the previous source. -/
structure Step {tau : Coherent.CoherentNamed} (input :
  Input tau) where
  /-- The complete retained input after the preparation step. -/ next : Input
    tau
  /-- The evidence route taken by the step. -/ route : Route
  /-- The step retains the original provenance exactly. -/ provenance_eq : next.provenance = input.provenance
  /-- The step preserves the retained request index. -/ index_eq : next.state.retained.nextIndex =
    input.state.retained.nextIndex
  /-- Every possible value at the next retained source is possible at the previous source. -/ persists : ∀ {value :
    Data.Gaussian.Basic.Canonical}, tau.name.process.Possible next.state.retained.source value →
    tau.name.process.Possible input.state.retained.source value

constructive_injectivity Purelib.Curves.Legendre.Acquisition.Words.State.Step

/-- Record an evidence route while leaving the complete retained input unchanged. -/
@[expose] def Step.unchanged {tau : Coherent.CoherentNamed}
  (input : Input tau) (route : Route) :
  Step input :=
  ⟨input, route, rfl, rfl, fun possible => possible⟩

/-- Install a finite signed-inspection result while retaining provenance and request identity. -/
@[expose] def Step.inspected {tau : Coherent.CoherentNamed}
  (input : Input tau) (route : Route)
    {delta : Fraction.Rational} {positive : 0 < delta}
    (report : Requested.Report tau input.state delta positive) : Step input :=
  { next := { input with state := report.retained }
    route := route
    provenance_eq := rfl
    index_eq := report.nextIndex_eq
    persists := report.possible_at_start }

/-- Add a successful all-matrix provider to a retained step without changing its persistence guarantees. -/
@[expose] def Step.cache {tau : Coherent.CoherentNamed} {input :
  Input tau} (step : Step input)
  (provider : Preparation.Basic.Provider tau) :
    Step input := { step with next := { step.next with provider := some provider
      } }
end Purelib.Curves.Legendre.Acquisition.Words.State

end
