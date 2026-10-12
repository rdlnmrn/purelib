module

import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
import Init.Prelude
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

section
@[expose] public section

/-!
# Exact provenance and operational zero obstructions

Exact identities concern finite observation protocols, not equality of every
approximate candidate. One explicit comparison at an apartness lower bound
refutes an identity to zero. Rational provenance then gives exact division
decisions while leaving the original numerical channel unchanged.
-/

namespace Purelib.Approximation.Gaussian.Provenance.Rational.Basic

set_option genInjectivity false in
/-- Numerical identity and exact rational data are stored separately. The sidecar does not replace the original
numerical channel. -/
structure RationalSidecar (channel :
  Coherent.CoherentNamed) where
  /-- The displayed exact Gaussian rational retained as optional symbolic provenance. -/ value :
    Data.Gaussian.Basic.Canonical
  /-- The finite-request identity between the original channel and the exact name of the retained rational value. -/
    equivalent : Gaussian.Equivalence.NamedEquivalent channel.name (Coherence.exact value).name

constructive_injectivity RationalSidecar

/-- Attach reflexive rational provenance to an exact coherent Gaussian name. -/
def RationalSidecar.exact (value :
  Data.Gaussian.Basic.Canonical) :
    RationalSidecar (Coherence.exact value) :=
  ⟨value, NamedEquivalent.refl _⟩

/-- Attach exact zero provenance using the original channel's retained operational zero identity. -/
def RationalSidecar.zero {channel :
  Coherent.CoherentNamed} (identity : Zero.ZeroIdentity channel) :
    RationalSidecar channel := ⟨0, identity⟩

set_option genInjectivity false in
/-- Optional provenance can be forgotten without changing the channel or its raw output. Unsupported operations need not
fabricate symbolic information. -/
structure WithRationalSidecar where
  /-- The original coherent numerical channel. -/ channel : Coherent.CoherentNamed
  /-- Optional exact rational provenance indexed by that same original channel. -/ sidecar : Option
    (RationalSidecar channel)

constructive_injectivity WithRationalSidecar

/-- Discard optional rational provenance while retaining the original coherent numerical channel. -/
def WithRationalSidecar.forget (input :
  WithRationalSidecar) :
  WithRationalSidecar :=
  { channel := input.channel, sidecar := none }

/-- Discarding optional rational provenance preserves the original channel exactly. -/
@[simp] theorem WithRationalSidecar.forget_channel
  (input : WithRationalSidecar) :
    input.forget.channel = input.channel := rfl

end Purelib.Approximation.Gaussian.Provenance.Rational.Basic

end
