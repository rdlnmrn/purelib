module
public import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Name.Coherent
import Init.Prelude
import Purelib.Data.Gaussian.Basic

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

namespace Purelib.Approximation.Gaussian.Equivalence.Zero

/-- A finite-request operational equivalence between the retained coherent channel and the exact Gaussian zero name. -/
def ZeroIdentity (channel : Coherent.CoherentNamed) :=
  Gaussian.Equivalence.NamedEquivalent channel.name (Coherence.exact 0).name
end Purelib.Approximation.Gaussian.Equivalence.Zero

end

section
@[expose] public section

/-!
# Semantic completeness and invariance of exact division decisions

Exact zero means an executable operational comparison with zero exists;
preparability means an equivalent whole-ball-apart presentation exists.
Neither predicate demands pointwise equality of approximate candidates.
The converse completeness laws require a computed exact decision, supplied
below by rational provenance and by the separate algebraic client. They are
not equality decisions for arbitrary opaque channels.
-/

namespace Purelib.Approximation.Gaussian.Equivalence.Zero

/-- The proposition that the retained coherent channel admits a finite-request operational identity with exact zero. -/
def IsZero (channel : Coherent.CoherentNamed) : Prop := Nonempty
  (ZeroIdentity channel)

/-- Transport an operational zero identity along an equivalence of the original coherent names. -/
def ZeroIdentity.transport {first second :
  Coherent.CoherentNamed} (zero : ZeroIdentity first)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) :
      ZeroIdentity second :=
  NamedEquivalent.trans
    (NamedEquivalent.symm equivalent) zero

/-- Existence of a finite-request operational zero identity is invariant under name equivalence. -/
theorem isZero_respects {first second : Coherent.CoherentNamed}
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) :
      IsZero first ↔ IsZero second :=
  ⟨fun ⟨zero⟩ => ⟨zero.transport equivalent⟩,
    fun ⟨zero⟩ => ⟨zero.transport (NamedEquivalent.symm equivalent)⟩⟩
end Purelib.Approximation.Gaussian.Equivalence.Zero

end
