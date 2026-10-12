module
public import Purelib.Approximation.Gaussian.Name.Apart.Exact
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic

section
public section

/-!
# Exact provenance and operational zero obstructions

Exact identities concern finite observation protocols, not equality of every
approximate candidate. One explicit comparison at an apartness lower bound
refutes an identity to zero. Rational provenance then gives exact division
decisions while leaving the original numerical channel unchanged.
-/

namespace Purelib.Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar

open Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Apart.Exact

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Approximation.Gaussian.Provenance

/-- Decide division preparation from a retained rational sidecar.

A zero value supplies the channel's operational zero identity. A nonzero value
retains its exact name, apartness certificate, and the sidecar's comparison
with the original channel. -/
@[expose] def decide {channel : Coherent.CoherentNamed} (sidecar : Rational.Basic.RationalSidecar channel) :
    Division.Prepared.Decision channel :=
  if zero : sidecar.value = 0 then
    .excluded (by
        unfold Purelib.Approximation.Gaussian.Equivalence.Zero.ZeroIdentity;
        simpa only [zero]
          using sidecar.equivalent)
  else .prepared
    { denominator := Coherence.exact sidecar.value
      apart := exactApart sidecar.value zero
      equivalent := sidecar.equivalent }
end Purelib.Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar

end
