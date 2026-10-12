module
public import Purelib.Approximation.Gaussian.Division.Prepared.Denominator
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent

import Purelib.Riemann.Integration.LegendreModularMonodromy

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

section
@[expose] public section

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

namespace Purelib.Approximation.Gaussian.Division.Prepared.Transport

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- Transport a retained denominator preparation along operational equivalence while reusing its exact apart
presentation. -/
def transportPreparation {first second :
  Coherent.CoherentNamed}
    (prepared : Prepared.DenominatorPreparation second)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) :
    Prepared.DenominatorPreparation first :=
  { prepared := prepared.prepared
    apart := prepared.apart
    equivalent := NamedEquivalent.trans equivalent prepared.equivalent }
end Purelib.Approximation.Gaussian.Division.Prepared.Transport

end
