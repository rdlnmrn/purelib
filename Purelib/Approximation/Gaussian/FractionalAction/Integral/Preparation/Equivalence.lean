module
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent

public import Purelib.Approximation.Gaussian.Division.Prepared.Transport
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Comparison
import Purelib.Riemann.Integration.LegendreModularMonodromy
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.LinearAlgebra.Matrix.Inverse.Right

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.FractionalAction.Integral

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

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Equivalence

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic (Provider)

/-- Transport an all-matrix preparation provider across equivalence of coherent inputs.

Each matrix denominator is compared operationally at the two input names, so the existing successful preparation can be
retained without equating approximate candidate readings. -/
def transportProvider {first
  second : Coherent.CoherentNamed} (provider : Preparation.Basic.Provider second)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) : Preparation.Basic.Provider first :=
  fun matrix inverse => Transport.transportPreparation (provider matrix inverse)
    (Comparison.denominatorComparison matrix equivalent)
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Equivalence

end
