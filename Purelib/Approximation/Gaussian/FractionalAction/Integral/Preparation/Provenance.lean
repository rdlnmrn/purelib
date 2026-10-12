module
import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic

public import Purelib.Approximation.Gaussian.Acquisition.Provenance
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Equivalence
public import Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Separated
public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Exact
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Init.Prelude
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.FractionalAction.Integral

open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Process.Imaginary.Separation

open Purelib.Approximation.Gaussian.Provenance

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

namespace Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Provenance

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Gaussian.Process.Imaginary (Separation)
open Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Basic (Provider)

/-- Construct an all-matrix preparation provider from nonreal rational provenance.

The exact rational sidecar supplies imaginary separation, and its operational equivalence transports the resulting
provider to the original coherent channel. -/
def rationalProvider {channel :
  Coherent.CoherentNamed} (sidecar : Rational.Basic.RationalSidecar channel)
    (nonreal : sidecar.value.im ≠ 0) : Preparation.Basic.Provider channel :=
  Equivalence.transportProvider (Separated.provider
    (Exact.exactSeparation sidecar.value nonreal)) sidecar.equivalent

/-- Unsupported provenance falls through to acquisition without asserting that the function is real, zero, or
unpreparable. -/
def inferredProvider {channel :
  Coherent.CoherentNamed} : Option (Approximation.Gaussian.Acquisition.Provenance channel) → Option
      (Preparation.Basic.Provider channel)
  | some (.inl rational) => if nonreal : rational.value.im ≠ 0
      then some (rationalProvider rational
        nonreal) else none
  | _ => none
end Purelib.Approximation.Gaussian.FractionalAction.Integral.Preparation.Provenance

end
