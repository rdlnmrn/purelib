module
import Purelib.Data.CCL.Encoding.Encoder.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve.Basic
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run
import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Sharpness
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic
import Purelib.Data.List.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
@[expose] public section

/-!
# Finite CCL prefixes for robust approximation-sharpness runs

The RFAP construction can compute any requested finite same-source run, but
its displayed rational source depends on the final run length.  This module
therefore reserves one finite final run before exposing intermediate states.
Every state uses the same robust box, rational sample, and complete finite CCL
encoding, and reveals only initial segments of the reserved windows and word.
This is the finite prefix-coherent statement: it neither forms an infinite
stream nor asserts compatibility between independently constructed final
runs.
-/

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve.Build

/-- Compute a finite prefix reserve from the fully robust RFAP run. -/
def reserve
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale totalWindows : Nat) :
    Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows := by
  let robust := Dirichlet.Critical.Robust.Run.criticalFullyRobustRun
    certificate requestedScale totalWindows
  let sample := robust.box.nonzeroSample robust.proper
  let fraction := GaussianInt.Fraction.ofGaussian sample.point
  let numeratorNonzero :=
    GaussianInt.Fraction.ofGaussian_numerator_ne_zero sample.nonzero
  exact
    { robust := robust
      sample := sample
      fraction := fraction
      fractionValue := GaussianInt.Fraction.ofGaussian_value sample.point
      numeratorNonzero := numeratorNonzero
      fullWord := Data.CCL.Encoding.Encoder.Integral.encode fraction numeratorNonzero
      fullWord_eq := rfl }

/-- Public one-call construction of a finite robust sharpness reserve with
coherent CCL-prefix stages. -/
def sharpnessTower
    {threshold : Fraction.Rational}
    (certificate :
      Dirichlet.Critical.Sharpness.IsSharperWindowThreshold threshold)
    (requestedScale totalWindows : Nat) :
    Dirichlet.Critical.CCL.Reserve.Basic.ReservedTower threshold requestedScale totalWindows :=
  reserve certificate requestedScale totalWindows

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve.Build

end
