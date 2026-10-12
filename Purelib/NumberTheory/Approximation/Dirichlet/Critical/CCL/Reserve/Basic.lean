module
meta import Purelib.Elab.ConstructiveInjectivity
public import Purelib.Data.CCL.Encoding.Encoder.Integral
import Purelib.Data.Rat.Fraction
import Purelib.Data.GaussianInt.Fraction.Basic
public import Purelib.Data.List.Basic
import Purelib.Geometry.Rational.Box.Sample
public import Purelib.NumberTheory.Approximation.Dirichlet.Critical.Robust.Run
import Purelib.Data.Gaussian.Basic
import Purelib.Data.GaussianInt.Basic

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.NumberTheory.Approximation

section
public section

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

namespace Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve.Basic

set_option genInjectivity false in
/-- One explicitly finite reserve from which coherent window and CCL prefixes
are exposed.  The encoder is run once on one computed nonzero rational sample
of the common robust box. -/
structure ReservedTower
    (threshold : Fraction.Rational) (requestedScale totalWindows : Nat) where
  /-- The fully robust finite window run retained by this reserve. -/ robust :
    Dirichlet.Critical.Robust.Run.FullyRobustRun
    threshold requestedScale totalWindows
  /-- One retained nonzero rational Gaussian sample inside the robust box. -/ sample :
    Geometry.Rational.Box.NonzeroSample robust.box
  /-- The retained Gaussian integer fraction representing the sampled point. -/ fraction : GaussianInt.Fraction
  /-- The fraction value is exactly the retained sample point. -/ fractionValue : fraction.value = sample.point
  /-- The retained fraction numerator is nonzero, as required by the encoder. -/ numeratorNonzero : fraction.numerator ≠
    0
  /-- The cached complete finite CCL word of the retained fraction. -/ fullWord :
    List.Basic.BinaryWord
  /-- The cached word is exactly the integral encoder output for the retained fraction and nonzero proof. -/ fullWord_eq
    : fullWord = Data.CCL.Encoding.Encoder.Integral.encode fraction numeratorNonzero

constructive_injectivity ReservedTower

end Purelib.NumberTheory.Approximation.Dirichlet.Critical.CCL.Reserve.Basic

end
