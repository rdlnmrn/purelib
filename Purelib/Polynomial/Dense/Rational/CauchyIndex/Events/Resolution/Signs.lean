module

import Purelib.Data.Rat.Interval.Basic
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Signs.Neutral
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Polynomial.Dense.Rational.Sign.Interval.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Signs.Neutral

/-!
# Sign readback of retained Cauchy resolutions

The retained polynomial inputs and interval bounds determine the certificate
indices. Each certificate retains its actual samples, signed chains and branch evidence.
-/

namespace Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution

open Purelib
open Purelib.Polynomial

/-- Read the finite endpoint-sign certificate from the retained neutral or numerator-resolved Cauchy event.

Each branch uses its retained strict-sign and neutral-chain certificates
to construct the corresponding formal event without rescanning the inputs. -/
@[expose] public def signs
    {R S : Dense.Rational.Basic.CoordinatePolynomial} {interval : Data.Rat.Interval.Bounds}
    (resolution : Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution R S interval) :
    Dense.Rational.CauchyIndex.Events.Signs.CauchyEventSigns R S interval :=
  match resolution with
  | .neutral denominator chain => .ofNeutral denominator chain
  | .numerator certificate tail => .ofResolvedNumerator certificate tail

end Purelib.Polynomial.Dense.Rational.CauchyIndex.Events.Resolution.Basic.CauchyEventResolution
