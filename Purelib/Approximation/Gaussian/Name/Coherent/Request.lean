module
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Rational.Request.Common
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Process.Coherence.Basic (Coherent)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Progressive CCL observations of quadratic jet certificates

This module connects the displayed quadratic-change certificates to the
productive CCL layer.  A `CertifiedCalculation` stores one finite rational
certificate, not five unrelated channels.  Its input increment, base value,
output value, slope, and remainder are then exposed as terminating coherent
CCL names.  One request returns certified enclosures and persistent raw CCL
prefixes for all five fields.

This is the exact-input specialization needed by the general progressive jet
construction.  Nothing here turns a non-rational result into a completed
value: the only exact channels introduced below are fields already present in
the supplied Gaussian-rational certificate.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Request

/-- One explicit request below both the visible radius target and the coherence sidechannel's semantic target. -/
def channelTarget (channel : CoherentNamed)
  (target : Fraction.Rational) :
    Fraction.Rational :=
  Coherent.commonRequest target
    (channel.coherent.accuracyRequest target)

/-- The common visible-radius and semantic-accuracy request is positive for a positive target. -/
theorem channelTarget_pos (channel :
  CoherentNamed) {target : Fraction.Rational}
    (positive : 0 < target) : 0 < channelTarget channel target :=
  Coherent.commonRequest_pos positive
    (channel.coherent.accuracyRequest_pos positive)

/-- The common channel request lies strictly below the displayed positive radius target. -/
theorem channelTarget_lt_target (channel :
  CoherentNamed)
    {target : Fraction.Rational} (positive : 0 < target) :
    channelTarget channel target < target :=
  Coherent.commonRequest_lt_left positive
    (channel.coherent.accuracyRequest_pos positive)

/-- The common channel request lies strictly below the coherence request for the displayed positive target. -/
theorem channelTarget_lt_allowanceRequest (channel :
  CoherentNamed)
    {target : Fraction.Rational} (positive : 0 < target) :
    channelTarget channel target < channel.coherent.accuracyRequest target
      :=
  Coherent.commonRequest_lt_right positive
    (channel.coherent.accuracyRequest_pos positive)

end Purelib.Approximation.Gaussian.Name.Coherent.Request

end
