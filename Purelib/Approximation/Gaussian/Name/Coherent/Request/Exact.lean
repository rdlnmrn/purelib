module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Request
public import Purelib.Approximation.Gaussian.Name.Refinement
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

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

namespace Purelib.Approximation.Gaussian.Name.Coherent.Request.Exact

/-- Refining an exact coherent Gaussian name by its joint channel request preserves the displayed enclosure center. -/
@[simp] theorem exactRequest_center (value :
  Data.Gaussian.Basic.Canonical) (target : Fraction.Rational)
    (positive : 0 < target) :
    let channel :=
      Coherence.exact value
    let named := Refinement.refined channel.name
      (Request.channelTarget channel target) (Request.channelTarget_pos channel positive)
    (named.process.ball named.state).center = value := by
  rfl

/-- Refining an exact coherent Gaussian name by any positive rational request preserves its exact enclosure center. -/
@[simp] theorem refinedExactChannel_center (value :
  Data.Gaussian.Basic.Canonical)
    (request : Fraction.Rational) (positive : 0 < request) :
    let channel :=
      Coherence.exact value
    let named := Refinement.refined channel.name
      request positive
    (named.process.ball named.state).center = value := by
  rfl

end Purelib.Approximation.Gaussian.Name.Coherent.Request.Exact

end
