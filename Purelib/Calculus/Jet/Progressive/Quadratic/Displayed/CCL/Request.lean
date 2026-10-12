module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Name.Coherent.CCL.ChannelRequest
import Purelib.Approximation.Gaussian.Name.Coherent.Request.Exact
public import Purelib.Calculus.Jet.Progressive.Quadratic.Displayed
import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Data.CCL.Transducer.Machine.Advance
import Purelib.Data.Gaussian.Norm.Basic

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

namespace Purelib.Calculus.Jet.Progressive.Quadratic.Displayed
namespace CertifiedCalculation

open Purelib.Approximation.Gaussian.Name.Coherent.CCL in
open Purelib.Data in
open Purelib.Calculus.Jet.Progressive.Quadratic.Displayed in
open Purelib.Calculus.Jet.Quadratic.Basic in
set_option genInjectivity false in
/-- Five channel requests retaining one exact displayed quadratic certificate.

Every request is indexed by the same calculation, positive rational target and bit count. The retained certificate is
explicitly equal to the calculation's original displayed certificate. -/
structure Request {increment : Gaussian.Basic.Canonical}
    (calculation : CertifiedCalculation increment) (target : Rat.Fraction.Rational)
    (positive : 0 < target) (count : Nat) where
  /-- The finite channel request for the indexed increment, at the shared target and bit count. -/ incrementRequest :
    Approximation.Gaussian.Name.Coherent.CCL.ChannelRequest calculation.incrementChannel target
    positive count
  /-- The finite channel request for the retained base, at the shared target and bit count. -/ baseRequest :
    Approximation.Gaussian.Name.Coherent.CCL.ChannelRequest calculation.baseChannel target positive count
  /-- The finite channel request for the retained output, at the shared target and bit count. -/ valueRequest :
    Approximation.Gaussian.Name.Coherent.CCL.ChannelRequest calculation.valueChannel target positive count
  /-- The finite channel request for the retained slope, at the shared target and bit count. -/ slopeRequest :
    Approximation.Gaussian.Name.Coherent.CCL.ChannelRequest calculation.slopeChannel target positive count
  /-- The finite channel request for the retained remainder, at the shared target and bit count. -/ remainderRequest :
    Approximation.Gaussian.Name.Coherent.CCL.ChannelRequest calculation.remainderChannel target
    positive count
  /-- The retained exact quadratic certificate at the indexed increment. -/ certificate : Certificate increment
  /-- The retained certificate is the calculation's original displayed certificate. -/ certificate_eq : certificate =
    calculation.displayed

constructive_injectivity Request

open Purelib.Approximation.Gaussian.Name.Coherent.CCL in
open Purelib.Data in
open Purelib.Calculus.Jet.Progressive.Quadratic.Displayed in
/-- Compute the five finite channel requests for a displayed quadratic calculation.

All channels receive the same positive target and bit count. The result retains the original certificate with reflexive
equality evidence. -/
def request {increment : Gaussian.Basic.Canonical}
    (calculation : CertifiedCalculation increment) (target : Rat.Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    CertifiedCalculation.Request calculation target positive count :=
  { incrementRequest := ChannelRequest.requestChannel calculation.incrementChannel target
      positive count
    baseRequest := ChannelRequest.requestChannel calculation.baseChannel target positive count
    valueRequest := ChannelRequest.requestChannel calculation.valueChannel target positive count
    slopeRequest := ChannelRequest.requestChannel calculation.slopeChannel target positive count
    remainderRequest := ChannelRequest.requestChannel calculation.remainderChannel target
      positive count
    certificate := calculation.displayed
    certificate_eq := rfl }

section
open Purelib.Approximation.Gaussian.Name.Coherent.CCL
open Purelib.Approximation.Gaussian
open Purelib.Data
open Purelib.Calculus.Jet.Progressive.Quadratic.Displayed
/-- The five requested enclosure centers satisfy the original exact expansion.

Each channel represents an exact displayed rational field, so its refined center recovers that field and the original
certificate supplies the identity. -/
theorem request_expansion {increment : Gaussian.Basic.Canonical}
    (calculation : CertifiedCalculation increment) (target : Rat.Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    let result := calculation.request target positive count
    (result.valueRequest.named.process.ball
          result.valueRequest.named.state).center -
        (result.baseRequest.named.process.ball
          result.baseRequest.named.state).center -
        (result.incrementRequest.named.process.ball
          result.incrementRequest.named.state).center *
          (result.slopeRequest.named.process.ball
            result.slopeRequest.named.state).center =
      (result.remainderRequest.named.process.ball
        result.remainderRequest.named.state).center := by
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, CertifiedCalculation.request, ChannelRequest.requestChannel,
    CertifiedCalculation.incrementChannel, CertifiedCalculation.baseChannel,
    CertifiedCalculation.valueChannel, CertifiedCalculation.slopeChannel, CertifiedCalculation.remainderChannel,
    Name.Coherent.Request.Exact.refinedExactChannel_center] using
      calculation.displayed.expansion

/-- The requested remainder center satisfies the retained certificate's quadratic bound.

Exact-channel refinement preserves both the displayed increment and remainder centers. The bound uses the factor in the
returned original certificate. -/
theorem request_remainder_le {increment : Gaussian.Basic.Canonical}
    (calculation : CertifiedCalculation increment) (target : Rat.Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    let result := calculation.request target positive count
    Gaussian.Norm.Basic.normSq
        (result.remainderRequest.named.process.ball
          result.remainderRequest.named.state).center ≤
      result.certificate.factor *
        Gaussian.Norm.Basic.normSq
          (result.incrementRequest.named.process.ball
            result.incrementRequest.named.state).center ^ 2 := by
  simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, CertifiedCalculation.request, ChannelRequest.requestChannel,
    CertifiedCalculation.incrementChannel, CertifiedCalculation.remainderChannel,
    Name.Coherent.Request.Exact.refinedExactChannel_center] using
      calculation.displayed.remainder_le

end

open Purelib.Data.CCL.Transducer in
open Purelib.Data in
open Purelib.Calculus.Jet.Progressive.Quadratic.Displayed in
/-- The five displayed channels emit the requested lengths and preserve the quadratic law.

The conjunction gives length count for each advanced machine, the exact expansion among their enclosure centers, and the
retained rational bound on remainder quadrance. -/
theorem synchronized_bitstream_and_quadratic_law {increment : Gaussian.Basic.Canonical}
    (calculation : CertifiedCalculation increment) (target : Rat.Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    let result := calculation.request target positive count
    (Machine.Advance.advance
        result.incrementRequest.named.machine count).emitted.length = count ∧
      (Machine.Advance.advance
        result.baseRequest.named.machine count).emitted.length = count ∧
      (Machine.Advance.advance
        result.valueRequest.named.machine count).emitted.length = count ∧
      (Machine.Advance.advance
        result.slopeRequest.named.machine count).emitted.length = count ∧
      (Machine.Advance.advance
        result.remainderRequest.named.machine count).emitted.length = count ∧
      (result.valueRequest.named.process.ball
            result.valueRequest.named.state).center -
          (result.baseRequest.named.process.ball
            result.baseRequest.named.state).center -
          (result.incrementRequest.named.process.ball
            result.incrementRequest.named.state).center *
            (result.slopeRequest.named.process.ball
              result.slopeRequest.named.state).center =
        (result.remainderRequest.named.process.ball
          result.remainderRequest.named.state).center ∧
      Gaussian.Norm.Basic.normSq
          (result.remainderRequest.named.process.ball
            result.remainderRequest.named.state).center ≤
        result.certificate.factor *
          Gaussian.Norm.Basic.normSq
            (result.incrementRequest.named.process.ball
              result.incrementRequest.named.state).center ^ 2 := by
  let result := calculation.request target positive count
  exact
    ⟨result.incrementRequest.emitted_length,
      result.baseRequest.emitted_length,
      result.valueRequest.emitted_length,
      result.slopeRequest.emitted_length,
      result.remainderRequest.emitted_length,
      calculation.request_expansion target positive count,
      calculation.request_remainder_le target positive count⟩

end CertifiedCalculation

end Purelib.Calculus.Jet.Progressive.Quadratic.Displayed

end
