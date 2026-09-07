import CCL.Progressive.FirstJet
import CCL.Calculus.QuadraticJet

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

namespace CCL.ProgressiveQuadraticJet

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev Certificate := CCL.QuadraticJet.Certificate

/-- One explicit request below both the visible radius target and the
coherence sidechannel's semantic target. -/
def channelTarget (channel : CoherentNamed) (target : Coordinate) :
    Coordinate :=
  CCL.ProgressiveCoherence.Coherent.commonRequest target
    (channel.coherent.accuracyRequest target)

theorem channelTarget_pos (channel : CoherentNamed) {target : Coordinate}
    (positive : 0 < target) : 0 < channelTarget channel target :=
  CCL.ProgressiveCoherence.Coherent.commonRequest_pos positive
    (channel.coherent.accuracyRequest_pos positive)

theorem channelTarget_lt_target (channel : CoherentNamed)
    {target : Coordinate} (positive : 0 < target) :
    channelTarget channel target < target :=
  CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left positive
    (channel.coherent.accuracyRequest_pos positive)

theorem channelTarget_lt_allowanceRequest (channel : CoherentNamed)
    {target : Coordinate} (positive : 0 < target) :
    channelTarget channel target < channel.coherent.accuracyRequest target :=
  CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right positive
    (channel.coherent.accuracyRequest_pos positive)

/-- One channel request, including both its semantic allowance and its actual
persistent CCL cursor. -/
structure ChannelRequest (channel : CoherentNamed) (target : Coordinate)
    (positive : 0 < target) (count : Nat) where
  named : Named
  named_eq : named = CCL.TranscendentalOutput.refined channel.name
    (channelTarget channel target) (channelTarget_pos channel positive)
  radius_lt : (named.process.ball named.state).radiusSq < target
  allowance_lt : channel.coherent.allowance
    (CCL.TranscendentalOutput.refined channel.name
      (channelTarget channel target)
      (channelTarget_pos channel positive)).state < target
  prefix_preserved : named.machine.emitted.IsPrefix
    (CCL.ProgressiveTransducer.advance
      named.machine count).emitted
  emitted_length :
    (CCL.ProgressiveTransducer.advance
      named.machine count).emitted.length = count
  exact_cursor : CCL.ProgressiveMachineSemantics.ExactCursor
    named.process named.state
    (CCL.ProgressiveTransducer.advance named.machine count)

/-- Execute one finite enclosure-and-prefix request against a coherent
channel. -/
def requestChannel (channel : CoherentNamed) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    ChannelRequest channel target positive count := by
  let named := CCL.TranscendentalOutput.refined channel.name
    (channelTarget channel target) (channelTarget_pos channel positive)
  exact
    { named := named
      named_eq := rfl
      radius_lt :=
        (CCL.TranscendentalOutput.refined_error channel.name
          (channelTarget channel target)
          (channelTarget_pos channel positive)).trans
            (channelTarget_lt_target channel positive)
      allowance_lt := channel.coherent.refine_accurate channel.name.state
        target positive (channelTarget channel target)
        (channelTarget_pos channel positive)
        (channelTarget_lt_allowanceRequest channel positive)
      prefix_preserved := (named.productive count).1
      emitted_length := (named.productive count).2
      exact_cursor :=
        CCL.ProgressiveMachineSemantics.Named.advance_exact
          named count }

@[simp] theorem exactRequest_center (value : Gaussian) (target : Coordinate)
    (positive : 0 < target) :
    let channel :=
      CCL.ProgressiveCoherence.CoherentNamed.exact value
    let named := CCL.TranscendentalOutput.refined channel.name
      (channelTarget channel target) (channelTarget_pos channel positive)
    (named.process.ball named.state).center = value := by
  rfl

@[simp] theorem refinedExactChannel_center (value : Gaussian)
    (request : Coordinate) (positive : 0 < request) :
    let channel :=
      CCL.ProgressiveCoherence.CoherentNamed.exact value
    let named := CCL.TranscendentalOutput.refined channel.name
      request positive
    (named.process.ball named.state).center = value := by
  rfl

/-- A single displayed quadratic law viewed as five synchronized coherent CCL
channels. -/
structure CertifiedCalculation (increment : Gaussian) where
  displayed : Certificate increment

namespace CertifiedCalculation

def incrementChannel {increment : Gaussian}
    (_calculation : CertifiedCalculation increment) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact increment

def baseChannel {increment : Gaussian}
    (calculation : CertifiedCalculation increment) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact
    calculation.displayed.base

def valueChannel {increment : Gaussian}
    (calculation : CertifiedCalculation increment) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact
    calculation.displayed.output

def slopeChannel {increment : Gaussian}
    (calculation : CertifiedCalculation increment) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact
    calculation.displayed.slope

def remainderChannel {increment : Gaussian}
    (calculation : CertifiedCalculation increment) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact
    calculation.displayed.remainder

/-- The finite output of one synchronized request. -/
structure Request {increment : Gaussian}
    (calculation : CertifiedCalculation increment) (target : Coordinate)
    (positive : 0 < target) (count : Nat) where
  incrementRequest : ChannelRequest calculation.incrementChannel target
    positive count
  baseRequest : ChannelRequest calculation.baseChannel target positive count
  valueRequest : ChannelRequest calculation.valueChannel target positive count
  slopeRequest : ChannelRequest calculation.slopeChannel target positive count
  remainderRequest : ChannelRequest calculation.remainderChannel target
    positive count
  certificate : Certificate increment
  certificate_eq : certificate = calculation.displayed

/-- Compute all five finite observations.  Each request uses the same visible
rational accuracy and bit-count target. -/
def request {increment : Gaussian}
    (calculation : CertifiedCalculation increment) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    Request calculation target positive count :=
  { incrementRequest := requestChannel calculation.incrementChannel target
      positive count
    baseRequest := requestChannel calculation.baseChannel target positive count
    valueRequest := requestChannel calculation.valueChannel target positive count
    slopeRequest := requestChannel calculation.slopeChannel target positive count
    remainderRequest := requestChannel calculation.remainderChannel target
      positive count
    certificate := calculation.displayed
    certificate_eq := rfl }

/-- The five exact enclosure centres returned by a request obey the original
quadratic-change identity. -/
theorem request_expansion {increment : Gaussian}
    (calculation : CertifiedCalculation increment) (target : Coordinate)
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
  simpa only [request, requestChannel, incrementChannel, baseChannel,
    valueChannel, slopeChannel, remainderChannel,
    refinedExactChannel_center] using
      calculation.displayed.expansion

/-- The returned remainder centre retains the displayed rational quadratic
bound and its explicit nonnegative factor. -/
theorem request_remainder_le {increment : Gaussian}
    (calculation : CertifiedCalculation increment) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    let result := calculation.request target positive count
    RFAP.ConstructiveGaussian.Gaussian.normSq
        (result.remainderRequest.named.process.ball
          result.remainderRequest.named.state).center ≤
      result.certificate.factor *
        RFAP.ConstructiveGaussian.Gaussian.normSq
          (result.incrementRequest.named.process.ball
            result.incrementRequest.named.state).center ^ 2 := by
  simpa only [request, requestChannel, incrementChannel, remainderChannel,
    refinedExactChannel_center] using
      calculation.displayed.remainder_le

/-- Every field of a displayed quadratic certificate therefore has an actual
productive CCL output, and its exact finite observations still satisfy the
semantic expansion and quadratic bound. -/
theorem synchronized_bitstream_and_quadratic_law {increment : Gaussian}
    (calculation : CertifiedCalculation increment) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    let result := calculation.request target positive count
    (CCL.ProgressiveTransducer.advance
        result.incrementRequest.named.machine count).emitted.length = count ∧
      (CCL.ProgressiveTransducer.advance
        result.baseRequest.named.machine count).emitted.length = count ∧
      (CCL.ProgressiveTransducer.advance
        result.valueRequest.named.machine count).emitted.length = count ∧
      (CCL.ProgressiveTransducer.advance
        result.slopeRequest.named.machine count).emitted.length = count ∧
      (CCL.ProgressiveTransducer.advance
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
      RFAP.ConstructiveGaussian.Gaussian.normSq
          (result.remainderRequest.named.process.ball
            result.remainderRequest.named.state).center ≤
        result.certificate.factor *
          RFAP.ConstructiveGaussian.Gaussian.normSq
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

end CCL.ProgressiveQuadraticJet
