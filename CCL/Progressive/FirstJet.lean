import CCL.Transcendental.LogBranchCalculus
import CCL.Transcendental.Output
import CCL.Calculus.Trigonometric

/-!
# Synchronized first jets over progressive CCL inputs

The displayed-input evaluator in `FirstJet` computes two rational
coordinates.  This module lifts the same algebra to arbitrary coherent
progressive inputs.  A jet contains two coherent names, one for the value
channel and one for the slope channel, together with an indexed finite program
which proves that the channels were produced by the same differentiation
calculation.  Thus an arbitrary unrelated pair of names is not a jet.  A joint
request computes one positive rational budget below the requested value error,
the requested slope error, and both semantic-coherence moduli.

No derivative is represented as a function.  Every observation consists of
two finite process states and two finite raw CCL prefixes.
-/

namespace CCL.ProgressiveFirstJet

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev Named := CCL.ProgressiveTransducer.Named
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed
abbrev AnchoredChart := CCL.LogBranchCalculus.AnchoredChart

/-- The exact coherent channel used by finite jet programs. -/
def exactChannel (value : Gaussian) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.exact value

/-- Pointwise addition at the coherent-name layer. -/
def addChannel (left right : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.add left right

/-- Pointwise negation at the coherent-name layer. -/
def negChannel (value : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.neg value

/-- Pointwise multiplication at the coherent-name layer. -/
def mulChannel (left right : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.mul left right

/-- Apartness-certified reciprocal channel. -/
def reciprocalChannel (value : CoherentNamed)
    (apart : CCL.ProgressiveTransducer.Named.Apart value.name) :
    CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.div (exactChannel 1)
    value apart

/-- Total range-reduced exponential channel. -/
def exponentialChannel (value : CoherentNamed) : CoherentNamed :=
  CCL.TranscendentalCoherence.exp value.name

/-- Finite provenance for a progressive value/slope pair.  The result indices
make every rule compute both channels together; in particular there is no
constructor which accepts an arbitrary value and an arbitrary slope.  Domain
evidence for partial rules refers to the actual computed value channel. -/
inductive Program : CoherentNamed → CoherentNamed → Prop
  | constant (value : Gaussian) :
      Program (exactChannel value) (exactChannel 0)
  | independent (value : CoherentNamed) :
      Program value (exactChannel 1)
  | add {leftValue leftSlope rightValue rightSlope : CoherentNamed} :
      Program leftValue leftSlope → Program rightValue rightSlope →
      Program (addChannel leftValue rightValue)
        (addChannel leftSlope rightSlope)
  | neg {value slope : CoherentNamed} : Program value slope →
      Program (negChannel value) (negChannel slope)
  | mul {leftValue leftSlope rightValue rightSlope : CoherentNamed} :
      Program leftValue leftSlope → Program rightValue rightSlope →
      Program (mulChannel leftValue rightValue)
        (addChannel (mulChannel leftSlope rightValue)
          (mulChannel leftValue rightSlope))
  | reciprocal {value slope : CoherentNamed} (program : Program value slope)
      (apart : CCL.ProgressiveTransducer.Named.Apart value.name) :
      Program (reciprocalChannel value apart)
        (negChannel (mulChannel slope
          (mulChannel (reciprocalChannel value apart)
            (reciprocalChannel value apart))))
  | compose {outerValue outerSlope innerValue innerSlope : CoherentNamed} :
      Program outerValue outerSlope → Program innerValue innerSlope →
      Program outerValue (mulChannel innerSlope outerSlope)
  | exponential {value slope : CoherentNamed} (program : Program value slope) :
      Program (exponentialChannel value)
        (mulChannel slope (exponentialChannel value))
  | logarithm {value slope : CoherentNamed} (program : Program value slope)
      (branch : AnchoredChart value)
      (apart : CCL.ProgressiveTransducer.Named.Apart value.name) :
      Program branch.output (mulChannel slope (reciprocalChannel value apart))
  | sine {value slope : CoherentNamed} (program : Program value slope) :
      Program (CCL.Trigonometric.sine value)
        (mulChannel slope (CCL.Trigonometric.cosine value))
  | cosine {value slope : CoherentNamed} (program : Program value slope) :
      Program (CCL.Trigonometric.cosine value)
        (negChannel (mulChannel slope
          (CCL.Trigonometric.sine value)))

/-- A synchronized progressive value and first-order coefficient, carrying
the finite program which produced both channels. -/
structure FirstJet where
  value : CoherentNamed
  slope : CoherentNamed
  program : Program value slope

namespace FirstJet

def constant (value : Gaussian) : FirstJet :=
  { value := CCL.ProgressiveCoherence.CoherentNamed.exact value
    slope := CCL.ProgressiveCoherence.CoherentNamed.exact 0
    program := Program.constant value }

def independent (value : CoherentNamed) : FirstJet :=
  { value := value
    slope := CCL.ProgressiveCoherence.CoherentNamed.exact 1
    program := Program.independent value }

def add (left right : FirstJet) : FirstJet :=
  { value := CCL.ProgressiveCoherence.CoherentNamed.add
      left.value right.value
    slope := CCL.ProgressiveCoherence.CoherentNamed.add
      left.slope right.slope
    program := Program.add left.program right.program }

def neg (jet : FirstJet) : FirstJet :=
  { value := CCL.ProgressiveCoherence.CoherentNamed.neg jet.value
    slope := CCL.ProgressiveCoherence.CoherentNamed.neg jet.slope
    program := Program.neg jet.program }

def sub (left right : FirstJet) : FirstJet := add left (neg right)

/-- The synchronized finite product rule. -/
def mul (left right : FirstJet) : FirstJet :=
  { value := CCL.ProgressiveCoherence.CoherentNamed.mul
      left.value right.value
    slope := CCL.ProgressiveCoherence.CoherentNamed.add
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        left.slope right.value)
      (CCL.ProgressiveCoherence.CoherentNamed.mul
        left.value right.slope)
    program := Program.mul left.program right.program }

/-- The synchronized reciprocal rule, guarded by the actual progressive
denominator's finite apartness certificate. -/
def reciprocal (jet : FirstJet)
    (apart : CCL.ProgressiveTransducer.Named.Apart
      jet.value.name) : FirstJet :=
  let inverse := CCL.ProgressiveCoherence.CoherentNamed.div
    (CCL.ProgressiveCoherence.CoherentNamed.exact 1)
    jet.value apart
  { value := inverse
    slope := CCL.ProgressiveCoherence.CoherentNamed.neg
      (CCL.ProgressiveCoherence.CoherentNamed.mul jet.slope
        (CCL.ProgressiveCoherence.CoherentNamed.mul
          inverse inverse))
    program := Program.reciprocal jet.program apart }

def div (numerator denominator : FirstJet)
    (apart : CCL.ProgressiveTransducer.Named.Apart
      denominator.value.name) : FirstJet :=
  mul numerator (reciprocal denominator apart)

/-- `outer` is already evaluated at the inner value. -/
def compose (outer inner : FirstJet) : FirstJet :=
  { value := outer.value
    slope := CCL.ProgressiveCoherence.CoherentNamed.mul
      inner.slope outer.slope
    program := Program.compose outer.program inner.program }

/-- Total exponential together with the synchronized chain-rule channel. -/
def exponential (input : FirstJet) : FirstJet :=
  let output := CCL.TranscendentalCoherence.exp input.value.name
  { value := output
    slope := CCL.ProgressiveCoherence.CoherentNamed.mul
      input.slope output
    program := Program.exponential input.program }

/-- Certified complex logarithm and its reciprocal derivative.  The branch
and non-vanishing evidence are explicit inputs. -/
def logarithm (input : FirstJet) (branch : AnchoredChart input.value)
    (apart : CCL.ProgressiveTransducer.Named.Apart
      input.value.name) : FirstJet :=
  let inverse := CCL.ProgressiveCoherence.CoherentNamed.div
    (CCL.ProgressiveCoherence.CoherentNamed.exact 1)
    input.value apart
  { value := branch.output
    slope := CCL.ProgressiveCoherence.CoherentNamed.mul
      input.slope inverse
    program := Program.logarithm input.program branch apart }

/-- Total sine with its synchronized chain-rule channel. -/
def sine (input : FirstJet) : FirstJet :=
  { value := CCL.Trigonometric.sine input.value
    slope := CCL.ProgressiveCoherence.CoherentNamed.mul input.slope
      (CCL.Trigonometric.cosine input.value)
    program := Program.sine input.program }

/-- Total cosine with its synchronized chain-rule channel. -/
def cosine (input : FirstJet) : FirstJet :=
  { value := CCL.Trigonometric.cosine input.value
    slope := CCL.ProgressiveCoherence.CoherentNamed.neg
      (CCL.ProgressiveCoherence.CoherentNamed.mul input.slope
        (CCL.Trigonometric.sine input.value))
    program := Program.cosine input.program }

/-- One rational request below the visible target and below both coherence
moduli.  `commonRequest` is a finite harmonic combination, not an infimum. -/
def requestTarget (jet : FirstJet) (target : Coordinate) : Coordinate :=
  CCL.ProgressiveCoherence.Coherent.commonRequest target
    (CCL.ProgressiveCoherence.Coherent.commonRequest
      (jet.value.coherent.accuracyRequest target)
      (jet.slope.coherent.accuracyRequest target))

theorem requestTarget_pos (jet : FirstJet) {target : Coordinate}
    (positive : 0 < target) : 0 < jet.requestTarget target := by
  apply CCL.ProgressiveCoherence.Coherent.commonRequest_pos positive
  exact CCL.ProgressiveCoherence.Coherent.commonRequest_pos
    (jet.value.coherent.accuracyRequest_pos positive)
    (jet.slope.coherent.accuracyRequest_pos positive)

theorem requestTarget_lt_target (jet : FirstJet) {target : Coordinate}
    (positive : 0 < target) : jet.requestTarget target < target := by
  exact CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
    positive
    (CCL.ProgressiveCoherence.Coherent.commonRequest_pos
      (jet.value.coherent.accuracyRequest_pos positive)
      (jet.slope.coherent.accuracyRequest_pos positive))

theorem requestTarget_lt_valueAllowance (jet : FirstJet)
    {target : Coordinate} (positive : 0 < target) :
    jet.requestTarget target < jet.value.coherent.accuracyRequest target := by
  have innerPositive :=
    CCL.ProgressiveCoherence.Coherent.commonRequest_pos
      (jet.value.coherent.accuracyRequest_pos positive)
      (jet.slope.coherent.accuracyRequest_pos positive)
  exact (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
    positive innerPositive).trans
      (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_left
        (jet.value.coherent.accuracyRequest_pos positive)
        (jet.slope.coherent.accuracyRequest_pos positive))

theorem requestTarget_lt_slopeAllowance (jet : FirstJet)
    {target : Coordinate} (positive : 0 < target) :
    jet.requestTarget target < jet.slope.coherent.accuracyRequest target := by
  have innerPositive :=
    CCL.ProgressiveCoherence.Coherent.commonRequest_pos
      (jet.value.coherent.accuracyRequest_pos positive)
      (jet.slope.coherent.accuracyRequest_pos positive)
  exact (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
    positive innerPositive).trans
      (CCL.ProgressiveCoherence.Coherent.commonRequest_lt_right
        (jet.value.coherent.accuracyRequest_pos positive)
        (jet.slope.coherent.accuracyRequest_pos positive))

def valueRequest (jet : FirstJet) (target : Coordinate)
    (positive : 0 < target) : Named :=
  CCL.TranscendentalOutput.refined jet.value.name
    (jet.requestTarget target) (jet.requestTarget_pos positive)

def slopeRequest (jet : FirstJet) (target : Coordinate)
    (positive : 0 < target) : Named :=
  CCL.TranscendentalOutput.refined jet.slope.name
    (jet.requestTarget target) (jet.requestTarget_pos positive)

theorem valueRequest_radius_lt (jet : FirstJet) {target : Coordinate}
    (positive : 0 < target) :
    ((jet.valueRequest target positive).process.ball
      (jet.valueRequest target positive).state).radiusSq < target :=
  (CCL.TranscendentalOutput.refined_error jet.value.name
    (jet.requestTarget target) (jet.requestTarget_pos positive)).trans
      (jet.requestTarget_lt_target positive)

theorem slopeRequest_radius_lt (jet : FirstJet) {target : Coordinate}
    (positive : 0 < target) :
    ((jet.slopeRequest target positive).process.ball
      (jet.slopeRequest target positive).state).radiusSq < target :=
  (CCL.TranscendentalOutput.refined_error jet.slope.name
    (jet.requestTarget target) (jet.requestTarget_pos positive)).trans
      (jet.requestTarget_lt_target positive)

/-- The value channel's semantic allowance is transported below the same
displayed target as its enclosure radius. -/
theorem valueRequest_allowance_lt (jet : FirstJet) {target : Coordinate}
    (positive : 0 < target) :
    jet.value.coherent.allowance (jet.valueRequest target positive).state <
      target :=
  jet.value.coherent.refine_accurate jet.value.name.state target positive
    (jet.requestTarget target) (jet.requestTarget_pos positive)
      (jet.requestTarget_lt_valueAllowance positive)

/-- The slope channel's semantic allowance is transported below the same
displayed target as its enclosure radius. -/
theorem slopeRequest_allowance_lt (jet : FirstJet) {target : Coordinate}
    (positive : 0 < target) :
    jet.slope.coherent.allowance (jet.slopeRequest target positive).state <
      target :=
  jet.slope.coherent.refine_accurate jet.slope.name.state target positive
    (jet.requestTarget target) (jet.requestTarget_pos positive)
      (jet.requestTarget_lt_slopeAllowance positive)

/-- Both channels answer the same finite bit-count request, with exact parser
semantics at their respective jointly budgeted states. -/
theorem synchronized_bitstream (jet : FirstJet) (target : Coordinate)
    (positive : 0 < target) (count : Nat) :
    let value := jet.valueRequest target positive
    let slope := jet.slopeRequest target positive
    value.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          value.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          value.machine count).emitted.length = count ∧
      slope.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          slope.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          slope.machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        value.process value.state
        (CCL.ProgressiveTransducer.advance
          value.machine count) ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        slope.process slope.state
        (CCL.ProgressiveTransducer.advance
          slope.machine count) := by
  let value := jet.valueRequest target positive
  let slope := jet.slopeRequest target positive
  exact
    ⟨(value.productive count).1, (value.productive count).2,
      (slope.productive count).1, (slope.productive count).2,
      CCL.ProgressiveMachineSemantics.Named.advance_exact
        value count,
      CCL.ProgressiveMachineSemantics.Named.advance_exact
        slope count⟩

end FirstJet

end CCL.ProgressiveFirstJet
