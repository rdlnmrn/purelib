import CCL.Transcendental.Coherence
import CCL.Transcendental.Output

/-!
# Trigonometric operations as certified finite CCL compositions

Sine and cosine need no new infinite series.  They are assembled from the
already total, range-reduced exponential process and ordinary coherent CCL
arithmetic.  Every constructor below therefore returns a productive CCL name
with the same rational accuracy sidechannel as exponential.

The domain is explicit and pleasantly simple: every coherent arithmetic CCL
name is accepted.  No global complex value, function graph, or completed
series is introduced.
-/

namespace CCL.Trigonometric

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed

/-- The displayed Gaussian-rational imaginary unit. -/
def imaginaryUnit : Gaussian := ⟨0, 1⟩

/-- The exact rational coefficient `1 / 2`. -/
def half : Gaussian := ⟨1 / 2, 0⟩

/-- The exact rational coefficient `1 / (2i) = -i/2`. -/
def inverseTwoI : Gaussian := ⟨0, -(1 / 2)⟩

/-- The coherent input `i z`. -/
def rotate (input : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.mul
    (CCL.ProgressiveCoherence.CoherentNamed.exact imaginaryUnit)
    input

/-- The actual range-reduced CCL computation of `exp(i z)`. -/
def positivePhase (input : CoherentNamed) : CoherentNamed :=
  CCL.TranscendentalCoherence.exp (rotate input).name

/-- The actual range-reduced CCL computation of `exp(-i z)`. -/
def negativePhase (input : CoherentNamed) : CoherentNamed :=
  CCL.TranscendentalCoherence.exp
    (CCL.ProgressiveCoherence.CoherentNamed.neg
      (rotate input)).name

/-- `sin z = (exp(i z) - exp(-i z)) / (2i)`, evaluated wholly through
certified finite CCL operations. -/
def sine (input : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.mul
    (CCL.ProgressiveCoherence.CoherentNamed.sub
      (positivePhase input) (negativePhase input))
    (CCL.ProgressiveCoherence.CoherentNamed.exact inverseTwoI)

/-- `cos z = (exp(i z) + exp(-i z)) / 2`, evaluated wholly through certified
finite CCL operations. -/
def cosine (input : CoherentNamed) : CoherentNamed :=
  CCL.ProgressiveCoherence.CoherentNamed.mul
    (CCL.ProgressiveCoherence.CoherentNamed.add
      (positivePhase input) (negativePhase input))
    (CCL.ProgressiveCoherence.CoherentNamed.exact half)

/-- One synchronized finite accuracy/bit request for the constructed sine. -/
theorem sine_bitstream_and_error (input : CoherentNamed)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    let refined := CCL.TranscendentalOutput.refined
      (sine input).name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          refined.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          refined.machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        refined.process refined.state
        (CCL.ProgressiveTransducer.advance
          refined.machine count) :=
  CCL.TranscendentalOutput.refined_bitstream_and_error
    (sine input).name target positive count

/-- One synchronized finite accuracy/bit request for the constructed cosine. -/
theorem cosine_bitstream_and_error (input : CoherentNamed)
    (target : Coordinate) (positive : 0 < target) (count : Nat) :
    let refined := CCL.TranscendentalOutput.refined
      (cosine input).name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (CCL.ProgressiveTransducer.advance
          refined.machine count).emitted ∧
      (CCL.ProgressiveTransducer.advance
          refined.machine count).emitted.length = count ∧
      CCL.ProgressiveMachineSemantics.ExactCursor
        refined.process refined.state
        (CCL.ProgressiveTransducer.advance
          refined.machine count) :=
  CCL.TranscendentalOutput.refined_bitstream_and_error
    (cosine input).name target positive count

end CCL.Trigonometric
