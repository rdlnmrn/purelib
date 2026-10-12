module
import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Logarithm.Chart.Anchored
import Purelib.Approximation.Gaussian.Name.Apart
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Approximation.Gaussian.Trigonometric.Name
public import Purelib.Calculus.Jet.Progressive.First.Provenance

open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

section
@[expose] public section

/-!
# Synchronized first jets over progressive CCL inputs

The displayed-input evaluator in `JetData` computes two rational
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

namespace Purelib.Calculus.Jet.Progressive.First.Provenance
namespace JetData

open Purelib.Approximation
open Purelib.Calculus.Jet.Progressive.First
/-- Build an exponential first jet from a progressive input jet.

The output exponential channel is computed once and reused in the slope product. The indexed derivation ties both
returned channels to the original input program. -/
def exponential (input : Provenance.JetData) :
  Provenance.JetData :=
  let output := Gaussian.Exponential.Progressive.Range.Coherent.exp input.value.name
  { value := output
    slope := CoherentNamed.mul
      input.slope output
    program := Provenance.Program.exponential input.program }

/-- Build a logarithm first jet in a supplied anchored chart.

The value is the chart's retained output. Apartness of the same input value supplies the reciprocal channel used with
the input slope; the resulting program retains both pieces of domain evidence. -/
def logarithm (input : Provenance.JetData) (branch :
  Gaussian.Logarithm.Chart.Anchored.AnchoredChart input.value)
    (apart : Gaussian.Name.Basic.Named.Apart
      input.value.name) : Provenance.JetData :=
  let inverse := CoherentNamed.div
    (CoherentNamed.Coherence.exact 1)
    input.value apart
  { value := branch.output
    slope := CoherentNamed.mul
      input.slope inverse
    program := Provenance.Program.logarithm input.program branch apart }

/-- Build a sine value channel with input slope multiplied by cosine as its slope.

The resulting indexed program derives both channels from the retained input jet. -/
def sine (input : Provenance.JetData) :
  Provenance.JetData :=
  { value := Gaussian.Trigonometric.Name.sine input.value
    slope := CoherentNamed.mul input.slope
      (Gaussian.Trigonometric.Name.cosine input.value)
    program := Provenance.Program.sine input.program }

/-- Build a cosine value channel with the negative input-slope-times-sine slope.

The resulting indexed program derives both channels from the retained input jet. -/
def cosine (input : Provenance.JetData) :
  Provenance.JetData :=
  { value := Gaussian.Trigonometric.Name.cosine input.value
    slope := CoherentNamed.neg
      (CoherentNamed.mul input.slope
        (Gaussian.Trigonometric.Name.sine input.value))
    program := Provenance.Program.cosine input.program }
end JetData

end Purelib.Calculus.Jet.Progressive.First.Provenance

end
