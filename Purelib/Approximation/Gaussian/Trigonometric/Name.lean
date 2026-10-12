module
public import Purelib.Approximation.Gaussian.Exponential.Progressive.Range.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic
import Purelib.Data.Gaussian.Constants

open Purelib

open Purelib.Approximation.Gaussian.Exponential.Progressive.Range

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed

open Purelib.Data.Gaussian

section
@[expose] public section

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

namespace Purelib.Approximation.Gaussian.Trigonometric.Name

/-- The actual range-reduced CCL computation of `exp(i z)`. -/
def positivePhase (input : CoherentNamed) :
  Coherent.CoherentNamed :=
  Coherent.exp (CoherentNamed.rotate input).name

/-- The actual range-reduced CCL computation of `exp(-i z)`. -/
def negativePhase (input : CoherentNamed) :
  Coherent.CoherentNamed :=
  Coherent.exp
    (CoherentNamed.neg
      (CoherentNamed.rotate input)).name

/-- `sin z = (exp(i z) - exp(-i z)) / (2i)`, evaluated wholly through certified finite CCL operations. -/
def sine (input : CoherentNamed) :
  Coherent.CoherentNamed :=
  CoherentNamed.mul
    (CoherentNamed.sub
      (positivePhase input)
        (negativePhase input))
    (Coherence.exact Constants.inverseTwoI)

/-- `cos z = (exp(i z) + exp(-i z)) / 2`, evaluated wholly through certified finite CCL operations. -/
def cosine (input : CoherentNamed) :
  Coherent.CoherentNamed :=
  CoherentNamed.mul
    (CoherentNamed.add
      (positivePhase input)
        (negativePhase input))
    (Coherence.exact Constants.half)
end Purelib.Approximation.Gaussian.Trigonometric.Name

end
