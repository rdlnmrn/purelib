module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Name.CCL.Contract
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Refinement
public import Purelib.Approximation.Gaussian.Trigonometric.Name
import Purelib.Data.CCL.Transducer.Machine.Advance
public import Purelib.Data.CCL.Transducer.Machine.Semantics.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.CCL.Output
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.CCL.Transducer.Machine.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Trigonometric

open Purelib.Data.CCL.Transducer.Machine

open Purelib.Data.Rat

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

namespace Purelib.Approximation.Gaussian.Trigonometric.CCL.Output

/-- One synchronized finite accuracy/bit request for the constructed sine. -/
theorem sine_bitstream_and_error (input :
  CoherentNamed)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    let refined := Refinement.refined
      (Name.sine input).name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (Advance.advance
          refined.machine count).emitted ∧
      (Advance.advance
          refined.machine count).emitted.length = count ∧
      Semantics.Basic.ExactCursor
        refined.process refined.state
        (Advance.advance
          refined.machine count) :=
  CCL.Contract.refined_bitstream_and_error
    (Name.sine input).name target positive count

/-- One synchronized finite accuracy/bit request for the constructed cosine. -/
theorem cosine_bitstream_and_error (input :
  CoherentNamed)
    (target : Fraction.Rational) (positive : 0 < target) (count : Nat) :
    let refined := Refinement.refined
      (Name.cosine input).name target positive
    (refined.process.ball refined.state).radiusSq < target ∧
      refined.machine.emitted.IsPrefix
        (Advance.advance
          refined.machine count).emitted ∧
      (Advance.advance
          refined.machine count).emitted.length = count ∧
      Semantics.Basic.ExactCursor
        refined.process refined.state
        (Advance.advance
          refined.machine count) :=
  CCL.Contract.refined_bitstream_and_error
    (Name.cosine input).name target positive count

end Purelib.Approximation.Gaussian.Trigonometric.CCL.Output

end
