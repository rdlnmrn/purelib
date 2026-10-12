module
import Purelib.Data.Rat.Fraction
public import Purelib.Calculus.Jet.Progressive.Quadratic.Program.Arithmetic
import Purelib.Calculus.Jet.Progressive.Quadratic.Program.Basic
public import Purelib.Calculus.Jet.Progressive.Quadratic.Program.CCL.Request
public import Test.Calculus.Jet.Progressive.QuadraticTrace
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat

open Purelib.Calculus.Jet.Progressive

section
@[expose] public section

/-! Changing-input regressions for synchronized quadratic CCL traces and calculations. -/

namespace Test.Calculus.Jet.Progressive.TraceProgram

/-! ## Executable regression witnesses -/

/-- An indexed source calculation for the changing exponential identity trace.

The calculation retains exactly the Horner sample program certified by the synchronized quadratic trace. -/
def changingInput :
  Quadratic.Program.Basic.Calculation
    QuadraticTrace.exponentialWitnessApproximation.sample :=
  Quadratic.Program.Basic.Calculation.source QuadraticTrace.nonterminatingIdentity

/-- Multiply the changing source calculation by the sum of two copies of itself.

All arithmetic nodes retain the same indexed input sample program and the original trace certificates. -/
def changingArithmetic :
  Quadratic.Program.Basic.Calculation
    QuadraticTrace.exponentialWitnessApproximation.sample :=
  changingInput.mul (changingInput.add
    changingInput)

/-- The arithmetic regression input has distinct samples at stages zero and one. -/
theorem changingArithmetic_input_changes :
    QuadraticTrace.exponentialWitnessApproximation.sample
        0 ≠
      QuadraticTrace.exponentialWitnessApproximation.sample
        1 :=
  QuadraticTrace.nonterminatingIdentity_changes

/-- The changing arithmetic calculation satisfies every positive finite persistent bitstream request.

The request retains the common input index, quadratic laws and persistent output contract for all five certified
channels. -/
theorem changingArithmetic_keeps_emitting
  (target : Fraction.Rational)
    (positive : 0 < target) (count : Nat) :
    Quadratic.Program.Basic.Calculation.PersistentRequestContract changingArithmetic
      0 target positive count :=
  changingArithmetic.persistent_bitstream_and_quadratic_law
    0 target positive count
end Test.Calculus.Jet.Progressive.TraceProgram

end
